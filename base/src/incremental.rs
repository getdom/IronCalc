//! Incremental recalculation.
//!
//! A full `evaluate()` visits every cell. Most edits touch one cell, and only the formulas
//! that read it (directly, through a range, or through a defined name) can change. The
//! dependency index is built from `support` — what each formula actually read during its
//! last evaluation — so it follows the real reads, including through names and
//! cross-sheet references. Cells whose formulas call a volatile function (NOW, RAND,
//! INDIRECT, OFFSET…) are recalculated every time, since their reads are not recorded.
//!
//! Anything the index cannot follow falls back to a full evaluation: a structural change
//! (rows, columns, sheets, names, tables) marks the index as stale, and dynamic arrays keep
//! the full two-phase algorithm.
use std::collections::{HashMap, HashSet};

use crate::expressions::parser::static_analysis::StaticResult;
use crate::expressions::parser::Node;
use crate::expressions::types::CellReferenceIndex;
use crate::functions::Function;
use crate::types::Cell;
use crate::model::{CellOrRange, Model};
use crate::types::ArrayKind;

/// (sheet, row, column)
pub(crate) type Key = (u32, i32, i32);

/// What an `evaluate_dirty` did, for logs and tests.
#[derive(Debug, Clone)]
pub struct RecalcReport {
    /// Everything was recalculated.
    pub full: bool,
    /// Why, when `full`.
    pub reason: &'static str,
    /// Cells recalculated (or, when full, formula cells in the workbook).
    pub cells: usize,
    /// Cells recalculated on every pass because their formula is volatile.
    pub volatile: usize,
    pub millis: u128,
    /// Conditional formatting, evaluated after an incremental pass.
    pub millis_cf: u128,
}

/// A range a formula reads: the formula is recalculated when any cell inside changes.
#[derive(Clone, Copy)]
pub(crate) struct RangeDep {
    r1: i32,
    c1: i32,
    r2: i32,
    c2: i32,
    dependent: Key,
    /// The dependent's generation when this entry was made; older entries are stale.
    gen: u32,
}

#[derive(Default)]
pub(crate) struct DependencyIndex {
    /// precedent cell → the formula cells that read it directly
    cells: HashMap<Key, HashSet<Key>>,
    /// per sheet, the ranges formulas read
    ranges: HashMap<u32, Vec<RangeDep>>,
    /// generation of each dependent's range entries
    gen: HashMap<Key, u32>,
    /// range entries left behind by re-evaluated cells, compacted when they dominate
    stale: usize,
    /// Cells inside a dynamic array's spill area (anchors included): an edit that touches
    /// one needs the full two-phase evaluation.
    spill_areas: HashSet<Key>,
    /// True once built by a full evaluation and not invalidated since.
    pub(crate) ready: bool,
}

fn is_volatile(node: &Node) -> bool {
    use Node::*;
    match node {
        FunctionKind { kind, args } => {
            matches!(kind, Function::Now | Function::Today | Function::Rand | Function::Randbetween | Function::Randarray | Function::Indirect | Function::Offset) || args.iter().any(is_volatile)
        }
        OpRangeKind { left, right } | OpConcatenateKind { left, right } | OpSumKind { left, right, .. } | OpProductKind { left, right, .. } | OpPowerKind { left, right } | CompareKind { left, right, .. } => is_volatile(left) || is_volatile(right),
        LambdaDefKind { body, .. } => is_volatile(body),
        LambdaCallKind { lambda, args } => is_volatile(lambda) || args.iter().any(is_volatile),
        NamedFunctionKind { args, .. } => args.iter().any(is_volatile),
        ImplicitIntersection { child, .. } | SpillRangeOperator { child } => is_volatile(child),
        UnaryKind { right, .. } => is_volatile(right),
        _ => false,
    }
}

impl Model<'_> {
    /// Tells the model a cell's content changed by hand or by an operation; the next
    /// `evaluate_dirty` recalculates what depends on it.
    pub fn mark_dirty(&mut self, sheet: u32, row: i32, column: i32) {
        self.dirty.push((sheet, row, column));
    }

    /// Tells the model something structural changed (rows, columns, sheets, names, tables):
    /// the next `evaluate_dirty` is a full evaluation.
    pub fn needs_full_evaluation(&mut self) {
        self.index.ready = false;
    }

    /// Recalculates the marked cells and everything that reads them, or everything when the
    /// index cannot be trusted. Conditional formatting is re-evaluated either way.
    pub fn evaluate_dirty(&mut self) -> RecalcReport {
        let full = |this: &mut Self, reason: &'static str| {
            let t = std::time::Instant::now();
            this.evaluate();
            RecalcReport { full: true, reason, cells: this.cells.len(), volatile: this.volatile.len(), millis: t.elapsed().as_millis(), millis_cf: 0 }
        };
        if !self.index.ready {
            return full(self, "index not ready");
        }
        let t = std::time::Instant::now();
        let seeds: Vec<Key> = std::mem::take(&mut self.dirty);
        // A new formula that may spill needs the two-phase evaluation.
        for &(sheet, row, column) in &seeds {
            if let Some(f) = self.fetch_cell(CellReferenceIndex { sheet, row, column }).and_then(|c| c.get_formula()) {
                if let Some((_, r)) = self.parsed_formulas.get(sheet as usize).and_then(|v| v.get(f as usize)) {
                    if !matches!(r, StaticResult::Scalar) {
                        return full(self, "a formula that may spill");
                    }
                }
            }
        }
        // Everything the seeds reach, plus the volatile cells.
        let mut queue: Vec<Key> = seeds;
        queue.extend(self.volatile.iter().copied());
        let mut visited: HashSet<Key> = HashSet::new();
        while let Some(k) = queue.pop() {
            if !visited.insert(k) {
                continue;
            }
            if let Some(deps) = self.index.cells.get(&k) {
                queue.extend(deps.iter().copied());
            }
            if let Some(list) = self.index.ranges.get(&k.0) {
                for rd in list {
                    if rd.r1 <= k.1 && k.1 <= rd.r2 && rd.c1 <= k.2 && k.2 <= rd.c2 && self.index.gen.get(&rd.dependent).copied().unwrap_or(0) == rd.gen {
                        queue.push(rd.dependent);
                    }
                }
            }
        }
        // Dynamic arrays keep the full two-phase evaluation: an anchor, a spilled cell, or a
        // cell inside a spill area among the touched ones.
        if visited.iter().any(|k| self.index.spill_areas.contains(k) || matches!(self.fetch_cell(CellReferenceIndex { sheet: k.0, row: k.1, column: k.2 }), Some(Cell::ArrayFormula { kind: ArrayKind::Dynamic, .. }) | Some(Cell::SpillCell { .. }))) {
            self.dirty = visited.into_iter().collect();
            return full(self, "touches a dynamic array");
        }
        // Forget what they were and what they read.
        for k in &visited {
            self.cells.remove(k);
            self.links.remove(k);
            self.forget_external_user(*k);
            if let Some(precs) = self.support.remove(&CellReferenceIndex { sheet: k.0, row: k.1, column: k.2 }) {
                let mut ranges = 0;
                for p in precs {
                    match p {
                        CellOrRange::Cell(c) => {
                            if let Some(set) = self.index.cells.get_mut(&c) {
                                set.remove(k);
                            }
                        }
                        CellOrRange::Range(_) => ranges += 1,
                    }
                }
                self.index.stale += ranges;
            }
            *self.index.gen.entry(*k).or_insert(0) += 1;
        }
        self.clear_variable_stack();
        self.clear_lambdas();
        for k in &visited {
            self.evaluate_cell(CellReferenceIndex { sheet: k.0, row: k.1, column: k.2 });
        }
        // A cell that started to spill just now: its neighbours must be written in order.
        if visited.iter().any(|k| matches!(self.fetch_cell(CellReferenceIndex { sheet: k.0, row: k.1, column: k.2 }), Some(Cell::ArrayFormula { kind: ArrayKind::Dynamic, r, .. }) if *r != (1, 1))) {
            return full(self, "a formula started to spill");
        }
        for k in &visited {
            self.index_cell(*k);
        }
        self.compact_ranges();
        let millis = t.elapsed().as_millis();
        let t = std::time::Instant::now();
        self.evaluate_conditional_formatting();
        RecalcReport { full: false, reason: "", cells: visited.len(), volatile: self.volatile.len(), millis, millis_cf: t.elapsed().as_millis() }
    }

    /// After a full evaluation: the index from every formula's recorded reads, and the
    /// volatile cells.
    pub(crate) fn build_dependency_index(&mut self) {
        self.index = DependencyIndex::default();
        self.dirty.clear();
        let keys: Vec<Key> = self.support.keys().map(|c| (c.sheet, c.row, c.column)).collect();
        for k in keys {
            self.index_cell(k);
        }
        let mut volatile = HashSet::new();
        let mut by_formula: HashMap<(u32, i32), bool> = HashMap::new();
        for c in self.get_all_cells() {
            let at = CellReferenceIndex { sheet: c.index, row: c.row, column: c.column };
            if let Some(f) = self.fetch_cell(at).and_then(|cell| cell.get_formula()) {
                let v = *by_formula.entry((c.index, f)).or_insert_with(|| self.parsed_formulas.get(c.index as usize).and_then(|v| v.get(f as usize)).map(|(n, _)| is_volatile(n)).unwrap_or(false));
                if v {
                    volatile.insert((c.index, c.row, c.column));
                }
            }
        }
        self.volatile = volatile;
        let mut areas = HashSet::new();
        for anchor in self.spill_cells.clone() {
            for c in self.get_spill_area(anchor) {
                areas.insert((c.sheet, c.row, c.column));
            }
            areas.insert((anchor.sheet, anchor.row, anchor.column));
        }
        self.index.spill_areas = areas;
        self.index.ready = true;
    }

    fn index_cell(&mut self, k: Key) {
        let precs = match self.support.get(&CellReferenceIndex { sheet: k.0, row: k.1, column: k.2 }) {
            Some(p) => p.clone(),
            None => return,
        };
        let gen = self.index.gen.get(&k).copied().unwrap_or(0);
        for p in precs.into_iter() {
            match p {
                CellOrRange::Cell(c) => {
                    self.index.cells.entry(c).or_default().insert(k);
                }
                CellOrRange::Range((sheet, r1, c1, r2, c2)) => {
                    self.index.ranges.entry(sheet).or_default().push(RangeDep { r1, c1, r2, c2, dependent: k, gen });
                }
            }
        }
    }

    fn compact_ranges(&mut self) {
        let total: usize = self.index.ranges.values().map(|v| v.len()).sum();
        if self.index.stale < 1024 || self.index.stale * 2 < total {
            return;
        }
        let gen = std::mem::take(&mut self.index.gen);
        for list in self.index.ranges.values_mut() {
            list.retain(|rd| gen.get(&rd.dependent).copied().unwrap_or(0) == rd.gen);
        }
        self.index.gen = gen;
        self.index.stale = 0;
    }
}

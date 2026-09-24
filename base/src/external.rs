//! `API(connection, variable…, field)`: a value that lives outside the workbook.
//!
//! The function itself does no I/O. It builds a key from its arguments, records that the
//! cell reads that key, and returns the value the application put in the cache for it —
//! or `#N/A` ("waiting for the API") while nothing has arrived yet. The application asks for
//! the keys still waiting, fetches them, and calls `set_external`, which marks every cell
//! reading that key dirty so the next incremental evaluation carries the value on.
use std::collections::{HashMap, HashSet};

use crate::calc_result::CalcResult;
use crate::expressions::parser::Node;
use crate::expressions::token::Error;
use crate::expressions::types::CellReferenceIndex;
use crate::incremental::Key;
use crate::model::Model;

/// What an external key resolved to.
#[derive(Debug, Clone, PartialEq)]
pub enum ExternalValue {
    Number(f64),
    Text(String),
    Boolean(bool),
    /// The fetch failed; the message shows as `#N/A` with this text.
    Failed(String),
}

/// The arguments of an `API` call joined into one key; `\u{1}` never appears in a formula.
pub const EXTERNAL_KEY_SEP: char = '\u{1}';

impl Model<'_> {
    pub(crate) fn fn_api(&mut self, args: &[Node], cell: CellReferenceIndex) -> CalcResult {
        if args.is_empty() {
            return CalcResult::new_args_number_error(cell);
        }
        let mut parts = Vec::with_capacity(args.len());
        for arg in args {
            match self.get_string(arg, cell) {
                Ok(s) => parts.push(s),
                Err(e) => return e,
            }
        }
        let key = parts.join(&EXTERNAL_KEY_SEP.to_string());
        let at = (cell.sheet, cell.row, cell.column);
        self.external_users.entry(key.clone()).or_default().insert(at);
        match self.externals.get(&key) {
            Some(ExternalValue::Number(n)) => CalcResult::Number(*n),
            Some(ExternalValue::Text(t)) => CalcResult::String(t.clone()),
            Some(ExternalValue::Boolean(b)) => CalcResult::Boolean(*b),
            Some(ExternalValue::Failed(m)) => CalcResult::Error { error: Error::NA, origin: cell, message: m.clone() },
            None => {
                self.external_requests.insert(key);
                CalcResult::Error { error: Error::NA, origin: cell, message: "waiting for the API".to_string() }
            }
        }
    }

    /// Keys asked for by `API` calls that have no value yet.
    pub fn external_requests(&self) -> Vec<String> {
        let mut v: Vec<String> = self.external_requests.iter().filter(|k| !self.externals.contains_key(*k)).cloned().collect();
        v.sort();
        v
    }

    /// Puts a value in the cache and marks every cell reading it dirty; `evaluate_dirty`
    /// then carries it on. Returns how many cells read the key.
    pub fn set_external(&mut self, key: &str, value: ExternalValue) -> usize {
        self.externals.insert(key.to_string(), value);
        self.external_requests.remove(key);
        let users: Vec<Key> = self.external_users.get(key).map(|s| s.iter().copied().collect()).unwrap_or_default();
        for (sheet, row, column) in &users {
            self.mark_dirty(*sheet, *row, *column);
        }
        users.len()
    }

    /// Forgets a cached value (the application will fetch it again); the cells reading it
    /// keep showing the old value until the new one arrives.
    pub fn forget_external(&mut self, key: &str) {
        self.externals.remove(key);
        self.external_requests.insert(key.to_string());
    }

    pub fn external_value(&self, key: &str) -> Option<&ExternalValue> {
        self.externals.get(key)
    }

    /// Every cached key with its value, for the file.
    pub fn externals(&self) -> Vec<(String, ExternalValue)> {
        let mut v: Vec<(String, ExternalValue)> = self.externals.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        v.sort_by(|a, b| a.0.cmp(&b.0));
        v
    }

    /// Every key whose first part (the connection) is `connection`.
    pub fn external_keys_of(&self, connection: &str) -> Vec<String> {
        let mut v: Vec<String> = self
            .externals
            .keys()
            .chain(self.external_requests.iter())
            .filter(|k| k.split(EXTERNAL_KEY_SEP).next() == Some(connection))
            .cloned()
            .collect();
        v.sort();
        v.dedup();
        v
    }

    /// The keys a cell reads through `API`, as of its last evaluation.
    pub fn cell_external_keys(&self, sheet: u32, row: i32, column: i32) -> Vec<String> {
        let at = (sheet, row, column);
        let mut v: Vec<String> = self.external_users.iter().filter(|(_, users)| users.contains(&at)).map(|(k, _)| k.clone()).collect();
        v.sort();
        v
    }

    pub(crate) fn clear_external_users(&mut self) {
        self.external_users.clear();
    }

    pub(crate) fn forget_external_user(&mut self, at: Key) {
        for users in self.external_users.values_mut() {
            users.remove(&at);
        }
    }
}

pub(crate) type ExternalUsers = HashMap<String, HashSet<Key>>;

pub mod dfa;
pub mod regex;

pub use regex_syntax::ast::Error;
pub use regex_syntax::Parser as RegexParser;

use std::collections::HashSet;

lazy_static::lazy_static! {
    pub static ref EMPTY_REGEX: regex::Regex = regex::Regex::Set(
        regex::Set::Set(HashSet::from([]))
    );
}

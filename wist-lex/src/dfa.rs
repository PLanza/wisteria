use crate::regex::{Regex, Symbol};
use regex_syntax::ast::Ast;

use std::collections::{HashMap, HashSet};

pub struct DFA {
    pub(crate) definitions: HashMap<String, Regex>,
    pub(crate) start_state: Regex,
    pub(crate) states: HashSet<Regex>,
    pub(crate) final_states: HashSet<Regex>,
}

impl DFA {
    pub fn from_regex(ast: Ast) -> DFA {
        let mut dfa = DFA {
            definitions: HashMap::new(),
            start_state: Regex::Null,
            states: HashSet::new(),
            final_states: HashSet::new(),
        };

        let regex = Regex::from_ast(ast, &dfa.definitions);
        dfa.start_state = regex.derivative(Symbol::Null);
        // let (states, transitions) = DFA::explore({start_state}, {}, start_state)
        dfa.final_states = dfa
            .states
            .iter()
            .cloned()
            .filter(|state| state.nullable())
            .collect();

        dfa
    }

    fn derivative_classes(regex: Regex) -> HashSet<Regex> {
        todo!()
    }
}

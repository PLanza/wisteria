use crate::grammar::Grammar;
use std::collections::HashMap;
use std::{cell::RefCell, rc::Rc};

#[derive(Debug, Clone)]
pub(crate) enum BackusNaur {
    Token(String),                         // UPPERCASE
    Def(String),                           // lowercase
    Seq(Box<BackusNaur>, Box<BackusNaur>), // {} {}
    Star(Box<BackusNaur>),                 // ({})*
    Named(String, Box<BackusNaur>),        // <id: {}>
}

impl BackusNaur {
    pub(crate) fn is_recursive(&self, def_name: &String) -> bool {
        use BackusNaur::*;
        match self {
            Token(_) => false,
            Def(name) => def_name == name,
            Seq(b1, b2) => b1.is_recursive(def_name) || b2.is_recursive(def_name),
            Star(b) => b.is_recursive(def_name),
            Named(_, b) => b.is_recursive(def_name),
        }
    }
    pub(crate) fn to_grammar(
        &self,
        name: &String,
        defs: &mut HashMap<String, Rc<RefCell<Grammar>>>,
    ) -> Grammar {
        use crate::grammar::GrammarTerm;
        use BackusNaur::*;
        match self {
            Token(tok) => Grammar::new(GrammarTerm::Token(tok.clone())),
            Def(def) => {
                if def == name {
                    Grammar::new(GrammarTerm::Var(def.clone()))
                } else {
                    let cell = defs.get(def).unwrap();
                    Grammar::new(GrammarTerm::Def(def.clone(), cell.clone()))
                }
            }
            Seq(b1, b2) => {
                let (g1, g2) = (b1.to_grammar(name, defs), b2.to_grammar(name, defs));
                Grammar::new(GrammarTerm::Seq(g1, g2))
            }
            Star(b) => {
                let g = b.to_grammar(name, defs);
                Grammar::new(GrammarTerm::Star(g))
            }
            Named(_, b) => b.to_grammar(name, defs),
        }
    }
}

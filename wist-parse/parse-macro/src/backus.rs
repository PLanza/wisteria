use proc_macro::TokenStream;
use std::collections::HashMap;

pub(crate) enum BackusNaur {
    Token(String),                         // UPPERCASE
    Def(String),                           // lowercase
    Seq(Box<BackusNaur>, Box<BackusNaur>), // {} {}
    Star(Box<BackusNaur>),                 // ({})*
    Named(String, Box<BackusNaur>),        // <id: {}>
}

impl BackusNaur {
    pub(crate) fn is_named(&self) -> bool {
        match self {
            Self::Named(..) => true,
            _ => false,
        }
    }
    pub(crate) fn to_grammar(
        &self,
        name: String,
        defs: &HashMap<String, TokenStream>,
    ) -> TokenStream {
        todo!()
    }
}

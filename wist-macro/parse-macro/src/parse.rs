use crate::backus::BackusNaur;
use crate::error::{GrammarError, GrammarErrorKind};
use crate::grammar::{Grammar, GrammarTerm};

use proc_macro2::TokenStream;
use quote::quote;
use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet},
    fs::File,
    io::{self, prelude::*, BufReader},
    rc::Rc,
};

use wist_utils::{Position, Span};

pub struct GrammarParser {
    /// The current position of the parser.
    file_name: String,
    pos: Cell<Position>,
    lines: std::iter::Peekable<io::Lines<BufReader<File>>>,
    curr_line: String,
    line_offset: usize,
    token_type_map: HashMap<syn::Ident, syn::Type>,
    pub(crate) defs: HashMap<String, Rc<RefCell<Grammar>>>,
    return_types: HashMap<String, syn::Type>,
    pub(crate) start: (String, Rc<RefCell<Grammar>>),
}

impl GrammarParser {
    pub fn new(path: String, token_type_map: HashMap<syn::Ident, syn::Type>) -> io::Result<Self> {
        let file = File::open(path.clone())?;
        let mut lines = BufReader::new(file).lines().peekable();
        let curr_line = lines.next().unwrap_or_else(|| {
            panic!(
                "{}",
                GrammarError::new(
                    path.clone(),
                    Span::splat(Position {
                        line: 0,
                        offset: 0,
                        column: 0
                    }),
                    String::new(),
                    GrammarErrorKind::EmptyFile
                )
            )
        })?;

        let mut parser = GrammarParser {
            file_name: path.clone(),
            pos: Cell::new(Position::new(0, 1, 0)),
            lines,
            curr_line,
            line_offset: 0,
            token_type_map,
            defs: HashMap::new(),
            return_types: HashMap::new(),
            start: (
                String::new(),
                Rc::new(RefCell::new(Grammar::new(GrammarTerm::Bot))),
            ),
        };

        parser.initialize();
        parser.reset();

        Ok(parser)
    }

    // Initializes defs, return types and starting grammar of parser
    fn initialize(&mut self) {
        while !self.is_eof() {
            self.initialize_grammar_def();
        }
        if self.start.0.is_empty() {
            self.panic(GrammarErrorKind::NoStartingParseRule);
        }
    }

    fn initialize_grammar_def(&mut self) {
        let mut def_name = String::new();
        let is_start = if self.char() == '$' {
            self.bump_and_bump_space();
            true
        } else {
            false
        };
        while !self.is_eof() && (self.char().is_lowercase() || self.char() == '_') {
            def_name.push(self.char());
            self.bump();
        }
        self.bump_space();

        if def_name.is_empty() {
            self.panic(GrammarErrorKind::EmptyDefinitionName)
        }

        if !self.bump_if("->") {
            self.panic(GrammarErrorKind::ExpectedReturnType)
        }

        // Parse the return type
        let mut seen_colon = false;
        let mut return_type = String::new();
        let start = self.pos();
        while !self.is_eof() {
            if seen_colon && self.char() == ':' {
                seen_colon = false;
            } else if seen_colon {
                return_type.pop();
                break;
            } else if self.char() == ':' {
                seen_colon = true;
            }
            return_type.push(self.char());
            self.bump();
        }
        self.bump_space();
        let return_type = syn::parse_str(&return_type).unwrap_or_else(|_| {
            self.panic_with_span(
                GrammarErrorKind::InvalidReturnType,
                Span::new(start, self.pos()),
            )
        });
        self.return_types.insert(def_name.clone(), return_type);

        self.initialize_map_grammar();
        while self.char() == '|' {
            self.bump_and_bump_space();
            self.initialize_map_grammar();
        }

        let cell = Rc::new(RefCell::new(Grammar::new(GrammarTerm::Bot)));
        self.defs.insert(def_name.clone(), cell.clone());
        if is_start {
            self.start = (def_name, cell);
        }
    }

    fn initialize_map_grammar(&mut self) {
        while !self.is_eof() && self.char() != '{' {
            self.bump();
        }

        let mut brace_count = 1;
        while brace_count != 0 {
            self.bump();
            if self.char() == '}' {
                brace_count -= 1;
            } else if self.char() == '{' {
                brace_count += 1;
            }
        }
        self.bump_and_bump_space();
    }

    fn reset(&mut self) {
        self.pos.set(Position {
            line: 0,
            offset: 0,
            column: 0,
        });

        let file = File::open(self.file_name.clone()).unwrap();
        self.lines = BufReader::new(file).lines().peekable();

        self.curr_line = self.lines.next().unwrap().unwrap();
        self.line_offset = 0;
    }

    /// Return the current offset of the parser.
    ///
    /// The offset starts at `0` from the beginning of the regular expression
    /// pattern string.
    fn offset(&self) -> usize {
        self.pos.get().offset
    }

    fn char(&self) -> char {
        if self.curr_line.is_empty() {
            return '\n';
        }
        self.curr_line[self.line_offset..]
            .chars()
            .next()
            .unwrap_or_else(|| panic!("expected char at offset {}", self.offset()))
    }

    /// Bump the parser to the next Unicode scalar value.
    ///
    /// If the end of the input has been reached, then `false` is returned.
    fn bump(&mut self) -> bool {
        if self.is_eof() {
            return false;
        }

        let Position {
            mut offset,
            mut line,
            mut column,
        } = self.pos();

        if self.is_end_of_line() {
            offset += '\n'.len_utf8();
            self.line_offset = 0;
            line = line.checked_add(1).unwrap();
            column = 1;

            self.curr_line = self.lines.next().unwrap().unwrap();
        } else {
            offset += self.char().len_utf8();
            self.line_offset += self.char().len_utf8();
            column = column.checked_add(1).unwrap();
        }

        self.pos.set(Position {
            offset,
            line,
            column,
        });
        self.curr_line[self.line_offset..].chars().next().is_some() || self.curr_line.is_empty()
    }

    fn bump_if(&mut self, prefix: &str) -> bool {
        if self.curr_line[self.line_offset..].starts_with(prefix) {
            for _ in 0..prefix.chars().count() {
                self.bump();
            }
            true
        } else {
            false
        }
    }

    fn bump_and_bump_space(&mut self) -> bool {
        if !self.bump() {
            return false;
        }
        self.bump_space();
        !self.is_eof()
    }

    // Returns true if bumped new line
    fn bump_space(&mut self) -> bool {
        let mut result = false;
        while !self.is_eof() {
            if self.curr_line.is_empty() {
                self.bump();
                result = true;
            } else if self.char().is_whitespace() {
                self.bump();
            } else {
                break;
            }
        }
        result
    }

    /// Returns true if the next call to `bump` would return false.
    fn is_eof(&mut self) -> bool {
        self.is_end_of_line() && self.lines.peek().is_none()
    }

    fn is_end_of_line(&self) -> bool {
        self.curr_line.is_empty() || self.line_offset == self.curr_line.len() - 1
    }

    /// Return the current position of the parser, which includes the offset,
    /// line and column.
    fn pos(&self) -> Position {
        self.pos.get()
    }

    /// Create a span at the current position of the parser. Both the start
    /// and end of the span are set.
    fn span(&self) -> Span {
        Span::splat(self.pos())
    }

    pub fn parse_grammar(&mut self) {
        while !self.is_eof() {
            self.parse_grammar_def();
        }
        if self.start.1.borrow_mut().create_fix_points(
            &self.start.0,
            &mut self.defs,
            HashSet::from([self.start.0.clone()]),
        ) {
            let inner = self.start.1.borrow().clone();
            *self.start.1.borrow_mut() =
                Grammar::new(GrammarTerm::Fix(self.start.0.clone(), inner));
        }

        self.start.1.borrow_mut().type_check(HashMap::new());

        for (name, def) in &self.defs {
            println!("{}: {}\n", name, def.borrow());
        }
    }

    fn parse_grammar_def(&mut self) {
        let mut def_name = String::new();
        if self.char() == '$' {
            self.bump_and_bump_space();
        }
        while !self.is_eof() && (self.char().is_lowercase() || self.char() == '_') {
            def_name.push(self.char());
            self.bump();
        }
        self.bump_space();
        self.bump_if("->");

        // Parse the return type
        let mut seen_colon = false;
        while !self.is_eof() {
            if seen_colon && self.char() == ':' {
                seen_colon = false;
            } else if seen_colon {
                break;
            } else if self.char() == ':' {
                seen_colon = true;
            }
            self.bump();
        }
        self.bump_space();

        // Parse all the grammar alternations individually
        let mut map_grammars = Vec::new();
        let mut is_recursive = false;

        let (map_grammar, is_rec) = self.parse_map_grammar(&def_name);
        map_grammars.push(map_grammar);
        is_recursive |= is_rec;

        while self.char() == '|' {
            self.bump_and_bump_space();
            let (map_grammar, is_rec) = self.parse_map_grammar(&def_name);
            map_grammars.push(map_grammar);
            is_recursive |= is_rec;
        }

        // Join the parsed alternations
        let mut alt_grammar = map_grammars.pop().unwrap();
        for grammar in map_grammars.iter().rev() {
            alt_grammar = Grammar::new(GrammarTerm::Alt(grammar.clone(), alt_grammar))
        }

        // Convert immediately recursive definitions to fix points
        let grammar = if is_recursive {
            Grammar::new(GrammarTerm::Fix(def_name.clone(), alt_grammar))
        } else {
            alt_grammar
        };

        let cell = self.defs.get(&def_name).unwrap();
        *cell.borrow_mut() = grammar;
    }

    fn parse_map_grammar(&mut self, def_name: &String) -> (Grammar, bool) {
        let backus_naur = self.parse_named_backus();

        let grammar = backus_naur.to_grammar(def_name, &mut self.defs);

        let mut map_fn = String::new();
        let start;
        if self.char() == '{' {
            let mut brace_count = 1;
            start = self.pos();
            while brace_count != 0 {
                self.bump();
                map_fn.push(self.char());
                if self.char() == '}' {
                    brace_count -= 1;
                } else if self.char() == '{' {
                    brace_count += 1;
                }
            }
            map_fn.pop(); // Remove the closing brace
            self.bump_and_bump_space();
        } else {
            self.panic(GrammarErrorKind::MissingRuleProduction)
        };

        let bindings = self.get_bindings(&backus_naur, syn::parse_str("out").unwrap());

        use core::str::FromStr;
        let map_fn = proc_macro2::TokenStream::from_str(map_fn.as_str()).unwrap_or_else(|_| {
            self.panic_with_span(
                GrammarErrorKind::ImproperRuleProduction,
                Span::new(start, self.pos()),
            )
        });

        (
            Grammar::new(GrammarTerm::Map(
                quote! {
                    |out| Box::new({
                        use ::std::any::Any;
                        #(#bindings)*
                        #map_fn
                    })
                },
                grammar,
            )),
            backus_naur.is_recursive(def_name),
        )
    }

    fn parse_named_backus(&mut self) -> BackusNaur {
        let first = if self.char() == '<' {
            let mut name = String::new();
            self.bump();
            while self.char().is_alphanumeric() || self.char() == '_' {
                name.push(self.char());
                self.bump();
            }
            if self.char() == ':' {
                self.bump_and_bump_space();
                let inner = self.parse_backus();
                if self.char() == '>' {
                    self.bump_and_bump_space();
                    BackusNaur::Named(name, Box::new(inner))
                } else {
                    self.panic(GrammarErrorKind::ExpectedRightAngle)
                }
            } else {
                self.panic(GrammarErrorKind::EmptyTokenBindingName)
            }
        } else {
            self.parse_backus()
        };
        if self.char().is_uppercase()
            || self.char().is_lowercase()
            || self.char() == '('
            || self.char() == '<'
        {
            let second = self.parse_named_backus();
            BackusNaur::Seq(Box::new(first), Box::new(second))
        } else {
            first
        }
    }

    fn parse_backus(&mut self) -> BackusNaur {
        if self.char() == '(' {
            self.bump_and_bump_space();
            let inner = self.parse_backus();
            if self.bump_if(")*") {
                self.bump_space();
                BackusNaur::Star(Box::new(inner))
            } else {
                panic!("Expecting \")*\"");
            }
        } else {
            if self.char().is_lowercase() {
                let mut def = String::new();
                while self.char().is_lowercase() || self.char() == '_' {
                    def.push(self.char());
                    self.bump();
                }
                BackusNaur::Def(def)
            } else if self.char().is_uppercase() {
                let mut tok = String::new();
                while self.char().is_uppercase() || self.char() == '_' {
                    tok.push(self.char());
                    self.bump();
                }
                self.bump_space();
                BackusNaur::Token(tok)
            } else {
                self.panic(GrammarErrorKind::UnexpectedCharacter(self.char()))
            }
        }
    }

    fn get_bindings(&self, backus: &BackusNaur, value: TokenStream) -> Vec<TokenStream> {
        use BackusNaur::*;
        match backus {
            Seq(b1, b2) => {
                let mut v1 = self.get_bindings(
                    b1,
                    quote!(#value.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap().0),
                );
                let mut v2 = self.get_bindings(
                    b2,
                    quote!(#value.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap().1),
                );
                v1.append(&mut v2);
                v1
            }
            Named(name, b) => {
                let cast_type = self.get_type_cast(b);
                let name_ident: syn::Ident = syn::parse_str(name).unwrap();
                if matches!(**b, Token(..)) {
                    vec![quote! {
                        let #name_ident: #cast_type = #value
                            .downcast_ref::<LexTokenValue>()
                            .unwrap().clone().into();
                    }]
                } else {
                    vec![quote! {
                        let #name_ident: #cast_type = #value
                            .downcast_ref::<#cast_type>()
                            .unwrap().clone();
                    }]
                }
            }
            _ => Vec::new(),
        }
    }

    fn get_type_cast(&self, backus: &BackusNaur) -> TokenStream {
        use BackusNaur::*;
        match backus {
            Token(tok) => {
                let tok_ident = syn::parse_str::<syn::Ident>(tok).unwrap();
                match self.token_type_map.get(&tok_ident) {
                    None => self.panic(GrammarErrorKind::TokenDoesNotExist(tok.clone())),
                    Some(ty) => quote!(#ty),
                }
            }
            Def(name) => match self.return_types.get(name) {
                None => self.panic(GrammarErrorKind::DefinitionDoesNotExist(name.clone())),
                Some(ty) => quote!(#ty),
            },
            Seq(..) => {
                quote!((Box<dyn Any>, Box<dyn Any>))
            }
            Star(_) => {
                quote!(Vec<Box<dyn Any>>)
            }
            Named(_, b) => self.get_type_cast(b),
        }
    }

    fn panic(&self, kind: GrammarErrorKind) -> ! {
        panic!(
            "{}",
            GrammarError::new(
                self.file_name.clone(),
                self.span(),
                self.curr_line.clone(),
                kind
            )
        )
    }

    fn panic_with_span(&self, kind: GrammarErrorKind, span: Span) -> ! {
        panic!(
            "{}",
            GrammarError::new(self.file_name.clone(), span, self.curr_line.clone(), kind)
        )
    }
}

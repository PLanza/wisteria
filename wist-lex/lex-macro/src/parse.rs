use crate::error::{ParseError, ParseErrorKind};

use std::{
    cell::Cell,
    fs::File,
    io::{self, prelude::*, BufReader},
};

use wist_utils::{Position, Span};

enum ParserState {
    TokenDecs,
    RegularDefs,
    MatchRules,
    Done,
}

pub struct LexParser {
    /// The current position of the parser.
    file_name: String,
    pos: Cell<Position>,
    state: ParserState,
    lines: std::iter::Peekable<io::Lines<BufReader<File>>>,
    curr_line: String,
    line_offset: usize,
}

impl LexParser {
    pub fn new(path: String) -> io::Result<Self> {
        let file = File::open(path.clone())?;
        let mut lines = BufReader::new(file).lines().peekable();
        // TODO: Handle Error
        let curr_line = lines.next().unwrap().unwrap();

        Ok(LexParser {
            file_name: path.clone(),
            pos: Cell::new(Position::new(0, 1, 0)),
            state: ParserState::TokenDecs,
            lines,
            curr_line,
            line_offset: 0,
        })
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

            // TODO: Handle IO Error
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

    pub fn parse_token_decs(
        &mut self,
    ) -> (
        Vec<syn::Ident>,
        Vec<Option<syn::Ident>>,
        Vec<Option<syn::Type>>,
    ) {
        if !matches!(self.state, ParserState::TokenDecs) {
            self.panic(ParseErrorKind::TokenDecsParsed)
        }

        let mut tok_names: Vec<String> = Vec::new();
        let mut tok_ty_variants = Vec::new();
        let mut tok_tys = Vec::new();

        loop {
            if let Some((tok_name, tok_ty_variant, tok_type)) = self.parse_next_token_dec() {
                tok_names.push(tok_name);
                tok_tys.push(tok_type);
                tok_ty_variants.push(tok_ty_variant);
            } else {
                break;
            }
        }

        self.state = ParserState::RegularDefs;
        (
            tok_names
                .iter()
                .map(|name| syn::parse_str(name).unwrap())
                .collect(),
            tok_ty_variants,
            tok_tys,
        )
    }

    pub fn parse_regular_defs(&mut self) -> (Vec<String>, Vec<String>) {
        if matches!(self.state, ParserState::TokenDecs) {
            self.panic(ParseErrorKind::TokenDecsNotParsed)
        } else if matches!(self.state, ParserState::MatchRules) {
            self.panic(ParseErrorKind::RegularDefsParsed)
        }

        let mut def_names: Vec<String> = Vec::new();
        let mut regexes: Vec<String> = Vec::new();

        loop {
            if let Some((def_name, regex)) = self.parse_next_regular_def() {
                def_names.push(def_name);
                regexes.push(regex);
            } else {
                break;
            }
        }

        self.state = ParserState::MatchRules;
        (def_names, regexes)
    }

    pub fn parse_match_rules(
        &mut self,
    ) -> (
        Vec<String>,
        Vec<Option<syn::Ident>>,
        Vec<Option<proc_macro2::TokenStream>>,
    ) {
        if !matches!(self.state, ParserState::MatchRules) {
            self.panic(ParseErrorKind::RegularDefsNotParsed)
        }

        let mut regexes: Vec<String> = Vec::new();
        let mut token_kinds = Vec::new();
        let mut token_contents = Vec::new();

        loop {
            if let Some((regex, token_kind, token_content)) = self.parse_next_match_rule() {
                regexes.push(regex);
                token_kinds.push(
                    token_kind.map(|kind| syn::parse_str::<syn::Ident>(kind.as_str()).unwrap()),
                );
                use core::str::FromStr;
                token_contents.push(
                    token_content.map(|content| {
                        proc_macro2::TokenStream::from_str(content.as_str()).unwrap()
                    }),
                );
            } else {
                break;
            }
        }

        self.state = ParserState::Done;

        (regexes, token_kinds, token_contents)
    }

    fn parse_next_token_dec(&mut self) -> Option<(String, Option<syn::Ident>, Option<syn::Type>)> {
        if self.parse_end_of_section() {
            return None;
        }

        let mut tok_name = String::new();
        while !self.is_eof() && self.char().is_uppercase() {
            tok_name.push(self.char());
            self.bump();
        }
        self.bump_space();

        if tok_name.is_empty() {
            return None;
        }

        let mut tok_type = String::new();

        if self.char() == '(' {
            let start_pos = self.pos();
            self.bump_and_bump_space();

            let type_start = self.pos();
            while self.char().is_alphanumeric() {
                tok_type.push(self.char());
                self.bump();
            }
            self.bump_space();
            let type_end = self.pos();

            if self.char() != ')' {
                self.panic_with_span(
                    ParseErrorKind::UnclosedParentheses,
                    Span::new(start_pos, self.pos()),
                )
            } else {
                self.bump_and_bump_space();
                if syn::parse_str::<syn::Type>(&tok_type.as_str()).is_err() {
                    self.panic_with_span(
                        ParseErrorKind::InvalidType,
                        Span::new(type_start, type_end),
                    )
                }
            }
        }

        if self.char() != ',' {
            if !self.parse_end_of_section() {
                self.panic(ParseErrorKind::ExpectedComma)
            }
        } else {
            self.bump_and_bump_space();
        }

        if tok_type.is_empty() {
            return Some((tok_name, None, None));
        }

        let ty = syn::parse_str::<syn::Type>(&tok_type.as_str()).ok();

        let first_char = tok_type.remove(0);
        tok_type.insert(0, first_char.to_uppercase().next().unwrap());
        let tok_type = syn::parse_str::<syn::Ident>(&tok_type).ok();

        Some((tok_name, tok_type, ty))
    }

    fn parse_next_regular_def(&mut self) -> Option<(String, String)> {
        if self.parse_end_of_section() {
            return None;
        }

        let mut def_name = String::new();
        while !self.is_eof() && self.char().is_lowercase() {
            def_name.push(self.char());
            self.bump();
        }
        self.bump_space();

        let mut regex = String::new();
        if self.char() == ':' {
            self.bump_and_bump_space();
            while !self.is_end_of_line() {
                regex.push(self.char());
                self.bump();
            }
            regex.push(self.char());
            self.bump_and_bump_space();

            Some((def_name, regex))
        } else {
            self.panic(ParseErrorKind::EmptyRegularDef);
            None
        }
    }

    fn parse_next_match_rule(&mut self) -> Option<(String, Option<String>, Option<String>)> {
        if self.is_eof() {
            return None;
        }

        let mut regex = String::new();
        let mut tok_kind = String::new();
        let mut tok_content = String::new();

        while !self.is_end_of_line() {
            if self.bump_if("=>") {
                break;
            }
            regex.push(self.char());
            self.bump();
        }
        self.bump_space();
        regex = regex.trim().to_string();

        if self.is_end_of_line() && self.char() == '_' {
            self.bump_and_bump_space();
            return Some((regex, None, None));
        }

        while !self.is_end_of_line() && self.char().is_uppercase() {
            tok_kind.push(self.char());
            self.bump();
        }
        if self.char().is_uppercase() {
            tok_kind.push(self.char());
        }

        if tok_kind.is_empty() {
            self.panic(ParseErrorKind::MatchRuleMissingKind);
        }
        if self.is_end_of_line() {
            self.bump_and_bump_space();
            return Some((regex, Some(tok_kind), None));
        }

        if self.char() == '(' {
            self.bump();

            let mut open_parens = 1;
            while self.char() != ')' || open_parens > 1 {
                if self.char() == '(' {
                    open_parens += 1;
                } else if self.char() == ')' {
                    open_parens -= 1;
                }
                tok_content.push(self.char());
                self.bump();
            }
            self.bump_and_bump_space();
        } else {
            self.panic(ParseErrorKind::InvalidMatchRuleContent);
        }

        return Some((regex, Some(tok_kind), Some(tok_content)));
    }

    fn parse_end_of_section(&mut self) -> bool {
        self.bump_space();
        for _ in 0..3 {
            if self.char() != '-' {
                return false;
            }
            self.bump();
        }
        self.bump_space();
        true
    }

    fn panic(&self, kind: ParseErrorKind) {
        panic!(
            "{}",
            ParseError::new(
                self.file_name.clone(),
                self.span(),
                self.curr_line.clone(),
                kind
            )
        )
    }

    fn panic_with_span(&self, kind: ParseErrorKind, span: Span) {
        panic!(
            "{}",
            ParseError::new(self.file_name.clone(), span, self.curr_line.clone(), kind)
        )
    }
}

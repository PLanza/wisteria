use crate::error::{ParseError, ParseErrorKind};

use std::{
    cell::Cell,
    fs::File,
    io::{self, prelude::*, BufReader},
};

use wist_utils::{Position, Span};

const VALID_TOKEN_TYPES: [&'static str; 5] = ["", "int", "float", "string", "bool"];

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

    /// Return the current line number of the parser.
    ///
    /// The line number starts at `1`.
    fn line(&self) -> usize {
        self.pos.get().line
    }

    /// Return the current column of the parser.
    ///
    /// The column number starts at `1` and is reset whenever a `\n` is seen.
    fn column(&self) -> usize {
        self.pos.get().column
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

    fn bump_space(&mut self) {
        while !self.is_eof() {
            if self.curr_line.is_empty() {
                self.bump();
            } else if self.char().is_whitespace() {
                self.bump();
            } else {
                break;
            }
        }
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

    /// Create a span that covers the current character.
    fn span_char(&self) -> Span {
        let mut next = Position {
            offset: self.offset().checked_add(self.char().len_utf8()).unwrap(),
            line: self.line(),
            column: self.column().checked_add(1).unwrap(),
        };
        if self.char() == '\n' {
            next.line += 1;
            next.column = 1;
        }
        Span::new(self.pos(), next)
    }

    pub fn parse_token_decs(&mut self) -> proc_macro::TokenStream {
        if !matches!(self.state, ParserState::TokenDecs) {
            self.panic(ParseErrorKind::TokenDecsParsed)
        }

        let mut token_names: Vec<String> = Vec::new();
        let mut token_types: Vec<String> = Vec::new();

        loop {
            if let Some((tok_name, tok_type)) = self.parse_next_token_dec() {
                token_names.push(tok_name);
                token_types.push(tok_type);
            } else {
                break;
            }
        }

        self.state = ParserState::RegularDefs;
        crate::gen_token_enum(token_names, token_types)
    }

    pub fn parse_regular_defs(&mut self) {
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
    }

    pub fn parse_match_rules(&mut self) {
        if !matches!(self.state, ParserState::MatchRules) {
            self.panic(ParseErrorKind::RegularDefsNotParsed)
        }

        let mut regexes: Vec<String> = Vec::new();
        let mut tokens: Vec<String> = Vec::new();

        loop {
            if let Some((regex, token)) = self.parse_next_match_rule() {
                regexes.push(regex);
                tokens.push(token);
            } else {
                break;
            }
        }

        self.state = ParserState::Done;
    }

    fn parse_next_token_dec(&mut self) -> Option<(String, String)> {
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
        let mut type_start = self.pos();
        let mut type_end = self.pos();
        if self.char() == '(' {
            let start_pos = self.pos();
            self.bump_and_bump_space();
            type_start = self.pos();
            while self.char().is_lowercase() {
                tok_type.push(self.char());
                type_end = self.pos();
                self.bump();
            }
            self.bump_space();

            if self.char() != ')' {
                self.panic_with_span(
                    ParseErrorKind::UnclosedParentheses,
                    Span::new(start_pos, self.pos()),
                )
            } else {
                self.bump_and_bump_space();
            }
        }

        if self.char() != ',' && !self.parse_end_of_section() {
            self.panic(ParseErrorKind::ExpectedComma)
        } else {
            self.bump_and_bump_space();
        }

        if !VALID_TOKEN_TYPES.contains(&tok_type.as_str()) {
            self.panic_with_span(ParseErrorKind::InvalidType, Span::new(type_start, type_end))
        }
        Some((tok_name, tok_type))
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

    fn parse_next_match_rule(&mut self) -> Option<(String, String)> {
        if self.is_eof() {
            return None;
        }

        let mut regex = String::new();
        let mut token = String::new();

        // 1. Advance until we reach =>
        // 2. Assume parsed string is the regex
        // 3. Advance the rest
        // 4. If we encounter => then add just parsed to regex
        // 5. Repeat 3-4 until end of line
        while !self.is_end_of_line() {
            if self.bump_if("=>") {
                regex.push_str(&token);
                regex.push_str("=>");
                token = String::new();
                continue;
            }
            token.push(self.char());
            self.bump();
        }
        if token.is_empty() {
            self.panic(ParseErrorKind::EmptyMatchRule);
        }
        regex = regex.strip_suffix("=>").unwrap().to_string();

        token.push(self.char());
        self.bump_and_bump_space();

        regex = regex.trim().to_string();
        token = token.trim().to_string();

        return Some((regex, token));
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

use wist_utils::Span;

pub(crate) struct ParseError {
    file: String,
    span: Span,
    line: String,
    kind: ParseErrorKind,
}

pub(crate) enum ParseErrorKind {
    TokenDecsParsed,
    TokenDecsNotParsed,
    RegularDefsParsed,
    RegularDefsNotParsed,
    UnclosedParentheses,
    ExpectedComma,
    InvalidType,
    EmptyRegularDef,
    EmptyMatchRule,
}

impl ParseError {
    pub(crate) fn new(file: String, span: Span, line: String, kind: ParseErrorKind) -> Self {
        Self {
            file,
            span,
            line,
            kind,
        }
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Parse error in lex file {}:", self.file)?;

        let mut line_str = String::new();

        line_str.push_str(&self.span.start.line.to_string());
        let line_length = line_str.len();

        line_str.push_str(": ");
        line_str.push_str(&self.line);
        line_str.push('\n');

        for _ in 0..(line_length + 2 + self.span.start.column) {
            line_str.push(' ');
        }
        let span_len = self.span.end.column.saturating_sub(self.span.start.column);
        for _ in 0..1.max(span_len) {
            line_str.push('^')
        }
        line_str.push('\n');
        write!(f, "{}", line_str)?;

        writeln!(f, "error: {}", self.kind)
    }
}

impl std::fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use self::ParseErrorKind::*;
        match *self {
            TokenDecsParsed => write!(f, "already parsed token declarations"),
            TokenDecsNotParsed => write!(f, "token declarations not yet parsed"),
            RegularDefsParsed => write!(f, "already parsed regular definitions"),
            RegularDefsNotParsed => write!(f, "regular definitions not yet parsed"),
            UnclosedParentheses => write!(f, "unclosed parentheses"),
            ExpectedComma => write!(f, "expected a comma"),
            InvalidType => write!(f, "invalid token type"),
            EmptyRegularDef => write!(f, "regular definition is empty"),
            EmptyMatchRule => write!(f, "match rule is empty"),
        }
    }
}

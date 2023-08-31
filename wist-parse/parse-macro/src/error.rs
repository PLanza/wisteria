use wist_utils::Span;

pub(crate) struct GrammarError {
    file: String,
    span: Span,
    line: String,
    kind: GrammarErrorKind,
}

pub(crate) enum GrammarErrorKind {
    EmptyFile,
}

impl GrammarError {
    pub(crate) fn new(file: String, span: Span, line: String, kind: GrammarErrorKind) -> Self {
        Self {
            file,
            span,
            line,
            kind,
        }
    }
}

impl std::fmt::Display for GrammarError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Parse error in lex file \"{}\":", self.file)?;

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

impl std::fmt::Display for GrammarErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use self::GrammarErrorKind::*;
        match *self {
            EmptyFile => write!(f, "file is empty"),
        }
    }
}

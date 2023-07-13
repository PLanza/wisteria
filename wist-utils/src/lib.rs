use core::cmp::Ordering;

/// Span represents the position information of a single AST item.
///
/// All span positions are absolute byte offsets that can be used on the
/// original regular expression that was parsed.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Span {
    /// The start byte offset.
    pub start: Position,
    /// The end byte offset.
    pub end: Position,
}

impl core::fmt::Debug for Span {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Span({:?}, {:?})", self.start, self.end)
    }
}

impl Ord for Span {
    fn cmp(&self, other: &Span) -> Ordering {
        (&self.start, &self.end).cmp(&(&other.start, &other.end))
    }
}

impl PartialOrd for Span {
    fn partial_cmp(&self, other: &Span) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// A single position in a regular expression.
///
/// A position encodes one half of a span, and include the byte offset, line
/// number and column number.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Position {
    /// The absolute offset of this position, starting at `0` from the
    /// beginning of the regular expression pattern string.
    pub offset: usize,
    /// The line number, starting at `1`.
    pub line: usize,
    /// The approximate column number, starting at `1`.
    pub column: usize,
}

impl core::fmt::Debug for Position {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "Position(o: {:?}, l: {:?}, c: {:?})",
            self.offset, self.line, self.column
        )
    }
}

impl Ord for Position {
    fn cmp(&self, other: &Position) -> Ordering {
        self.offset.cmp(&other.offset)
    }
}

impl PartialOrd for Position {
    fn partial_cmp(&self, other: &Position) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Span {
    /// Create a new span with the given positions.
    pub fn new(start: Position, end: Position) -> Span {
        Span { start, end }
    }

    /// Create a new span using the given position as the start and end.
    pub fn splat(pos: Position) -> Span {
        Span::new(pos, pos)
    }

    /// Create a new span by replacing the starting the position with the one
    /// given.
    pub fn with_start(self, pos: Position) -> Span {
        Span { start: pos, ..self }
    }

    /// Create a new span by replacing the ending the position with the one
    /// given.
    pub fn with_end(self, pos: Position) -> Span {
        Span { end: pos, ..self }
    }

    /// Returns true if and only if this span occurs on a single line.
    pub fn is_one_line(&self) -> bool {
        self.start.line == self.end.line
    }

    /// Returns true if and only if this span is empty. That is, it points to
    /// a single position in the concrete syntax of a regular expression.
    pub fn is_empty(&self) -> bool {
        self.start.offset == self.end.offset
    }
}

impl Position {
    /// Create a new position with the given information.
    ///
    /// `offset` is the absolute offset of the position, starting at `0` from
    /// the beginning of the regular expression pattern string.
    ///
    /// `line` is the line number, starting at `1`.
    ///
    /// `column` is the approximate column number, starting at `1`.
    pub fn new(offset: usize, line: usize, column: usize) -> Position {
        Position { offset, line, column }
    }
}


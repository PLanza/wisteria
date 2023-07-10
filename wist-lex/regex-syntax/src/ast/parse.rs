/*!
This module provides a regular expression parser.
*/

use core::{
    borrow::Borrow,
    cell::{Cell, RefCell},
};

use alloc::{
    boxed::Box,
    string::ToString,
    vec,
    vec::Vec,
};

use crate::{
    ast::{self, Ast, Position, Span},
    either::Either,
    is_escapeable_character, is_meta_character,
};

type Result<T> = core::result::Result<T, ast::Error>;

/// A primitive is an expression with no sub-expressions. This includes
/// literals, assertions and non-set character classes. This representation
/// is used as intermediate state in the parser.
///
/// This does not include ASCII character classes, since they can only appear
/// within a set character class.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Primitive {
    Literal(ast::Literal),
    Dot(Span),
}

impl Primitive {
    /// Return the span of this primitive.
    fn span(&self) -> &Span {
        match *self {
            Primitive::Literal(ref x) => &x.span,
            Primitive::Dot(ref span) => span,
        }
    }

    /// Convert this primitive into a proper AST.
    fn into_ast(self) -> Ast {
        match self {
            Primitive::Literal(lit) => Ast::Literal(lit),
            Primitive::Dot(span) => Ast::Dot(span),
        }
    }

    /// Convert this primitive into an item in a character class.
    ///
    /// If this primitive is not a legal item (i.e., an assertion or a dot),
    /// then return an error.
    fn into_class_set<P: Borrow<Parser>>(
        self,
        p: &ParserI<'_, P>,
    ) -> Result<ast::ClassSet> {
        use self::Primitive::*;
        use crate::ast::ClassSet;

        match self {
            Literal(lit) => Ok(ClassSet::Literal(lit)),
            x => Err(p.error(*x.span(), ast::ErrorKind::ClassEscapeInvalid)),
        }
    }

    /// Convert this primitive into a literal in a character class. In
    /// particular, literals are the only valid items that can appear in
    /// ranges.
    ///
    /// If this primitive is not a legal item (i.e., a class, assertion or a
    /// dot), then return an error.
    fn into_class_literal<P: Borrow<Parser>>(
        self,
        p: &ParserI<'_, P>,
    ) -> Result<ast::Literal> {
        use self::Primitive::*;

        match self {
            Literal(lit) => Ok(lit),
            x => Err(p.error(*x.span(), ast::ErrorKind::ClassRangeLiteral)),
        }
    }
}

/// A regular expression parser.
///
/// This parses a string representation of a regular expression into an
/// abstract syntax tree. The size of the tree is proportional to the length
/// of the regular expression pattern.
///
/// A `Parser` can be configured in more detail via a [`ParserBuilder`].
#[derive(Clone, Debug)]
pub struct Parser {
    /// The current position of the parser.
    pos: Cell<Position>,
    /// A stack of grouped sub-expressions, including alternations.
    stack_group: RefCell<Vec<GroupState>>,
    /// A stack of nested character classes. This is only non-empty when
    /// parsing a class.
    stack_class: RefCell<Vec<ClassState>>,
}

/// ParserI is the internal parser implementation.
///
/// We use this separate type so that we can carry the provided pattern string
/// along with us. In particular, a `Parser` internal state is not tied to any
/// one pattern, but `ParserI` is.
///
/// This type also lets us use `ParserI<&Parser>` in production code while
/// retaining the convenience of `ParserI<Parser>` for tests, which sometimes
/// work against the internal interface of the parser.
#[derive(Clone, Debug)]
struct ParserI<'s, P> {
    /// The parser state/configuration.
    parser: P,
    /// The full regular expression provided by the user.
    pattern: &'s str,
}

/// GroupState represents a single stack frame while parsing nested groups
/// and alternations. Each frame records the state up to an opening parenthesis
/// or a alternating bracket `|`.
#[derive(Clone, Debug)]
enum GroupState {
    /// This state is pushed whenever an opening group is found.
    Group {
        /// The concatenation immediately preceding the opening group.
        concat: ast::Concat,
        /// The group that has been opened. Its sub-AST is always empty.
        group: ast::Group,
    },
    /// This state is pushed whenever a new alternation branch is found. If
    /// an alternation branch is found and this state is at the top of the
    /// stack, then this state should be modified to include the new
    /// alternation.
    Alternation(ast::Alternation),
}

/// ClassState represents a single stack frame while parsing character classes.
/// Each frame records the state up to an intersection, difference, symmetric
/// difference or nested class.
///
/// Note that a parser's character class stack is only non-empty when parsing
/// a character class. In all other cases, it is empty.
#[derive(Clone, Debug)]
struct ClassState {
    /// This state is pushed whenever an opening bracket is found.
    ///
    /// The union of class items immediately preceding this class.
    union: ast::ClassSetUnion,
    /// The class that has been opened. Typically this just corresponds
    /// to the `[`, but it can also include `[^` since `^` indicates
    /// negation of the class.
    set: ast::Class,
}

impl Parser {
    /// Create a new parser with a default configuration.
    ///
    /// The parser can be run with either the `parse` or `parse_with_comments`
    /// methods. The parse methods return an abstract syntax tree.
    pub fn new() -> Self {
        Parser {
            pos: Cell::new(Position { offset: 0, line: 1, column: 1 }),
            stack_group: RefCell::new(vec![]),
            stack_class: RefCell::new(vec![]),
        }
    }

    /// Parse the regular expression into an abstract syntax tree.
    pub fn parse(&mut self, pattern: &str) -> Result<Ast> {
        ParserI::new(self, pattern).parse()
    }

    /// Reset the internal state of a parser.
    ///
    /// This is called at the beginning of every parse. This prevents the
    /// parser from running with inconsistent state (say, if a previous
    /// invocation returned an error and the parser is reused).
    fn reset(&self) {
        // These settings should be in line with the construction
        // in `ParserBuilder::build`.
        self.pos.set(Position { offset: 0, line: 1, column: 1 });
        self.stack_group.borrow_mut().clear();
        self.stack_class.borrow_mut().clear();
    }
}

impl<'s, P: Borrow<Parser>> ParserI<'s, P> {
    /// Build an internal parser from a parser configuration and a pattern.
    fn new(parser: P, pattern: &'s str) -> ParserI<'s, P> {
        ParserI { parser, pattern }
    }

    /// Return a reference to the parser state.
    fn parser(&self) -> &Parser {
        self.parser.borrow()
    }

    /// Return a reference to the pattern being parsed.
    fn pattern(&self) -> &str {
        self.pattern.borrow()
    }

    /// Create a new error with the given span and error type.
    fn error(&self, span: Span, kind: ast::ErrorKind) -> ast::Error {
        ast::Error { kind, pattern: self.pattern().to_string(), span }
    }

    /// Return the current offset of the parser.
    ///
    /// The offset starts at `0` from the beginning of the regular expression
    /// pattern string.
    fn offset(&self) -> usize {
        self.parser().pos.get().offset
    }

    /// Return the current line number of the parser.
    ///
    /// The line number starts at `1`.
    fn line(&self) -> usize {
        self.parser().pos.get().line
    }

    /// Return the current column of the parser.
    ///
    /// The column number starts at `1` and is reset whenever a `\n` is seen.
    fn column(&self) -> usize {
        self.parser().pos.get().column
    }

    /// Return the character at the current position of the parser.
    ///
    /// This panics if the current position does not point to a valid char.
    fn char(&self) -> char {
        self.char_at(self.offset())
    }

    /// Return the character at the given position.
    ///
    /// This panics if the given position does not point to a valid char.
    fn char_at(&self, i: usize) -> char {
        self.pattern()[i..]
            .chars()
            .next()
            .unwrap_or_else(|| panic!("expected char at offset {}", i))
    }

    /// Bump the parser to the next Unicode scalar value.
    ///
    /// If the end of the input has been reached, then `false` is returned.
    fn bump(&self) -> bool {
        if self.is_eof() {
            return false;
        }
        let Position { mut offset, mut line, mut column } = self.pos();
        if self.char() == '\n' {
            line = line.checked_add(1).unwrap();
            column = 1;
        } else {
            column = column.checked_add(1).unwrap();
        }
        offset += self.char().len_utf8();
        self.parser().pos.set(Position { offset, line, column });
        self.pattern()[self.offset()..].chars().next().is_some()
    }

    /// Bump the parser, and if the `x` flag is enabled, bump through any
    /// subsequent spaces. Return true if and only if the parser is not at
    /// EOF.
    fn bump_and_bump_space(&self) -> bool {
        if !self.bump() {
            return false;
        }
        self.bump_space();
        !self.is_eof()
    }

    /// This should be used selectively throughout the parser where
    /// arbitrary whitespace is permitted when the `x` flag is enabled. For
    /// example, `{   5  , 6}` is equivalent to `{5,6}`.
    fn bump_space(&self) {
        while !self.is_eof() {
            if self.char().is_whitespace() {
                self.bump();
            } else {
                break;
            }
        }
    }

    /// Like peek, but will ignore spaces when the parser is in whitespace
    /// insensitive mode.
    fn peek_space(&self) -> Option<char> {
        if self.is_eof() {
            return None;
        }
        let mut start = self.offset() + self.char().len_utf8();
        for (i, c) in self.pattern()[start..].char_indices() {
            if c.is_whitespace() {
                continue;
            } else {
                start += i;
                break;
            }
        }
        self.pattern()[start..].chars().next()
    }

    /// Returns true if the next call to `bump` would return false.
    fn is_eof(&self) -> bool {
        self.offset() == self.pattern().len()
    }

    /// Return the current position of the parser, which includes the offset,
    /// line and column.
    fn pos(&self) -> Position {
        self.parser().pos.get()
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

    /// Parse and push a single alternation on to the parser's internal stack.
    /// If the top of the stack already has an alternation, then add to that
    /// instead of pushing a new one.
    ///
    /// The concatenation given corresponds to a single alternation branch.
    /// The concatenation returned starts the next branch and is empty.
    ///
    /// This assumes the parser is currently positioned at `|` and will advance
    /// the parser to the character following `|`.
    #[inline(never)]
    fn push_alternate(&self, mut concat: ast::Concat) -> Result<ast::Concat> {
        assert_eq!(self.char(), '|');
        concat.span.end = self.pos();
        self.push_or_add_alternation(concat);
        self.bump();
        Ok(ast::Concat { span: self.span(), asts: vec![] })
    }

    /// Pushes or adds the given branch of an alternation to the parser's
    /// internal stack of state.
    fn push_or_add_alternation(&self, concat: ast::Concat) {
        use self::GroupState::*;

        let mut stack = self.parser().stack_group.borrow_mut();
        if let Some(&mut Alternation(ref mut alts)) = stack.last_mut() {
            alts.asts.push(concat.into_ast());
            return;
        }
        stack.push(Alternation(ast::Alternation {
            span: Span::new(concat.span.start, self.pos()),
            asts: vec![concat.into_ast()],
        }));
    }

    /// Parse and push a group AST (and its parent concatenation) on to the
    /// parser's internal stack. Return a fresh concatenation corresponding
    /// to the group's sub-AST.
    ///
    /// This assumes that the parser is currently positioned on the opening
    /// parenthesis. It advances the parser to the character at the start
    /// of the sub-expression (or adjoining expression).
    ///
    /// If there was a problem parsing the start of the group, then an error
    /// is returned.
    #[inline(never)]
    fn push_group(&self, concat: ast::Concat) -> Result<ast::Concat> {
        assert_eq!(self.char(), '(');
        let group = self.parse_group()?; 
        self.parser().stack_group.borrow_mut().push(
            GroupState::Group {
                concat,
                group,
            },
        );
        Ok(ast::Concat { span: self.span(), asts: vec![] })
    }

    /// Pop a group AST from the parser's internal stack and set the group's
    /// AST to the given concatenation. Return the concatenation containing
    /// the group.
    ///
    /// This assumes that the parser is currently positioned on the closing
    /// parenthesis and advances the parser to the character following the `)`.
    ///
    /// If no such group could be popped, then an unopened group error is
    /// returned.
    #[inline(never)]
    fn pop_group(&self, mut group_concat: ast::Concat) -> Result<ast::Concat> {
        use self::GroupState::*;

        assert_eq!(self.char(), ')');
        let mut stack = self.parser().stack_group.borrow_mut();
        let (mut prior_concat, mut group, alt) = match stack.pop() {
            Some(Group { concat, group }) => {
                (concat, group, None)
            }
            Some(Alternation(alt)) => match stack.pop() {
                Some(Group { concat, group }) => {
                    (concat, group, Some(alt))
                }
                None | Some(Alternation(_)) => {
                    return Err(self.error(
                        self.span_char(),
                        ast::ErrorKind::GroupUnopened,
                    ));
                }
            },
            None => {
                return Err(self
                    .error(self.span_char(), ast::ErrorKind::GroupUnopened));
            }
        };
        group_concat.span.end = self.pos();
        self.bump();
        group.span.end = self.pos();
        match alt {
            Some(mut alt) => {
                alt.span.end = group_concat.span.end;
                alt.asts.push(group_concat.into_ast());
                group.ast = Box::new(alt.into_ast());
            }
            None => {
                group.ast = Box::new(group_concat.into_ast());
            }
        }
        prior_concat.asts.push(Ast::Group(group));
        Ok(prior_concat)
    }

    /// Pop the last state from the parser's internal stack, if it exists, and
    /// add the given concatenation to it. There either must be no state or a
    /// single alternation item on the stack. Any other scenario produces an
    /// error.
    ///
    /// This assumes that the parser has advanced to the end.
    #[inline(never)]
    fn pop_group_end(&self, mut concat: ast::Concat) -> Result<Ast> {
        concat.span.end = self.pos();
        let mut stack = self.parser().stack_group.borrow_mut();
        let ast = match stack.pop() {
            None => Ok(concat.into_ast()),
            Some(GroupState::Alternation(mut alt)) => {
                alt.span.end = self.pos();
                alt.asts.push(concat.into_ast());
                Ok(Ast::Alternation(alt))
            }
            Some(GroupState::Group { group, .. }) => {
                return Err(
                    self.error(group.span, ast::ErrorKind::GroupUnclosed)
                );
            }
        };
        // If we try to pop again, there should be nothing.
        match stack.pop() {
            None => ast,
            Some(GroupState::Alternation(_)) => {
                // This unreachable is unfortunate. This case can't happen
                // because the only way we can be here is if there were two
                // `GroupState::Alternation`s adjacent in the parser's stack,
                // which we guarantee to never happen because we never push a
                // `GroupState::Alternation` if one is already at the top of
                // the stack.
                unreachable!()
            }
            Some(GroupState::Group { group, .. }) => {
                Err(self.error(group.span, ast::ErrorKind::GroupUnclosed))
            }
        }
    }

    /// Parse the opening of a character class and push the current class
    /// parsing context onto the parser's stack. This assumes that the parser
    /// is positioned at an opening `[`. The given union should correspond to
    /// the union of set items built up before seeing the `[`.
    ///
    /// If there was a problem parsing the opening of the class, then an error
    /// is returned. Otherwise, a new union of set items for the class is
    /// returned (which may be populated with either a `]` or a `-`).
    #[inline(never)]
    fn push_class_open(
        &self,
        parent_union: ast::ClassSetUnion,
    ) -> Result<ast::ClassSetUnion> {
        assert_eq!(self.char(), '[');

        let (nested_set, nested_union) = self.parse_set_class_open()?;
        self.parser()
            .stack_class
            .borrow_mut()
            .push(ClassState { union: parent_union, set: nested_set });
        Ok(nested_union)
    }

    /// Pop a character class set from the character class parser stack. If the
    /// top of the stack is just an item (not an operation), then return the
    /// given set unchanged. If the top of the stack is an operation, then the
    /// given set will be used as the rhs of the operation on the top of the
    /// stack. In that case, the binary operation is returned as a set.
    #[inline(never)]
    fn pop_class_op(&self, rhs: ast::ClassSet) -> ast::ClassSet {
        let mut stack = self.parser().stack_class.borrow_mut();
        match stack.pop() {
            Some(state) => {
                stack.push(state);
                return rhs;
            }
            None => unreachable!(),
        };
    }

    /// Parse the end of a character class set and pop the character class
    /// parser stack. The union given corresponds to the last union built
    /// before seeing the closing `]`. The union returned corresponds to the
    /// parent character class set with the nested class added to it.
    ///
    /// This assumes that the parser is positioned at a `]` and will advance
    /// the parser to the byte immediately following the `]`.
    ///
    /// If the stack is empty after popping, then this returns the final
    /// "top-level" character class AST (where a "top-level" character class
    /// is one that is not nested inside any other character class).
    ///
    /// If there is no corresponding opening bracket on the parser's stack,
    /// then an error is returned.
    #[inline(never)]
    fn pop_class(
        &self,
        nested_union: ast::ClassSetUnion,
    ) -> Result<Either<ast::ClassSetUnion, ast::Class>> {
        assert_eq!(self.char(), ']');

        let item = nested_union.into_item();
        let prevset = self.pop_class_op(item);
        let mut stack = self.parser().stack_class.borrow_mut();
        match stack.pop() {
            None => {
                // We can never observe an empty stack:
                //
                // 1) We are guaranteed to start with a non-empty stack since
                //    the character class parser is only initiated when it sees
                //    a `[`.
                // 2) If we ever observe an empty stack while popping after
                //    seeing a `]`, then we signal the character class parser
                //    to terminate.
                panic!("unexpected empty character class stack")
            }
            Some(ClassState { mut union, mut set }) => {
                self.bump();
                set.span.end = self.pos();
                set.kind = prevset;
                if stack.is_empty() {
                    Ok(Either::Right(set))
                } else {
                    union.push(ast::ClassSet::Bracketed(Box::new(set)));
                    Ok(Either::Left(union))
                }
            }
        }
    }

    /// Return an "unclosed class" error whose span points to the most
    /// recently opened class.
    ///
    /// This should only be called while parsing a character class.
    #[inline(never)]
    fn unclosed_class_error(&self) -> ast::Error {
        for state in self.parser().stack_class.borrow().iter().rev() {
            return self.error(state.set.span, ast::ErrorKind::ClassUnclosed);
        }
        // We are guaranteed to have a non-empty stack with at least
        // one open bracket, so we should never get here.
        panic!("no open character class found")
    }
}

impl<'s, P: Borrow<Parser>> ParserI<'s, P> {

    /// Parse the regular expression and return an abstract syntax tree
    fn parse(&self) -> Result<Ast> {
        assert_eq!(self.offset(), 0, "parser can only be used once");
        self.parser().reset();
        let mut concat = ast::Concat { span: self.span(), asts: vec![] };
        loop {
            self.bump_space();
            if self.is_eof() {
                break;
            }
            match self.char() {
                '(' => concat = self.push_group(concat)?,
                ')' => concat = self.pop_group(concat)?,
                '|' => concat = self.push_alternate(concat)?,
                '[' => {
                    let class = self.parse_set_class()?;
                    concat.asts.push(Ast::Class(class));
                }
                '?' => {
                    concat = self.parse_uncounted_repetition(
                        concat,
                        ast::RepetitionKind::ZeroOrOne,
                    )?;
                }
                '*' => {
                    concat = self.parse_uncounted_repetition(
                        concat,
                        ast::RepetitionKind::ZeroOrMore,
                    )?;
                }
                '+' => {
                    concat = self.parse_uncounted_repetition(
                        concat,
                        ast::RepetitionKind::OneOrMore,
                    )?;
                }
                '{' => {
                    concat.asts.push(Ast::Definition(self.parse_definition()?));
                }
                _ => concat.asts.push(self.parse_primitive()?.into_ast()),
            }
        }
        self.pop_group_end(concat)
    }

    /// Parses an uncounted repetition operation. An uncounted repetition
    /// operator includes ?, * and +, but does not include the {m,n} syntax.
    /// The given `kind` should correspond to the operator observed by the
    /// caller.
    ///
    /// This assumes that the parser is currently positioned at the repetition
    /// operator and advances the parser to the first character after the
    /// operator. (Note that the operator may include a single additional `?`,
    /// which makes the operator ungreedy.)
    ///
    /// The caller should include the concatenation that is being built. The
    /// concatenation returned includes the repetition operator applied to the
    /// last expression in the given concatenation.
    #[inline(never)]
    fn parse_uncounted_repetition(
        &self,
        mut concat: ast::Concat,
        kind: ast::RepetitionKind,
    ) -> Result<ast::Concat> {
        assert!(
            self.char() == '?' || self.char() == '*' || self.char() == '+'
        );
        let op_start = self.pos();
        let ast = match concat.asts.pop() {
            Some(ast) => ast,
            None => {
                return Err(
                    self.error(self.span(), ast::ErrorKind::RepetitionMissing)
                )
            }
        };
        match ast {
            Ast::Empty(_) => {
                return Err(
                    self.error(self.span(), ast::ErrorKind::RepetitionMissing)
                )
            }
            _ => {}
        }
        self.bump();
        concat.asts.push(Ast::Repetition(ast::Repetition {
            span: ast.span().with_end(self.pos()),
            op: ast::RepetitionOp {
                span: Span::new(op_start, self.pos()),
                kind,
            },
            ast: Box::new(ast),
        }));
        Ok(concat)
    }


    #[inline(never)]
    fn parse_definition(
        &self,
    ) -> Result<ast::Definition> {
        assert!(self.char() == '{');
        let start = self.pos();
        let mut name = String::new();
        loop {
            self.bump();
            if self.is_eof() {
                return Err(self.error(
                    Span::new(start, self.pos()),
                    ast::ErrorKind::DefinitionUnclosed,
                ))
            }
            match self.char() {
                '}' => {
                    self.bump();
                    return Ok(ast::Definition { 
                        span: Span::new(start, self.pos()),
                        name,
                    })
                }
                c => name.push(c),
            }
        }
    }

    /// Parse a group (which contains a sub-expression) or a set of flags.
    ///
    /// If a group was found, then it is returned with an empty AST. If a set
    /// of flags is found, then that set is returned.
    ///
    /// The parser should be positioned at the opening parenthesis.
    ///
    /// This advances the parser to the character before the start of the
    /// sub-expression (in the case of a group) or to the closing parenthesis
    /// immediately following the set of flags.
    #[inline(never)]
    fn parse_group(&self) -> Result<ast::Group> {
        assert_eq!(self.char(), '(');
        let open_span = self.span_char();
        self.bump();
        self.bump_space();
        Ok(ast::Group {
            span: open_span,
            ast: Box::new(Ast::Empty(self.span())),
        })
    }

    /// Parse a primitive AST. e.g., A literal, non-set character class or
    /// assertion.
    ///
    /// This assumes that the parser expects a primitive at the current
    /// location. i.e., All other non-primitive cases have been handled.
    /// For example, if the parser's position is at `|`, then `|` will be
    /// treated as a literal (e.g., inside a character class).
    ///
    /// This advances the parser to the first character immediately following
    /// the primitive.
    fn parse_primitive(&self) -> Result<Primitive> {
        match self.char() {
            '\\' => self.parse_escape(),
            '.' => {
                let ast = Primitive::Dot(self.span_char());
                self.bump();
                Ok(ast)
            }
            c => {
                let ast = Primitive::Literal(ast::Literal {
                    span: self.span_char(),
                    kind: ast::LiteralKind::Verbatim,
                    c,
                });
                self.bump();
                Ok(ast)
            }
        }
    }

    /// Parse an escape sequence as a primitive AST.
    ///
    /// This assumes the parser is positioned at the start of the escape
    /// sequence, i.e., `\`. It advances the parser to the first position
    /// immediately following the escape sequence.
    #[inline(never)]
    fn parse_escape(&self) -> Result<Primitive> {
        assert_eq!(self.char(), '\\');
        let start = self.pos();
        if !self.bump() {
            return Err(self.error(
                Span::new(start, self.pos()),
                ast::ErrorKind::EscapeUnexpectedEof,
            ));
        }
        let c = self.char();

        // Handle all of the one letter sequences inline.
        self.bump();
        let span = Span::new(start, self.pos());
        if is_meta_character(c) {
            return Ok(Primitive::Literal(ast::Literal {
                span,
                kind: ast::LiteralKind::Meta,
                c,
            }));
        }
        if is_escapeable_character(c) {
            return Ok(Primitive::Literal(ast::Literal {
                span,
                kind: ast::LiteralKind::Superfluous,
                c,
            }));
        }
        let special = |kind, c| {
            Ok(Primitive::Literal(ast::Literal {
                span,
                kind: ast::LiteralKind::Special(kind),
                c,
            }))
        };
        match c {
            't' => special(ast::SpecialLiteralKind::Tab, '\t'),
            'n' => special(ast::SpecialLiteralKind::LineFeed, '\n'),
            'r' => special(ast::SpecialLiteralKind::CarriageReturn, '\r'),
            _ => Err(self.error(span, ast::ErrorKind::EscapeUnrecognized)),
        }
    }

    /// Parse a standard character class consisting primarily of characters or
    /// character ranges, but can also contain nested character classes of
    /// any type (sans `.`).
    ///
    /// This assumes the parser is positioned at the opening `[`. If parsing
    /// is successful, then the parser is advanced to the position immediately
    /// following the closing `]`.
    #[inline(never)]
    fn parse_set_class(&self) -> Result<ast::Class> {
        assert_eq!(self.char(), '[');

        let mut union =
            ast::ClassSetUnion { span: self.span(), items: vec![] };
        loop {
            self.bump_space();
            if self.is_eof() {
                return Err(self.unclosed_class_error());
            }
            match self.char() {
                '[' => {
                    union = self.push_class_open(union)?;
                }
                ']' => match self.pop_class(union)? {
                    Either::Left(nested_union) => {
                        union = nested_union;
                    }
                    Either::Right(class) => return Ok(class),
                },
                _ => {
                    union.push(self.parse_set_class_range()?);
                }
            }
        }
    }

    /// Parse a single primitive item in a character class set. The item to
    /// be parsed can either be one of a simple literal character, a range
    /// between two simple literal characters or a "primitive" character
    /// class like \w or \p{Greek}.
    ///
    /// If an invalid escape is found, or if a character class is found where
    /// a simple literal is expected (e.g., in a range), then an error is
    /// returned.
    #[inline(never)]
    fn parse_set_class_range(&self) -> Result<ast::ClassSet> {
        let prim1 = self.parse_set_class_lit()?;
        self.bump_space();
        if self.is_eof() {
            return Err(self.unclosed_class_error());
        }
        // If the next char isn't a `-`, then we don't have a range.
        // There are two exceptions. If the char after a `-` is a `]`, then
        // `-` is interpreted as a literal `-`. Alternatively, if the char
        // after a `-` is a `-`, then `--` corresponds to a "difference"
        // operation.
        if self.char() != '-' || self.peek_space() == Some(']') {
            return prim1.into_class_set(self);
        }
        // OK, now we're parsing a range, so bump past the `-` and parse the
        // second half of the range.
        if !self.bump_and_bump_space() {
            return Err(self.unclosed_class_error());
        }
        let prim2 = self.parse_set_class_lit()?;
        let range = ast::ClassSetRange {
            span: Span::new(prim1.span().start, prim2.span().end),
            start: prim1.into_class_literal(self)?,
            end: prim2.into_class_literal(self)?,
        };
        if !range.is_valid() {
            return Err(
                self.error(range.span, ast::ErrorKind::ClassRangeInvalid)
            );
        }
        Ok(ast::ClassSet::Range(range))
    }

    /// Parse a single item in a character class as a primitive, where the
    /// primitive either consists of a verbatim literal or a single escape
    /// sequence.
    ///
    /// This assumes the parser is positioned at the beginning of a primitive,
    /// and advances the parser to the first position after the primitive if
    /// successful.
    ///
    /// Note that it is the caller's responsibility to report an error if an
    /// illegal primitive was parsed.
    #[inline(never)]
    fn parse_set_class_lit(&self) -> Result<Primitive> {
        if self.char() == '\\' {
            self.parse_escape()
        } else {
            let x = Primitive::Literal(ast::Literal {
                span: self.span_char(),
                kind: ast::LiteralKind::Verbatim,
                c: self.char(),
            });
            self.bump();
            Ok(x)
        }
    }

    /// Parses the opening of a character class set. This includes the opening
    /// bracket along with `^` if present to indicate negation. This also
    /// starts parsing the opening set of unioned items if applicable, since
    /// there are special rules applied to certain characters in the opening
    /// of a character class. For example, `[^]]` is the class of all
    /// characters not equal to `]`. (`]` would need to be escaped in any other
    /// position.) Similarly for `-`.
    ///
    /// In all cases, the op inside the returned `ast::ClassBracketed` is an
    /// empty union. This empty union should be replaced with the actual item
    /// when it is popped from the parser's stack.
    ///
    /// This assumes the parser is positioned at the opening `[` and advances
    /// the parser to the first non-special byte of the character class.
    ///
    /// An error is returned if EOF is found.
    #[inline(never)]
    fn parse_set_class_open(
        &self,
    ) -> Result<(ast::Class, ast::ClassSetUnion)> {
        assert_eq!(self.char(), '[');
        let start = self.pos();
        if !self.bump_and_bump_space() {
            return Err(self.error(
                Span::new(start, self.pos()),
                ast::ErrorKind::ClassUnclosed,
            ));
        }

        let negated = if self.char() != '^' {
            false
        } else {
            if !self.bump_and_bump_space() {
                return Err(self.error(
                    Span::new(start, self.pos()),
                    ast::ErrorKind::ClassUnclosed,
                ));
            }
            true
        };
        // Accept any number of `-` as literal `-`.
        let mut union =
            ast::ClassSetUnion { span: self.span(), items: vec![] };
        while self.char() == '-' {
            union.push(ast::ClassSet::Literal(ast::Literal {
                span: self.span_char(),
                kind: ast::LiteralKind::Verbatim,
                c: '-',
            }));
            if !self.bump_and_bump_space() {
                return Err(self.error(
                    Span::new(start, start),
                    ast::ErrorKind::ClassUnclosed,
                ));
            }
        }
        // If `]` is the *first* char in a set, then interpret it as a literal
        // `]`. That is, an empty class is impossible to write.
        if union.items.is_empty() && self.char() == ']' {
            union.push(ast::ClassSet::Literal(ast::Literal {
                span: self.span_char(),
                kind: ast::LiteralKind::Verbatim,
                c: ']',
            }));
            if !self.bump_and_bump_space() {
                return Err(self.error(
                    Span::new(start, self.pos()),
                    ast::ErrorKind::ClassUnclosed,
                ));
            }
        }
        let set = ast::Class {
            span: Span::new(start, self.pos()),
            negated,
            kind: ast::ClassSet::Union(ast::ClassSetUnion {
                span: Span::new(union.span.start, union.span.start),
                items: vec![],
            }),
        };
        Ok((set, union))
    }
}

// #[cfg(test)]
// mod tests {
//     use core::ops::Range;
//
//     use alloc::format;
//
//     use crate::ast::{self, Ast, Position, Span};
//
//     use super::*;
//
//     // Our own assert_eq, which has slightly better formatting (but honestly
//     // still kind of crappy).
//     macro_rules! assert_eq {
//         ($left:expr, $right:expr) => {{
//             match (&$left, &$right) {
//                 (left_val, right_val) => {
//                     if !(*left_val == *right_val) {
//                         panic!(
//                             "assertion failed: `(left == right)`\n\n\
//                              left:  `{:?}`\nright: `{:?}`\n\n",
//                             left_val, right_val
//                         )
//                     }
//                 }
//             }
//         }};
//     }
//
//     // We create these errors to compare with real ast::Errors in the tests.
//     // We define equality between TestError and ast::Error to disregard the
//     // pattern string in ast::Error, which is annoying to provide in tests.
//     #[derive(Clone, Debug)]
//     struct TestError {
//         span: Span,
//         kind: ast::ErrorKind,
//     }
//
//     impl PartialEq<ast::Error> for TestError {
//         fn eq(&self, other: &ast::Error) -> bool {
//             self.span == other.span && self.kind == other.kind
//         }
//     }
//
//     impl PartialEq<TestError> for ast::Error {
//         fn eq(&self, other: &TestError) -> bool {
//             self.span == other.span && self.kind == other.kind
//         }
//     }
//
//     fn s(str: &str) -> String {
//         str.to_string()
//     }
//
//     fn parser(pattern: &str) -> ParserI<'_, Parser> {
//         ParserI::new(Parser::new(), pattern)
//     }
//
//     /// Short alias for creating a new span.
//     fn nspan(start: Position, end: Position) -> Span {
//         Span::new(start, end)
//     }
//
//     /// Short alias for creating a new position.
//     fn npos(offset: usize, line: usize, column: usize) -> Position {
//         Position::new(offset, line, column)
//     }
//
//     /// Create a new span from the given offset range. This assumes a single
//     /// line and sets the columns based on the offsets. i.e., This only works
//     /// out of the box for ASCII, which is fine for most tests.
//     fn span(range: Range<usize>) -> Span {
//         let start = Position::new(range.start, 1, range.start + 1);
//         let end = Position::new(range.end, 1, range.end + 1);
//         Span::new(start, end)
//     }
//
//     /// Create a new span for the corresponding byte range in the given string.
//     fn span_range(subject: &str, range: Range<usize>) -> Span {
//         let start = Position {
//             offset: range.start,
//             line: 1 + subject[..range.start].matches('\n').count(),
//             column: 1 + subject[..range.start]
//                 .chars()
//                 .rev()
//                 .position(|c| c == '\n')
//                 .unwrap_or(subject[..range.start].chars().count()),
//         };
//         let end = Position {
//             offset: range.end,
//             line: 1 + subject[..range.end].matches('\n').count(),
//             column: 1 + subject[..range.end]
//                 .chars()
//                 .rev()
//                 .position(|c| c == '\n')
//                 .unwrap_or(subject[..range.end].chars().count()),
//         };
//         Span::new(start, end)
//     }
//
//     /// Create a verbatim literal starting at the given position.
//     fn lit(c: char, start: usize) -> Ast {
//         lit_with(c, span(start..start + c.len_utf8()))
//     }
//
//     /// Create a meta literal starting at the given position.
//     fn meta_lit(c: char, span: Span) -> Ast {
//         Ast::Literal(ast::Literal { span, kind: ast::LiteralKind::Meta, c })
//     }
//
//     /// Create a verbatim literal with the given span.
//     fn lit_with(c: char, span: Span) -> Ast {
//         Ast::Literal(ast::Literal {
//             span,
//             kind: ast::LiteralKind::Verbatim,
//             c,
//         })
//     }
//
//     /// Create a concatenation with the given range.
//     fn concat(range: Range<usize>, asts: Vec<Ast>) -> Ast {
//         concat_with(span(range), asts)
//     }
//
//     /// Create a concatenation with the given span.
//     fn concat_with(span: Span, asts: Vec<Ast>) -> Ast {
//         Ast::Concat(ast::Concat { span, asts })
//     }
//
//     /// Create an alternation with the given span.
//     fn alt(range: Range<usize>, asts: Vec<Ast>) -> Ast {
//         Ast::Alternation(ast::Alternation { span: span(range), asts })
//     }
//
//     /// Create a capturing group with the given span.
//     fn group(range: Range<usize>, index: u32, ast: Ast) -> Ast {
//         Ast::Group(ast::Group {
//             span: span(range),
//             ast: Box::new(ast),
//         })
//     }
//     #[test]
//     fn parse_holistic() {
//         assert_eq!(parser("]").parse(), Ok(lit(']', 0)));
//         assert_eq!(
//             parser(r"\\\.\+\*\?\(\)\|\[\]\{\}\^\$\#\&\-\~").parse(),
//             Ok(concat(
//                 0..36,
//                 vec![
//                     meta_lit('\\', span(0..2)),
//                     meta_lit('.', span(2..4)),
//                     meta_lit('+', span(4..6)),
//                     meta_lit('*', span(6..8)),
//                     meta_lit('?', span(8..10)),
//                     meta_lit('(', span(10..12)),
//                     meta_lit(')', span(12..14)),
//                     meta_lit('|', span(14..16)),
//                     meta_lit('[', span(16..18)),
//                     meta_lit(']', span(18..20)),
//                     meta_lit('{', span(20..22)),
//                     meta_lit('}', span(22..24)),
//                     meta_lit('^', span(24..26)),
//                     meta_lit('$', span(26..28)),
//                     meta_lit('#', span(28..30)),
//                     meta_lit('&', span(30..32)),
//                     meta_lit('-', span(32..34)),
//                     meta_lit('~', span(34..36)),
//                 ]
//             ))
//         );
//     }
//
//     #[test]
//     fn parse_ignore_whitespace() {
//         // Test that basic whitespace insensitivity works.
//         let pat = "(?x)a b";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(concat_with(
//                 nspan(npos(0, 1, 1), npos(7, 1, 8)),
//                 vec![
//                     flag_set(pat, 0..4, ast::Flag::IgnoreWhitespace, false),
//                     lit_with('a', nspan(npos(4, 1, 5), npos(5, 1, 6))),
//                     lit_with('b', nspan(npos(6, 1, 7), npos(7, 1, 8))),
//                 ]
//             ))
//         );
//
//         // Test that we can toggle whitespace insensitivity.
//         let pat = "(?x)a b(?-x)a b";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(concat_with(
//                 nspan(npos(0, 1, 1), npos(15, 1, 16)),
//                 vec![
//                     flag_set(pat, 0..4, ast::Flag::IgnoreWhitespace, false),
//                     lit_with('a', nspan(npos(4, 1, 5), npos(5, 1, 6))),
//                     lit_with('b', nspan(npos(6, 1, 7), npos(7, 1, 8))),
//                     flag_set(pat, 7..12, ast::Flag::IgnoreWhitespace, true),
//                     lit_with('a', nspan(npos(12, 1, 13), npos(13, 1, 14))),
//                     lit_with(' ', nspan(npos(13, 1, 14), npos(14, 1, 15))),
//                     lit_with('b', nspan(npos(14, 1, 15), npos(15, 1, 16))),
//                 ]
//             ))
//         );
//
//         // Test that nesting whitespace insensitive flags works.
//         let pat = "a (?x:a )a ";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(concat_with(
//                 span_range(pat, 0..11),
//                 vec![
//                     lit_with('a', span_range(pat, 0..1)),
//                     lit_with(' ', span_range(pat, 1..2)),
//                     Ast::Group(ast::Group {
//                         span: span_range(pat, 2..9),
//                         kind: ast::GroupKind::NonCapturing(ast::Flags {
//                             span: span_range(pat, 4..5),
//                             items: vec![ast::FlagsItem {
//                                 span: span_range(pat, 4..5),
//                                 kind: ast::FlagsItemKind::Flag(
//                                     ast::Flag::IgnoreWhitespace
//                                 ),
//                             },],
//                         }),
//                         ast: Box::new(lit_with('a', span_range(pat, 6..7))),
//                     }),
//                     lit_with('a', span_range(pat, 9..10)),
//                     lit_with(' ', span_range(pat, 10..11)),
//                 ]
//             ))
//         );
//
//         // Test that whitespace after an opening paren is insignificant.
//         let pat = "(?x)( ?P<foo> a )";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(concat_with(
//                 span_range(pat, 0..pat.len()),
//                 vec![
//                     flag_set(pat, 0..4, ast::Flag::IgnoreWhitespace, false),
//                     Ast::Group(ast::Group {
//                         span: span_range(pat, 4..pat.len()),
//                         kind: ast::GroupKind::CaptureName {
//                             starts_with_p: true,
//                             name: ast::CaptureName {
//                                 span: span_range(pat, 9..12),
//                                 name: s("foo"),
//                                 index: 1,
//                             }
//                         },
//                         ast: Box::new(lit_with('a', span_range(pat, 14..15))),
//                     }),
//                 ]
//             ))
//         );
//         let pat = "(?x)(  a )";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(concat_with(
//                 span_range(pat, 0..pat.len()),
//                 vec![
//                     flag_set(pat, 0..4, ast::Flag::IgnoreWhitespace, false),
//                     Ast::Group(ast::Group {
//                         span: span_range(pat, 4..pat.len()),
//                         kind: ast::GroupKind::CaptureIndex(1),
//                         ast: Box::new(lit_with('a', span_range(pat, 7..8))),
//                     }),
//                 ]
//             ))
//         );
//         let pat = "(?x)(  ?:  a )";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(concat_with(
//                 span_range(pat, 0..pat.len()),
//                 vec![
//                     flag_set(pat, 0..4, ast::Flag::IgnoreWhitespace, false),
//                     Ast::Group(ast::Group {
//                         span: span_range(pat, 4..pat.len()),
//                         kind: ast::GroupKind::NonCapturing(ast::Flags {
//                             span: span_range(pat, 8..8),
//                             items: vec![],
//                         }),
//                         ast: Box::new(lit_with('a', span_range(pat, 11..12))),
//                     }),
//                 ]
//             ))
//         );
//         let pat = r"(?x)\x { 53 }";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(concat_with(
//                 span_range(pat, 0..pat.len()),
//                 vec![
//                     flag_set(pat, 0..4, ast::Flag::IgnoreWhitespace, false),
//                     Ast::Literal(ast::Literal {
//                         span: span(4..13),
//                         kind: ast::LiteralKind::HexBrace(
//                             ast::HexLiteralKind::X
//                         ),
//                         c: 'S',
//                     }),
//                 ]
//             ))
//         );
//
//         // Test that whitespace after an escape is OK.
//         let pat = r"(?x)\ ";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(concat_with(
//                 span_range(pat, 0..pat.len()),
//                 vec![
//                     flag_set(pat, 0..4, ast::Flag::IgnoreWhitespace, false),
//                     Ast::Literal(ast::Literal {
//                         span: span_range(pat, 4..6),
//                         kind: ast::LiteralKind::Superfluous,
//                         c: ' ',
//                     }),
//                 ]
//             ))
//         );
//     }
//
//     #[test]
//     fn parse_newlines() {
//         let pat = ".\n.";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(concat_with(
//                 span_range(pat, 0..3),
//                 vec![
//                     Ast::Dot(span_range(pat, 0..1)),
//                     lit_with('\n', span_range(pat, 1..2)),
//                     Ast::Dot(span_range(pat, 2..3)),
//                 ]
//             ))
//         );
//
//         let pat = "foobar\nbaz\nquux\n";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(concat_with(
//                 span_range(pat, 0..pat.len()),
//                 vec![
//                     lit_with('f', nspan(npos(0, 1, 1), npos(1, 1, 2))),
//                     lit_with('o', nspan(npos(1, 1, 2), npos(2, 1, 3))),
//                     lit_with('o', nspan(npos(2, 1, 3), npos(3, 1, 4))),
//                     lit_with('b', nspan(npos(3, 1, 4), npos(4, 1, 5))),
//                     lit_with('a', nspan(npos(4, 1, 5), npos(5, 1, 6))),
//                     lit_with('r', nspan(npos(5, 1, 6), npos(6, 1, 7))),
//                     lit_with('\n', nspan(npos(6, 1, 7), npos(7, 2, 1))),
//                     lit_with('b', nspan(npos(7, 2, 1), npos(8, 2, 2))),
//                     lit_with('a', nspan(npos(8, 2, 2), npos(9, 2, 3))),
//                     lit_with('z', nspan(npos(9, 2, 3), npos(10, 2, 4))),
//                     lit_with('\n', nspan(npos(10, 2, 4), npos(11, 3, 1))),
//                     lit_with('q', nspan(npos(11, 3, 1), npos(12, 3, 2))),
//                     lit_with('u', nspan(npos(12, 3, 2), npos(13, 3, 3))),
//                     lit_with('u', nspan(npos(13, 3, 3), npos(14, 3, 4))),
//                     lit_with('x', nspan(npos(14, 3, 4), npos(15, 3, 5))),
//                     lit_with('\n', nspan(npos(15, 3, 5), npos(16, 4, 1))),
//                 ]
//             ))
//         );
//     }
//
//     #[test]
//     fn parse_uncounted_repetition() {
//         assert_eq!(
//             parser(r"a*").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..2),
//                 op: ast::RepetitionOp {
//                     span: span(1..2),
//                     kind: ast::RepetitionKind::ZeroOrMore,
//                 },
//                 greedy: true,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//         assert_eq!(
//             parser(r"a+").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..2),
//                 op: ast::RepetitionOp {
//                     span: span(1..2),
//                     kind: ast::RepetitionKind::OneOrMore,
//                 },
//                 greedy: true,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//
//         assert_eq!(
//             parser(r"a?").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..2),
//                 op: ast::RepetitionOp {
//                     span: span(1..2),
//                     kind: ast::RepetitionKind::ZeroOrOne,
//                 },
//                 greedy: true,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//         assert_eq!(
//             parser(r"a??").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..3),
//                 op: ast::RepetitionOp {
//                     span: span(1..3),
//                     kind: ast::RepetitionKind::ZeroOrOne,
//                 },
//                 greedy: false,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//         assert_eq!(
//             parser(r"a?").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..2),
//                 op: ast::RepetitionOp {
//                     span: span(1..2),
//                     kind: ast::RepetitionKind::ZeroOrOne,
//                 },
//                 greedy: true,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//         assert_eq!(
//             parser(r"a?b").parse(),
//             Ok(concat(
//                 0..3,
//                 vec![
//                     Ast::Repetition(ast::Repetition {
//                         span: span(0..2),
//                         op: ast::RepetitionOp {
//                             span: span(1..2),
//                             kind: ast::RepetitionKind::ZeroOrOne,
//                         },
//                         greedy: true,
//                         ast: Box::new(lit('a', 0)),
//                     }),
//                     lit('b', 2),
//                 ]
//             ))
//         );
//         assert_eq!(
//             parser(r"a??b").parse(),
//             Ok(concat(
//                 0..4,
//                 vec![
//                     Ast::Repetition(ast::Repetition {
//                         span: span(0..3),
//                         op: ast::RepetitionOp {
//                             span: span(1..3),
//                             kind: ast::RepetitionKind::ZeroOrOne,
//                         },
//                         greedy: false,
//                         ast: Box::new(lit('a', 0)),
//                     }),
//                     lit('b', 3),
//                 ]
//             ))
//         );
//         assert_eq!(
//             parser(r"ab?").parse(),
//             Ok(concat(
//                 0..3,
//                 vec![
//                     lit('a', 0),
//                     Ast::Repetition(ast::Repetition {
//                         span: span(1..3),
//                         op: ast::RepetitionOp {
//                             span: span(2..3),
//                             kind: ast::RepetitionKind::ZeroOrOne,
//                         },
//                         greedy: true,
//                         ast: Box::new(lit('b', 1)),
//                     }),
//                 ]
//             ))
//         );
//         assert_eq!(
//             parser(r"(ab)?").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..5),
//                 op: ast::RepetitionOp {
//                     span: span(4..5),
//                     kind: ast::RepetitionKind::ZeroOrOne,
//                 },
//                 greedy: true,
//                 ast: Box::new(group(
//                     0..4,
//                     1,
//                     concat(1..3, vec![lit('a', 1), lit('b', 2),])
//                 )),
//             }))
//         );
//         assert_eq!(
//             parser(r"|a?").parse(),
//             Ok(alt(
//                 0..3,
//                 vec![
//                     Ast::Empty(span(0..0)),
//                     Ast::Repetition(ast::Repetition {
//                         span: span(1..3),
//                         op: ast::RepetitionOp {
//                             span: span(2..3),
//                             kind: ast::RepetitionKind::ZeroOrOne,
//                         },
//                         greedy: true,
//                         ast: Box::new(lit('a', 1)),
//                     }),
//                 ]
//             ))
//         );
//
//         assert_eq!(
//             parser(r"*").parse().unwrap_err(),
//             TestError {
//                 span: span(0..0),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"(?i)*").parse().unwrap_err(),
//             TestError {
//                 span: span(4..4),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"(*)").parse().unwrap_err(),
//             TestError {
//                 span: span(1..1),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"(?:?)").parse().unwrap_err(),
//             TestError {
//                 span: span(3..3),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"+").parse().unwrap_err(),
//             TestError {
//                 span: span(0..0),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"?").parse().unwrap_err(),
//             TestError {
//                 span: span(0..0),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"(?)").parse().unwrap_err(),
//             TestError {
//                 span: span(1..1),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"|*").parse().unwrap_err(),
//             TestError {
//                 span: span(1..1),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"|+").parse().unwrap_err(),
//             TestError {
//                 span: span(1..1),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"|?").parse().unwrap_err(),
//             TestError {
//                 span: span(1..1),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_counted_repetition() {
//         assert_eq!(
//             parser(r"a{5}").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..4),
//                 op: ast::RepetitionOp {
//                     span: span(1..4),
//                     kind: ast::RepetitionKind::Range(
//                         ast::RepetitionRange::Exactly(5)
//                     ),
//                 },
//                 greedy: true,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//         assert_eq!(
//             parser(r"a{5,}").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..5),
//                 op: ast::RepetitionOp {
//                     span: span(1..5),
//                     kind: ast::RepetitionKind::Range(
//                         ast::RepetitionRange::AtLeast(5)
//                     ),
//                 },
//                 greedy: true,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//         assert_eq!(
//             parser(r"a{5,9}").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..6),
//                 op: ast::RepetitionOp {
//                     span: span(1..6),
//                     kind: ast::RepetitionKind::Range(
//                         ast::RepetitionRange::Bounded(5, 9)
//                     ),
//                 },
//                 greedy: true,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//         assert_eq!(
//             parser(r"a{5}?").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..5),
//                 op: ast::RepetitionOp {
//                     span: span(1..5),
//                     kind: ast::RepetitionKind::Range(
//                         ast::RepetitionRange::Exactly(5)
//                     ),
//                 },
//                 greedy: false,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//         assert_eq!(
//             parser(r"ab{5}").parse(),
//             Ok(concat(
//                 0..5,
//                 vec![
//                     lit('a', 0),
//                     Ast::Repetition(ast::Repetition {
//                         span: span(1..5),
//                         op: ast::RepetitionOp {
//                             span: span(2..5),
//                             kind: ast::RepetitionKind::Range(
//                                 ast::RepetitionRange::Exactly(5)
//                             ),
//                         },
//                         greedy: true,
//                         ast: Box::new(lit('b', 1)),
//                     }),
//                 ]
//             ))
//         );
//         assert_eq!(
//             parser(r"ab{5}c").parse(),
//             Ok(concat(
//                 0..6,
//                 vec![
//                     lit('a', 0),
//                     Ast::Repetition(ast::Repetition {
//                         span: span(1..5),
//                         op: ast::RepetitionOp {
//                             span: span(2..5),
//                             kind: ast::RepetitionKind::Range(
//                                 ast::RepetitionRange::Exactly(5)
//                             ),
//                         },
//                         greedy: true,
//                         ast: Box::new(lit('b', 1)),
//                     }),
//                     lit('c', 5),
//                 ]
//             ))
//         );
//
//         assert_eq!(
//             parser(r"a{ 5 }").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..6),
//                 op: ast::RepetitionOp {
//                     span: span(1..6),
//                     kind: ast::RepetitionKind::Range(
//                         ast::RepetitionRange::Exactly(5)
//                     ),
//                 },
//                 greedy: true,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//         assert_eq!(
//             parser(r"a{ 5 , 9 }").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..10),
//                 op: ast::RepetitionOp {
//                     span: span(1..10),
//                     kind: ast::RepetitionKind::Range(
//                         ast::RepetitionRange::Bounded(5, 9)
//                     ),
//                 },
//                 greedy: true,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//         assert_eq!(
//             parser_ignore_whitespace(r"a{5,9} ?").parse(),
//             Ok(Ast::Repetition(ast::Repetition {
//                 span: span(0..8),
//                 op: ast::RepetitionOp {
//                     span: span(1..8),
//                     kind: ast::RepetitionKind::Range(
//                         ast::RepetitionRange::Bounded(5, 9)
//                     ),
//                 },
//                 greedy: false,
//                 ast: Box::new(lit('a', 0)),
//             }))
//         );
//
//         assert_eq!(
//             parser(r"(?i){0}").parse().unwrap_err(),
//             TestError {
//                 span: span(4..4),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"(?m){1,1}").parse().unwrap_err(),
//             TestError {
//                 span: span(4..4),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"a{]}").parse().unwrap_err(),
//             TestError {
//                 span: span(2..2),
//                 kind: ast::ErrorKind::RepetitionCountDecimalEmpty,
//             }
//         );
//         assert_eq!(
//             parser(r"a{1,]}").parse().unwrap_err(),
//             TestError {
//                 span: span(4..4),
//                 kind: ast::ErrorKind::RepetitionCountDecimalEmpty,
//             }
//         );
//         assert_eq!(
//             parser(r"a{").parse().unwrap_err(),
//             TestError {
//                 span: span(1..2),
//                 kind: ast::ErrorKind::RepetitionCountUnclosed,
//             }
//         );
//         assert_eq!(
//             parser(r"a{}").parse().unwrap_err(),
//             TestError {
//                 span: span(2..2),
//                 kind: ast::ErrorKind::RepetitionCountDecimalEmpty,
//             }
//         );
//         assert_eq!(
//             parser(r"a{a").parse().unwrap_err(),
//             TestError {
//                 span: span(2..2),
//                 kind: ast::ErrorKind::RepetitionCountDecimalEmpty,
//             }
//         );
//         assert_eq!(
//             parser(r"a{9999999999}").parse().unwrap_err(),
//             TestError {
//                 span: span(2..12),
//                 kind: ast::ErrorKind::DecimalInvalid,
//             }
//         );
//         assert_eq!(
//             parser(r"a{9").parse().unwrap_err(),
//             TestError {
//                 span: span(1..3),
//                 kind: ast::ErrorKind::RepetitionCountUnclosed,
//             }
//         );
//         assert_eq!(
//             parser(r"a{9,a").parse().unwrap_err(),
//             TestError {
//                 span: span(4..4),
//                 kind: ast::ErrorKind::RepetitionCountDecimalEmpty,
//             }
//         );
//         assert_eq!(
//             parser(r"a{9,9999999999}").parse().unwrap_err(),
//             TestError {
//                 span: span(4..14),
//                 kind: ast::ErrorKind::DecimalInvalid,
//             }
//         );
//         assert_eq!(
//             parser(r"a{9,").parse().unwrap_err(),
//             TestError {
//                 span: span(1..4),
//                 kind: ast::ErrorKind::RepetitionCountUnclosed,
//             }
//         );
//         assert_eq!(
//             parser(r"a{9,11").parse().unwrap_err(),
//             TestError {
//                 span: span(1..6),
//                 kind: ast::ErrorKind::RepetitionCountUnclosed,
//             }
//         );
//         assert_eq!(
//             parser(r"a{2,1}").parse().unwrap_err(),
//             TestError {
//                 span: span(1..6),
//                 kind: ast::ErrorKind::RepetitionCountInvalid,
//             }
//         );
//         assert_eq!(
//             parser(r"{5}").parse().unwrap_err(),
//             TestError {
//                 span: span(0..0),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//         assert_eq!(
//             parser(r"|{5}").parse().unwrap_err(),
//             TestError {
//                 span: span(1..1),
//                 kind: ast::ErrorKind::RepetitionMissing,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_alternate() {
//         assert_eq!(
//             parser(r"a|b").parse(),
//             Ok(Ast::Alternation(ast::Alternation {
//                 span: span(0..3),
//                 asts: vec![lit('a', 0), lit('b', 2)],
//             }))
//         );
//         assert_eq!(
//             parser(r"(a|b)").parse(),
//             Ok(group(
//                 0..5,
//                 1,
//                 Ast::Alternation(ast::Alternation {
//                     span: span(1..4),
//                     asts: vec![lit('a', 1), lit('b', 3)],
//                 })
//             ))
//         );
//
//         assert_eq!(
//             parser(r"a|b|c").parse(),
//             Ok(Ast::Alternation(ast::Alternation {
//                 span: span(0..5),
//                 asts: vec![lit('a', 0), lit('b', 2), lit('c', 4)],
//             }))
//         );
//         assert_eq!(
//             parser(r"ax|by|cz").parse(),
//             Ok(Ast::Alternation(ast::Alternation {
//                 span: span(0..8),
//                 asts: vec![
//                     concat(0..2, vec![lit('a', 0), lit('x', 1)]),
//                     concat(3..5, vec![lit('b', 3), lit('y', 4)]),
//                     concat(6..8, vec![lit('c', 6), lit('z', 7)]),
//                 ],
//             }))
//         );
//         assert_eq!(
//             parser(r"(ax|by|cz)").parse(),
//             Ok(group(
//                 0..10,
//                 1,
//                 Ast::Alternation(ast::Alternation {
//                     span: span(1..9),
//                     asts: vec![
//                         concat(1..3, vec![lit('a', 1), lit('x', 2)]),
//                         concat(4..6, vec![lit('b', 4), lit('y', 5)]),
//                         concat(7..9, vec![lit('c', 7), lit('z', 8)]),
//                     ],
//                 })
//             ))
//         );
//         assert_eq!(
//             parser(r"(ax|(by|(cz)))").parse(),
//             Ok(group(
//                 0..14,
//                 1,
//                 alt(
//                     1..13,
//                     vec![
//                         concat(1..3, vec![lit('a', 1), lit('x', 2)]),
//                         group(
//                             4..13,
//                             2,
//                             alt(
//                                 5..12,
//                                 vec![
//                                     concat(
//                                         5..7,
//                                         vec![lit('b', 5), lit('y', 6)]
//                                     ),
//                                     group(
//                                         8..12,
//                                         3,
//                                         concat(
//                                             9..11,
//                                             vec![lit('c', 9), lit('z', 10),]
//                                         )
//                                     ),
//                                 ]
//                             )
//                         ),
//                     ]
//                 )
//             ))
//         );
//
//         assert_eq!(
//             parser(r"|").parse(),
//             Ok(alt(
//                 0..1,
//                 vec![Ast::Empty(span(0..0)), Ast::Empty(span(1..1)),]
//             ))
//         );
//         assert_eq!(
//             parser(r"||").parse(),
//             Ok(alt(
//                 0..2,
//                 vec![
//                     Ast::Empty(span(0..0)),
//                     Ast::Empty(span(1..1)),
//                     Ast::Empty(span(2..2)),
//                 ]
//             ))
//         );
//         assert_eq!(
//             parser(r"a|").parse(),
//             Ok(alt(0..2, vec![lit('a', 0), Ast::Empty(span(2..2)),]))
//         );
//         assert_eq!(
//             parser(r"|a").parse(),
//             Ok(alt(0..2, vec![Ast::Empty(span(0..0)), lit('a', 1),]))
//         );
//
//         assert_eq!(
//             parser(r"(|)").parse(),
//             Ok(group(
//                 0..3,
//                 1,
//                 alt(
//                     1..2,
//                     vec![Ast::Empty(span(1..1)), Ast::Empty(span(2..2)),]
//                 )
//             ))
//         );
//         assert_eq!(
//             parser(r"(a|)").parse(),
//             Ok(group(
//                 0..4,
//                 1,
//                 alt(1..3, vec![lit('a', 1), Ast::Empty(span(3..3)),])
//             ))
//         );
//         assert_eq!(
//             parser(r"(|a)").parse(),
//             Ok(group(
//                 0..4,
//                 1,
//                 alt(1..3, vec![Ast::Empty(span(1..1)), lit('a', 2),])
//             ))
//         );
//
//         assert_eq!(
//             parser(r"a|b)").parse().unwrap_err(),
//             TestError {
//                 span: span(3..4),
//                 kind: ast::ErrorKind::GroupUnopened,
//             }
//         );
//         assert_eq!(
//             parser(r"(a|b").parse().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::GroupUnclosed,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_unsupported_lookaround() {
//         assert_eq!(
//             parser(r"(?=a)").parse().unwrap_err(),
//             TestError {
//                 span: span(0..3),
//                 kind: ast::ErrorKind::UnsupportedLookAround,
//             }
//         );
//         assert_eq!(
//             parser(r"(?!a)").parse().unwrap_err(),
//             TestError {
//                 span: span(0..3),
//                 kind: ast::ErrorKind::UnsupportedLookAround,
//             }
//         );
//         assert_eq!(
//             parser(r"(?<=a)").parse().unwrap_err(),
//             TestError {
//                 span: span(0..4),
//                 kind: ast::ErrorKind::UnsupportedLookAround,
//             }
//         );
//         assert_eq!(
//             parser(r"(?<!a)").parse().unwrap_err(),
//             TestError {
//                 span: span(0..4),
//                 kind: ast::ErrorKind::UnsupportedLookAround,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_group() {
//         assert_eq!(
//             parser("(?i)").parse(),
//             Ok(Ast::Flags(ast::SetFlags {
//                 span: span(0..4),
//                 flags: ast::Flags {
//                     span: span(2..3),
//                     items: vec![ast::FlagsItem {
//                         span: span(2..3),
//                         kind: ast::FlagsItemKind::Flag(
//                             ast::Flag::CaseInsensitive
//                         ),
//                     }],
//                 },
//             }))
//         );
//         assert_eq!(
//             parser("(?iU)").parse(),
//             Ok(Ast::Flags(ast::SetFlags {
//                 span: span(0..5),
//                 flags: ast::Flags {
//                     span: span(2..4),
//                     items: vec![
//                         ast::FlagsItem {
//                             span: span(2..3),
//                             kind: ast::FlagsItemKind::Flag(
//                                 ast::Flag::CaseInsensitive
//                             ),
//                         },
//                         ast::FlagsItem {
//                             span: span(3..4),
//                             kind: ast::FlagsItemKind::Flag(
//                                 ast::Flag::SwapGreed
//                             ),
//                         },
//                     ],
//                 },
//             }))
//         );
//         assert_eq!(
//             parser("(?i-U)").parse(),
//             Ok(Ast::Flags(ast::SetFlags {
//                 span: span(0..6),
//                 flags: ast::Flags {
//                     span: span(2..5),
//                     items: vec![
//                         ast::FlagsItem {
//                             span: span(2..3),
//                             kind: ast::FlagsItemKind::Flag(
//                                 ast::Flag::CaseInsensitive
//                             ),
//                         },
//                         ast::FlagsItem {
//                             span: span(3..4),
//                             kind: ast::FlagsItemKind::Negation,
//                         },
//                         ast::FlagsItem {
//                             span: span(4..5),
//                             kind: ast::FlagsItemKind::Flag(
//                                 ast::Flag::SwapGreed
//                             ),
//                         },
//                     ],
//                 },
//             }))
//         );
//
//         assert_eq!(
//             parser("()").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..2),
//                 kind: ast::GroupKind::CaptureIndex(1),
//                 ast: Box::new(Ast::Empty(span(1..1))),
//             }))
//         );
//         assert_eq!(
//             parser("(a)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..3),
//                 kind: ast::GroupKind::CaptureIndex(1),
//                 ast: Box::new(lit('a', 1)),
//             }))
//         );
//         assert_eq!(
//             parser("(())").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..4),
//                 kind: ast::GroupKind::CaptureIndex(1),
//                 ast: Box::new(Ast::Group(ast::Group {
//                     span: span(1..3),
//                     kind: ast::GroupKind::CaptureIndex(2),
//                     ast: Box::new(Ast::Empty(span(2..2))),
//                 })),
//             }))
//         );
//
//         assert_eq!(
//             parser("(?:a)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..5),
//                 kind: ast::GroupKind::NonCapturing(ast::Flags {
//                     span: span(2..2),
//                     items: vec![],
//                 }),
//                 ast: Box::new(lit('a', 3)),
//             }))
//         );
//
//         assert_eq!(
//             parser("(?i:a)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..6),
//                 kind: ast::GroupKind::NonCapturing(ast::Flags {
//                     span: span(2..3),
//                     items: vec![ast::FlagsItem {
//                         span: span(2..3),
//                         kind: ast::FlagsItemKind::Flag(
//                             ast::Flag::CaseInsensitive
//                         ),
//                     },],
//                 }),
//                 ast: Box::new(lit('a', 4)),
//             }))
//         );
//         assert_eq!(
//             parser("(?i-U:a)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..8),
//                 kind: ast::GroupKind::NonCapturing(ast::Flags {
//                     span: span(2..5),
//                     items: vec![
//                         ast::FlagsItem {
//                             span: span(2..3),
//                             kind: ast::FlagsItemKind::Flag(
//                                 ast::Flag::CaseInsensitive
//                             ),
//                         },
//                         ast::FlagsItem {
//                             span: span(3..4),
//                             kind: ast::FlagsItemKind::Negation,
//                         },
//                         ast::FlagsItem {
//                             span: span(4..5),
//                             kind: ast::FlagsItemKind::Flag(
//                                 ast::Flag::SwapGreed
//                             ),
//                         },
//                     ],
//                 }),
//                 ast: Box::new(lit('a', 6)),
//             }))
//         );
//
//         assert_eq!(
//             parser("(").parse().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::GroupUnclosed,
//             }
//         );
//         assert_eq!(
//             parser("(?").parse().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::GroupUnclosed,
//             }
//         );
//         assert_eq!(
//             parser("(?P").parse().unwrap_err(),
//             TestError {
//                 span: span(2..3),
//                 kind: ast::ErrorKind::FlagUnrecognized,
//             }
//         );
//         assert_eq!(
//             parser("(?P<").parse().unwrap_err(),
//             TestError {
//                 span: span(4..4),
//                 kind: ast::ErrorKind::GroupNameUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser("(a").parse().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::GroupUnclosed,
//             }
//         );
//         assert_eq!(
//             parser("(()").parse().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::GroupUnclosed,
//             }
//         );
//         assert_eq!(
//             parser(")").parse().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::GroupUnopened,
//             }
//         );
//         assert_eq!(
//             parser("a)").parse().unwrap_err(),
//             TestError {
//                 span: span(1..2),
//                 kind: ast::ErrorKind::GroupUnopened,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_capture_name() {
//         assert_eq!(
//             parser("(?<a>z)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..7),
//                 kind: ast::GroupKind::CaptureName {
//                     starts_with_p: false,
//                     name: ast::CaptureName {
//                         span: span(3..4),
//                         name: s("a"),
//                         index: 1,
//                     }
//                 },
//                 ast: Box::new(lit('z', 5)),
//             }))
//         );
//         assert_eq!(
//             parser("(?P<a>z)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..8),
//                 kind: ast::GroupKind::CaptureName {
//                     starts_with_p: true,
//                     name: ast::CaptureName {
//                         span: span(4..5),
//                         name: s("a"),
//                         index: 1,
//                     }
//                 },
//                 ast: Box::new(lit('z', 6)),
//             }))
//         );
//         assert_eq!(
//             parser("(?P<abc>z)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..10),
//                 kind: ast::GroupKind::CaptureName {
//                     starts_with_p: true,
//                     name: ast::CaptureName {
//                         span: span(4..7),
//                         name: s("abc"),
//                         index: 1,
//                     }
//                 },
//                 ast: Box::new(lit('z', 8)),
//             }))
//         );
//
//         assert_eq!(
//             parser("(?P<a_1>z)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..10),
//                 kind: ast::GroupKind::CaptureName {
//                     starts_with_p: true,
//                     name: ast::CaptureName {
//                         span: span(4..7),
//                         name: s("a_1"),
//                         index: 1,
//                     }
//                 },
//                 ast: Box::new(lit('z', 8)),
//             }))
//         );
//
//         assert_eq!(
//             parser("(?P<a.1>z)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..10),
//                 kind: ast::GroupKind::CaptureName {
//                     starts_with_p: true,
//                     name: ast::CaptureName {
//                         span: span(4..7),
//                         name: s("a.1"),
//                         index: 1,
//                     }
//                 },
//                 ast: Box::new(lit('z', 8)),
//             }))
//         );
//
//         assert_eq!(
//             parser("(?P<a[1]>z)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: span(0..11),
//                 kind: ast::GroupKind::CaptureName {
//                     starts_with_p: true,
//                     name: ast::CaptureName {
//                         span: span(4..8),
//                         name: s("a[1]"),
//                         index: 1,
//                     }
//                 },
//                 ast: Box::new(lit('z', 9)),
//             }))
//         );
//
//         assert_eq!(
//             parser("(?P<a¾>)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: Span::new(
//                     Position::new(0, 1, 1),
//                     Position::new(9, 1, 9),
//                 ),
//                 kind: ast::GroupKind::CaptureName {
//                     starts_with_p: true,
//                     name: ast::CaptureName {
//                         span: Span::new(
//                             Position::new(4, 1, 5),
//                             Position::new(7, 1, 7),
//                         ),
//                         name: s("a¾"),
//                         index: 1,
//                     }
//                 },
//                 ast: Box::new(Ast::Empty(Span::new(
//                     Position::new(8, 1, 8),
//                     Position::new(8, 1, 8),
//                 ))),
//             }))
//         );
//         assert_eq!(
//             parser("(?P<名字>)").parse(),
//             Ok(Ast::Group(ast::Group {
//                 span: Span::new(
//                     Position::new(0, 1, 1),
//                     Position::new(12, 1, 9),
//                 ),
//                 kind: ast::GroupKind::CaptureName {
//                     starts_with_p: true,
//                     name: ast::CaptureName {
//                         span: Span::new(
//                             Position::new(4, 1, 5),
//                             Position::new(10, 1, 7),
//                         ),
//                         name: s("名字"),
//                         index: 1,
//                     }
//                 },
//                 ast: Box::new(Ast::Empty(Span::new(
//                     Position::new(11, 1, 8),
//                     Position::new(11, 1, 8),
//                 ))),
//             }))
//         );
//
//         assert_eq!(
//             parser("(?P<").parse().unwrap_err(),
//             TestError {
//                 span: span(4..4),
//                 kind: ast::ErrorKind::GroupNameUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser("(?P<>z)").parse().unwrap_err(),
//             TestError {
//                 span: span(4..4),
//                 kind: ast::ErrorKind::GroupNameEmpty,
//             }
//         );
//         assert_eq!(
//             parser("(?P<a").parse().unwrap_err(),
//             TestError {
//                 span: span(5..5),
//                 kind: ast::ErrorKind::GroupNameUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser("(?P<ab").parse().unwrap_err(),
//             TestError {
//                 span: span(6..6),
//                 kind: ast::ErrorKind::GroupNameUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser("(?P<0a").parse().unwrap_err(),
//             TestError {
//                 span: span(4..5),
//                 kind: ast::ErrorKind::GroupNameInvalid,
//             }
//         );
//         assert_eq!(
//             parser("(?P<~").parse().unwrap_err(),
//             TestError {
//                 span: span(4..5),
//                 kind: ast::ErrorKind::GroupNameInvalid,
//             }
//         );
//         assert_eq!(
//             parser("(?P<abc~").parse().unwrap_err(),
//             TestError {
//                 span: span(7..8),
//                 kind: ast::ErrorKind::GroupNameInvalid,
//             }
//         );
//         assert_eq!(
//             parser("(?P<a>y)(?P<a>z)").parse().unwrap_err(),
//             TestError {
//                 span: span(12..13),
//                 kind: ast::ErrorKind::GroupNameDuplicate {
//                     original: span(4..5),
//                 },
//             }
//         );
//         assert_eq!(
//             parser("(?P<5>)").parse().unwrap_err(),
//             TestError {
//                 span: span(4..5),
//                 kind: ast::ErrorKind::GroupNameInvalid,
//             }
//         );
//         assert_eq!(
//             parser("(?P<5a>)").parse().unwrap_err(),
//             TestError {
//                 span: span(4..5),
//                 kind: ast::ErrorKind::GroupNameInvalid,
//             }
//         );
//         assert_eq!(
//             parser("(?P<¾>)").parse().unwrap_err(),
//             TestError {
//                 span: Span::new(
//                     Position::new(4, 1, 5),
//                     Position::new(6, 1, 6),
//                 ),
//                 kind: ast::ErrorKind::GroupNameInvalid,
//             }
//         );
//         assert_eq!(
//             parser("(?P<¾a>)").parse().unwrap_err(),
//             TestError {
//                 span: Span::new(
//                     Position::new(4, 1, 5),
//                     Position::new(6, 1, 6),
//                 ),
//                 kind: ast::ErrorKind::GroupNameInvalid,
//             }
//         );
//         assert_eq!(
//             parser("(?P<☃>)").parse().unwrap_err(),
//             TestError {
//                 span: Span::new(
//                     Position::new(4, 1, 5),
//                     Position::new(7, 1, 6),
//                 ),
//                 kind: ast::ErrorKind::GroupNameInvalid,
//             }
//         );
//         assert_eq!(
//             parser("(?P<a☃>)").parse().unwrap_err(),
//             TestError {
//                 span: Span::new(
//                     Position::new(5, 1, 6),
//                     Position::new(8, 1, 7),
//                 ),
//                 kind: ast::ErrorKind::GroupNameInvalid,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_flags() {
//         assert_eq!(
//             parser("i:").parse_flags(),
//             Ok(ast::Flags {
//                 span: span(0..1),
//                 items: vec![ast::FlagsItem {
//                     span: span(0..1),
//                     kind: ast::FlagsItemKind::Flag(ast::Flag::CaseInsensitive),
//                 }],
//             })
//         );
//         assert_eq!(
//             parser("i)").parse_flags(),
//             Ok(ast::Flags {
//                 span: span(0..1),
//                 items: vec![ast::FlagsItem {
//                     span: span(0..1),
//                     kind: ast::FlagsItemKind::Flag(ast::Flag::CaseInsensitive),
//                 }],
//             })
//         );
//
//         assert_eq!(
//             parser("isU:").parse_flags(),
//             Ok(ast::Flags {
//                 span: span(0..3),
//                 items: vec![
//                     ast::FlagsItem {
//                         span: span(0..1),
//                         kind: ast::FlagsItemKind::Flag(
//                             ast::Flag::CaseInsensitive
//                         ),
//                     },
//                     ast::FlagsItem {
//                         span: span(1..2),
//                         kind: ast::FlagsItemKind::Flag(
//                             ast::Flag::DotMatchesNewLine
//                         ),
//                     },
//                     ast::FlagsItem {
//                         span: span(2..3),
//                         kind: ast::FlagsItemKind::Flag(ast::Flag::SwapGreed),
//                     },
//                 ],
//             })
//         );
//
//         assert_eq!(
//             parser("-isU:").parse_flags(),
//             Ok(ast::Flags {
//                 span: span(0..4),
//                 items: vec![
//                     ast::FlagsItem {
//                         span: span(0..1),
//                         kind: ast::FlagsItemKind::Negation,
//                     },
//                     ast::FlagsItem {
//                         span: span(1..2),
//                         kind: ast::FlagsItemKind::Flag(
//                             ast::Flag::CaseInsensitive
//                         ),
//                     },
//                     ast::FlagsItem {
//                         span: span(2..3),
//                         kind: ast::FlagsItemKind::Flag(
//                             ast::Flag::DotMatchesNewLine
//                         ),
//                     },
//                     ast::FlagsItem {
//                         span: span(3..4),
//                         kind: ast::FlagsItemKind::Flag(ast::Flag::SwapGreed),
//                     },
//                 ],
//             })
//         );
//         assert_eq!(
//             parser("i-sU:").parse_flags(),
//             Ok(ast::Flags {
//                 span: span(0..4),
//                 items: vec![
//                     ast::FlagsItem {
//                         span: span(0..1),
//                         kind: ast::FlagsItemKind::Flag(
//                             ast::Flag::CaseInsensitive
//                         ),
//                     },
//                     ast::FlagsItem {
//                         span: span(1..2),
//                         kind: ast::FlagsItemKind::Negation,
//                     },
//                     ast::FlagsItem {
//                         span: span(2..3),
//                         kind: ast::FlagsItemKind::Flag(
//                             ast::Flag::DotMatchesNewLine
//                         ),
//                     },
//                     ast::FlagsItem {
//                         span: span(3..4),
//                         kind: ast::FlagsItemKind::Flag(ast::Flag::SwapGreed),
//                     },
//                 ],
//             })
//         );
//         assert_eq!(
//             parser("i-sR:").parse_flags(),
//             Ok(ast::Flags {
//                 span: span(0..4),
//                 items: vec![
//                     ast::FlagsItem {
//                         span: span(0..1),
//                         kind: ast::FlagsItemKind::Flag(
//                             ast::Flag::CaseInsensitive
//                         ),
//                     },
//                     ast::FlagsItem {
//                         span: span(1..2),
//                         kind: ast::FlagsItemKind::Negation,
//                     },
//                     ast::FlagsItem {
//                         span: span(2..3),
//                         kind: ast::FlagsItemKind::Flag(
//                             ast::Flag::DotMatchesNewLine
//                         ),
//                     },
//                     ast::FlagsItem {
//                         span: span(3..4),
//                         kind: ast::FlagsItemKind::Flag(ast::Flag::CRLF),
//                     },
//                 ],
//             })
//         );
//
//         assert_eq!(
//             parser("isU").parse_flags().unwrap_err(),
//             TestError {
//                 span: span(3..3),
//                 kind: ast::ErrorKind::FlagUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser("isUa:").parse_flags().unwrap_err(),
//             TestError {
//                 span: span(3..4),
//                 kind: ast::ErrorKind::FlagUnrecognized,
//             }
//         );
//         assert_eq!(
//             parser("isUi:").parse_flags().unwrap_err(),
//             TestError {
//                 span: span(3..4),
//                 kind: ast::ErrorKind::FlagDuplicate { original: span(0..1) },
//             }
//         );
//         assert_eq!(
//             parser("i-sU-i:").parse_flags().unwrap_err(),
//             TestError {
//                 span: span(4..5),
//                 kind: ast::ErrorKind::FlagRepeatedNegation {
//                     original: span(1..2),
//                 },
//             }
//         );
//         assert_eq!(
//             parser("-)").parse_flags().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::FlagDanglingNegation,
//             }
//         );
//         assert_eq!(
//             parser("i-)").parse_flags().unwrap_err(),
//             TestError {
//                 span: span(1..2),
//                 kind: ast::ErrorKind::FlagDanglingNegation,
//             }
//         );
//         assert_eq!(
//             parser("iU-)").parse_flags().unwrap_err(),
//             TestError {
//                 span: span(2..3),
//                 kind: ast::ErrorKind::FlagDanglingNegation,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_flag() {
//         assert_eq!(parser("i").parse_flag(), Ok(ast::Flag::CaseInsensitive));
//         assert_eq!(parser("m").parse_flag(), Ok(ast::Flag::MultiLine));
//         assert_eq!(parser("s").parse_flag(), Ok(ast::Flag::DotMatchesNewLine));
//         assert_eq!(parser("U").parse_flag(), Ok(ast::Flag::SwapGreed));
//         assert_eq!(parser("u").parse_flag(), Ok(ast::Flag::Unicode));
//         assert_eq!(parser("R").parse_flag(), Ok(ast::Flag::CRLF));
//         assert_eq!(parser("x").parse_flag(), Ok(ast::Flag::IgnoreWhitespace));
//
//         assert_eq!(
//             parser("a").parse_flag().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::FlagUnrecognized,
//             }
//         );
//         assert_eq!(
//             parser("☃").parse_flag().unwrap_err(),
//             TestError {
//                 span: span_range("☃", 0..3),
//                 kind: ast::ErrorKind::FlagUnrecognized,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_primitive_non_escape() {
//         assert_eq!(
//             parser(r".").parse_primitive(),
//             Ok(Primitive::Dot(span(0..1)))
//         );
//         assert_eq!(
//             parser(r"^").parse_primitive(),
//             Ok(Primitive::Assertion(ast::Assertion {
//                 span: span(0..1),
//                 kind: ast::AssertionKind::StartLine,
//             }))
//         );
//         assert_eq!(
//             parser(r"$").parse_primitive(),
//             Ok(Primitive::Assertion(ast::Assertion {
//                 span: span(0..1),
//                 kind: ast::AssertionKind::EndLine,
//             }))
//         );
//
//         assert_eq!(
//             parser(r"a").parse_primitive(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span(0..1),
//                 kind: ast::LiteralKind::Verbatim,
//                 c: 'a',
//             }))
//         );
//         assert_eq!(
//             parser(r"|").parse_primitive(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span(0..1),
//                 kind: ast::LiteralKind::Verbatim,
//                 c: '|',
//             }))
//         );
//         assert_eq!(
//             parser(r"☃").parse_primitive(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span_range("☃", 0..3),
//                 kind: ast::LiteralKind::Verbatim,
//                 c: '☃',
//             }))
//         );
//     }
//
//     #[test]
//     fn parse_escape() {
//         assert_eq!(
//             parser(r"\|").parse_primitive(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span(0..2),
//                 kind: ast::LiteralKind::Meta,
//                 c: '|',
//             }))
//         );
//         let specials = &[
//             (r"\a", '\x07', ast::SpecialLiteralKind::Bell),
//             (r"\f", '\x0C', ast::SpecialLiteralKind::FormFeed),
//             (r"\t", '\t', ast::SpecialLiteralKind::Tab),
//             (r"\n", '\n', ast::SpecialLiteralKind::LineFeed),
//             (r"\r", '\r', ast::SpecialLiteralKind::CarriageReturn),
//             (r"\v", '\x0B', ast::SpecialLiteralKind::VerticalTab),
//         ];
//         for &(pat, c, ref kind) in specials {
//             assert_eq!(
//                 parser(pat).parse_primitive(),
//                 Ok(Primitive::Literal(ast::Literal {
//                     span: span(0..2),
//                     kind: ast::LiteralKind::Special(kind.clone()),
//                     c,
//                 }))
//             );
//         }
//         assert_eq!(
//             parser(r"\A").parse_primitive(),
//             Ok(Primitive::Assertion(ast::Assertion {
//                 span: span(0..2),
//                 kind: ast::AssertionKind::StartText,
//             }))
//         );
//         assert_eq!(
//             parser(r"\z").parse_primitive(),
//             Ok(Primitive::Assertion(ast::Assertion {
//                 span: span(0..2),
//                 kind: ast::AssertionKind::EndText,
//             }))
//         );
//         assert_eq!(
//             parser(r"\b").parse_primitive(),
//             Ok(Primitive::Assertion(ast::Assertion {
//                 span: span(0..2),
//                 kind: ast::AssertionKind::WordBoundary,
//             }))
//         );
//         assert_eq!(
//             parser(r"\B").parse_primitive(),
//             Ok(Primitive::Assertion(ast::Assertion {
//                 span: span(0..2),
//                 kind: ast::AssertionKind::NotWordBoundary,
//             }))
//         );
//
//         // We also support superfluous escapes in most cases now too.
//         for c in ['!', '@', '%', '"', '\'', '/', ' '] {
//             let pat = format!(r"\{}", c);
//             assert_eq!(
//                 parser(&pat).parse_primitive(),
//                 Ok(Primitive::Literal(ast::Literal {
//                     span: span(0..2),
//                     kind: ast::LiteralKind::Superfluous,
//                     c,
//                 }))
//             );
//         }
//
//         // Some superfluous escapes, namely [0-9A-Za-z], are still banned. This
//         // gives flexibility for future evolution.
//         assert_eq!(
//             parser(r"\e").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(0..2),
//                 kind: ast::ErrorKind::EscapeUnrecognized,
//             }
//         );
//         assert_eq!(
//             parser(r"\y").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(0..2),
//                 kind: ast::ErrorKind::EscapeUnrecognized,
//             }
//         );
//         // But also, < and > are banned, so that we may evolve them into
//         // start/end word boundary assertions. (Not sure if we will...)
//         assert_eq!(
//             parser(r"\<").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(0..2),
//                 kind: ast::ErrorKind::EscapeUnrecognized,
//             }
//         );
//         assert_eq!(
//             parser(r"\>").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(0..2),
//                 kind: ast::ErrorKind::EscapeUnrecognized,
//             }
//         );
//
//         // An unfinished escape is illegal.
//         assert_eq!(
//             parser(r"\").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_unsupported_backreference() {
//         assert_eq!(
//             parser(r"\0").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(0..2),
//                 kind: ast::ErrorKind::UnsupportedBackreference,
//             }
//         );
//         assert_eq!(
//             parser(r"\9").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(0..2),
//                 kind: ast::ErrorKind::UnsupportedBackreference,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_octal() {
//         for i in 0..511 {
//             let pat = format!(r"\{:o}", i);
//             assert_eq!(
//                 parser_octal(&pat).parse_escape(),
//                 Ok(Primitive::Literal(ast::Literal {
//                     span: span(0..pat.len()),
//                     kind: ast::LiteralKind::Octal,
//                     c: char::from_u32(i).unwrap(),
//                 }))
//             );
//         }
//         assert_eq!(
//             parser_octal(r"\778").parse_escape(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span(0..3),
//                 kind: ast::LiteralKind::Octal,
//                 c: '?',
//             }))
//         );
//         assert_eq!(
//             parser_octal(r"\7777").parse_escape(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span(0..4),
//                 kind: ast::LiteralKind::Octal,
//                 c: '\u{01FF}',
//             }))
//         );
//         assert_eq!(
//             parser_octal(r"\778").parse(),
//             Ok(Ast::Concat(ast::Concat {
//                 span: span(0..4),
//                 asts: vec![
//                     Ast::Literal(ast::Literal {
//                         span: span(0..3),
//                         kind: ast::LiteralKind::Octal,
//                         c: '?',
//                     }),
//                     Ast::Literal(ast::Literal {
//                         span: span(3..4),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: '8',
//                     }),
//                 ],
//             }))
//         );
//         assert_eq!(
//             parser_octal(r"\7777").parse(),
//             Ok(Ast::Concat(ast::Concat {
//                 span: span(0..5),
//                 asts: vec![
//                     Ast::Literal(ast::Literal {
//                         span: span(0..4),
//                         kind: ast::LiteralKind::Octal,
//                         c: '\u{01FF}',
//                     }),
//                     Ast::Literal(ast::Literal {
//                         span: span(4..5),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: '7',
//                     }),
//                 ],
//             }))
//         );
//
//         assert_eq!(
//             parser_octal(r"\8").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(0..2),
//                 kind: ast::ErrorKind::EscapeUnrecognized,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_hex_two() {
//         for i in 0..256 {
//             let pat = format!(r"\x{:02x}", i);
//             assert_eq!(
//                 parser(&pat).parse_escape(),
//                 Ok(Primitive::Literal(ast::Literal {
//                     span: span(0..pat.len()),
//                     kind: ast::LiteralKind::HexFixed(ast::HexLiteralKind::X),
//                     c: char::from_u32(i).unwrap(),
//                 }))
//             );
//         }
//
//         assert_eq!(
//             parser(r"\xF").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(3..3),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser(r"\xG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(2..3),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\xFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(3..4),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_hex_four() {
//         for i in 0..65536 {
//             let c = match char::from_u32(i) {
//                 None => continue,
//                 Some(c) => c,
//             };
//             let pat = format!(r"\u{:04x}", i);
//             assert_eq!(
//                 parser(&pat).parse_escape(),
//                 Ok(Primitive::Literal(ast::Literal {
//                     span: span(0..pat.len()),
//                     kind: ast::LiteralKind::HexFixed(
//                         ast::HexLiteralKind::UnicodeShort
//                     ),
//                     c,
//                 }))
//             );
//         }
//
//         assert_eq!(
//             parser(r"\uF").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(3..3),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser(r"\uG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(2..3),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\uFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(3..4),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\uFFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(4..5),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\uFFFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(5..6),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\uD800").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(2..6),
//                 kind: ast::ErrorKind::EscapeHexInvalid,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_hex_eight() {
//         for i in 0..65536 {
//             let c = match char::from_u32(i) {
//                 None => continue,
//                 Some(c) => c,
//             };
//             let pat = format!(r"\U{:08x}", i);
//             assert_eq!(
//                 parser(&pat).parse_escape(),
//                 Ok(Primitive::Literal(ast::Literal {
//                     span: span(0..pat.len()),
//                     kind: ast::LiteralKind::HexFixed(
//                         ast::HexLiteralKind::UnicodeLong
//                     ),
//                     c,
//                 }))
//             );
//         }
//
//         assert_eq!(
//             parser(r"\UF").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(3..3),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser(r"\UG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(2..3),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\UFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(3..4),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\UFFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(4..5),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\UFFFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(5..6),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\UFFFFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(6..7),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\UFFFFFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(7..8),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\UFFFFFFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(8..9),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\UFFFFFFFG").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(9..10),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_hex_brace() {
//         assert_eq!(
//             parser(r"\u{26c4}").parse_escape(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span(0..8),
//                 kind: ast::LiteralKind::HexBrace(
//                     ast::HexLiteralKind::UnicodeShort
//                 ),
//                 c: '⛄',
//             }))
//         );
//         assert_eq!(
//             parser(r"\U{26c4}").parse_escape(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span(0..8),
//                 kind: ast::LiteralKind::HexBrace(
//                     ast::HexLiteralKind::UnicodeLong
//                 ),
//                 c: '⛄',
//             }))
//         );
//         assert_eq!(
//             parser(r"\x{26c4}").parse_escape(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span(0..8),
//                 kind: ast::LiteralKind::HexBrace(ast::HexLiteralKind::X),
//                 c: '⛄',
//             }))
//         );
//         assert_eq!(
//             parser(r"\x{26C4}").parse_escape(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span(0..8),
//                 kind: ast::LiteralKind::HexBrace(ast::HexLiteralKind::X),
//                 c: '⛄',
//             }))
//         );
//         assert_eq!(
//             parser(r"\x{10fFfF}").parse_escape(),
//             Ok(Primitive::Literal(ast::Literal {
//                 span: span(0..10),
//                 kind: ast::LiteralKind::HexBrace(ast::HexLiteralKind::X),
//                 c: '\u{10FFFF}',
//             }))
//         );
//
//         assert_eq!(
//             parser(r"\x").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(2..2),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser(r"\x{").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(2..3),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser(r"\x{FF").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(2..5),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser(r"\x{}").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(2..4),
//                 kind: ast::ErrorKind::EscapeHexEmpty,
//             }
//         );
//         assert_eq!(
//             parser(r"\x{FGF}").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(4..5),
//                 kind: ast::ErrorKind::EscapeHexInvalidDigit,
//             }
//         );
//         assert_eq!(
//             parser(r"\x{FFFFFF}").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(3..9),
//                 kind: ast::ErrorKind::EscapeHexInvalid,
//             }
//         );
//         assert_eq!(
//             parser(r"\x{D800}").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(3..7),
//                 kind: ast::ErrorKind::EscapeHexInvalid,
//             }
//         );
//         assert_eq!(
//             parser(r"\x{FFFFFFFFF}").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(3..12),
//                 kind: ast::ErrorKind::EscapeHexInvalid,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_decimal() {
//         assert_eq!(parser("123").parse_decimal(), Ok(123));
//         assert_eq!(parser("0").parse_decimal(), Ok(0));
//         assert_eq!(parser("01").parse_decimal(), Ok(1));
//
//         assert_eq!(
//             parser("-1").parse_decimal().unwrap_err(),
//             TestError { span: span(0..0), kind: ast::ErrorKind::DecimalEmpty }
//         );
//         assert_eq!(
//             parser("").parse_decimal().unwrap_err(),
//             TestError { span: span(0..0), kind: ast::ErrorKind::DecimalEmpty }
//         );
//         assert_eq!(
//             parser("9999999999").parse_decimal().unwrap_err(),
//             TestError {
//                 span: span(0..10),
//                 kind: ast::ErrorKind::DecimalInvalid,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_set_class() {
//         fn union(span: Span, items: Vec<ast::ClassSetItem>) -> ast::ClassSet {
//             ast::ClassSet::union(ast::ClassSetUnion { span, items })
//         }
//
//         fn intersection(
//             span: Span,
//             lhs: ast::ClassSet,
//             rhs: ast::ClassSet,
//         ) -> ast::ClassSet {
//             ast::ClassSet::BinaryOp(ast::ClassSetBinaryOp {
//                 span,
//                 kind: ast::ClassSetBinaryOpKind::Intersection,
//                 lhs: Box::new(lhs),
//                 rhs: Box::new(rhs),
//             })
//         }
//
//         fn difference(
//             span: Span,
//             lhs: ast::ClassSet,
//             rhs: ast::ClassSet,
//         ) -> ast::ClassSet {
//             ast::ClassSet::BinaryOp(ast::ClassSetBinaryOp {
//                 span,
//                 kind: ast::ClassSetBinaryOpKind::Difference,
//                 lhs: Box::new(lhs),
//                 rhs: Box::new(rhs),
//             })
//         }
//
//         fn symdifference(
//             span: Span,
//             lhs: ast::ClassSet,
//             rhs: ast::ClassSet,
//         ) -> ast::ClassSet {
//             ast::ClassSet::BinaryOp(ast::ClassSetBinaryOp {
//                 span,
//                 kind: ast::ClassSetBinaryOpKind::SymmetricDifference,
//                 lhs: Box::new(lhs),
//                 rhs: Box::new(rhs),
//             })
//         }
//
//         fn itemset(item: ast::ClassSetItem) -> ast::ClassSet {
//             ast::ClassSet::Item(item)
//         }
//
//         fn item_ascii(cls: ast::ClassAscii) -> ast::ClassSetItem {
//             ast::ClassSetItem::Ascii(cls)
//         }
//
//         fn item_unicode(cls: ast::ClassUnicode) -> ast::ClassSetItem {
//             ast::ClassSetItem::Unicode(cls)
//         }
//
//         fn item_perl(cls: ast::ClassPerl) -> ast::ClassSetItem {
//             ast::ClassSetItem::Perl(cls)
//         }
//
//         fn item_bracket(cls: ast::ClassBracketed) -> ast::ClassSetItem {
//             ast::ClassSetItem::Bracketed(Box::new(cls))
//         }
//
//         fn lit(span: Span, c: char) -> ast::ClassSetItem {
//             ast::ClassSetItem::Literal(ast::Literal {
//                 span,
//                 kind: ast::LiteralKind::Verbatim,
//                 c,
//             })
//         }
//
//         fn empty(span: Span) -> ast::ClassSetItem {
//             ast::ClassSetItem::Empty(span)
//         }
//
//         fn range(span: Span, start: char, end: char) -> ast::ClassSetItem {
//             let pos1 = Position {
//                 offset: span.start.offset + start.len_utf8(),
//                 column: span.start.column + 1,
//                 ..span.start
//             };
//             let pos2 = Position {
//                 offset: span.end.offset - end.len_utf8(),
//                 column: span.end.column - 1,
//                 ..span.end
//             };
//             ast::ClassSetItem::Range(ast::ClassSetRange {
//                 span,
//                 start: ast::Literal {
//                     span: Span { end: pos1, ..span },
//                     kind: ast::LiteralKind::Verbatim,
//                     c: start,
//                 },
//                 end: ast::Literal {
//                     span: Span { start: pos2, ..span },
//                     kind: ast::LiteralKind::Verbatim,
//                     c: end,
//                 },
//             })
//         }
//
//         fn alnum(span: Span, negated: bool) -> ast::ClassAscii {
//             ast::ClassAscii { span, kind: ast::ClassAsciiKind::Alnum, negated }
//         }
//
//         fn lower(span: Span, negated: bool) -> ast::ClassAscii {
//             ast::ClassAscii { span, kind: ast::ClassAsciiKind::Lower, negated }
//         }
//
//         assert_eq!(
//             parser("[[:alnum:]]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..11),
//                 negated: false,
//                 kind: itemset(item_ascii(alnum(span(1..10), false))),
//             })))
//         );
//         assert_eq!(
//             parser("[[[:alnum:]]]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..13),
//                 negated: false,
//                 kind: itemset(item_bracket(ast::ClassBracketed {
//                     span: span(1..12),
//                     negated: false,
//                     kind: itemset(item_ascii(alnum(span(2..11), false))),
//                 })),
//             })))
//         );
//         assert_eq!(
//             parser("[[:alnum:]&&[:lower:]]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..22),
//                 negated: false,
//                 kind: intersection(
//                     span(1..21),
//                     itemset(item_ascii(alnum(span(1..10), false))),
//                     itemset(item_ascii(lower(span(12..21), false))),
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser("[[:alnum:]--[:lower:]]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..22),
//                 negated: false,
//                 kind: difference(
//                     span(1..21),
//                     itemset(item_ascii(alnum(span(1..10), false))),
//                     itemset(item_ascii(lower(span(12..21), false))),
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser("[[:alnum:]~~[:lower:]]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..22),
//                 negated: false,
//                 kind: symdifference(
//                     span(1..21),
//                     itemset(item_ascii(alnum(span(1..10), false))),
//                     itemset(item_ascii(lower(span(12..21), false))),
//                 ),
//             })))
//         );
//
//         assert_eq!(
//             parser("[a]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..3),
//                 negated: false,
//                 kind: itemset(lit(span(1..2), 'a')),
//             })))
//         );
//         assert_eq!(
//             parser(r"[a\]]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..5),
//                 negated: false,
//                 kind: union(
//                     span(1..4),
//                     vec![
//                         lit(span(1..2), 'a'),
//                         ast::ClassSetItem::Literal(ast::Literal {
//                             span: span(2..4),
//                             kind: ast::LiteralKind::Meta,
//                             c: ']',
//                         }),
//                     ]
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser(r"[a\-z]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..6),
//                 negated: false,
//                 kind: union(
//                     span(1..5),
//                     vec![
//                         lit(span(1..2), 'a'),
//                         ast::ClassSetItem::Literal(ast::Literal {
//                             span: span(2..4),
//                             kind: ast::LiteralKind::Meta,
//                             c: '-',
//                         }),
//                         lit(span(4..5), 'z'),
//                     ]
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser("[ab]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..4),
//                 negated: false,
//                 kind: union(
//                     span(1..3),
//                     vec![lit(span(1..2), 'a'), lit(span(2..3), 'b'),]
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser("[a-]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..4),
//                 negated: false,
//                 kind: union(
//                     span(1..3),
//                     vec![lit(span(1..2), 'a'), lit(span(2..3), '-'),]
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser("[-a]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..4),
//                 negated: false,
//                 kind: union(
//                     span(1..3),
//                     vec![lit(span(1..2), '-'), lit(span(2..3), 'a'),]
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser(r"[\pL]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..5),
//                 negated: false,
//                 kind: itemset(item_unicode(ast::ClassUnicode {
//                     span: span(1..4),
//                     negated: false,
//                     kind: ast::ClassUnicodeKind::OneLetter('L'),
//                 })),
//             })))
//         );
//         assert_eq!(
//             parser(r"[\w]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..4),
//                 negated: false,
//                 kind: itemset(item_perl(ast::ClassPerl {
//                     span: span(1..3),
//                     kind: ast::ClassPerlKind::Word,
//                     negated: false,
//                 })),
//             })))
//         );
//         assert_eq!(
//             parser(r"[a\wz]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..6),
//                 negated: false,
//                 kind: union(
//                     span(1..5),
//                     vec![
//                         lit(span(1..2), 'a'),
//                         item_perl(ast::ClassPerl {
//                             span: span(2..4),
//                             kind: ast::ClassPerlKind::Word,
//                             negated: false,
//                         }),
//                         lit(span(4..5), 'z'),
//                     ]
//                 ),
//             })))
//         );
//
//         assert_eq!(
//             parser("[a-z]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..5),
//                 negated: false,
//                 kind: itemset(range(span(1..4), 'a', 'z')),
//             })))
//         );
//         assert_eq!(
//             parser("[a-cx-z]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..8),
//                 negated: false,
//                 kind: union(
//                     span(1..7),
//                     vec![
//                         range(span(1..4), 'a', 'c'),
//                         range(span(4..7), 'x', 'z'),
//                     ]
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser(r"[\w&&a-cx-z]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..12),
//                 negated: false,
//                 kind: intersection(
//                     span(1..11),
//                     itemset(item_perl(ast::ClassPerl {
//                         span: span(1..3),
//                         kind: ast::ClassPerlKind::Word,
//                         negated: false,
//                     })),
//                     union(
//                         span(5..11),
//                         vec![
//                             range(span(5..8), 'a', 'c'),
//                             range(span(8..11), 'x', 'z'),
//                         ]
//                     ),
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser(r"[a-cx-z&&\w]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..12),
//                 negated: false,
//                 kind: intersection(
//                     span(1..11),
//                     union(
//                         span(1..7),
//                         vec![
//                             range(span(1..4), 'a', 'c'),
//                             range(span(4..7), 'x', 'z'),
//                         ]
//                     ),
//                     itemset(item_perl(ast::ClassPerl {
//                         span: span(9..11),
//                         kind: ast::ClassPerlKind::Word,
//                         negated: false,
//                     })),
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser(r"[a--b--c]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..9),
//                 negated: false,
//                 kind: difference(
//                     span(1..8),
//                     difference(
//                         span(1..5),
//                         itemset(lit(span(1..2), 'a')),
//                         itemset(lit(span(4..5), 'b')),
//                     ),
//                     itemset(lit(span(7..8), 'c')),
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser(r"[a~~b~~c]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..9),
//                 negated: false,
//                 kind: symdifference(
//                     span(1..8),
//                     symdifference(
//                         span(1..5),
//                         itemset(lit(span(1..2), 'a')),
//                         itemset(lit(span(4..5), 'b')),
//                     ),
//                     itemset(lit(span(7..8), 'c')),
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser(r"[\^&&^]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..7),
//                 negated: false,
//                 kind: intersection(
//                     span(1..6),
//                     itemset(ast::ClassSetItem::Literal(ast::Literal {
//                         span: span(1..3),
//                         kind: ast::LiteralKind::Meta,
//                         c: '^',
//                     })),
//                     itemset(lit(span(5..6), '^')),
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser(r"[\&&&&]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..7),
//                 negated: false,
//                 kind: intersection(
//                     span(1..6),
//                     itemset(ast::ClassSetItem::Literal(ast::Literal {
//                         span: span(1..3),
//                         kind: ast::LiteralKind::Meta,
//                         c: '&',
//                     })),
//                     itemset(lit(span(5..6), '&')),
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser(r"[&&&&]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..6),
//                 negated: false,
//                 kind: intersection(
//                     span(1..5),
//                     intersection(
//                         span(1..3),
//                         itemset(empty(span(1..1))),
//                         itemset(empty(span(3..3))),
//                     ),
//                     itemset(empty(span(5..5))),
//                 ),
//             })))
//         );
//
//         let pat = "[☃-⛄]";
//         assert_eq!(
//             parser(pat).parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span_range(pat, 0..9),
//                 negated: false,
//                 kind: itemset(ast::ClassSetItem::Range(ast::ClassSetRange {
//                     span: span_range(pat, 1..8),
//                     start: ast::Literal {
//                         span: span_range(pat, 1..4),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: '☃',
//                     },
//                     end: ast::Literal {
//                         span: span_range(pat, 5..8),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: '⛄',
//                     },
//                 })),
//             })))
//         );
//
//         assert_eq!(
//             parser(r"[]]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..3),
//                 negated: false,
//                 kind: itemset(lit(span(1..2), ']')),
//             })))
//         );
//         assert_eq!(
//             parser(r"[]\[]").parse(),
//             Ok(Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                 span: span(0..5),
//                 negated: false,
//                 kind: union(
//                     span(1..4),
//                     vec![
//                         lit(span(1..2), ']'),
//                         ast::ClassSetItem::Literal(ast::Literal {
//                             span: span(2..4),
//                             kind: ast::LiteralKind::Meta,
//                             c: '[',
//                         }),
//                     ]
//                 ),
//             })))
//         );
//         assert_eq!(
//             parser(r"[\[]]").parse(),
//             Ok(concat(
//                 0..5,
//                 vec![
//                     Ast::Class(ast::Class::Bracketed(ast::ClassBracketed {
//                         span: span(0..4),
//                         negated: false,
//                         kind: itemset(ast::ClassSetItem::Literal(
//                             ast::Literal {
//                                 span: span(1..3),
//                                 kind: ast::LiteralKind::Meta,
//                                 c: '[',
//                             }
//                         )),
//                     })),
//                     Ast::Literal(ast::Literal {
//                         span: span(4..5),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: ']',
//                     }),
//                 ]
//             ))
//         );
//
//         assert_eq!(
//             parser("[").parse().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//         assert_eq!(
//             parser("[[").parse().unwrap_err(),
//             TestError {
//                 span: span(1..2),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//         assert_eq!(
//             parser("[[-]").parse().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//         assert_eq!(
//             parser("[[[:alnum:]").parse().unwrap_err(),
//             TestError {
//                 span: span(1..2),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//         assert_eq!(
//             parser(r"[\b]").parse().unwrap_err(),
//             TestError {
//                 span: span(1..3),
//                 kind: ast::ErrorKind::ClassEscapeInvalid,
//             }
//         );
//         assert_eq!(
//             parser(r"[\w-a]").parse().unwrap_err(),
//             TestError {
//                 span: span(1..3),
//                 kind: ast::ErrorKind::ClassRangeLiteral,
//             }
//         );
//         assert_eq!(
//             parser(r"[a-\w]").parse().unwrap_err(),
//             TestError {
//                 span: span(3..5),
//                 kind: ast::ErrorKind::ClassRangeLiteral,
//             }
//         );
//         assert_eq!(
//             parser(r"[z-a]").parse().unwrap_err(),
//             TestError {
//                 span: span(1..4),
//                 kind: ast::ErrorKind::ClassRangeInvalid,
//             }
//         );
//
//         assert_eq!(
//             parser_ignore_whitespace("[a ").parse().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//         assert_eq!(
//             parser_ignore_whitespace("[a- ").parse().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_set_class_open() {
//         assert_eq!(parser("[a]").parse_set_class_open(), {
//             let set = ast::ClassBracketed {
//                 span: span(0..1),
//                 negated: false,
//                 kind: ast::ClassSet::union(ast::ClassSetUnion {
//                     span: span(1..1),
//                     items: vec![],
//                 }),
//             };
//             let union = ast::ClassSetUnion { span: span(1..1), items: vec![] };
//             Ok((set, union))
//         });
//         assert_eq!(
//             parser_ignore_whitespace("[   a]").parse_set_class_open(),
//             {
//                 let set = ast::ClassBracketed {
//                     span: span(0..4),
//                     negated: false,
//                     kind: ast::ClassSet::union(ast::ClassSetUnion {
//                         span: span(4..4),
//                         items: vec![],
//                     }),
//                 };
//                 let union =
//                     ast::ClassSetUnion { span: span(4..4), items: vec![] };
//                 Ok((set, union))
//             }
//         );
//         assert_eq!(parser("[^a]").parse_set_class_open(), {
//             let set = ast::ClassBracketed {
//                 span: span(0..2),
//                 negated: true,
//                 kind: ast::ClassSet::union(ast::ClassSetUnion {
//                     span: span(2..2),
//                     items: vec![],
//                 }),
//             };
//             let union = ast::ClassSetUnion { span: span(2..2), items: vec![] };
//             Ok((set, union))
//         });
//         assert_eq!(
//             parser_ignore_whitespace("[ ^ a]").parse_set_class_open(),
//             {
//                 let set = ast::ClassBracketed {
//                     span: span(0..4),
//                     negated: true,
//                     kind: ast::ClassSet::union(ast::ClassSetUnion {
//                         span: span(4..4),
//                         items: vec![],
//                     }),
//                 };
//                 let union =
//                     ast::ClassSetUnion { span: span(4..4), items: vec![] };
//                 Ok((set, union))
//             }
//         );
//         assert_eq!(parser("[-a]").parse_set_class_open(), {
//             let set = ast::ClassBracketed {
//                 span: span(0..2),
//                 negated: false,
//                 kind: ast::ClassSet::union(ast::ClassSetUnion {
//                     span: span(1..1),
//                     items: vec![],
//                 }),
//             };
//             let union = ast::ClassSetUnion {
//                 span: span(1..2),
//                 items: vec![ast::ClassSetItem::Literal(ast::Literal {
//                     span: span(1..2),
//                     kind: ast::LiteralKind::Verbatim,
//                     c: '-',
//                 })],
//             };
//             Ok((set, union))
//         });
//         assert_eq!(
//             parser_ignore_whitespace("[ - a]").parse_set_class_open(),
//             {
//                 let set = ast::ClassBracketed {
//                     span: span(0..4),
//                     negated: false,
//                     kind: ast::ClassSet::union(ast::ClassSetUnion {
//                         span: span(2..2),
//                         items: vec![],
//                     }),
//                 };
//                 let union = ast::ClassSetUnion {
//                     span: span(2..3),
//                     items: vec![ast::ClassSetItem::Literal(ast::Literal {
//                         span: span(2..3),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: '-',
//                     })],
//                 };
//                 Ok((set, union))
//             }
//         );
//         assert_eq!(parser("[^-a]").parse_set_class_open(), {
//             let set = ast::ClassBracketed {
//                 span: span(0..3),
//                 negated: true,
//                 kind: ast::ClassSet::union(ast::ClassSetUnion {
//                     span: span(2..2),
//                     items: vec![],
//                 }),
//             };
//             let union = ast::ClassSetUnion {
//                 span: span(2..3),
//                 items: vec![ast::ClassSetItem::Literal(ast::Literal {
//                     span: span(2..3),
//                     kind: ast::LiteralKind::Verbatim,
//                     c: '-',
//                 })],
//             };
//             Ok((set, union))
//         });
//         assert_eq!(parser("[--a]").parse_set_class_open(), {
//             let set = ast::ClassBracketed {
//                 span: span(0..3),
//                 negated: false,
//                 kind: ast::ClassSet::union(ast::ClassSetUnion {
//                     span: span(1..1),
//                     items: vec![],
//                 }),
//             };
//             let union = ast::ClassSetUnion {
//                 span: span(1..3),
//                 items: vec![
//                     ast::ClassSetItem::Literal(ast::Literal {
//                         span: span(1..2),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: '-',
//                     }),
//                     ast::ClassSetItem::Literal(ast::Literal {
//                         span: span(2..3),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: '-',
//                     }),
//                 ],
//             };
//             Ok((set, union))
//         });
//         assert_eq!(parser("[]a]").parse_set_class_open(), {
//             let set = ast::ClassBracketed {
//                 span: span(0..2),
//                 negated: false,
//                 kind: ast::ClassSet::union(ast::ClassSetUnion {
//                     span: span(1..1),
//                     items: vec![],
//                 }),
//             };
//             let union = ast::ClassSetUnion {
//                 span: span(1..2),
//                 items: vec![ast::ClassSetItem::Literal(ast::Literal {
//                     span: span(1..2),
//                     kind: ast::LiteralKind::Verbatim,
//                     c: ']',
//                 })],
//             };
//             Ok((set, union))
//         });
//         assert_eq!(
//             parser_ignore_whitespace("[ ] a]").parse_set_class_open(),
//             {
//                 let set = ast::ClassBracketed {
//                     span: span(0..4),
//                     negated: false,
//                     kind: ast::ClassSet::union(ast::ClassSetUnion {
//                         span: span(2..2),
//                         items: vec![],
//                     }),
//                 };
//                 let union = ast::ClassSetUnion {
//                     span: span(2..3),
//                     items: vec![ast::ClassSetItem::Literal(ast::Literal {
//                         span: span(2..3),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: ']',
//                     })],
//                 };
//                 Ok((set, union))
//             }
//         );
//         assert_eq!(parser("[^]a]").parse_set_class_open(), {
//             let set = ast::ClassBracketed {
//                 span: span(0..3),
//                 negated: true,
//                 kind: ast::ClassSet::union(ast::ClassSetUnion {
//                     span: span(2..2),
//                     items: vec![],
//                 }),
//             };
//             let union = ast::ClassSetUnion {
//                 span: span(2..3),
//                 items: vec![ast::ClassSetItem::Literal(ast::Literal {
//                     span: span(2..3),
//                     kind: ast::LiteralKind::Verbatim,
//                     c: ']',
//                 })],
//             };
//             Ok((set, union))
//         });
//         assert_eq!(parser("[-]a]").parse_set_class_open(), {
//             let set = ast::ClassBracketed {
//                 span: span(0..2),
//                 negated: false,
//                 kind: ast::ClassSet::union(ast::ClassSetUnion {
//                     span: span(1..1),
//                     items: vec![],
//                 }),
//             };
//             let union = ast::ClassSetUnion {
//                 span: span(1..2),
//                 items: vec![ast::ClassSetItem::Literal(ast::Literal {
//                     span: span(1..2),
//                     kind: ast::LiteralKind::Verbatim,
//                     c: '-',
//                 })],
//             };
//             Ok((set, union))
//         });
//
//         assert_eq!(
//             parser("[").parse_set_class_open().unwrap_err(),
//             TestError {
//                 span: span(0..1),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//         assert_eq!(
//             parser_ignore_whitespace("[    ")
//                 .parse_set_class_open()
//                 .unwrap_err(),
//             TestError {
//                 span: span(0..5),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//         assert_eq!(
//             parser("[^").parse_set_class_open().unwrap_err(),
//             TestError {
//                 span: span(0..2),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//         assert_eq!(
//             parser("[]").parse_set_class_open().unwrap_err(),
//             TestError {
//                 span: span(0..2),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//         assert_eq!(
//             parser("[-").parse_set_class_open().unwrap_err(),
//             TestError {
//                 span: span(0..0),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//         assert_eq!(
//             parser("[--").parse_set_class_open().unwrap_err(),
//             TestError {
//                 span: span(0..0),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//
//         // See: https://github.com/rust-lang/regex/issues/792
//         assert_eq!(
//             parser("(?x)[-#]").parse_with_comments().unwrap_err(),
//             TestError {
//                 span: span(4..4),
//                 kind: ast::ErrorKind::ClassUnclosed,
//             }
//         );
//     }
//
//     #[test]
//     fn maybe_parse_ascii_class() {
//         assert_eq!(
//             parser(r"[:alnum:]").maybe_parse_ascii_class(),
//             Some(ast::ClassAscii {
//                 span: span(0..9),
//                 kind: ast::ClassAsciiKind::Alnum,
//                 negated: false,
//             })
//         );
//         assert_eq!(
//             parser(r"[:alnum:]A").maybe_parse_ascii_class(),
//             Some(ast::ClassAscii {
//                 span: span(0..9),
//                 kind: ast::ClassAsciiKind::Alnum,
//                 negated: false,
//             })
//         );
//         assert_eq!(
//             parser(r"[:^alnum:]").maybe_parse_ascii_class(),
//             Some(ast::ClassAscii {
//                 span: span(0..10),
//                 kind: ast::ClassAsciiKind::Alnum,
//                 negated: true,
//             })
//         );
//
//         let p = parser(r"[:");
//         assert_eq!(p.maybe_parse_ascii_class(), None);
//         assert_eq!(p.offset(), 0);
//
//         let p = parser(r"[:^");
//         assert_eq!(p.maybe_parse_ascii_class(), None);
//         assert_eq!(p.offset(), 0);
//
//         let p = parser(r"[^:alnum:]");
//         assert_eq!(p.maybe_parse_ascii_class(), None);
//         assert_eq!(p.offset(), 0);
//
//         let p = parser(r"[:alnnum:]");
//         assert_eq!(p.maybe_parse_ascii_class(), None);
//         assert_eq!(p.offset(), 0);
//
//         let p = parser(r"[:alnum]");
//         assert_eq!(p.maybe_parse_ascii_class(), None);
//         assert_eq!(p.offset(), 0);
//
//         let p = parser(r"[:alnum:");
//         assert_eq!(p.maybe_parse_ascii_class(), None);
//         assert_eq!(p.offset(), 0);
//     }
//
//     #[test]
//     fn parse_unicode_class() {
//         assert_eq!(
//             parser(r"\pN").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..3),
//                 negated: false,
//                 kind: ast::ClassUnicodeKind::OneLetter('N'),
//             }))
//         );
//         assert_eq!(
//             parser(r"\PN").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..3),
//                 negated: true,
//                 kind: ast::ClassUnicodeKind::OneLetter('N'),
//             }))
//         );
//         assert_eq!(
//             parser(r"\p{N}").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..5),
//                 negated: false,
//                 kind: ast::ClassUnicodeKind::Named(s("N")),
//             }))
//         );
//         assert_eq!(
//             parser(r"\P{N}").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..5),
//                 negated: true,
//                 kind: ast::ClassUnicodeKind::Named(s("N")),
//             }))
//         );
//         assert_eq!(
//             parser(r"\p{Greek}").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..9),
//                 negated: false,
//                 kind: ast::ClassUnicodeKind::Named(s("Greek")),
//             }))
//         );
//
//         assert_eq!(
//             parser(r"\p{scx:Katakana}").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..16),
//                 negated: false,
//                 kind: ast::ClassUnicodeKind::NamedValue {
//                     op: ast::ClassUnicodeOpKind::Colon,
//                     name: s("scx"),
//                     value: s("Katakana"),
//                 },
//             }))
//         );
//         assert_eq!(
//             parser(r"\p{scx=Katakana}").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..16),
//                 negated: false,
//                 kind: ast::ClassUnicodeKind::NamedValue {
//                     op: ast::ClassUnicodeOpKind::Equal,
//                     name: s("scx"),
//                     value: s("Katakana"),
//                 },
//             }))
//         );
//         assert_eq!(
//             parser(r"\p{scx!=Katakana}").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..17),
//                 negated: false,
//                 kind: ast::ClassUnicodeKind::NamedValue {
//                     op: ast::ClassUnicodeOpKind::NotEqual,
//                     name: s("scx"),
//                     value: s("Katakana"),
//                 },
//             }))
//         );
//
//         assert_eq!(
//             parser(r"\p{:}").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..5),
//                 negated: false,
//                 kind: ast::ClassUnicodeKind::NamedValue {
//                     op: ast::ClassUnicodeOpKind::Colon,
//                     name: s(""),
//                     value: s(""),
//                 },
//             }))
//         );
//         assert_eq!(
//             parser(r"\p{=}").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..5),
//                 negated: false,
//                 kind: ast::ClassUnicodeKind::NamedValue {
//                     op: ast::ClassUnicodeOpKind::Equal,
//                     name: s(""),
//                     value: s(""),
//                 },
//             }))
//         );
//         assert_eq!(
//             parser(r"\p{!=}").parse_escape(),
//             Ok(Primitive::Unicode(ast::ClassUnicode {
//                 span: span(0..6),
//                 negated: false,
//                 kind: ast::ClassUnicodeKind::NamedValue {
//                     op: ast::ClassUnicodeOpKind::NotEqual,
//                     name: s(""),
//                     value: s(""),
//                 },
//             }))
//         );
//
//         assert_eq!(
//             parser(r"\p").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(2..2),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser(r"\p{").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(3..3),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser(r"\p{N").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(4..4),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//         assert_eq!(
//             parser(r"\p{Greek").parse_escape().unwrap_err(),
//             TestError {
//                 span: span(8..8),
//                 kind: ast::ErrorKind::EscapeUnexpectedEof,
//             }
//         );
//
//         assert_eq!(
//             parser(r"\pNz").parse(),
//             Ok(Ast::Concat(ast::Concat {
//                 span: span(0..4),
//                 asts: vec![
//                     Ast::Class(ast::Class::Unicode(ast::ClassUnicode {
//                         span: span(0..3),
//                         negated: false,
//                         kind: ast::ClassUnicodeKind::OneLetter('N'),
//                     })),
//                     Ast::Literal(ast::Literal {
//                         span: span(3..4),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: 'z',
//                     }),
//                 ],
//             }))
//         );
//         assert_eq!(
//             parser(r"\p{Greek}z").parse(),
//             Ok(Ast::Concat(ast::Concat {
//                 span: span(0..10),
//                 asts: vec![
//                     Ast::Class(ast::Class::Unicode(ast::ClassUnicode {
//                         span: span(0..9),
//                         negated: false,
//                         kind: ast::ClassUnicodeKind::Named(s("Greek")),
//                     })),
//                     Ast::Literal(ast::Literal {
//                         span: span(9..10),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: 'z',
//                     }),
//                 ],
//             }))
//         );
//         assert_eq!(
//             parser(r"\p\{").parse().unwrap_err(),
//             TestError {
//                 span: span(2..3),
//                 kind: ast::ErrorKind::UnicodeClassInvalid,
//             }
//         );
//         assert_eq!(
//             parser(r"\P\{").parse().unwrap_err(),
//             TestError {
//                 span: span(2..3),
//                 kind: ast::ErrorKind::UnicodeClassInvalid,
//             }
//         );
//     }
//
//     #[test]
//     fn parse_perl_class() {
//         assert_eq!(
//             parser(r"\d").parse_escape(),
//             Ok(Primitive::Perl(ast::ClassPerl {
//                 span: span(0..2),
//                 kind: ast::ClassPerlKind::Digit,
//                 negated: false,
//             }))
//         );
//         assert_eq!(
//             parser(r"\D").parse_escape(),
//             Ok(Primitive::Perl(ast::ClassPerl {
//                 span: span(0..2),
//                 kind: ast::ClassPerlKind::Digit,
//                 negated: true,
//             }))
//         );
//         assert_eq!(
//             parser(r"\s").parse_escape(),
//             Ok(Primitive::Perl(ast::ClassPerl {
//                 span: span(0..2),
//                 kind: ast::ClassPerlKind::Space,
//                 negated: false,
//             }))
//         );
//         assert_eq!(
//             parser(r"\S").parse_escape(),
//             Ok(Primitive::Perl(ast::ClassPerl {
//                 span: span(0..2),
//                 kind: ast::ClassPerlKind::Space,
//                 negated: true,
//             }))
//         );
//         assert_eq!(
//             parser(r"\w").parse_escape(),
//             Ok(Primitive::Perl(ast::ClassPerl {
//                 span: span(0..2),
//                 kind: ast::ClassPerlKind::Word,
//                 negated: false,
//             }))
//         );
//         assert_eq!(
//             parser(r"\W").parse_escape(),
//             Ok(Primitive::Perl(ast::ClassPerl {
//                 span: span(0..2),
//                 kind: ast::ClassPerlKind::Word,
//                 negated: true,
//             }))
//         );
//
//         assert_eq!(
//             parser(r"\d").parse(),
//             Ok(Ast::Class(ast::Class::Perl(ast::ClassPerl {
//                 span: span(0..2),
//                 kind: ast::ClassPerlKind::Digit,
//                 negated: false,
//             })))
//         );
//         assert_eq!(
//             parser(r"\dz").parse(),
//             Ok(Ast::Concat(ast::Concat {
//                 span: span(0..3),
//                 asts: vec![
//                     Ast::Class(ast::Class::Perl(ast::ClassPerl {
//                         span: span(0..2),
//                         kind: ast::ClassPerlKind::Digit,
//                         negated: false,
//                     })),
//                     Ast::Literal(ast::Literal {
//                         span: span(2..3),
//                         kind: ast::LiteralKind::Verbatim,
//                         c: 'z',
//                     }),
//                 ],
//             }))
//         );
//     }
//
//     // This tests a bug fix where the nest limit checker wasn't decrementing
//     // its depth during post-traversal, which causes long regexes to trip
//     // the default limit too aggressively.
//     #[test]
//     fn regression_454_nest_too_big() {
//         let pattern = r#"
//         2(?:
//           [45]\d{3}|
//           7(?:
//             1[0-267]|
//             2[0-289]|
//             3[0-29]|
//             4[01]|
//             5[1-3]|
//             6[013]|
//             7[0178]|
//             91
//           )|
//           8(?:
//             0[125]|
//             [139][1-6]|
//             2[0157-9]|
//             41|
//             6[1-35]|
//             7[1-5]|
//             8[1-8]|
//             90
//           )|
//           9(?:
//             0[0-2]|
//             1[0-4]|
//             2[568]|
//             3[3-6]|
//             5[5-7]|
//             6[0167]|
//             7[15]|
//             8[0146-9]
//           )
//         )\d{4}
//         "#;
//         assert!(parser_nest_limit(pattern, 50).parse().is_ok());
//     }
//
//     // This tests that we treat a trailing `-` in a character class as a
//     // literal `-` even when whitespace mode is enabled and there is whitespace
//     // after the trailing `-`.
//     #[test]
//     fn regression_455_trailing_dash_ignore_whitespace() {
//         assert!(parser("(?x)[ / - ]").parse().is_ok());
//         assert!(parser("(?x)[ a - ]").parse().is_ok());
//         assert!(parser(
//             "(?x)[
//             a
//             - ]
//         "
//         )
//         .parse()
//         .is_ok());
//         assert!(parser(
//             "(?x)[
//             a # wat
//             - ]
//         "
//         )
//         .parse()
//         .is_ok());
//
//         assert!(parser("(?x)[ / -").parse().is_err());
//         assert!(parser("(?x)[ / - ").parse().is_err());
//         assert!(parser(
//             "(?x)[
//             / -
//         "
//         )
//         .parse()
//         .is_err());
//         assert!(parser(
//             "(?x)[
//             / - # wat
//         "
//         )
//         .parse()
//         .is_err());
//     }
// }

/*!
This module provides a regular expression printer for `Ast`.
*/

use core::fmt;

use crate::ast::{
    self,
    visitor::{self, Visitor},
    Ast,
};

/// A builder for constructing a printer.
///
/// Note that since a printer doesn't have any configuration knobs, this type
/// remains unexported.
#[derive(Clone, Debug)]
struct PrinterBuilder {
    _priv: (),
}

impl Default for PrinterBuilder {
    fn default() -> PrinterBuilder {
        PrinterBuilder::new()
    }
}

impl PrinterBuilder {
    fn new() -> PrinterBuilder {
        PrinterBuilder { _priv: () }
    }

    fn build(&self) -> Printer {
        Printer { _priv: () }
    }
}

/// A printer for a regular expression abstract syntax tree.
///
/// A printer converts an abstract syntax tree (AST) to a regular expression
/// pattern string. This particular printer uses constant stack space and heap
/// space proportional to the size of the AST.
///
/// This printer will not necessarily preserve the original formatting of the
/// regular expression pattern string. For example, all whitespace and comments
/// are ignored.
#[derive(Debug)]
pub struct Printer {
    _priv: (),
}

impl Printer {
    /// Create a new printer.
    pub fn new() -> Printer {
        PrinterBuilder::new().build()
    }

    /// Print the given `Ast` to the given writer. The writer must implement
    /// `fmt::Write`. Typical implementations of `fmt::Write` that can be used
    /// here are a `fmt::Formatter` (which is available in `fmt::Display`
    /// implementations) or a `&mut String`.
    pub fn print<W: fmt::Write>(&mut self, ast: &Ast, wtr: W) -> fmt::Result {
        visitor::visit(ast, Writer { wtr })
    }
}

#[derive(Debug)]
struct Writer<W> {
    wtr: W,
}

impl<W: fmt::Write> Visitor for Writer<W> {
    type Output = ();
    type Err = fmt::Error;
    fn finish(self) -> fmt::Result {
        Ok(())
    }

    fn visit_pre(&mut self, ast: &Ast) -> fmt::Result {
        match *ast {
            Ast::Group(_) => self.fmt_group_pre(),
            Ast::Class(ref x) => self.fmt_class_pre(x),
            _ => Ok(()),
        }
    }

    fn visit_post(&mut self, ast: &Ast) -> fmt::Result {
        match *ast {
            Ast::Empty(_) => Ok(()),
            Ast::Literal(ref x) => self.fmt_literal(x),
            Ast::Dot(_) => self.wtr.write_str("."),
            Ast::Class(ref x) => self.fmt_class_post(x),
            Ast::Repetition(ref x) => self.fmt_repetition(x),
            Ast::Group(ref x) => self.fmt_group_post(x),
            Ast::Definition(ref x) => self.fmt_definition(x),
            Ast::Alternation(_) => Ok(()),
            Ast::Concat(_) => Ok(()),
        }
    }

    fn visit_alternation_in(&mut self) -> fmt::Result {
        self.wtr.write_str("|")
    }

    fn visit_class_set_pre(&mut self, ast: &ast::ClassSet) -> Result<(), Self::Err> {
        match *ast {
            ast::ClassSet::Bracketed(ref x) => self.fmt_class_pre(x),
            _ => Ok(()),
        }
    }

    fn visit_class_set_post(&mut self, ast: &ast::ClassSet) -> Result<(), Self::Err> {
        use crate::ast::ClassSet::*;

        match *ast {
            Literal(ref x) => self.fmt_literal(x),
            Range(ref x) => {
                self.fmt_literal(&x.start)?;
                self.wtr.write_str("-")?;
                self.fmt_literal(&x.end)?;
                Ok(())
            }
            Bracketed(ref x) => self.fmt_class_post(x),
            Union(_) => Ok(()),
        }
    }
}

impl<W: fmt::Write> Writer<W> {
    fn fmt_group_pre(&mut self) -> fmt::Result {
        self.wtr.write_str("(")
    }

    fn fmt_group_post(&mut self, _ast: &ast::Group) -> fmt::Result {
        self.wtr.write_str(")")
    }

    fn fmt_repetition(&mut self, ast: &ast::Repetition) -> fmt::Result {
        use crate::ast::RepetitionKind::*;
        match ast.op.kind {
            ZeroOrOne => self.wtr.write_str("?"),
            ZeroOrMore => self.wtr.write_str("*"),
            OneOrMore => self.wtr.write_str("+"),
        }
    }

    fn fmt_definition(&mut self, ast: &ast::Definition) -> fmt::Result {
        self.wtr.write_str("{")?;
        self.wtr.write_str(&ast.name)?;
        self.wtr.write_str("}")
    }

    fn fmt_literal(&mut self, ast: &ast::Literal) -> fmt::Result {
        use crate::ast::LiteralKind::*;

        match ast.kind {
            Verbatim => self.wtr.write_char(ast.c),
            Meta | Superfluous => write!(self.wtr, r"\{}", ast.c),
            Special(ast::SpecialLiteralKind::Tab) => self.wtr.write_str(r"\t"),
            Special(ast::SpecialLiteralKind::LineFeed) => self.wtr.write_str(r"\n"),
            Special(ast::SpecialLiteralKind::CarriageReturn) => self.wtr.write_str(r"\r"),
        }
    }

    fn fmt_class_pre(&mut self, ast: &ast::Class) -> fmt::Result {
        if ast.negated {
            self.wtr.write_str("[^")
        } else {
            self.wtr.write_str("[")
        }
    }

    fn fmt_class_post(&mut self, _ast: &ast::Class) -> fmt::Result {
        self.wtr.write_str("]")
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::String;

    use crate::ast::parse::Parser;

    use super::*;

    fn roundtrip(given: &str) {
        let ast = Parser::new().parse(given).unwrap();

        let mut printer = Printer::new();
        let mut dst = String::new();
        printer.print(&ast, &mut dst).unwrap();
        assert_eq!(given, dst);
    }

    #[test]
    fn print_literal() {
        roundtrip("a");
        roundtrip(r"\[");
        roundtrip(r"\x61");
        roundtrip(r"\x7F");
        roundtrip(r"\u0061");
        roundtrip(r"\U00000061");
        roundtrip(r"\x{61}");
        roundtrip(r"\x{7F}");
        roundtrip(r"\u{61}");
        roundtrip(r"\U{61}");

        roundtrip(r"\a");
        roundtrip(r"\f");
        roundtrip(r"\t");
        roundtrip(r"\n");
        roundtrip(r"\r");
        roundtrip(r"\v");
        roundtrip(r"(?x)\ ");
    }

    #[test]
    fn print_dot() {
        roundtrip(".");
    }

    #[test]
    fn print_concat() {
        roundtrip("ab");
        roundtrip("abcde");
        roundtrip("a(bcd)ef");
    }

    #[test]
    fn print_alternation() {
        roundtrip("a|b");
        roundtrip("a|b|c|d|e");
        roundtrip("|a|b|c|d|e");
        roundtrip("|a|b|c|d|e|");
        roundtrip("a(b|c|d)|e|f");
    }

    #[test]
    fn print_assertion() {
        roundtrip(r"^");
        roundtrip(r"$");
        roundtrip(r"\A");
        roundtrip(r"\z");
        roundtrip(r"\b");
        roundtrip(r"\B");
    }

    #[test]
    fn print_repetition() {
        roundtrip("a?");
        roundtrip("a??");
        roundtrip("a*");
        roundtrip("a*?");
        roundtrip("a+");
        roundtrip("a+?");
        roundtrip("a{5}");
        roundtrip("a{5}?");
        roundtrip("a{5,}");
        roundtrip("a{5,}?");
        roundtrip("a{5,10}");
        roundtrip("a{5,10}?");
    }

    #[test]
    fn print_flags() {
        roundtrip("(?i)");
        roundtrip("(?-i)");
        roundtrip("(?s-i)");
        roundtrip("(?-si)");
        roundtrip("(?siUmux)");
    }

    #[test]
    fn print_group() {
        roundtrip("(?i:a)");
        roundtrip("(?P<foo>a)");
        roundtrip("(?<foo>a)");
        roundtrip("(a)");
    }

    #[test]
    fn print_class() {
        roundtrip(r"[abc]");
        roundtrip(r"[a-z]");
        roundtrip(r"[^a-z]");
        roundtrip(r"[a-z0-9]");
        roundtrip(r"[-a-z0-9]");
        roundtrip(r"[-a-z0-9]");
        roundtrip(r"[a-z0-9---]");
        roundtrip(r"[a-z&&m-n]");
        roundtrip(r"[[a-z&&m-n]]");
        roundtrip(r"[a-z--m-n]");
        roundtrip(r"[a-z~~m-n]");
        roundtrip(r"[a-z[0-9]]");
        roundtrip(r"[a-z[^0-9]]");

        roundtrip(r"\d");
        roundtrip(r"\D");
        roundtrip(r"\s");
        roundtrip(r"\S");
        roundtrip(r"\w");
        roundtrip(r"\W");

        roundtrip(r"[[:alnum:]]");
        roundtrip(r"[[:^alnum:]]");
        roundtrip(r"[[:alpha:]]");
        roundtrip(r"[[:^alpha:]]");
        roundtrip(r"[[:ascii:]]");
        roundtrip(r"[[:^ascii:]]");
        roundtrip(r"[[:blank:]]");
        roundtrip(r"[[:^blank:]]");
        roundtrip(r"[[:cntrl:]]");
        roundtrip(r"[[:^cntrl:]]");
        roundtrip(r"[[:digit:]]");
        roundtrip(r"[[:^digit:]]");
        roundtrip(r"[[:graph:]]");
        roundtrip(r"[[:^graph:]]");
        roundtrip(r"[[:lower:]]");
        roundtrip(r"[[:^lower:]]");
        roundtrip(r"[[:print:]]");
        roundtrip(r"[[:^print:]]");
        roundtrip(r"[[:punct:]]");
        roundtrip(r"[[:^punct:]]");
        roundtrip(r"[[:space:]]");
        roundtrip(r"[[:^space:]]");
        roundtrip(r"[[:upper:]]");
        roundtrip(r"[[:^upper:]]");
        roundtrip(r"[[:word:]]");
        roundtrip(r"[[:^word:]]");
        roundtrip(r"[[:xdigit:]]");
        roundtrip(r"[[:^xdigit:]]");

        roundtrip(r"\pL");
        roundtrip(r"\PL");
        roundtrip(r"\p{L}");
        roundtrip(r"\P{L}");
        roundtrip(r"\p{X=Y}");
        roundtrip(r"\P{X=Y}");
        roundtrip(r"\p{X:Y}");
        roundtrip(r"\P{X:Y}");
        roundtrip(r"\p{X!=Y}");
        roundtrip(r"\P{X!=Y}");
    }
}

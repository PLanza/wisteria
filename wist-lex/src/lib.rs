use regex_syntax::Parser;

pub fn testing() {
    let mut parser = Parser::new();
    let ast = parser.parse("{digit}+(\\.{digit}+)?").unwrap();
    let mut printer = regex_syntax::ast::print::Printer::new();
    let mut s = String::new();
    printer.print(&ast, &mut s).unwrap();
    println!("{s}");
}

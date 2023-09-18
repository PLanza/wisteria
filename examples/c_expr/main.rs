wisteria::attach_wisteria_files!("examples/c_expr/c.wisl", "examples/c_expr/c_expr.wisp");

mod ast;
use ast::*;

fn main() {
    let mut lexer = Lexer::new().unwrap();

    let tokens = lexer
        .lex_file("examples/c_expr/test.c_expr".to_string())
        .unwrap();
    let stream = tokens.iter().peekable();

    let parser = Parser::new();
    let out = parser.parse(stream);

    let ast = out
        .downcast::<Box<Ast>>()
        .unwrap_or_else(|e| panic!("{:?}", e.type_id()));

    println!("{:?}", ast);
}

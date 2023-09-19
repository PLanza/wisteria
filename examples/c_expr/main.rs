wisteria::attach_wisteria_files!("examples/c_expr/c.wisl", "examples/c_expr/c_expr.wisp");

mod ast;
use ast::*;

fn main() {
    let ast = lex_and_parse::<Box<Ast>>("examples/c_expr/test.c_expr".to_string()).unwrap();

    println!("{:?}", ast);
}

wist_lex::attach_lex_file!("example/test.wilex");

fn main() {
    let mut lexer = Lexer::<11>::new().unwrap();
    let tokens = lexer.lex_file("example/code.test".to_string()).unwrap();
    println!("{:?}", tokens);
    println!("Done.");
}

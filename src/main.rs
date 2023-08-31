wist_lex::attach_lex_file!("example/snesc.wisl");
// wist_parse::attach_parse_file!("example/snesc.wisp");

fn main() {
    let mut lexer = Lexer::new().unwrap();
    let tokens = lexer.lex_file("example/code.test".to_string()).unwrap();
    for token in tokens {
        println!("{token}");
    }
    wist_parse::test::test();
}

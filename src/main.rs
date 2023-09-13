wist_macro::attach_wisteria_files!("example/c.wisl", "example/c.wisp");

#[derive(Debug, Clone)]
pub enum Op {
    And,
    Star,
    Assign,
    Mulass,
}

#[derive(Debug, Clone)]
pub enum Ast {
    Unary(Op, Box<Ast>),
    SizeOf(Box<Ast>),
    Int(i32),
    Ident(String),
    Assign(Box<Ast>, Op, Box<Ast>),
}

fn main() {
    let mut lexer = Lexer::new().unwrap();

    let tokens = lexer.lex_file("example/code.test".to_string()).unwrap();
    for token in &tokens {
        println!("{token}");
    }
    let stream = tokens.iter().peekable();

    let parser = Parser::new();
    let out = parser.parse(stream);

    println!("{:?}", std::any::TypeId::of::<Box<Ast>>());
    println!(
        "out: {:?}",
        out.downcast::<Box<Ast>>()
            .unwrap_or_else(|e| panic!("{:?}", e.type_id()))
    );
}

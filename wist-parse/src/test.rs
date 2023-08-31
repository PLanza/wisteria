use crate::*;
fn g(term: GrammarTerm) -> Grammar {
    Grammar {
        term: Box::new(term),
        ty: GrammarType::bot(),
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Val {
    Int(i32),
    Unit,
}

impl TokenVal for Val {}

fn lparen() -> Token {
    Token {
        tag: TokenTag::LPAREN,
        val: Box::new(Val::Unit),
    }
}
fn rparen() -> Token {
    Token {
        tag: TokenTag::RPAREN,
        val: Box::new(Val::Unit),
    }
}
fn int(i: i32) -> Token {
    Token {
        tag: TokenTag::INT,
        val: Box::new(Val::Int(i)),
    }
}

fn g_fix<F>(f: F) -> Grammar
where
    F: Fn(Grammar) -> Grammar,
{
    f(g(GrammarTerm::Var(0)))
}

fn de_paren(o: Output) -> Output {
    match o {
        Output::Double(_, o) => match *o {
            Output::Double(o, _) => *o,
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}

pub fn test() {
    use GrammarTerm::*;
    use TokenTag::*;
    let mut grammar = g(Fix(g_fix(|paren| {
        g(Alt(
            g(Map(|i| i, g(Token(INT)))),
            g(Map(
                de_paren,
                g(Seq(g(Token(LPAREN)), g(Seq(paren, g(Token(RPAREN)))))),
            )),
        ))
    })));

    type_check(&mut grammar);
    println!("{:?}", grammar.ty);

    let parser = parse(grammar, Vec::new());
    let code = vec![
        lparen(),
        lparen(),
        lparen(),
        int(24),
        rparen(),
        rparen(),
        rparen(),
    ];
    let out = parser(&mut code.iter().peekable());
    println!("{:?}", out);

    // Should fail since fewer ')' than '('
    // let fail = parser(&mut vec![lparen(), lparen(), int(1), rparen()].iter().peekable());
}

pub mod test;

pub use parse_macro::attach_parse_file;

use std::cell::RefCell;
use std::collections::HashSet;
use std::iter::Peekable;
use std::rc::Rc;
use std::slice::Iter;

use dyn_clone::DynClone;

#[derive(Eq, PartialEq, Debug, PartialOrd, Clone, Copy, Hash)]
pub enum TokenTag {
    LPAREN,
    RPAREN,
    INT,
}

pub trait TokenVal: DynClone + std::fmt::Debug {}
dyn_clone::clone_trait_object!(TokenVal);

type Value = Box<dyn TokenVal>;

#[derive(Debug)]
pub struct Token {
    tag: TokenTag,
    val: Value,
}

#[derive(Debug, Clone, PartialEq)]
pub struct GrammarType {
    first: HashSet<TokenTag>,
    follow: HashSet<TokenTag>,
    null: bool,
    guarded: bool,
}

#[derive(Clone)]
pub enum GrammarTerm {
    Empty(Value),
    Bot,
    Token(TokenTag),
    Seq(Grammar, Grammar),
    Alt(Grammar, Grammar),
    Star(Grammar),
    Fix(Grammar),
    Map(fn(Output) -> Output, Grammar),
    Var(usize),
}

#[derive(Clone)]
pub struct Grammar {
    term: Box<GrammarTerm>,
    ty: GrammarType,
}

impl GrammarType {
    fn apart(t1: GrammarType, t2: GrammarType) -> bool {
        !t1.null && (t1.follow.is_disjoint(&t2.first))
    }

    fn disjoint(t1: GrammarType, t2: GrammarType) -> bool {
        !(t1.null && t2.null) && (t1.first.is_disjoint(&t2.first))
    }

    fn empty() -> Self {
        GrammarType {
            first: HashSet::new(),
            follow: HashSet::new(),
            null: true,
            guarded: true,
        }
    }
    fn bot() -> Self {
        GrammarType {
            first: HashSet::new(),
            follow: HashSet::new(),
            null: false,
            guarded: true,
        }
    }
    fn token(tag: TokenTag) -> Self {
        GrammarType {
            first: HashSet::from([tag]),
            follow: HashSet::new(),
            null: false,
            guarded: true,
        }
    }
    fn seq(t1: GrammarType, t2: GrammarType) -> Self {
        if !(Self::apart(t1.clone(), t2.clone())) {
            panic!("Grammars must be apart to form sequence")
        }

        let follow_union = if t2.null {
            t2.first.union(&t1.follow).copied().collect()
        } else {
            HashSet::new()
        };

        // Assuming t1 is not null
        GrammarType {
            first: t1.first.clone(),
            follow: t2.follow.union(&follow_union).copied().collect(),
            null: false,
            guarded: t1.guarded,
        }
    }
    fn alt(t1: GrammarType, t2: GrammarType) -> Self {
        if !(Self::disjoint(t1.clone(), t2.clone())) {
            panic!("Grammars must be joint to form alternation")
        }
        // Assuming t1 is not null
        GrammarType {
            first: t1.first.union(&t2.first).copied().collect(),
            follow: t1.follow.union(&t2.follow).copied().collect(),
            null: t1.null || t2.null,
            guarded: t1.guarded && t2.guarded,
        }
    }
    fn star(t: GrammarType) -> Self {
        let mut new_t = Self::seq(t.clone(), t.clone());
        new_t.null = true;
        new_t.follow = t.first.union(&t.follow).copied().collect();
        new_t
    }
    fn fix<F>(f: F) -> Self
    where
        F: Fn(GrammarType) -> GrammarType,
    {
        let mut prev = GrammarType {
            first: HashSet::new(),
            follow: HashSet::new(),
            null: false,
            guarded: false,
        };
        let mut curr = f(prev.clone());
        while prev != curr {
            prev = curr;
            curr = f(prev.clone());
        }
        curr
    }
}

impl Grammar {
    fn type_check(&mut self, mut env: Vec<GrammarType>) {
        use GrammarTerm::*;
        match self.term.as_mut() {
            Empty(_) => self.ty = GrammarType::empty(),
            Bot => self.ty = GrammarType::bot(),
            Token(tok) => self.ty = GrammarType::token(tok.clone()),
            Seq(g1, g2) => {
                g1.type_check(env.clone());
                for i in 0..env.len() {
                    env[i].guarded = true;
                }
                g2.type_check(env);
                self.ty = GrammarType::seq(g1.ty.clone(), g2.ty.clone());
            }
            Alt(g1, g2) => {
                g1.type_check(env.clone());
                g2.type_check(env);
                self.ty = GrammarType::alt(g1.ty.clone(), g2.ty.clone());
            }
            Star(g) => {
                g.type_check(env);
                self.ty = GrammarType::star(g.ty.clone())
            }
            Fix(g) => {
                let ty = GrammarType::fix(|ty| {
                    let (mut g, mut env) = (g.clone(), env.clone());
                    env.push(ty);
                    g.type_check(env);
                    g.ty
                });
                if !ty.guarded {
                    panic!("Expected fix point grammar to be guarded")
                }
                env.push(ty);
                g.type_check(env);
                self.ty = g.ty.clone();
            }
            Var(i) => self.ty = env[*i].clone(),
            Map(_, g) => {
                g.type_check(env);
                self.ty = g.ty.clone();
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum Output {
    Single(Value),
    Double(Box<Output>, Box<Output>),
    List(Vec<Output>),
}
type TokenStream<'a> = Peekable<Iter<'a, Token>>;
type Parser = Rc<Box<dyn Fn(&mut TokenStream) -> Output>>;

fn empty(v: Value) -> Parser {
    Rc::new(Box::new(move |_s| Output::Single(v.clone())))
}

fn bot() -> Parser {
    Rc::new(Box::new(|_s| panic!("Impossible")))
}

fn token(tag: TokenTag) -> Parser {
    Rc::new(Box::new(move |s| {
        let output = match s.peek() {
            None => panic!("Expected token {:?}, reached end of stream", tag),
            Some(s_tok) => {
                if tag == s_tok.tag {
                    Output::Single(s_tok.val.clone())
                } else {
                    panic!("Expected token {:?} got {:?}", tag, s_tok.tag)
                }
            }
        };
        s.next();
        output
    }))
}

fn seq(p1: Parser, p2: Parser) -> Parser {
    Rc::new(Box::new(move |s| {
        let a = p1(s);
        let b = p2(s);
        Output::Double(Box::new(a), Box::new(b))
    }))
}

fn alt(ty1: GrammarType, p1: Parser, ty2: GrammarType, p2: Parser) -> Parser {
    Rc::new(Box::new(move |s| match s.peek() {
        None => {
            if ty1.null {
                p1(s)
            } else if ty2.null {
                p2(s)
            } else {
                panic!("Unexpected end of stream")
            }
        }
        Some(tok) => {
            if ty1.first.contains(&tok.tag) {
                p1(s)
            } else if ty2.first.contains(&tok.tag) {
                p2(s)
            } else if ty1.null {
                p1(s)
            } else if ty2.null {
                p2(s)
            } else {
                panic!("Unexpected end of stream")
            }
        }
    }))
}

fn star(ty: GrammarType, p: Parser) -> Parser {
    Rc::new(Box::new(move |s| {
        let mut acc: Vec<Output> = Vec::new();
        loop {
            match s.peek() {
                None => return Output::List(acc),
                Some(tok) if !ty.first.contains(&tok.tag) => return Output::List(acc),
                _ => acc.push(p(s)),
            }
        }
    }))
}

fn map<F>(f: F, p: Parser) -> Parser
where
    F: Fn(Output) -> Output + 'static,
{
    Rc::new(Box::new(move |s| f(p(s))))
}

fn parse(g: Grammar, env: Vec<Parser>) -> Parser {
    use GrammarTerm::*;
    match *g.term {
        Empty(v) => empty(v),
        Bot => bot(),
        Token(tok) => token(tok),
        Seq(g1, g2) => seq(parse(g1, env.clone()), parse(g2, env)),
        Alt(g1, g2) => alt(
            g1.ty.clone(),
            parse(g1, env.clone()),
            g2.ty.clone(),
            parse(g2, env),
        ),
        Star(g) => star(g.ty.clone(), parse(g, env)),
        // Landin's Knot-esque
        Fix(g) => {
            let r = Rc::new(RefCell::new(bot()));
            let r_clone = r.clone();
            let p: Parser = Rc::new(Box::new(move |s| r.borrow()(s)));

            let mut env = env.clone();
            env.push(p.clone());
            let q = parse(g, env);

            let mut r_ref = r_clone.borrow_mut();
            *r_ref = q;

            p
        }
        Map(f, g) => map(f, parse(g, env)),
        Var(n) => env[n].clone(),
    }
}

fn type_check(g: &mut Grammar) {
    g.type_check(Vec::new())
}

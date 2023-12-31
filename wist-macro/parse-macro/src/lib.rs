mod backus;
mod error;
mod grammar;
mod parse;

use quote::quote;

pub use parse::GrammarParser;

pub fn generate_parser(mut parser: GrammarParser) -> proc_macro2::TokenStream {
    parser.parse_grammar();

    // Order needed so that fix point variables are available when needed
    let start = parser.start.0;
    let mut order = parser.start.1.borrow().order();
    order.insert(0, start.clone());

    println!("Generating Code");
    let (mut names, mut parsers) = (Vec::new(), Vec::new());
    let mut seen = std::collections::HashSet::new();
    for name in order {
        if !seen.insert(name.clone()) {
            continue;
        }
        names.push(name.clone());
        parsers.push(parser.defs.get(&name).unwrap().borrow().to_parser());
    }

    quote! {
        type TokenStream<'a> = ::std::iter::Peekable<::std::slice::Iter<'a, LexToken>>;
        type ParserFn = ::std::rc::Rc<Box<dyn Fn(&mut TokenStream) -> Box<dyn ::std::any::Any>>>;

        fn __bot() -> ParserFn {
            ::std::rc::Rc::new(Box::new(|_s| panic!("Impossible")))
        }

        fn __token(tag: LexTokenTag) -> ParserFn{
            ::std::rc::Rc::new(Box::new(move |s| {
                let output = match s.peek() {
                    None => panic!("Expected token {:?}, reached end of stream", tag),
                    Some(s_tok) => {
                        println!("{}", s_tok);
                        if tag == s_tok.tag {
                            s_tok.val.clone()
                        } else {
                            panic!("Expected token {:?} got {:?}", tag, s_tok.tag)
                        }
                    }
                };
                s.next();
                Box::new(output)
            }))
        }

        fn __seq(p1: ParserFn, p2: ParserFn) -> ParserFn {
            ::std::rc::Rc::new(Box::new(move |s| {
                let a = p1(s);
                let b = p2(s);
                Box::new((a, b))
            }))
        }

        fn __alt(
            ty1: (bool, ::std::collections::HashSet<LexTokenTag>),
            p1: ParserFn,
            ty2: (bool, ::std::collections::HashSet<LexTokenTag>),
            p2: ParserFn,
        ) -> ParserFn {
            ::std::rc::Rc::new(Box::new(move |s| match s.peek() {
                None => {
                    if ty1.0 {
                        p1(s)
                    } else if ty2.0 {
                        p2(s)
                    } else {
                        panic!("Unexpected end of stream: {:?}, {:?}", ty1, ty2)
                    }
                } Some(tok) => {
                    if ty1.1.contains(&tok.tag) {
                        p1(s)
                    } else if ty2.1.contains(&tok.tag) {
                        p2(s)
                    } else if ty1.0 {
                        p1(s)
                    } else if ty2.0 {
                        p2(s)
                    } else {
                        panic!("No progress possible: saw token {:?}", tok)
                    }
                }
            }))
        }

        fn __star(
            ty: (bool, ::std::collections::HashSet<LexTokenTag>),
            p: ParserFn,
        ) -> ParserFn {
            ::std::rc::Rc::new(Box::new(move |s| {
                let mut acc: Vec<Box<dyn ::std::any::Any>> = Vec::new();
                loop {
                    match s.peek() {
                        None => return Box::new(acc),
                        Some(tok) if !ty.1.contains(&tok.tag) => return Box::new(acc),
                        _ => acc.push(p(s)),
                    }
                }
            }))
        }

        fn __map<F>(f: F, p: ParserFn) -> ParserFn
        where F : Fn(Box<dyn ::std::any::Any + 'static>) -> Box<dyn ::std::any::Any> + 'static
        {
            ::std::rc::Rc::new(Box::new(move |s| f(p(s))))
        }

        struct Parser {
            fix_vars: ::std::collections::HashMap<String, ParserFn>,
            parser_defs: ::std::collections::HashMap<String, ::std::rc::Rc<::std::cell::RefCell<ParserFn>>>,
            parser: ParserFn,
        }

        impl Parser {
            pub fn new() -> Parser {
                use ::std::collections::HashMap;
                use ::std::rc::Rc;
                use ::std::cell::RefCell;

                let mut parser_defs: HashMap<String, Rc<RefCell<ParserFn>>> = HashMap::new();
                #(parser_defs.insert(#names.to_string(), Rc::new(RefCell::new(__bot())));)*

                let mut parser = Parser {
                    fix_vars: ::std::collections::HashMap::new(),
                    parser_defs,
                    parser: __bot(),
                };

                parser.populate_parsers();

                parser.parser = parser.parser_defs.get(#start)
                    .unwrap_or_else(|| panic!("Missing starting grammar: {}", #start)).borrow().clone();
                parser
            }

            fn populate_parsers(&mut self) {
                use ::std::any::Any;
                #(*self.parser_defs.get(#names).unwrap_or_else(|| panic!("Grammar {} has not been initialized", #names)).borrow_mut() = #parsers;)*
            }

            fn def(
                &self,
                name: String,
            ) -> ParserFn {
                let cell = self.parser_defs.get(&name)
                    .unwrap_or_else(|| panic!("Missing grammar {}", name)).clone();
                ::std::rc::Rc::new(Box::new(move |s| {
                    cell.borrow()(s)
                }))
            }

            pub fn parse(&self, mut stream: TokenStream) -> Box<dyn ::std::any::Any> {
                let out = (self.parser)(&mut stream);
                if stream.next().is_some() {
                    panic!("Entire file has not been parsed");
                }
                out
            }
        }
    }
}

use proc_macro2::TokenStream;
use quote::quote;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct GrammarType {
    first: HashSet<String>,
    follow: HashSet<String>,
    null: bool,
    guarded: bool,
}

#[derive(Clone, Debug)]
pub enum GrammarTerm {
    Bot,
    Token(String),
    Seq(Grammar, Grammar),
    Alt(Grammar, Grammar),
    Star(Grammar),
    Fix(String, Grammar),
    Var(String),
    Def(String, Rc<RefCell<Grammar>>),
    Map(TokenStream, Grammar),
}

#[derive(Clone, Debug)]
pub struct Grammar {
    pub(crate) term: Box<GrammarTerm>,
    pub(crate) ty: GrammarType,
}

impl GrammarType {
    fn apart(t1: GrammarType, t2: GrammarType) -> bool {
        !t1.null && (t1.follow.is_disjoint(&t2.first))
    }

    fn disjoint(t1: GrammarType, t2: GrammarType) -> bool {
        !(t1.null && t2.null) && (t1.first.is_disjoint(&t2.first))
    }

    fn bot() -> Self {
        GrammarType {
            first: HashSet::new(),
            follow: HashSet::new(),
            null: false,
            guarded: true,
        }
    }
    fn token(tag: String) -> Self {
        GrammarType {
            first: HashSet::from([tag]),
            follow: HashSet::new(),
            null: false,
            guarded: true,
        }
    }
    fn seq(t1: GrammarType, t2: GrammarType) -> Self {
        if !(Self::apart(t1.clone(), t2.clone())) {
            panic!(
                "Grammars must be apart to form sequence:\n  {:?}\n| {:?}",
                t1, t2
            )
        }

        let follow_union = if t2.null {
            t2.first.union(&t1.follow).cloned().collect()
        } else {
            HashSet::new()
        };

        // Assuming t1 is not null
        GrammarType {
            first: t1.first.clone(),
            follow: t2.follow.union(&follow_union).cloned().collect(),
            null: false,
            guarded: t1.guarded,
        }
    }
    fn alt(t1: GrammarType, t2: GrammarType) -> Self {
        if !(Self::disjoint(t1.clone(), t2.clone())) {
            panic!(
                "Grammars must be joint to form alternation:\n  {:?}\n| {:?}",
                t1, t2
            )
        }
        // Assuming t1 is not null
        GrammarType {
            first: t1.first.union(&t2.first).cloned().collect(),
            follow: t1.follow.union(&t2.follow).cloned().collect(),
            null: t1.null || t2.null,
            guarded: t1.guarded && t2.guarded,
        }
    }
    fn star(t: GrammarType) -> Self {
        let mut new_t = Self::seq(t.clone(), t.clone());
        new_t.null = true;
        new_t.follow = t.first.union(&t.follow).cloned().collect();
        new_t
    }
    fn fix<F>(mut f: F) -> Self
    where
        F: FnMut(GrammarType) -> GrammarType,
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

    pub(crate) fn to_token_stream(&self) -> TokenStream {
        let first: Vec<syn::Variant> = self
            .first
            .iter()
            .map(|tok_str| syn::parse_str(tok_str).unwrap())
            .collect();
        let null = self.null;
        quote!((#null, ::std::collections::HashSet::from([#(LexTokenTag::#first),*])))
    }
}

impl Grammar {
    pub fn new(term: GrammarTerm) -> Self {
        Grammar {
            term: Box::new(term),
            ty: GrammarType::bot(),
        }
    }
    pub fn type_check(&mut self, mut env: HashMap<String, GrammarType>) {
        use GrammarTerm::*;
        match self.term.as_mut() {
            Bot => self.ty = GrammarType::bot(),
            Token(tok) => self.ty = GrammarType::token(tok.clone()),
            Seq(g1, g2) => {
                g1.type_check(env.clone());
                for (_, ty) in env.iter_mut() {
                    ty.guarded = true;
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
            Fix(var, g) => {
                let ty = GrammarType::fix(|ty| {
                    let mut env = env.clone();
                    env.insert(var.to_string(), ty);
                    g.type_check(env);
                    g.ty.clone()
                });
                if !ty.guarded {
                    panic!("Expected fix point grammar to be guarded: {}", var)
                }
                env.insert(var.to_string(), ty);
                g.type_check(env);
                self.ty = g.ty.clone();
            }
            Var(s) => {
                self.ty = env
                    .get(s)
                    .unwrap_or_else(|| panic!("Unexpected fix point variable {}", s))
                    .clone()
            }
            Def(_name, cell) => {
                cell.borrow_mut().type_check(env);
                self.ty = cell.borrow().ty.clone();
            }
            Map(_, g) => {
                g.type_check(env);
                self.ty = g.ty.clone()
            }
        }
    }

    pub fn create_fix_points(
        &mut self,
        mut to_replace: HashSet<String>,
        defs: &HashMap<String, Rc<RefCell<Grammar>>>,
    ) -> HashSet<String> {
        // bool means is modified
        use GrammarTerm::*;
        match self.term.as_mut() {
            Def(def, cell) => {
                if to_replace.contains(def) {
                    let mut replaced = HashSet::new();
                    replaced.insert(def.clone());
                    self.term = Box::new(Var(def.clone()));
                    replaced
                } else {
                    to_replace.insert(def.clone());

                    let replaced = cell.borrow_mut().create_fix_points(to_replace, defs);
                    if replaced.contains(def) {
                        let inner = cell.borrow().clone();
                        *cell.borrow_mut() = Grammar::new(Fix(def.clone(), inner));
                    }
                    replaced
                }
            }
            Seq(g1, g2) => g1
                .create_fix_points(to_replace.clone(), defs)
                .union(&g2.create_fix_points(to_replace, defs))
                .cloned()
                .collect(),
            Alt(g1, g2) => g1
                .create_fix_points(to_replace.clone(), defs)
                .union(&g2.create_fix_points(to_replace, defs))
                .cloned()
                .collect(),
            Star(g) => g.create_fix_points(to_replace, defs),
            Fix(_, g) => g.create_fix_points(to_replace, defs),
            Map(_, g) => g.create_fix_points(to_replace, defs),
            _ => HashSet::new(),
        }
    }

    pub fn order(&self) -> Vec<String> {
        use GrammarTerm::*;
        match &*self.term {
            Seq(g1, g2) => vec![g1.order(), g2.order()].concat(),
            Alt(g1, g2) => vec![g1.order(), g2.order()].concat(),
            Star(g) => g.order(),
            Fix(_, g) => g.order(),
            Def(name, cell) => vec![vec![name.clone()], cell.borrow().order()].concat(),
            Map(_, g) => g.order(),
            _ => Vec::new(),
        }
    }

    pub fn to_parser(&self) -> TokenStream {
        use GrammarTerm::*;
        match self.term.as_ref() {
            Bot => quote!(__bot()),
            Token(tok) => {
                let tok_ident: syn::Variant = syn::parse_str(tok).unwrap();
                quote!(__token(LexTokenTag::#tok_ident))
            }
            Seq(g1, g2) => {
                let p1 = g1.to_parser();
                let p2 = g2.to_parser();
                quote!(__seq(#p1, #p2))
            }
            Alt(g1, g2) => {
                let ty1 = g1.ty.to_token_stream();
                let p1 = g1.to_parser();
                let ty2 = g2.ty.to_token_stream();
                let p2 = g2.to_parser();
                quote!(__alt(#ty1, #p1, #ty2, #p2))
            }
            Star(g) => {
                let ty = g.ty.to_token_stream();
                let p = g.to_parser();
                quote!(__star(#ty, #p))
            }
            Fix(var, g) => {
                let q = g.to_parser();
                quote! {{
                    let r = ::std::rc::Rc::new(::std::cell::RefCell::new(__bot()));
                    let r_clone = r.clone();
                    let p: ParserFn = ::std::rc::Rc::new(Box::new(move |s| r.borrow()(s)));

                    self.fix_vars.insert(#var.to_string(), p.clone());
                    let q = #q;
                    *r_clone.borrow_mut() = q;

                    p
                }}
            }
            Map(f, g) => {
                let p = g.to_parser();
                quote!(__map(#f, #p))
            }
            Var(var) => quote! {
                match self.fix_vars.get(#var) {
                    Some(p) => p.clone(),
                    None => panic!("Lost Fix Point Variable {}", #var),
                }
            },
            Def(name, _) => quote! ( self.def(#name.to_string()) ),
        }
    }
}

impl std::fmt::Display for GrammarTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use GrammarTerm::*;
        match self {
            Bot => write!(f, "⊥"),
            Token(stream) => write!(f, "{stream}"),
            Seq(g1, g2) => write!(f, "{g1} {g2}"),
            Alt(g1, g2) => write!(f, "{g1}\n| {g2}"),
            Star(g) => write!(f, "({})*", g),
            Fix(fix, g) => write!(f, "λ {fix}. ({g})"),
            Var(var) => write!(f, "{var}"),
            Map(func, g) => write!(f, "{g} => {{ {func} }}"),
            Def(name, _) => write!(f, "<{name}>"),
        }
    }
}

impl std::fmt::Display for Grammar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.term)
    }
}

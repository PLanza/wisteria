use regex_syntax::ast::Ast;
use regex_syntax::ast::{ClassSet, ClassSetRange, ClassSetUnion, RepetitionKind, RepetitionOp};

use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy)]
pub(crate) enum Symbol {
    Empty,
    Char(char),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Regex {
    Null,
    Set(Set),
    Repetition(Box<Regex>),
    Alternation(Box<Regex>, Box<Regex>),
    Concat(Box<Regex>, Box<Regex>),
}

impl Regex {
    fn new_alternation(left: Regex, right: Regex) -> Regex {
        use Regex::Alternation;
        if left == right {
            return left;
        }

        // If empty set
        if matches!(left.clone(), Regex::Set(self::Set::Set(inner)) if inner.is_empty()) {
            return right;
        }
        if matches!(right.clone(), Regex::Set(self::Set::Set(inner)) if inner.is_empty()) {
            return left;
        }

        if let (Regex::Set(left), Regex::Set(right)) = (left.clone(), right.clone()) {
            return Regex::Set(left.union(&right));
        }

        if let Alternation(left_l, left_r) = left {
            return Alternation(left_l, Box::new(Alternation(left_r, Box::new(right))));
        }

        if left < right {
            return Alternation(Box::new(left), Box::new(right));
        } else {
            return Alternation(Box::new(left), Box::new(right));
        }
    }

    fn new_concat(left: Regex, right: Regex) -> Regex {
        use Regex::{Concat, Null};
        if matches!(left.clone(), Regex::Set(self::Set::Set(inner)) if inner.is_empty())
            || matches!(right.clone(),  Regex::Set(self::Set::Set(inner)) if inner.is_empty())
        {
            return Regex::Set(self::Set::empty());
        }

        if matches!(left, Null) {
            return right;
        }
        if matches!(right, Null) {
            return left;
        }

        if let Concat(left_l, left_r) = left {
            return Concat(left_l, Box::new(Concat(left_r, Box::new(right))));
        }

        Concat(Box::new(left), Box::new(right))
    }

    fn new_repetition(inner: Regex, kind: RepetitionKind) -> Regex {
        use Regex::*;
        use RepetitionKind::*;
        match kind {
            ZeroOrOne => Alternation(Box::new(Null), Box::new(inner)),
            OneOrMore => Concat(
                Box::new(inner.clone()),
                Box::new(Regex::new_repetition(inner, ZeroOrMore)),
            ),
            ZeroOrMore => match inner {
                Null => Regex::Null,
                Set(self::Set::Set(set)) if set.is_empty() => Regex::Null,
                Repetition(_) => inner,
                _ => Repetition(Box::new(inner)),
            },
        }
    }

    // Needs to create a regex in =-canonical form
    pub fn from_ast(ast: Ast, defs: &HashMap<String, Regex>) -> Regex {
        match ast {
            Ast::Empty(_) => Regex::Null,
            Ast::Literal(regex_syntax::ast::Literal { c, .. }) => {
                Regex::Set(Set::Set(HashSet::from([c])))
            }
            Ast::Dot(_) => Regex::Set(Set::dot()),
            Ast::Class(class) => Regex::Set(Set::from_class(class)),
            Ast::Repetition(regex_syntax::ast::Repetition {
                op: RepetitionOp { kind, .. },
                ast,
                ..
            }) => Self::new_repetition(Regex::from_ast(*ast, defs), kind),
            Ast::Group(regex_syntax::ast::Group { ast, .. }) => Regex::from_ast(*ast, defs),
            Ast::Alternation(regex_syntax::ast::Alternation { mut asts, span }) => {
                let left = Regex::from_ast(asts[0].clone(), defs);
                let right;
                if asts.len() > 2 {
                    asts.remove(0);
                    right = Regex::from_ast(
                        regex_syntax::ast::Alternation { asts, span }.into_ast(),
                        defs,
                    )
                } else {
                    right = Regex::from_ast(asts.pop().unwrap(), defs);
                }
                Self::new_alternation(left, right)
            }
            Ast::Concat(regex_syntax::ast::Concat { mut asts, span }) => {
                let left = Regex::from_ast(asts[0].clone(), defs);
                let right;
                if asts.len() > 2 {
                    asts.remove(0);
                    right =
                        Regex::from_ast(regex_syntax::ast::Concat { asts, span }.into_ast(), defs)
                } else {
                    right = Regex::from_ast(asts.pop().unwrap(), defs);
                }
                Self::new_concat(left, right)
            }
            Ast::Definition(regex_syntax::ast::Definition { name, .. }) => defs
                .get(&name)
                // TODO: Convert to an error
                .unwrap_or_else(|| panic!("Cannot find defintion {}", name))
                .clone(),
        }
    }

    /// Returns true if the regex is nullable
    pub fn nullable(&self) -> bool {
        use Regex::*;
        match self {
            Null | Repetition(_) => true,
            Set(_) => false,
            Alternation(left, right) => left.as_ref().nullable() || right.as_ref().nullable(),
            Concat(left, right) => left.as_ref().nullable() && right.as_ref().nullable(),
        }
    }

    // Returned Regex also needs to be in =-canonical form
    pub(crate) fn derivative(&self, symbol: Symbol) -> Regex {
        let symbol_char;
        if let Symbol::Char(char) = symbol {
            symbol_char = char;
        } else {
            return Regex::Set(self::Set::empty());
        }

        use Regex::*;
        match self {
            Null => Set(self::Set::empty()),
            Set(set) => match set {
                self::Set::Set(set) => {
                    if set.contains(&symbol_char) {
                        Null
                    } else {
                        Set(self::Set::empty())
                    }
                }
                self::Set::NegSet(set) => {
                    if set.contains(&symbol_char) {
                        Set(self::Set::empty())
                    } else {
                        Null
                    }
                }
            },
            Repetition(inner) => Self::new_concat(inner.derivative(symbol), self.clone()),
            Alternation(left, right) => {
                Self::new_alternation(left.derivative(symbol), right.derivative(symbol))
            }
            Concat(left, right) => {
                let null_res = if left.nullable() {
                    Null
                } else {
                    Set(self::Set::empty())
                };
                Self::new_alternation(
                    Self::new_concat(left.derivative(symbol), *right.clone()),
                    Self::new_concat(null_res, right.derivative(symbol)),
                )
            }
        }
    }

    pub(crate) fn derivative_classes(&self) -> HashSet<Set> {
        match self {
            Regex::Null => HashSet::from([Set::dot()]),
            Regex::Set(set) => match set {
                Set::Set(inner) => HashSet::from([set.clone(), Set::NegSet(inner.clone())]),
                Set::NegSet(inner) => HashSet::from([set.clone(), Set::Set(inner.clone())]),
            },
            Regex::Repetition(inner) => Self::derivative_classes(inner),
            Regex::Alternation(left, right) => {
                let mut result = HashSet::new();
                for l_set in Self::derivative_classes(left) {
                    for r_set in Self::derivative_classes(right) {
                        result.insert(l_set.intersection(&r_set));
                    }
                }
                result
            }
            Regex::Concat(left, right) => {
                if !left.nullable() {
                    Self::derivative_classes(left)
                } else {
                    let mut result = HashSet::new();
                    for l_set in Self::derivative_classes(left) {
                        for r_set in Self::derivative_classes(right) {
                            result.insert(l_set.intersection(&r_set));
                        }
                    }
                    result
                }
            }
        }
    }
}

impl std::fmt::Display for Regex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Null => write!(f, "ε"),
            Self::Set(set) => match set {
                Set::Set(chars) => {
                    write!(f, "[")?;
                    for c in chars {
                        write!(f, "{}", c)?;
                    }
                    write!(f, "]")
                }
                Set::NegSet(chars) => {
                    write!(f, "\\[")?;
                    for c in chars {
                        write!(f, "{}", c)?;
                    }
                    write!(f, "]")
                }
            },
            Self::Repetition(r) => write!(f, "({})*", *r),
            Self::Alternation(r1, r2) => write!(f, "{}|{}", *r1, *r2),
            Self::Concat(r1, r2) => write!(f, "{}{}", *r1, *r2),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Set {
    Set(HashSet<char>),
    NegSet(HashSet<char>),
}

impl Set {
    pub(crate) fn empty() -> Set {
        Set::Set(HashSet::new())
    }

    pub(crate) fn dot() -> Set {
        Set::NegSet(HashSet::new())
    }

    pub(crate) fn from_class(class: regex_syntax::ast::Class) -> Set {
        let set = match class.kind {
            ClassSet::Literal(regex_syntax::ast::Literal { c, .. }) => Set::Set(HashSet::from([c])),
            ClassSet::Range(ClassSetRange { start, end, .. }) => {
                Set::Set((start.c..=end.c).collect())
            }
            ClassSet::Bracketed(class) => Set::from_class(*class),
            ClassSet::Union(ClassSetUnion { items, .. }) => {
                let mut set = Set::empty();
                for inner in items {
                    set = set.union(&Set::from_class(regex_syntax::ast::Class {
                        span: class.span,
                        negated: false,
                        kind: inner,
                    }))
                }
                set
            }
        };
        if class.negated {
            set.negate()
        } else {
            set
        }
    }

    pub(crate) fn negate(self) -> Set {
        match self {
            Set::Set(set) => Set::NegSet(set),
            Set::NegSet(set) => Set::Set(set),
        }
    }

    pub(crate) fn union(&self, other: &Self) -> Set {
        use self::Set::*;
        match (self, other) {
            (Set(left), Set(right)) => Set(left.union(&right).cloned().collect()),
            (Set(left), NegSet(right)) => NegSet(right.difference(&left).cloned().collect()),
            (NegSet(left), Set(right)) => NegSet(left.difference(&right).cloned().collect()),
            (NegSet(left), NegSet(right)) => NegSet(left.intersection(&right).cloned().collect()),
        }
    }

    pub(crate) fn intersection(&self, other: &Self) -> Set {
        use self::Set::*;
        match (self, other) {
            (Set(left), Set(right)) => Set(left.intersection(&right).cloned().collect()),
            (Set(left), NegSet(right)) => Set(left.difference(&right).cloned().collect()),
            (NegSet(left), Set(right)) => Set(right.difference(&left).cloned().collect()),
            (NegSet(left), NegSet(right)) => NegSet(left.union(&right).cloned().collect()),
        }
    }

    pub(crate) fn get_symbol(&self) -> Symbol {
        match self {
            Set::Set(set) => {
                if set.is_empty() {
                    Symbol::Empty
                } else {
                    Symbol::Char(*set.iter().next().unwrap())
                }
            }
            // Ascii 27 is the escape control character that should always be available
            Set::NegSet(_) => Symbol::Char(27u8 as char),
        }
    }
    pub fn contains(&self, c: char) -> bool {
        match self {
            Set::Set(set) => set.contains(&c),
            Set::NegSet(set) => !set.contains(&c),
        }
    }
}

use std::hash::{Hash, Hasher};
impl Hash for Set {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use self::Set::*;
        match self {
            Set(set) => {
                state.write_u8(0);
                for c in set {
                    c.hash(state);
                }
            }
            NegSet(set) => {
                state.write_u8(1);
                for c in set {
                    c.hash(state);
                }
            }
        }
    }
}

use std::cmp::Ordering;
impl Ord for Set {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use self::Set::*;
        match (self, other) {
            (Set(left), Set(right)) => {
                if matches!(left.len().cmp(&right.len()), Ordering::Equal) {
                    for (cl, cr) in left.iter().zip(right) {
                        if !matches!(cl.cmp(&cr), Ordering::Equal) {
                            return cl.cmp(&cr);
                        }
                    }
                    return Ordering::Equal;
                } else {
                    left.len().cmp(&right.len())
                }
            }
            (Set(_), NegSet(_)) => Ordering::Less,
            (NegSet(_), Set(_)) => Ordering::Greater,
            (NegSet(left), NegSet(right)) => {
                if matches!(left.len().cmp(&right.len()), Ordering::Equal) {
                    for (cl, cr) in left.iter().zip(right) {
                        if !matches!(cl.cmp(&cr), Ordering::Equal) {
                            return cl.cmp(&cr);
                        }
                    }
                    return Ordering::Equal;
                } else {
                    left.len().cmp(&right.len())
                }
            }
        }
    }
}
impl PartialOrd for Set {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

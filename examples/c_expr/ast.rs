#[derive(Debug, Clone)]
pub enum Constant {
    Int(i32),
    Float(f64),
    Char(char),
}

#[derive(Debug, Clone)]
pub enum BoolOp {
    Or,
    And,
}

#[derive(Debug, Clone)]
pub enum BitOp {
    Or,
    Xor,
    And,
    LShift,
    RShift,
}

#[derive(Debug, Clone)]
pub enum RelatOp {
    Eq,
    NEq,
    LT,
    GT,
    LEq,
    GEq,
}

#[derive(Debug, Clone)]
pub enum AssignOp {
    Assign,
    Mul,
    Div,
    Mod,
    Plus,
    Minus,
    LShift,
    RShift,
    And,
    Or,
    Xor,
}

#[derive(Debug, Clone)]
pub enum ArithOp {
    Plus,
    Minus,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, Clone)]
pub enum UnaryOp {
    Incr,
    Decr,
    Ref,
    Deref,
    Pos,
    Neg,
    BitNot,
    BoolNot,
}

#[derive(Debug, Clone)]
pub enum Ast {
    Ident(String),
    Constant(Constant),
    StringLit(String),
    Comma(Box<Ast>, Box<Ast>),
    Assign(Box<Ast>, AssignOp, Box<Ast>),
    Conditional(Box<Ast>, Box<Ast>, Box<Ast>),
    BoolOp(Box<Ast>, BoolOp, Box<Ast>),
    BitOp(Box<Ast>, BitOp, Box<Ast>),
    RelatOp(Box<Ast>, RelatOp, Box<Ast>),
    ArithOp(Box<Ast>, ArithOp, Box<Ast>),
    UnaryOp(UnaryOp, Box<Ast>),
    SizeOfExpr(Box<Ast>),
}

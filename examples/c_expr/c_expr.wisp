$ primary_expr -> Box<Ast> :
  <i: INT_C> { Box::new(Ast::Constant(Constant::Int(i))) }
| <f: FLOAT_C> { Box::new(Ast::Constant(Constant::Float(f))) }
| <c: CHAR_C> { Box::new(Ast::Constant(Constant::Char(c))) }
| <s: STR_LIT> { Box::new(Ast::StringLit(s)) }
| LPAREN <e: expr> RPAREN { e }

expr -> Box<Ast> : 
  <e1: assign_expr> <es: (COMMA assign_expr)*> {
    let es: Vec<Box<Ast>> = es.into_iter().map(|e| 
      e.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap().1
        .downcast_ref::<Box<Ast>>().unwrap()
        .clone()).collect();

    let mut result = e1;
    for e in es {
      result = Box::new(Ast::Comma(result, e));
    }

    result
  }

assign_op -> AssignOp : 
  ASSIGN { AssignOp::Assign }
| MULASS { AssignOp::Mul }
| DIVASS { AssignOp::Div }
| MODASS { AssignOp::Mod }
| PLUSASS { AssignOp::Plus }
| MINASS { AssignOp::Minus }
| LSHASS { AssignOp::LShift }
| RSHASS { AssignOp::RShift }
| ANDASS { AssignOp::And }
| ORASS { AssignOp::Or }
| XORASS { AssignOp::Xor }

assign_expr -> Box<Ast> : 
  <e1: ID> <o: assign_op> <e2: assign_expr> { 
    Box::new(Ast::Assign(Box::new(Ast::Ident(e1)), o, e2)) 
  }
| <e: conditional_expr> { e }

conditional_expr -> Box<Ast> :
  <e1: bool_or_expr> <es: (QUESTION expr COLON bool_or_expr)*> {
    let es: Vec<(Box<Ast>, Box<Ast>)> = es.into_iter().map(|e| {
      let temp = e.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap().1
        .downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap();
      let e1 = temp.0.downcast_ref::<Box<Ast>>().unwrap().clone();
      let e2 = temp.1.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap().1
        .downcast_ref::<Box<Ast>>().unwrap().clone();
        (e1, e2)
    }).collect();

    if es.len() == 0 {
      e1
    } else {
      let mut iter = es.into_iter();
      let (mut prev_e2, mut prev_e3) = iter.next().unwrap(); 
      for (e2, e3) in iter {
        prev_e3 = Box::new(Ast::Conditional(e3, prev_e2, prev_e3));
        prev_e2 = e2;
      }
      
      Box::new(Ast::Conditional(e1, prev_e2, prev_e3))
    }
  }

bool_or_expr -> Box<Ast> : 
  <e1: bool_and_expr> <es: (OROR bool_and_expr)*> {
    let es: Vec<Box<Ast>> = es.into_iter().map(|e| 
      e.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap().1
        .downcast_ref::<Box<Ast>>().unwrap()
        .clone()).collect();

    let mut result = e1;
    for e in es {
      result = Box::new(Ast::BoolOp(result, BoolOp::Or, e));
    }

    result
  }

bool_and_expr -> Box<Ast> : 
  <e1: bit_or_expr> <es: (ANDAND bit_or_expr)*> {
    let es: Vec<Box<Ast>> = es.into_iter().map(|e| 
      e.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap().1
        .downcast_ref::<Box<Ast>>().unwrap()
        .clone()).collect();

    let mut result = e1;
    for e in es {
      result = Box::new(Ast::BoolOp(result, BoolOp::And, e));
    }

    result
  }
  
bit_or_expr -> Box<Ast> : 
  <e1: bit_xor_expr> <es: (OR bit_xor_expr)*> {
    let es: Vec<Box<Ast>> = es.into_iter().map(|e| 
      e.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap().1
        .downcast_ref::<Box<Ast>>().unwrap()
        .clone()).collect();

    let mut result = e1;
    for e in es {
      result = Box::new(Ast::BitOp(result, BitOp::Or, e));
    }

    result
  }

bit_xor_expr -> Box<Ast> : 
  <e1: bit_and_expr> <es: (XOR bit_and_expr)*> {
    let es: Vec<Box<Ast>> = es.into_iter().map(|e| 
      e.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap().1
        .downcast_ref::<Box<Ast>>().unwrap()
        .clone()).collect();

    let mut result = e1;
    for e in es {
      result = Box::new(Ast::BitOp(result, BitOp::Xor, e));
    }

    result
  }

bit_and_expr -> Box<Ast> : 
  <e1: equality_expr> <es: (AND equality_expr)*> {
    let es: Vec<Box<Ast>> = es.into_iter().map(|e| 
      e.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap().1
        .downcast_ref::<Box<Ast>>().unwrap()
        .clone()).collect();

    let mut result = e1;
    for e in es {
      result = Box::new(Ast::BitOp(result, BitOp::And, e));
    }

    result
  }

equality_op -> RelatOp :
  EQ { RelatOp::Eq }
| NEQ { RelatOp::NEq }

equality_expr -> Box<Ast> : 
  <e1: relational_expr> <es: (equality_op relational_expr)*> {
    let es: Vec<(RelatOp, Box<Ast>)> = es.into_iter().map(
      |pair| {
        let temp = pair.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap();
        let op = temp.0.downcast_ref::<RelatOp>().unwrap().clone();
        let e = temp.1
          .downcast_ref::<Box<Ast>>().unwrap()
          .clone();
        (op, e)
      }).collect();

    let mut result = e1;
    for (op, e) in es {
      result = Box::new(Ast::RelatOp(result, op, e));
    }

    result
  }

relational_op -> RelatOp :
  LT { RelatOp::LT }
| GT { RelatOp::GT }
| LEQ { RelatOp::LEq }
| GEQ { RelatOp::GEq }

relational_expr -> Box<Ast> : 
  <e1: shift_expr> <es: (relational_op shift_expr)*> {
    let es: Vec<(RelatOp, Box<Ast>)> = es.into_iter().map(
      |pair| {
        let temp = pair.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap();
        let op = temp.0.downcast_ref::<RelatOp>().unwrap().clone();
        let e = temp.1
          .downcast_ref::<Box<Ast>>().unwrap()
          .clone();
        (op, e)
      }).collect();

    let mut result = e1;
    for (op, e) in es {
      result = Box::new(Ast::RelatOp(result, op, e));
    }

    result
  }

shift_op -> BitOp :
  LSHIFT { BitOp::LShift }
| RSHIFT { BitOp::RShift }

shift_expr -> Box<Ast> : 
  <e1: additive_expr> <es: (shift_op additive_expr)*> {
    let es: Vec<(BitOp, Box<Ast>)> = es.into_iter().map(
      |pair| {
        let temp = pair.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap();
        let op = temp.0.downcast_ref::<BitOp>().unwrap().clone();
        let e = temp.1
          .downcast_ref::<Box<Ast>>().unwrap()
          .clone();
        (op, e)
      }).collect();

    let mut result = e1;
    for (op, e) in es {
      result = Box::new(Ast::BitOp(result, op, e));
    }

    result
  }

additive_op -> ArithOp :
  PLUS { ArithOp::Plus }
| MINUS { ArithOp::Minus }

additive_expr -> Box<Ast> : 
  <e1: multiplicative_expr> <es: (additive_op multiplicative_expr)*> {
    let es: Vec<(ArithOp, Box<Ast>)> = es.into_iter().map(
      |pair| {
        let temp = pair.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap();
        let op = temp.0.downcast_ref::<ArithOp>().unwrap().clone();
        let e = temp.1
          .downcast_ref::<Box<Ast>>().unwrap()
          .clone();
        (op, e)
      }).collect();

    let mut result = e1;
    for (op, e) in es {
      result = Box::new(Ast::ArithOp(result, op, e));
    }

    result
  }

multiplicative_op -> ArithOp :
  STAR { ArithOp::Mul }
| DIV { ArithOp::Div }
| MOD { ArithOp::Mod }

multiplicative_expr -> Box<Ast> : 
  <e1: unary_expr> <es: (multiplicative_op unary_expr)*> {
    let es: Vec<(ArithOp, Box<Ast>)> = es.into_iter().map(
      |pair| {
        let temp = pair.downcast_ref::<(Box<dyn Any>, Box<dyn Any>)>().unwrap();
        let op = temp.0.downcast_ref::<ArithOp>().unwrap().clone();
        let e = temp.1
          .downcast_ref::<Box<Ast>>().unwrap()
          .clone();
        (op, e)
      }).collect();

    let mut result = e1;
    for (op, e) in es {
      result = Box::new(Ast::ArithOp(result, op, e));
    }

    result
  }

unary_op -> UnaryOp : 
  AND { UnaryOp::Ref }
| STAR { UnaryOp::Deref }
| PLUS { UnaryOp::Pos }
| MINUS { UnaryOp::Neg }
| TILDE { UnaryOp::BitNot }
| EXCLAM { UnaryOp::BoolNot }

unary_expr -> Box<Ast> :
  <e: primary_expr> { e }
| INCR <e: unary_expr> { Box::new(Ast::UnaryOp(UnaryOp::Incr, e)) }
| DECR <e: unary_expr> { Box::new(Ast::UnaryOp(UnaryOp::Decr, e)) }
| <op: unary_op> <e: unary_expr> { Box::new(Ast::UnaryOp(op, e)) }
| SIZEOF <e: unary_expr> { Box::new(Ast::SizeOfExpr(e)) }

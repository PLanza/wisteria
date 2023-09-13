unary_op -> Op : 
  AND { Op::And }
| STAR { Op::Star }

unary_expr -> Box<Ast>: 
  SIZEOF <i: INT_C> { Box::new(Ast::SizeOf(Box::new(Ast::Int(i)))) }
| <o: unary_op> <e: unary_expr> { Box::new(Ast::Unary(o, e)) }

assign_op -> Op : 
  ASSIGN { Op::Assign }
| MULASS { Op::Mulass }

$ assign_expr -> Box<Ast> : 
  <e1: unary_expr> <o: assign_op> <e2: assign_expr> { 
    Box::new(Ast::Assign(e1, o, e2)) 
  }
| <i: ID> { Box::new(Ast::Ident(i)) }


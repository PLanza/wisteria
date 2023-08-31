unary_op : AND { Op::And }
         | STAR { Op::Star }

unary_expr : SIZEOF <e: unary_expr> { Ast::SizeOf(Box::new(e)) }
           | <o: unary_op> <e: unary_expr> { Ast::Unary(o, Box::new(e)) }

assign_op : ASSIGN { Op::Assign }
          | MULASS { Op::Mulass }

assign_expr : <e1: unary_expr> <o: assign_op> <e2: assign_expr> { Ast::Assign(e1, o, e2) }

expr : <a: assign_expr> { Ast::Expr(Box::new(a)) }
     | <es: (expr COMMA)*> { Ast::Comma(es) }

primary_expr : <i: ID> { Ast::Id(i) }
             | <i: INT_C> { Ast::Int(i) }
             | <s: STRING_C> { Ast::String(s) }
             | LPAREN <e: expr> RPAREN { e }

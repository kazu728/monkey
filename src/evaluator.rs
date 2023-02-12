use crate::ast::{Expression, ExpressionStatement, Program, Statement};

use super::object::Object;

pub fn eval(program: Program) -> Object {
    let mut obj = Object::Null;

    for stmt in program.statements {
        obj = evaluate_statement(stmt);
    }
    obj
}

fn evaluate_statement(statement: Statement) -> Object {
    match statement {
        Statement::Expression(expression_statement) => evaluate_expression(expression_statement),
        _ => panic!("statement is not ExpressionStatement. got={:?}", statement),
    }
}

fn evaluate_expression(expression_statement: ExpressionStatement) -> Object {
    match expression_statement.expression {
        Expression::NumberLiteral(integer_literal) => Object::Integer(integer_literal.value),
        _ => panic!(
            "expression is not IntegerLiteral. got={:?}",
            expression_statement.expression
        ),
    }
}

#[cfg(test)]
mod tests {
    use crate::{lexer::Lexer, object::Object, parser::Parser};

    use super::eval;

    fn test_eval(input: String) -> Object {
        let program = Parser::new(Lexer::new(input)).parse_program();

        eval(program)
    }

    fn test_integer_object(obj: Object, expected: i64) {
        match obj {
            Object::Integer(val) => assert_eq!(val, expected),
            _ => panic!("object is not Integer. got={:?}", obj),
        }
    }

    #[test]
    fn test_eval_integer_expression() {
        let input = vec![("5", 5), ("10", 10)];

        for case in input {
            let evaluated = test_eval(case.0.to_string());
            test_integer_object(evaluated, case.1);
        }
    }
}

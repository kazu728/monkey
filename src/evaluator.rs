use crate::{
    ast::{Expression, PrefixExpression, Program, Statement},
    object::OBJECT_NULL,
};

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
        Statement::Expression(expression_statement) => {
            evaluate_expression(expression_statement.expression)
        }
        _ => panic!("statement is not ExpressionStatement. got={:?}", statement),
    }
}

fn evaluate_expression(expression: Expression) -> Object {
    match expression {
        Expression::NumberLiteral(integer_literal) => Object::Integer(integer_literal.value),
        Expression::Boolean(boolean) => boolean.value.into(),
        Expression::PrefixExpression(prefix_expression) => {
            evaluate_prefix_expression(prefix_expression)
        }
        _ => panic!("Unexpected expression. got={:?}", expression),
    }
}

fn evaluate_prefix_expression(prefix_expression: PrefixExpression) -> Object {
    let right = evaluate_expression(*prefix_expression.right);

    match prefix_expression.operator.as_str() {
        "!" => match right {
            Object::Bool(val) => Object::Bool(!val),
            Object::Integer(val) => Object::Bool(val == 0),
            _ => OBJECT_NULL,
        },
        "-" => match right {
            Object::Integer(val) => Object::Integer(-val),
            _ => OBJECT_NULL,
        },
        _ => OBJECT_NULL,
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

    #[test]
    fn test_eval_integer_expression() {
        let input = vec![("5", 5), ("10", 10), ("-5", -5), ("-10", -10)];

        for case in input {
            let evaluated = test_eval(case.0.to_string());
            match evaluated {
                Object::Integer(val) => assert_eq!(val, case.1),
                _ => panic!("object is not Integer. got={:?}", evaluated),
            };
        }
    }

    #[test]
    fn test_boolean_exporession() {
        let input = vec![("true", true), ("false", false)];

        for case in input {
            let evaluated = test_eval(case.0.to_string());
            match evaluated {
                Object::Bool(val) => assert_eq!(val, case.1),
                _ => panic!("object is not Boolean. got={:?}", evaluated),
            }
        }
    }

    #[test]
    fn test_bang_operator() {
        struct Test {
            input: String,
            expected: bool,
        }
        impl Test {
            pub fn new(input: &str, expected: bool) -> Self {
                Self {
                    input: input.to_string(),
                    expected,
                }
            }
        }

        let cases = vec![
            Test::new("!true", false),
            Test::new("!false", true),
            Test::new("!5", false),
            Test::new("!!true", true),
            Test::new("!!false", false),
            Test::new("!!5", true),
        ];

        for case in cases {
            let evaluated = test_eval(case.input);
            match evaluated {
                Object::Bool(val) => assert_eq!(val, case.expected),
                _ => panic!("object is not Boolean. got={:?}", evaluated),
            }
        }
    }
}

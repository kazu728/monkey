use super::ast::{
    BlockStatement, Expression, Identifier, IfExpression, InfixExpression, PrefixExpression,
    Program, Statement,
};
use super::environment::Environment;
use super::object::{Object, OBJECT_NULL};

pub fn eval(program: Program, env: &mut Environment) -> Object {
    let mut obj = OBJECT_NULL;

    for stmt in program.statements {
        obj = evaluate_statement(stmt, env);

        if let Object::Return(value) = obj {
            return *value;
        };
        if let Object::Error(_) = obj {
            return obj;
        }
    }
    obj
}

fn evaluate_statement(statement: Statement, env: &mut Environment) -> Object {
    match statement {
        Statement::Expression(expression_statement) => {
            evaluate_expression(expression_statement.expression, env)
        }
        Statement::Let(let_statement) => {
            let value = evaluate_expression(let_statement.value, env);
            if let Object::Error(_) = &value {
                return value;
            }

            env.set(let_statement.name.value, value.clone());
            value
        }
        Statement::Return(return_statement) => Object::Return(Box::new(evaluate_expression(
            return_statement.return_value,
            env,
        ))),
        _ => panic!("statement is not ExpressionStatement. got={:?}", statement),
    }
}

fn evaluate_block_statement(block_statement: BlockStatement, env: &mut Environment) -> Object {
    let mut obj = Object::Null;
    for stmt in block_statement.statements {
        obj = evaluate_statement(stmt, env);

        if let Object::Return(_) = obj {
            return obj;
        }

        if let Object::Error(_) = obj {
            return obj;
        }
    }
    obj
}

fn evaluate_expression(expression: Expression, env: &mut Environment) -> Object {
    match expression {
        Expression::NumberLiteral(integer_literal) => Object::Integer(integer_literal.value),
        Expression::Boolean(boolean) => boolean.value.into(),
        Expression::PrefixExpression(prefix_expression) => {
            evaluate_prefix_expression(prefix_expression, env)
        }
        Expression::InfixExpression(infix_expression) => {
            evaluate_infix_expression(infix_expression, env)
        }
        Expression::IfExpression(if_expression) => evaluate_if_expression(if_expression, env),
        Expression::Identifier(identifier) => {
            if let Some(obj) = env.get(&identifier.value) {
                obj.clone()
            } else {
                Object::Error(format!("identifier not found: {}", identifier.value))
            }
        }
        Expression::FunctionLiteral(function_literal) => {
            let params = function_literal.parameters;
            let body = function_literal.body;

            Object::Function(params, body, env.clone())
        }
        Expression::CallExpression(call_expression) => {
            let function = evaluate_expression(*call_expression.function, env);

            if let Object::Error(_) = function {
                return function;
            }

            let mut args = vec![];

            for arg in call_expression.arguments {
                let evaluated = evaluate_expression(arg, env);
                if let Object::Error(_) = evaluated {
                    return evaluated;
                }
                args.push(evaluated);
            }

            apply_function(function, args)
        }
        _ => panic!("Unexpected expression. got={:?}", expression),
    }
}

fn apply_function(function: Object, args: Vec<Object>) -> Object {
    match function {
        Object::Function(params, body, env) => {
            let mut extended_env = extend_function_env(params, args, env);

            evaluate_block_statement(body, &mut extended_env)
        }
        _ => Object::Error(format!("not a function: {:?}", function)),
    }
}

fn extend_function_env(
    params: Vec<Identifier>,
    args: Vec<Object>,
    env: Environment,
) -> Environment {
    let mut new_env = Environment::new_enclosed_environment(env);

    for (param, arg) in params.iter().zip(args) {
        new_env.set(param.value.clone(), arg);
    }

    new_env
}

fn evaluate_prefix_expression(
    prefix_expression: PrefixExpression,
    env: &mut Environment,
) -> Object {
    let right = evaluate_expression(*prefix_expression.right, env);

    if let Object::Error(_) = right {
        return right;
    }

    match prefix_expression.operator.as_str() {
        "!" => match right {
            Object::Bool(val) => Object::Bool(!val),
            Object::Integer(val) => Object::Bool(val == 0),
            Object::Null => Object::Bool(true),
            _ => Object::Bool(false),
        },
        "-" => match right {
            Object::Integer(val) => Object::Integer(-val),
            _ => Object::Error(format!(
                "unknown operator: {}BOOLEAN",
                prefix_expression.operator
            )),
        },
        _ => Object::Error(format!(
            "unknown operator: {}{}",
            prefix_expression.operator, right
        )),
    }
}

fn evaluate_infix_expression(infix_expression: InfixExpression, env: &mut Environment) -> Object {
    let left = evaluate_expression(*infix_expression.left, env);
    if let Object::Error(_) = left {
        return left;
    }

    let right = evaluate_expression(*infix_expression.right, env);
    if let Object::Error(_) = right {
        return right;
    }

    match (left, right) {
        (Object::Integer(a), Object::Integer(b)) => match infix_expression.operator.as_str() {
            "+" => Object::Integer(a + b),
            "-" => Object::Integer(a - b),
            "*" => Object::Integer(a * b),
            "/" => Object::Integer(a / b),
            "<" => (a < b).into(),
            ">" => (a > b).into(),
            "==" => (a == b).into(),
            "!=" => (a != b).into(),
            _ => Object::Error(format!(
                "unknown operator: INTEGER {} INTEGER",
                infix_expression.operator
            )),
        },
        (Object::Bool(a), Object::Bool(b)) => match infix_expression.operator.as_str() {
            "==" => (a == b).into(),
            "!=" => (a != b).into(),
            _ => Object::Error(format!(
                "unknown operator: BOOLEAN {} BOOLEAN",
                infix_expression.operator
            )),
        },
        (Object::Integer(_), Object::Bool(_)) | (Object::Bool(_), Object::Integer(_)) => {
            Object::Error(format!(
                "type mismatch: INTEGER {} BOOLEAN",
                infix_expression.operator
            ))
        }
        _ => Object::Error("unknown operator: BOOLEAN {} BOOLEAN".to_string()),
    }
}

fn evaluate_if_expression(if_expression: IfExpression, env: &mut Environment) -> Object {
    let condition = evaluate_expression(*if_expression.condition, env);

    if let Object::Error(_) = condition {
        return condition;
    }

    if is_truthy(condition) {
        evaluate_block_statement(if_expression.consequence, env)
    } else if let Some(alternative) = if_expression.alternative {
        evaluate_block_statement(alternative, env)
    } else {
        OBJECT_NULL
    }
}

fn is_truthy(object: Object) -> bool {
    match object {
        Object::Bool(val) => val,
        Object::Integer(val) => val != 0,
        Object::Null => false,
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use crate::{environment::Environment, lexer::Lexer, object::Object, parser::Parser};

    use super::eval;

    fn test_eval(input: String) -> Object {
        let program = Parser::new(Lexer::new(input)).parse_program();

        eval(program, &mut Environment::new())
    }

    #[test]
    fn test_eval_integer_expression() {
        let input = vec![
            ("5", 5),
            ("10", 10),
            ("-5", -5),
            ("-10", -10),
            ("5 + 5 + 5 + 5 - 10", 10),
            ("2 * 2 * 2 * 2 * 2", 32),
            ("-50 + 100 + -50", 0),
            ("5 * 2 + 10", 20),
            ("5 + 2 * 10", 25),
            ("20 + 2 * -10", 0),
            ("50 / 2 * 2 + 10", 60),
            ("2 * (5 + 10)", 30),
            ("3 * 3 * 3 + 10", 37),
            ("3 * (3 * 3) + 10", 37),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
        ];

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
        let input = vec![
            ("true", true),
            ("false", false),
            ("1 < 2", true),
            ("1 > 2", false),
            ("1 < 1", false),
            ("1 > 1", false),
            ("1 == 1", true),
            ("1 != 1", false),
            ("1 == 2", false),
            ("1 != 2", true),
            ("true == true", true),
            ("false == false", true),
            ("true == false", false),
            ("true != false", true),
            ("false != true", true),
            ("(1 < 2) == true", true),
            ("(1 < 2) == false", false),
            ("(1 > 2) == true", false),
            ("(1 > 2) == false", true),
        ];

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

    #[test]
    fn test_if_expressions() {
        struct Input {
            input: String,
            expected: Object,
        }
        impl Input {
            pub fn new(input: &str, expected: Object) -> Self {
                Input {
                    input: input.to_string(),
                    expected,
                }
            }
        }
        let cases = vec![
            Input::new("if (true) { 10 }", Object::Integer(10)),
            Input::new("if (false) { 10 }", Object::Null),
            Input::new("if (1) { 10 }", Object::Integer(10)),
            Input::new("if (1 < 2) { 10 }", Object::Integer(10)),
            Input::new("if (1 > 2) { 10 }", Object::Null),
            Input::new("if (1 > 2) { 10 } else { 20 }", Object::Integer(20)),
            Input::new("if (1 < 2) { 10 } else { 20 }", Object::Integer(10)),
        ];

        for case in cases {
            let evaluated = test_eval(case.input);
            match evaluated {
                Object::Integer(val) => match case.expected {
                    Object::Integer(expected) => assert_eq!(val, expected),
                    _ => panic!("object is not Integer. got={:?}", evaluated),
                },
                Object::Null => match case.expected {
                    Object::Null => assert!(true),
                    _ => panic!("object is not Null. got={:?}", evaluated),
                },
                _ => panic!("object is not Integer. got={:?}", evaluated),
            }
        }
    }

    #[test]
    fn test_return_statements() {
        struct Case {
            input: String,
            expected: i64,
        }
        impl Case {
            fn new(input: &str, expected: i64) -> Self {
                Case {
                    input: input.to_string(),
                    expected,
                }
            }
        }
        let cases = vec![
            Case::new("return 10;", 10),
            Case::new("return 10; 9;", 10),
            Case::new("return 2 * 5; 9;", 10),
            Case::new("9; return 2 * 5; 9;", 10),
            Case::new(
                "
                if (10 > 1) {
                    if (10 > 1) {
                        return 10;
                    }
                    return 1;
                }
                ",
                10,
            ),
        ];

        for case in cases {
            let evaluated = test_eval(case.input);
            match evaluated {
                Object::Integer(val) => assert_eq!(val, case.expected),
                _ => panic!("object is not Integer. got={}", evaluated),
            }
        }
    }

    #[test]
    fn test_error_handling() {
        struct Case {
            input: String,
            expected: String,
        }
        impl Case {
            fn new(input: &str, expected: &str) -> Self {
                Case {
                    input: input.to_string(),
                    expected: expected.to_string(),
                }
            }
        }
        let cases = vec![
            Case::new("5 + true;", "type mismatch: INTEGER + BOOLEAN"),
            Case::new("5 + true; 5;", "type mismatch: INTEGER + BOOLEAN"),
            Case::new("-true", "unknown operator: -BOOLEAN"),
            Case::new("true + false;", "unknown operator: BOOLEAN + BOOLEAN"),
            Case::new("5; true + false; 5", "unknown operator: BOOLEAN + BOOLEAN"),
            Case::new(
                "if (10 > 1) { true + false; }",
                "unknown operator: BOOLEAN + BOOLEAN",
            ),
            Case::new(
                "
                if (10 > 1) {
                    if (10 > 1) {
                        return true + false;
                    }
                    return 1;
                }
                ",
                "unknown operator: BOOLEAN + BOOLEAN",
            ),
            Case::new("foobar", "identifier not found: foobar"),
        ];

        for case in cases {
            let evaluated = test_eval(case.input);
            match evaluated {
                Object::Error(val) => assert_eq!(val, case.expected),
                _ => panic!("object is not Error. got={}", evaluated),
            }
        }
    }
    #[test]
    fn test_let_statements() {
        struct Case {
            input: String,
            expected: i64,
        }
        impl Case {
            fn new(input: &str, expected: i64) -> Self {
                Case {
                    input: input.to_string(),
                    expected,
                }
            }
        }
        let cases = vec![
            Case::new("let a = 5; a;", 5),
            Case::new("let a = 5 * 5; a;", 25),
            Case::new("let a = 5; let b = a; b;", 5),
            Case::new("let a = 5; let b = a; let c = a + b + 5; c;", 15),
        ];

        for case in cases {
            let evaluated = test_eval(case.input);
            match evaluated {
                Object::Integer(val) => assert_eq!(val, case.expected),
                _ => panic!("object is not Integer. got={}", evaluated),
            }
        }
    }

    #[test]
    fn test_function_object() {
        let input = "fn(x) { x + 2; };";
        let evaluated = test_eval(input.to_string());

        match evaluated {
            Object::Function(parameters, body, _) => {
                assert_eq!(parameters.len(), 1);
                assert_eq!(parameters[0].value, "x".to_string());
                assert_eq!(body.statements.len(), 1);
            }
            _ => panic!("object is not Function. got={}", evaluated),
        }
    }

    #[test]
    fn test_function_application() {
        struct Case {
            input: String,
            expected: i64,
        }
        impl Case {
            fn new(input: &str, expected: i64) -> Self {
                Case {
                    input: input.to_string(),
                    expected,
                }
            }
        }
        let cases = vec![
            Case::new("let identity = fn(x) { x; }; identity(5);", 5),
            Case::new("let identity = fn(x) { return x; }; identity(5);", 5),
            Case::new("let double = fn(x) { x * 2; }; double(5);", 10),
            Case::new("let add = fn(x, y) { x + y; }; add(5, 5);", 10),
            Case::new("let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));", 20),
            Case::new("fn(x) { x; }(5)", 5),
        ];

        for case in cases {
            let evaluated = test_eval(case.input);
            match evaluated {
                Object::Integer(val) => assert_eq!(val, case.expected),
                _ => panic!("object is not Integer. got={}", evaluated),
            }
        }
    }
}

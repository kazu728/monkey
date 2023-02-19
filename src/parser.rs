use super::ast::{
    BlockStatement, Boolean, CallExpression, Expression, ExpressionStatement, FunctionLiteral,
    Identifier, IfExpression, InfixExpression, IntegerLiteral, LetStatement, PrefixExpression,
    Program, ReturnStatement, Statement, StringLiteral,
};
use super::lexer::{Lexer, Token};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

#[derive(Debug)]
pub enum ParserError {
    UnexpectedToken { expected: Token, actual: Token },
    UnexpectedEof,
    NotPrefixOperator { actual: Token },
    NotInfixOperator { actual: Token },
}

#[derive(Debug, PartialEq, PartialOrd)]
enum Precedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

impl Precedence {
    fn from_token(token: &Token) -> Precedence {
        match token {
            Token::Eq | Token::NotEq => Precedence::Equals,
            Token::Lt | Token::Gt => Precedence::LessGreater,
            Token::Plus | Token::Minus => Precedence::Sum,
            Token::Slash | Token::Asterisk => Precedence::Product,
            Token::LParen => Precedence::Call,
            _ => Precedence::Lowest,
        }
    }
}

type PrefixParseFnType = fn(&mut Parser) -> Result<Expression, ParserError>;
struct PrefixParseFn {
    apply: PrefixParseFnType,
}
type InfixParseFnType = fn(&mut Parser, Expression) -> Result<Expression, ParserError>;
struct InfixParsefn {
    apply: InfixParseFnType,
}

impl Debug for PrefixParseFn {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "PrefixParseFn")
    }
}

impl Debug for InfixParsefn {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "InfixParsefn")
    }
}

#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
    current_token: Option<Token>,
    peek_token: Option<Token>,
    prefix_parse_fns: HashMap<Token, PrefixParseFn>,
    infix_parse_fns: HashMap<Token, InfixParsefn>,
    errors: Vec<String>,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Parser {
        let mut parser = Parser {
            lexer,
            current_token: None,
            peek_token: None,
            prefix_parse_fns: HashMap::new(),
            infix_parse_fns: HashMap::new(),
            errors: vec![],
        };
        parser.next_token();
        parser.next_token();

        parser.register_prefix(Token::Identifier("_".to_string()), Parser::parse_identifier);
        parser.register_prefix(Token::Integer(0), Parser::parse_integer);
        parser.register_prefix(Token::String("_".to_string()), Parser::parse_string);
        parser.register_prefix(Token::Bang, Parser::parse_prefix_expression);
        parser.register_prefix(Token::Minus, Parser::parse_prefix_expression);
        parser.register_prefix(Token::True, Parser::parse_boolean);
        parser.register_prefix(Token::False, Parser::parse_boolean);
        parser.register_prefix(Token::LParen, Parser::parse_grouped_expression);
        parser.register_prefix(Token::If, Parser::parse_if_expression);
        parser.register_prefix(Token::Fn, Parser::parse_function_literal);
        parser.register_infix(Token::Plus, Parser::parse_infix_expression);
        parser.register_infix(Token::Minus, Parser::parse_infix_expression);
        parser.register_infix(Token::Slash, Parser::parse_infix_expression);
        parser.register_infix(Token::Asterisk, Parser::parse_infix_expression);
        parser.register_infix(Token::Eq, Parser::parse_infix_expression);
        parser.register_infix(Token::NotEq, Parser::parse_infix_expression);
        parser.register_infix(Token::Lt, Parser::parse_infix_expression);
        parser.register_infix(Token::Gt, Parser::parse_infix_expression);
        parser.register_infix(Token::LParen, Parser::parse_call_expression);

        parser
    }

    fn next_token(&mut self) {
        self.current_token = self.peek_token.clone();
        self.peek_token = self.lexer.pop_token();
    }
    fn skip_to_semicoron(&mut self) {
        loop {
            match &self.peek_token {
                None => break,
                Some(token) => match token {
                    Token::Semicolon => {
                        self.next_token();
                        break;
                    }

                    _ => self.next_token(),
                },
            };
        }
    }

    fn register_prefix(&mut self, token: Token, f: PrefixParseFnType) {
        self.prefix_parse_fns
            .insert(token, PrefixParseFn { apply: f });
    }
    fn register_infix(&mut self, token: Token, f: InfixParseFnType) {
        self.infix_parse_fns
            .insert(token, InfixParsefn { apply: f });
    }

    fn expect_token(&mut self, expected: Token) -> Result<(), ParserError> {
        if self.peek_token.as_ref() == Some(&expected) {
            self.next_token();
            Ok(())
        } else {
            Err(ParserError::UnexpectedToken {
                expected,
                actual: self.peek_token.clone().unwrap(),
            })
        }
    }
    pub fn parse_program(&mut self) -> Program {
        let mut program = Program { statements: vec![] };

        while self.current_token.is_some() {
            match self.parse_statement() {
                Ok(statement) => program.statements.push(statement),
                Err(e) => {
                    self.skip_to_semicoron();
                    match e {
                        ParserError::UnexpectedToken { expected, actual } => self
                            .errors
                            .push(format!("Expected {:?}, but got {:?}", expected, actual)),
                        ParserError::UnexpectedEof => {
                            self.errors.push("Unexpected EOF".to_string())
                        }
                        ParserError::NotPrefixOperator { actual } => self
                            .errors
                            .push(format!("Not prefix operator: {:?}", actual)),
                        ParserError::NotInfixOperator { actual } => self
                            .errors
                            .push(format!("Not infix operator: {:?}", actual)),
                    }
                }
            }

            self.next_token()
        }
        if !self.errors.is_empty() {
            panic!("ERRORS: {:#?}", self.errors);
        } else {
            program
        }
    }

    fn parse_statement(&mut self) -> Result<Statement, ParserError> {
        match &self.current_token {
            Some(token) => match token {
                Token::Let => Ok(Statement::Let(self.parse_let_statement()?)),
                Token::Return => Ok(Statement::Return(self.parse_return_statement()?)),
                _ => Ok(Statement::Expression(self.parse_expression_statement()?)),
            },
            None => Err(ParserError::UnexpectedEof),
        }
    }
    fn parse_let_statement(&mut self) -> Result<LetStatement, ParserError> {
        match &self.peek_token {
            Some(Token::Identifier(s)) => {
                let identifier = Identifier::new(Token::Identifier(s.to_string()));

                self.next_token();
                self.expect_token(Token::Assign)?;
                self.next_token();

                let value = self.parse_expression(Precedence::Lowest)?;

                if self.peek_token == Some(Token::Semicolon) {
                    self.next_token();
                };

                Ok(LetStatement {
                    token: Token::Let,
                    name: identifier,
                    value,
                })
            }
            _ => Err(ParserError::UnexpectedToken {
                expected: Token::Identifier("${IDENTIFIER}".to_string()),
                actual: self.peek_token.clone().unwrap(),
            }),
        }
    }

    fn parse_return_statement(&mut self) -> Result<ReturnStatement, ParserError> {
        let token = self.current_token.clone().unwrap();

        self.next_token();

        let return_value = self.parse_expression(Precedence::Lowest).unwrap();

        if self.peek_token == Some(Token::Semicolon) {
            self.next_token();
        }

        Ok(ReturnStatement {
            token,
            return_value,
        })
    }

    fn parse_expression_statement(&mut self) -> Result<ExpressionStatement, ParserError> {
        let token = self
            .current_token
            .clone()
            .ok_or(ParserError::UnexpectedEof)?;

        let expression = self.parse_expression(Precedence::Lowest)?;

        if self.peek_token == Some(Token::Semicolon) {
            self.next_token();
        }

        Ok(ExpressionStatement { token, expression })
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Result<Expression, ParserError> {
        let mut left_expression = (self
            .prefix_parse_fns
            .get(&match &self.current_token {
                Some(Token::Identifier(_)) => Token::Identifier("_".to_string()),
                Some(Token::Integer(_)) => Token::Integer(0),
                Some(Token::String(_)) => Token::String("_".to_string()),
                Some(token) => token.clone(),
                _ => panic!("Unexpected token: {:?}", self.current_token),
            })
            .expect("Expression's parseFn is not registered")
            .apply)(self)?;

        while match &self.peek_token {
            Some(Token::Semicolon) => false,
            Some(token) => precedence < Precedence::from_token(token),
            None => false,
        } {
            self.next_token();

            let maybe_infix_parsefn = self
                .infix_parse_fns
                .get(self.current_token.as_ref().unwrap());

            match maybe_infix_parsefn {
                Some(infix_parsefn) => {
                    left_expression = (infix_parsefn.apply)(self, left_expression)?;
                }
                None => return Ok(left_expression),
            }
        }
        Ok(left_expression)
    }

    pub fn parse_identifier(&mut self) -> Result<Expression, ParserError> {
        match &self.current_token {
            Some(Token::Identifier(s)) => Ok(Expression::Identifier(Identifier::new(
                Token::Identifier(s.to_string()),
            ))),
            Some(unexpected_token) => Err(ParserError::UnexpectedToken {
                expected: Token::Identifier("Identifier".to_string()),
                actual: unexpected_token.clone(),
            }),
            None => Err(ParserError::UnexpectedEof),
        }
    }

    pub fn parse_integer(&mut self) -> Result<Expression, ParserError> {
        match &self.current_token {
            Some(Token::Integer(n)) => Ok(Expression::IntegerLiteral(IntegerLiteral::new(
                Token::Integer(*n),
                *n,
            ))),
            Some(unexpected_token) => Err(ParserError::UnexpectedToken {
                expected: Token::Integer(0),
                actual: unexpected_token.clone(),
            }),
            None => Err(ParserError::UnexpectedEof),
        }
    }

    pub fn parse_string(&mut self) -> Result<Expression, ParserError> {
        match &self.current_token {
            Some(Token::String(s)) => Ok(Expression::StringLiteral(StringLiteral::new(
                Token::String(s.to_string()),
                s.to_string(),
            ))),
            Some(unexpected_token) => Err(ParserError::UnexpectedToken {
                expected: Token::String("String".to_string()),
                actual: unexpected_token.clone(),
            }),
            None => Err(ParserError::UnexpectedEof),
        }
    }

    pub fn parse_boolean(&mut self) -> Result<Expression, ParserError> {
        match &self.current_token {
            Some(Token::True) => Ok(Expression::Boolean(Boolean::new(Token::True))),
            Some(Token::False) => Ok(Expression::Boolean(Boolean::new(Token::False))),
            Some(unexpected_token) => Err(ParserError::UnexpectedToken {
                expected: Token::True,
                actual: unexpected_token.clone(),
            }),
            None => Err(ParserError::UnexpectedEof),
        }
    }

    pub fn parse_prefix_expression(&mut self) -> Result<Expression, ParserError> {
        match &self.current_token.clone() {
            Some(token) => {
                let operator = match token {
                    Token::Bang => "!",
                    Token::Minus => "-",
                    _ => Err(ParserError::NotPrefixOperator {
                        actual: token.clone(),
                    })?,
                }
                .to_string();

                self.next_token();

                Ok(Expression::PrefixExpression(PrefixExpression::new(
                    token.clone(),
                    operator,
                    self.parse_expression(Precedence::Prefix)?,
                )))
            }
            None => Err(ParserError::UnexpectedEof),
        }
    }

    pub fn parse_grouped_expression(&mut self) -> Result<Expression, ParserError> {
        self.next_token();

        let expression = self.parse_expression(Precedence::Lowest)?;

        if self.current_token == Some(Token::RParen) {
            return Err(ParserError::UnexpectedToken {
                expected: Token::RParen,
                actual: self.current_token.clone().unwrap(),
            });
        }

        self.next_token();

        Ok(expression)
    }
    pub fn parse_if_expression(&mut self) -> Result<Expression, ParserError> {
        self.expect_token(Token::LParen)?;
        self.next_token();

        let confidtion = self.parse_expression(Precedence::Lowest)?;

        self.expect_token(Token::RParen)?;
        self.expect_token(Token::LBrace)?;

        let consequence = self.parse_block_statement()?;

        let alternative = match self.peek_token.as_ref() {
            Some(Token::Else) => {
                self.next_token();
                self.next_token();

                Some(self.parse_block_statement()?)
            }
            _ => None,
        };

        Ok(Expression::IfExpression(IfExpression::new(
            Token::If,
            confidtion,
            consequence,
            alternative,
        )))
    }

    pub fn parse_function_literal(&mut self) -> Result<Expression, ParserError> {
        self.expect_token(Token::LParen)?;

        let parameters = self.parse_function_parameters()?;

        self.expect_token(Token::LBrace)?;
        let body = self.parse_block_statement()?;

        Ok(Expression::FunctionLiteral(FunctionLiteral::new(
            Token::Fn,
            parameters,
            body,
        )))
    }

    fn parse_function_parameters(&mut self) -> Result<Vec<Identifier>, ParserError> {
        let mut idetifiers: Vec<Identifier> = Vec::new();

        if self.peek_token == Some(Token::RParen) {
            self.next_token();
            return Ok(idetifiers);
        }

        self.next_token();

        let identifier = match &self.current_token {
            Some(Token::Identifier(s)) => Identifier::new(Token::Identifier(s.to_string())),
            Some(unexpected_token) => Err(ParserError::UnexpectedToken {
                expected: Token::Identifier("Identifier".to_string()),
                actual: unexpected_token.clone(),
            })?,
            None => Err(ParserError::UnexpectedEof)?,
        };

        idetifiers.push(identifier);

        while self.peek_token == Some(Token::Comma) {
            self.next_token();
            self.next_token();

            let identifier = match &self.current_token {
                Some(Token::Identifier(s)) => Identifier::new(Token::Identifier(s.to_string())),
                Some(unexpected_token) => Err(ParserError::UnexpectedToken {
                    expected: Token::Identifier("Identifier".to_string()),
                    actual: unexpected_token.clone(),
                })?,
                None => Err(ParserError::UnexpectedEof)?,
            };

            idetifiers.push(identifier);
        }
        self.expect_token(Token::RParen)?;

        Ok(idetifiers)
    }

    fn parse_block_statement(&mut self) -> Result<BlockStatement, ParserError> {
        let mut block = Vec::new();

        self.next_token();

        while self.current_token != Some(Token::RBrace) {
            let statement = self.parse_statement()?;
            block.push(statement);
            self.next_token();
        }

        Ok(BlockStatement::new(Token::LBrace, block))
    }

    pub fn parse_infix_expression(&mut self, left: Expression) -> Result<Expression, ParserError> {
        match self.current_token.clone() {
            Some(token) => {
                let operator = match &token {
                    Token::Plus => "+",
                    Token::Minus => "-",
                    Token::Slash => "/",
                    Token::Asterisk => "*",
                    Token::Eq => "==",
                    Token::NotEq => "!=",
                    Token::Lt => "<",
                    Token::Gt => ">",
                    _ => Err(ParserError::NotInfixOperator {
                        actual: token.clone(),
                    })?,
                }
                .to_string();
                self.next_token();

                Ok(Expression::InfixExpression(InfixExpression::new(
                    token.clone(),
                    left,
                    operator,
                    self.parse_expression(Precedence::from_token(&token))?,
                )))
            }
            None => Err(ParserError::UnexpectedEof),
        }
    }

    pub fn parse_call_expression(
        &mut self,
        function: Expression,
    ) -> Result<Expression, ParserError> {
        Ok(Expression::CallExpression(CallExpression::new(
            self.current_token.clone().unwrap(),
            function,
            self.parse_call_arguments()?,
        )))
    }

    fn parse_call_arguments(&mut self) -> Result<Vec<Expression>, ParserError> {
        let mut args: Vec<Expression> = Vec::new();

        if self.peek_token == Some(Token::RParen) {
            self.next_token();
            return Ok(args);
        }
        self.next_token();

        args.push(self.parse_expression(Precedence::Lowest)?);

        while self.peek_token == Some(Token::Comma) {
            self.next_token();
            self.next_token();

            args.push(self.parse_expression(Precedence::Lowest)?);
        }

        self.expect_token(Token::RParen)?;
        Ok(args)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{Expression, Program, Statement},
        lexer::*,
        object::{Object, OBJECT_FALSE, OBJECT_TRUE},
    };

    use super::Parser;

    fn expect_statement_len(program: &Program, expected: usize) {
        if program.statements.len() != expected {
            panic!(
                "program does not contain {} statements. got: {}, statements: {:?}",
                expected,
                program.statements.len(),
                program.statements
            )
        }
    }

    fn assert_integer_literal(expression: &Expression, expected: i64) {
        match expression {
            Expression::IntegerLiteral(integer) => assert_eq!(integer.value, expected),
            _ => panic!("Expected IntegerLiteral, but got {:?}", expression),
        }
    }

    fn assert_identifier(expression: &Expression, expected: &str) {
        match expression {
            Expression::Identifier(identifier) => {
                assert_eq!(identifier.get_token_value(), expected)
            }
            _ => panic!("Expected Identifier, but got {:?}", expression),
        }
    }

    #[test]
    fn test_let_statements() {
        let input = "
          let x = 5;
          let y = 10;
          let foobar = 838383;
        ";
        let program = Parser::new(Lexer::new(input.to_string())).parse_program();

        expect_statement_len(&program, 3);

        let expected_identifiers: Vec<String> = vec!["x", "y", "foobar"]
            .iter()
            .map(|s| s.to_string())
            .collect();

        for (i, statement) in program.statements.into_iter().enumerate() {
            let identifier = expected_identifiers.get(i).unwrap();

            match statement {
                Statement::Let(statement) => {
                    assert_eq!(statement.token, Token::Let);
                    assert_eq!(statement.name.get_token_value(), *identifier);
                }
                _ => panic!("statement is not a let statement"),
            }
        }
    }

    #[test]
    fn test_return_statements() {
        let input = "
          return 5;
          return 10;
          return 993322;
        ";
        let program = Parser::new(Lexer::new(input.to_string())).parse_program();

        expect_statement_len(&program, 3);

        for statement in program.statements {
            match statement {
                Statement::Return(statement) => assert_eq!(statement.token, Token::Return),
                _ => panic!("statement is not a return statement"),
            }
        }
    }

    #[test]
    fn test_identifier_expression() {
        let input = "foobar;".to_string();
        let program = Parser::new(Lexer::new(input)).parse_program();

        expect_statement_len(&program, 1);

        match program.statements.get(0) {
            Some(Statement::Expression(statement)) => match &statement.expression {
                Expression::Identifier(identifier) => {
                    assert_eq!(identifier.token, Token::Identifier("foobar".to_string()));
                }
                _ => panic!("Expected Identifier, but got {:?}", statement.expression),
            },
            _ => panic!(
                "Expected ExpressionStatement, but got {:?}",
                program.statements.get(0)
            ),
        }
    }

    #[test]
    fn test_bool() {
        let input = "true;";
        let program = Parser::new(Lexer::new(input.to_string())).parse_program();

        expect_statement_len(&program, 1);

        match program.statements.get(0) {
            Some(Statement::Expression(statement)) => match &statement.expression {
                Expression::Boolean(boolean) => assert_eq!(boolean.token, Token::True),
                _ => panic!("Expected Boolean, but got {:?}", statement.expression),
            },
            _ => panic!(
                "Expected ExpressionStatement, but got {:?}",
                program.statements.get(0)
            ),
        }
    }

    #[test]
    fn test_integer() {
        let input = "5;";
        let program = Parser::new(Lexer::new(input.to_string())).parse_program();

        expect_statement_len(&program, 1);

        match program.statements.get(0) {
            Some(Statement::Expression(statement)) => {
                assert_integer_literal(&statement.expression, 5)
            }
            _ => panic!(
                "Expected ExpressionStatement, but got {:?}",
                program.statements.get(0)
            ),
        }
    }

    #[test]
    fn test_string() {
        let input = "\"hello world\";";
        let program = Parser::new(Lexer::new(input.to_string())).parse_program();

        expect_statement_len(&program, 1);

        match program.statements.get(0) {
            Some(Statement::Expression(statement)) => match &statement.expression {
                Expression::StringLiteral(string) => assert_eq!(string.value, "hello world"),
                _ => panic!("Expected StringLiteral, but got {:?}", statement.expression),
            },
            _ => panic!(
                "Expected ExpressionStatement, but got {:?}",
                program.statements.get(0)
            ),
        }
    }

    #[test]
    fn test_parsing_prefix_expressions() {
        struct Case {
            input: String,
            operator: String,
            value: Object,
        }

        impl Case {
            pub fn new(input: &str, operator: &str, value: Object) -> Self {
                Self {
                    input: input.to_string(),
                    operator: operator.to_string(),
                    value,
                }
            }
        }
        let cases: Vec<Case> = vec![
            Case::new("!5;", "!", Object::Integer(5)),
            Case::new("-15;", "-", Object::Integer(15)),
            Case::new("!true;", "!", Object::Bool(true)),
            Case::new("!false;", "!", Object::Bool(false)),
        ];

        for case in cases {
            let program = Parser::new(Lexer::new(case.input)).parse_program();

            expect_statement_len(&program, 1);

            match program.statements.get(0) {
                Some(Statement::Expression(statement)) => match &statement.expression {
                    Expression::PrefixExpression(expression) => {
                        assert_eq!(expression.operator, case.operator);
                        match &*expression.right {
                            Expression::IntegerLiteral(integer) => {
                                assert_eq!(Object::Integer(integer.value), case.value)
                            }
                            Expression::Boolean(boolean) => {
                                let boolean: Object = boolean.clone().into();
                                assert_eq!(boolean, case.value);
                            }
                            _ => panic!(
                                "Expected IntegerLiteral or Boolean, but got {:?}",
                                expression.right
                            ),
                        }
                    }
                    _ => panic!(
                        "Expected PrefixExpression, but got {:?}",
                        statement.expression
                    ),
                },
                _ => panic!(
                    "Expected ExpressionStatement, but got {:?}",
                    program.statements.get(0)
                ),
            }
        }
    }

    #[test]
    fn test_parsing_infix_expression() {
        #[derive(Debug)]
        struct Case {
            input: String,
            left: Object,
            operator: String,
            right: Object,
        }
        impl Case {
            fn new(input: &str, left: Object, operator: &str, right: Object) -> Case {
                Case {
                    input: input.to_string(),
                    left,
                    operator: operator.to_string(),
                    right,
                }
            }
        }

        let cases: Vec<Case> = vec![
            Case::new("5 + 5;", Object::Integer(5), "+", Object::Integer(5)),
            Case::new("5 - 5;", Object::Integer(5), "-", Object::Integer(5)),
            Case::new("5 * 5;", Object::Integer(5), "*", Object::Integer(5)),
            Case::new("5 / 5;", Object::Integer(5), "/", Object::Integer(5)),
            Case::new("5 > 5;", Object::Integer(5), ">", Object::Integer(5)),
            Case::new("5 < 5;", Object::Integer(5), "<", Object::Integer(5)),
            Case::new("5 == 5;", Object::Integer(5), "==", Object::Integer(5)),
            Case::new("5 != 5;", Object::Integer(5), "!=", Object::Integer(5)),
            Case::new("true == true;", OBJECT_TRUE, "==", OBJECT_TRUE),
            Case::new("true != false;", OBJECT_TRUE, "!=", OBJECT_FALSE),
            Case::new(
                "false == false;",
                Object::Bool(false),
                "==",
                Object::Bool(false),
            ),
        ];

        for case in cases {
            let program = Parser::new(Lexer::new(case.input)).parse_program();

            expect_statement_len(&program, 1);

            match program.statements.get(0) {
                Some(Statement::Expression(statement)) => match &statement.expression {
                    Expression::InfixExpression(expression) => {
                        assert_eq!(expression.operator, case.operator);
                        match &*expression.left {
                            Expression::IntegerLiteral(n) => {
                                assert_eq!(Object::Integer(n.value), case.left)
                            }
                            Expression::Boolean(boolean) => {
                                let boolean: Object = boolean.clone().into();
                                assert_eq!(boolean, case.left);
                            }
                            _ => panic!(
                                "Expected IntegerLiteral or Boolean, but got {:?}",
                                expression.left
                            ),
                        }
                        match &*expression.right {
                            Expression::IntegerLiteral(integer) => {
                                assert_eq!(Object::Integer(integer.value), case.right);
                            }
                            Expression::Boolean(boolean) => {
                                let boolean: Object = boolean.clone().into();
                                assert_eq!(boolean, case.right);
                            }
                            _ => panic!(
                                "Expected IntegerLiteral or Boolean, but got {:?}",
                                expression.right
                            ),
                        }
                    }
                    _ => panic!(
                        "Expected InfixExpression, but got {:?}",
                        statement.expression
                    ),
                },
                _ => panic!(
                    "Expected ExpressionStatement, but got {:?}",
                    program.statements.get(0)
                ),
            }
        }
    }

    #[test]
    fn test_if_expression() {
        let input = "if (x < y) { x } else { y }";

        let program = Parser::new(Lexer::new(input.to_string())).parse_program();

        expect_statement_len(&program, 1);

        match program.statements.get(0) {
            Some(Statement::Expression(statement)) => match &statement.expression {
                Expression::IfExpression(if_expression) => {
                    match &*if_expression.condition {
                        Expression::InfixExpression(infix_expression) => {
                            assert_eq!(infix_expression.operator, "<");

                            assert_identifier(&infix_expression.left, "x");
                            assert_identifier(&infix_expression.right, "y");
                        }
                        _ => panic!(
                            "Expected InfixExpression, but got {:?}",
                            if_expression.condition
                        ),
                    };
                    match if_expression.consequence.statements.get(0) {
                        Some(Statement::Expression(expression)) => {
                            assert_identifier(&expression.expression, "x")
                        }
                        _ => panic!(
                            "Expected ExpressionStatement, but got {:?}",
                            if_expression.consequence.statements.get(0)
                        ),
                    };
                    let maybe_statement = if_expression
                        .alternative
                        .as_ref()
                        .unwrap()
                        .statements
                        .get(0);

                    match maybe_statement {
                        Some(Statement::Expression(expression)) => {
                            assert_identifier(&expression.expression, "y")
                        }
                        _ => panic!(
                            "Expected ExpressionStatement, but got {:?}",
                            maybe_statement
                        ),
                    }
                }
                _ => panic!("Expected IfExpression, but got {:?}", statement.expression),
            },
            _ => panic!(
                "Expected ExpressionStatement, but got {:?}",
                program.statements.get(0)
            ),
        }
    }

    #[test]
    fn test_function_literal_parsing() {
        #[derive(PartialEq, Eq)]
        struct Case {
            pub input: String,
            pub expected_parameters: Vec<String>,
        }

        let cases = vec![
            Case {
                input: "fn() {}".to_string(),
                expected_parameters: vec![],
            },
            Case {
                input: "fn(x) {}".to_string(),
                expected_parameters: vec!["x".to_string()],
            },
            Case {
                input: "fn(x, y, z) {}".to_string(),
                expected_parameters: vec!["x".to_string(), "y".to_string(), "z".to_string()],
            },
        ];

        for case in cases {
            let program = Parser::new(Lexer::new(case.input)).parse_program();

            expect_statement_len(&program, 1);

            match program.statements.get(0) {
                Some(Statement::Expression(statement)) => match &statement.expression {
                    Expression::FunctionLiteral(function_literal) => {
                        assert_eq!(
                            function_literal.parameters.len(),
                            case.expected_parameters.len()
                        );
                        for (i, parameter) in function_literal.parameters.iter().enumerate() {
                            assert_eq!(
                                parameter.get_token_value(),
                                *case.expected_parameters.get(i).unwrap()
                            );
                        }
                        assert_eq!(function_literal.body.statements.len(), 0);
                    }
                    _ => panic!(
                        "Expected FunctionLiteral, but got {:?}",
                        statement.expression
                    ),
                },
                _ => panic!(
                    "Expected ExpressionStatement, but got {:?}",
                    program.statements.get(0)
                ),
            }
        }
    }

    #[test]
    fn test_call_expression_parsing() {
        let input = "add(1, 2 * 3, 4 + 5);";
        let program = Parser::new(Lexer::new(input.to_string())).parse_program();

        expect_statement_len(&program, 1);

        match program.statements.get(0).unwrap() {
            Statement::Expression(statement) => match &statement.expression {
                Expression::CallExpression(call_expression) => {
                    assert_identifier(&call_expression.function, "add");
                    assert_eq!(call_expression.arguments.len(), 3);
                    assert_integer_literal(call_expression.arguments.get(0).unwrap(), 1);

                    match call_expression.arguments.get(1).unwrap() {
                        Expression::InfixExpression(infix_expression) => {
                            assert_eq!(infix_expression.operator, "*");
                            assert_integer_literal(&*infix_expression.left, 2);
                            assert_integer_literal(&*infix_expression.right, 3);
                        }
                        _ => panic!(
                            "Expected InfixExpression, but got {:?}",
                            call_expression.arguments.get(1)
                        ),
                    }
                    match call_expression.arguments.get(2).unwrap() {
                        Expression::InfixExpression(infix_expression) => {
                            assert_eq!(infix_expression.operator, "+");

                            assert_integer_literal(&*infix_expression.left, 4);
                            assert_integer_literal(&*infix_expression.right, 5);
                        }
                        _ => panic!(
                            "Expected InfixExpression, but got {:?}",
                            call_expression.arguments.get(2)
                        ),
                    }
                }
                _ => panic!(
                    "Expected CallExpression, but got {:?}",
                    statement.expression
                ),
            },
            _ => panic!(
                "Expected ExpressionStatement, but got {:?}",
                program.statements.get(0)
            ),
        }
    }
}

use super::ast::{
    BlockStatement, Boolean, CallExpression, Expression, ExpressionStatement, FunctionLiteral,
    Identifier, IfExpression, InfixExpression, LetStatement, NumberLiteral, PrefixExpression,
    Program, ReturnStatement, Statement,
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

struct PrefixParseFn {
    apply: fn(&mut Parser) -> Result<Expression, ParserError>,
}
struct InfixParsefn {
    apply: fn(&mut Parser, Expression) -> Result<Expression, ParserError>,
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

        parser.register_prefix(
            Token::Identifier("Identifier".to_string()),
            Parser::parse_identifier,
        );

        parser.register_prefix(Token::Number(0), Parser::parse_number);
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

    fn register_prefix(
        &mut self,
        token: Token,
        f: fn(&mut Parser) -> Result<Expression, ParserError>,
    ) {
        self.prefix_parse_fns
            .insert(token, PrefixParseFn { apply: f });
    }
    fn register_infix(
        &mut self,
        token: Token,
        f: fn(&mut Parser, left: Expression) -> Result<Expression, ParserError>,
    ) {
        self.infix_parse_fns
            .insert(token, InfixParsefn { apply: f });
    }

    fn expect_token(&mut self, expected: Token) -> Result<(), ParserError> {
        if self.peek_token.as_ref().unwrap() == &expected {
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
            None => unreachable!("While statemment is passed, but current token is None."),
        }
    }
    fn parse_let_statement(&mut self) -> Result<LetStatement, ParserError> {
        let maybe_identifier_token =
            self.peek_token
                .as_ref()
                .ok_or(ParserError::UnexpectedToken {
                    expected: Token::Identifier("${IDENTIFIER}".to_string()),
                    actual: Token::Eof,
                })?;

        match maybe_identifier_token {
            Token::Identifier(s) => {
                let identifier = Identifier::new(maybe_identifier_token.clone(), s.to_string());

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
                actual: maybe_identifier_token.clone(),
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
            .get(&match self.current_token {
                Some(Token::Identifier(_)) => Token::Identifier("Identifier".to_string()),
                Some(Token::Number(_)) => Token::Number(0),
                Some(Token::True) => Token::True,
                Some(Token::False) => Token::False,
                Some(Token::Bang) => Token::Bang,
                Some(Token::Minus) => Token::Minus,
                Some(Token::If) => Token::If,
                Some(Token::Fn) => Token::Fn,
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
                s.to_string(),
            ))),
            Some(unexpected_token) => Err(ParserError::UnexpectedToken {
                expected: Token::Identifier("Identifier".to_string()),
                actual: unexpected_token.clone(),
            }),
            None => Err(ParserError::UnexpectedEof),
        }
    }

    pub fn parse_number(&mut self) -> Result<Expression, ParserError> {
        match &self.current_token {
            Some(Token::Number(n)) => Ok(Expression::NumberLiteral(NumberLiteral::new(
                Token::Number(*n),
                *n,
            ))),
            Some(unexpected_token) => Err(ParserError::UnexpectedToken {
                expected: Token::Number(0),
                actual: unexpected_token.clone(),
            }),
            None => Err(ParserError::UnexpectedEof),
        }
    }

    pub fn parse_boolean(&mut self) -> Result<Expression, ParserError> {
        match &self.current_token {
            Some(Token::True) => Ok(Expression::Boolean(Boolean::new(Token::True, true))),
            Some(Token::False) => Ok(Expression::Boolean(Boolean::new(Token::False, false))),
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
            Some(_) => Err(ParserError::UnexpectedToken {
                expected: Token::Else,
                actual: self.peek_token.clone().unwrap(),
            })?,
            None => None,
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
            Some(Token::Identifier(s)) => {
                Identifier::new(Token::Identifier(s.to_string()), s.to_string())
            }
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
                Some(Token::Identifier(s)) => {
                    Identifier::new(Token::Identifier(s.to_string()), s.to_string())
                }
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
    };

    use super::Parser;

    #[derive(Debug, PartialEq)]
    enum Value {
        Number(i64),
        Boolean(bool),
    }
    use Value::*;

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

    #[test]
    fn test_let_statements() {
        let input = "
          let x = 5;
          let y = 10;
          let foobar = 838383;
        ";
        let program = Parser::new(Lexer::new(input.to_string())).parse_program();

        expect_statement_len(&program, 3);

        let expected_identifiers = vec!["x", "y", "foobar"];

        for (i, statement) in program.statements.into_iter().enumerate() {
            let identifier = expected_identifiers.get(i).unwrap();

            match statement {
                Statement::Let(statement) => {
                    assert_eq!(statement.token, Token::Let);
                    assert_eq!(statement.name.value, identifier.to_string());
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
                    assert_eq!(identifier.value, "foobar".to_string());
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
                Expression::Boolean(boolean) => {
                    assert_eq!(boolean.token, Token::True);
                    assert!(boolean.value);
                }
                _ => panic!("Expected Boolean, but got {:?}", statement.expression),
            },
            _ => panic!(
                "Expected ExpressionStatement, but got {:?}",
                program.statements.get(0)
            ),
        }
    }

    #[test]
    fn test_number() {
        let input = "5;";
        let program = Parser::new(Lexer::new(input.to_string())).parse_program();

        expect_statement_len(&program, 1);

        match program.statements.get(0) {
            Some(Statement::Expression(statement)) => match &statement.expression {
                Expression::NumberLiteral(number) => {
                    assert_eq!(number.token, Token::Number(5));
                    assert_eq!(number.value, 5);
                }
                _ => panic!("Expected Number, but got {:?}", statement.expression),
            },
            _ => panic!(
                "Expected ExpressionStatement, but got {:?}",
                program.statements.get(0)
            ),
        }
    }
    #[test]
    fn test_parsing_prefix_expressions() {
        struct PrefixInputExpression {
            input: String,
            operator: String,
            value: Value,
        }

        impl PrefixInputExpression {
            pub fn new(input: &str, operator: &str, value: Value) -> Self {
                Self {
                    input: input.to_string(),
                    operator: operator.to_string(),
                    value,
                }
            }
        }
        let prefix_expressions: Vec<PrefixInputExpression> = vec![
            PrefixInputExpression::new("!5;", "!", Number(5)),
            PrefixInputExpression::new("-15;", "-", Number(15)),
            PrefixInputExpression::new("!true;", "!", Boolean(true)),
            PrefixInputExpression::new("!false;", "!", Boolean(false)),
        ];

        for prefix_expression in prefix_expressions {
            let program = Parser::new(Lexer::new(prefix_expression.input)).parse_program();

            expect_statement_len(&program, 1);

            match program.statements.get(0) {
                Some(Statement::Expression(statement)) => match &statement.expression {
                    Expression::PrefixExpression(expression) => {
                        assert_eq!(expression.operator, prefix_expression.operator);
                        match &*expression.right {
                            Expression::NumberLiteral(number) => {
                                assert_eq!(Number(number.value), prefix_expression.value)
                            }
                            Expression::Boolean(boolean) => {
                                assert_eq!(Boolean(boolean.value), prefix_expression.value);
                            }
                            _ => panic!(
                                "Expected NumberLiteral or Boolean, but got {:?}",
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
        struct InfixInputExpression {
            input: String,
            left: Value,
            operator: String,
            right: Value,
        }
        impl InfixInputExpression {
            fn new(input: &str, left: Value, operator: &str, right: Value) -> InfixInputExpression {
                InfixInputExpression {
                    input: input.to_string(),
                    left,
                    operator: operator.to_string(),
                    right,
                }
            }
        }

        let infix_expressions: Vec<InfixInputExpression> = vec![
            InfixInputExpression::new("5 + 5;", Number(5), "+", Number(5)),
            InfixInputExpression::new("5 - 5;", Number(5), "-", Number(5)),
            InfixInputExpression::new("5 * 5;", Number(5), "*", Number(5)),
            InfixInputExpression::new("5 / 5;", Number(5), "/", Number(5)),
            InfixInputExpression::new("5 > 5;", Number(5), ">", Number(5)),
            InfixInputExpression::new("5 < 5;", Number(5), "<", Number(5)),
            InfixInputExpression::new("5 == 5;", Number(5), "==", Number(5)),
            InfixInputExpression::new("5 != 5;", Number(5), "!=", Number(5)),
            InfixInputExpression::new("true == true;", Boolean(true), "==", Boolean(true)),
            InfixInputExpression::new("true != false;", Boolean(true), "!=", Boolean(false)),
            InfixInputExpression::new("false == false;", Boolean(false), "==", Boolean(false)),
        ];

        for infix_expression in infix_expressions {
            let program = Parser::new(Lexer::new(infix_expression.input)).parse_program();

            expect_statement_len(&program, 1);

            match program.statements.get(0) {
                Some(Statement::Expression(statement)) => match &statement.expression {
                    Expression::InfixExpression(expression) => {
                        assert_eq!(expression.operator, infix_expression.operator);
                        match &*expression.left {
                            Expression::NumberLiteral(number) => {
                                assert_eq!(Number(number.value), infix_expression.left);
                            }
                            Expression::Boolean(boolean) => {
                                assert_eq!(Boolean(boolean.value), infix_expression.left);
                            }
                            _ => panic!(
                                "Expected NumberLiteral or Boolean, but got {:?}",
                                expression.left
                            ),
                        }
                        match &*expression.right {
                            Expression::NumberLiteral(number) => {
                                assert_eq!(Number(number.value), infix_expression.right);
                            }
                            Expression::Boolean(boolean) => {
                                assert_eq!(Boolean(boolean.value), infix_expression.right);
                            }
                            _ => panic!(
                                "Expected NumberLiteral or Boolean, but got {:?}",
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

                            match &*infix_expression.left {
                                Expression::Identifier(identifier) => {
                                    assert_eq!(identifier.value, "x")
                                }
                                _ => panic!(
                                    "Expected Identifier, but got {:?}",
                                    infix_expression.left
                                ),
                            }
                            match &*infix_expression.right {
                                Expression::Identifier(identifier) => {
                                    assert_eq!(identifier.value, "y");
                                }
                                _ => panic!(
                                    "Expected Identifier, but got {:?}",
                                    infix_expression.right
                                ),
                            }
                        }
                        _ => panic!(
                            "Expected InfixExpression, but got {:?}",
                            if_expression.condition
                        ),
                    };
                    match if_expression.consequence.statements.get(0) {
                        Some(Statement::Expression(expression)) => match &expression.expression {
                            Expression::Identifier(identifier) => assert_eq!(identifier.value, "x"),
                            _ => panic!(
                                "Expected Identifier, but got {:?}",
                                if_expression.consequence.statements.get(0)
                            ),
                        },
                        _ => panic!(
                            "Expected ExpressionStatement, but got {:?}",
                            if_expression.consequence.statements.get(0)
                        ),
                    };
                    match if_expression
                        .alternative
                        .as_ref()
                        .unwrap()
                        .statements
                        .get(0)
                    {
                        Some(Statement::Expression(expression)) => match &expression.expression {
                            Expression::Identifier(identifier) => {
                                assert_eq!(identifier.value, "y");
                            }
                            _ => panic!(
                                "Expected Identifier, but got {:?}",
                                if_expression
                                    .alternative
                                    .as_ref()
                                    .unwrap()
                                    .statements
                                    .get(0)
                            ),
                        },
                        _ => panic!(
                            "Expected ExpressionStatement, but got {:?}",
                            if_expression
                                .alternative
                                .as_ref()
                                .unwrap()
                                .statements
                                .get(0)
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
        struct FunctionLiteralInputExpression {
            pub input: String,
            pub expected_parameters: Vec<String>,
        }

        let inputs = vec![
            FunctionLiteralInputExpression {
                input: "fn() {}".to_string(),
                expected_parameters: vec![],
            },
            FunctionLiteralInputExpression {
                input: "fn(x) {}".to_string(),
                expected_parameters: vec!["x".to_string()],
            },
            FunctionLiteralInputExpression {
                input: "fn(x, y, z) {}".to_string(),
                expected_parameters: vec!["x".to_string(), "y".to_string(), "z".to_string()],
            },
        ];

        for input in inputs {
            let program = Parser::new(Lexer::new(input.input)).parse_program();

            expect_statement_len(&program, 1);

            match program.statements.get(0) {
                Some(Statement::Expression(statement)) => match &statement.expression {
                    Expression::FunctionLiteral(function_literal) => {
                        assert_eq!(
                            function_literal.parameters.len(),
                            input.expected_parameters.len()
                        );
                        for (i, parameter) in function_literal.parameters.iter().enumerate() {
                            assert_eq!(parameter.value, *input.expected_parameters.get(i).unwrap());
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
                    match &*call_expression.function {
                        Expression::Identifier(identifier) => {
                            assert_eq!(identifier.value, "add");
                        }
                        _ => panic!(
                            "Expected Identifier, but got {:?}",
                            call_expression.function
                        ),
                    }
                    assert_eq!(call_expression.arguments.len(), 3);
                    match call_expression.arguments.get(0).unwrap() {
                        Expression::NumberLiteral(number) => {
                            assert_eq!(number.value, 1);
                        }
                        _ => panic!(
                            "Expected NumberLiteral, but got {:?}",
                            call_expression.arguments.get(0)
                        ),
                    }
                    match call_expression.arguments.get(1).unwrap() {
                        Expression::InfixExpression(infix_expression) => {
                            assert_eq!(infix_expression.operator, "*");
                            match &*infix_expression.left {
                                Expression::NumberLiteral(number) => {
                                    assert_eq!(number.value, 2);
                                }
                                _ => panic!(
                                    "Expected NumberLiteral, but got {:?}",
                                    infix_expression.left
                                ),
                            }
                            match &*infix_expression.right {
                                Expression::NumberLiteral(number) => {
                                    assert_eq!(number.value, 3);
                                }
                                _ => panic!(
                                    "Expected NumberLiteral, but got {:?}",
                                    infix_expression.right
                                ),
                            }
                        }
                        _ => panic!(
                            "Expected InfixExpression, but got {:?}",
                            call_expression.arguments.get(1)
                        ),
                    }
                    match call_expression.arguments.get(2).unwrap() {
                        Expression::InfixExpression(infix_expression) => {
                            assert_eq!(infix_expression.operator, "+");
                            match &*infix_expression.left {
                                Expression::NumberLiteral(number) => {
                                    assert_eq!(number.value, 4);
                                }
                                _ => panic!(
                                    "Expected NumberLiteral, but got {:?}",
                                    infix_expression.left
                                ),
                            }
                            match &*infix_expression.right {
                                Expression::NumberLiteral(number) => {
                                    assert_eq!(number.value, 5);
                                }
                                _ => panic!(
                                    "Expected NumberLiteral, but got {:?}",
                                    infix_expression.right
                                ),
                            }
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

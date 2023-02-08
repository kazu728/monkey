use super::ast::{
    Expression, ExpressionStatement, Identifier, InfixExpression, LetStatement, NumberLiteral,
    PrefixExpression, Program, ReturnStatement, Statement,
};

use super::lexer::{Lexer, Token};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

#[derive(Debug)]
pub enum ParserError {
    UnexpectedToken { expected: Token, actual: Token },
    UnexpectedEOF,
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
            _ => Precedence::Lowest,
        }
    }
}

struct PrefixParseFn(fn(&mut Parser) -> Expression);
struct InfixParsefn(fn(&mut Parser, Expression) -> Expression);

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
        parser.register_infix(Token::Plus, Parser::parse_infix_expression);
        parser.register_infix(Token::Minus, Parser::parse_infix_expression);
        parser.register_infix(Token::Slash, Parser::parse_infix_expression);
        parser.register_infix(Token::Asterisk, Parser::parse_infix_expression);
        parser.register_infix(Token::Eq, Parser::parse_infix_expression);
        parser.register_infix(Token::NotEq, Parser::parse_infix_expression);
        parser.register_infix(Token::Lt, Parser::parse_infix_expression);
        parser.register_infix(Token::Gt, Parser::parse_infix_expression);

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
                Some(asdf) => match asdf {
                    Token::Semicolon => {
                        self.next_token();
                        break;
                    }

                    _ => self.next_token(),
                },
            };
        }
    }

    fn register_prefix(&mut self, token: Token, f: fn(&mut Parser) -> Expression) {
        self.prefix_parse_fns.insert(token, PrefixParseFn(f));
    }
    fn register_infix(&mut self, token: Token, f: fn(&mut Parser, left: Expression) -> Expression) {
        self.infix_parse_fns.insert(token, InfixParsefn(f));
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
                        ParserError::UnexpectedEOF => {
                            self.errors.push("Unexpected EOF".to_string())
                        }
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

                let maybe_assign_token =
                    self.peek_token
                        .as_ref()
                        .ok_or(ParserError::UnexpectedToken {
                            expected: Token::Assign,
                            actual: Token::Eof,
                        })?;

                match maybe_assign_token {
                    Token::Assign => {
                        self.next_token();
                        self.skip_to_semicoron();

                        Ok(LetStatement {
                            token: Token::Let,
                            name: identifier,
                            value: Expression::Todo,
                        })
                    }
                    _ => Err(ParserError::UnexpectedToken {
                        expected: Token::Assign,
                        actual: maybe_assign_token.clone(),
                    }),
                }
            }
            _ => Err(ParserError::UnexpectedToken {
                expected: Token::Identifier("${IDENTIFIER}".to_string()),
                actual: maybe_identifier_token.clone(),
            }),
        }
    }

    fn parse_return_statement(&mut self) -> Result<ReturnStatement, ParserError> {
        let token = self.current_token.clone().unwrap();

        self.skip_to_semicoron();

        Ok(ReturnStatement {
            token,
            return_value: Expression::Todo,
        })
    }

    fn parse_expression_statement(&mut self) -> Result<ExpressionStatement, ParserError> {
        let token = self
            .current_token
            .clone()
            .ok_or(ParserError::UnexpectedEOF)?;

        let expression = self.parse_expression(Precedence::Lowest);

        self.skip_to_semicoron();

        Ok(ExpressionStatement { token, expression })
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Expression {
        let mut left_expression = match self.current_token {
            Some(Token::Identifier(_)) => self
                .prefix_parse_fns
                .get(&Token::Identifier("Identifier".to_string()))
                .expect("Identifier's parseFn is not registered")
                .0(self),
            Some(Token::Number(_)) => self
                .prefix_parse_fns
                .get(&Token::Number(0))
                .expect("Number's parseFn is not registered")
                .0(self),
            Some(Token::Bang) => self
                .prefix_parse_fns
                .get(&Token::Bang)
                .expect("Bang's parseFn is not registered")
                .0(self),
            Some(Token::Minus) => self
                .prefix_parse_fns
                .get(&Token::Minus)
                .expect("Minus's parseFn is not registered")
                .0(self),
            _ => panic!("Unexpected token: {:?}", self.current_token),
        };

        while self.peek_token != Some(Token::Semicolon)
            && precedence < Precedence::from_token(self.peek_token.as_ref().unwrap())
        {
            self.next_token();

            let infix = self
                .infix_parse_fns
                .get(self.current_token.as_ref().unwrap());

            match infix {
                Some(infix_parsefn) => {
                    left_expression = infix_parsefn.0(self, left_expression);
                }
                None => {
                    return left_expression;
                }
            }
        }
        left_expression
    }

    pub fn parse_identifier(&mut self) -> Expression {
        match &self.current_token {
            Some(Token::Identifier(s)) => Expression::Identifier(Identifier::new(
                Token::Identifier(s.to_string()),
                s.to_string(),
            )),
            _ => unreachable!(),
        }
    }

    pub fn parse_number(&mut self) -> Expression {
        match &self.current_token {
            Some(Token::Number(n)) => {
                Expression::NumberLiteral(NumberLiteral::new(Token::Number(*n), *n))
            }
            _ => unreachable!(),
        }
    }

    pub fn parse_prefix_expression(&mut self) -> Expression {
        match &self.current_token.clone() {
            Some(token) => {
                let operator = match token {
                    Token::Bang => "!".to_string(),
                    Token::Minus => "-".to_string(),
                    _ => unreachable!(),
                };
                self.next_token();

                Expression::PrefixExpression(PrefixExpression::new(
                    token.clone(),
                    operator,
                    self.parse_expression(Precedence::Prefix),
                ))
            }
            None => unreachable!(),
        }
    }

    pub fn parse_infix_expression(&mut self, left: Expression) -> Expression {
        match self.current_token.clone() {
            Some(token) => {
                let operator = match &token {
                    Token::Plus => "+".to_string(),
                    Token::Minus => "-".to_string(),
                    Token::Slash => "/".to_string(),
                    Token::Asterisk => "*".to_string(),
                    Token::Eq => "==".to_string(),
                    Token::NotEq => "!=".to_string(),
                    Token::Lt => "<".to_string(),
                    Token::Gt => ">".to_string(),
                    _ => panic!("Unexpected token: {:?}", self.current_token),
                };
                self.next_token();

                Expression::InfixExpression(InfixExpression::new(
                    token.clone(),
                    left,
                    operator,
                    self.parse_expression(Precedence::from_token(&token)),
                ))
            }
            _ => panic!("Unexpected token: {:?}", self.current_token),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{Expression, Statement},
        lexer::*,
    };

    use super::Parser;

    #[test]
    fn test_let_statements() {
        let input = "
          let x = 5;
          let y = 10;
          let foobar = 838383;
        ";
        let lexer = Lexer::new(input.to_string());
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();

        if program.statements.len() != 3 {
            panic!(
                "program does not contain 3 statements. got: {}, statements: {:?}",
                program.statements.len(),
                program.statements
            )
        }
        let expected_identifiers = vec!["x", "y", "foobar"];

        for (i, statement) in program.statements.into_iter().enumerate() {
            let identifier = expected_identifiers.get(i).unwrap();

            match statement {
                Statement::Let(statement) => {
                    assert_eq!(statement.token, Token::Let);
                    assert_eq!(statement.name.value, identifier.to_string());
                }
                _ => unreachable!(),
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
        let lexer = Lexer::new(input.to_string());
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();

        if program.statements.len() != 3 {
            panic!(
                "program does not contain 3 statements. got: {}, statements: {:?}",
                program.statements.len(),
                program.statements
            )
        }

        for statement in program.statements {
            match statement {
                Statement::Return(statement) => {
                    assert_eq!(statement.token, Token::Return);
                }
                _ => unreachable!(),
            }
        }
    }

    #[test]
    fn test_identifier_expression() {
        let input = "foobar;";

        let lexer = Lexer::new(input.to_string());
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if program.statements.len() != 1 {
            panic!(
                "program does not contain 1 statements. got: {}, statements: {:?}",
                program.statements.len(),
                program.statements
            )
        }
        match program.statements.get(0) {
            Some(Statement::Expression(statement)) => match &statement.expression {
                Expression::Identifier(identifier) => {
                    assert_eq!(identifier.token, Token::Identifier("foobar".to_string()));
                    assert_eq!(identifier.value, "foobar".to_string());
                }
                _ => unreachable!(),
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

        let lexer = Lexer::new(input.to_string());
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if program.statements.len() != 1 {
            panic!(
                "program does not contain 1 statements. got: {}, statements: {:?}",
                program.statements.len(),
                program.statements
            )
        }
        match program.statements.get(0) {
            Some(Statement::Expression(statement)) => match &statement.expression {
                Expression::NumberLiteral(number) => {
                    assert_eq!(number.token, Token::Number(5));
                    assert_eq!(number.value, 5);
                }
                _ => unreachable!(),
            },
            _ => panic!(
                "Expected ExpressionStatement, but got {:?}",
                program.statements.get(0)
            ),
        }
    }
    #[test]
    fn test_parsing_prefix_expressions() {
        struct InputExpression {
            input: String,
            operator: String,
            value: u64,
        }
        let prefix_expressions: Vec<InputExpression> = vec![
            InputExpression {
                input: "!5;".to_string(),
                operator: "!".to_string(),
                value: 5,
            },
            InputExpression {
                input: "-15;".to_string(),
                operator: "-".to_string(),
                value: 15,
            },
        ];

        for prefix_expression in prefix_expressions {
            let lexer = Lexer::new(prefix_expression.input);
            let mut parser = Parser::new(lexer);
            let program = parser.parse_program();

            if program.statements.len() != 1 {
                panic!(
                    "program does not contain 1 statements. got: {}, statements: {:?}",
                    program.statements.len(),
                    program.statements
                )
            }
            match program.statements.get(0) {
                Some(Statement::Expression(statement)) => match &statement.expression {
                    Expression::PrefixExpression(expression) => {
                        assert_eq!(expression.operator, prefix_expression.operator);
                        match &*expression.right {
                            Expression::NumberLiteral(number) => {
                                assert_eq!(number.value, prefix_expression.value);
                            }
                            _ => unreachable!(),
                        }
                    }
                    _ => unreachable!(),
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
        struct InputExpression {
            input: String,
            left_value: u64,
            operator: String,
            right_value: u64,
        }
        let infix_expressions: Vec<InputExpression> = vec![
            InputExpression {
                input: "5 + 5;".to_string(),
                left_value: 5,
                operator: "+".to_string(),
                right_value: 5,
            },
            InputExpression {
                input: "5 - 5;".to_string(),
                left_value: 5,
                operator: "-".to_string(),
                right_value: 5,
            },
            InputExpression {
                input: "5 * 5;".to_string(),
                left_value: 5,
                operator: "*".to_string(),
                right_value: 5,
            },
            InputExpression {
                input: "5 / 5;".to_string(),
                left_value: 5,
                operator: "/".to_string(),
                right_value: 5,
            },
            InputExpression {
                input: "5 > 5;".to_string(),
                left_value: 5,
                operator: ">".to_string(),
                right_value: 5,
            },
            InputExpression {
                input: "5 < 5;".to_string(),
                left_value: 5,
                operator: "<".to_string(),
                right_value: 5,
            },
            InputExpression {
                input: "5 == 5;".to_string(),
                left_value: 5,
                operator: "==".to_string(),
                right_value: 5,
            },
            InputExpression {
                input: "5 != 5;".to_string(),
                left_value: 5,
                operator: "!=".to_string(),
                right_value: 5,
            },
        ];

        for infix_expression in infix_expressions {
            let lexer = Lexer::new(infix_expression.input);
            let mut parser = Parser::new(lexer);
            let program = parser.parse_program();

            if program.statements.len() != 1 {
                panic!(
                    "program does not contain 1 statements. got: {}, statements: {:?}",
                    program.statements.len(),
                    program.statements
                )
            }
            match program.statements.get(0) {
                Some(Statement::Expression(statement)) => match &statement.expression {
                    Expression::InfixExpression(expression) => {
                        assert_eq!(expression.operator, infix_expression.operator);
                        match &*expression.left {
                            Expression::NumberLiteral(number) => {
                                assert_eq!(number.value, infix_expression.left_value);
                            }
                            _ => unreachable!(),
                        }
                        match &*expression.right {
                            Expression::NumberLiteral(number) => {
                                assert_eq!(number.value, infix_expression.right_value);
                            }
                            _ => unreachable!(),
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
}

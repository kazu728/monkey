use super::ast::{
    Expression, ExpressionStatement, Identifier, LetStatement, Program, ReturnStatement, Statement,
};

use super::lexer::{Lexer, Token};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

#[derive(Debug)]
pub enum ParserError {
    UnexpectedToken { expected: Token, actual: Token },
    UnexpectedEOF,
}

enum Precedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

struct ParseFn(fn(&mut Parser) -> Expression);

impl Debug for ParseFn {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "FunctionWrapper")
    }
}

#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
    current_token: Option<Token>,
    peek_token: Option<Token>,
    prefix_parse_fns: HashMap<Token, ParseFn>,
    infix_parse_fns: HashMap<Token, fn(Expression) -> Expression>,
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
        self.prefix_parse_fns.insert(token, ParseFn(f));
    }
    fn register_infix(&mut self, token: Token, f: fn(Expression) -> Expression) {
        self.infix_parse_fns.insert(token, f);
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

    fn parse_expression(&mut self, _precedence: Precedence) -> Expression {
        match self.current_token {
            Some(Token::Identifier(_)) => self
                .prefix_parse_fns
                .get(&Token::Identifier("Identifier".to_string()))
                .expect("Identifier's parseFn is not registered")
                .0(self),
            _ => Expression::Todo,
        }
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
}

#[cfg(test)]
mod tests {
    use crate::{ast::Statement, lexer::*};

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
            Some(Statement::Expression(statement)) => {
                assert_eq!(statement.token, Token::Identifier("foobar".to_string()));
            }
            _ => panic!(
                "Expected ExpressionStatement, but got {:?}",
                program.statements.get(0)
            ),
        }
    }
}

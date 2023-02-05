use crate::ast::{Expression, Identifier, LetStatement, ReturnStatement, Statement};

use super::ast::Program;
use super::lexer::{Lexer, Token};

#[derive(Debug)]
pub enum ParserError {
    UnexpectedToken { expected: Token, actual: Token },
}

#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
    current_token: Option<Token>,
    peek_token: Option<Token>,
    errors: Vec<String>,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Parser {
        let mut parser = Parser {
            lexer,
            current_token: None,
            peek_token: None,
            errors: vec![],
        };
        parser.next_token();
        parser.next_token();

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
                Token::Let => Ok(Statement::LetStatement(self.parse_let_statement()?)),
                Token::Return => Ok(Statement::ReturnStatement(self.parse_return_statement()?)),

                _ => todo!("Implement later. Current token is {:?}", token),
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
                            value: Expression {},
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
            return_value: Expression {},
        })
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
                Statement::LetStatement(statement) => {
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
                Statement::ReturnStatement(statement) => {
                    assert_eq!(statement.token, Token::Return);
                }
                _ => unreachable!(),
            }
        }
    }
}

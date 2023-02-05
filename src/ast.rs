use crate::lexer::Token;

pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Expression {}

#[derive(Debug)]
pub enum Statement {
    LetStatement(LetStatement),
}

#[derive(Debug)]
pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Expression,
}

#[derive(Debug)]
pub struct Identifier {
    pub token: Token,
    pub value: String,
}

impl Identifier {
    pub fn new(token: Token, value: String) -> Identifier {
        Identifier { token, value }
    }
}

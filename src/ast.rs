use crate::lexer::Token;

#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Expression,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStatement {
    pub token: Token,
    pub return_value: Expression,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExpressionStatement {
    pub token: Token,
    pub expression: Expression,
}

impl ExpressionStatement {
    pub fn new(token: Token, expression: Expression) -> ExpressionStatement {
        ExpressionStatement { token, expression }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockStatement {
    pub token: Token,
    pub statements: Vec<Statement>,
}

impl BlockStatement {
    pub fn new(token: Token, statements: Vec<Statement>) -> BlockStatement {
        BlockStatement { token, statements }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Identifier(Identifier),
    NumberLiteral(NumberLiteral),
    Boolean(Boolean),
    PrefixExpression(PrefixExpression),
    InfixExpression(InfixExpression),
    IfExpression(IfExpression),
    FunctionLiteral(FunctionLiteral),
    CallExpression(CallExpression),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier {
    pub token: Token,
}

impl Identifier {
    pub fn new(token: Token) -> Identifier {
        Identifier { token }
    }

    pub fn get_token_value(&self) -> String {
        match &self.token {
            Token::Identifier(value) => value.to_string(),
            _ => panic!("Identifier::get_token_value() called on non-identifier token"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NumberLiteral {
    pub token: Token,
    pub value: i64,
}

impl NumberLiteral {
    pub fn new(token: Token, value: i64) -> NumberLiteral {
        NumberLiteral { token, value }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Boolean {
    pub token: Token,
}

impl Boolean {
    pub fn new(token: Token) -> Boolean {
        Boolean { token }
    }
}

impl From<&Boolean> for bool {
    fn from(b: &Boolean) -> Self {
        match b.token {
            Token::True => true,
            Token::False => false,
            _ => panic!("bool::from(Boolean) called on non-boolean token"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct PrefixExpression {
    pub token: Token,
    pub operator: String,
    pub right: Box<Expression>,
}

impl PrefixExpression {
    pub fn new(token: Token, operator: String, right: Expression) -> PrefixExpression {
        PrefixExpression {
            token,
            operator,
            right: Box::new(right),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InfixExpression {
    pub token: Token,
    pub left: Box<Expression>,
    pub operator: String,
    pub right: Box<Expression>,
}

impl InfixExpression {
    pub fn new(
        token: Token,
        left: Expression,
        operator: String,
        right: Expression,
    ) -> InfixExpression {
        InfixExpression {
            token,
            left: Box::new(left),
            operator,
            right: Box::new(right),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfExpression {
    pub token: Token,
    pub condition: Box<Expression>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

impl IfExpression {
    pub fn new(
        token: Token,
        condition: Expression,
        consequence: BlockStatement,
        alternative: Option<BlockStatement>,
    ) -> IfExpression {
        IfExpression {
            token,
            condition: Box::new(condition),
            consequence,
            alternative,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionLiteral {
    pub token: Token,
    pub parameters: Vec<Identifier>,
    pub body: BlockStatement,
}

impl FunctionLiteral {
    pub fn new(token: Token, parameters: Vec<Identifier>, body: BlockStatement) -> FunctionLiteral {
        FunctionLiteral {
            token,
            parameters,
            body,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpression {
    pub token: Token,
    pub function: Box<Expression>,
    pub arguments: Vec<Expression>,
}

impl CallExpression {
    pub fn new(token: Token, function: Expression, arguments: Vec<Expression>) -> CallExpression {
        CallExpression {
            token,
            function: Box::new(function),
            arguments,
        }
    }
}

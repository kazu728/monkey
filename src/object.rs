use core::fmt;

use crate::{
    ast::{BlockStatement, Boolean, Identifier},
    environment::Environment,
    lexer::Token,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Object {
    Integer(i64),
    String(String),
    Bool(bool),
    Return(Box<Object>),
    Function(Vec<Identifier>, BlockStatement, Environment),
    BuiltinFunction(fn(Vec<Object>) -> Object),
    Array(Vec<Object>),
    Error(String),
    Null,
}

pub const OBJECT_NULL: Object = Object::Null;

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Object::Integer(val) => write!(f, "{}", val),
            Object::String(val) => write!(f, "{}", val),
            Object::Bool(val) => write!(f, "{}", val),
            Object::Return(val) => write!(f, "return {}", val),
            Object::Error(val) => write!(f, "error: {}", val),
            Object::Null => write!(f, "null"),
            Object::Function(identifiers, body, env) => write!(
                f,
                "function {} {:?} {:?}",
                identifiers
                    .iter()
                    .map(|i| i.get_token_value())
                    .collect::<Vec<String>>()
                    .join(", "),
                body,
                env
            ),
            Object::BuiltinFunction(_) => write!(f, "builtin function"),
            Object::Array(vals) => write!(
                f,
                "[{}]",
                vals.iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        }
    }
}

pub fn transform_to_object_type(object: &Object) -> &'static str {
    match object {
        Object::Integer(_) => "INTEGER",
        Object::String(_) => "STRING",
        Object::Bool(_) => "BOOLEAN",
        Object::Return(_) => "RETURN",
        Object::Function(_, _, _) => "FUNCTION",
        Object::BuiltinFunction(_) => "BUILTIN",
        Object::Array(_) => "ARRAY",
        Object::Error(_) => "ERROR",
        Object::Null => "NULL",
    }
}

pub const OBJECT_TRUE: Object = Object::Bool(true);
pub const OBJECT_FALSE: Object = Object::Bool(false);

impl From<Boolean> for Object {
    fn from(b: Boolean) -> Self {
        match b.token {
            Token::True => OBJECT_TRUE,
            Token::False => OBJECT_FALSE,
            _ => panic!("Object::from(Boolean) called on non-boolean token"),
        }
    }
}

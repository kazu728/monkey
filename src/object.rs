use core::fmt;

#[derive(Debug, Clone)]
pub enum Object {
    Integer(i64),
    Bool(bool),
    Return(Box<Object>),
    Error(String),
    Null,
}

pub const OBJECT_NULL: Object = Object::Null;

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Object::Integer(val) => write!(f, "{}", val),
            Object::Bool(val) => write!(f, "{}", val),
            Object::Return(val) => write!(f, "return {}", val),
            Object::Error(val) => write!(f, "error: {}", val),
            Object::Null => write!(f, "null"),
        }
    }
}

const OBJECT_TRUE: Object = Object::Bool(true);
const OBJECT_FALSE: Object = Object::Bool(false);

impl From<bool> for Object {
    fn from(b: bool) -> Self {
        if b {
            OBJECT_TRUE
        } else {
            OBJECT_FALSE
        }
    }
}

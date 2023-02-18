use std::collections::HashMap;

use crate::object::Object;

#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
    store: HashMap<String, Object>,
    outer: Box<Option<Environment>>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment {
            store: HashMap::new(),
            outer: Box::new(None),
        }
    }

    pub fn new_enclosed_environment(outer: Environment) -> Environment {
        Environment {
            store: HashMap::new(),
            outer: Box::new(Some(outer)),
        }
    }

    pub fn get(&self, name: &str) -> Option<&Object> {
        match self.store.get(name) {
            Some(obj) => Some(obj),
            None => match &*self.outer {
                Some(env) => env.get(name),
                None => None,
            },
        }
    }

    pub fn set(&mut self, name: String, value: Object) -> Option<Object> {
        self.store.insert(name, value)
    }
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

use phf::phf_map;

use crate::object::{transform_to_object_type, Object};

pub static BUILTIN: phf::Map<&'static str, Object> = phf_map! {
    "len" => Object::BuiltinFunction(len),
};

fn len(objects: Vec<Object>) -> Object {
    if objects.len() != 1 {
        return Object::Error(format!(
            "wrong number of arguments. got={}, want=1",
            objects.len()
        ));
    }

    match objects.get(0) {
        Some(Object::String(s)) => Object::Integer(s.len() as i64),
        Some(a) => Object::Error(format!(
            "argument to `len` not supported, got {}",
            transform_to_object_type(a)
        )),
        None => Object::Error("argument to `len` not supported".to_string()),
    }
}

use phf::phf_map;

use crate::object::{transform_to_object_type, Object};

pub static BUILTIN: phf::Map<&'static str, Object> = phf_map! {
    "len" => Object::BuiltinFunction(len),
    "first" => Object::BuiltinFunction(first),
    "last" => Object::BuiltinFunction(last),
    "rest" => Object::BuiltinFunction(rest),
    "push" => Object::BuiltinFunction(push),
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
        Some(Object::Array(a)) => Object::Integer(a.len() as i64),
        Some(a) => Object::Error(format!(
            "argument to `len` not supported, got {}",
            transform_to_object_type(a)
        )),
        None => Object::Error("argument to `len` not supported".to_string()),
    }
}

fn first(objects: Vec<Object>) -> Object {
    if objects.len() != 1 {
        return Object::Error(format!(
            "wrong number of arguments. got={}, want=1",
            objects.len()
        ));
    }

    match objects.get(0) {
        Some(Object::Array(a)) => match a.get(0) {
            Some(o) => o.clone(),
            None => Object::Null,
        },
        Some(a) => Object::Error(format!(
            "argument to `first` not supported, got {}",
            transform_to_object_type(a)
        )),
        None => Object::Error("argument to `first` not supported".to_string()),
    }
}

fn last(obejcts: Vec<Object>) -> Object {
    if obejcts.len() != 1 {
        return Object::Error(format!(
            "wrong number of arguments. got={}, want=1",
            obejcts.len()
        ));
    }

    match obejcts.get(0) {
        Some(Object::Array(a)) => match a.last() {
            Some(o) => o.clone(),
            None => Object::Null,
        },
        Some(a) => Object::Error(format!(
            "argument to `last` not supported, got {}",
            transform_to_object_type(a)
        )),
        None => Object::Error("argument to `last` not supported".to_string()),
    }
}

fn rest(objects: Vec<Object>) -> Object {
    if objects.len() != 1 {
        return Object::Error(format!(
            "wrong number of arguments. got={}, want=1",
            objects.len()
        ));
    }

    match objects.get(0) {
        Some(Object::Array(a)) => match a.get(1..) {
            Some(o) => Object::Array(o.to_vec()),
            None => Object::Null,
        },
        Some(a) => Object::Error(format!(
            "argument to `rest` not supported, got {}",
            transform_to_object_type(a)
        )),
        None => Object::Error("argument to `rest` not supported".to_string()),
    }
}

fn push(objects: Vec<Object>) -> Object {
    if objects.len() != 2 {
        return Object::Error(format!(
            "wrong number of arguments. got={}, want=2",
            objects.len()
        ));
    }

    match objects.get(0) {
        Some(Object::Array(a)) => {
            let mut new_array = a.to_vec();
            new_array.push(objects.get(1).unwrap().clone());
            Object::Array(new_array)
        }
        Some(a) => Object::Error(format!(
            "argument to `push` not supported, got {}",
            transform_to_object_type(a)
        )),
        None => Object::Error("argument to `push` not supported".to_string()),
    }
}

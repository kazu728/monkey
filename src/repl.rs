use std::io;

use super::environment::Environment;
use super::evaluator::eval;
use super::lexer::Lexer;
use super::parser::Parser;

const PROMPT: &str = "λ ";

fn prompt(s: &str) -> io::Result<()> {
    use std::io::{stdout, Write};
    let mut stdout = stdout().lock();

    stdout.write(s.as_bytes()).and(stdout.flush())
}

pub fn start() {
    use std::io::{stdin, BufRead, BufReader};
    let mut lines = BufReader::new(stdin().lock()).lines();
    let mut env = Environment::new();

    loop {
        prompt(PROMPT).unwrap();
        if let Some(Ok(line)) = lines.next() {
            let program = Parser::new(Lexer::new(line)).parse_program();
            let evaluated = eval(program, &mut env);

            println!("{}", evaluated);
        } else {
            break;
        }
    }
}

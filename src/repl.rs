use std::io;

use crate::lexer::Lexer;

const PROMPT: &str = "λ ";

fn prompt(s: &str) -> io::Result<()> {
    use std::io::{stdout, Write};
    let mut stdout = stdout().lock();

    stdout.write(s.as_bytes()).and(stdout.flush())
}

pub fn start() {
    use std::io::{stdin, BufRead, BufReader};
    let mut lines = BufReader::new(stdin().lock()).lines();

    loop {
        prompt(PROMPT).unwrap();
        if let Some(Ok(line)) = lines.next() {
            let mut lexer = Lexer::new(line);
            let token = lexer.pop_token();

            println!("{:?}", token);
        } else {
            break;
        }
    }
}

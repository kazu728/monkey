use std::io;

use crate::lexer::lex;

const PROMPT: &str = "λ ";

fn prompt(s: &str) -> io::Result<()> {
    use std::io::{stdout, Write};
    let stdout = stdout();
    let mut stdout = stdout.lock();

    stdout.write(s.as_bytes());
    stdout.flush()
}

pub fn start() {
    use std::io::{stdin, BufRead, BufReader};
    let stdin = stdin();
    let stdin = stdin.lock();
    let stdin = BufReader::new(stdin);

    let mut lines = stdin.lines();

    loop {
        prompt(PROMPT).unwrap();
        if let Some(Ok(line)) = lines.next() {
            let token = lex(&line);
            println!("{:?}", token);
        } else {
            break;
        }
    }
}

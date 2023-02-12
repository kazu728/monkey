use phf::phf_map;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Token {
    Illegal,
    Eof,

    Identifier(String),
    Number(i64),

    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,

    Eq,
    NotEq,
    Lt,
    Gt,

    Comma,
    Semicolon,

    LParen,
    RParen,
    LBrace,
    RBrace,

    Fn,
    Let,
    True,
    False,
    If,
    Else,
    Return,
}

static KEYWORDS: phf::Map<&'static str, Token> = phf_map! {
    "fn" => Token::Fn,
    "let" => Token::Let,
    "true" => Token::True,
    "false" => Token::False,
    "if" => Token::If,
    "else" => Token::Else,
    "return" => Token::Return,
};

#[derive(Debug)]
pub struct Lexer {
    input: String,
    pos: usize,
    next_token: Option<Token>,
}

impl Lexer {
    pub fn new(input: String) -> Lexer {
        Lexer {
            input,
            pos: 0,
            next_token: None,
        }
    }

    pub fn peek(&self) -> Option<char> {
        self.input.chars().nth(self.pos)
    }

    pub fn pop(&mut self) -> Option<char> {
        self.pos += 1;
        self.input.chars().nth(self.pos - 1)
    }

    pub fn pop_token(&mut self) -> Option<Token> {
        if self.next_token.is_none() {
            self.next_token = self.pop_token_internal();
        }

        self.next_token.take()
    }

    fn pop_token_internal(&mut self) -> Option<Token> {
        loop {
            match self.peek() {
                None => return None,
                Some(c) => match c {
                    'a'..='z' | '_' => {
                        let mut s = String::new();
                        while let Some('a'..='z' | '_') = self.peek() {
                            let popped = self
                                .pop()
                                .expect("Peek returned Some, but pop returned None");
                            s.push(popped);
                        }

                        return Some(match KEYWORDS.get(&s) {
                            Some(token) => token.clone(),
                            None => Token::Identifier(s),
                        });
                    }
                    '0'..='9' => {
                        let mut s = String::new();
                        while let Some('0'..='9') = self.peek() {
                            let popped = self
                                .pop()
                                .expect("Peek returned Some, but pop returned None");
                            s.push(popped);
                        }

                        return Some(Token::Number(s.parse().unwrap()));
                    }
                    '=' => {
                        self.pop();
                        if self.peek() == Some('=') {
                            self.pop();
                            return Some(Token::Eq);
                        } else {
                            return Some(Token::Assign);
                        }
                    }
                    '+' => return self.pop().and(Some(Token::Plus)),
                    '-' => return self.pop().and(Some(Token::Minus)),
                    '!' => {
                        self.pop();
                        if self.peek() == Some('=') {
                            self.pop();
                            return Some(Token::NotEq);
                        } else {
                            return Some(Token::Bang);
                        }
                    }
                    '*' => return self.pop().and(Some(Token::Asterisk)),
                    '/' => return self.pop().and(Some(Token::Slash)),
                    '<' => return self.pop().and(Some(Token::Lt)),
                    '>' => return self.pop().and(Some(Token::Gt)),
                    '(' => return self.pop().and(Some(Token::LParen)),
                    ')' => return self.pop().and(Some(Token::RParen)),
                    '{' => return self.pop().and(Some(Token::LBrace)),
                    '}' => return self.pop().and(Some(Token::RBrace)),
                    ',' => return self.pop().and(Some(Token::Comma)),
                    ';' => return self.pop().and(Some(Token::Semicolon)),
                    ' ' | '\t' | '\n' => {
                        self.pop();
                    }
                    _ => return Some(Token::Illegal),
                },
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum LexError {
    InvalidByte,
}

#[cfg(test)]
mod tests {

    use self::super::*;

    #[test]
    fn test_lexer_with_simple_char() {
        let input = "=+(){},;";

        let expect: Vec<Token> = vec![
            Token::Assign,
            Token::Plus,
            Token::LParen,
            Token::RParen,
            Token::LBrace,
            Token::RBrace,
            Token::Comma,
            Token::Semicolon,
        ];

        let mut lexer = Lexer::new(input.to_string());

        for token in expect.iter() {
            let popped_token = lexer.pop_token();

            assert_eq!(Some(token), popped_token.as_ref());
        }
    }

    #[test]
    fn test_lexer() {
        let input = "
            let five = 5;
            let ten = 10;
            let add = fn(x, y){
                x + y;
            };
            let result = add(five, ten);
            !-/*5;
            5 < 10 > 5;
            if (5 < 10) {
                return true;
            } else {
                return false;
            }
            10 == 10;
            10 != 9;
        ";

        let expect: Vec<Token> = vec![
            Token::Let,
            Token::Identifier("five".to_string()),
            Token::Assign,
            Token::Number(5),
            Token::Semicolon,
            Token::Let,
            Token::Identifier("ten".to_string()),
            Token::Assign,
            Token::Number(10),
            Token::Semicolon,
            Token::Let,
            Token::Identifier("add".to_string()),
            Token::Assign,
            Token::Fn,
            Token::LParen,
            Token::Identifier("x".to_string()),
            Token::Comma,
            Token::Identifier("y".to_string()),
            Token::RParen,
            Token::LBrace,
            Token::Identifier("x".to_string()),
            Token::Plus,
            Token::Identifier("y".to_string()),
            Token::Semicolon,
            Token::RBrace,
            Token::Semicolon,
            Token::Let,
            Token::Identifier("result".to_string()),
            Token::Assign,
            Token::Identifier("add".to_string()),
            Token::LParen,
            Token::Identifier("five".to_string()),
            Token::Comma,
            Token::Identifier("ten".to_string()),
            Token::RParen,
            Token::Semicolon,
            Token::Bang,
            Token::Minus,
            Token::Slash,
            Token::Asterisk,
            Token::Number(5),
            Token::Semicolon,
            Token::Number(5),
            Token::Lt,
            Token::Number(10),
            Token::Gt,
            Token::Number(5),
            Token::Semicolon,
            Token::If,
            Token::LParen,
            Token::Number(5),
            Token::Lt,
            Token::Number(10),
            Token::RParen,
            Token::LBrace,
            Token::Return,
            Token::True,
            Token::Semicolon,
            Token::RBrace,
            Token::Else,
            Token::LBrace,
            Token::Return,
            Token::False,
            Token::Semicolon,
            Token::RBrace,
            Token::Number(10),
            Token::Eq,
            Token::Number(10),
            Token::Semicolon,
            Token::Number(10),
            Token::NotEq,
            Token::Number(9),
            Token::Semicolon,
        ];

        let mut lexer = Lexer::new(input.to_string());

        for token in expect.iter() {
            let popped_token = lexer.pop_token();
            assert_eq!(Some(token), popped_token.as_ref());
        }
    }
}

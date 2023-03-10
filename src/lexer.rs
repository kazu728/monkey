use phf::phf_map;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Token {
    Illegal,
    Eof,

    Identifier(String),
    Integer(i64),
    String(String),

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
    LBracket,
    RBracket,

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
    next_token: Token,
}

impl Lexer {
    pub fn new(input: String) -> Lexer {
        Lexer {
            input,
            pos: 0,
            next_token: Token::Eof,
        }
    }

    pub fn peek(&self) -> Option<char> {
        self.input.chars().nth(self.pos)
    }

    pub fn pop(&mut self) -> Option<char> {
        self.pos += 1;
        self.input.chars().nth(self.pos - 1)
    }

    pub fn pop_token(&mut self) -> Token {
        let mut token = Token::Eof;

        if self.next_token == Token::Eof {
            token = self.pop_token_internal();
        }

        token
    }

    fn pop_token_internal(&mut self) -> Token {
        loop {
            match self.peek() {
                None => return Token::Eof,
                Some(c) => match c {
                    'a'..='z' | '_' => {
                        let mut s = String::new();
                        while let Some('a'..='z' | 'A'..='Z' | '_') = self.peek() {
                            let popped = self
                                .pop()
                                .expect("Peek returned Some, but pop returned None");
                            s.push(popped);
                        }
                        return match KEYWORDS.get(&s) {
                            Some(token) => token.clone(),
                            None => Token::Identifier(s),
                        };
                    }
                    '0'..='9' => {
                        let mut s = String::new();
                        while let Some('0'..='9') = self.peek() {
                            let popped = self
                                .pop()
                                .expect("Peek returned Some, but pop returned None");
                            s.push(popped);
                        }

                        return Token::Integer(s.parse().unwrap());
                    }
                    '"' => {
                        self.pop();
                        let mut s = String::new();

                        while let Some('a'..='z' | 'A'..='Z' | '_' | ' ') = self.peek() {
                            let popped = self
                                .pop()
                                .expect("Peek returned Some, but pop returned None");
                            s.push(popped);
                        }

                        self.pop();

                        return Token::String(s);
                    }
                    '=' => {
                        self.pop();

                        return match self.peek() {
                            Some('=') => self.pop().and(Some(Token::Eq)).unwrap(),
                            _ => Token::Assign,
                        };
                    }
                    '+' => return self.pop().and(Some(Token::Plus)).unwrap(),
                    '-' => return self.pop().and(Some(Token::Minus)).unwrap(),
                    '!' => {
                        return self
                            .pop()
                            .and_then(|_| match self.peek() {
                                Some('=') => self.pop().and(Some(Token::NotEq)),
                                _ => Some(Token::Bang),
                            })
                            .unwrap()
                    }
                    '*' => return self.pop().and(Some(Token::Asterisk)).unwrap(),
                    '/' => return self.pop().and(Some(Token::Slash)).unwrap(),
                    '<' => return self.pop().and(Some(Token::Lt)).unwrap(),
                    '>' => return self.pop().and(Some(Token::Gt)).unwrap(),
                    '(' => return self.pop().and(Some(Token::LParen)).unwrap(),
                    ')' => return self.pop().and(Some(Token::RParen)).unwrap(),
                    '{' => return self.pop().and(Some(Token::LBrace)).unwrap(),
                    '}' => return self.pop().and(Some(Token::RBrace)).unwrap(),
                    '[' => return self.pop().and(Some(Token::LBracket)).unwrap(),
                    ']' => return self.pop().and(Some(Token::RBracket)).unwrap(),
                    ',' => return self.pop().and(Some(Token::Comma)).unwrap(),
                    ';' => return self.pop().and(Some(Token::Semicolon)).unwrap(),
                    ' ' | '\t' | '\n' => {
                        self.pop();
                    }
                    _ => return Token::Illegal,
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
            Token::Eof,
        ];

        let mut lexer = Lexer::new(input.to_string());

        for token in expect.iter() {
            let popped_token = lexer.pop_token();

            assert_eq!(token, &popped_token);
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
            \"foobar\"
            \"foo bar\"
            [1, 2];
        ";

        let expect: Vec<Token> = vec![
            Token::Let,
            Token::Identifier("five".to_string()),
            Token::Assign,
            Token::Integer(5),
            Token::Semicolon,
            Token::Let,
            Token::Identifier("ten".to_string()),
            Token::Assign,
            Token::Integer(10),
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
            Token::Integer(5),
            Token::Semicolon,
            Token::Integer(5),
            Token::Lt,
            Token::Integer(10),
            Token::Gt,
            Token::Integer(5),
            Token::Semicolon,
            Token::If,
            Token::LParen,
            Token::Integer(5),
            Token::Lt,
            Token::Integer(10),
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
            Token::Integer(10),
            Token::Eq,
            Token::Integer(10),
            Token::Semicolon,
            Token::Integer(10),
            Token::NotEq,
            Token::Integer(9),
            Token::Semicolon,
            Token::String("foobar".to_string()),
            Token::String("foo bar".to_string()),
            Token::LBracket,
            Token::Integer(1),
            Token::Comma,
            Token::Integer(2),
            Token::RBracket,
            Token::Semicolon,
            Token::Eof,
        ];

        let mut lexer = Lexer::new(input.to_string());

        for token in expect.iter() {
            let popped_token = lexer.pop_token();
            assert_eq!(token, &popped_token);
        }
    }
}

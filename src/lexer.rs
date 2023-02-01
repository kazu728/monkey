use phf::phf_map;
use std::str::from_utf8;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Token<'a> {
    Illegal,
    Eof,

    Identifier(&'a str),
    Number(u64),

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

#[derive(Debug, PartialEq, Eq)]
pub enum LexError {
    InvalidByte,
    ParseIntError(std::num::ParseIntError),
}

impl From<std::str::Utf8Error> for LexError {
    fn from(_: std::str::Utf8Error) -> Self {
        LexError::InvalidByte
    }
}

impl From<std::num::ParseIntError> for LexError {
    fn from(e: std::num::ParseIntError) -> Self {
        LexError::ParseIntError(e)
    }
}

pub fn lex(input: &str) -> Result<Vec<Token>, LexError> {
    let mut tokens: Vec<Token> = Vec::new();
    let binarized_input = input.as_bytes();

    let mut pos = 0;

    while pos < binarized_input.len() {
        match binarized_input[pos] {
            b'a'..=b'z' | b'_' => {
                let mut end = pos;

                while let Some(b'a'..=b'z' | b'_') = binarized_input.get(end) {
                    end += 1;
                }

                let identifier = &binarized_input[pos..end];

                tokens.push(match KEYWORDS.get(from_utf8(identifier)?) {
                    Some(token) => *token,
                    None => Token::Identifier(from_utf8(identifier)?),
                });

                pos = end - 1;
            }

            b'0'..=b'9' => {
                let mut end = pos;
                while let Some(b'0'..=b'9') = binarized_input.get(end) {
                    end += 1;
                }

                tokens.push(Token::Number(
                    from_utf8(&binarized_input[pos..end])?.parse()?,
                ));
                pos = end - 1;
            }
            b'=' => {
                let end = pos;
                if binarized_input.get(end + 1) == Some(&b'=') {
                    tokens.push(Token::Eq);
                    pos += 1;
                } else {
                    tokens.push(Token::Assign);
                }
            }
            b'+' => tokens.push(Token::Plus),
            b'-' => tokens.push(Token::Minus),
            b'*' => tokens.push(Token::Asterisk),
            b'!' => {
                let end = pos;
                if binarized_input.get(end + 1) == Some(&b'=') {
                    tokens.push(Token::NotEq);
                    pos += 1;
                } else {
                    tokens.push(Token::Bang);
                }
            }
            b'/' => tokens.push(Token::Slash),
            b'<' => tokens.push(Token::Lt),
            b'>' => tokens.push(Token::Gt),
            b'(' => tokens.push(Token::LParen),
            b')' => tokens.push(Token::RParen),
            b'{' => tokens.push(Token::LBrace),
            b'}' => tokens.push(Token::RBrace),
            b',' => tokens.push(Token::Comma),
            b';' => tokens.push(Token::Semicolon),
            b' ' | b'\n' | b'\t' | b'\r' => (),

            b => unreachable!(
                "Token\n pos:{:?}\n bin:{:?}\n Tokens: {:?}",
                pos,
                char::from_u32(b as u32).unwrap(),
                tokens
            ),
        }
        pos += 1;
    }
    tokens.push(Token::Eof);

    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use self::super::{lex, Token};

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
        assert_eq!(expect, lex(input).expect("LexError is returned"));
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
            Token::Identifier("five"),
            Token::Assign,
            Token::Number(5),
            Token::Semicolon,
            Token::Let,
            Token::Identifier("ten"),
            Token::Assign,
            Token::Number(10),
            Token::Semicolon,
            Token::Let,
            Token::Identifier("add"),
            Token::Assign,
            Token::Fn,
            Token::LParen,
            Token::Identifier("x"),
            Token::Comma,
            Token::Identifier("y"),
            Token::RParen,
            Token::LBrace,
            Token::Identifier("x"),
            Token::Plus,
            Token::Identifier("y"),
            Token::Semicolon,
            Token::RBrace,
            Token::Semicolon,
            Token::Let,
            Token::Identifier("result"),
            Token::Assign,
            Token::Identifier("add"),
            Token::LParen,
            Token::Identifier("five"),
            Token::Comma,
            Token::Identifier("ten"),
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
            Token::Eof,
        ];

        assert_eq!(expect, lex(input).expect("LexError is returned"));
    }
}

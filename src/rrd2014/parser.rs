use std::iter::FromIterator;
use std::iter::Peekable;
use std::vec::IntoIter;

use failure::Fail;

#[derive(Debug, PartialEq)]
struct Position {
    line: usize,
    column: usize,
}

#[derive(Debug, PartialEq)]
enum TokenKind {
    Mono,
    Int,
    Arrow,
    Lambda,
    Dot,
    Fun,
    Colon,
    Equal,
    DoubleArrow,
    OpaqueSealing,

    Val,
    Type,
    Module,
    Signature,
    Include,

    Where,

    LParen,
    RParen,

    Struct,
    Sig,
    End,

    Ident(String),
    IntLit(isize),
}

#[derive(Debug, PartialEq)]
struct Token {
    kind: TokenKind,
    pos: Position,
}

struct Lexer {
    line: usize,
    column: usize,
    src: Peekable<IntoIter<char>>,
    filename: Option<String>,
}

#[derive(Debug, Fail, PartialEq)]
enum LexError {
    #[fail(display = "unexpected end of file: line {}, column {}", _0, _1)]
    UnexpectedEOF(usize, usize),
}

type Res<T> = Result<T, LexError>;

impl Lexer {
    fn new(src: Vec<char>) -> Self {
        Lexer {
            line: 0,
            column: 0,
            src: src.into_iter().peekable(),
            filename: None,
        }
    }

    fn with_filename(src: Vec<char>, filename: String) -> Self {
        Lexer {
            line: 0,
            column: 0,
            src: src.into_iter().peekable(),
            filename: Some(filename),
        }
    }

    fn proceed(&mut self) {
        if let Some(ch) = self.src.next() {
            if ch == '\n' {
                self.line += 1;
                self.column = 0;
            } else {
                self.column += 1;
            }
        }
    }

    fn next(&mut self) -> Res<char> {
        self.next_opt()
            .ok_or_else(|| LexError::UnexpectedEOF(self.line, self.column))
    }

    fn next_opt(&mut self) -> Option<char> {
        if let Some(ch) = self.src.next() {
            if ch == '\n' {
                self.line += 1;
                self.column = 0;
            } else {
                self.column += 1;
            }
            Some(ch)
        } else {
            None
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.src.peek().cloned()
    }

    fn pos(&self) -> Position {
        Position {
            line: self.line,
            column: self.column,
        }
    }

    fn token(&self, kind: TokenKind) -> Token {
        Token {
            kind,
            pos: self.pos(),
        }
    }

    fn lex(&mut self) -> Option<Token> {
        macro_rules! proceeding {
            ($token:expr) => {{
                let token = $token;
                self.proceed();
                Some(token)
            }};
        };

        let pos = self.pos();
        match self.peek()? {
            '*' => proceeding!(self.token(TokenKind::Mono)),
            '.' => proceeding!(self.token(TokenKind::Dot)),
            '(' => proceeding!(self.token(TokenKind::LParen)),
            ')' => proceeding!(self.token(TokenKind::RParen)),
            ':' => {
                self.proceed();
                self.colon(pos)
            }
            '=' => {
                self.proceed();
                self.double_arrow(pos)
            }
            '-' => {
                self.proceed();
                self.arrow(pos)
            }
            '\u{03bb}' => proceeding!(self.token(TokenKind::Lambda)),
            ch if ch.is_ascii_digit() => self.int(),
            ch if ch.is_ascii_alphabetic() => self.ident(),
            _ => None,
        }
    }

    fn arrow(&mut self, pos: Position) -> Option<Token> {
        match self.next_opt()? {
            '>' => Some(Token {
                kind: TokenKind::Arrow,
                pos,
            }),
            _ => None,
        }
    }

    fn double_arrow(&mut self, pos: Position) -> Option<Token> {
        macro_rules! proceeding {
            ($token:expr) => {{
                let token = $token;
                self.proceed();
                Some(token)
            }};
        };

        match self.peek() {
            Some('>') => proceeding!(Token {
                kind: TokenKind::DoubleArrow,
                pos,
            }),
            _ => Some(Token {
                kind: TokenKind::Equal,
                pos,
            }),
        }
    }

    fn colon(&mut self, pos: Position) -> Option<Token> {
        macro_rules! proceeding {
            ($token:expr) => {{
                let token = $token;
                self.proceed();
                Some(token)
            }};
        };

        match self.peek() {
            Some('>') => proceeding!(Token {
                kind: TokenKind::OpaqueSealing,
                pos,
            }),
            _ => Some(Token {
                kind: TokenKind::Colon,
                pos,
            }),
        }
    }

    fn ident(&mut self) -> Option<Token> {
        let pos = self.pos();
        let mut v = Vec::new();
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                v.push(ch);
                self.proceed();
            } else {
                break;
            }
        }
        let kind = keyword_or_ident(String::from_iter(v));
        Some(Token { kind, pos })
    }

    fn int(&mut self) -> Option<Token> {
        let pos = self.pos();
        let mut n = 0;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                n = n * 10 + ch.to_digit(10).unwrap() as isize;
            } else if ch != '_' {
                break;
            }
            self.proceed();
        }
        Some(Token {
            kind: TokenKind::IntLit(n),
            pos,
        })
    }
}

fn keyword_or_ident(s: String) -> TokenKind {
    match s.as_str() {
        "int" => TokenKind::Int,
        "fun" => TokenKind::Fun,
        "val" => TokenKind::Val,
        "type" => TokenKind::Type,
        "module" => TokenKind::Module,
        "signature" => TokenKind::Signature,
        "include" => TokenKind::Include,
        "where" => TokenKind::Where,
        "struct" => TokenKind::Struct,
        "sig" => TokenKind::Sig,
        "end" => TokenKind::End,
        _ => TokenKind::Ident(s),
    }
}

#[cfg(test)]
mod tests {
    #![warn(dead_code)]

    use super::*;

    #[test]
    fn lambda() {
        let mut l = Lexer::new(vec!['λ']);
        assert_eq!(
            l.lex(),
            Some(Token {
                kind: TokenKind::Lambda,
                pos: Position { line: 0, column: 0 }
            })
        );
    }

    #[test]
    fn int_literal() {
        let mut l = Lexer::new(vec!['0', '1', '_', '9']);
        assert_eq!(
            l.lex(),
            Some(Token {
                kind: TokenKind::IntLit(19),
                pos: Position { line: 0, column: 0 }
            })
        );
    }
}

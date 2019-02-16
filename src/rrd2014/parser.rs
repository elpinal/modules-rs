use std::io;
use std::io::Read;
use std::iter::FromIterator;
use std::iter::Peekable;
use std::vec::IntoIter;

use failure::Fail;

use super::*;

#[derive(Clone, Debug, PartialEq)]
struct Position {
    line: usize,
    column: usize,
}

#[derive(Clone, Debug, PartialEq)]
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

#[derive(Clone, Debug, PartialEq)]
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

struct Parser {
    src: Peekable<IntoIter<Token>>,
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

    fn lex_all(&mut self) -> Vec<Token> {
        let mut v = Vec::new();
        while let Some(token) = self.lex() {
            v.push(token);
        }
        v
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

impl Parser {
    fn new(src: Vec<Token>) -> Self {
        Parser {
            src: src.into_iter().peekable(),
            filename: None,
        }
    }

    fn with_filename(src: Vec<Token>, filename: String) -> Self {
        Parser {
            src: src.into_iter().peekable(),
            filename: Some(filename),
        }
    }

    fn next_opt(&mut self) -> Option<Token> {
        self.src.next()
    }

    fn proceed(&mut self) {
        self.src.next();
    }

    fn peek(&mut self) -> Option<Token> {
        self.src.peek().cloned()
    }

    fn kind(&mut self) -> Option<Kind> {
        match self.next_opt()?.kind {
            TokenKind::Mono => Some(Kind::Mono),
            _ => None,
        }
    }

    fn type_atom(&mut self) -> Option<Type> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Int,
                ..
            }) => Some(Type::Int),
            Some(Token {
                kind: TokenKind::LParen,
                ..
            }) => {
                self.proceed();
                let ty = self.r#type()?;
                self.expect(TokenKind::RParen)?;
                Some(ty)
            }
            _ => None,
        }
    }

    fn r#type(&mut self) -> Option<Type> {
        let ty = self.type_atom()?;
        match self.peek() {
            Some(Token {
                kind: TokenKind::Arrow,
                ..
            }) => Some(Type::fun(ty, self.r#type()?)),
            _ => Some(ty),
        }
    }

    fn expr_atom(&mut self) -> Option<Expr> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::IntLit(n),
                ..
            }) => Some(Expr::Int(n)),
            Some(Token {
                kind: TokenKind::LParen,
                ..
            }) => {
                self.proceed();
                let e = self.expr()?;
                self.expect(TokenKind::RParen)?;
                Some(e)
            }
            _ => None,
        }
    }

    fn expect(&mut self, kind: TokenKind) -> Option<Token> {
        match self.next_opt()? {
            token if token.kind == kind => Some(token),
            _ => None,
        }
    }

    fn abs(&mut self) -> Option<Expr> {
        match self.peek()?.kind {
            TokenKind::Ident(s) => {
                let id = Ident::from(s);
                self.expect(TokenKind::Dot)?;
                let e = self.expr()?;
                Some(Expr::abs(id, e))
            }
            _ => None,
        }
    }

    fn expr(&mut self) -> Option<Expr> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Lambda,
                ..
            }) => {
                self.proceed();
                self.abs()
            }
            Some(_) => {
                let mut e0 = self.expr_atom()?;
                while let Some(e) = self.expr_atom() {
                    e0 = Expr::app(e0, e);
                }
                Some(e0)
            }
            None => None,
        }
    }

    fn decl(&mut self) -> Option<Decl> {
        let token_opt = self.peek();
        match token_opt?.kind {
            TokenKind::Val => {
                self.proceed();
                self.val_decl()
            }
            TokenKind::Type => {
                self.proceed();
                self.type_decl()
            }
            TokenKind::Module => {
                self.proceed();
                self.module_decl()
            }
            TokenKind::Signature => {
                self.proceed();
                self.signature_decl()
            }
            TokenKind::Include => {
                self.proceed();
                self.include_decl()
            }
            _ => None,
        }
    }

    fn ident(&mut self) -> Option<Ident> {
        match self.next_opt()?.kind {
            TokenKind::Ident(s) => Some(Ident::from(s)),
            _ => None,
        }
    }

    fn val_decl(&mut self) -> Option<Decl> {
        let id = self.ident()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.r#type()?;
        Some(Decl::Val(id, ty))
    }

    fn type_decl(&mut self) -> Option<Decl> {
        let id = self.ident()?;
        match self.next_opt()?.kind {
            TokenKind::Colon => {
                let k = self.kind()?;
                Some(Decl::AbsType(id, k))
            }
            TokenKind::Equal => {
                let ty = self.r#type()?;
                Some(Decl::ManType(id, ty))
            }
            _ => None,
        }
    }

    fn module_decl(&mut self) -> Option<Decl> {
        let id = self.ident()?;
        self.expect(TokenKind::Colon)?;
        let sig = self.signature()?;
        Some(Decl::Module(id, sig))
    }

    fn signature_decl(&mut self) -> Option<Decl> {
        let id = self.ident()?;
        self.expect(TokenKind::Equal)?;
        let sig = self.signature()?;
        Some(Decl::Signature(id, sig))
    }

    fn include_decl(&mut self) -> Option<Decl> {
        let sig = self.signature()?;
        Some(Decl::Include(sig))
    }

    fn signature(&mut self) -> Option<Sig> {
        match self.peek()?.kind {
            TokenKind::Sig => {
                let mut v = Vec::new();
                while let Some(decl) = self.decl() {
                    v.push(decl);
                }
                self.expect(TokenKind::End)?;
                Some(Sig::Seq(v))
            }
            TokenKind::LParen => {
                let id = self.ident()?;
                self.expect(TokenKind::Colon)?;
                let sig1 = self.signature()?;
                self.expect(TokenKind::RParen)?;
                self.expect(TokenKind::Arrow)?;
                let sig2 = self.signature()?;
                Some(Sig::fun(id, sig1, sig2))
            }
            _ => None,
        }
    }

    fn binding(&mut self) -> Option<Binding> {
        let token_opt = self.peek();
        match token_opt?.kind {
            TokenKind::Val => {
                self.proceed();
                self.val_binding()
            }
            TokenKind::Type => {
                self.proceed();
                self.type_binding()
            }
            TokenKind::Module => {
                self.proceed();
                self.module_binding()
            }
            TokenKind::Signature => {
                self.proceed();
                self.signature_binding()
            }
            TokenKind::Include => {
                self.proceed();
                self.include_binding()
            }
            _ => None,
        }
    }

    fn val_binding(&mut self) -> Option<Binding> {
        let id = self.ident()?;
        self.expect(TokenKind::Equal)?;
        let e = self.expr()?;
        Some(Binding::Val(id, e))
    }

    fn type_binding(&mut self) -> Option<Binding> {
        let id = self.ident()?;
        self.expect(TokenKind::Equal)?;
        let ty = self.r#type()?;
        Some(Binding::Type(id, ty))
    }

    fn module_binding(&mut self) -> Option<Binding> {
        let id = self.ident()?;
        self.expect(TokenKind::Equal)?;
        let m = self.module()?;
        Some(Binding::Module(id, m))
    }

    fn signature_binding(&mut self) -> Option<Binding> {
        let id = self.ident()?;
        self.expect(TokenKind::Equal)?;
        let sig = self.signature()?;
        Some(Binding::Signature(id, sig))
    }

    fn include_binding(&mut self) -> Option<Binding> {
        let m = self.module()?;
        Some(Binding::Include(m))
    }

    fn module(&mut self) -> Option<Module> {
        match self.peek()?.kind {
            TokenKind::Struct => {
                let mut v = Vec::new();
                while let Some(binding) = self.binding() {
                    v.push(binding);
                }
                self.expect(TokenKind::End)?;
                Some(Module::Seq(v))
            }
            TokenKind::Fun => {
                let id = self.ident()?;
                self.expect(TokenKind::Colon)?;
                let sig = self.signature()?;
                self.expect(TokenKind::Arrow)?;
                let m = self.module()?;
                Some(Module::fun(id, sig, m))
            }
            _ => None,
        }
    }
}

fn parse<I>(src: I) -> Option<Module>
where
    I: IntoIterator<Item = char>,
{
    let mut l = Lexer::new(src.into_iter().collect());
    let tokens = l.lex_all();
    let mut p = Parser::new(tokens);
    p.module()
}

pub fn parse_file<P>(filename: P) -> io::Result<Option<Module>>
where
    P: AsRef<std::path::Path>,
{
    use std::fs::File;
    let mut s = String::new();
    let mut f = File::open(filename)?;
    f.read_to_string(&mut s)?;
    Ok(parse(s.chars()))
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

    #[test]
    fn parse_module() {
        let mut p = Parser::new(vec![]);
        assert_eq!(p.module(), None);
    }
}

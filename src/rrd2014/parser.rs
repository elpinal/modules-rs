use std::io::Read;
use std::iter::FromIterator;
use std::iter::Peekable;
use std::vec::IntoIter;

use failure::err_msg;
use failure::Fail;
use failure::Fallible;

use super::*;

#[derive(Clone, Debug, Default, PartialEq)]
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

    Pack,
    Unpack,

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

struct State(Peekable<IntoIter<Token>>);

#[derive(Debug, Fail, PartialEq)]
enum LexError {
    #[fail(display = "no token")]
    NoToken,

    #[fail(display = "unexpected end of file: line {}, column {}", _0, _1)]
    UnexpectedEOF(usize, usize),

    #[fail(display = "{}:{}: illegal character: {:?}", _0, _1, _2)]
    IllegalCharacter(usize, usize, char),

    #[fail(display = "{}:{}: expected {:?}, but found {:?}", _0, _1, _2, _3)]
    Expected(usize, usize, char, char),
}

type Res<T> = Result<T, LexError>;

impl TokenKind {
    fn ident(s: &str) -> Self {
        TokenKind::Ident(s.to_string())
    }
}

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

    fn peek(&mut self) -> Res<char> {
        self.src.peek().cloned().ok_or(LexError::NoToken)
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

    fn lex(&mut self) -> Res<Token> {
        macro_rules! proceeding {
            ($token:expr) => {{
                let token = $token;
                self.proceed();
                Ok(token)
            }};
        };

        let pos = self.pos();
        match self.peek()? {
            ' ' | '\n' | '\t' => {
                self.proceed();
                self.lex()
            }
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
            ch => Err(LexError::IllegalCharacter(self.line, self.column, ch)),
        }
    }

    fn arrow(&mut self, pos: Position) -> Res<Token> {
        match self.next_opt() {
            Some('>') => Ok(Token {
                kind: TokenKind::Arrow,
                pos,
            }),
            Some(ch) => Err(LexError::Expected(self.line, self.column, '>', ch)),
            None => Err(LexError::UnexpectedEOF(self.line, self.column)),
        }
    }

    fn double_arrow(&mut self, pos: Position) -> Res<Token> {
        macro_rules! proceeding {
            ($token:expr) => {{
                let token = $token;
                self.proceed();
                Ok(token)
            }};
        };

        match self.peek() {
            Ok('>') => proceeding!(Token {
                kind: TokenKind::DoubleArrow,
                pos,
            }),
            _ => Ok(Token {
                kind: TokenKind::Equal,
                pos,
            }),
        }
    }

    fn colon(&mut self, pos: Position) -> Res<Token> {
        macro_rules! proceeding {
            ($token:expr) => {{
                let token = $token;
                self.proceed();
                Ok(token)
            }};
        };

        match self.peek() {
            Ok('>') => proceeding!(Token {
                kind: TokenKind::OpaqueSealing,
                pos,
            }),
            _ => Ok(Token {
                kind: TokenKind::Colon,
                pos,
            }),
        }
    }

    fn ident(&mut self) -> Res<Token> {
        let pos = self.pos();
        let mut v = Vec::new();
        while let Ok(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                v.push(ch);
                self.proceed();
            } else {
                break;
            }
        }
        let kind = keyword_or_ident(String::from_iter(v));
        Ok(Token { kind, pos })
    }

    fn int(&mut self) -> Res<Token> {
        let pos = self.pos();
        let mut n = 0;
        while let Ok(ch) = self.peek() {
            if ch.is_ascii_digit() {
                n = n * 10 + ch.to_digit(10).unwrap() as isize;
            } else if ch != '_' {
                break;
            }
            self.proceed();
        }
        Ok(Token {
            kind: TokenKind::IntLit(n),
            pos,
        })
    }

    fn lex_all(&mut self) -> Res<Vec<Token>> {
        let mut v = Vec::new();
        loop {
            match self.lex() {
                Ok(token) => v.push(token),
                Err(LexError::NoToken) => return Ok(v),
                Err(e) => return Err(e),
            }
        }
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
        "pack" => TokenKind::Pack,
        "unpack" => TokenKind::Unpack,
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

    fn save(&self) -> State {
        State(self.src.clone())
    }

    fn restore(&mut self, s: State) {
        self.src = s.0
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
        match self.peek()?.kind {
            TokenKind::Int => {
                self.proceed();
                Some(Type::Int)
            }
            TokenKind::Ident(_) => {
                let m = self.module()?;
                Some(Type::path(m))
            }
            TokenKind::LParen => {
                let state = self.save();
                if let Some(m) = self.module() {
                    return Some(Type::path(m));
                } else {
                    self.restore(state);
                }
                self.proceed();
                let ty = self.r#type()?;
                self.expect(TokenKind::RParen)?;
                Some(ty)
            }
            TokenKind::Pack => {
                self.proceed();
                let sig = self.signature_atom()?;
                Some(Type::pack(sig))
            }
            _ => None,
        }
    }

    fn r#type(&mut self) -> Option<Type> {
        let ty = self.type_atom()?;
        match self.peek().map(|t| t.kind) {
            Some(TokenKind::Arrow) => {
                self.proceed();
                Some(Type::fun(ty, self.r#type()?))
            }
            _ => Some(ty),
        }
    }

    fn expr_atom(&mut self) -> Option<Expr> {
        match self.peek()?.kind {
            TokenKind::IntLit(n) => {
                self.proceed();
                Some(Expr::Int(n))
            }
            TokenKind::Ident(s) => {
                self.proceed();
                let mut m0 = Module::Ident(Ident::from(s));
                while self.peek_expect(TokenKind::Dot) {
                    self.proceed();
                    let id = self.ident()?;
                    m0 = Module::proj(m0, id);
                }
                Some(Expr::path(m0))
            }
            TokenKind::LParen => {
                let state = self.save();
                if let Some(e) = self.expr_atom_aux() {
                    return Some(e);
                } else {
                    self.restore(state);
                }
                Some(Expr::path(self.module()?))
            }
            _ => None,
        }
    }

    fn expr_atom_aux(&mut self) -> Option<Expr> {
        self.proceed();
        let e = self.expr()?;
        self.expect(TokenKind::RParen)?;
        Some(e)
    }

    fn expect(&mut self, kind: TokenKind) -> Option<Token> {
        match self.next_opt()? {
            token if token.kind == kind => Some(token),
            _ => None,
        }
    }

    fn peek_expect(&mut self, kind: TokenKind) -> bool {
        if let Some(token) = self.peek() {
            token.kind == kind
        } else {
            false
        }
    }

    fn abs(&mut self) -> Option<Expr> {
        match self.next_opt()?.kind {
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
        match self.peek()?.kind {
            TokenKind::Lambda => {
                self.proceed();
                self.abs()
            }
            TokenKind::Pack => {
                self.proceed();
                let m = self.module()?;
                self.expect(TokenKind::Colon)?;
                let sig = self.signature()?;
                Some(Expr::pack(m, sig))
            }
            _ => {
                let mut e0 = self.expr_atom()?;
                while let Some(e) = self.expr_atom() {
                    e0 = Expr::app(e0, e);
                }
                Some(e0)
            }
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

    fn peek_ident(&mut self) -> Option<Ident> {
        match self.peek()?.kind {
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

    fn signature_atom(&mut self) -> Option<Sig> {
        match self.peek()?.kind {
            TokenKind::Sig => {
                self.proceed();
                let mut v = Vec::new();
                while let Some(decl) = self.decl() {
                    v.push(decl);
                }
                self.expect(TokenKind::End)?;
                Some(Sig::Seq(v))
            }
            TokenKind::Ident(_) => {
                let m = self.module()?;
                Some(Sig::path(m))
            }
            TokenKind::LParen => {
                let state = self.save();
                if let Some(m) = self.module() {
                    return Some(Sig::path(m));
                } else {
                    self.restore(state);
                }
                self.proceed();
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

    fn signature(&mut self) -> Option<Sig> {
        let sig = self.signature_atom()?;
        if self.peek_expect(TokenKind::Where) {
            self.proceed();
            self.expect(TokenKind::Type)?;
            let root = self.ident()?;
            let mut v = Vec::new();
            while self.peek_expect(TokenKind::Dot) {
                self.proceed();
                v.push(self.ident()?);
            }
            self.expect(TokenKind::Equal)?;
            let ty = self.r#type()?;
            Some(Sig::r#where(sig, Proj(root, v), ty))
        } else {
            Some(sig)
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

    fn module_ident(&mut self, id: Ident) -> Option<Module> {
        match self.peek().map(|t| t.kind) {
            Some(TokenKind::OpaqueSealing) => {
                self.proceed();
                let sig = self.signature()?;
                Some(Module::Seal(id, sig))
            }
            Some(TokenKind::Ident(s)) => {
                self.proceed();
                Some(Module::App(id, Ident::from(s)))
            }
            _ => Some(Module::Ident(id)),
        }
    }

    fn module_atom(&mut self) -> Option<Module> {
        match self.peek()?.kind {
            TokenKind::Ident(s) => {
                self.proceed();
                self.module_ident(Ident::from(s))
            }
            TokenKind::LParen => {
                self.proceed();
                let m = self.module()?;
                self.expect(TokenKind::RParen)?;
                Some(m)
            }
            _ => None,
        }
    }

    fn module(&mut self) -> Option<Module> {
        match self.peek()?.kind {
            TokenKind::Struct => {
                self.proceed();
                let mut v = Vec::new();
                while let Some(binding) = self.binding() {
                    v.push(binding);
                }
                self.expect(TokenKind::End)?;
                Some(Module::Seq(v))
            }
            TokenKind::Fun => {
                self.proceed();
                let id = self.ident()?;
                self.expect(TokenKind::Colon)?;
                let sig = self.signature()?;
                self.expect(TokenKind::DoubleArrow)?;
                let m = self.module()?;
                Some(Module::fun(id, sig, m))
            }
            TokenKind::Unpack => {
                self.proceed();
                let e = self.expr()?;
                self.expect(TokenKind::Colon)?;
                let sig = self.signature()?;
                Some(Module::unpack(e, sig))
            }
            _ => {
                let mut m0 = self.module_atom()?;
                while self.peek_expect(TokenKind::Dot) {
                    self.proceed();
                    let id = self.ident()?;
                    m0 = Module::proj(m0, id);
                }
                Some(m0)
            }
        }
    }
}

fn parse<I>(src: I) -> Fallible<Module>
where
    I: IntoIterator<Item = char>,
{
    let mut l = Lexer::new(src.into_iter().collect());
    let tokens = l.lex_all()?;
    let mut p = Parser::new(tokens);
    p.module().ok_or_else(|| err_msg("parse error"))
}

pub fn parse_file<P>(filename: P) -> Fallible<Module>
where
    P: AsRef<std::path::Path>,
{
    use std::fs::File;
    let mut s = String::new();
    let mut f = File::open(filename)?;
    f.read_to_string(&mut s)?;
    parse(s.chars())
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
            Ok(Token {
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
            Ok(Token {
                kind: TokenKind::IntLit(19),
                pos: Position { line: 0, column: 0 }
            })
        );
    }

    #[test]
    fn lexer() {
        let mut l = Lexer::new(vec!['s', 't', 'r', 'u', 'c', 't', ' ', 'e', 'n', 'd']);

        assert_eq!(
            l.lex(),
            Ok(Token {
                kind: TokenKind::Struct,
                pos: Position { line: 0, column: 0 }
            })
        );

        assert_eq!(
            l.lex(),
            Ok(Token {
                kind: TokenKind::End,
                pos: Position { line: 0, column: 7 }
            })
        );
    }

    #[test]
    fn parse_expr() {
        let mut p = Parser::new(vec![Token {
            kind: TokenKind::IntLit(33),
            pos: Default::default(),
        }]);
        assert_eq!(p.expr_atom(), Some(Expr::Int(33)));

        let mut p = Parser::new(vec![Token {
            kind: TokenKind::IntLit(33),
            pos: Default::default(),
        }]);
        assert_eq!(p.expr(), Some(Expr::Int(33)));

        let mut p = Parser::new(vec![Token {
            kind: TokenKind::ident("a"),
            pos: Default::default(),
        }]);
        assert_eq!(p.expr(), Some(Expr::path(Module::Ident(Ident::from("a")))));

        let mut p = Parser::new(vec![
            Token {
                kind: TokenKind::ident("a"),
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::ident("a"),
                pos: Default::default(),
            },
        ]);
        assert_eq!(
            p.expr(),
            Some(Expr::app(
                Expr::path(Module::Ident(Ident::from("a"))),
                Expr::path(Module::Ident(Ident::from("a")))
            ))
        );
    }

    #[test]
    fn parse_type() {
        let mut p = Parser::new(vec![Token {
            kind: TokenKind::Int,
            pos: Default::default(),
        }]);
        assert_eq!(p.type_atom(), Some(Type::Int));

        let mut p = Parser::new(vec![Token {
            kind: TokenKind::Int,
            pos: Default::default(),
        }]);
        assert_eq!(p.r#type(), Some(Type::Int));

        let mut p = Parser::new(vec![Token {
            kind: TokenKind::Ident("t".to_string()),
            pos: Default::default(),
        }]);
        assert_eq!(
            p.r#type(),
            Some(Type::path(Module::Ident(Ident::from("t"))))
        );
    }

    #[test]
    fn parse_signature() {
        let mut p = Parser::new(vec![
            Token {
                kind: TokenKind::Sig,
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::Type,
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::Ident("x".to_string()),
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::Equal,
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::Ident("t".to_string()),
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::End,
                pos: Default::default(),
            },
        ]);
        assert_eq!(
            p.signature(),
            Some(Sig::Seq(vec![Decl::ManType(
                Ident::from("x"),
                Type::path(Module::Ident(Ident::from("t")))
            )]))
        );
    }

    #[test]
    fn parse_decl() {
        let mut p = Parser::new(vec![
            Token {
                kind: TokenKind::Type,
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::Ident("x".to_string()),
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::Equal,
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::Ident("t".to_string()),
                pos: Default::default(),
            },
        ]);
        assert_eq!(
            p.decl(),
            Some(Decl::ManType(
                Ident::from("x"),
                Type::path(Module::Ident(Ident::from("t")))
            ))
        );
    }

    #[test]
    fn parse_binding() {
        let mut p = Parser::new(vec![
            Token {
                kind: TokenKind::Type,
                pos: Position { line: 0, column: 0 },
            },
            Token {
                kind: TokenKind::Ident("t".to_string()),
                pos: Position { line: 0, column: 5 },
            },
            Token {
                kind: TokenKind::Equal,
                pos: Position { line: 0, column: 7 },
            },
            Token {
                kind: TokenKind::Int,
                pos: Position { line: 0, column: 9 },
            },
        ]);
        assert_eq!(
            p.binding(),
            Some(Binding::Type(Ident::from("t"), Type::Int))
        );

        let mut p = Parser::new(vec![
            Token {
                kind: TokenKind::Val,
                pos: Position { line: 0, column: 0 },
            },
            Token {
                kind: TokenKind::Ident("x".to_string()),
                pos: Position { line: 0, column: 4 },
            },
            Token {
                kind: TokenKind::Equal,
                pos: Position { line: 0, column: 6 },
            },
            Token {
                kind: TokenKind::IntLit(3),
                pos: Position { line: 0, column: 8 },
            },
        ]);
        assert_eq!(
            p.binding(),
            Some(Binding::Val(Ident::from("x"), Expr::Int(3)))
        );

        let mut p = Parser::new(vec![
            Token {
                kind: TokenKind::Type,
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::Ident("x".to_string()),
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::Equal,
                pos: Default::default(),
            },
            Token {
                kind: TokenKind::Ident("t".to_string()),
                pos: Default::default(),
            },
        ]);
        assert_eq!(
            p.binding(),
            Some(Binding::Type(
                Ident::from("x"),
                Type::path(Module::Ident(Ident::from("t")))
            ))
        );
    }

    #[test]
    fn parse_module() {
        let mut p = Parser::new(vec![]);
        assert_eq!(p.module(), None);

        let mut p = Parser::new(vec![
            Token {
                kind: TokenKind::Struct,
                pos: Position { line: 0, column: 0 },
            },
            Token {
                kind: TokenKind::End,
                pos: Position { line: 0, column: 7 },
            },
        ]);
        assert_eq!(p.module(), Some(Module::Seq(vec![])));

        let mut p = Parser::new(vec![
            Token {
                kind: TokenKind::Struct,
                pos: Position { line: 0, column: 0 },
            },
            Token {
                kind: TokenKind::Type,
                pos: Position { line: 0, column: 7 },
            },
            Token {
                kind: TokenKind::Ident("t".to_string()),
                pos: Position {
                    line: 0,
                    column: 12,
                },
            },
            Token {
                kind: TokenKind::Equal,
                pos: Position {
                    line: 0,
                    column: 14,
                },
            },
            Token {
                kind: TokenKind::Int,
                pos: Position {
                    line: 0,
                    column: 16,
                },
            },
            Token {
                kind: TokenKind::End,
                pos: Position {
                    line: 0,
                    column: 20,
                },
            },
        ]);
        assert_eq!(
            p.module(),
            Some(Module::Seq(vec![Binding::Type(
                Ident::from("t"),
                Type::Int
            )]))
        );
    }
}

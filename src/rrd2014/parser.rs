use std::io::Read;
use std::iter::FromIterator;
use std::iter::Peekable;
use std::vec::IntoIter;

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

    #[fail(display = "{}:{}: expected {}, but found {:?}", _0, _1, _2, _3)]
    Expected(usize, usize, String, char),
}

#[derive(Debug, Fail, PartialEq)]
enum ParseError {
    #[fail(display = "unexpected end of file")]
    UnexpectedEOF,

    #[fail(display = "{}:{}: expected {}, but found {:?}", _0, _1, _2, _3)]
    Expected(usize, usize, String, TokenKind),

    #[fail(display = "{}:{}: expected {:?}, but found {:?}", _0, _1, _2, _3)]
    ExpectedToken(usize, usize, TokenKind, TokenKind),
}

type Res<T> = Result<T, LexError>;

type ParseRes<T> = Result<T, ParseError>;

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
            Some(ch) => Err(LexError::Expected(
                self.line,
                self.column,
                '>'.to_string(),
                ch,
            )),
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

impl ParseError {
    fn expected(s: &str, token: Token) -> Self {
        ParseError::Expected(token.pos.line, token.pos.column, s.to_string(), token.kind)
    }

    fn expected_token(kind: TokenKind, token: Token) -> Self {
        ParseError::ExpectedToken(token.pos.line, token.pos.column, kind, token.kind)
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

    fn next(&mut self) -> ParseRes<Token> {
        self.next_opt().ok_or(ParseError::UnexpectedEOF)
    }

    fn next_opt(&mut self) -> Option<Token> {
        self.src.next()
    }

    fn proceed(&mut self) {
        self.src.next();
    }

    fn peek(&mut self) -> ParseRes<Token> {
        self.src.peek().cloned().ok_or(ParseError::UnexpectedEOF)
    }

    fn expect_eof(&mut self) -> ParseRes<()> {
        if let Some(token) = self.src.peek() {
            Err(ParseError::expected("eof", token.clone()))?;
        }
        Ok(())
    }

    fn kind(&mut self) -> ParseRes<Kind> {
        let token = self.next()?;
        match token.kind {
            TokenKind::Mono => Ok(Kind::Mono),
            k => Err(ParseError::Expected(
                token.pos.line,
                token.pos.column,
                "kind".to_string(),
                k,
            )),
        }
    }

    fn type_atom(&mut self) -> ParseRes<Type> {
        let token = self.peek()?;
        match token.kind {
            TokenKind::Int => {
                self.proceed();
                Ok(Type::Int)
            }
            TokenKind::Ident(_) => {
                let m = self.module()?;
                Ok(Type::path(m))
            }
            TokenKind::LParen => {
                let state = self.save();
                if let Ok(m) = self.module() {
                    return Ok(Type::path(m));
                } else {
                    self.restore(state);
                }
                self.proceed();
                let ty = self.r#type()?;
                self.expect(TokenKind::RParen)?;
                Ok(ty)
            }
            TokenKind::Pack => {
                self.proceed();
                let sig = self.signature_atom()?;
                Ok(Type::pack(sig))
            }
            _ => Err(ParseError::expected("type", token)),
        }
    }

    fn r#type(&mut self) -> ParseRes<Type> {
        let ty = self.type_atom()?;
        match self.peek().map(|t| t.kind) {
            Ok(TokenKind::Arrow) => {
                self.proceed();
                Ok(Type::fun(ty, self.r#type()?))
            }
            _ => Ok(ty),
        }
    }

    fn expr_atom(&mut self) -> ParseRes<Expr> {
        let token = self.peek()?;
        match token.kind {
            TokenKind::IntLit(n) => {
                self.proceed();
                Ok(Expr::Int(n))
            }
            TokenKind::Ident(s) => {
                self.proceed();
                let mut m0 = Module::Ident(Ident::from(s));
                while self.peek_expect(TokenKind::Dot) {
                    self.proceed();
                    let id = self.ident()?;
                    m0 = Module::proj(m0, id);
                }
                Ok(Expr::path(m0))
            }
            TokenKind::LParen => {
                let state = self.save();
                if let Ok(e) = self.expr_atom_aux() {
                    return Ok(e);
                } else {
                    self.restore(state);
                }
                Ok(Expr::path(self.module()?))
            }
            _ => Err(ParseError::expected("expression", token)),
        }
    }

    fn expr_atom_aux(&mut self) -> ParseRes<Expr> {
        self.proceed();
        let e = self.expr()?;
        self.expect(TokenKind::RParen)?;
        Ok(e)
    }

    fn expect(&mut self, kind: TokenKind) -> ParseRes<Token> {
        match self.next()? {
            token if token.kind == kind => Ok(token),
            token => Err(ParseError::expected_token(kind, token)),
        }
    }

    fn peek_expect(&mut self, kind: TokenKind) -> bool {
        if let Ok(token) = self.peek() {
            token.kind == kind
        } else {
            false
        }
    }

    fn abs(&mut self) -> ParseRes<Expr> {
        let token = self.next()?;
        match token.kind {
            TokenKind::Ident(s) => {
                let id = Ident::from(s);
                self.expect(TokenKind::Dot)?;
                let e = self.expr()?;
                Ok(Expr::abs(id, e))
            }
            _ => Err(ParseError::expected("identifier", token)),
        }
    }

    fn expr(&mut self) -> ParseRes<Expr> {
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
                Ok(Expr::pack(m, sig))
            }
            _ => {
                let mut e0 = self.expr_atom()?;
                let mut state = self.save();
                while let Ok(e) = self.expr_atom() {
                    e0 = Expr::app(e0, e);
                    state = self.save();
                }
                self.restore(state);
                Ok(e0)
            }
        }
    }

    fn decl(&mut self) -> ParseRes<Decl> {
        let token = self.peek()?;
        match token.kind {
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
            _ => Err(ParseError::expected("declaration", token)),
        }
    }

    fn ident(&mut self) -> ParseRes<Ident> {
        let token = self.next()?;
        match token.kind {
            TokenKind::Ident(s) => Ok(Ident::from(s)),
            _ => Err(ParseError::expected("identifier", token)),
        }
    }

    fn peek_ident(&mut self) -> ParseRes<Ident> {
        let token = self.peek()?;
        match token.kind {
            TokenKind::Ident(s) => Ok(Ident::from(s)),
            _ => Err(ParseError::expected("identifier", token)),
        }
    }

    fn val_decl(&mut self) -> ParseRes<Decl> {
        let id = self.ident()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.r#type()?;
        Ok(Decl::Val(id, ty))
    }

    fn type_decl(&mut self) -> ParseRes<Decl> {
        let id = self.ident()?;
        let token = self.next()?;
        match token.kind {
            TokenKind::Colon => {
                let k = self.kind()?;
                Ok(Decl::AbsType(id, k))
            }
            TokenKind::Equal => {
                let ty = self.r#type()?;
                Ok(Decl::ManType(id, ty))
            }
            _ => Err(ParseError::expected("':' or '='", token)),
        }
    }

    fn module_decl(&mut self) -> ParseRes<Decl> {
        let id = self.ident()?;
        self.expect(TokenKind::Colon)?;
        let sig = self.signature()?;
        Ok(Decl::Module(id, sig))
    }

    fn signature_decl(&mut self) -> ParseRes<Decl> {
        let id = self.ident()?;
        self.expect(TokenKind::Equal)?;
        let sig = self.signature()?;
        Ok(Decl::Signature(id, sig))
    }

    fn include_decl(&mut self) -> ParseRes<Decl> {
        let sig = self.signature()?;
        Ok(Decl::Include(sig))
    }

    fn signature_atom(&mut self) -> ParseRes<Sig> {
        let token = self.peek()?;
        match token.kind {
            TokenKind::Sig => {
                self.proceed();
                let mut v = Vec::new();
                let mut state = self.save();
                while let Ok(decl) = self.decl() {
                    v.push(decl);
                    state = self.save();
                }
                self.restore(state);
                self.expect(TokenKind::End)?;
                Ok(Sig::Seq(v))
            }
            TokenKind::Ident(_) => {
                let m = self.module()?;
                Ok(Sig::path(m))
            }
            TokenKind::LParen => {
                let state = self.save();
                if let Ok(m) = self.module() {
                    return Ok(Sig::path(m));
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
                Ok(Sig::fun(id, sig1, sig2))
            }
            _ => Err(ParseError::expected(
                "signature ('sig', identifier, etc.)",
                token,
            )),
        }
    }

    fn signature(&mut self) -> ParseRes<Sig> {
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
            Ok(Sig::r#where(sig, Proj(root, v), ty))
        } else {
            Ok(sig)
        }
    }

    fn binding(&mut self) -> ParseRes<Binding> {
        let token = self.peek()?;
        match token.kind {
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
            _ => Err(ParseError::expected("binding", token)),
        }
    }

    fn val_binding(&mut self) -> ParseRes<Binding> {
        let id = self.ident()?;
        self.expect(TokenKind::Equal)?;
        let e = self.expr()?;
        Ok(Binding::Val(id, e))
    }

    fn type_binding(&mut self) -> ParseRes<Binding> {
        let id = self.ident()?;
        self.expect(TokenKind::Equal)?;
        let ty = self.r#type()?;
        Ok(Binding::Type(id, ty))
    }

    fn module_binding(&mut self) -> ParseRes<Binding> {
        let id = self.ident()?;
        self.expect(TokenKind::Equal)?;
        let m = self.module()?;
        Ok(Binding::Module(id, m))
    }

    fn signature_binding(&mut self) -> ParseRes<Binding> {
        let id = self.ident()?;
        self.expect(TokenKind::Equal)?;
        let sig = self.signature()?;
        Ok(Binding::Signature(id, sig))
    }

    fn include_binding(&mut self) -> ParseRes<Binding> {
        let m = self.module()?;
        Ok(Binding::Include(m))
    }

    fn module_ident(&mut self, id: Ident) -> ParseRes<Module> {
        match self.peek().map(|t| t.kind) {
            Ok(TokenKind::OpaqueSealing) => {
                self.proceed();
                let sig = self.signature()?;
                Ok(Module::Seal(id, sig))
            }
            Ok(TokenKind::Ident(s)) => {
                self.proceed();
                Ok(Module::App(id, Ident::from(s)))
            }
            _ => Ok(Module::Ident(id)),
        }
    }

    fn module_atom(&mut self) -> ParseRes<Module> {
        let token = self.peek()?;
        match token.kind {
            TokenKind::Ident(s) => {
                self.proceed();
                self.module_ident(Ident::from(s))
            }
            TokenKind::LParen => {
                self.proceed();
                let m = self.module()?;
                self.expect(TokenKind::RParen)?;
                Ok(m)
            }
            _ => Err(ParseError::expected("module", token)),
        }
    }

    fn module(&mut self) -> ParseRes<Module> {
        match self.peek()?.kind {
            TokenKind::Struct => {
                self.proceed();
                let mut v = Vec::new();
                let mut state = self.save();
                while let Ok(binding) = self.binding() {
                    v.push(binding);
                    state = self.save();
                }
                self.restore(state);
                self.expect(TokenKind::End)?;
                Ok(Module::Seq(v))
            }
            TokenKind::Fun => {
                self.proceed();
                let id = self.ident()?;
                self.expect(TokenKind::Colon)?;
                let sig = self.signature()?;
                self.expect(TokenKind::DoubleArrow)?;
                let m = self.module()?;
                Ok(Module::fun(id, sig, m))
            }
            TokenKind::Unpack => {
                self.proceed();
                let e = self.expr()?;
                self.expect(TokenKind::Colon)?;
                let sig = self.signature()?;
                Ok(Module::unpack(e, sig))
            }
            _ => {
                let mut m0 = self.module_atom()?;
                while self.peek_expect(TokenKind::Dot) {
                    self.proceed();
                    let id = self.ident()?;
                    m0 = Module::proj(m0, id);
                }
                Ok(m0)
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
    let m = p.module()?;
    p.expect_eof()?;
    Ok(m)
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

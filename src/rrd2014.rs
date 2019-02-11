//! Andreas Rossberg, Claudio V. Russo and Derek Dreyer.
//! F-ing modules.
//! Journal of Functional Programming, 24(5), 2014.

#![allow(dead_code)]

pub mod internal;

use internal::Name;

struct Ident(Name);

enum Kind {
    Mono,
}

enum Type {
    Fun(Box<Type>, Box<Type>),
    Path(Path),
    Int,
}

enum Expr {
    Var(Ident),
    Abs(Ident, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Path(Path),
    Int(isize),
}

struct Path(Box<Module>);

enum Module {
    Ident(Ident),
    Seq(Vec<Binding>),
    Proj(Box<Module>, Ident),
    Fun(Ident, Sig, Box<Module>),
    App(Ident, Ident),
    Seal(Ident, Sig),
}

enum Binding {
    Val(Ident, Expr),
    Type(Ident, Type),
    Module(Ident, Module),
    Signature(Ident, Sig),
    Include(Module),
}

enum Sig {
    Path(Path),
    Seq(Vec<Decl>),
    Fun(Ident, Box<Sig>, Box<Sig>),
    Where(Box<Sig>, Proj<Ident>, Type),
}

struct Proj<T>(T, Vec<T>);

enum Decl {
    Val(Ident, Type),
    ManType(Ident, Type),
    AbsType(Ident, Kind),
    Module(Ident, Sig),
    Signature(Ident, Sig),
    Include(Sig),
}

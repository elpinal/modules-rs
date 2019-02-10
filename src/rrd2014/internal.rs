//! The internal language.

use std::collections::HashMap;

struct Name(String);

enum Label {
    Label(Name),
}

struct Variable(usize);

struct Record<T>(HashMap<Label, T>);

enum Kind {
    Mono,
    Fun(Box<Kind>, Box<Kind>),
}

enum Type {
    Var(Variable),
    Fun(Box<Type>, Box<Type>),
    Record(Record<Type>),
    Forall(Kind, Box<Type>),
    Some(Kind, Box<Type>),
    Abs(Kind, Box<Type>),
    App(Box<Type>, Box<Type>),
    Int,
}

enum Term {
    Var(Variable),
    Abs(Type, Box<Term>),
    App(Box<Term>, Box<Term>),
    Record(Record<Term>),
    Proj(Box<Term>, Label),
    Poly(Kind, Box<Term>),
    Inst(Box<Term>, Type),
    Pack(Type, Box<Term>, Type),
    Unpack(Box<Term>, Box<Term>),
    Int(isize),
}

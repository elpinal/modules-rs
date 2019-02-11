//! Andreas Rossberg, Claudio V. Russo and Derek Dreyer.
//! F-ing modules.
//! Journal of Functional Programming, 24(5), 2014.

#![allow(dead_code)]

pub mod internal;

use std::collections::HashMap;

use failure::Fail;

use internal::Kind as IKind;
use internal::Type as IType;
use internal::{Label, Name};

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

#[derive(Clone, Debug, PartialEq)]
struct Quantified<T> {
    qs: Vec<IKind>,
    body: T,
}

#[derive(Clone, Debug, PartialEq)]
struct Existential<T>(Quantified<T>);

#[derive(Clone, Debug, PartialEq)]
struct Universal<T>(Quantified<T>);

type AbstractSig = Existential<SemanticSig>;

#[derive(Clone, Debug, PartialEq)]
struct Fun(SemanticSig, AbstractSig);

#[derive(Clone, Debug, PartialEq)]
enum SemanticSig {
    AtomicTerm(IType),
    AtomicType(IType, IKind),
    AtomicSig(Box<AbstractSig>),
    StructureSig(HashMap<Label, SemanticSig>),
    FunctorSig(Universal<Box<Fun>>),
}

#[derive(Debug, Fail, PartialEq)]
#[fail(display = "not atomic semantic signature: {:?}", _0)]
struct NonAtomicError(SemanticSig);

impl SemanticSig {
    fn atomic(&self) -> Result<(), NonAtomicError> {
        use SemanticSig::*;
        match *self {
            AtomicTerm(..) | AtomicType(..) | AtomicSig(..) => Ok(()),
            _ => Err(NonAtomicError(self.clone())),
        }
    }
}

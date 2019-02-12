//! Andreas Rossberg, Claudio V. Russo and Derek Dreyer.
//! F-ing modules.
//! Journal of Functional Programming, 24(5), 2014.

#![allow(dead_code)]

pub mod internal;

use std::collections::HashMap;
use std::convert::TryFrom;

use failure::Fail;

use internal::Kind as IKind;
use internal::Shift;
use internal::Term as ITerm;
use internal::Type as IType;
use internal::{Label, Name};
use internal::{Subst, Substitution};

#[derive(Clone, Debug, PartialEq)]
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
struct StemFrom {
    id: Ident,
    prefix: Vec<Ident>,
}

#[derive(Clone, Debug, PartialEq)]
struct Quantified<T> {
    qs: Vec<(IKind, StemFrom)>,
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

type Env = internal::Env<SemanticSig, Option<StemFrom>>;

#[derive(Debug, Fail, PartialEq)]
enum TypeError {
    #[fail(display = "not function type: {:?}", _0)]
    NotFunction(IType),

    #[fail(display = "type mismatch: {:?} and {:?}", _0, _1)]
    TypeMismatch(IType, IType),

    #[fail(display = "unification: {}", _0)]
    Unification(internal::UnificationError),
}

impl From<internal::UnificationError> for TypeError {
    fn from(e: internal::UnificationError) -> Self {
        TypeError::Unification(e)
    }
}

impl<T: Substitution> Substitution for Quantified<T> {
    fn apply(&mut self, s: &Subst) {
        let n = self.qs.len();
        let s = s.clone();
        self.body.apply(&s.shift(isize::try_from(n).unwrap()));
    }
}

impl<T: Substitution> Substitution for Existential<T> {
    fn apply(&mut self, s: &Subst) {
        self.0.apply(s);
    }
}

impl<T: Substitution> Substitution for Universal<T> {
    fn apply(&mut self, s: &Subst) {
        self.0.apply(s);
    }
}

impl Substitution for Fun {
    fn apply(&mut self, s: &Subst) {
        self.0.apply(s);
        self.1.apply(s);
    }
}

impl Substitution for SemanticSig {
    fn apply(&mut self, s: &Subst) {
        use SemanticSig::*;

        match *self {
            AtomicTerm(ref mut ty) => ty.apply(s),
            AtomicType(ref mut ty, ref mut k) => {
                k.apply(s);
                ty.apply(s);
            }
            AtomicSig(ref mut asig) => asig.apply(s),
            StructureSig(ref mut m) => m.values_mut().for_each(|ssig| ssig.apply(s)),
            FunctorSig(ref mut u) => u.apply(s),
        }
    }
}

impl<T: Substitution> Substitution for Box<T> {
    fn apply(&mut self, s: &Subst) {
        (**self).apply(s);
    }
}

impl<T: Shift> Shift for Quantified<T> {
    fn shift_above(&mut self, c: usize, d: isize) {
        let c1 = c + self.qs.len();
        self.qs.shift_above(c1, d);
        self.body.shift_above(c1, d);
    }
}

impl<T: Shift> Shift for Existential<T> {
    fn shift_above(&mut self, c: usize, d: isize) {
        self.0.shift_above(c, d);
    }
}

impl<T: Shift> Shift for Universal<T> {
    fn shift_above(&mut self, c: usize, d: isize) {
        self.0.shift_above(c, d);
    }
}

impl<T: Shift> Shift for (T, StemFrom) {
    fn shift_above(&mut self, c: usize, d: isize) {
        self.0.shift_above(c, d);
    }
}

impl Shift for Fun {
    fn shift_above(&mut self, c: usize, d: isize) {
        self.0.shift_above(c, d);
        self.1.shift_above(c, d);
    }
}

impl Shift for SemanticSig {
    fn shift_above(&mut self, c: usize, d: isize) {
        use SemanticSig::*;
        match *self {
            AtomicTerm(ref mut ty) => ty.shift_above(c, d),
            AtomicType(ref mut ty, ref mut k) => {
                ty.shift_above(c, d);
                k.shift_above(c, d);
            }
            AtomicSig(ref mut asig) => asig.shift_above(c, d),
            StructureSig(ref mut m) => m.values_mut().for_each(|ssig| ssig.shift_above(c, d)),
            FunctorSig(ref mut u) => u.shift_above(c, d),
        }
    }
}

trait Elaboration {
    type Output;
    type Error;

    fn elaborate(self, env: &mut Env) -> Result<Self::Output, Self::Error>;
}

#[derive(Debug, Fail, PartialEq)]
enum AtomicError {
    #[fail(display = "not atomic semantic signature: {:?}", _0)]
    Atomic(SemanticSig),

    #[fail(display = "not atomic term: {:?}", _0)]
    AtomicTerm(SemanticSig),

    #[fail(display = "not atomic type: {:?}", _0)]
    AtomicType(SemanticSig),
}

impl SemanticSig {
    fn atomic(&self) -> Result<(), AtomicError> {
        use SemanticSig::*;
        match *self {
            AtomicTerm(..) | AtomicType(..) | AtomicSig(..) => Ok(()),
            _ => Err(AtomicError::Atomic(self.clone())),
        }
    }

    fn get_atomic_term(self) -> Result<IType, AtomicError> {
        match self {
            SemanticSig::AtomicTerm(ty) => Ok(ty),
            _ => Err(AtomicError::AtomicTerm(self)),
        }
    }

    fn get_atomic_type(self) -> Result<(IType, IKind), AtomicError> {
        match self {
            SemanticSig::AtomicType(ty, k) => Ok((ty, k)),
            _ => Err(AtomicError::AtomicType(self)),
        }
    }
}

impl Elaboration for Kind {
    type Output = IKind;
    type Error = ();

    fn elaborate(self, _: &mut Env) -> Result<Self::Output, Self::Error> {
        match self {
            Kind::Mono => Ok(IKind::Mono),
        }
    }
}

impl Elaboration for Type {
    type Output = (IType, IKind);
    type Error = internal::NotMonoError;

    fn elaborate(self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Type::*;
        match self {
            Int => Ok((IType::Int, IKind::Mono)),
            Fun(ty1, ty2) => {
                let (ty1, k1) = ty1.elaborate(env)?;
                k1.mono()?;
                let (ty2, k2) = ty2.elaborate(env)?;
                k2.mono()?;
                Ok((IType::fun(ty1, ty2), IKind::Mono))
            }
            _ => unimplemented!(),
        }
    }
}

impl Elaboration for Expr {
    type Output = (ITerm, IType);
    type Error = TypeError;

    fn elaborate(self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        let (t, ty, _) = self.infer(env)?;
        Ok((t, ty))
    }
}

impl Expr {
    fn infer(self, env: &mut Env) -> Result<(ITerm, IType, Subst), TypeError> {
        use Expr::*;
        use IKind::*;
        match self {
            Abs(id, e) => {
                let v = env.fresh_type_variable(Mono, None);
                let mut ty0 = IType::Var(v);
                let name = Name::from(id);
                let prev = env.insert_value(name.clone(), SemanticSig::AtomicTerm(ty0.clone()));
                let (t, ty, s) = e.infer(env)?;
                env.drop_value(name, prev);
                ty0.apply(&s);
                Ok((ITerm::abs(ty0.clone(), t), IType::fun(ty0, ty), s))
            }
            App(e1, e2) => {
                let (t1, mut ty1, s1) = e1.infer(env)?;
                let (t2, ty2, s2) = e2.infer(env)?;
                ty1.apply(&s2);
                let mut v = IType::Var(env.fresh_type_variable(Mono, None));
                let s3 = env.unify(vec![(ty1, IType::fun(ty2, v.clone()))])?;
                v.apply(&s3);
                let s = s3.compose(s2).compose(s1);
                Ok((ITerm::app(t1, t2), v, s))
            }
            Int(n) => Ok((ITerm::Int(n), IType::Int, Subst::default())),
            _ => unimplemented!(),
        }
    }
}

impl Type {
    fn fun(ty1: Type, ty2: Type) -> Self {
        Type::Fun(Box::new(ty1), Box::new(ty2))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn env_insert() {
        use internal::Kind::*;
        use internal::*;
        use SemanticSig::*;

        let mut env: Env<SemanticSig, _> = Env::default();

        env.insert_types(vec![(Mono, "s"), (Kind::fun(Mono, Mono), "M.t")]);
        assert_eq!(
            env.lookup_type(Variable::new(0)),
            Ok((Kind::fun(Mono, Mono), "M.t"))
        );
        assert_eq!(env.lookup_type(Variable::new(1)), Ok((Mono, "s")));

        env.insert_value(Name::new("x".to_string()), AtomicTerm(Type::Int));
        assert_eq!(
            env.lookup_value(Variable::new(0)),
            Ok(AtomicTerm(Type::Int))
        );
    }
}

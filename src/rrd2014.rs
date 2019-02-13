//! Andreas Rossberg, Claudio V. Russo and Derek Dreyer.
//! F-ing modules.
//! Journal of Functional Programming, 24(5), 2014.

#![allow(dead_code)]

pub mod internal;

use std::collections::HashMap;
use std::convert::TryFrom;
use std::iter::FromIterator;

use failure::Fail;

use internal::EnvError;
use internal::Kind as IKind;
use internal::Record;
use internal::Shift;
use internal::Term as ITerm;
use internal::Type as IType;
use internal::{Label, Name};
use internal::{Subst, Substitution};

#[derive(Clone, Debug, PartialEq)]
struct Ident(Name);

#[derive(Clone, Debug, PartialEq)]
enum Kind {
    Mono,
}

#[derive(Clone, Debug, PartialEq)]
enum Type {
    Fun(Box<Type>, Box<Type>),
    Path(Path),
    Int,
}

#[derive(Clone, Debug, PartialEq)]
enum Expr {
    Abs(Ident, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Path(Path),
    Int(isize),
}

#[derive(Clone, Debug, PartialEq)]
struct Path(Box<Module>);

#[derive(Clone, Debug, PartialEq)]
enum Module {
    Ident(Ident),
    Seq(Vec<Binding>),
    Proj(Box<Module>, Ident),
    Fun(Ident, Sig, Box<Module>),
    App(Ident, Ident),
    Seal(Ident, Sig),
}

#[derive(Clone, Debug, PartialEq)]
enum Binding {
    Val(Ident, Expr),
    Type(Ident, Type),
    Module(Ident, Module),
    Signature(Ident, Sig),
    Include(Module),
}

#[derive(Clone, Debug, PartialEq)]
enum Sig {
    Path(Path),
    Seq(Vec<Decl>),
    Fun(Ident, Box<Sig>, Box<Sig>),
    Where(Box<Sig>, Proj<Ident>, Type),
}

#[derive(Clone, Debug, PartialEq)]
struct Proj<T>(T, Vec<T>);

#[derive(Clone, Debug, PartialEq)]
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

enum SemanticTerm {
    Term(ITerm),
    Type(IType, IKind),
    Sig(AbstractSig),
}

type Env = internal::Env<SemanticSig, Option<StemFrom>>;

#[derive(Debug, Fail, PartialEq)]
enum TypeError {
    #[fail(display = "type-checking {:?}: unification: {}", _0, _1)]
    Unification(Expr, internal::UnificationError),

    #[fail(display = "defining type {:?}: {}", _0, _1)]
    TypeBinding(Ident, Box<TypeError>),

    #[fail(display = "environment error: {}", _0)]
    Env(EnvError),

    #[fail(display = "internal kind error: {}", _0)]
    KindError(internal::KindError),

    #[fail(display = "not mono kind: {}", _0)]
    NotMono(internal::NotMonoError),

    #[fail(display = "type {:?} is not well-kinded: {}", _0, _1)]
    IllKinded(Type, internal::NotMonoError),

    #[fail(display = "{}", _0)]
    Atomic(AtomicError),
}

impl From<EnvError> for TypeError {
    fn from(e: EnvError) -> Self {
        TypeError::Env(e)
    }
}

impl From<AtomicError> for TypeError {
    fn from(e: AtomicError) -> Self {
        TypeError::Atomic(e)
    }
}

impl From<Name> for Ident {
    fn from(name: Name) -> Self {
        Ident(name)
    }
}

impl<'a> From<&'a str> for Ident {
    fn from(s: &str) -> Self {
        Ident::from(Name::from(s))
    }
}

impl From<String> for Ident {
    fn from(s: String) -> Self {
        Ident::from(Name::from(s))
    }
}

impl From<Module> for Path {
    fn from(m: Module) -> Self {
        Path(Box::new(m))
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

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error>;
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

    fn elaborate(&self, _: &mut Env) -> Result<Self::Output, Self::Error> {
        match *self {
            Kind::Mono => Ok(IKind::Mono),
        }
    }
}

impl Elaboration for Type {
    type Output = (IType, IKind);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Type::*;
        match *self {
            Int => Ok((IType::Int, IKind::Mono)),
            Fun(ref ty1, ref ty2) => {
                let (ty11, k1) = ty1.elaborate(env)?;
                k1.mono()
                    .map_err(|e| TypeError::IllKinded(*ty1.clone(), e))?;
                let (ty21, k2) = ty2.elaborate(env)?;
                k2.mono()
                    .map_err(|e| TypeError::IllKinded(*ty2.clone(), e))?;
                Ok((IType::fun(ty11, ty21), IKind::Mono))
            }
            Path(ref p) => {
                let (_, ssig) = p.elaborate(env)?;
                let (ty, k) = ssig.get_atomic_type()?;
                Ok((ty, k))
            }
        }
    }
}

impl Elaboration for Expr {
    type Output = (ITerm, IType);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        let (t, ty, _) = self.infer(env)?;
        Ok((t, ty))
    }
}

impl Elaboration for Binding {
    type Output = (ITerm, Existential<HashMap<Label, SemanticSig>>);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Binding::*;
        use SemanticSig::*;
        match *self {
            Val(ref id, ref e) => {
                let (t, ty) = e.elaborate(env)?;
                Ok((
                    ITerm::Record(Record::from_iter(vec![(
                        Label::from(id.clone()),
                        SemanticTerm::Term(t).into(),
                    )])),
                    Existential::from(HashMap::from_iter(vec![(
                        Label::from(id.clone()),
                        AtomicTerm(ty),
                    )])),
                ))
            }
            Type(ref id, ref ty) => {
                let (ty, k) = ty
                    .elaborate(env)
                    .map_err(|e| TypeError::TypeBinding(id.clone(), Box::new(e)))?;
                Ok((
                    ITerm::Record(Record::from_iter(vec![(
                        Label::from(id.clone()),
                        SemanticTerm::Type(ty.clone(), k.clone()).into(),
                    )])),
                    Existential::from(HashMap::from_iter(vec![(
                        Label::from(id.clone()),
                        AtomicType(ty, k),
                    )])),
                ))
            }
            _ => unimplemented!(),
        }
    }
}

impl Elaboration for Module {
    type Output = (ITerm, AbstractSig);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Module::*;
        match *self {
            Ident(ref id) => {
                let (ssig, v) = env.lookup_value_by_name(id.into())?;
                Ok((ITerm::Var(v), Existential::from(ssig)))
            }
            _ => unimplemented!(),
        }
    }
}

impl Elaboration for Path {
    type Output = (ITerm, SemanticSig);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        let (t, asig) = self.0.elaborate(env)?;
        // Need shift?
        IType::from(asig.0.body.clone())
            .kind_of(env)
            .map_err(TypeError::KindError)?
            .mono()
            .map_err(TypeError::NotMono)?;
        Ok((
            ITerm::unpack(t, asig.0.qs.len(), asig.clone().into(), ITerm::var(0)),
            asig.0.body,
        ))
    }
}

impl<T> From<T> for Existential<T> {
    fn from(x: T) -> Self {
        Existential(Quantified {
            qs: vec![],
            body: x,
        })
    }
}

impl Expr {
    fn abs(id: Ident, e: Expr) -> Self {
        Expr::Abs(id, Box::new(e))
    }

    fn app(e1: Expr, e2: Expr) -> Self {
        Expr::App(Box::new(e1), Box::new(e2))
    }

    fn path(m: Module) -> Self {
        Expr::Path(Path::from(m))
    }

    fn infer(&self, env: &mut Env) -> Result<(ITerm, IType, Subst), TypeError> {
        use Expr::*;
        use IKind::*;
        match *self {
            Abs(ref id, ref e) => {
                let v = env.fresh_type_variable(Mono, None);
                let mut ty0 = IType::Var(v);
                let name = Name::from(id.clone());
                let prev = env.insert_value(name.clone(), SemanticSig::AtomicTerm(ty0.clone()));
                let (t, ty, s) = e.infer(env)?;
                env.drop_value(name, prev);
                ty0.apply(&s);
                Ok((ITerm::abs(ty0.clone(), t), IType::fun(ty0, ty), s))
            }
            App(ref e1, ref e2) => {
                let (mut t1, mut ty1, s1) = e1.infer(env)?;
                let (t2, ty2, s2) = e2.infer(env)?;
                t1.apply(&s2);
                ty1.apply(&s2);
                let mut v = IType::Var(env.fresh_type_variable(Mono, None));
                let s3 = env
                    .unify(vec![(ty1, IType::fun(ty2, v.clone()))])
                    .map_err(|e| TypeError::Unification(self.clone(), e))?;
                t1.apply(&s3);
                v.apply(&s3);
                let s = s3.compose(s2).compose(s1);
                Ok((ITerm::app(t1, t2), v, s))
            }
            Int(n) => Ok((ITerm::Int(n), IType::Int, Subst::default())),
            Path(ref p) => {
                let (t, ssig) = p.elaborate(env)?;
                let ty = ssig.get_atomic_term()?;
                Ok((ITerm::Proj(Box::new(t), Label::Val), ty, Subst::default()))
            }
        }
    }
}

impl Type {
    fn fun(ty1: Type, ty2: Type) -> Self {
        Type::Fun(Box::new(ty1), Box::new(ty2))
    }

    fn path(m: Module) -> Self {
        Type::Path(Path::from(m))
    }
}

impl SemanticSig {
    fn atomic_sig(qs: Vec<(IKind, StemFrom)>, body: SemanticSig) -> Self {
        SemanticSig::AtomicSig(Box::new(Existential(Quantified { qs, body })))
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

    macro_rules! assert_elaborate_ok {
        ($x:expr, $r:expr) => {{
            let mut env = Env::default();
            assert_eq!($x.elaborate(&mut env), Ok($r));
        }};
    }

    macro_rules! assert_elaborate_err {
        ($x:expr, $r:expr) => {{
            let mut env = Env::default();
            assert_eq!($x.elaborate(&mut env), Err($r));
        }};
    }

    #[test]
    fn elaborate_type() {
        use IKind::*;
        use Type::*;

        assert_elaborate_ok!(Int, (IType::Int, Mono));
        assert_elaborate_ok!(
            Type::fun(Int, Int),
            (IType::fun(IType::Int, IType::Int), Mono)
        );
    }

    #[test]
    fn elaborate_expr() {
        use internal::UnificationError;
        use Expr::*;

        assert_elaborate_ok!(Int(55), (ITerm::Int(55), IType::Int));

        assert_elaborate_ok!(
            Expr::abs(Ident::from("x"), Int(55)),
            (
                ITerm::abs(IType::var(0), ITerm::Int(55)),
                IType::fun(IType::var(0), IType::Int)
            )
        );

        assert_elaborate_ok!(
            Expr::app(Expr::abs(Ident::from("x"), Int(55)), Int(98)),
            (
                ITerm::app(ITerm::abs(IType::Int, ITerm::Int(55)), ITerm::Int(98)),
                IType::Int
            )
        );

        assert_elaborate_err!(
            Expr::app(Int(45), Int(98)),
            TypeError::Unification(
                Expr::app(Int(45), Int(98)),
                UnificationError::NotUnifiable(IType::Int, IType::fun(IType::Int, IType::var(0)))
            )
        );
    }

    #[test]
    fn elaborate_binding() {
        use super::Type as T;
        use Binding::*;
        use SemanticSig::*;

        assert_elaborate_ok!(
            Val(Ident::from("x"), Expr::Int(23)),
            (
                ITerm::Record(Record::from_iter(vec![(
                    Label::from("x"),
                    ITerm::Record(Record::from_iter(vec![(Label::Val, ITerm::Int(23))]))
                )])),
                Existential::from(HashMap::from_iter(vec![(
                    Label::from("x"),
                    AtomicTerm(IType::Int)
                )]))
            )
        );

        assert_elaborate_ok!(
            Val(Ident::from("x"), Expr::abs(Ident::from("y"), Expr::Int(22))),
            (
                ITerm::Record(Record::from_iter(vec![(
                    Label::from("x"),
                    ITerm::Record(Record::from_iter(vec![(
                        Label::Val,
                        ITerm::abs(IType::var(0), ITerm::Int(22))
                    )]))
                )])),
                Existential::from(HashMap::from_iter(vec![(
                    Label::from("x"),
                    AtomicTerm(IType::fun(IType::var(0), IType::Int))
                )]))
            )
        );

        assert_elaborate_ok!(
            Type(Ident::from("t"), T::Int),
            (
                ITerm::Record(Record::from_iter(vec![(
                    Label::from("t"),
                    ITerm::Record(Record::from_iter(vec![(
                        Label::Typ,
                        ITerm::poly(
                            vec![IKind::fun(IKind::Mono, IKind::Mono)],
                            ITerm::abs(IType::app(IType::var(0), IType::Int), ITerm::var(0))
                        )
                    )]))
                )])),
                Existential::from(HashMap::from_iter(vec![(
                    Label::from("t"),
                    AtomicType(IType::Int, IKind::Mono)
                )]))
            )
        );

        assert_elaborate_ok!(
            Type(Ident::from("t"), T::fun(T::Int, T::Int)),
            (
                ITerm::Record(Record::from_iter(vec![(
                    Label::from("t"),
                    ITerm::Record(Record::from_iter(vec![(
                        Label::Typ,
                        ITerm::poly(
                            vec![IKind::fun(IKind::Mono, IKind::Mono)],
                            ITerm::abs(
                                IType::app(IType::var(0), IType::fun(IType::Int, IType::Int)),
                                ITerm::var(0)
                            )
                        )
                    )]))
                )])),
                Existential::from(HashMap::from_iter(vec![(
                    Label::from("t"),
                    AtomicType(IType::fun(IType::Int, IType::Int), IKind::Mono)
                )]))
            )
        );
    }
}

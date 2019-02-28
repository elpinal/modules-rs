//! Andreas Rossberg, Claudio V. Russo and Derek Dreyer.
//! F-ing modules.
//! Journal of Functional Programming, 24(5), 2014.

#![allow(dead_code)]

pub mod internal;
pub mod parser;

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::convert::TryFrom;
use std::iter::FromIterator;

use failure::Fail;

use internal::EnvAbs;
use internal::EnvError;
use internal::Fgtv;
use internal::Kind as IKind;
use internal::Shift;
use internal::Term as ITerm;
use internal::Type as IType;
use internal::{Label, Name};
use internal::{Subst, Substitution};

#[derive(Clone, Debug, PartialEq)]
pub struct Ident(Name);

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    Mono,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Fun(Box<Type>, Box<Type>),
    Path(Path),

    /// A package type.
    Pack(Box<Sig>),

    Int,
    Bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Abs(Ident, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Path(Path),
    Pack(Box<Module>, Sig),
    Int(isize),
    Bool(bool),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum BinOp {
    LessThan,
    GreaterThan,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Path(Box<Module>);

#[derive(Clone, Debug, PartialEq)]
pub enum Module {
    Ident(Ident),
    Seq(Vec<Binding>),
    Proj(Box<Module>, Ident),
    Fun(Ident, Sig, Box<Module>),
    App(Ident, Ident),
    Seal(Ident, Sig),
    Unpack(Box<Expr>, Sig),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Binding {
    Val(Ident, Expr),
    Type(Ident, Type),
    Module(Ident, Module),
    Signature(Ident, Sig),
    Include(Module),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Sig {
    Path(Path),
    Seq(Vec<Decl>),
    Generative(Ident, Box<Sig>, Box<Sig>),
    Applicative(Ident, Box<Sig>, Box<Sig>),
    Where(Box<Sig>, Proj<Ident>, Type),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Proj<T>(T, Vec<T>);

#[derive(Clone, Debug, PartialEq)]
pub enum Decl {
    Val(Ident, Type),
    ManType(Ident, Type),
    AbsType(Ident, Kind),
    Module(Ident, Sig),
    Signature(Ident, Sig),
    Include(Sig),
}

/// Just for error messages, i.e., irrelevant to the essential algorithm.
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
pub struct Existential<T>(Quantified<T>);

#[derive(Clone, Debug, PartialEq)]
pub struct Universal<T>(Quantified<T>);

pub type AbstractSig = Existential<SemanticSig>;

#[derive(Clone, Debug, PartialEq)]
pub struct Fun(SemanticSig, AbstractSig);

#[derive(Clone, Debug, PartialEq)]
pub struct Applicative(SemanticSig, SemanticSig);

#[derive(Clone, Debug, PartialEq)]
pub enum SemanticSig {
    AtomicTerm(SemanticPath, IType),
    AtomicType(IType, IKind),
    AtomicSig(Box<AbstractSig>),
    StructureSig(HashMap<Label, SemanticSig>),
    FunctorSig(Universal<Box<Fun>>),
    Applicative(Universal<Box<Applicative>>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct SemanticPath {
    v: internal::Variable,
    tys: Vec<IType>,
}

enum SemanticTerm {
    Term(ITerm),
    Type(IType, IKind),
    Sig(AbstractSig),
}

struct BindingInformation {
    t: ITerm,
    n: usize,
    w: Vec<ITerm>,
}

type Memory<T, S> = Vec<(EnvAbs<T, S>, Purity, Vec<Label>, usize, usize, usize)>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Purity {
    Pure,
    Impure,
}

type Env = internal::Env<SemanticSig, Option<StemFrom>>;

#[derive(Debug, Fail, PartialEq)]
pub enum TypeError {
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
    SemanticSigError(SemanticSigError),

    #[fail(display = "duplicate label: {:?}", _0)]
    DuplicateLabel(Label),

    #[fail(display = "{:?} is not subtype of {:?}", _0, _1)]
    NotSubtype(IType, IType),

    #[fail(display = "type mismatch: {:?} {:?}", _0, _1)]
    TypeMismatch(IType, IType),

    #[fail(display = "missing label: {:?}", _0)]
    MissingLabel(Label),

    #[fail(display = "{:?} is not sub-signature of {:?}", _0, _1)]
    NotSubsignature(SemanticSig, SemanticSig),

    #[fail(display = "not local abstract type: {:?}", _0)]
    NotLocalAbstractType(internal::Variable),

    #[fail(display = "not abstract type: {:?}", _0)]
    NotAbstractType(IType),

    #[fail(display = "value identity mismatch: {:?} and {:?}", _0, _1)]
    SemanticPathMismatch(SemanticPath, SemanticPath),
}

impl From<EnvError> for TypeError {
    fn from(e: EnvError) -> Self {
        TypeError::Env(e)
    }
}

impl From<SemanticSigError> for TypeError {
    fn from(e: SemanticSigError) -> Self {
        TypeError::SemanticSigError(e)
    }
}

impl From<!> for TypeError {
    fn from(e: !) -> Self {
        e
    }
}

impl From<usize> for SemanticPath {
    fn from(n: usize) -> Self {
        SemanticPath {
            v: internal::Variable::new(n),
            tys: Vec::new(),
        }
    }
}

impl From<internal::Variable> for SemanticPath {
    fn from(v: internal::Variable) -> Self {
        SemanticPath { v, tys: Vec::new() }
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

impl From<Ident> for StemFrom {
    fn from(id: Ident) -> Self {
        StemFrom {
            id,
            prefix: Default::default(),
        }
    }
}

impl<'a> From<&'a Ident> for StemFrom {
    fn from(id: &'a Ident) -> Self {
        StemFrom {
            id: id.clone(),
            prefix: Default::default(),
        }
    }
}

impl From<SemanticPath> for IType {
    fn from(sp: SemanticPath) -> Self {
        sp.tys.into_iter().fold(IType::Var(sp.v), IType::app)
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

impl Substitution for Applicative {
    fn apply(&mut self, s: &Subst) {
        self.0.apply(s);
        self.1.apply(s);
    }
}

impl Substitution for SemanticPath {
    fn apply(&mut self, s: &Subst) {
        // TODO: How about `self.v`?
        self.tys.iter_mut().for_each(|ty| ty.apply(s));
    }
}

impl Substitution for SemanticSig {
    fn apply(&mut self, s: &Subst) {
        use SemanticSig::*;

        match *self {
            AtomicTerm(ref mut sp, ref mut ty) => {
                sp.apply(s);
                ty.apply(s);
            }
            AtomicType(ref mut ty, ref mut k) => {
                k.apply(s);
                ty.apply(s);
            }
            AtomicSig(ref mut asig) => asig.apply(s),
            StructureSig(ref mut m) => m.values_mut().for_each(|ssig| ssig.apply(s)),
            FunctorSig(ref mut u) => u.apply(s),
            Applicative(ref mut u) => u.apply(s),
        }
    }
}

impl<T: Substitution> Substitution for Box<T> {
    fn apply(&mut self, s: &Subst) {
        (**self).apply(s);
    }
}

impl Substitution for BindingInformation {
    fn apply(&mut self, s: &Subst) {
        // This is not verified to be correct.
        self.t.apply(s);
        self.w.apply(s);
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

impl Shift for Applicative {
    fn shift_above(&mut self, c: usize, d: isize) {
        self.0.shift_above(c, d);
        self.1.shift_above(c, d);
    }
}

impl Shift for SemanticPath {
    fn shift_above(&mut self, c: usize, d: isize) {
        self.v.shift_above(c, d);
        self.tys.iter_mut().for_each(|ty| ty.shift_above(c, d));
    }
}

impl Shift for SemanticSig {
    fn shift_above(&mut self, c: usize, d: isize) {
        use SemanticSig::*;
        match *self {
            AtomicTerm(ref mut sp, ref mut ty) => {
                sp.shift_above(c, d);
                ty.shift_above(c, d);
            }
            AtomicType(ref mut ty, ref mut k) => {
                ty.shift_above(c, d);
                k.shift_above(c, d);
            }
            AtomicSig(ref mut asig) => asig.shift_above(c, d),
            StructureSig(ref mut m) => m.values_mut().for_each(|ssig| ssig.shift_above(c, d)),
            FunctorSig(ref mut u) => u.shift_above(c, d),
            Applicative(ref mut u) => u.shift_above(c, d),
        }
    }
}

impl<T: Fgtv> Fgtv for Box<T> {
    fn fgtv(&self) -> HashSet<usize> {
        (**self).fgtv()
    }
}

impl<T: Fgtv> Fgtv for Quantified<T> {
    fn fgtv(&self) -> HashSet<usize> {
        self.body.fgtv()
    }
}

impl<T: Fgtv> Fgtv for Existential<T> {
    fn fgtv(&self) -> HashSet<usize> {
        self.0.fgtv()
    }
}

impl<T: Fgtv> Fgtv for Universal<T> {
    fn fgtv(&self) -> HashSet<usize> {
        self.0.fgtv()
    }
}

impl Fgtv for Fun {
    fn fgtv(&self) -> HashSet<usize> {
        let mut s = self.0.fgtv();
        s.extend(self.1.fgtv());
        s
    }
}

impl Fgtv for Applicative {
    fn fgtv(&self) -> HashSet<usize> {
        let mut s = self.0.fgtv();
        s.extend(self.1.fgtv());
        s
    }
}

impl Fgtv for SemanticPath {
    fn fgtv(&self) -> HashSet<usize> {
        let mut s = self.v.fgtv();
        s.extend(self.tys.iter().flat_map(|ty| ty.fgtv()));
        s
    }
}

impl Fgtv for SemanticSig {
    fn fgtv(&self) -> HashSet<usize> {
        use SemanticSig::*;
        match *self {
            AtomicTerm(ref sp, ref ty) => {
                let mut s = sp.fgtv();
                s.extend(ty.fgtv());
                s
            }
            AtomicType(ref ty, ref k) => {
                let mut s = ty.fgtv();
                s.extend(k.fgtv());
                s
            }
            AtomicSig(ref asig) => asig.fgtv(),
            StructureSig(ref m) => m.values().flat_map(|ssig| ssig.fgtv()).collect(),
            FunctorSig(ref u) => u.fgtv(),
            Applicative(ref u) => u.fgtv(),
        }
    }
}

trait Elaboration {
    type Output;
    type Error;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error>;
}

pub fn elaborate(m: Module) -> Result<(ITerm, AbstractSig, Vec<IKind>), TypeError> {
    let mut env = Env::default();
    let triple = m.elaborate(&mut env)?;
    Ok((triple.0, triple.1, env.get_generated_type_env()))
}

trait Subtype<RHS = Self> {
    type Error;

    fn subtype_of(&self, env: &mut Env, another: &RHS) -> Result<ITerm, Self::Error>;
}

trait Normalize {
    fn normalize(self) -> Self;
}

trait Lift<RHS = Self> {
    fn lifted_by(self, another: &RHS) -> Self;
}

trait Pureness {
    fn is_pure(&self) -> bool;
}

#[derive(Debug, Fail, PartialEq)]
pub enum SemanticSigError {
    #[fail(display = "unexpected atomic semantic signature: {:?}", _0)]
    Atomic(SemanticSig),

    #[fail(display = "not atomic term: {:?}", _0)]
    AtomicTerm(SemanticSig),

    #[fail(display = "not atomic type: {:?}", _0)]
    AtomicType(SemanticSig),

    #[fail(display = "not atomic signature: {:?}", _0)]
    AtomicSig(SemanticSig),

    #[fail(display = "not structure signature: {:?}", _0)]
    Structure(SemanticSig),

    #[fail(display = "not functor signature: {:?}", _0)]
    Functor(SemanticSig),
}

impl SemanticSig {
    fn structure_sig<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (Label, SemanticSig)>,
    {
        SemanticSig::StructureSig(HashMap::from_iter(iter))
    }

    fn atomic(&self) -> Result<(), SemanticSigError> {
        use SemanticSig::*;
        match *self {
            AtomicTerm(..) | AtomicType(..) | AtomicSig(..) => {
                Err(SemanticSigError::Atomic(self.clone()))
            }
            _ => Ok(()),
        }
    }

    fn get_atomic_term(self) -> Result<(SemanticPath, IType), SemanticSigError> {
        match self {
            SemanticSig::AtomicTerm(sp, ty) => Ok((sp, ty)),
            _ => Err(SemanticSigError::AtomicTerm(self)),
        }
    }

    fn get_atomic_type(self) -> Result<(IType, IKind), SemanticSigError> {
        match self {
            SemanticSig::AtomicType(ty, k) => Ok((ty, k)),
            _ => Err(SemanticSigError::AtomicType(self)),
        }
    }

    fn get_atomic_sig(self) -> Result<AbstractSig, SemanticSigError> {
        match self {
            SemanticSig::AtomicSig(asig) => Ok(*asig),
            _ => Err(SemanticSigError::AtomicSig(self)),
        }
    }

    fn get_structure(self) -> Result<HashMap<Label, SemanticSig>, SemanticSigError> {
        match self {
            SemanticSig::StructureSig(m) => Ok(m),
            _ => Err(SemanticSigError::Structure(self)),
        }
    }

    fn get_functor(self) -> Result<Universal<Fun>, SemanticSigError> {
        match self {
            SemanticSig::FunctorSig(u) => Ok(u.map(|f| *f)),
            _ => Err(SemanticSigError::Functor(self)),
        }
    }
}

impl Lift for Vec<(IKind, StemFrom)> {
    fn lifted_by(self, another: &Self) -> Self {
        self.into_iter()
            .map(|(k, sf)| {
                (
                    another
                        .iter()
                        .fold(k, |acc, p| IKind::fun(p.0.clone(), acc)),
                    sf,
                )
            })
            .collect()
    }
}

impl Lift<Env> for Vec<(IKind, StemFrom)> {
    fn lifted_by(self, another: &Env) -> Self {
        self.into_iter()
            .map(|(k, sf)| (IKind::fun_env(another, k), sf))
            .collect()
    }
}

impl Pureness for Expr {
    fn is_pure(&self) -> bool {
        use Expr::*;
        match *self {
            Path(ref p) => p.is_pure(),
            Pack(ref m, _) => m.is_pure(),
            // In this implementation, the core language is purely functional.
            _ => true,
        }
    }
}

impl Pureness for Path {
    fn is_pure(&self) -> bool {
        self.0.is_pure()
    }
}

impl Pureness for Module {
    fn is_pure(&self) -> bool {
        use Module::*;
        match *self {
            App(..) | Unpack(..) => false,
            Seq(ref bs) => bs.iter().all(|b| b.is_pure()),
            Proj(ref m, _) => m.is_pure(),
            _ => true,
        }
    }
}

impl Pureness for Binding {
    fn is_pure(&self) -> bool {
        use Binding::*;
        match *self {
            Val(_, ref e) => e.is_pure(),
            Module(_, ref m) | Include(ref m) => m.is_pure(),
            _ => true,
        }
    }
}

impl Elaboration for Kind {
    type Output = IKind;
    type Error = !;

    fn elaborate(&self, _: &mut Env) -> Result<Self::Output, Self::Error> {
        match *self {
            Kind::Mono => Ok(IKind::Mono),
        }
    }
}

impl Elaboration for Type {
    type Output = (IType, IKind, Subst);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Type::*;
        match *self {
            Int => Ok((IType::Int, IKind::Mono, Subst::default())),
            Bool => Ok((IType::Bool, IKind::Mono, Subst::default())),
            Fun(ref ty1, ref ty2) => {
                let (ty11, k1, s1) = ty1.elaborate(env)?;
                k1.mono()
                    .map_err(|e| TypeError::IllKinded(*ty1.clone(), e))?;
                let (ty21, k2, s2) = ty2.elaborate(env)?;
                k2.mono()
                    .map_err(|e| TypeError::IllKinded(*ty2.clone(), e))?;
                Ok((IType::fun(ty11, ty21), IKind::Mono, s1.compose(s2)))
            }
            Path(ref p) => {
                let (_, ssig, s) = p.elaborate(env)?;
                let (ty, k) = ssig.get_atomic_type()?;
                Ok((ty, k, s))
            }
            Pack(ref sig) => {
                let (asig, s) = sig.elaborate(env)?;
                Ok((IType::from(asig.normalize()), IKind::Mono, s))
            }
        }
    }
}

impl Elaboration for Expr {
    type Output = (ITerm, IType, Subst);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        self.infer(env)
    }
}

impl Elaboration for Decl {
    type Output = (Existential<HashMap<Label, SemanticSig>>, Subst);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Decl::*;
        use SemanticSig::*;
        let f = |id: &Ident, ssig: SemanticSig| {
            Existential::from(HashMap::from_iter(Some((Label::from(id), ssig))))
        };
        match *self {
            Val(ref id, ref ty) => {
                let (ty, k, s) = ty.elaborate(env)?;
                k.mono().map_err(TypeError::NotMono)?;
                Ok((
                    Existential(Quantified {
                        qs: vec![(IKind::Mono, id.into())],
                        body: HashMap::from_iter(Some((
                            id.into(),
                            AtomicTerm(SemanticPath::from(0), ty),
                        ))),
                    }),
                    s,
                ))
            }
            ManType(ref id, ref ty) => {
                let (ty, k, s) = ty.elaborate(env)?;
                Ok((f(id, AtomicType(ty, k)), s))
            }
            AbsType(ref id, ref k) => {
                let k = k.elaborate(env)?;
                Ok((
                    Existential(Quantified {
                        qs: vec![(k.clone(), id.into())],
                        body: HashMap::from_iter(Some((
                            Label::from(id),
                            AtomicType(IType::var(0), k),
                        ))),
                    }),
                    Subst::default(),
                ))
            }
            Module(ref id, ref sig) => {
                let (asig, s) = sig.elaborate(env)?;
                Ok((
                    asig.map(|ssig| HashMap::from_iter(Some((Label::from(id), ssig)))),
                    s,
                ))
            }
            Signature(ref id, ref sig) => {
                let (asig, s) = sig.elaborate(env)?;
                Ok((f(id, AtomicSig(Box::new(asig))), s))
            }
            Include(ref sig) => {
                let (asig, s) = sig.elaborate(env)?;
                Ok((
                    asig.try_map::<_, _, TypeError, _>(|ssig| ssig.get_structure())?,
                    s,
                ))
            }
        }
    }
}

impl Elaboration for Sig {
    type Output = (AbstractSig, Subst);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Sig::*;
        match *self {
            Path(ref p) => {
                let (_, ssig, s) = p.elaborate(env)?;
                Ok((ssig.get_atomic_sig()?, s))
            }
            Seq(ref ds) => {
                let enter_state = env.get_state();
                let (ex, s) = ds.iter().try_fold(
                    (Existential::from(HashMap::new()), Subst::default()),
                    |(acc, subst), d| -> Result<_, TypeError> {
                        let (ex, s) = d.elaborate(env)?;
                        env.insert_types(ex.0.qs.clone().into_iter().map(|(k, s)| (k, Some(s))));
                        for (l, ssig) in ex.0.body.iter() {
                            env.insert_value(Name::try_from(l.clone()).unwrap(), ssig.clone());
                        }
                        Ok((acc.merge(ex)?, subst.compose(s)))
                    },
                )?;
                env.drop_values_state(ex.0.body.len(), enter_state);
                env.drop_types(ex.0.qs.len());
                Ok((ex.map(SemanticSig::StructureSig), s))
            }
            Generative(ref id, ref domain, ref range) => {
                let enter_state = env.get_state();
                let (asig1, s1) = domain.elaborate(env)?;
                env.insert_types(asig1.0.qs.clone().into_iter().map(|(k, s)| (k, Some(s))));
                env.insert_value(Name::from(id.clone()), asig1.0.body.clone());
                let (asig2, s2) = range.elaborate(env)?;
                env.drop_values_state(1, enter_state);
                env.drop_types(asig1.0.qs.len());
                Ok((
                    Existential::from(SemanticSig::FunctorSig(
                        Universal::from(asig1).map(|ssig| Box::new(Fun(ssig, asig2))),
                    )),
                    s1.compose(s2),
                ))
            }
            Applicative(ref id, ref domain, ref range) => {
                let enter_state = env.get_state();
                let (mut asig1, s1) = domain.elaborate(env)?;
                env.insert_types(asig1.0.qs.clone().into_iter().map(|(k, s)| (k, Some(s))));
                env.insert_value(Name::from(id.clone()), asig1.0.body.clone());
                let (asig2, s2) = range.elaborate(env)?;
                env.drop_values_state(1, enter_state);
                env.drop_types(asig1.0.qs.len());
                let mut ssig2 = asig2.0.body;
                let len2 = asig2.0.qs.len();
                let qs = asig2.0.qs.lifted_by(&asig1.0.qs);
                asig1.shift(isize::try_from(len2).unwrap());
                ssig2.skolemize(asig1.0.qs.len(), len2);
                Ok((
                    Existential(Quantified {
                        qs,
                        body: SemanticSig::Applicative(
                            Universal::from(asig1)
                                .map(|ssig1| Box::new(self::Applicative(ssig1, ssig2))),
                        ),
                    }),
                    s1.compose(s2),
                ))
            }
            Where(ref sig, ref p, ref ty) => {
                let (asig, s1) = sig.elaborate(env)?;
                let (mut ty, k1, s2) = ty.elaborate(env)?;
                // TODO: `asig.apply(&s2)`?
                let (ty0, k2) = asig.0.body.proj_multi(p)?.clone().get_atomic_type()?;
                match ty0 {
                    IType::Var(v) if v.get_index() >= asig.0.qs.len() => {
                        Err(TypeError::NotLocalAbstractType(v))
                    }
                    IType::Var(v) if k1.equal(&k2) => {
                        let mut qs = asig.0.qs;
                        ty.shift(isize::try_from(qs.len()).unwrap());
                        qs.remove(qs.len() - v.get_index() - 1);
                        let mut body = asig.0.body;
                        body.apply(&Subst::from_iter(Some((v, ty))));
                        body.shift_above(v.get_index(), -1);
                        Ok((Existential(Quantified { qs, body }), s1.compose(s2)))
                    }
                    IType::Var(_) => Err(TypeError::KindError(internal::KindError::KindMismatch(
                        k1.clone(),
                        k2.clone(),
                    ))),
                    _ => Err(TypeError::NotAbstractType(ty0)),
                }
            }
        }
    }
}

impl Elaboration for Binding {
    type Output = (
        ITerm,
        Existential<HashMap<Label, SemanticSig>>,
        Subst,
        Purity,
    );
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Binding::*;
        use Purity::*;
        use SemanticSig::*;
        match *self {
            Val(ref id, ref e) => {
                // TODO: Which generalization strategy should be taken?
                match *e {
                    Expr::Path(ref p) => {
                        let (t, asig, s, p) = p.0.elaborate(env)?;
                        let (sp, ty) = asig.0.body.get_atomic_term()?;
                        return Ok((
                            ITerm::unpack(
                                t,
                                asig.0.qs.len(),
                                ITerm::pack(
                                    ITerm::abs_env_purity(
                                        &*env,
                                        p,
                                        ITerm::record(Some((
                                            id.into(),
                                            ITerm::var(env.tenv_len()),
                                        ))),
                                    ),
                                    (0..asig.0.qs.len()).map(IType::var).collect(),
                                    asig.0.qs.iter().map(|p| p.0.clone()),
                                    IType::forall_env_purity(
                                        env,
                                        p,
                                        IType::record(Some((
                                            id.into(),
                                            AtomicTerm(sp.clone(), ty.clone()).into(),
                                        ))),
                                    ),
                                ),
                            ),
                            Existential(Quantified {
                                qs: asig.0.qs,
                                body: HashMap::from_iter(Some((id.into(), AtomicTerm(sp, ty)))),
                            }),
                            s,
                            p,
                        ));
                    }
                    _ if e.is_pure() => {
                        let (t, ty, s) = e.elaborate(env)?;
                        return Ok((
                            ITerm::pack(
                                ITerm::abs_env(
                                    &*env,
                                    ITerm::record(Some((
                                        id.into(),
                                        ITerm::from(SemanticTerm::Term(t)),
                                    ))),
                                ),
                                vec![IType::abs_env(&*env, IType::record(None))],
                                Some(IKind::fun_env(&*env, IKind::Mono)),
                                IType::forall_env(
                                    env,
                                    IType::record(Some((
                                        id.into(),
                                        IType::from(AtomicTerm(
                                            SemanticPath {
                                                v: internal::Variable::new(0),
                                                tys: (0..env.tenv_len())
                                                    .rev()
                                                    .map(|n| IType::var(n + 1))
                                                    .collect(),
                                            },
                                            ty.clone(),
                                        )),
                                    ))),
                                ),
                            ),
                            Existential(Quantified {
                                qs: vec![(IKind::fun_env(env, IKind::Mono), id.into())],
                                body: HashMap::from_iter(Some((
                                    id.into(),
                                    AtomicTerm(
                                        SemanticPath {
                                            v: internal::Variable::new(0),
                                            tys: (0..env.tenv_len())
                                                .rev()
                                                .map(|n| IType::var(n + 1))
                                                .collect(),
                                        },
                                        ty,
                                    ),
                                ))),
                            }),
                            s,
                            Pure,
                        ));
                    }
                    _ => (),
                }
                let (t, ty, s) = e.elaborate(env)?;
                let (scheme, s1, ks) = ty.close(env);
                let mut t = ITerm::from(SemanticTerm::Term(t));
                t.shift(isize::try_from(ks.len()).unwrap());
                t.apply(&s1);
                Ok((
                    // ITerm::abs_env(
                    //     env,
                    //     ITerm::record(vec![(Label::from(id), ITerm::poly(ks, t))]),
                    // ),
                    ITerm::pack(
                        ITerm::record(Some((
                            id.into(),
                            ITerm::poly(ks, ITerm::from(SemanticTerm::Term(t))),
                        ))),
                        vec![IType::record(None)],
                        Some(IKind::Mono),
                        IType::record(Some((
                            id.into(),
                            IType::from(AtomicTerm(SemanticPath::from(0), scheme.clone())),
                        ))),
                    ),
                    Existential(Quantified {
                        qs: vec![(IKind::Mono, id.into())],
                        body: HashMap::from_iter(Some((
                            id.into(),
                            AtomicTerm(SemanticPath::from(0), scheme),
                        ))),
                    }),
                    s,
                    Impure,
                ))
            }
            Type(ref id, ref ty) => {
                let (ty, k, s) = ty
                    .elaborate(env)
                    .map_err(|e| TypeError::TypeBinding(id.clone(), Box::new(e)))?;
                Ok((
                    ITerm::abs_env(
                        env,
                        ITerm::record(vec![(
                            Label::from(id.clone()),
                            SemanticTerm::Type(ty.clone(), k.clone()).into(),
                        )]),
                    ),
                    Existential::from(HashMap::from_iter(vec![(
                        Label::from(id.clone()),
                        AtomicType(ty, k),
                    )])),
                    s,
                    Pure,
                ))
            }
            Module(ref id, ref m) => {
                let (t, asig, s, p) = m.elaborate(env)?;
                asig.0.body.atomic()?;
                Ok((
                    ITerm::unpack(
                        t,
                        asig.0.qs.len(),
                        ITerm::pack(
                            ITerm::abs_env_purity(
                                &*env,
                                p,
                                ITerm::record(vec![(
                                    Label::from(id),
                                    ITerm::app_env_purity(ITerm::var(0), &*env, p),
                                )]),
                            ),
                            (0..asig.0.qs.len()).map(IType::var).collect(),
                            asig.0.qs.iter().map(|p| p.0.clone()),
                            StructureSig(HashMap::from_iter(Some((
                                Label::from(id.clone()),
                                asig.0.body.clone(),
                            ))))
                            .into(),
                        ),
                    ),
                    asig.map(|ssig| HashMap::from_iter(vec![(Label::from(id.clone()), ssig)])),
                    s,
                    p,
                ))
            }
            Signature(ref id, ref sig) => {
                let (asig, s) = sig.elaborate(env)?;
                Ok((
                    ITerm::abs_env(
                        env,
                        ITerm::record(Some((
                            Label::from(id),
                            SemanticTerm::Sig(asig.clone()).into(),
                        ))),
                    ),
                    Existential::from(HashMap::from_iter(Some((
                        Label::from(id),
                        SemanticSig::AtomicSig(Box::new(asig)),
                    )))),
                    s,
                    Pure,
                ))
            }
            Include(ref m) => {
                let (t, asig, s, p) = m.elaborate(env)?;
                let ex = asig.try_map::<_, _, TypeError, _>(|ssig| ssig.get_structure())?;
                Ok((t, ex, s, p))
            }
        }
    }
}

impl Elaboration for Module {
    type Output = (ITerm, AbstractSig, Subst, Purity);
    type Error = TypeError;

    #[allow(clippy::many_single_char_names)]
    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Module::*;
        use Purity::*;
        match *self {
            Ident(ref id) => {
                let (ssig, v) = env.lookup_value_by_name(id.into())?;
                Ok((
                    ITerm::abs_env(env, ITerm::Var(v)),
                    Existential::from(ssig),
                    Subst::default(),
                    Pure,
                ))
            }
            Seq(ref bs) => {
                use internal::Variable::Variable as V;
                let mut v = Vec::new();
                let mut ls = HashMap::new();
                let mut qs = Vec::new();
                let mut body = HashMap::new();
                let mut ret_subst = Subst::default();
                let mut n = 0;
                let mut z = 0;
                let mut d = 0;
                let mut memory: Memory<_, _> = Vec::new();
                let mut qs_count = 0;
                let enter_state = env.get_state();
                for (i, b) in bs.iter().enumerate() {
                    let (t, ex, s, p) = b.elaborate(env)?;
                    let len = ex.0.qs.len();
                    let z0 = z;
                    z += if len == 0 { 1 } else { len };
                    memory.push((
                        EnvAbs::from(&*env),
                        p,
                        ex.0.body.keys().cloned().collect(),
                        z,
                        qs_count,
                        d,
                    ));
                    qs_count += len;
                    n += if len == 0 { 1 } else { len };
                    let n0 = n;
                    ret_subst = ret_subst.compose(s.clone());
                    body.apply(&s);
                    v.apply(&s);
                    env.insert_types(ex.0.qs.clone().into_iter().map(|(k, s)| (k, Some(s))));
                    env.insert_dummy_values_at(V(d), if len == 0 { 1 } else { len });
                    qs.extend(ex.0.qs.clone());
                    body.shift(isize::try_from(len).unwrap());
                    body.extend(ex.0.body.clone());
                    let mut w = Vec::new();
                    for (i, (l, ssig)) in ex.0.body.into_iter().enumerate() {
                        ls.insert(l.clone(), n0);
                        // `w` might be unneeded.
                        w.push(ITerm::proj(ITerm::var(i), Some(l.clone())));
                        n += 1;
                        d += 1;
                        env.insert_value(Name::try_from(l).unwrap(), ssig);
                    }
                    let mut j = 0;
                    let t = ITerm::let_in(
                        memory[..i]
                            .iter()
                            .flat_map(|&(ref ea, p0, ref ls, i0, _, _)| {
                                ls.iter()
                                    .map(|l| {
                                        let ret = ITerm::abs_env_purity(
                                            ea.clone(),
                                            p.join(p0),
                                            ITerm::proj(
                                                ITerm::app_env_purity_skip(
                                                    ITerm::var(
                                                        z0 - i0
                                                            + j
                                                            + ea.venv_abs_len_purity(p.join(p0)),
                                                    ),
                                                    ea.clone(),
                                                    p0,
                                                    0,
                                                    0,
                                                    0,
                                                ),
                                                Some(l.clone()),
                                            ),
                                        );
                                        j += 1;
                                        ret
                                    })
                                    .collect::<Vec<_>>()
                            })
                            .collect::<Vec<_>>(),
                        t,
                    );
                    v.push(BindingInformation { t, n: len, w });
                }
                let ea_last = EnvAbs::from(&*env);
                env.drop_values_state(n, enter_state);
                env.drop_types(qs.len());
                let mut n0 = 0;
                let m: HashMap<Label, ITerm> = memory
                    .iter()
                    .rev()
                    .map(|x| -> HashMap<Label, ITerm> {
                        x.2.iter()
                            .rev()
                            .map(|l| -> (Label, ITerm) {
                                let p = (l.clone(), ITerm::var(n0));
                                n0 += 1;
                                p
                            })
                            .collect()
                    })
                    .flatten()
                    .collect();
                let p_all = memory.iter().fold(Pure, |acc, entry| acc.join(entry.1));
                let mut j = 0;
                let t = v.into_iter().rfold(
                    ITerm::pack(
                        ITerm::abs_env_purity(
                            env,
                            p_all,
                            ITerm::let_in(
                                memory
                                    .iter()
                                    .flat_map(|&(_, p0, ref ls, i0, qs_count0, d0)| {
                                        ls.iter()
                                            .map(|l| {
                                                let ret = ITerm::proj(
                                                    ITerm::app_env_purity_skip(
                                                        ITerm::var(z - i0 + j),
                                                        ea_last.clone(),
                                                        p0,
                                                        qs_count - qs_count0,
                                                        d - d0,
                                                        0,
                                                    ),
                                                    Some(l.clone()),
                                                );
                                                j += 1;
                                                ret
                                            })
                                            .collect::<Vec<_>>()
                                    })
                                    .collect::<Vec<_>>(),
                                ITerm::record(m),
                            ),
                        ),
                        (0..qs.len()).map(IType::var).collect(),
                        qs.iter().map(|p| p.0.clone()).rev(),
                        SemanticSig::StructureSig(body.clone()).into(),
                    ),
                    |t0, BindingInformation { t, n, .. }| ITerm::unpack(t, n, t0),
                );
                Ok((
                    t,
                    Existential(Quantified {
                        qs,
                        body: SemanticSig::StructureSig(body),
                    }),
                    ret_subst,
                    p_all,
                ))
            }
            Proj(ref m, ref id) => {
                // TODO: there may be room for performance improvement.
                let (t, asig, s, p) = m.elaborate(env)?;
                let asig0 = asig.clone().try_map::<_, _, TypeError, _>(|ssig| {
                    let mut m = ssig.get_structure()?;
                    m.remove(&id.into())
                        .ok_or_else(|| TypeError::MissingLabel(id.into()))
                })?;
                Ok((
                    ITerm::unpack(
                        t,
                        asig.0.qs.len(),
                        ITerm::pack(
                            ITerm::abs_env_purity(
                                &*env,
                                p,
                                ITerm::proj(
                                    ITerm::app_env_purity(ITerm::var(0), &*env, p),
                                    Some(id.into()),
                                ),
                            ),
                            (0..asig.0.qs.len()).map(IType::var).collect(),
                            asig.0.qs.iter().map(|p| p.0.clone()),
                            asig0.0.body.clone().into(),
                        ),
                    ),
                    asig0,
                    s,
                    p,
                ))
            }
            Seal(ref id, ref sig) => {
                let (ssig, v) = env.lookup_value_by_name(id.into())?;
                let (asig, s) = sig.elaborate(env)?;
                let (t, tys) = ssig.r#match(env, &asig)?;
                let qs = asig.0.qs.clone().lifted_by(env);
                let mut body = asig.0.body.clone();
                {
                    use internal::Variable::Variable as V;
                    let s0 = Subst::from_iter(
                        (0..qs.len()).map(|i| (V(i), IType::app_env(IType::var(i), env))),
                    );
                    body.apply(&s0);
                }
                Ok((
                    //TODO: the 4th argument to `ITerm::pack` should perhaps be changed.
                    ITerm::pack(
                        ITerm::abs_env(&*env, ITerm::app(t, ITerm::Var(v))),
                        tys.into_iter()
                            .map(|ty| IType::abs_env(&*env, ty))
                            .collect(),
                        asig.0.qs.iter().map(|p| p.0.clone()),
                        asig.0.body.clone().into(),
                    ),
                    Existential(Quantified { qs, body }),
                    s,
                    Pure,
                ))
            }
            Fun(ref id, ref sig, ref m) => {
                let (asig1, s1) = sig.elaborate(env)?;
                let enter_state = env.get_state();
                env.insert_types(asig1.0.qs.clone().into_iter().map(|(k, s)| (k, Some(s))));
                env.insert_value(Name::from(id.clone()), asig1.0.body.clone());
                let (t, asig2, s2, p) = m.elaborate(env)?;
                // TODO: apply `s2` to `asig1`?
                env.drop_values_state(1, enter_state);
                env.drop_types(asig1.0.qs.len());
                if p.is_pure() {
                    unimplemented!();
                }
                Ok((
                    ITerm::abs_env(
                        env,
                        ITerm::poly(
                            asig1.0.qs.iter().map(|p| p.0.clone()),
                            ITerm::abs(asig1.0.body.clone().into(), t),
                        ),
                    ),
                    Existential::from(SemanticSig::FunctorSig(
                        Universal::from(asig1).map(|ssig| Box::new(self::Fun(ssig, asig2))),
                    )),
                    s1.compose(s2),
                    Pure,
                ))
            }
            App(ref id1, ref id2) => {
                let (ssig1, v1) = env.lookup_value_by_name(id1.into())?;
                let (ssig2, v2) = env.lookup_value_by_name(id2.into())?;
                // FIXME: Support applicative functors.
                let u = ssig1.get_functor()?;
                let p = Impure;
                let self::Fun(ssig1, mut asig1) = u.0.body;
                let len = u.0.qs.len();
                let (t, tys) = ssig2.r#match(
                    env,
                    &Existential(Quantified {
                        qs: u.0.qs,
                        body: ssig1,
                    }),
                )?;
                let s =
                    Subst::from_iter((0..len).rev().map(internal::Variable::new).zip(tys.clone()));
                // TODO: This may be wrong.
                asig1.apply(&s);
                Ok((
                    ITerm::abs_env_purity(
                        env,
                        p,
                        ITerm::app(
                            ITerm::inst(ITerm::Var(v1), tys),
                            ITerm::app(t, ITerm::Var(v2)),
                        ),
                    ),
                    asig1,
                    Subst::default(),
                    p,
                ))
            }
            Unpack(ref e, ref sig) => {
                let (asig, s1) = sig.elaborate(env)?;
                let asig = asig.normalize();
                let ty1 = IType::from(asig.clone());
                let (t, ty, s2) = e.elaborate(env)?;
                if !ty.equal(&ty1) {
                    Err(TypeError::TypeMismatch(ty, ty1))?;
                }
                Ok((t, asig, s1.compose(s2), Impure))
            }
        }
    }
}

impl Elaboration for Path {
    type Output = (ITerm, SemanticSig, Subst);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        let (t, asig, s, p) = self.0.elaborate(env)?;
        // Need shift?
        IType::from(asig.0.body.clone())
            .kind_of(env)
            .map_err(TypeError::KindError)?
            .mono()
            .map_err(TypeError::NotMono)?;
        Ok((
            ITerm::unpack(
                t,
                asig.0.qs.len(),
                ITerm::app_env_purity(ITerm::var(0), env, p),
            ),
            asig.0.body,
            s,
        ))
    }
}

impl Subtype for IType {
    type Error = TypeError;

    fn subtype_of(&self, _: &mut Env, another: &Self) -> Result<ITerm, Self::Error> {
        if self.equal(another) {
            Ok(ITerm::abs(self.clone(), ITerm::var(0)))
        } else {
            Err(TypeError::NotSubtype(self.clone(), another.clone()))
        }
    }
}

impl Subtype<AbstractSig> for SemanticSig {
    type Error = TypeError;

    fn subtype_of(&self, env: &mut Env, another: &AbstractSig) -> Result<ITerm, Self::Error> {
        let ty: IType = self.clone().into();
        let (t, tys) = self.r#match(env, another)?;
        Ok(ITerm::abs(
            ty,
            ITerm::pack(
                ITerm::app(t, ITerm::var(0)),
                tys,
                another.0.qs.iter().map(|p| p.0.clone()),
                another.0.body.clone().into(),
            ),
        ))
    }
}

impl Subtype for SemanticSig {
    type Error = TypeError;

    fn subtype_of(&self, env: &mut Env, another: &Self) -> Result<ITerm, Self::Error> {
        use SemanticSig::*;
        match (self, another) {
            (&AtomicTerm(ref sp1, ref ty1), &AtomicTerm(ref sp2, ref ty2)) => {
                if !sp1.equal(sp2) {
                    return Err(TypeError::SemanticPathMismatch(sp1.clone(), sp2.clone()));
                }
                let t = ty1.subtype_of(env, ty2)?;
                Ok(ITerm::abs(
                    IType::from(AtomicTerm(sp1.clone(), ty1.clone())),
                    ITerm::from(SemanticTerm::Term(ITerm::app(t, ITerm::var(0)))),
                ))
            }
            (&AtomicType(ref ty1, ref k1), &AtomicType(ref ty2, ref k2)) => {
                if k1 != k2 {
                    Err(TypeError::KindError(internal::KindError::KindMismatch(
                        k1.clone(),
                        k2.clone(),
                    )))?;
                }
                if !ty1.equal(ty2) {
                    Err(TypeError::TypeMismatch(ty1.clone(), ty2.clone()))?;
                }
                Ok(ITerm::abs(
                    IType::from(AtomicType(ty1.clone(), k1.clone())),
                    ITerm::var(0),
                ))
            }
            (&AtomicSig(ref asig1), &AtomicSig(ref asig2)) => {
                let _ = asig1.subtype_of(env, asig2)?;
                let _ = asig2.subtype_of(env, asig1)?;
                Ok(ITerm::abs(
                    AtomicSig(asig1.clone()).into(),
                    SemanticTerm::Sig(*asig2.clone()).into(),
                ))
            }
            (&StructureSig(ref m1), &StructureSig(ref m2)) => {
                let mut m = HashMap::new();
                for (l, ssig2) in m2.iter() {
                    let ssig1 = m1
                        .get(l)
                        .ok_or_else(|| TypeError::MissingLabel(l.clone()))?;
                    let t = ssig1.subtype_of(env, ssig2)?;
                    m.insert(
                        l.clone(),
                        ITerm::app(t, ITerm::proj(ITerm::var(0), Some(l.clone()))),
                    );
                }
                Ok(ITerm::abs(IType::from(self.clone()), ITerm::record(m)))
            }
            (&FunctorSig(ref u1), &FunctorSig(ref u2)) => subtype_functor(env, u1, u2),
            (&Applicative(ref u1), &FunctorSig(ref u2)) => subtype_functor(env, u1, u2),
            (&Applicative(ref u1), &Applicative(ref u2)) => subtype_functor(env, u1, u2),
            _ => Err(TypeError::NotSubsignature(self.clone(), another.clone())),
        }
    }
}

fn subtype_functor<T, U>(
    env: &mut Env,
    u1: &Universal<Box<T>>,
    u2: &Universal<Box<U>>,
) -> Result<ITerm, TypeError>
where
    T: Functional + Clone + Into<IType>,
    U: Functional + Clone + Into<IType>,
    TypeError: From<<T::Range as Subtype<U::Range>>::Error>,
    T::Range: Subtype<U::Range>,
{
    env.insert_types(u2.0.qs.clone().into_iter().map(|(k, s)| (k, Some(s))));
    let (ssig1, mut asig1) = u1.0.body.clone().get_function();
    let (ssig2, asig2) = u2.0.body.ref_function();
    // contra-variant.
    let (t1, tys) = ssig2.r#match(
        env,
        &Existential(Quantified {
            qs: u1.0.qs.clone(),
            body: ssig1,
        }),
    )?;
    let s = Subst::from_iter(
        (0..u1.0.qs.len())
            .rev()
            .map(internal::Variable::new)
            .zip(tys.clone()),
    );
    asig1.apply(&s);
    // TODO: maybe `asig1.shift(-u1.0.qs.len())` is needed here.

    // covariant.
    let t2 = asig1.subtype_of(env, &asig2)?;
    env.drop_types(u2.0.qs.len());
    Ok(ITerm::abs(
        u1.clone().into(),
        ITerm::poly(
            u2.0.qs.iter().map(|p| p.0.clone()),
            ITerm::abs(
                ssig2.clone().into(),
                ITerm::app(
                    t2,
                    ITerm::app(
                        ITerm::inst(ITerm::var(1), tys),
                        ITerm::app(t1, ITerm::var(0)),
                    ),
                ),
            ),
        ),
    ))
}

impl Subtype for AbstractSig {
    type Error = TypeError;

    fn subtype_of(&self, env: &mut Env, another: &Self) -> Result<ITerm, Self::Error> {
        env.insert_types(self.0.qs.clone().into_iter().map(|(k, s)| (k, Some(s))));
        let ty: IType = self.clone().into();
        let (t, tys) = self.0.body.r#match(env, another)?;
        // FIXME: drop types from `env`.
        Ok(ITerm::abs(
            ty,
            ITerm::unpack(
                ITerm::var(0),
                self.0.qs.len(),
                ITerm::pack(
                    ITerm::app(t, ITerm::var(0)),
                    tys,
                    another.0.qs.iter().map(|p| p.0.clone()),
                    another.0.body.clone().into(),
                ),
            ),
        ))
    }
}

impl Normalize for IType {
    fn normalize(self) -> Self {
        // TODO: Canonicalize the order of quantified type variables in polymorphic types.
        self
    }
}

impl Normalize for SemanticPath {
    fn normalize(self) -> Self {
        // TODO: What is the correct definition?
        self
    }
}

impl Normalize for SemanticSig {
    fn normalize(self) -> Self {
        use SemanticSig::*;
        match self {
            AtomicTerm(sp, ty) => AtomicTerm(sp.normalize(), ty.normalize()),
            AtomicType(..) => self,
            AtomicSig(asig) => AtomicSig(Box::new(asig.normalize())),
            StructureSig(m) => StructureSig(
                m.into_iter()
                    .map(|(l, ssig)| (l, ssig.normalize()))
                    .collect(),
            ),
            FunctorSig(u) => {
                let Fun(ssig, asig) = *u.0.body;
                let ssig = ssig.normalize();
                let (ks, s) = ssig.sort_quantifiers(u.0.qs);
                let mut f = Fun(ssig, asig.normalize());
                f.apply(&s);
                FunctorSig(Universal(Quantified {
                    qs: ks,
                    body: Box::new(f),
                }))
            }
            Applicative(u) => {
                let self::Applicative(ssig1, ssig2) = *u.0.body;
                let ssig1 = ssig1.normalize();
                let (ks, s) = ssig1.sort_quantifiers(u.0.qs);
                let mut f = self::Applicative(ssig1, ssig2.normalize());
                f.apply(&s);
                Applicative(Universal(Quantified {
                    qs: ks,
                    body: Box::new(f),
                }))
            }
        }
    }
}

impl Normalize for AbstractSig {
    fn normalize(self) -> Self {
        let mut ssig = self.0.body.normalize();
        let (ks, s) = ssig.sort_quantifiers(self.0.qs);
        ssig.apply(&s);
        Existential(Quantified { qs: ks, body: ssig })
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

impl<T> From<Existential<T>> for Universal<T> {
    fn from(ex: Existential<T>) -> Self {
        Universal(ex.0)
    }
}

impl<T> Quantified<T> {
    fn map<F, U>(self, f: F) -> Quantified<U>
    where
        F: FnOnce(T) -> U,
    {
        Quantified {
            qs: self.qs,
            body: f(self.body),
        }
    }

    fn try_map<F, U, ER, EQ>(self, f: F) -> Result<Quantified<U>, ER>
    where
        F: FnOnce(T) -> Result<U, EQ>,
        ER: From<EQ>,
    {
        Ok(Quantified {
            qs: self.qs,
            body: f(self.body)?,
        })
    }
}

impl<T> Existential<T> {
    fn new(qs: Vec<(IKind, StemFrom)>, body: T) -> Self {
        Existential(Quantified { qs, body })
    }

    fn map<F, U>(self, f: F) -> Existential<U>
    where
        F: FnOnce(T) -> U,
    {
        Existential(self.0.map(f))
    }

    fn try_map<F, U, ER, EQ>(self, f: F) -> Result<Existential<U>, ER>
    where
        F: FnOnce(T) -> Result<U, EQ>,
        ER: From<EQ>,
    {
        Ok(Existential(self.0.try_map(f)?))
    }
}

impl<T> Universal<T> {
    fn map<F, U>(self, f: F) -> Universal<U>
    where
        F: FnOnce(T) -> U,
    {
        Universal(self.0.map(f))
    }
}

impl<S: std::hash::BuildHasher> Existential<HashMap<Label, SemanticSig, S>> {
    fn merge(mut self, ex: Existential<HashMap<Label, SemanticSig>>) -> Result<Self, TypeError> {
        for l in ex.0.body.keys() {
            if self.0.body.contains_key(l) {
                Err(TypeError::DuplicateLabel(l.clone()))?;
            }
        }
        self.0.body.shift(isize::try_from(ex.0.qs.len()).unwrap());
        self.0.qs.extend(ex.0.qs);
        self.0.body.extend(ex.0.body);
        Ok(self)
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

    fn pack(m: Module, sig: Sig) -> Self {
        Expr::Pack(Box::new(m), sig)
    }

    fn r#if(e1: Expr, e2: Expr, e3: Expr) -> Self {
        Expr::If(Box::new(e1), Box::new(e2), Box::new(e3))
    }

    fn bin_op(op: BinOp, e1: Expr, e2: Expr) -> Self {
        Expr::BinOp(op, Box::new(e1), Box::new(e2))
    }

    fn infer(&self, env: &mut Env) -> Result<(ITerm, IType, Subst), TypeError> {
        use Expr::*;
        use IKind::*;
        match *self {
            Abs(ref id, ref e) => {
                let v = env.fresh_type_variable(Mono);
                let mut ty0 = IType::Var(v);
                let name = Name::from(id.clone());
                let enter_state = env.get_state();
                env.insert_value(name.clone(), SemanticSig::default_atomic_term(ty0.clone()));
                let (t, ty, s) = e.infer(env)?;
                env.drop_values_state(1, enter_state);
                ty0.apply(&s);
                Ok((
                    ITerm::abs(SemanticSig::default_atomic_term(ty0.clone()).into(), t),
                    IType::fun(ty0, ty),
                    s,
                ))
            }
            App(ref e1, ref e2) => {
                let (mut t1, mut ty1, s1) = e1.infer(env)?;
                let (t2, ty2, s2) = e2.infer(env)?;
                t1.apply(&s2);
                ty1.apply(&s2);
                let mut v = IType::Var(env.fresh_type_variable(Mono));
                let s3 = env
                    .unify(vec![(ty1, IType::fun(ty2, v.clone()))])
                    .map_err(|e| TypeError::Unification(self.clone(), e))?;
                t1.apply(&s3);
                v.apply(&s3);
                let s = s1.compose(s2).compose(s3);
                Ok((ITerm::app(t1, t2), v, s))
            }
            Path(ref p) => {
                let (t, asig, s, p) = p.0.elaborate(env)?;
                let qs = asig.0.qs;
                let (_, ty) = asig.0.body.get_atomic_term()?;
                // Need shift?
                ty.kind_of(env)
                    .map_err(TypeError::KindError)?
                    .mono()
                    .map_err(TypeError::NotMono)?;
                let (ty, tys) = ty.new_instance(env);
                Ok((
                    ITerm::unpack(
                        t,
                        qs.len(),
                        ITerm::inst(ITerm::app_env_purity(ITerm::var(0), env, p), tys),
                    ),
                    ty,
                    s,
                ))
            }
            Pack(ref m, ref sig) => {
                let (t2, asig0, s1, p) = m.elaborate(env)?;
                let (asig, s2) = sig.elaborate(env)?;
                let asig = asig.normalize();
                let t1 = asig0.subtype_of(env, &asig)?;
                Ok((
                    ITerm::app(
                        t1,
                        ITerm::unpack(
                            t2,
                            asig0.0.qs.len(),
                            ITerm::pack(
                                ITerm::app_env_purity(ITerm::var(0), env, p),
                                (0..asig0.0.qs.len()).map(IType::var).collect(),
                                asig.0.qs.iter().map(|p| p.0.clone()),
                                asig0.into(),
                            ),
                        ),
                    ),
                    asig.into(),
                    s1.compose(s2),
                ))
            }
            Int(n) => Ok((ITerm::Int(n), IType::Int, Subst::default())),
            Bool(b) => Ok((ITerm::Bool(b), IType::Bool, Subst::default())),
            If(ref e1, ref e2, ref e3) => {
                let (mut t1, ty1, s1) = e1.infer(env)?;
                let u1 = env
                    .unify(vec![(ty1, IType::Bool)])
                    .map_err(|e| TypeError::Unification(self.clone(), e))?;
                let (mut t2, mut ty2, s2) = e2.infer(env)?;
                let (mut t3, ty3, s3) = e3.infer(env)?;
                let u2 = env
                    .unify(vec![(ty2.clone(), ty3)])
                    .map_err(|e| TypeError::Unification(self.clone(), e))?;

                t1.apply(&u1);
                t1.apply(&s2);
                t1.apply(&s3);
                t1.apply(&u2);

                t2.apply(&s3);
                t2.apply(&u2);

                ty2.apply(&s3);
                ty2.apply(&u2);

                t3.apply(&u2);

                Ok((
                    ITerm::r#if(t1, t2, t3),
                    ty2,
                    s1.compose(u1).compose(s2).compose(s3).compose(u2),
                ))
            }
            BinOp(ref op, ref e1, ref e2) => {
                use self::BinOp::*;
                match op {
                    LessThan | GreaterThan => {
                        let (mut t1, ty1, s1) = e1.infer(env)?;
                        let u1 = env
                            .unify(vec![(ty1, IType::Int)])
                            .map_err(|e| TypeError::Unification(self.clone(), e))?;
                        let (mut t2, ty2, s2) = e2.infer(env)?;
                        let u2 = env
                            .unify(vec![(ty2, IType::Int)])
                            .map_err(|e| TypeError::Unification(self.clone(), e))?;

                        t1.apply(&u1);
                        t1.apply(&s2);
                        t1.apply(&u2);

                        t2.apply(&u2);
                        Ok((
                            ITerm::bin_op(op.clone(), t1, t2),
                            IType::Bool,
                            s1.compose(u1).compose(s2).compose(u2),
                        ))
                    }
                }
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

    fn pack(sig: Sig) -> Self {
        Type::Pack(Box::new(sig))
    }
}

impl SemanticSig {
    fn atomic_sig(qs: Vec<(IKind, StemFrom)>, body: SemanticSig) -> Self {
        SemanticSig::AtomicSig(Box::new(Existential(Quantified { qs, body })))
    }

    // TODO: remove this function.
    fn default_atomic_term(ty: IType) -> Self {
        // An arbitrary value.
        SemanticSig::AtomicTerm(SemanticPath::from(100_000), ty)
    }

    fn lookup_instantiation(&self, ssig: &SemanticSig, mut sp: SemanticPath) -> Option<IType> {
        use SemanticSig::*;
        match (self, ssig) {
            (&AtomicTerm(ref sp1, _), &AtomicTerm(ref sp2, _)) => {
                if sp.equal(sp2) {
                    Some(sp1.clone().into())
                } else {
                    None
                }
            }
            (&AtomicType(ref ty1, _), &AtomicType(ref ty2, _)) => {
                // Kind equality is later tested (maybe).
                if sp.equal_type(ty2) {
                    Some(ty1.clone())
                } else {
                    None
                }
            }
            (&StructureSig(ref m1), &StructureSig(ref m2)) => {
                for (l, ssig2) in m2.iter() {
                    if let Some(ssig1) = m1.get(l) {
                        if let Some(ty) = ssig1.lookup_instantiation(ssig2, sp.clone()) {
                            return Some(ty);
                        }
                    }
                }
                None
            }
            (&Applicative(ref u1), &Applicative(ref u2)) => {
                let self::Applicative(ref ssig11, ref ssig12) = *u1.0.body;
                let self::Applicative(ref ssig21, ref ssig22) = *u2.0.body;
                let tys = ssig21.lookup_instantiations(
                    ssig11,
                    (0..u1.0.qs.len()).map(internal::Variable::new).collect(),
                );
                let mut ssig12 = ssig12.clone();
                ssig12.apply(&Subst::from_iter(
                    (0..u1.0.qs.len()).map(internal::Variable::new).zip(tys),
                ));
                sp.append((0..u2.0.qs.len()).map(IType::var));
                let ty = ssig12.lookup_instantiation(ssig22, sp)?;
                Some(IType::abs(u2.0.qs.iter().rev().map(|p| p.0.clone()), ty))
            }
            _ => None,
        }
    }

    fn lookup_instantiations(&self, ssig: &SemanticSig, vs: Vec<internal::Variable>) -> Vec<IType> {
        vs.into_iter()
            .scan(ssig.clone(), |ssig, v| {
                let x = self
                    .lookup_instantiation(ssig, v.into())
                    .expect("not explicit");
                ssig.apply(&Subst::from_iter(Some((v, x.clone()))));
                Some(x)
            })
            .collect()
    }

    fn r#match(
        &self,
        env: &mut Env,
        against: &AbstractSig,
    ) -> Result<(ITerm, Vec<IType>), TypeError> {
        let n = against.0.qs.len();
        let tys = self.lookup_instantiations(
            &against.0.body,
            (0..n).map(internal::Variable::new).collect(),
        );
        // TODO: Should be well-kindness of `tys` tested?.
        let mut tys0 = tys.clone();
        let ni = isize::try_from(n).unwrap();
        tys0.shift(ni);
        let mut ssig = against.0.body.clone();
        let iter = (0..n).map(internal::Variable::new).zip(tys0);
        ssig.apply(&Subst::from_iter(iter));
        ssig.shift(-ni);
        let t = self.subtype_of(env, &ssig)?;
        Ok((t, tys))
    }

    fn proj(&self, id: &Ident) -> Result<&SemanticSig, TypeError> {
        match *self {
            SemanticSig::StructureSig(ref m) => m
                .get(&id.into())
                .ok_or_else(|| TypeError::MissingLabel(id.into())),
            _ => Err(TypeError::SemanticSigError(SemanticSigError::Structure(
                self.clone(),
            ))),
        }
    }

    fn proj_multi(&self, p: &Proj<Ident>) -> Result<&SemanticSig, TypeError> {
        let mut ssig = self.proj(&p.0)?;
        for id in p.1.iter() {
            ssig = ssig.proj(id)?;
        }
        Ok(ssig)
    }

    fn first_apper(&self, v: internal::Variable) -> Option<VecDeque<Label>> {
        use SemanticSig::*;
        match *self {
            AtomicType(IType::Var(v0), _) if v0 == v => Some(VecDeque::new()),
            StructureSig(ref m) => {
                let (l, mut v) = BTreeMap::from_iter(m)
                    .into_iter()
                    .find_map(|(l, ssig)| ssig.first_apper(v).map(|v| (l, v)))?;
                v.push_front(l.clone());
                Some(v)
            }
            _ => None,
        }
    }

    fn sort_quantifiers<K>(&self, ks: Vec<K>) -> (Vec<K>, Subst) {
        use internal::Variable::Variable;
        let len = ks.len();
        let mut xs: Vec<(K, usize)> = ks.into_iter().zip((0..len).rev()).collect();
        xs.sort_unstable_by_key(|&(_, i)| self.first_apper(Variable(i)));
        let ys = (0..)
            .zip(xs)
            .map(|(n, (k, i))| (k, (Variable(i), IType::var(n))));
        let mut ks = VecDeque::new();
        let mut m = HashMap::new();
        for (k, (v, ty)) in ys {
            ks.push_front(k);
            m.insert(v, ty);
        }
        (Vec::from(ks), Subst::from_iter(m))
    }

    fn skolemize(&mut self, m: usize, n: usize) {
        use internal::Variable::Variable as V;

        // TODO: `Subst::compose` may be useful.
        let s = Subst::from_iter(
            (0..n)
                .map(|i| (i, i + m))
                .chain((0..m).map(|i| (n + i, i)))
                .map(|(i, j)| (V(i), IType::var(j))),
        );
        self.apply(&s);

        let s = Subst::from_iter((0..n).map(|i| {
            (
                V(m + i),
                (0..m).fold(IType::var(m + i), |acc, j| IType::app(acc, IType::var(j))),
            )
        }));
        self.apply(&s);
    }
}

impl Sig {
    fn path(m: Module) -> Self {
        Sig::Path(Path::from(m))
    }

    fn generative(id: Ident, sig1: Sig, sig2: Sig) -> Self {
        Sig::Generative(id, Box::new(sig1), Box::new(sig2))
    }

    fn applicative(id: Ident, sig1: Sig, sig2: Sig) -> Self {
        Sig::Applicative(id, Box::new(sig1), Box::new(sig2))
    }

    fn r#where(sig: Sig, p: Proj<Ident>, ty: Type) -> Self {
        Sig::Where(Box::new(sig), p, ty)
    }
}

impl Module {
    fn proj(m: Module, id: Ident) -> Self {
        Module::Proj(Box::new(m), id)
    }

    fn fun(id: Ident, sig: Sig, m: Module) -> Self {
        Module::Fun(id, sig, Box::new(m))
    }

    fn unpack(e: Expr, sig: Sig) -> Self {
        Module::Unpack(Box::new(e), sig)
    }
}

trait Functional {
    type Range: Substitution + Subtype;

    fn get_function(self) -> (SemanticSig, Self::Range);
    fn ref_function(&self) -> (&SemanticSig, &Self::Range);
}

impl Functional for Fun {
    type Range = AbstractSig;

    fn get_function(self) -> (SemanticSig, Self::Range) {
        (self.0, self.1)
    }

    fn ref_function(&self) -> (&SemanticSig, &Self::Range) {
        (&self.0, &self.1)
    }
}

impl Functional for Applicative {
    type Range = SemanticSig;

    fn get_function(self) -> (SemanticSig, Self::Range) {
        (self.0, self.1)
    }

    fn ref_function(&self) -> (&SemanticSig, &Self::Range) {
        (&self.0, &self.1)
    }
}

impl Purity {
    /// # Examples
    ///
    /// ```
    /// use modules::rrd2014::*;
    /// use Purity::*;
    ///
    /// assert_eq!(Pure.join(Pure), Pure);
    /// assert_eq!(Pure.join(Impure), Impure);
    /// assert_eq!(Impure.join(Pure), Impure);
    /// assert_eq!(Impure.join(Impure), Impure);
    /// ```
    pub fn join(self, p: Purity) -> Self {
        self.max(p)
    }

    fn is_pure(self) -> bool {
        self == Purity::Pure
    }

    fn is_impure(self) -> bool {
        self == Purity::Impure
    }
}

impl SemanticPath {
    pub fn equal(&self, sp: &SemanticPath) -> bool {
        self.v == sp.v
            && self.tys.len() == sp.tys.len()
            && self
                .tys
                .iter()
                .zip(sp.tys.iter())
                .all(|(ty1, ty2)| ty1.equal(ty2))
    }

    pub fn equal_type(&self, ty: &IType) -> bool {
        self.tys
            .iter()
            .fold(IType::Var(self.v), |acc, ty| IType::app(acc, ty.clone()))
            .equal(ty)
    }

    fn append<I>(&mut self, tys: I)
    where
        I: IntoIterator<Item = IType>,
    {
        self.tys.extend(tys);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn env_insert() {
        use internal::Kind::*;
        use internal::*;

        let mut env: Env<SemanticSig, _> = Env::default();

        env.insert_types(vec![(Mono, "s"), (Kind::fun(Mono, Mono), "M.t")]);
        assert_eq!(
            env.lookup_type(Variable::new(0)),
            Ok((Kind::fun(Mono, Mono), "M.t"))
        );
        assert_eq!(env.lookup_type(Variable::new(1)), Ok((Mono, "s")));

        env.insert_value(
            Name::new("x".to_string()),
            SemanticSig::default_atomic_term(Type::Int),
        );
        assert_eq!(
            env.lookup_value(Variable::new(0)),
            Ok(SemanticSig::default_atomic_term(Type::Int))
        );
    }

    macro_rules! assert_elaborate_ok_1 {
        ($x:expr, $r:expr) => {{
            let mut env = Env::default();
            let p = $x.elaborate(&mut env).unwrap();
            assert_eq!(p.0, $r);
        }};
    }

    macro_rules! assert_elaborate_ok_2 {
        ($x:expr, ($r1:expr, $r2:expr)) => {{
            let mut env = Env::default();
            let p = $x.elaborate(&mut env).unwrap();
            assert_eq!((p.0, p.1), ($r1, $r2));
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

        assert_elaborate_ok_2!(Int, (IType::Int, Mono));
        assert_elaborate_ok_2!(
            Type::fun(Int, Int),
            (IType::fun(IType::Int, IType::Int), Mono)
        );
        assert_elaborate_err!(
            Type::path(Module::Ident(Ident::from("t"))),
            TypeError::Env(EnvError::UnboundName(Name::from("t")))
        );
    }

    #[test]
    fn elaborate_expr() {
        use internal::UnificationError;
        use Expr::*;

        assert_elaborate_ok_2!(Int(55), (ITerm::Int(55), IType::Int));

        assert_elaborate_ok_2!(
            Expr::abs(Ident::from("x"), Int(55)),
            (
                ITerm::abs(IType::generated_var(0), ITerm::Int(55)),
                IType::fun(IType::generated_var(0), IType::Int)
            )
        );

        assert_elaborate_ok_2!(
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
                UnificationError::NotUnifiable(
                    IType::Int,
                    IType::fun(IType::Int, IType::generated_var(0))
                )
            )
        );

        assert_elaborate_err!(
            Expr::path(Module::Ident(Ident::from("x"))),
            TypeError::Env(EnvError::UnboundName(Name::from("x")))
        );

        assert_elaborate_ok_2!(
            Expr::abs(
                Ident::from("x"),
                Expr::path(Module::Ident(Ident::from("x")))
            ),
            (
                ITerm::abs(
                    IType::generated_var(0),
                    ITerm::r#let(ITerm::var(0), ITerm::var(0)),
                ),
                IType::fun(IType::generated_var(0), IType::generated_var(0))
            )
        );
    }

    #[test]
    fn elaborate_binding() {
        use super::Type as T;
        use Binding::*;
        use IKind::*;
        use SemanticSig::*;

        assert_elaborate_ok_2!(
            Val(Ident::from("x"), Expr::Int(23)),
            (
                ITerm::record(vec![(Label::from("x"), ITerm::Int(23))]),
                Existential::from(HashMap::from_iter(vec![(
                    Label::from("x"),
                    SemanticSig::default_atomic_term(IType::Int)
                )]))
            )
        );

        assert_elaborate_ok_2!(
            Val(Ident::from("x"), Expr::abs(Ident::from("y"), Expr::Int(22))),
            (
                ITerm::record(vec![(
                    Label::from("x"),
                    ITerm::poly(vec![Mono], ITerm::abs(IType::var(0), ITerm::Int(22)))
                )]),
                Existential::from(HashMap::from_iter(vec![(
                    Label::from("x"),
                    SemanticSig::default_atomic_term(IType::forall(
                        vec![Mono],
                        IType::fun(IType::var(0), IType::Int)
                    ))
                )]))
            )
        );

        assert_elaborate_ok_2!(
            Type(Ident::from("t"), T::Int),
            (
                ITerm::record(vec![(
                    Label::from("t"),
                    ITerm::poly(
                        vec![IKind::fun(IKind::Mono, IKind::Mono)],
                        ITerm::abs(IType::app(IType::var(0), IType::Int), ITerm::var(0))
                    )
                )]),
                Existential::from(HashMap::from_iter(vec![(
                    Label::from("t"),
                    AtomicType(IType::Int, IKind::Mono)
                )]))
            )
        );

        assert_elaborate_ok_2!(
            Type(Ident::from("t"), T::fun(T::Int, T::Int)),
            (
                ITerm::record(vec![(
                    Label::from("t"),
                    ITerm::poly(
                        vec![IKind::fun(IKind::Mono, IKind::Mono)],
                        ITerm::abs(
                            IType::app(IType::var(0), IType::fun(IType::Int, IType::Int)),
                            ITerm::var(0)
                        )
                    )
                )]),
                Existential::from(HashMap::from_iter(vec![(
                    Label::from("t"),
                    AtomicType(IType::fun(IType::Int, IType::Int), IKind::Mono)
                )]))
            )
        );
    }

    #[test]
    fn elaborate_module() {
        use super::Ident as I;
        use super::Module::*;
        use super::Type as T;
        use Binding::*;
        use SemanticSig::*;

        assert_elaborate_ok_2!(
            Seq(vec![]),
            (
                ITerm::record(None),
                Existential::from(StructureSig(HashMap::new()))
            )
        );

        assert_elaborate_ok_2!(
            Seq(vec![Type(I::from("t"), T::Int)]),
            (
                ITerm::r#let(
                    ITerm::record(vec![(
                        Label::from("t"),
                        ITerm::poly(
                            vec![IKind::fun(IKind::Mono, IKind::Mono)],
                            ITerm::abs(IType::app(IType::var(0), IType::Int), ITerm::var(0))
                        )
                    )]),
                    ITerm::r#let(
                        ITerm::proj(ITerm::var(0), Some(Label::from("t"))),
                        ITerm::record(vec![(
                            Label::from("t"),
                            ITerm::proj(ITerm::var(1), Some(Label::from("t")))
                        )])
                    )
                ),
                Existential::from(StructureSig(HashMap::from_iter(vec![(
                    Label::from("t"),
                    AtomicType(IType::Int, IKind::Mono)
                )])))
            )
        );

        assert_elaborate_ok_2!(
            Seq(vec![
                Type(I::from("t"), T::Int),
                Type(I::from("s"), T::path(Ident(I::from("t"))))
            ]),
            (
                ITerm::r#let(
                    ITerm::record(vec![(
                        Label::from("t"),
                        ITerm::poly(
                            vec![IKind::fun(IKind::Mono, IKind::Mono)],
                            ITerm::abs(IType::app(IType::var(0), IType::Int), ITerm::var(0))
                        )
                    )]),
                    ITerm::r#let(
                        ITerm::proj(ITerm::var(0), Some(Label::from("t"))),
                        ITerm::r#let(
                            ITerm::record(vec![(
                                Label::from("s"),
                                ITerm::poly(
                                    vec![IKind::fun(IKind::Mono, IKind::Mono)],
                                    ITerm::abs(
                                        IType::app(IType::var(0), IType::Int),
                                        ITerm::var(0)
                                    )
                                )
                            )]),
                            ITerm::r#let(
                                ITerm::proj(ITerm::var(0), Some(Label::from("s"))),
                                ITerm::record(vec![
                                    (
                                        Label::from("t"),
                                        ITerm::proj(ITerm::var(3), Some(Label::from("t")))
                                    ),
                                    (
                                        Label::from("s"),
                                        ITerm::proj(ITerm::var(1), Some(Label::from("s")))
                                    )
                                ])
                            )
                        )
                    )
                ),
                Existential::from(StructureSig(HashMap::from_iter(vec![
                    (Label::from("t"), AtomicType(IType::Int, IKind::Mono)),
                    (Label::from("s"), AtomicType(IType::Int, IKind::Mono))
                ])))
            )
        );

        assert_elaborate_ok_2!(
            Seq(vec![
                Type(I::from("t"), T::Int),
                Type(
                    I::from("s"),
                    T::fun(T::path(Ident(I::from("t"))), T::path(Ident(I::from("t"))))
                )
            ]),
            (
                ITerm::r#let(
                    ITerm::record(vec![(
                        Label::from("t"),
                        ITerm::poly(
                            vec![IKind::fun(IKind::Mono, IKind::Mono)],
                            ITerm::abs(IType::app(IType::var(0), IType::Int), ITerm::var(0))
                        )
                    )]),
                    ITerm::r#let(
                        ITerm::proj(ITerm::var(0), Some(Label::from("t"))),
                        ITerm::r#let(
                            ITerm::record(vec![(
                                Label::from("s"),
                                ITerm::poly(
                                    vec![IKind::fun(IKind::Mono, IKind::Mono)],
                                    ITerm::abs(
                                        IType::app(
                                            IType::var(0),
                                            IType::fun(IType::Int, IType::Int)
                                        ),
                                        ITerm::var(0)
                                    )
                                )
                            )]),
                            ITerm::r#let(
                                ITerm::proj(ITerm::var(0), Some(Label::from("s"))),
                                ITerm::record(vec![
                                    (
                                        Label::from("t"),
                                        ITerm::proj(ITerm::var(3), Some(Label::from("t")))
                                    ),
                                    (
                                        Label::from("s"),
                                        ITerm::proj(ITerm::var(1), Some(Label::from("s")))
                                    )
                                ])
                            )
                        )
                    )
                ),
                Existential::from(StructureSig(HashMap::from_iter(vec![
                    (Label::from("t"), AtomicType(IType::Int, IKind::Mono)),
                    (
                        Label::from("s"),
                        AtomicType(IType::fun(IType::Int, IType::Int), IKind::Mono)
                    )
                ])))
            )
        );

        let id = I::from;
        let l = internal::Label::from;
        let proj = |x, y| ITerm::proj(x, Some(y));

        assert_elaborate_ok_2!(
            Seq(vec![
                Module(id("M"), Seq(vec![])),
                Module(id("N"), Seal(id("M"), Sig::Seq(vec![])))
            ]),
            (
                ITerm::r#let(
                    ITerm::r#let(
                        ITerm::record(None),
                        ITerm::record(Some((l("M"), ITerm::var(0))))
                    ),
                    ITerm::r#let(
                        proj(ITerm::var(0), l("M")),
                        ITerm::r#let(
                            ITerm::r#let(
                                ITerm::app(
                                    ITerm::abs(IType::record(None), ITerm::record(None)),
                                    ITerm::var(0)
                                ),
                                ITerm::record(Some((l("N"), ITerm::var(0))))
                            ),
                            ITerm::r#let(
                                proj(ITerm::var(0), l("N")),
                                ITerm::record(vec![
                                    (l("M"), proj(ITerm::var(3), l("M"))),
                                    (l("N"), proj(ITerm::var(1), l("N"))),
                                ])
                            )
                        )
                    )
                ),
                Existential::from(SemanticSig::structure_sig(vec![
                    (l("M"), SemanticSig::structure_sig(None)),
                    (l("N"), SemanticSig::structure_sig(None))
                ]))
            )
        );

        assert_eq!(
            Seq(vec![
                Val(id("f"), Expr::abs(id("x"), Expr::path(Ident(id("x"))))),
                Val(
                    id("y"),
                    Expr::app(
                        Expr::path(Ident(id("f"))),
                        Expr::app(Expr::path(Ident(id("f"))), Expr::Int(1))
                    )
                )
            ])
            .elaborate(&mut Env::default())
            .ok()
            .map(|p| p.1),
            Some(Existential::from(SemanticSig::structure_sig(vec![
                (l("y"), SemanticSig::default_atomic_term(IType::Int)),
                (
                    l("f"),
                    SemanticSig::default_atomic_term(IType::forall(
                        vec![IKind::Mono],
                        IType::fun(IType::var(0), IType::var(0))
                    ))
                ),
            ])))
        );
    }

    #[test]
    fn elaborate_decl() {
        use Decl::*;
        use SemanticSig::*;

        let id = Ident::from;
        let l = Label::from;

        assert_elaborate_ok_1!(
            Val(id("a"), Type::Int),
            Existential::from(HashMap::from_iter(Some((
                l("a"),
                SemanticSig::default_atomic_term(IType::Int)
            ))))
        );

        assert_elaborate_ok_1!(
            ManType(id("a"), Type::Int),
            Existential::from(HashMap::from_iter(Some((
                l("a"),
                AtomicType(IType::Int, IKind::Mono)
            ))))
        );

        assert_elaborate_ok_1!(
            AbsType(id("a"), Kind::Mono),
            Existential::new(
                vec![(IKind::Mono, StemFrom::from(id("a")))],
                HashMap::from_iter(Some((l("a"), AtomicType(IType::var(0), IKind::Mono))))
            )
        );
    }

    #[test]
    fn elaborate_sig() {
        use super::Module as Mod;
        use Decl::*;
        use SemanticSig::*;
        use Sig::*;

        let id = Ident::from;
        let l = Label::from;

        assert_elaborate_ok_1!(Seq(vec![]), Existential::from(StructureSig(HashMap::new())));

        assert_elaborate_ok_1!(
            Seq(vec![Val(id("a"), Type::Int)]),
            Existential::from(StructureSig(HashMap::from_iter(vec![(
                l("a"),
                SemanticSig::default_atomic_term(IType::Int)
            )])))
        );

        assert_elaborate_ok_1!(
            Seq(vec![Val(id("a"), Type::Int), Val(id("b"), Type::Int)]),
            Existential::from(StructureSig(HashMap::from_iter(vec![
                (l("a"), SemanticSig::default_atomic_term(IType::Int)),
                (l("b"), SemanticSig::default_atomic_term(IType::Int))
            ])))
        );

        assert_elaborate_ok_1!(
            Seq(vec![Val(id("a"), Type::Int), ManType(id("b"), Type::Int)]),
            Existential::from(StructureSig(HashMap::from_iter(vec![
                (l("a"), SemanticSig::default_atomic_term(IType::Int)),
                (l("b"), AtomicType(IType::Int, IKind::Mono))
            ])))
        );

        assert_elaborate_ok_1!(
            Seq(vec![AbsType(id("a"), Kind::Mono),]),
            Existential::new(
                vec![(IKind::Mono, id("a").into())],
                StructureSig(HashMap::from_iter(vec![(
                    l("a"),
                    AtomicType(IType::var(0), IKind::Mono)
                ),]))
            )
        );

        assert_elaborate_ok_1!(
            Seq(vec![
                AbsType(id("a"), Kind::Mono),
                ManType(id("b"), Type::Int)
            ]),
            Existential::new(
                vec![(IKind::Mono, id("a").into())],
                StructureSig(HashMap::from_iter(vec![
                    (l("a"), AtomicType(IType::var(0), IKind::Mono)),
                    (l("b"), AtomicType(IType::Int, IKind::Mono))
                ]))
            )
        );

        assert_elaborate_ok_1!(
            Seq(vec![
                AbsType(id("a"), Kind::Mono),
                ManType(
                    id("b"),
                    Type::fun(Type::path(Mod::Ident(id("a"))), Type::Int)
                ),
                ManType(
                    id("c"),
                    Type::fun(Type::Int, Type::path(Mod::Ident(id("b"))))
                )
            ]),
            Existential::new(
                vec![(IKind::Mono, id("a").into())],
                StructureSig(HashMap::from_iter(vec![
                    (l("a"), AtomicType(IType::var(0), IKind::Mono)),
                    (
                        l("b"),
                        AtomicType(IType::fun(IType::var(0), IType::Int), IKind::Mono)
                    ),
                    (
                        l("c"),
                        AtomicType(
                            IType::fun(IType::Int, IType::fun(IType::var(0), IType::Int)),
                            IKind::Mono
                        )
                    )
                ]))
            )
        );

        assert_elaborate_ok_1!(
            Seq(vec![
                AbsType(id("a"), Kind::Mono),
                AbsType(id("b"), Kind::Mono),
                AbsType(id("c"), Kind::Mono)
            ]),
            Existential::new(
                vec![
                    (IKind::Mono, id("a").into()),
                    (IKind::Mono, id("b").into()),
                    (IKind::Mono, id("c").into())
                ],
                StructureSig(HashMap::from_iter(vec![
                    (l("a"), AtomicType(IType::var(2), IKind::Mono)),
                    (l("b"), AtomicType(IType::var(1), IKind::Mono)),
                    (l("c"), AtomicType(IType::var(0), IKind::Mono)),
                ]))
            )
        );
    }

    macro_rules! assert_subtype_ok {
        ($x:expr, $y:expr, $r:expr) => {{
            let mut env = Env::default();
            assert_eq!($x.subtype_of(&mut env, &$y), Ok($r));
        }};
    }

    macro_rules! assert_subtype_err {
        ($x:expr, $y:expr, $r:expr) => {{
            let mut env = Env::default();
            assert_eq!($x.subtype_of(&mut env, &$y), Err($r));
        }};
    }

    #[test]
    fn subtype_semantic_sig() {
        use IKind as Kind;
        use IKind::Mono;
        use ITerm as Term;
        use IType as Type;
        use IType::Int;
        use SemanticSig::*;

        let l = internal::Label::from;

        assert_subtype_ok!(
            SemanticSig::default_atomic_term(Int),
            SemanticSig::default_atomic_term(Int),
            Term::abs(Int, Term::app(Term::abs(Int, Term::var(0)), Term::var(0)))
        );

        assert_subtype_err!(
            SemanticSig::default_atomic_term(Int),
            SemanticSig::default_atomic_term(Type::fun(Int, Int)),
            TypeError::NotSubtype(Int, Type::fun(Int, Int))
        );

        assert_subtype_ok!(
            AtomicType(Int, Mono),
            AtomicType(Int, Mono),
            Term::abs(
                Type::forall(
                    Some(Kind::fun(Mono, Mono)),
                    Type::fun(Type::app(Type::var(0), Int), Type::app(Type::var(0), Int))
                ),
                Term::var(0)
            )
        );

        assert_subtype_err!(
            AtomicType(Int, Mono),
            AtomicType(Int, Kind::fun(Mono, Mono)),
            TypeError::KindError(internal::KindError::KindMismatch(
                Mono,
                Kind::fun(Mono, Mono)
            ))
        );

        assert_subtype_err!(
            AtomicType(Int, Mono),
            AtomicType(Type::fun(Int, Int), Mono),
            TypeError::TypeMismatch(Int, Type::fun(Int, Int))
        );

        assert_subtype_ok!(
            SemanticSig::structure_sig(None),
            SemanticSig::structure_sig(None),
            Term::abs(Type::record(None), Term::record(None))
        );

        assert_subtype_ok!(
            SemanticSig::structure_sig(Some((l("a"), SemanticSig::default_atomic_term(Int)))),
            SemanticSig::structure_sig(None),
            Term::abs(Type::record(Some((l("a"), Int))), Term::record(None))
        );

        assert_subtype_ok!(
            SemanticSig::structure_sig(Some((l("a"), SemanticSig::default_atomic_term(Int)))),
            SemanticSig::structure_sig(Some((l("a"), SemanticSig::default_atomic_term(Int)))),
            Term::abs(
                Type::record(Some((l("a"), Int))),
                Term::record(Some((
                    l("a"),
                    Term::app(
                        Term::abs(Int, Term::app(Term::abs(Int, Term::var(0)), Term::var(0))),
                        Term::proj(Term::var(0), Some(l("a")))
                    )
                )))
            )
        );

        let t1 = Term::abs(Int, Term::app(Term::abs(Int, Term::var(0)), Term::var(0)));
        assert_subtype_ok!(
            SemanticSig::structure_sig(vec![
                (l("a"), SemanticSig::default_atomic_term(Int)),
                (l("b"), SemanticSig::default_atomic_term(Int)),
                (l("c"), SemanticSig::default_atomic_term(Int))
            ]),
            SemanticSig::structure_sig(vec![
                (l("a"), SemanticSig::default_atomic_term(Int)),
                (l("b"), SemanticSig::default_atomic_term(Int))
            ]),
            Term::abs(
                Type::record(vec![(l("a"), Int), (l("b"), Int), (l("c"), Int)]),
                Term::record(vec![
                    (
                        l("a"),
                        Term::app(t1.clone(), Term::proj(Term::var(0), Some(l("a"))))
                    ),
                    (
                        l("b"),
                        Term::app(t1, Term::proj(Term::var(0), Some(l("b"))))
                    )
                ])
            )
        );
    }

    #[test]
    fn variable_apper_first() {
        use internal::Variable::*;
        use IKind::Mono;
        use IType as Type;
        use IType::Int;
        use SemanticSig::*;

        let l = Label::from;

        assert_eq!(
            SemanticSig::default_atomic_term(Int).first_apper(Variable(0)),
            None
        );
        assert_eq!(
            SemanticSig::default_atomic_term(Type::var(0)).first_apper(Variable(0)),
            None
        );

        assert_eq!(AtomicType(Int, Mono).first_apper(Variable(0)), None);
        assert_eq!(
            AtomicType(Type::var(0), Mono).first_apper(Variable(0)),
            Some(VecDeque::new())
        );
        assert_eq!(
            AtomicType(Type::var(0), Mono).first_apper(Variable(1)),
            None
        );

        assert_eq!(
            SemanticSig::structure_sig(vec![(l("a"), AtomicType(Type::var(0), Mono))])
                .first_apper(Variable(0)),
            Some(VecDeque::from(vec![l("a")]))
        );
        assert_eq!(
            SemanticSig::structure_sig(vec![(l("b"), AtomicType(Type::var(0), Mono))])
                .first_apper(Variable(0)),
            Some(VecDeque::from(vec![l("b")]))
        );
        assert_eq!(
            SemanticSig::structure_sig(vec![
                (l("abc"), AtomicType(Type::var(0), Mono)),
                (l("ab"), AtomicType(Type::var(0), Mono))
            ])
            .first_apper(Variable(0)),
            Some(VecDeque::from(vec![l("ab")]))
        );
        assert_eq!(
            SemanticSig::structure_sig(vec![
                (l("abc"), AtomicType(Type::var(0), Mono)),
                (l("ab"), AtomicType(Type::var(1), Mono))
            ])
            .first_apper(Variable(0)),
            Some(VecDeque::from(vec![l("abc")]))
        );
        assert_eq!(
            SemanticSig::structure_sig(vec![
                (l("abc"), AtomicType(Type::var(0), Mono)),
                (l("ab"), AtomicType(Type::var(1), Mono))
            ])
            .first_apper(Variable(1)),
            Some(VecDeque::from(vec![l("ab")]))
        );

        assert_eq!(
            SemanticSig::structure_sig(vec![
                (l("abc"), AtomicType(Type::var(0), Mono)),
                (
                    l("ab"),
                    SemanticSig::structure_sig(vec![(l("def"), AtomicType(Type::var(0), Mono))])
                )
            ])
            .first_apper(Variable(0)),
            Some(VecDeque::from(vec![l("ab"), l("def")]))
        );

        assert_eq!(
            SemanticSig::structure_sig(vec![
                (l("a"), AtomicType(Type::var(0), Mono)),
                (
                    l("ab"),
                    SemanticSig::structure_sig(vec![(l("def"), AtomicType(Type::var(0), Mono))])
                )
            ])
            .first_apper(Variable(0)),
            Some(VecDeque::from(vec![l("a")]))
        );
    }

    #[test]
    fn sort_quantifiers() {
        use internal::Variable::*;
        use IKind as Kind;
        use IKind::Mono;
        use IType as Type;
        use IType::Int;
        use SemanticSig::*;

        let l = Label::from;

        assert_eq!(
            SemanticSig::default_atomic_term(Int).sort_quantifiers::<()>(vec![]),
            (vec![], Subst::from_iter(vec![]))
        );

        assert_eq!(
            AtomicType(Int, Mono).sort_quantifiers::<()>(vec![]),
            (vec![], Subst::from_iter(vec![]))
        );

        assert_eq!(
            AtomicType(Type::var(0), Mono).sort_quantifiers::<()>(vec![]),
            (vec![], Subst::from_iter(vec![]))
        );

        assert_eq!(
            AtomicType(Int, Mono).sort_quantifiers(vec![Mono]),
            (
                vec![Mono],
                Subst::from_iter(vec![(Variable(0), Type::var(0))])
            )
        );

        assert_eq!(
            AtomicType(Type::var(0), Mono).sort_quantifiers(vec![Mono]),
            (
                vec![Mono],
                Subst::from_iter(vec![(Variable(0), Type::var(0))])
            )
        );

        assert_eq!(
            AtomicType(Type::var(1), Mono).sort_quantifiers(vec![Mono]),
            (
                vec![Mono],
                Subst::from_iter(vec![(Variable(0), Type::var(0))])
            )
        );

        assert_eq!(
            SemanticSig::structure_sig(vec![(l("a"), AtomicType(Type::var(0), Mono))])
                .sort_quantifiers(vec![Mono]),
            (
                vec![Mono],
                Subst::from_iter(vec![(Variable(0), Type::var(0))])
            )
        );

        assert_eq!(
            SemanticSig::structure_sig(vec![
                (l("a"), AtomicType(Type::var(0), Mono)),
                (l("b"), AtomicType(Type::var(1), Mono)),
            ])
            .sort_quantifiers(vec![Mono, Mono]),
            (
                vec![Mono, Mono],
                Subst::from_iter(vec![
                    (Variable(0), Type::var(0)),
                    (Variable(1), Type::var(1)),
                ])
            )
        );

        assert_eq!(
            SemanticSig::structure_sig(vec![
                (l("b"), AtomicType(Type::var(0), Kind::fun(Mono, Mono))),
                (l("a"), AtomicType(Type::var(1), Mono)),
            ])
            .sort_quantifiers(vec![Mono, Kind::fun(Mono, Mono)]),
            (
                vec![Kind::fun(Mono, Mono), Mono],
                Subst::from_iter(vec![
                    (Variable(0), Type::var(1)),
                    (Variable(1), Type::var(0)),
                ])
            )
        );

        assert_eq!(
            SemanticSig::structure_sig(vec![
                (l("a"), AtomicType(Type::var(1), Kind::fun(Mono, Mono))),
                (l("b"), AtomicType(Type::var(0), Mono)),
                (l("c"), AtomicType(Type::var(1), Kind::fun(Mono, Mono))),
            ])
            .sort_quantifiers(vec![Kind::fun(Mono, Mono), Mono]),
            (
                vec![Mono, Kind::fun(Mono, Mono)],
                Subst::from_iter(vec![
                    (Variable(0), Type::var(1)),
                    (Variable(1), Type::var(0)),
                ])
            )
        );

        assert_eq!(
            SemanticSig::structure_sig(vec![
                (l("a"), AtomicType(Type::var(2), Kind::fun(Mono, Mono))),
                (l("b"), AtomicType(Type::var(0), Mono)),
                (l("c"), AtomicType(Type::var(1), Mono)),
            ])
            .sort_quantifiers(vec![Kind::fun(Mono, Mono), Mono, Mono]),
            (
                vec![Mono, Mono, Kind::fun(Mono, Mono)],
                Subst::from_iter(vec![
                    (Variable(0), Type::var(1)),
                    (Variable(1), Type::var(2)),
                    (Variable(2), Type::var(0)),
                ])
            )
        );
    }

    #[test]
    fn lifted_by() {
        use IKind as Kind;
        use IKind::Mono;

        fn sf(s: &str) -> StemFrom {
            StemFrom::from(Ident::from(s))
        }

        assert_eq!(vec![].lifted_by(&vec![]), vec![]);

        assert_eq!(vec![].lifted_by(&vec![(Mono, sf("b"))]), vec![]);

        assert_eq!(
            vec![(Mono, sf("a"))].lifted_by(&vec![]),
            vec![(Mono, sf("a"))]
        );

        assert_eq!(
            vec![(Mono, sf("a"))].lifted_by(&vec![(Mono, sf("b"))]),
            vec![(Kind::fun(Mono, Mono), sf("a"))]
        );

        assert_eq!(
            vec![(Mono, sf("a"))]
                .lifted_by(&vec![(Mono, sf("b")), (Kind::fun(Mono, Mono), sf("c"))]),
            vec![(
                Kind::fun(Kind::fun(Mono, Mono), Kind::fun(Mono, Mono)),
                sf("a")
            )]
        );

        assert_eq!(
            vec![(Mono, sf("a"))]
                .lifted_by(&vec![(Kind::fun(Mono, Mono), sf("c")), (Mono, sf("b"))]),
            vec![(
                Kind::fun(Mono, Kind::fun(Kind::fun(Mono, Mono), Mono)),
                sf("a")
            )]
        );

        assert_eq!(
            vec![(Mono, sf("a")), (Kind::fun(Mono, Mono), sf("d"))]
                .lifted_by(&vec![(Kind::fun(Mono, Mono), sf("c")), (Mono, sf("b"))]),
            vec![
                (
                    Kind::fun(Mono, Kind::fun(Kind::fun(Mono, Mono), Mono)),
                    sf("a")
                ),
                (
                    Kind::fun(
                        Mono,
                        Kind::fun(Kind::fun(Mono, Mono), Kind::fun(Mono, Mono))
                    ),
                    sf("d")
                )
            ]
        );
    }

    macro_rules! assert_skolemize {
        ($ssig:expr, $m:expr, $n:expr, $r:expr) => {{
            let mut ssig = $ssig;
            ssig.skolemize($m, $n);
            assert_eq!(ssig, $r);
        }};
    }

    #[test]
    fn skolemize() {
        use IType::Int;

        let var = IType::var;
        let app = IType::app;

        assert_skolemize!(
            SemanticSig::default_atomic_term(Int),
            0,
            0,
            SemanticSig::default_atomic_term(Int)
        );

        assert_skolemize!(
            SemanticSig::default_atomic_term(var(0)),
            0,
            0,
            SemanticSig::default_atomic_term(var(0))
        );
        assert_skolemize!(
            SemanticSig::default_atomic_term(var(0)),
            1,
            0,
            SemanticSig::default_atomic_term(var(0))
        );
        assert_skolemize!(
            SemanticSig::default_atomic_term(var(0)),
            0,
            1,
            SemanticSig::default_atomic_term(var(0))
        );
        assert_skolemize!(
            SemanticSig::default_atomic_term(var(0)),
            1,
            1,
            SemanticSig::default_atomic_term(app(var(1), var(0)))
        );

        assert_skolemize!(
            SemanticSig::default_atomic_term(var(1)),
            0,
            0,
            SemanticSig::default_atomic_term(var(1))
        );
        assert_skolemize!(
            SemanticSig::default_atomic_term(var(1)),
            1,
            0,
            SemanticSig::default_atomic_term(var(1))
        );
        assert_skolemize!(
            SemanticSig::default_atomic_term(var(1)),
            0,
            1,
            SemanticSig::default_atomic_term(var(1))
        );
        assert_skolemize!(
            SemanticSig::default_atomic_term(var(1)),
            1,
            1,
            SemanticSig::default_atomic_term(var(0))
        );

        assert_skolemize!(
            SemanticSig::default_atomic_term(var(0)),
            2,
            1,
            SemanticSig::default_atomic_term(app(app(var(2), var(0)), var(1)))
        );
        assert_skolemize!(
            SemanticSig::default_atomic_term(var(0)),
            1,
            2,
            SemanticSig::default_atomic_term(app(var(1), var(0)))
        );
        assert_skolemize!(
            SemanticSig::default_atomic_term(var(0)),
            2,
            2,
            SemanticSig::default_atomic_term(app(app(var(2), var(0)), var(1)))
        );

        assert_skolemize!(
            SemanticSig::default_atomic_term(var(1)),
            2,
            1,
            SemanticSig::default_atomic_term(var(0))
        );
        assert_skolemize!(
            SemanticSig::default_atomic_term(var(1)),
            1,
            2,
            SemanticSig::default_atomic_term(app(var(2), var(0)))
        );
        assert_skolemize!(
            SemanticSig::default_atomic_term(var(1)),
            2,
            2,
            SemanticSig::default_atomic_term(app(app(var(3), var(0)), var(1)))
        );
    }
}

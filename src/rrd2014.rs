//! Andreas Rossberg, Claudio V. Russo and Derek Dreyer.
//! F-ing modules.
//! Journal of Functional Programming, 24(5), 2014.

#![allow(dead_code)]

pub mod internal;
pub mod parser;

use std::collections::HashMap;
use std::convert::TryFrom;
use std::iter::FromIterator;

use failure::Fail;

use internal::EnvError;
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
    Int,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Abs(Ident, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Path(Path),
    Int(isize),
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
    Fun(Ident, Box<Sig>, Box<Sig>),
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
pub enum SemanticSig {
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

struct BindingInformation {
    t: ITerm,
    n: usize,
    ty: IType,
    w: Vec<ITerm>,
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
    Atomic(SemanticSigError),

    #[fail(display = "duplicate label: {:?}", _0)]
    DuplicateLabel(Label),

    #[fail(display = "{:?} is not subtype of {:?}", _0, _1)]
    NotSubtype(IType, IType),

    #[fail(display = "type mismatch: {:?} {:?}", _0, _1)]
    TypeMismatch(IType, IType),

    #[fail(display = "missing label: {:?}", _0)]
    MissingLabel(Label),
}

impl From<EnvError> for TypeError {
    fn from(e: EnvError) -> Self {
        TypeError::Env(e)
    }
}

impl From<SemanticSigError> for TypeError {
    fn from(e: SemanticSigError) -> Self {
        TypeError::Atomic(e)
    }
}

impl From<!> for TypeError {
    fn from(e: !) -> Self {
        e
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

impl Substitution for BindingInformation {
    fn apply(&mut self, s: &Subst) {
        // This is not verified to be correct.
        self.t.apply(s);
        self.ty.apply(s);
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

pub fn elaborate(m: Module) -> Result<(ITerm, AbstractSig, Vec<IKind>), TypeError> {
    let mut env = Env::default();
    let triple = m.elaborate(&mut env)?;
    Ok((triple.0, triple.1, env.get_generated_type_env()))
}

trait Subtype {
    type Error;

    fn subtype_of(&self, env: &mut Env, another: &Self) -> Result<ITerm, Self::Error>;
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

    fn get_atomic_term(self) -> Result<IType, SemanticSigError> {
        match self {
            SemanticSig::AtomicTerm(ty) => Ok(ty),
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
                Ok((f(id, AtomicTerm(ty)), s))
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
            Fun(ref id, ref domain, ref range) => {
                let enter_state = env.get_state();
                let (asig1, s1) = domain.elaborate(env)?;
                env.insert_types(asig1.0.qs.clone().into_iter().map(|(k, s)| (k, Some(s))));
                env.insert_value(Name::from(id.clone()), asig1.0.body.clone());
                let (asig2, s2) = range.elaborate(env)?;
                env.drop_values_state(1, enter_state);
                env.drop_types(asig1.0.qs.len());
                Ok((
                    Existential::from(SemanticSig::FunctorSig(
                        Universal::from(asig1).map(|ssig| Box::new(self::Fun(ssig, asig2))),
                    )),
                    s1.compose(s2),
                ))
            }
            _ => unimplemented!(),
        }
    }
}

impl Elaboration for Binding {
    type Output = (ITerm, Existential<HashMap<Label, SemanticSig>>, Subst);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Binding::*;
        use SemanticSig::*;
        match *self {
            Val(ref id, ref e) => {
                let (t, ty, s) = e.elaborate(env)?;
                Ok((
                    ITerm::record(vec![(
                        Label::from(id.clone()),
                        SemanticTerm::Term(t).into(),
                    )]),
                    Existential::from(HashMap::from_iter(vec![(
                        Label::from(id.clone()),
                        AtomicTerm(ty),
                    )])),
                    s,
                ))
            }
            Type(ref id, ref ty) => {
                let (ty, k, s) = ty
                    .elaborate(env)
                    .map_err(|e| TypeError::TypeBinding(id.clone(), Box::new(e)))?;
                Ok((
                    ITerm::record(vec![(
                        Label::from(id.clone()),
                        SemanticTerm::Type(ty.clone(), k.clone()).into(),
                    )]),
                    Existential::from(HashMap::from_iter(vec![(
                        Label::from(id.clone()),
                        AtomicType(ty, k),
                    )])),
                    s,
                ))
            }
            Module(ref id, ref m) => {
                let (t, asig, s) = m.elaborate(env)?;
                asig.0.body.atomic()?;
                Ok((
                    ITerm::unpack(
                        t,
                        asig.0.qs.len(),
                        asig.clone().into(),
                        ITerm::pack(
                            ITerm::record(vec![(Label::from(id.clone()), ITerm::var(0))]),
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
                ))
            }
            _ => unimplemented!(),
        }
    }
}

impl Elaboration for Module {
    type Output = (ITerm, AbstractSig, Subst);
    type Error = TypeError;

    #[allow(clippy::many_single_char_names)]
    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        use Module::*;
        match *self {
            Ident(ref id) => {
                let (ssig, v) = env.lookup_value_by_name(id.into())?;
                Ok((ITerm::Var(v), Existential::from(ssig), Subst::default()))
            }
            Seq(ref bs) => {
                let mut v = Vec::new();
                let mut ls = HashMap::new();
                let mut qs = Vec::new();
                let mut body = HashMap::new();
                let mut ret_subst = Subst::default();
                let mut n = 0;
                let enter_state = env.get_state();
                for b in bs {
                    let (t, ex, s) = b.elaborate(env)?;
                    n += 1;
                    let n0 = n;
                    ret_subst = ret_subst.compose(s.clone());
                    body.apply(&s);
                    v.apply(&s);
                    env.insert_types(ex.0.qs.clone().into_iter().map(|(k, s)| (k, Some(s))));
                    env.insert_dummy_value();
                    qs.extend(ex.0.qs.clone());
                    body.extend(ex.0.body.clone());
                    let mut w = Vec::new();
                    for (i, (l, ssig)) in ex.0.body.iter().enumerate() {
                        ls.insert(l.clone(), n0);
                        w.push(ITerm::proj(ITerm::var(i), Some(l.clone())));
                        n += 1;
                        env.insert_value(Name::try_from(l.clone()).unwrap(), ssig.clone());
                    }
                    v.push(BindingInformation {
                        t,
                        n: ex.0.qs.len(),
                        ty: IType::from(ex.map(SemanticSig::StructureSig)),
                        w,
                    });
                }
                env.drop_values_state(n, enter_state);
                env.drop_types(qs.len());
                let m = ls
                    .into_iter()
                    .flat_map(|(l, i)| Some((l.clone(), ITerm::proj(ITerm::var(n - i), Some(l)))));
                let t = v.into_iter().rfold(
                    ITerm::pack(
                        ITerm::record(m),
                        (0..qs.len()).map(IType::var).collect(),
                        qs.iter().map(|p| p.0.clone()),
                        SemanticSig::StructureSig(body.clone()).into(),
                    ),
                    |t0, BindingInformation { t, n, ty, w }| {
                        ITerm::unpack(t, n, ty, ITerm::let_in(w, t0))
                    },
                );
                Ok((
                    t,
                    Existential(Quantified {
                        qs,
                        body: SemanticSig::StructureSig(body),
                    }),
                    ret_subst,
                ))
            }
            Proj(ref m, ref id) => {
                let (t, asig, s) = m.elaborate(env)?;
                let asig0 = asig.clone().try_map::<_, _, TypeError, _>(|ssig| {
                    let mut m = ssig.get_structure()?;
                    m.remove(&id.into())
                        .ok_or_else(|| TypeError::MissingLabel(id.into()))
                })?;
                Ok((
                    ITerm::unpack(
                        t,
                        asig.0.qs.len(),
                        asig.clone().into(),
                        ITerm::pack(
                            ITerm::proj(ITerm::var(0), Some(id.into())),
                            (0..asig.0.qs.len()).map(IType::var).collect(),
                            asig.0.qs.iter().map(|p| p.0.clone()),
                            asig0.0.body.clone().into(),
                        ),
                    ),
                    asig0,
                    s,
                ))
            }
            Seal(ref id, ref sig) => {
                let (ssig, v) = env.lookup_value_by_name(id.into())?;
                let (asig, s) = sig.elaborate(env)?;
                let (t, tys) = ssig.r#match(env, &asig)?;
                Ok((
                    ITerm::pack(
                        ITerm::app(t, ITerm::Var(v)),
                        tys,
                        asig.0.qs.iter().map(|p| p.0.clone()),
                        asig.0.body.clone().into(),
                    ),
                    asig,
                    s,
                ))
            }
            _ => unimplemented!(),
        }
    }
}

impl Elaboration for Path {
    type Output = (ITerm, SemanticSig, Subst);
    type Error = TypeError;

    fn elaborate(&self, env: &mut Env) -> Result<Self::Output, Self::Error> {
        let (t, asig, s) = self.0.elaborate(env)?;
        // Need shift?
        IType::from(asig.0.body.clone())
            .kind_of(env)
            .map_err(TypeError::KindError)?
            .mono()
            .map_err(TypeError::NotMono)?;
        Ok((
            ITerm::unpack(t, asig.0.qs.len(), asig.clone().into(), ITerm::var(0)),
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

impl Subtype for SemanticSig {
    type Error = TypeError;

    fn subtype_of(&self, env: &mut Env, another: &Self) -> Result<ITerm, Self::Error> {
        use SemanticSig::*;
        match (self, another) {
            (&AtomicTerm(ref ty1), &AtomicTerm(ref ty2)) => {
                let t = ty1.subtype_of(env, ty2)?;
                Ok(ITerm::abs(
                    IType::from(AtomicTerm(ty1.clone())),
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
            _ => unimplemented!(),
        }
    }
}

impl Subtype for AbstractSig {
    type Error = TypeError;

    fn subtype_of(&self, env: &mut Env, another: &Self) -> Result<ITerm, Self::Error> {
        env.insert_types(self.0.qs.clone().into_iter().map(|(k, s)| (k, Some(s))));
        let ty: IType = self.clone().into();
        let (t, tys) = self.0.body.r#match(env, another)?;
        Ok(ITerm::abs(
            ty.clone(),
            ITerm::unpack(
                ITerm::var(0),
                self.0.qs.len(),
                ty,
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

    fn infer(&self, env: &mut Env) -> Result<(ITerm, IType, Subst), TypeError> {
        use Expr::*;
        use IKind::*;
        match *self {
            Abs(ref id, ref e) => {
                let v = env.fresh_type_variable(Mono);
                let mut ty0 = IType::Var(v);
                let name = Name::from(id.clone());
                let enter_state = env.get_state();
                env.insert_value(name.clone(), SemanticSig::AtomicTerm(ty0.clone()));
                let (t, ty, s) = e.infer(env)?;
                env.drop_values_state(1, enter_state);
                ty0.apply(&s);
                Ok((
                    ITerm::abs(SemanticSig::AtomicTerm(ty0.clone()).into(), t),
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
            Int(n) => Ok((ITerm::Int(n), IType::Int, Subst::default())),
            Path(ref p) => {
                let (t, ssig, s) = p.elaborate(env)?;
                let ty = ssig.get_atomic_term()?;
                Ok((t, ty, s))
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

    fn lookup_instantiation(&self, ssig: &SemanticSig, v: internal::Variable) -> Option<IType> {
        use SemanticSig::*;
        match (self, ssig) {
            (&AtomicType(ref ty1, _), &AtomicType(ref ty2, _)) => {
                // Kind equality is later tested (maybe).
                match *ty2 {
                    IType::Var(v0) if v0 == v => Some(ty1.clone()),
                    _ => None,
                }
            }
            (&StructureSig(ref m1), &StructureSig(ref m2)) => {
                for (l, ssig2) in m2.iter() {
                    if let Some(ssig1) = m1.get(l) {
                        if let Some(ty) = ssig1.lookup_instantiation(ssig2, v) {
                            return Some(ty);
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Looks up instantiations.
    /// Assumes at least `ssig` is *explicit* (see section 5.2).
    fn lookup_instantiations(&self, ssig: &SemanticSig, vs: Vec<internal::Variable>) -> Vec<IType> {
        vs.iter()
            .map(|v| self.lookup_instantiation(ssig, *v).expect("not explicit"))
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
}

impl Sig {
    fn path(m: Module) -> Self {
        Sig::Path(Path::from(m))
    }

    fn fun(id: Ident, sig1: Sig, sig2: Sig) -> Self {
        Sig::Fun(id, Box::new(sig1), Box::new(sig2))
    }
}

impl Module {
    fn proj(m: Module, id: Ident) -> Self {
        Module::Proj(Box::new(m), id)
    }

    fn fun(id: Ident, sig: Sig, m: Module) -> Self {
        Module::Fun(id, sig, Box::new(m))
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
        use SemanticSig::*;

        assert_elaborate_ok_2!(
            Val(Ident::from("x"), Expr::Int(23)),
            (
                ITerm::record(vec![(Label::from("x"), ITerm::Int(23))]),
                Existential::from(HashMap::from_iter(vec![(
                    Label::from("x"),
                    AtomicTerm(IType::Int)
                )]))
            )
        );

        assert_elaborate_ok_2!(
            Val(Ident::from("x"), Expr::abs(Ident::from("y"), Expr::Int(22))),
            (
                ITerm::record(vec![(
                    Label::from("x"),
                    ITerm::abs(IType::generated_var(0), ITerm::Int(22))
                )]),
                Existential::from(HashMap::from_iter(vec![(
                    Label::from("x"),
                    AtomicTerm(IType::fun(IType::generated_var(0), IType::Int))
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
                (l("y"), SemanticSig::AtomicTerm(IType::Int)),
                (
                    l("f"),
                    SemanticSig::AtomicTerm(IType::fun(IType::Int, IType::Int))
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
            Existential::from(HashMap::from_iter(Some((l("a"), AtomicTerm(IType::Int)))))
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
                AtomicTerm(IType::Int)
            )])))
        );

        assert_elaborate_ok_1!(
            Seq(vec![Val(id("a"), Type::Int), Val(id("b"), Type::Int)]),
            Existential::from(StructureSig(HashMap::from_iter(vec![
                (l("a"), AtomicTerm(IType::Int)),
                (l("b"), AtomicTerm(IType::Int))
            ])))
        );

        assert_elaborate_ok_1!(
            Seq(vec![Val(id("a"), Type::Int), ManType(id("b"), Type::Int)]),
            Existential::from(StructureSig(HashMap::from_iter(vec![
                (l("a"), AtomicTerm(IType::Int)),
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
            AtomicTerm(Int),
            AtomicTerm(Int),
            Term::abs(Int, Term::app(Term::abs(Int, Term::var(0)), Term::var(0)))
        );

        assert_subtype_err!(
            AtomicTerm(Int),
            AtomicTerm(Type::fun(Int, Int)),
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
            SemanticSig::structure_sig(Some((l("a"), AtomicTerm(Int)))),
            SemanticSig::structure_sig(None),
            Term::abs(Type::record(Some((l("a"), Int))), Term::record(None))
        );

        assert_subtype_ok!(
            SemanticSig::structure_sig(Some((l("a"), AtomicTerm(Int)))),
            SemanticSig::structure_sig(Some((l("a"), AtomicTerm(Int)))),
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
                (l("a"), AtomicTerm(Int)),
                (l("b"), AtomicTerm(Int)),
                (l("c"), AtomicTerm(Int))
            ]),
            SemanticSig::structure_sig(vec![(l("a"), AtomicTerm(Int)), (l("b"), AtomicTerm(Int))]),
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
}

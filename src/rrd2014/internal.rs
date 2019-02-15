//! The internal language.

use std::borrow::Cow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::convert::TryFrom;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::iter::FromIterator;

use failure::Fail;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name(String);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Label {
    Label(Name),
    Val,
    Typ,
    Sig,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Variable(usize);

#[derive(Clone, Debug, PartialEq)]
pub struct Record<T>(HashMap<Label, T>);

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    Mono,
    Fun(Box<Kind>, Box<Kind>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Var(Variable),
    Fun(Box<Type>, Box<Type>),
    Record(Record<Type>),

    /// A universal type.
    Forall(Kind, Box<Type>),

    /// An existential type.
    Some(Kind, Box<Type>),

    Abs(Kind, Box<Type>),
    App(Box<Type>, Box<Type>),
    Int,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Var(Variable),
    Abs(Type, Box<Term>),
    App(Box<Term>, Box<Term>),
    Record(Record<Term>),

    /// A projection from a record via a label.
    Proj(Box<Term>, Label),

    /// A polymorphic function.
    Poly(Kind, Box<Term>),

    /// An instantiation.
    Inst(Box<Term>, Type),

    /// An existential introduction.
    /// `Pack(witness, t, ty)` represents *pack [`witness`, `t`] as `ty`*.
    Pack(Type, Box<Term>, Type),

    /// An existential elimination.
    Unpack(Box<Term>, Box<Term>),

    Int(isize),
}

#[derive(Debug, PartialEq)]
pub struct Env<T, S> {
    tenv: Vec<(Kind, S)>,
    venv: Vec<Option<T>>,

    /// A name-to-index map.
    nmap: HashMap<Name, usize>,
}

pub struct EnvState(HashMap<Name, usize>);

#[derive(Clone, Debug, PartialEq)]
pub struct Context<'a> {
    tenv: Vec<Cow<'a, Kind>>,
    venv: Vec<Cow<'a, Type>>,
}

#[derive(Debug, Fail, PartialEq)]
pub enum KindError {
    #[fail(display = "kind mismatch: {:?} and {:?}", _0, _1)]
    KindMismatch(Kind, Kind),

    #[fail(display = "not function kind: {:?}", _0)]
    NotFunction(Kind),

    #[fail(display = "type {:?} does not have mono kind: {}", _0, _1)]
    NotMono(Type, NotMonoError),

    #[fail(display = "label {:?} in record: {}", _0, _1)]
    Record(Label, Box<KindError>),

    #[fail(display = "environment error: {}", _0)]
    Env(EnvError),
}

#[derive(Debug, Fail, PartialEq)]
pub enum TypeError {
    #[fail(display = "type mismatch: {:?} and {:?}", _0, _1)]
    TypeMismatch(Type, Type),

    #[fail(display = "not function type: {:?}", _0)]
    NotFunction(Type),

    #[fail(display = "missing label: {:?}", _0)]
    MissingLabel(Label),

    #[fail(display = "not record type: {:?}", _0)]
    NotRecord(Type),

    #[fail(display = "not universal type: {:?}", _0)]
    NotForall(Type),

    #[fail(display = "not existential type: {:?}", _0)]
    NotSome(Type),

    #[fail(display = "environment error: {}", _0)]
    Env(EnvError),

    #[fail(display = "kind error: {}", _0)]
    KindError(KindError),
}

#[derive(Clone, Default)]
pub struct Subst(HashMap<Variable, Type>);

pub trait Substitution {
    fn apply(&mut self, s: &Subst);
}

impl<T, S> Default for Env<T, S> {
    fn default() -> Self {
        Env {
            tenv: vec![],
            venv: vec![],
            nmap: HashMap::new(),
        }
    }
}

pub trait Shift {
    fn shift_above(&mut self, c: usize, d: isize);

    fn shift(&mut self, d: isize) {
        self.shift_above(0, d)
    }
}

impl Shift for Type {
    fn shift_above(&mut self, c: usize, d: isize) {
        let f = |c0, v: Variable| {
            if c0 <= v.0 {
                Type::Var(v.add(d))
            } else {
                Type::Var(v)
            }
        };
        self.map(&f, c)
    }
}

impl Shift for Kind {
    fn shift_above(&mut self, _: usize, _: isize) {}
}

impl<T: Shift> Shift for Box<T> {
    fn shift_above(&mut self, c: usize, d: isize) {
        (**self).shift_above(c, d)
    }
}

impl<T: Shift> Shift for Option<T> {
    fn shift_above(&mut self, c: usize, d: isize) {
        if let Some(x) = self.as_mut() {
            x.shift_above(c, d);
        }
    }
}

impl<T: Shift> Shift for Vec<T> {
    fn shift_above(&mut self, c: usize, d: isize) {
        self.iter_mut().for_each(|x| {
            x.shift_above(c, d);
        });
    }
}

impl<K: Eq + Hash, T: Shift, S: BuildHasher> Shift for HashMap<K, T, S> {
    fn shift_above(&mut self, c: usize, d: isize) {
        self.values_mut().for_each(|x| {
            x.shift_above(c, d);
        });
    }
}

impl<T: Substitution> Substitution for Option<T> {
    fn apply(&mut self, s: &Subst) {
        self.iter_mut().for_each(|x| x.apply(s));
    }
}

impl<T: Substitution> Substitution for Vec<T> {
    fn apply(&mut self, s: &Subst) {
        self.iter_mut().for_each(|x| x.apply(s));
    }
}

impl<T: Substitution> Substitution for (T, T) {
    fn apply(&mut self, s: &Subst) {
        self.0.apply(s);
        self.1.apply(s);
    }
}

impl<T: Substitution> Substitution for Record<T> {
    fn apply(&mut self, s: &Subst) {
        self.0.values_mut().for_each(|x| x.apply(s));
    }
}

impl Substitution for Kind {
    fn apply(&mut self, _: &Subst) {}
}

impl Substitution for Type {
    fn apply(&mut self, s: &Subst) {
        use Type::*;
        match *self {
            Var(ref mut v) => {
                if let Option::Some(ty) = s.0.get(v) {
                    *self = ty.clone();
                }
            }
            Fun(ref mut ty1, ref mut ty2) => {
                ty1.apply(s);
                ty2.apply(s);
            }
            Record(ref mut r) => r.apply(s),
            Forall(ref mut k, ref mut ty) => {
                k.apply(s);
                ty.apply(s); // The possibility of variable capture.
            }
            Some(ref mut k, ref mut ty) => {
                k.apply(s);
                ty.apply(s); // The possibility of variable capture.
            }
            Abs(ref mut k, ref mut ty) => {
                k.apply(s);
                ty.apply(s); // The possibility of variable capture.
            }
            App(ref mut ty1, ref mut ty2) => {
                ty1.apply(s);
                ty2.apply(s);
            }
            Int => (),
        }
    }
}

impl Substitution for Term {
    fn apply(&mut self, s: &Subst) {
        use Term::*;
        match *self {
            Var(_) | Int(_) => (),
            Abs(ref mut ty, ref mut t) => {
                ty.apply(s);
                t.apply(s);
            }
            App(ref mut t1, ref mut t2) => {
                t1.apply(s);
                t2.apply(s);
            }
            Record(ref mut r) => r.apply(s),
            Proj(ref mut t, _) => t.apply(s),
            Poly(ref mut k, ref mut t) => {
                k.apply(s);
                t.apply(s); // The possibility of variable capture.
            }
            Inst(ref mut t, ref mut ty) => {
                t.apply(s);
                ty.apply(s);
            }
            Pack(ref mut ty1, ref mut t, ref mut ty2) => {
                ty1.apply(s);
                t.apply(s);
                ty2.apply(s);
            }
            Unpack(ref mut t1, ref mut t2) => {
                t1.apply(s);
                t2.apply(s); // The possibility of variable capture.
            }
        }
    }
}

impl Substitution for Subst {
    fn apply(&mut self, s: &Subst) {
        self.0.values_mut().for_each(|ty| ty.apply(s));
    }
}

impl<T: Substitution, S> Substitution for Env<T, S> {
    fn apply(&mut self, s: &Subst) {
        self.tenv.iter_mut().for_each(|p| p.0.apply(s));
        self.venv.iter_mut().for_each(|x| x.apply(s));
    }
}

impl From<EnvError> for TypeError {
    fn from(e: EnvError) -> Self {
        TypeError::Env(e)
    }
}

impl From<KindError> for TypeError {
    fn from(e: KindError) -> Self {
        TypeError::KindError(e)
    }
}

impl From<super::SemanticSig> for Type {
    fn from(st: super::SemanticSig) -> Self {
        use super::SemanticSig::*;
        match st {
            AtomicTerm(ty) => Type::record(vec![(Label::Val, ty)]),
            AtomicType(mut ty, k) => {
                ty.shift(1);
                Type::record(vec![(
                    Label::Typ,
                    Type::forall(
                        vec![Kind::fun(k, Kind::Mono)],
                        Type::fun(
                            Type::app(Type::var(0), ty.clone()),
                            Type::app(Type::var(0), ty),
                        ),
                    ),
                )])
            }
            AtomicSig(asig) => {
                let ty = Type::from(asig);
                Type::record(vec![(Label::Sig, Type::fun(ty.clone(), ty))])
            }
            StructureSig(m) => Type::Record(
                m.into_iter()
                    .map(|(l, ssig)| (l, Type::from(ssig)))
                    .collect(),
            ),
            FunctorSig(u) => u.into(),
        }
    }
}

impl<T: Into<Type>> From<super::Existential<T>> for Type {
    fn from(ex: super::Existential<T>) -> Self {
        Type::some(
            ex.0.qs.into_iter().map(|p| p.0).collect::<Vec<_>>(),
            ex.0.body.into(),
        )
    }
}

impl<T: Into<Type>> From<super::Universal<T>> for Type {
    fn from(u: super::Universal<T>) -> Self {
        Type::forall(
            u.0.qs.into_iter().map(|p| p.0).collect::<Vec<_>>(),
            u.0.body.into(),
        )
    }
}

impl From<super::Fun> for Type {
    fn from(f: super::Fun) -> Self {
        Type::fun(f.0.into(), f.1.into())
    }
}

impl<T: Into<Type>> From<Box<T>> for Type {
    fn from(x: Box<T>) -> Self {
        (*x).into()
    }
}

impl From<super::SemanticTerm> for Term {
    fn from(st: super::SemanticTerm) -> Self {
        use super::SemanticTerm as ST;
        match st {
            ST::Term(t) => Term::record(vec![(Label::Val, t)]),
            ST::Type(mut ty, k) => {
                ty.shift(1);
                Term::record(vec![(
                    Label::Typ,
                    Term::poly(
                        vec![Kind::fun(k, Kind::Mono)],
                        Term::abs(Type::app(Type::var(0), ty), Term::var(0)),
                    ),
                )])
            }
            ST::Sig(asig) => Term::record(vec![(
                Label::Sig,
                Term::abs(Type::from(asig), Term::var(0)),
            )]),
        }
    }
}

impl From<super::Ident> for Label {
    fn from(id: super::Ident) -> Self {
        Label::Label(Name::from(id))
    }
}

impl<'a> From<&'a super::Ident> for Label {
    fn from(id: &'a super::Ident) -> Self {
        Label::Label(Name::from(id.clone()))
    }
}

impl From<Name> for Label {
    fn from(name: Name) -> Self {
        Label::Label(name)
    }
}

impl<'a> From<&'a str> for Label {
    fn from(s: &str) -> Self {
        Label::Label(Name::from(s))
    }
}

impl<'a> From<&'a str> for Name {
    fn from(s: &str) -> Self {
        Name(s.to_string())
    }
}

impl From<String> for Name {
    fn from(s: String) -> Self {
        Name(s)
    }
}

impl From<super::Ident> for Name {
    fn from(id: super::Ident) -> Self {
        id.0
    }
}

impl<'a> From<&'a super::Ident> for &'a Name {
    fn from(id: &'a super::Ident) -> Self {
        &id.0
    }
}

impl TryFrom<Label> for Name {
    type Error = String;

    fn try_from(l: Label) -> Result<Self, Self::Error> {
        match l {
            Label::Label(name) => Ok(name),
            _ => Err(format!("could not convert to name: {:?}", l)),
        }
    }
}

impl Name {
    pub fn new(s: String) -> Self {
        Name(s)
    }
}

impl Variable {
    pub fn new(n: usize) -> Self {
        Variable(n)
    }

    fn add(self, d: isize) -> Self {
        Variable(
            usize::try_from(isize::try_from(self.0).unwrap() + d)
                .unwrap_or_else(|_| panic!("negative index: {:?} and {}", self, d)),
        )
    }
}

impl FromIterator<(Variable, Type)> for Subst {
    fn from_iter<I: IntoIterator<Item = (Variable, Type)>>(iter: I) -> Self {
        Subst(HashMap::from_iter(iter))
    }
}

impl<T> FromIterator<(Label, T)> for Record<T> {
    fn from_iter<I: IntoIterator<Item = (Label, T)>>(iter: I) -> Self {
        Record(HashMap::from_iter(iter))
    }
}

impl Record<Type> {
    fn map<F>(&mut self, f: &F, c: usize)
    where
        F: Fn(usize, Variable) -> Type,
    {
        self.0.values_mut().for_each(|ty| ty.map(f, c));
    }
}

#[derive(Debug, Fail, PartialEq)]
#[fail(display = "not mono kind: {:?}", _0)]
pub struct NotMonoError(Kind);

impl Kind {
    pub fn fun(k1: Kind, k2: Kind) -> Self {
        Kind::Fun(Box::new(k1), Box::new(k2))
    }

    fn map<F>(&mut self, _: &F, _: usize) {}

    pub fn mono(&self) -> Result<(), NotMonoError> {
        match *self {
            Kind::Mono => Ok(()),
            _ => Err(NotMonoError(self.clone())),
        }
    }

    fn eta_reducible(&self, _: usize) -> bool {
        true
    }

    fn equal(&self, k: &Kind) -> bool {
        self == k
    }
}

impl Type {
    pub fn var(n: usize) -> Self {
        Type::Var(Variable(n))
    }

    pub fn fun(ty1: Type, ty2: Type) -> Self {
        Type::Fun(Box::new(ty1), Box::new(ty2))
    }

    pub fn app(ty1: Type, ty2: Type) -> Self {
        Type::App(Box::new(ty1), Box::new(ty2))
    }

    pub fn record<I: IntoIterator<Item = (Label, Type)>>(iter: I) -> Self {
        Type::Record(Record::from_iter(iter))
    }

    /// Creates an n-ary existential type.
    ///
    /// # Examples
    ///
    /// ```
    /// use modules::rrd2014::internal::*;
    /// use Type::Int;
    /// use Kind::*;
    ///
    /// assert_eq!(Type::some(None, Int), Int);
    ///
    /// assert_eq!(
    ///     Type::some(vec![Mono], Int),
    ///     Type::Some(Mono, Box::new(Int))
    /// );
    ///
    /// assert_eq!(
    ///     Type::some(vec![Mono, Mono], Int),
    ///     Type::Some(Mono, Box::new(Type::Some(Mono, Box::new(Int))))
    /// );
    ///
    /// assert_eq!(
    ///     Type::some(vec![Kind::fun(Mono, Mono), Mono], Int),
    ///     Type::Some(Mono, Box::new(Type::Some(Kind::fun(Mono, Mono), Box::new(Int))))
    /// );
    /// ```
    pub fn some<I>(ks: I, ty: Type) -> Self
    where
        I: IntoIterator<Item = Kind>,
    {
        ks.into_iter().fold(ty, |ty, k| Type::Some(k, Box::new(ty)))
    }

    /// Creates an n-ary universal type.
    ///
    /// # Examples
    ///
    /// ```
    /// use modules::rrd2014::internal::*;
    /// use Type::Int;
    /// use Kind::*;
    ///
    /// assert_eq!(Type::forall(None, Int), Int);
    ///
    /// assert_eq!(
    ///     Type::forall(vec![Mono], Int),
    ///     Type::Forall(Mono, Box::new(Int))
    /// );
    ///
    /// assert_eq!(
    ///     Type::forall(vec![Mono, Mono], Int),
    ///     Type::Forall(Mono, Box::new(Type::Forall(Mono, Box::new(Int))))
    /// );
    ///
    /// assert_eq!(
    ///     Type::forall(vec![Kind::fun(Mono, Mono), Mono], Int),
    ///     Type::Forall(Mono, Box::new(Type::Forall(Kind::fun(Mono, Mono), Box::new(Int))))
    /// );
    /// ```
    pub fn forall<I>(ks: I, ty: Type) -> Self
    where
        I: IntoIterator<Item = Kind>,
    {
        ks.into_iter()
            .fold(ty, |ty, k| Type::Forall(k, Box::new(ty)))
    }

    /// Creates an n-ary type-level lambda abstraction.
    ///
    /// # Examples
    ///
    /// ```
    /// use modules::rrd2014::internal::*;
    /// use Type::Int;
    /// use Kind::*;
    ///
    /// assert_eq!(Type::abs(None, Int), Int);
    ///
    /// assert_eq!(
    ///     Type::abs(vec![Mono], Int),
    ///     Type::Abs(Mono, Box::new(Int))
    /// );
    ///
    /// assert_eq!(
    ///     Type::abs(vec![Mono, Mono], Int),
    ///     Type::Abs(Mono, Box::new(Type::Abs(Mono, Box::new(Int))))
    /// );
    ///
    /// assert_eq!(
    ///     Type::abs(vec![Kind::fun(Mono, Mono), Mono], Int),
    ///     Type::Abs(Mono, Box::new(Type::Abs(Kind::fun(Mono, Mono), Box::new(Int))))
    /// );
    /// ```
    pub fn abs<I>(ks: I, ty: Type) -> Self
    where
        I: IntoIterator<Item = Kind>,
    {
        ks.into_iter().fold(ty, |ty, k| Type::Abs(k, Box::new(ty)))
    }

    fn map<F>(&mut self, f: &F, c: usize)
    where
        F: Fn(usize, Variable) -> Type,
    {
        use Type::*;
        match *self {
            Var(v) => {
                let ty = f(c, v);
                *self = ty;
            }
            Fun(ref mut ty1, ref mut ty2) => {
                ty1.map(f, c);
                ty2.map(f, c);
            }
            Record(ref mut r) => r.map(f, c),
            Forall(ref mut k, ref mut ty) => {
                k.map(f, c); // Currently, kinds do not depend on types, though.
                ty.map(f, c + 1);
            }
            Some(ref mut k, ref mut ty) => {
                k.map(f, c); // Currently, kinds do not depend on types, though.
                ty.map(f, c + 1);
            }
            Abs(ref mut k, ref mut ty) => {
                k.map(f, c); // Currently, kinds do not depend on types, though.
                ty.map(f, c + 1);
            }
            App(ref mut ty1, ref mut ty2) => {
                ty1.map(f, c);
                ty2.map(f, c);
            }
            Int => (),
        }
    }

    fn subst(&mut self, j: usize, ty: &Type) {
        let f = |c: usize, v: Variable| {
            if c + j == v.0 {
                let mut ty = ty.clone();
                ty.shift(isize::try_from(c).unwrap());
                ty
            } else {
                Type::Var(v)
            }
        };
        self.map(&f, 0)
    }

    fn subst_top(&mut self, ty: &mut Type) {
        ty.shift(1);
        self.subst(0, ty);
        self.shift(-1);
    }

    fn subst_shift(&mut self, j: usize, ty: &Type, d: isize) {
        let f = |c: usize, v: Variable| {
            if c + j == v.0 {
                let mut ty = ty.clone();
                ty.shift(isize::try_from(c).unwrap() + d);
                ty
            } else {
                Type::Var(v)
            }
        };
        self.map(&f, 0)
    }

    fn ftv(&self) -> HashSet<Variable> {
        use Type::*;
        match *self {
            Var(v) => HashSet::from_iter(vec![v]),
            Fun(ref ty1, ref ty2) => {
                let mut s = ty1.ftv();
                s.extend(ty2.ftv());
                s
            }
            Record(ref r) => r.0.values().flat_map(|ty| ty.ftv()).collect(),
            App(ref ty1, ref ty2) => {
                let mut s = ty1.ftv();
                s.extend(ty2.ftv());
                s
            }
            Int => HashSet::new(),
            _ => unimplemented!(),
        }
    }

    /// System F type equality.
    pub fn equal(&self, ty: &Type) -> bool {
        // TODO: Make it efficient.
        self.clone().reduce() == ty.clone().reduce()
    }

    fn reduce(self) -> Self {
        use Type::*;
        match self {
            Var(_) | Int => self,
            Fun(ty1, ty2) => Type::fun(ty1.reduce(), ty2.reduce()),
            Record(r) => Type::record(r.0.into_iter().map(|(l, ty)| (l, ty.reduce()))),
            // TODO: Is there any case where kinds depends on types which are sensible about
            // beta-eta equivalence?
            Forall(k, ty) => Type::forall(vec![k], ty.reduce()),
            Some(k, ty) => Type::some(vec![k], ty.reduce()),
            Abs(k, ty) => match ty.reduce() {
                App(mut ty1, ty2) if *ty2 == Var(Variable(0)) && ty1.eta_reducible(0) => {
                    ty1.shift(-1);
                    *ty1
                }
                ty => Type::abs(vec![k], ty),
            },
            App(ty1, ty2) => {
                let mut ty2 = ty2.reduce();
                match ty1.reduce() {
                    // The kind is ignored.
                    Abs(_, mut ty1) => {
                        ty2.shift(1);
                        ty1.subst(0, &ty2);
                        ty1.shift(-1);
                        ty1.reduce() // Well-kinded types may terminate (no proof, though).
                    }
                    ty1 => Type::app(ty1, ty2),
                }
            }
        }
    }

    fn eta_reducible(&self, n: usize) -> bool {
        use Type::*;
        match *self {
            Var(v) => v.0 != n,
            Fun(ref ty1, ref ty2) => ty1.eta_reducible(n) && ty2.eta_reducible(n),
            Record(ref r) => r.0.values().all(|ty| ty.eta_reducible(n)),
            Forall(ref k, ref ty) => k.eta_reducible(n + 1) && ty.eta_reducible(n + 1),
            Some(ref k, ref ty) => k.eta_reducible(n + 1) && ty.eta_reducible(n + 1),
            Abs(ref k, ref ty) => k.eta_reducible(n + 1) && ty.eta_reducible(n + 1),
            App(ref ty1, ref ty2) => ty1.eta_reducible(n) && ty2.eta_reducible(n),
            Int => true,
        }
    }

    pub fn kind_of<T: Shift, S: Clone + Default>(
        &self,
        env: &mut Env<T, S>,
    ) -> Result<Kind, KindError> {
        use Kind::Mono;
        use Type::*;
        match *self {
            Var(v) => Ok(env.lookup_type(v).map_err(KindError::Env)?.0),
            Fun(ref ty1, ref ty2) => {
                let k1 = ty1.kind_of(env)?;
                k1.mono().map_err(|e| KindError::NotMono(*ty1.clone(), e))?;
                let k2 = ty2.kind_of(env)?;
                k2.mono().map_err(|e| KindError::NotMono(*ty2.clone(), e))?;
                Ok(Mono)
            }
            Record(ref r) => {
                r.0.iter().try_for_each(|(l, ty)| -> Result<_, KindError> {
                    ty.kind_of(env)?.mono().map_err(|e| {
                        KindError::Record(l.clone(), Box::new(KindError::NotMono(ty.clone(), e)))
                    })?;
                    Ok(())
                })?;
                Ok(Mono)
            }
            Forall(ref k, ref ty) | Some(ref k, ref ty) => {
                env.insert_type(k.clone(), S::default());
                ty.kind_of(env)?
                    .mono()
                    .map_err(|e| KindError::NotMono(*ty.clone(), e))?;
                env.drop_type();
                Ok(Mono)
            }
            Abs(ref k1, ref ty) => {
                env.insert_type(k1.clone(), S::default());
                let k2 = ty.kind_of(env)?;
                env.drop_type();
                Ok(Kind::fun(k1.clone(), k2))
            }
            App(ref ty1, ref ty2) => {
                let k1 = ty1.kind_of(env)?;
                let k2 = ty2.kind_of(env)?;
                match k1 {
                    Kind::Fun(k11, k12) => {
                        if *k11 == k2 {
                            Ok(*k12)
                        } else {
                            Err(KindError::KindMismatch(*k11, k2))
                        }
                    }
                    _ => Err(KindError::NotFunction(k1)),
                }
            }
            Int => Ok(Mono),
        }
    }
}

impl Term {
    pub fn var(n: usize) -> Self {
        Term::Var(Variable(n))
    }

    pub fn abs(ty: Type, t: Term) -> Self {
        Term::Abs(ty, Box::new(t))
    }

    pub fn app(t1: Term, t2: Term) -> Self {
        Term::App(Box::new(t1), Box::new(t2))
    }

    pub fn record<I: IntoIterator<Item = (Label, Term)>>(iter: I) -> Self {
        Term::Record(Record::from_iter(iter))
    }

    /// Creates a successive projection.
    ///
    /// # Examples
    ///
    /// ```
    /// use modules::rrd2014::internal::*;
    /// use Term::Int;
    ///
    /// assert_eq!(Term::proj(Int(0), None), Int(0));
    ///
    /// assert_eq!(
    ///     Term::proj(Int(1), vec![Label::from("a")]),
    ///     Term::Proj(Box::new(Int(1)), Label::from("a"))
    /// );
    ///
    /// assert_eq!(
    ///     Term::proj(Int(1), vec![Label::from("r"), Label::from("u")]),
    ///     Term::Proj(Box::new(Term::Proj(Box::new(Int(1)), Label::from("r"))), Label::from("u"))
    /// );
    ///
    /// assert_eq!(
    ///     Term::proj(Term::var(800), vec![Label::Sig, Label::from("u")]),
    ///     Term::Proj(Box::new(Term::Proj(Box::new(Term::var(800)), Label::Sig)), Label::from("u"))
    /// );
    /// ```
    pub fn proj<I>(t: Term, ls: I) -> Self
    where
        I: IntoIterator<Item = Label>,
    {
        ls.into_iter().fold(t, |t, l| Term::Proj(Box::new(t), l))
    }

    /// Creates an n-ary polymorphic function.
    ///
    /// # Examples
    ///
    /// ```
    /// use modules::rrd2014::internal::*;
    /// use Term::Int;
    /// use Kind::*;
    ///
    /// assert_eq!(Term::poly(None, Int(0)), Int(0));
    ///
    /// assert_eq!(
    ///     Term::poly(vec![Mono], Int(1)),
    ///     Term::Poly(Mono, Box::new(Int(1)))
    /// );
    ///
    /// assert_eq!(
    ///     Term::poly(vec![Mono, Mono], Int(1)),
    ///     Term::Poly(Mono, Box::new(Term::Poly(Mono, Box::new(Int(1)))))
    /// );
    ///
    /// assert_eq!(
    ///     Term::poly(vec![Mono, Kind::fun(Mono, Mono)], Int(8)),
    ///     Term::Poly(Kind::fun(Mono, Mono), Box::new(Term::Poly(Mono, Box::new(Int(8)))))
    /// );
    /// ```
    pub fn poly<I>(ks: I, t: Term) -> Self
    where
        I: IntoIterator<Item = Kind>,
    {
        ks.into_iter().fold(t, |t, k| Term::Poly(k, Box::new(t)))
    }

    /// Creates an n-ary instantiation.
    ///
    /// # Examples
    ///
    /// ```
    /// use modules::rrd2014::internal::*;
    /// use Term::Int;
    ///
    /// assert_eq!(Term::inst(Int(0), None), Int(0));
    ///
    /// assert_eq!(
    ///     Term::inst(Int(1), vec![Type::Int]),
    ///     Term::Inst(Box::new(Int(1)), Type::Int)
    /// );
    ///
    /// assert_eq!(
    ///     Term::inst(Int(1), vec![Type::Int, Type::Int]),
    ///     Term::Inst(Box::new(Term::Inst(Box::new(Int(1)), Type::Int)), Type::Int)
    /// );
    ///
    /// assert_eq!(
    ///     Term::inst(Int(1), vec![Type::fun(Type::Int, Type::Int), Type::Int]),
    ///     Term::Inst(
    ///         Box::new(Term::Inst(Box::new(Int(1)), Type::fun(Type::Int, Type::Int))),
    ///         Type::Int
    ///     )
    /// );
    /// ```
    pub fn inst<I>(t: Term, tys: I) -> Self
    where
        I: IntoIterator<Item = Type>,
    {
        tys.into_iter().fold(t, |t, ty| Term::Inst(Box::new(t), ty))
    }

    /// Creates an n-ary let-expression.
    ///
    /// # Examples
    ///
    /// ```
    /// use modules::rrd2014::internal::*;
    /// use Term::Int;
    ///
    /// assert_eq!(Term::let_in(None, Int(0)), Int(0));
    ///
    /// assert_eq!(
    ///     Term::let_in(vec![(Int(12), Type::Int)], Int(0)),
    ///     Term::app(Term::Abs(Type::Int, Box::new(Int(0))), Int(12))
    /// );
    ///
    /// assert_eq!(
    ///     Term::let_in(
    ///         vec![(Int(12), Type::Int), (Int(36), Type::fun(Type::Int, Type::Int))],
    ///         Int(0)
    ///     ),
    ///     Term::app(
    ///         Term::app(
    ///             Term::Abs(
    ///                 Type::Int,
    ///                 Box::new(Term::Abs(Type::fun(Type::Int, Type::Int), Box::new(Int(0))))
    ///             ),
    ///             Int(12)
    ///         ),
    ///         Int(36)
    ///     )
    /// );
    /// ```
    pub fn let_in<I>(bs: I, t: Term) -> Self
    where
        I: IntoIterator<Item = (Term, Type)>,
        I::IntoIter: DoubleEndedIterator,
    {
        let mut t0 = t;
        let mut v = vec![];
        for (t, ty) in bs.into_iter().rev() {
            t0 = Term::Abs(ty, Box::new(t0));
            v.push(t);
        }
        v.into_iter().rfold(t0, Term::app)
    }

    /// Creates an n-ary pack.
    ///
    /// # Examples
    ///
    /// ```
    /// use modules::rrd2014::internal::*;
    /// use Kind::*;
    /// use Type::Int;
    ///
    /// assert_eq!(
    ///     Term::pack(Term::Int(3), vec![], None, Int),
    ///     Term::Int(3)
    /// );
    ///
    /// assert_eq!(
    ///     Term::pack(Term::Int(3), vec![Int], vec![Mono], Int),
    ///     Term::Pack(Int, Box::new(Term::Int(3)), Type::some(vec![Mono], Int))
    /// );
    ///
    /// assert_eq!(
    ///     Term::pack(Term::Int(3), vec![Int, Int], vec![Mono, Mono], Int),
    ///     Term::Pack(
    ///         Int,
    ///         Box::new(Term::Pack(Int, Box::new(Term::Int(3)), Type::some(vec![Mono], Int))),
    ///         Type::some(vec![Mono, Mono], Int)
    ///     )
    /// );
    ///
    /// assert_eq!(
    ///     Term::pack(
    ///         Term::Int(2),
    ///         vec![Type::var(576), Type::fun(Int, Int)],
    ///         vec![Kind::fun(Mono, Mono), Mono],
    ///         Int
    ///     ),
    ///     Term::Pack(
    ///         Type::fun(Int, Int),
    ///         Box::new(Term::Pack(
    ///             Type::var(576),
    ///             Box::new(Term::Int(2)),
    ///             Type::some(vec![Kind::fun(Mono, Mono)], Int)
    ///         )),
    ///         Type::some(vec![Kind::fun(Mono, Mono), Mono], Int)
    ///     )
    /// );
    ///
    /// assert_eq!(
    ///     Term::pack(
    ///         Term::Int(2),
    ///         vec![Type::var(576), Type::fun(Int, Int)],
    ///         vec![Kind::fun(Mono, Mono), Mono],
    ///         Type::fun(Type::var(0), Type::var(1))
    ///     ),
    ///     Term::Pack(
    ///         Type::fun(Int, Int),
    ///         Box::new(Term::Pack(
    ///             Type::var(576),
    ///             Box::new(Term::Int(2)),
    ///             Type::some(
    ///                 vec![Kind::fun(Mono, Mono)],
    ///                 Type::fun(Type::var(0), Type::fun(Int, Int))
    ///             )
    ///         )),
    ///         Type::some(vec![Kind::fun(Mono, Mono), Mono], Type::fun(Type::var(0), Type::var(1)))
    ///     )
    /// );
    ///
    /// assert_eq!(
    ///     Term::pack(
    ///         Term::Int(2),
    ///         vec![Type::var(576), Type::var(30)],
    ///         vec![Kind::fun(Mono, Mono), Mono],
    ///         Type::fun(Type::var(0), Type::var(1))
    ///     ),
    ///     Term::Pack(
    ///         Type::var(30),
    ///         Box::new(Term::Pack(
    ///             Type::var(576),
    ///             Box::new(Term::Int(2)),
    ///             Type::some(
    ///                 vec![Kind::fun(Mono, Mono)],
    ///                 Type::fun(Type::var(0), Type::var(31))
    ///             )
    ///         )),
    ///         Type::some(vec![Kind::fun(Mono, Mono), Mono], Type::fun(Type::var(0), Type::var(1)))
    ///     )
    /// );
    /// ```
    pub fn pack<K>(t: Term, tys: Vec<Type>, ks: K, mut body: Type) -> Self
    where
        K: IntoIterator<Item = Kind>,
    {
        let ks: Vec<Kind> = ks.into_iter().collect();
        let v: Vec<Type> = tys
            .iter()
            .enumerate()
            .rev()
            .map(|(i, ty)| {
                let ret = body.clone();
                body.subst_shift(i, &ty, isize::try_from(i).unwrap() + 1);
                body.shift_above(i, -1);
                ret
            })
            .enumerate()
            .map(|(i, ty)| Type::some(Vec::from(&ks[..ks.len() - i]), ty))
            .collect();
        tys.into_iter()
            .zip(v.into_iter().rev())
            .fold(t, |t, (wit, ty)| Term::Pack(wit, Box::new(t), ty))
    }

    /// Creates an n-ary unpack.
    ///
    /// # Examples
    ///
    /// ```
    /// use modules::rrd2014::internal::*;
    /// use Kind::*;
    /// use Type::Int;
    ///
    /// assert_eq!(
    ///     Term::unpack(Term::Int(3), 0, Int, Term::Int(5)),
    ///     Term::app(Term::abs(Int, Term::Int(5)), Term::Int(3))
    /// );
    ///
    /// assert_eq!(
    ///     Term::unpack(Term::Int(3), 1, Int, Term::Int(5)),
    ///     Term::Unpack(
    ///         Box::new(Term::Int(3)),
    ///         Box::new(Term::Int(5)),
    ///     )
    /// );
    ///
    /// assert_eq!(
    ///     Term::unpack(Term::Int(3), 2, Int, Term::Int(5)),
    ///     Term::Unpack(
    ///         Box::new(Term::Int(3)),
    ///         Box::new(
    ///             Term::Unpack(
    ///                 Box::new(Term::var(0)),
    ///                 Box::new(Term::Int(5)),
    ///             )
    ///         )
    ///     )
    /// );
    ///
    /// assert_eq!(
    ///     Term::unpack(Term::Int(3), 3, Type::Int, Term::Int(5)),
    ///     Term::Unpack(
    ///         Box::new(Term::Int(3)),
    ///         Box::new(
    ///             Term::Unpack(
    ///                 Box::new(Term::var(0)),
    ///                 Box::new(
    ///                     Term::Unpack(
    ///                         Box::new(Term::var(0)),
    ///                         Box::new(Term::Int(5)),
    ///                     )
    ///                 )
    ///             )
    ///         )
    ///     )
    /// );
    pub fn unpack(t1: Term, n: usize, ty: Type, t2: Term) -> Self {
        let mut t = t2;
        for _ in 1..n {
            t = Term::Unpack(Box::new(Term::var(0)), Box::new(t));
        }
        if 0 < n {
            Term::Unpack(Box::new(t1), Box::new(t))
        } else {
            Term::let_in(Some((t1, ty)), t)
        }
    }

    fn type_of<'a>(&'a self, ctx: &mut Context<'a>) -> Result<Type, TypeError> {
        use Term::*;
        match *self {
            Var(v) => Ok(ctx.lookup_value(v)?.into_owned()),
            Abs(ref ty1, ref t) => {
                ctx.insert_value(Cow::Borrowed(ty1));
                let ty2 = t.type_of(ctx)?;
                ctx.drop_value();
                Ok(Type::fun(ty1.clone(), ty2))
            }
            App(ref t1, ref t2) => {
                let ty1 = t1.type_of(ctx)?.reduce();
                let ty2 = t2.type_of(ctx)?.reduce();
                match ty1 {
                    Type::Fun(ty11, ty12) if ty11.equal(&ty2) => Ok(*ty12),
                    Type::Fun(ty11, _) => Err(TypeError::TypeMismatch(*ty11, ty2)),
                    _ => Err(TypeError::NotFunction(ty1)),
                }
            }
            Record(ref r) => Ok(Type::Record(self::Record(
                r.0.iter()
                    .map(|(l, t)| Ok((l.clone(), t.type_of(ctx)?)))
                    .collect::<Result<_, TypeError>>()?,
            ))),
            Proj(ref t, ref l) => match t.type_of(ctx)?.reduce() {
                Type::Record(mut r) => {
                    r.0.remove(l)
                        .ok_or_else(|| TypeError::MissingLabel(l.clone()))
                }
                ty => Err(TypeError::NotRecord(ty)),
            },
            Poly(ref k, ref t) => {
                ctx.insert_type(Cow::Borrowed(k));
                let ty = t.type_of(ctx)?;
                ctx.drop_type();
                Ok(Type::forall(Some(k.clone()), ty))
            }
            Inst(ref t, ref ty2) => {
                let ty1 = t.type_of(ctx)?.reduce();
                match ty1 {
                    Type::Forall(k1, mut ty) => {
                        let k2 = ty2.kind_of::<_, ()>(&mut Env::from(ctx.clone()))?;
                        if k1.equal(&k2) {
                            ty.subst_top(&mut ty2.clone());
                            Ok(*ty)
                        } else {
                            Err(TypeError::KindError(KindError::KindMismatch(k1, k2)))
                        }
                    }
                    _ => Err(TypeError::NotForall(ty1)),
                }
            }
            Pack(ref ty1, ref t, ref ty2) => {
                ty2.kind_of::<_, ()>(&mut Env::from(ctx.clone()))?
                    .mono()
                    .map_err(|e| TypeError::KindError(KindError::NotMono(ty2.clone(), e)))?;
                match *ty2 {
                    Type::Some(ref k1, ref ty) => {
                        let k2 = ty1.kind_of::<_, ()>(&mut Env::from(ctx.clone()))?;
                        if k1.equal(&k2) {
                            let ty0 = t.type_of(ctx)?;
                            let mut ty = *ty.clone();
                            ty.subst_top(&mut ty1.clone());
                            if ty0 == ty {
                                Ok(ty2.clone())
                            } else {
                                Err(TypeError::TypeMismatch(ty0, ty))
                            }
                        } else {
                            Err(TypeError::KindError(KindError::KindMismatch(
                                k1.clone(),
                                k2,
                            )))
                        }
                    }
                    ref ty2 => Err(TypeError::NotSome(ty2.clone())),
                }
            }
            Unpack(ref t1, ref t2) => match t1.type_of(ctx)? {
                Type::Some(k, ty1) => {
                    ctx.insert_type(Cow::Owned(k));
                    ctx.insert_value(Cow::Owned(*ty1));
                    let ty2 = t2.type_of(ctx)?;
                    ctx.drop_value();
                    ctx.drop_type();
                    ty2.kind_of::<_, ()>(&mut Env::from(ctx.clone()))?
                        .mono()
                        .map_err(|e| TypeError::KindError(KindError::NotMono(ty2.clone(), e)))?;
                    Ok(ty2)
                }
                ty1 => Err(TypeError::NotSome(ty1)),
            },
            Int(_) => Ok(Type::Int),
        }
    }
}

#[derive(Debug, Fail, PartialEq)]
pub enum EnvError {
    #[fail(display = "unbound type variable: {:?}", _0)]
    UnboundTypeVariable(Variable),

    #[fail(display = "unbound variable: {:?}", _0)]
    UnboundVariable(Variable),

    #[fail(display = "unbound name: {:?}", _0)]
    UnboundName(Name),
}

#[derive(Debug, Fail, PartialEq)]
pub enum UnificationError {
    #[fail(display = "could not unify: {:?} and {:?}", _0, _1)]
    NotUnifiable(Type, Type),

    #[fail(display = "recursive type is not allowed: {:?} and {:?}", _0, _1)]
    Recursion(Variable, Type),
}

impl<T, S> Env<T, S> {
    pub fn lookup_type(&self, v: Variable) -> Result<(Kind, S), EnvError>
    where
        S: Clone,
    {
        self.tenv
            .iter()
            .rev()
            .nth(v.0)
            .cloned()
            .ok_or_else(|| EnvError::UnboundTypeVariable(v))
    }

    pub fn lookup_value(&self, v: Variable) -> Result<T, EnvError>
    where
        T: Clone,
    {
        self.venv
            .iter()
            .rev()
            .nth(v.0)
            .cloned()
            .ok_or_else(|| EnvError::UnboundVariable(v))?
            .ok_or_else(|| EnvError::UnboundVariable(v))
    }

    pub fn lookup_value_by_name(&self, name: &Name) -> Result<(T, Variable), EnvError>
    where
        T: Clone,
    {
        let n = *self
            .nmap
            .get(&name)
            .ok_or_else(|| EnvError::UnboundName(name.clone()))?;
        Ok((
            self.venv
                .get(n)
                .expect("lookup_value_by_name: unexpected None")
                .clone()
                .expect("lookup_value_by_name: unexpected None"),
            Variable(self.venv.len() - n - 1),
        ))
    }

    pub fn insert_type(&mut self, k: Kind, x: S)
    where
        T: Shift,
    {
        self.tenv.push((k, x));
        self.tenv.iter_mut().for_each(|k| k.0.shift(1));
        self.venv.iter_mut().for_each(|x| x.shift(1));
    }

    pub fn insert_types<I>(&mut self, ks: I)
    where
        T: Shift,
        I: IntoIterator<Item = (Kind, S)>,
    {
        ks.into_iter().for_each(|(k, x)| self.insert_type(k, x));
    }

    fn drop_type(&mut self)
    where
        T: Shift,
    {
        self.tenv.pop();
        self.tenv.iter_mut().for_each(|k| k.0.shift(-1));
        self.venv.iter_mut().for_each(|x| x.shift(-1));
    }

    /// One should probably use `drop_values_state` before `drop_value` in case indices in value
    /// environment become negative and then the program panics.
    pub fn drop_types(&mut self, n: usize)
    where
        T: Shift,
    {
        self.tenv.truncate(self.tenv.len() - n);
        let m = isize::try_from(n).unwrap();
        self.tenv.iter_mut().for_each(|k| k.0.shift(-m));
        self.venv.iter_mut().for_each(|x| x.shift(-m));
    }

    pub fn insert_value(&mut self, name: Name, x: T) -> Option<Variable> {
        let v = self.nmap.get(&name).map(|&n| Variable(n));
        self.nmap.insert(name, self.venv.len());
        self.venv.push(Some(x));
        v
    }

    pub fn insert_dummy_value(&mut self) {
        self.venv.push(None);
    }

    pub fn drop_value(&mut self, name: Name, prev: Option<Variable>) {
        self.venv.pop();
        if let Some(v) = prev {
            self.nmap.insert(name, v.0);
        } else {
            self.nmap.remove(&name);
        }
    }

    pub fn drop_values_state(&mut self, n: usize, state: EnvState) {
        self.venv.truncate(self.venv.len() - n);
        self.nmap = state.0;
    }

    pub fn get_state(&self) -> EnvState {
        EnvState(self.nmap.clone())
    }

    pub fn unify<I>(&mut self, iter: I) -> Result<Subst, UnificationError>
    where
        I: IntoIterator<Item = (Type, Type)>,
        T: Substitution,
    {
        self.unify_aux(iter, Subst::default())
    }

    fn unify_aux<I>(&mut self, iter: I, mut s: Subst) -> Result<Subst, UnificationError>
    where
        I: IntoIterator<Item = (Type, Type)>,
        T: Substitution,
    {
        use Type::*;
        let mut w: Vec<(Type, Type)> = iter.into_iter().collect();
        loop {
            if let Option::Some((ty1, ty2)) = w.pop() {
                if ty1 == ty2 {
                    continue;
                }
                match (ty1, ty2) {
                    (Var(v), ty) | (ty, Var(v)) => {
                        let tvs = ty.ftv();
                        if tvs.contains(&v) {
                            return Err(UnificationError::Recursion(v, ty));
                        }
                        let new_s = Subst::from_iter(vec![(v, ty)]);
                        self.apply(&new_s);
                        w.apply(&new_s);
                        s = s.compose(new_s);
                    }
                    (Fun(ty11, ty12), Fun(ty21, ty22)) => {
                        w.extend(vec![(*ty11, *ty21), (*ty12, *ty22)]);
                    }
                    (ty1, ty2) => Err(UnificationError::NotUnifiable(ty1, ty2))?,
                }
            } else {
                return Ok(s);
            }
        }
    }

    pub fn fresh_type_variable(&mut self, k: Kind, x: S) -> Variable
    where
        T: Shift,
    {
        let l = self.tenv.len();
        self.insert_type(k, x);
        Variable(l)
    }
}

impl Subst {
    pub fn compose(mut self, mut s: Subst) -> Self {
        s.apply(&self);
        self.0.extend(s.0);
        self
    }

    pub fn shift(self, d: isize) -> Self {
        let f = |p: (Variable, Type)| {
            let (v, mut ty) = p;
            ty.shift(d);
            (v.add(d), ty)
        };
        Subst(self.0.into_iter().map(f).collect())
    }
}

impl<'a> Context<'a> {
    fn lookup_type(&self, v: Variable) -> Result<Cow<Kind>, EnvError> {
        self.tenv
            .iter()
            .rev()
            .nth(v.0)
            .cloned()
            .ok_or_else(|| EnvError::UnboundTypeVariable(v))
    }

    fn lookup_value(&self, v: Variable) -> Result<Cow<Type>, EnvError> {
        self.venv
            .iter()
            .rev()
            .nth(v.0)
            .cloned()
            .ok_or_else(|| EnvError::UnboundVariable(v))
    }

    fn insert_type(&mut self, k: Cow<'a, Kind>) {
        self.tenv.push(k);
        self.tenv.iter_mut().for_each(|k| k.to_mut().shift(1));
        self.venv.iter_mut().for_each(|x| x.to_mut().shift(1));
    }

    /// One should probably use `drop_value` prior to `drop_type` in case indices in value
    /// environment become negative and then the program panics.
    fn drop_type(&mut self) {
        self.tenv.pop();
        self.tenv.iter_mut().for_each(|k| k.to_mut().shift(-1));
        self.venv.iter_mut().for_each(|x| x.to_mut().shift(-1));
    }

    fn insert_value(&mut self, ty: Cow<'a, Type>) {
        self.venv.push(ty);
    }

    fn drop_value(&mut self) {
        self.venv.pop();
    }
}

impl<'a, S: Clone + Default> From<Context<'a>> for Env<Type, S> {
    fn from(ctx: Context<'a>) -> Self {
        Env {
            tenv: ctx
                .tenv
                .into_iter()
                .map(|k| (k.into_owned(), S::default()))
                .collect(),
            venv: ctx
                .venv
                .into_iter()
                .map(|ty| Some(ty.into_owned()))
                .collect(),
            nmap: HashMap::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    #![warn(dead_code)]
    use super::*;

    macro_rules! assert_type_shift {
        ($t:expr, $d:expr, $r:expr) => {{
            let mut ty = $t;
            ty.shift($d);
            assert_eq!(ty, $r);
        }};
    }

    #[test]
    fn type_shift() {
        use Kind::Mono;
        use Type::*;

        assert_type_shift!(Int, 0, Int);
        assert_type_shift!(Int, 1, Int);

        assert_type_shift!(Type::var(0), 0, Type::var(0));
        assert_type_shift!(Type::var(0), 1, Type::var(1));
        assert_type_shift!(Type::var(0), 2, Type::var(2));

        assert_type_shift!(Type::var(1), 2, Type::var(3));
        assert_type_shift!(Type::var(8), 1, Type::var(9));

        assert_type_shift!(
            Type::some(vec![Mono], Type::var(0)),
            1,
            Type::some(vec![Mono], Type::var(0))
        );

        assert_type_shift!(
            Type::some(vec![Mono], Type::var(1)),
            1,
            Type::some(vec![Mono], Type::var(2))
        );

        assert_type_shift!(
            Type::some(vec![Mono], Type::var(8)),
            1,
            Type::some(vec![Mono], Type::var(9))
        );

        assert_type_shift!(
            Type::some(vec![Mono], Type::var(48)),
            70136,
            Type::some(vec![Mono], Type::var(70184))
        );

        assert_type_shift!(
            Type::some(vec![Mono], Type::var(48)),
            -29,
            Type::some(vec![Mono], Type::var(19))
        );

        assert_type_shift!(
            Type::some(vec![Mono], Type::var(48)),
            -48,
            Type::some(vec![Mono], Type::var(0))
        );
    }

    #[test]
    #[should_panic]
    fn type_shift_panic() {
        use Kind::Mono;

        assert_type_shift!(
            Type::some(vec![Mono], Type::var(4)),
            -48,
            Type::some(vec![Mono], Type::var(0))
        );
    }

    macro_rules! assert_type_subst {
        ($t:expr, $j:expr, $by:expr, $r:expr) => {{
            let mut ty = $t;
            ty.subst($j, &$by);
            assert_eq!(ty, $r);
        }};
    }

    #[test]
    fn type_subst() {
        use Kind::Mono;
        use Type::*;

        assert_type_subst!(Int, 0, Int, Int);
        assert_type_subst!(Int, 1, Int, Int);

        assert_type_subst!(Type::var(0), 0, Int, Int);
        assert_type_subst!(Type::var(1), 0, Int, Type::var(1));
        assert_type_subst!(Type::var(0), 1, Int, Type::var(0));

        assert_type_subst!(Type::var(0), 0, Type::var(0), Type::var(0));
        assert_type_subst!(Type::var(1), 0, Type::var(0), Type::var(1));
        assert_type_subst!(Type::var(0), 1, Type::var(0), Type::var(0));
        assert_type_subst!(Type::var(0), 0, Type::var(1), Type::var(1));
        assert_type_subst!(Type::var(1), 1, Type::var(0), Type::var(0));

        assert_type_subst!(
            Type::some(vec![Mono], Type::var(0)),
            0,
            Type::var(0),
            Type::some(vec![Mono], Type::var(0))
        );

        assert_type_subst!(
            Type::some(vec![Mono], Type::var(1)),
            0,
            Type::var(0),
            Type::some(vec![Mono], Type::var(1))
        );

        assert_type_subst!(
            Type::some(vec![Mono], Type::var(1)),
            0,
            Type::var(106),
            Type::some(vec![Mono], Type::var(107))
        );

        assert_type_subst!(
            Type::some(vec![Mono], Type::var(0)),
            0,
            Type::var(106),
            Type::some(vec![Mono], Type::var(0))
        );

        assert_type_subst!(
            Type::some(vec![Mono, Mono], Type::var(1)),
            0,
            Type::var(106),
            Type::some(vec![Mono, Mono], Type::var(1))
        );

        assert_type_subst!(
            Type::some(vec![Mono, Mono], Type::var(3)),
            1,
            Type::var(16),
            Type::some(vec![Mono, Mono], Type::var(18))
        );
    }

    #[test]
    fn pack() {
        use Kind::*;

        fn label(x: &str) -> Label {
            Label::Label(Name(x.to_string()))
        }

        assert_eq!(
            Term::pack(
                Term::Int(1),
                vec![
                    Type::var(576),
                    Type::var(0),
                    Type::forall(vec![Mono], Type::var(0)),
                    Type::var(30)
                ],
                vec![
                    Kind::fun(Mono, Mono),
                    Kind::fun(Mono, Kind::fun(Mono, Mono)),
                    Kind::fun(Kind::fun(Mono, Mono), Mono),
                    Mono
                ],
                Type::record(vec![
                    (label("a"), Type::var(3)),
                    (label("b"), Type::var(2)),
                    (label("c"), Type::var(0)),
                    (label("d"), Type::var(1)),
                    (label("e"), Type::var(4)),
                ])
            ),
            Term::Pack(
                Type::var(30),
                Box::new(Term::Pack(
                    Type::forall(vec![Mono], Type::var(0)),
                    Box::new(Term::Pack(
                        Type::var(0),
                        Box::new(Term::Pack(
                            Type::var(576),
                            Box::new(Term::Int(1)),
                            Type::some(
                                vec![Kind::fun(Mono, Mono)],
                                Type::record(vec![
                                    (label("a"), Type::var(31)),
                                    (label("b"), Type::forall(vec![Mono], Type::var(0))),
                                    (label("c"), Type::var(0)),
                                    (label("d"), Type::var(1)),
                                    (label("e"), Type::var(1)),
                                ])
                            ),
                        )),
                        Type::some(
                            vec![
                                Kind::fun(Mono, Mono),
                                Kind::fun(Mono, Kind::fun(Mono, Mono))
                            ],
                            Type::record(vec![
                                (label("a"), Type::var(32)),
                                (label("b"), Type::forall(vec![Mono], Type::var(0))),
                                (label("c"), Type::var(0)),
                                (label("d"), Type::var(1)),
                                (label("e"), Type::var(2)),
                            ])
                        ),
                    )),
                    Type::some(
                        vec![
                            Kind::fun(Mono, Mono),
                            Kind::fun(Mono, Kind::fun(Mono, Mono)),
                            Kind::fun(Kind::fun(Mono, Mono), Mono)
                        ],
                        Type::record(vec![
                            (label("a"), Type::var(33)),
                            (label("b"), Type::var(2)),
                            (label("c"), Type::var(0)),
                            (label("d"), Type::var(1)),
                            (label("e"), Type::var(3)),
                        ])
                    ),
                )),
                Type::some(
                    vec![
                        Kind::fun(Mono, Mono),
                        Kind::fun(Mono, Kind::fun(Mono, Mono)),
                        Kind::fun(Kind::fun(Mono, Mono), Mono),
                        Mono
                    ],
                    Type::record(vec![
                        (label("a"), Type::var(3)),
                        (label("b"), Type::var(2)),
                        (label("c"), Type::var(0)),
                        (label("d"), Type::var(1)),
                        (label("e"), Type::var(4)),
                    ])
                ),
            )
        );
    }

    #[test]
    fn env_lookup() {
        use Kind::*;

        let env = Env {
            tenv: vec![(Mono, "M.t"), (Kind::fun(Mono, Mono), "M.s")],
            venv: vec![Type::var(3), Type::var(6)]
                .into_iter()
                .map(Some)
                .collect(),
            nmap: HashMap::new(),
        };

        assert_eq!(
            env.lookup_type(Variable(0)),
            Ok((Kind::fun(Mono, Mono), "M.s"))
        );
        assert_eq!(env.lookup_type(Variable(1)), Ok((Mono, "M.t")));

        assert_eq!(env.lookup_value(Variable(0)), Ok(Type::var(6)));
        assert_eq!(env.lookup_value(Variable(1)), Ok(Type::var(3)));

        let mut env = env;
        env.insert_type(Kind::fun(Mono, Kind::fun(Mono, Mono)), "M.u");

        assert_eq!(
            env.lookup_type(Variable(0)),
            Ok((Kind::fun(Mono, Kind::fun(Mono, Mono)), "M.u"))
        );
        assert_eq!(
            env.lookup_type(Variable(1)),
            Ok((Kind::fun(Mono, Mono), "M.s"))
        );
        assert_eq!(env.lookup_type(Variable(2)), Ok((Mono, "M.t")));

        assert_eq!(
            env.lookup_type(Variable(3)),
            Err(EnvError::UnboundTypeVariable(Variable(3)))
        );

        assert_eq!(env.lookup_value(Variable(0)), Ok(Type::var(7)));
        assert_eq!(env.lookup_value(Variable(1)), Ok(Type::var(4)));

        assert_eq!(
            env.lookup_value(Variable(2)),
            Err(EnvError::UnboundVariable(Variable(2)))
        );
    }

    #[test]
    fn env_insert() {
        use Kind::*;

        let mut env = Env {
            tenv: vec![(Mono, "N.t")],
            venv: vec![Type::var(0)].into_iter().map(Some).collect(),
            nmap: HashMap::new(),
        };
        env.insert_type(Mono, "P.t");
        assert_eq!(
            env,
            Env {
                tenv: vec![(Mono, "N.t"), (Mono, "P.t")],
                venv: vec![Type::var(1)].into_iter().map(Some).collect(),
                nmap: HashMap::new(),
            }
        );
    }

    #[test]
    fn env_by_name() {
        use Kind::*;
        use Type::*;

        let mut env = Env {
            tenv: vec![(Mono, "t")],
            venv: vec![],
            nmap: HashMap::new(),
        };

        env.insert_value(Name::from("x"), Int);
        assert_eq!(
            env.lookup_value_by_name(&Name::from("x")),
            Ok((Int, Variable(0)))
        );

        env.insert_value(Name::from("y"), Type::fun(Int, Int));
        assert_eq!(
            env.lookup_value_by_name(&Name::from("x")),
            Ok((Int, Variable(1)))
        );
        assert_eq!(
            env.lookup_value_by_name(&Name::from("y")),
            Ok((Type::fun(Int, Int), Variable(0)))
        );

        env.insert_value(Name::from("x"), Type::fun(Int, Type::var(0)));
        assert_eq!(
            env.lookup_value_by_name(&Name::from("x")),
            Ok((Type::fun(Int, Type::var(0)), Variable(0)))
        );
        assert_eq!(
            env.lookup_value_by_name(&Name::from("y")),
            Ok((Type::fun(Int, Int), Variable(1)))
        );
    }

    macro_rules! assert_encoding {
        ($s:expr, $l:expr, $x:expr) => {{
            use self::Record as R;
            assert_eq!(Type::from($s), Record(R::from_iter(vec![($l, $x)])));
        }};
    }

    #[test]
    fn encoding() {
        use crate::rrd2014::SemanticSig::*;
        use Kind::*;
        use Type::*;

        assert_encoding!(AtomicTerm(Int), Label::Val, Int);
        assert_encoding!(AtomicTerm(Type::var(0)), Label::Val, Type::var(0));

        assert_encoding!(
            AtomicType(Int, Mono),
            Label::Typ,
            Type::forall(
                vec![Kind::fun(Mono, Mono)],
                Type::fun(Type::app(Type::var(0), Int), Type::app(Type::var(0), Int))
            )
        );

        assert_encoding!(
            AtomicType(Type::var(0), Mono),
            Label::Typ,
            Type::forall(
                vec![Kind::fun(Mono, Mono)],
                Type::fun(
                    Type::app(Type::var(0), Type::var(1)),
                    Type::app(Type::var(0), Type::var(1)),
                )
            )
        );
    }

    impl Shift for () {
        fn shift_above(&mut self, _: usize, _: isize) {}
    }

    macro_rules! assert_kinding_ok {
        ($ty:expr, $k:expr) => {{
            use Option::Some as S;
            assert_eq!($ty.kind_of::<(), ()>(&mut Env::default()).ok(), S($k));
        }};
    }

    macro_rules! assert_kinding_err {
        ($ty:expr, $e:expr) => {{
            match $ty.kind_of::<(), ()>(&mut Env::default()) {
                Err(e) => assert_eq!(e, $e, "{:?}", e),
                Ok(k) => panic!("unexpectedly well-kinded: {:?}", k),
            }
        }};
    }

    #[test]
    fn kinding() {
        use super::Record as R;
        use Kind::Mono;
        use Type::*;

        assert_kinding_ok!(Int, Mono);
        assert_kinding_ok!(Type::fun(Int, Int), Mono);
        assert_kinding_ok!(Type::forall(vec![Mono], Int), Mono);
        assert_kinding_ok!(Type::some(vec![Kind::fun(Mono, Mono)], Int), Mono);
        assert_kinding_ok!(Type::abs(vec![Mono], Int), Kind::fun(Mono, Mono));
        assert_kinding_ok!(
            Type::abs(vec![Kind::fun(Mono, Mono)], Int),
            Kind::fun(Kind::fun(Mono, Mono), Mono)
        );
        assert_kinding_ok!(Type::app(Type::abs(vec![Mono], Int), Int), Mono);
        assert_kinding_ok!(Type::abs(vec![Mono], Type::var(0)), Kind::fun(Mono, Mono));
        assert_kinding_ok!(
            Type::abs(vec![Kind::fun(Mono, Mono)], Type::var(0)),
            Kind::fun(Kind::fun(Mono, Mono), Kind::fun(Mono, Mono))
        );
        assert_kinding_ok!(Record(R::from_iter(None)), Mono);
        assert_kinding_ok!(Record(R::from_iter(vec![(Label::from("a"), Int)])), Mono);
        assert_kinding_ok!(
            Record(R::from_iter(vec![
                (Label::from("a"), Int),
                (Label::from("b"), Int)
            ])),
            Mono
        );

        assert_kinding_err!(
            Type::var(0),
            KindError::Env(EnvError::UnboundTypeVariable(Variable(0)))
        );
        assert_kinding_err!(
            Type::fun(Int, Type::abs(vec![Mono], Int)),
            KindError::NotMono(
                Type::abs(vec![Mono], Int),
                NotMonoError(Kind::fun(Mono, Mono))
            )
        );
        assert_kinding_err!(
            Type::some(vec![Mono], Type::abs(vec![Mono], Int)),
            KindError::NotMono(
                Type::abs(vec![Mono], Int),
                NotMonoError(Kind::fun(Mono, Mono))
            )
        );
        assert_kinding_err!(
            Record(R::from_iter(vec![(
                Label::from("a"),
                Type::abs(vec![Mono], Type::var(0))
            )])),
            KindError::Record(
                Label::from("a"),
                Box::new(KindError::NotMono(
                    Type::abs(vec![Mono], Type::var(0)),
                    NotMonoError(Kind::fun(Mono, Mono))
                ))
            )
        );
        assert_kinding_err!(
            Record(R::from_iter(vec![
                (Label::from("a"), Int),
                (Label::from("b"), Type::abs(vec![Mono], Type::var(0)))
            ])),
            KindError::Record(
                Label::from("b"),
                Box::new(KindError::NotMono(
                    Type::abs(vec![Mono], Type::var(0)),
                    NotMonoError(Kind::fun(Mono, Mono))
                ))
            )
        );
        assert_kinding_err!(Type::app(Int, Int), KindError::NotFunction(Mono));
        assert_kinding_err!(
            Type::app(Type::abs(vec![Kind::fun(Mono, Mono)], Int), Int),
            KindError::KindMismatch(Kind::fun(Mono, Mono), Mono)
        );
    }
}

//! The internal language.

use std::collections::HashMap;
use std::collections::HashSet;
use std::convert::TryFrom;
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

#[derive(Debug, PartialEq)]
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

impl From<super::SemanticSig> for Type {
    fn from(st: super::SemanticSig) -> Self {
        use super::SemanticSig::*;
        match st {
            AtomicTerm(ty) => Type::Record(Record::from_iter(vec![(Label::Val, ty)])),
            AtomicType(mut ty, k) => {
                ty.shift(1);
                Type::Record(Record::from_iter(vec![(
                    Label::Typ,
                    Type::forall(
                        vec![Kind::fun(k, Kind::Mono)],
                        Type::fun(
                            Type::app(Type::var(0), ty.clone()),
                            Type::app(Type::var(0), ty),
                        ),
                    ),
                )]))
            }
            AtomicSig(asig) => {
                let ty = Type::from(asig);
                Type::Record(Record::from_iter(vec![(
                    Label::Sig,
                    Type::fun(ty.clone(), ty),
                )]))
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
            ST::Term(t) => Term::Record(Record::from_iter(vec![(Label::Val, t)])),
            ST::Type(mut ty, k) => {
                ty.shift(1);
                Term::Record(Record::from_iter(vec![(
                    Label::Typ,
                    Term::poly(
                        vec![Kind::fun(k, Kind::Mono)],
                        Term::abs(Type::app(Type::var(0), ty), Term::var(0)),
                    ),
                )]))
            }
            ST::Sig(asig) => Term::Record(Record::from_iter(vec![(
                Label::Sig,
                Term::abs(Type::from(asig), Term::var(0)),
            )])),
        }
    }
}

impl From<super::Ident> for Label {
    fn from(id: super::Ident) -> Self {
        Label::Label(Name::from(id))
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
        Variable(usize::try_from(isize::try_from(self.0).unwrap() + d).expect("negative index"))
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
                Type::Record(Record::from_iter(vec![
                    (label("a"), Type::var(3)),
                    (label("b"), Type::var(2)),
                    (label("c"), Type::var(0)),
                    (label("d"), Type::var(1)),
                    (label("e"), Type::var(4)),
                ]))
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
                                Type::Record(Record::from_iter(vec![
                                    (label("a"), Type::var(31)),
                                    (label("b"), Type::forall(vec![Mono], Type::var(0))),
                                    (label("c"), Type::var(0)),
                                    (label("d"), Type::var(1)),
                                    (label("e"), Type::var(1)),
                                ],)),
                            ),
                        )),
                        Type::some(
                            vec![
                                Kind::fun(Mono, Mono),
                                Kind::fun(Mono, Kind::fun(Mono, Mono))
                            ],
                            Type::Record(Record::from_iter(vec![
                                (label("a"), Type::var(32)),
                                (label("b"), Type::forall(vec![Mono], Type::var(0))),
                                (label("c"), Type::var(0)),
                                (label("d"), Type::var(1)),
                                (label("e"), Type::var(2)),
                            ],)),
                        ),
                    )),
                    Type::some(
                        vec![
                            Kind::fun(Mono, Mono),
                            Kind::fun(Mono, Kind::fun(Mono, Mono)),
                            Kind::fun(Kind::fun(Mono, Mono), Mono)
                        ],
                        Type::Record(Record::from_iter(vec![
                            (label("a"), Type::var(33)),
                            (label("b"), Type::var(2)),
                            (label("c"), Type::var(0)),
                            (label("d"), Type::var(1)),
                            (label("e"), Type::var(3)),
                        ],)),
                    ),
                )),
                Type::some(
                    vec![
                        Kind::fun(Mono, Mono),
                        Kind::fun(Mono, Kind::fun(Mono, Mono)),
                        Kind::fun(Kind::fun(Mono, Mono), Mono),
                        Mono
                    ],
                    Type::Record(Record::from_iter(vec![
                        (label("a"), Type::var(3)),
                        (label("b"), Type::var(2)),
                        (label("c"), Type::var(0)),
                        (label("d"), Type::var(1)),
                        (label("e"), Type::var(4)),
                    ],)),
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
}

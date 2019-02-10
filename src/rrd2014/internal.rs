//! The internal language.

use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Name(String);

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Label {
    Label(Name),
}

#[derive(Debug, PartialEq)]
pub struct Variable(usize);

#[derive(Debug, PartialEq)]
pub struct Record<T>(HashMap<Label, T>);

#[derive(Debug, PartialEq)]
pub enum Kind {
    Mono,
    Fun(Box<Kind>, Box<Kind>),
}

#[derive(Debug, PartialEq)]
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
    Proj(Box<Term>, Label),
    Poly(Kind, Box<Term>),
    Inst(Box<Term>, Type),
    Pack(Type, Box<Term>, Type),
    Unpack(Box<Term>, Box<Term>),
    Int(isize),
}

impl Kind {
    pub fn fun(k1: Kind, k2: Kind) -> Self {
        Kind::Fun(Box::new(k1), Box::new(k2))
    }
}

impl Type {
    pub fn fun(ty1: Type, ty2: Type) -> Self {
        Type::Fun(Box::new(ty1), Box::new(ty2))
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
    pub fn some<I>(ks: I, mut ty: Type) -> Self
    where
        I: IntoIterator<Item = Kind>,
    {
        for k in ks.into_iter() {
            ty = Type::Some(k, Box::new(ty))
        }
        ty
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
    pub fn forall<I>(ks: I, mut ty: Type) -> Self
    where
        I: IntoIterator<Item = Kind>,
    {
        for k in ks.into_iter() {
            ty = Type::Forall(k, Box::new(ty))
        }
        ty
    }
}

impl Term {
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
}

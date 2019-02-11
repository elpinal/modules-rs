//! The internal language.

use std::collections::HashMap;
use std::convert::TryFrom;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name(String);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Label {
    Label(Name),
}

#[derive(Clone, Copy, Debug, PartialEq)]
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
    Proj(Box<Term>, Label),
    Poly(Kind, Box<Term>),
    Inst(Box<Term>, Type),
    Pack(Type, Box<Term>, Type),
    Unpack(Box<Term>, Box<Term>),
    Int(isize),
}

impl Variable {
    fn add(self, d: isize) -> Self {
        Variable(usize::try_from(isize::try_from(self.0).unwrap() + d).expect("negative index"))
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

impl Kind {
    pub fn fun(k1: Kind, k2: Kind) -> Self {
        Kind::Fun(Box::new(k1), Box::new(k2))
    }

    fn map<F>(&mut self, _: &F, _: usize) {}
}

impl Type {
    fn var(n: usize) -> Self {
        Type::Var(Variable(n))
    }

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

    fn shift(&mut self, d: isize) {
        self.shift_above(0, d)
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
}

impl Term {
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
}

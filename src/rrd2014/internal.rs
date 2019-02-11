//! The internal language.

use std::collections::HashMap;
use std::convert::TryFrom;
use std::iter::FromIterator;

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
struct Env<T> {
    tenv: Vec<Kind>,
    venv: Vec<T>,
}

trait Shift {
    fn shift(&mut self, d: isize);
}

impl Shift for Type {
    fn shift(&mut self, d: isize) {
        self.shift_above(0, d)
    }
}

impl Shift for Kind {
    fn shift(&mut self, _: isize) {}
}

impl Variable {
    fn add(self, d: isize) -> Self {
        Variable(usize::try_from(isize::try_from(self.0).unwrap() + d).expect("negative index"))
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

impl Kind {
    pub fn fun(k1: Kind, k2: Kind) -> Self {
        Kind::Fun(Box::new(k1), Box::new(k2))
    }

    fn map<F>(&mut self, _: &F, _: usize) {}
}

impl Type {
    pub fn var(n: usize) -> Self {
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

impl<T> Env<T> {
    fn lookup_type(&self, v: Variable) -> Result<Kind, ()> {
        self.tenv.iter().rev().nth(v.0).cloned().ok_or(())
    }

    fn lookup_value(&self, v: Variable) -> Result<T, ()>
    where
        T: Clone,
    {
        self.venv.iter().rev().nth(v.0).cloned().ok_or(())
    }

    fn insert_type(&mut self, k: Kind)
    where
        T: Shift,
    {
        self.tenv.push(k);
        self.tenv.iter_mut().for_each(|k| k.shift(1));
        self.venv.iter_mut().for_each(|x| x.shift(1));
    }

    fn insert_value(&mut self, x: T) {
        self.venv.push(x);
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
            tenv: vec![Mono, Kind::fun(Mono, Mono)],
            venv: vec![Type::var(3), Type::var(6)],
        };

        assert_eq!(env.lookup_type(Variable(0)), Ok(Kind::fun(Mono, Mono)));
        assert_eq!(env.lookup_type(Variable(1)), Ok(Mono));

        assert_eq!(env.lookup_value(Variable(0)), Ok(Type::var(6)));
        assert_eq!(env.lookup_value(Variable(1)), Ok(Type::var(3)));

        let mut env = env;
        env.insert_type(Kind::fun(Mono, Kind::fun(Mono, Mono)));

        assert_eq!(
            env.lookup_type(Variable(0)),
            Ok(Kind::fun(Mono, Kind::fun(Mono, Mono)))
        );
        assert_eq!(env.lookup_type(Variable(1)), Ok(Kind::fun(Mono, Mono)));
        assert_eq!(env.lookup_type(Variable(2)), Ok(Mono));

        assert_eq!(env.lookup_value(Variable(0)), Ok(Type::var(7)));
        assert_eq!(env.lookup_value(Variable(1)), Ok(Type::var(4)));
    }

    #[test]
    fn env_insert() {
        use Kind::*;

        let mut env = Env {
            tenv: vec![Mono],
            venv: vec![Type::var(0)],
        };
        env.insert_type(Mono);
        assert_eq!(
            env,
            Env {
                tenv: vec![Mono, Mono],
                venv: vec![Type::var(1)]
            }
        );
    }
}

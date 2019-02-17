use failure::*;

use super::*;

/// `body` is the body of the function of a closure.
/// Variables indexed by 0 is an argument to the closure.
/// The other variables are captured by `env`.
#[derive(Clone, Debug, PartialEq)]
pub struct Closure {
    body: Term,
    env: DynEnv,
}

/// This sort of a closure represents a polymorphic function.
/// `body` is the body of the function of a closure.
/// All variables are captured by `env`.
#[derive(Clone, Debug, PartialEq)]
pub struct TypeClosure {
    body: Term,
    env: DynEnv,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Int(isize),
    Closure(Closure),
    TypeClosure(TypeClosure),
    Record(Record<Value>),
    Pack(Box<Value>),
}

/// A dynamic environment.
#[derive(Clone, Debug, Default, PartialEq)]
struct DynEnv {
    vs: Vec<Value>,
}

pub fn reduce(t: Term) -> Fallible<Value> {
    let mut env = DynEnv::default();
    env.reduce(t)
}

impl Value {
    fn pack(v: Value) -> Self {
        Value::Pack(Box::new(v))
    }
}

impl DynEnv {
    fn insert(&mut self, v: Value) {
        self.vs.push(v);
    }

    fn get(&self, v: Variable) -> Option<&Value> {
        self.vs.iter().rev().nth(v.get_index())
    }

    fn drop(&mut self) {
        self.vs.pop();
    }

    fn reduce(&mut self, t: Term) -> Fallible<Value> {
        use Term::*;
        match t {
            Var(v) => self
                .get(v)
                .cloned()
                .ok_or_else(|| format_err!("unbound variable: {:?}", v)),
            Abs(_, t) => Ok(Value::Closure(Closure {
                body: *t,
                env: self.clone(),
            })),
            App(t1, t2) => {
                let v1 = self.reduce(*t1)?;
                let v2 = self.reduce(*t2)?;
                match v1 {
                    Value::Closure(cls) => {
                        let mut env = cls.env;
                        env.insert(v2);
                        env.reduce(cls.body)
                    }
                    _ => bail!("not closure: {:?}", v1),
                }
            }
            Record(r) => Ok(Value::Record(
                r.0.into_iter()
                    .map(|(l, t)| Ok((l, self.reduce(t)?)))
                    .collect::<Fallible<_>>()?,
            )),
            Proj(t, l) => match self.reduce(*t)? {
                Value::Record(r) => r
                    .get(&l)
                    .cloned()
                    .ok_or_else(|| format_err!("unknown label: {:?}", l)),
                v => bail!("not record: {:?}", v),
            },
            Poly(_, t) => Ok(Value::TypeClosure(TypeClosure {
                body: *t,
                env: self.clone(),
            })),
            Inst(t, _) => match self.reduce(*t)? {
                Value::TypeClosure(cls) => {
                    let mut env = cls.env;
                    env.reduce(cls.body)
                }
                v => bail!("not type closure: {:?}", v),
            },
            Pack(_, t, _) => Ok(Value::pack(self.reduce(*t)?)),
            Unpack(t1, t2) => match self.reduce(*t1)? {
                Value::Pack(v) => {
                    self.insert(*v);
                    let v = self.reduce(*t2)?;
                    self.drop();
                    Ok(v)
                }
                v => bail!("not package: {:?}", v),
            },
            Int(n) => Ok(Value::Int(n)),
        }
    }
}

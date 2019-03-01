//! Modules

#![feature(bind_by_move_pattern_guards)]
#![feature(never_type)]
#![feature(try_from)]

pub mod rrd2014;

use failure::bail;
use failure::Fallible;

use rrd2014::internal;
use rrd2014::internal::dynamic;
use rrd2014::parser;

pub fn exec<I>(src: I) -> Fallible<()>
where
    I: IntoIterator<Item = char>,
{
    let m = parser::parse(src)?;
    let (t, asig, gtenv) = rrd2014::elaborate(m)?;
    let ty = internal::typecheck(&t, gtenv)?;
    let expected = asig.into();
    if !ty.equal(&expected) {
        bail!("invariant violation");
    }
    let _ = dynamic::reduce(t)?;
    Ok(())
}

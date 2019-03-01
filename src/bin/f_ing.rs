use structopt::StructOpt;

use failure::format_err;
use failure::Error;
use failure::ResultExt;

use colored::*;

use modules::rrd2014;
use modules::rrd2014::internal;
use modules::rrd2014::internal::dynamic;
use modules::rrd2014::parser;
use modules::rrd2014::Module;

macro_rules! exitln {
    ( $code:expr, $($x:expr),* ) => {
        {
            eprintln!($($x),*);
            std::process::exit($code);
        }
    }
}

#[derive(StructOpt, Debug)]
#[structopt(name = "f-ing", author = "", version_short = "v")]
/// F-ing modules.
enum Opt {
    #[structopt(name = "parse")]
    /// Parses a program.
    Parse {
        /// Input filename
        #[structopt(name = "filename")]
        file: String,
    },

    #[structopt(name = "typecheck")]
    /// Typechecks a program.
    Typecheck {
        /// Input filename
        #[structopt(name = "filename")]
        file: String,

        /// Output filename
        #[structopt(short = "o")]
        output: Option<String>,
    },

    #[structopt(name = "typecheck-internal")]
    /// Translates a program into an internal program, and then typechecks it to ensure type
    /// soundness.
    TypecheckInternal {
        /// Input filename
        #[structopt(name = "filename")]
        file: String,
    },

    #[structopt(name = "exec")]
    /// Executes a program.
    Exec {
        /// Input filename
        #[structopt(name = "filename")]
        file: String,
    },
}

fn main() {
    if let Err(e) = run(Opt::from_args()) {
        exitln!(1, "{}", e);
    }
}

fn run(opt: Opt) -> Result<(), Error> {
    match opt {
        Opt::Parse { file } => {
            println!("{:?}", parse(file)?);
        }
        Opt::Typecheck { file, output } => match elaborate(parse(file)?)? {
            (t, asig, _) => {
                println!("{}:", "signature".bright_cyan().bold());
                println!("{:?}", asig);
                println!();
                println!("{}:", "translated F\u{03c9} term".bright_cyan().bold());
                println!("{:?}", t);
                if let Some(f) = output {
                    std::fs::write(f, format!("{:#?}", t))?;
                }
            }
        },
        Opt::TypecheckInternal { file } => match elaborate(parse(file)?)? {
            (t, asig, gtenv) => {
                let ty = internal::typecheck(&t, gtenv).with_context(|e| {
                    format!(
                        "{}:\n{}",
                        "[bug(unsound)] internal type error".bright_red().bold(),
                        e
                    )
                })?;
                let expect = asig.into();
                if ty.equal(&expect) {
                    println!("{}", "The translation is sound.".bright_green().bold());
                    println!("{}", "internal type:".bright_cyan().bold());
                    println!("{:?}", ty);
                } else {
                    Err(format_err!(
                        "{}:\ntype mismatch:\n{:?}\nand\n{:?}",
                        "[bug] invariant violation".bright_red().bold(),
                        ty,
                        expect
                    ))?;
                }
            }
        },
        Opt::Exec { file } => match elaborate(parse(file)?)? {
            (t, asig, gtenv) => {
                let ty = internal::typecheck(&t, gtenv).with_context(|e| {
                    format!(
                        "{}:\n{}",
                        "[bug(unsound)] internal type error".bright_red().bold(),
                        e
                    )
                })?;
                let expect = asig.into();
                if ty.equal(&expect) {
                    let v = dynamic::reduce(t)?;
                    println!("{}:", "result".bright_green().bold());
                    println!("{:?}", v);
                } else {
                    Err(format_err!(
                        "{}:\ntype mismatch:\n{:?}\nand\n{:?}",
                        "[bug] invariant violation".bright_red().bold(),
                        ty,
                        expect
                    ))?;
                }
            }
        },
    }
    Ok(())
}

fn parse<P>(file: P) -> Result<Module, Error>
where
    P: AsRef<std::path::Path>,
{
    parser::parse_file(&file)
}

fn elaborate(
    m: Module,
) -> Result<(internal::Term, rrd2014::AbstractSig, Vec<internal::Kind>), Error> {
    Ok(rrd2014::elaborate(m)
        .with_context(|e| format!("{}:\n{}", "type error".bright_red().bold(), e))?)
}

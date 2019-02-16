use structopt::StructOpt;

use failure::format_err;
use failure::Error;

use modules::rrd2014::elaborate;
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
        Opt::Typecheck { file } => match elaborate(parse(file)?)? {
            (t, asig) => {
                println!("signature:");
                println!("{:?}", asig);
                println!();
                println!("translated term:");
                println!("{:?}", t);
            }
        },
    }
    Ok(())
}

fn parse<P>(file: P) -> Result<Module, Error>
where
    P: AsRef<std::path::Path>,
{
    parser::parse_file(&file)?.ok_or_else(|| format_err!("parse error"))
}

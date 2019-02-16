use structopt::StructOpt;

use modules::rrd2014::parser;

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
}

fn main() {
    let opt = Opt::from_args();
    match opt {
        Opt::Parse { file } => match parser::parse_file(&file) {
            Ok(Some(b)) => println!("{:?}", b),
            Ok(None) => exitln!(1, "parse error"),
            Err(e) => exitln!(1, "{}", e),
        },
    }
}

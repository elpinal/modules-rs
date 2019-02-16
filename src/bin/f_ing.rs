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
struct Opt {
    /// Input filename
    #[structopt(name = "filename")]
    file: String,
}

fn main() {
    let opt = Opt::from_args();
    match parser::parse_file(&opt.file) {
        Ok(Some(b)) => println!("{:?}", b),
        Ok(None) => exitln!(1, "parse error"),
        Err(e) => exitln!(1, "{}", e),
    }
}

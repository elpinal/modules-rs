# Modules

This repository contains an interpreter of F-ing modules in Rust.

## Install

Use Rust nightly.

```
$ cargo install --git https://github.com/elpinal/modules-rs
```

## Usage

```
$ f_ing
f-ing 0.1.0
F-ing modules.

USAGE:
    f_ing <SUBCOMMAND>

FLAGS:
    -h, --help       Prints help information
    -v, --version    Prints version information

SUBCOMMANDS:
    exec                  Executes a program.
    help                  Prints this message or the help of the given subcommand(s)
    parse                 Parses a program.
    typecheck             Typechecks a program.
    typecheck-internal    Translates a program into an internal program, and then typechecks it to ensure type
                          soundness.
```

## See also

- [elpinal/modules](https://github.com/elpinal/modules)
contains my previous implementation of F-ing modules in Haskell.

## Reference

Andreas Rossberg, Claudio V. Russo and Derek Dreyer.  
F-ing modules.  
Journal of Functional Programming, 24(5), 2014.  
[PDF](https://people.mpi-sws.org/~rossberg/f-ing/f-ing-jfp.pdf).

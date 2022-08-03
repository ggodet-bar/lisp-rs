use crate::lisprs::error::Error;
use crate::lisprs::Cell;
use clap::{ArgGroup, Parser};
use filesystem::{FileSystem, OsFileSystem};
use std::path::PathBuf;

mod lisprs;

#[derive(Parser, Debug)]
#[clap(group(ArgGroup::new("input").required(true).multiple(false)))]
struct Args {
    #[clap(group = "input")]
    file_path: Option<PathBuf>,

    #[clap(group = "input", short, long)]
    eval: Option<String>,
}

fn main() -> Result<(), Error> {
    let fs = OsFileSystem::new();
    let args = Args::parse();
    let expr_str = if let Some(file_path) = args.file_path {
        fs.read_file_to_string(&file_path)?
    } else {
        args.eval.unwrap()
    };

    let mut env = lisprs::LispEnv::new();

    let program = env.parse(&expr_str)?;
    let result = env.evaluate(program)?;

    println!("{}", Cell::format_component(result));

    Ok(())
}

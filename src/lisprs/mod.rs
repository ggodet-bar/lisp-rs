mod cell;
mod core;
pub mod evaluator;
mod iter;
mod lisp_env;
pub mod parser;
mod util;

pub use lisp_env::LispEnv;

#[derive(rust_embed::RustEmbed)]
#[folder = "stdlib/"]
struct Assets;

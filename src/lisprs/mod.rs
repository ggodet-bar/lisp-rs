mod cell;
mod core;
pub mod evaluator;
mod frame;
mod iter;
mod lisp_env;
mod list;
pub mod parser;
mod symbol;
mod util;

pub use cell::Cell;
pub use lisp_env::LispEnv;

#[derive(rust_embed::RustEmbed)]
#[folder = "stdlib/"]
struct Assets;

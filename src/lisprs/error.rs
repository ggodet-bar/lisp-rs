use std::str::Utf8Error;

#[derive(err_derive::Error, Debug)]
pub enum Error {
    #[error(display = "Failed to access file: {:?}", _0)]
    Io(#[error(from)] std::io::Error),

    #[error(display = "Failed to parse Lisp expr: {:?}", _0)]
    Parsing(#[error(from)] pest::error::Error<super::parser::Rule>),

    #[error(display = "File encoding error: {:?}", _0)]
    Encoding(#[error(from)] Utf8Error),

    #[error(display = "Evaluation error")]
    Evaluation(#[error(from)] super::evaluator::Error),
}

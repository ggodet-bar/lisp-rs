use crate::lisprs::lisp_env::LispFunction;

mod add;
mod def;
mod mult;
mod put;
mod quote;
mod structural_eq;
mod symbols;

pub static CORE_FUNCTIONS: &'static [&dyn LispFunction] = &[
    &add::Add,
    &def::Def,
    &structural_eq::Eq,
    &mult::Mult,
    &put::Put,
    &quote::Quote,
    &symbols::Symbols,
];

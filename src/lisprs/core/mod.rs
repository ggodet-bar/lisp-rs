use crate::lisprs::lisp_env::LispFunction;

mod add;
mod def;
mod eq;
mod mult;
mod put;
mod quote;
mod symbols;

pub static CORE_FUNCTIONS: &'static [&dyn LispFunction] = &[
    &add::Add,
    &def::Def,
    &eq::Eq,
    &mult::Mult,
    &put::Put,
    &quote::Quote,
    &symbols::Symbols,
];

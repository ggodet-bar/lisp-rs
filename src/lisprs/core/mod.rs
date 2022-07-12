use crate::lisprs::lisp_env::LispFunction;

mod add;
mod car;
mod cdr;
mod def;
mod r#if;
mod mult;
mod not;
mod put;
mod quote;
mod structural_eq;
mod symbols;

pub static CORE_FUNCTIONS: &'static [&dyn LispFunction] = &[
    &add::Add,
    &car::Car,
    &cdr::Cdr,
    &def::Def,
    &structural_eq::Eq,
    &r#if::If,
    &mult::Mult,
    &not::Not,
    &put::Put,
    &quote::Quote,
    &symbols::Symbols,
];

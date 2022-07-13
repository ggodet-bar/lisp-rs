use crate::lisprs::lisp_env::LispFunction;

mod add;
mod car;
mod cdr;
mod def;
mod r#if;
mod lt_equal;
mod mult;
mod not;
mod put;
mod quote;
mod structural_eq;
mod sub;
mod symbols;

pub static CORE_FUNCTIONS: &'static [&dyn LispFunction] = &[
    &add::Add,
    &car::Car,
    &cdr::Cdr,
    &def::Def,
    &r#if::If,
    &lt_equal::LtEqual,
    &mult::Mult,
    &not::Not,
    &put::Put,
    &quote::Quote,
    &structural_eq::Eq,
    &sub::Sub,
    &symbols::Symbols,
];

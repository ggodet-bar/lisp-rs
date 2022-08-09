use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{is_symbol_ptr, ptr};
use crate::lisprs::LispEnv;
use log::*;

pub struct Car;

impl LispFunction for Car {
    fn symbol(&self) -> String {
        "car".to_string()
    }

    fn function(
        &self,
        arg_idx: usize,
        env: &LispEnv,
    ) -> Result<u64, super::super::evaluator::Error> {
        let first_arg_ptr = env.memory.borrow_mem(arg_idx).cell.car;
        let first_arg_result = env.evaluate_atom(first_arg_ptr)?;
        trace!(
            "First arg ptr: {}",
            Cell::format_component(first_arg_result)
        );
        if first_arg_result == 0 {
            return Ok(0);
        }
        if is_symbol_ptr(first_arg_result) {
            unimplemented!()
        } else {
            let result = env.memory.borrow_mem(ptr(first_arg_result)).cell.car;
            trace!("Car result {}", Cell::format_component(result));

            Ok(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::as_number;
    use crate::lisprs::LispEnv;

    #[test]
    fn single_element_list_returns_element() {
        let mut env = LispEnv::new();
        let program = env.parse("(car (1))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(1, as_number(result));
    }

    #[test]
    fn empty_list_returns_empty_list() {
        let mut env = LispEnv::new();
        let program = env.parse("(car ())").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(0, result);
    }

    #[test]
    fn multi_element_list_returns_first_element() {
        let mut env = LispEnv::new();
        let program = env.parse("(car (1 2 3 4))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(1, as_number(result));
    }

    #[test]
    fn evaluate_list() {
        let mut env = LispEnv::new();
        let program = env.parse("(car (cdr (1 2 3 4)))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());

        env.print_memory();

        let result = result.unwrap();
        assert_eq!(2, as_number(result));
    }
}

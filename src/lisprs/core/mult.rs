use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{as_number, is_number, number_pointer};
use crate::lisprs::LispEnv;
use log::*;

pub struct Mult;

impl LispFunction for Mult {
    fn symbol(&self) -> String {
        "*".to_string()
    }

    fn function(
        &self,
        args_idx: usize,
        env: &LispEnv,
    ) -> Result<u64, super::super::evaluator::Error> {
        let result = {
            let args = env.memory.borrow()[args_idx].clone();
            let mut result = as_number(env.evaluate_atom(args.car)?);
            let mut current_cell = args;
            while current_cell.cdr != 0 {
                trace!("* current cell: {:?}", current_cell);
                let next_cell = env.memory.borrow()[current_cell.cdr_ptr()].clone();
                trace!("Next cell: {:?}", next_cell);

                let next_value = env.evaluate_atom(next_cell.car)?;
                if !is_number(next_value) {
                    panic!("Expected a number!");
                }
                trace!("Next value: {}", Cell::format_component(next_value));
                result *= as_number(next_value);
                trace!("current result: {}", result);

                current_cell = next_cell;
            }

            result
        };
        Ok(number_pointer(result))
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::number_pointer;
    use crate::lisprs::LispEnv;

    #[test]
    fn simple_multiplication() {
        let mut env = LispEnv::new();
        let program = env.parse("(* 3 4)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(number_pointer(12), result);
    }

    #[test]
    fn multiple_terms() {
        let mut env = LispEnv::new();
        let program = env.parse("(* 3 4 5)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(number_pointer(60), result);
    }

    #[test]
    fn nested_multiplication() {
        let mut env = LispEnv::new();
        let program = env.parse("(* 3 (* 2 3))").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(number_pointer(18), result);
    }
}

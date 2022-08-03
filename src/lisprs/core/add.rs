use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{as_number, is_number, number_pointer};
use crate::lisprs::LispEnv;
use log::*;

pub struct Add;

impl LispFunction for Add {
    fn symbol(&self) -> String {
        "+".to_string()
    }

    fn function(
        &self,
        args_idx: usize,
        env: &LispEnv,
    ) -> Result<u64, super::super::evaluator::Error> {
        let sum = {
            let mut sum = 0;
            let mut current_cell = env.memory.borrow()[args_idx].clone();

            loop {
                trace!("+ current cell: {:?}", current_cell);

                let value = env.evaluate_atom(current_cell.car)?;
                if !is_number(value) {
                    panic!("Unexpected result in addition");
                }

                sum += as_number(value);
                trace!("current sum: {}", sum);

                if current_cell.cdr == 0 {
                    break;
                }
                current_cell = env.memory.borrow()[current_cell.cdr_ptr()].clone();
            }

            sum
        };
        // TODO Return a short nb whenever possible, or encode the result on the heap and
        //      return its pointer
        Ok(number_pointer(sum))
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::{as_number, is_number, number_pointer};
    use crate::lisprs::LispEnv;

    #[test]
    fn evaluate_simple_addition() {
        let mut env = LispEnv::new();
        let program = env.parse("(+ 1 2)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(number_pointer(3), result);
    }

    #[test]
    fn parse_nested_operation_1() {
        let mut env = LispEnv::new();
        let program = env.parse("(+ (+ 1 2) 4)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(7, as_number(result));
    }

    #[test]
    fn parse_nested_operation_2() {
        let mut env = LispEnv::new();
        let program = env.parse("(+ (+ 1 2) (+ 3 (+ 4 5 6)))").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(21, as_number(result));
    }
}

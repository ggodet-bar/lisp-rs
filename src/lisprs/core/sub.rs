use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{as_number, is_number, number_pointer, ptr};
use crate::lisprs::LispEnv;

pub struct Sub;

impl LispFunction for Sub {
    fn symbol(&self) -> String {
        "-".to_string()
    }

    fn function(
        &self,
        arg_idx: usize,
        env: &LispEnv,
    ) -> Result<u64, super::super::evaluator::Error> {
        let (first_term, second_term) = {
            let first_arg_cell = &env.memory.borrow()[arg_idx];
            let second_arg_cell = &env.memory.borrow()[ptr(first_arg_cell.cdr)];

            (first_arg_cell.car, second_arg_cell.car)
        };

        let first_term = env.evaluate_atom(first_term)?;
        let second_term = env.evaluate_atom(second_term)?;

        if !is_number(first_term) || !is_number(second_term) {
            panic!("Looking for numbers");
        }

        let result = number_pointer(as_number(first_term) - as_number(second_term));
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::number_pointer;
    use crate::lisprs::LispEnv;

    #[test]
    fn basic_subtraction() {
        let mut env = LispEnv::new();
        let program = env.parse("(- 4 1)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(number_pointer(3), result);
    }
}

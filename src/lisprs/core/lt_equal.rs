use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{as_number, is_number, ptr, true_symbol};
use crate::lisprs::LispEnv;

pub struct LtEqual;

impl LispFunction for LtEqual {
    fn symbol(&self) -> String {
        "<=".to_string()
    }

    fn function(
        &self,
        arg_idx: usize,
        env: &LispEnv,
    ) -> Result<u64, super::super::evaluator::Error> {
        let (first_term, second_term) = {
            let mem = env.memory.borrow();
            let first_arg_cell = &mem[arg_idx];
            let second_arg_cell = &mem[ptr(first_arg_cell.cdr)];

            (first_arg_cell.car, second_arg_cell.car)
        };

        let first_term = env.evaluate_atom(first_term)?;
        let second_term = env.evaluate_atom(second_term)?;

        if !is_number(first_term) || !is_number(second_term) {
            panic!("Looking for numbers");
        }

        Ok(if as_number(first_term) <= as_number(second_term) {
            true_symbol()
        } else {
            0
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::true_symbol;
    use crate::lisprs::LispEnv;

    #[test]
    fn lower() {
        let mut env = LispEnv::new();
        let program = env.parse("(<= 1 4)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(true_symbol(), result);
    }

    #[test]
    fn equal() {
        let mut env = LispEnv::new();
        let program = env.parse("(<= 4 4)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(true_symbol(), result);
    }

    #[test]
    fn greater() {
        let mut env = LispEnv::new();
        let program = env.parse("(<= 4 1)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(0, result);
    }
}

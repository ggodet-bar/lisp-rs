use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::LispEnv;

pub struct Not;

impl LispFunction for Not {
    fn symbol(&self) -> String {
        "not".to_string()
    }

    fn function(&self, arg_idx: usize, env: &LispEnv) -> u64 {
        let first_ptr = env.memory.borrow()[arg_idx].car;
        let result = env.evaluate_atom(first_ptr).unwrap();
        if result == 0 {
            Cell::encode_symbol_name("T").0
        } else {
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::is_true;
    use crate::lisprs::LispEnv;

    #[test]
    fn expects_nil() {
        let mut env = LispEnv::new();
        let program = env.parse("(not (= 1 1))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(0, result.unwrap());
    }

    #[test]
    fn expects_true() {
        let mut env = LispEnv::new();
        let program = env.parse("(not (= 1 2))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert!(is_true(result.unwrap()));
    }
}

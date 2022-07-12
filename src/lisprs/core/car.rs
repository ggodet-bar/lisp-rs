use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{is_symbol_ptr, ptr};
use crate::lisprs::LispEnv;

pub struct Car;

impl LispFunction for Car {
    fn symbol(&self) -> String {
        "car".to_string()
    }

    fn function(&self, arg_idx: usize, env: &LispEnv) -> u64 {
        let first_arg_ptr = env.memory.borrow()[arg_idx].car;
        if is_symbol_ptr(first_arg_ptr) {
            unimplemented!()
        } else {
            env.memory.borrow()[ptr(first_arg_ptr)].car
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::{as_number, is_pointer, is_true, ptr};
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
}

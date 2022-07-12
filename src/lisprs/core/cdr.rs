use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::ptr;
use crate::lisprs::LispEnv;

pub struct Cdr;

impl LispFunction for Cdr {
    fn symbol(&self) -> String {
        "cdr".to_string()
    }

    fn function(&self, args_idx: usize, env: &LispEnv) -> u64 {
        let list_ptr = env.memory.borrow()[args_idx].car;
        env.memory.borrow()[ptr(list_ptr)].cdr
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::{as_number, is_pointer, is_true, ptr};
    use crate::lisprs::LispEnv;

    #[test]
    fn single_element_list_returns_empty_list() {
        let mut env = LispEnv::new();
        let program = env.parse("(cdr (1))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(0, result);
    }

    #[test]
    fn empty_list_returns_empty_list() {
        let mut env = LispEnv::new();
        let program = env.parse("(cdr ())").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(0, result);
    }

    #[test]
    fn multi_element_list() {
        let mut env = LispEnv::new();
        let program = env.parse("(cdr (1 2 3 4))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());

        env.print_memory();
        let result = result.unwrap();
        assert!(is_pointer(result));

        let first_item = env.memory.borrow()[ptr(result)].car;
        assert_eq!(2, as_number(first_item));

        let test = env.parse("(= (2 3 4) (cdr (1 2 3 4)))").unwrap();
        let test_result = env.evaluate(test).unwrap();
        assert!(is_true(test_result));
    }
}
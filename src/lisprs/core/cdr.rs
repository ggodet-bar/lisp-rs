use crate::lisprs::cell::Cell;
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
        let evaluated_ptr = env.evaluate_atom(list_ptr).unwrap();
        println!("First cdr arg: {}", Cell::format_component(evaluated_ptr));
        env.memory.borrow()[ptr(evaluated_ptr)].cdr
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::list::List;
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

    #[test]
    fn evaluate_list() {
        let mut env = LispEnv::new();
        let program = env.parse("(def X (1 2 3 4))\n(cdr X)").unwrap();
        println!("------");
        let result = env.evaluate(program);
        assert!(result.is_ok());

        env.print_memory();
        // FIXME The way the property is stored in the _lisprs struct conflicts with the weird
        //       symbol-like data struct we end up using because we lazy...
        let result = dbg!(result).unwrap();
        assert_ne!(0, result);
        assert!(is_pointer(result));

        let list_values = List::as_list(result, &env)
            .iter()
            .map(|val| as_number(val))
            .collect::<Vec<i64>>();
        assert_eq!([2, 3, 4].to_vec(), list_values);
    }
}

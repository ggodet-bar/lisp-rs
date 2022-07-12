use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{as_number, is_number, is_symbol_ptr, ptr};
use crate::lisprs::LispEnv;

pub struct If;

impl LispFunction for If {
    fn symbol(&self) -> String {
        "if".to_string()
    }

    fn function(&self, args_idx: usize, env: &LispEnv) -> u64 {
        let condition_cell = &env.memory.borrow()[args_idx];
        let true_cell = &env.memory.borrow()[ptr(condition_cell.cdr)];
        let condition = env.evaluate_atom(condition_cell.car).unwrap();
        if condition == 0 || is_number(condition) || is_symbol_ptr(condition) {
            // if post-evaluation the symbol returns itself, then its value is true
            if condition != 0 && as_number(condition_cell.car) != 0 {
                true_cell.car
            } else {
                let false_cell = &env.memory.borrow()[ptr(true_cell.cdr)];
                false_cell.car
            }
        } else {
            unimplemented!()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::{as_number, is_number};
    use crate::lisprs::LispEnv;

    #[test]
    fn if_true() {
        let mut env = LispEnv::new();
        let program = env.parse("(if T 1 2)").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(1, as_number(result));
    }

    #[test]
    fn if_false() {
        let mut env = LispEnv::new();
        let program = env.parse("(if NIL 1 2)").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(2, as_number(result));
    }

    #[test]
    fn if_with_function_eval() {
        let mut env = LispEnv::new();
        let program = env.parse("(if (= 2 1) 1 2)").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(2, as_number(result));
    }
}

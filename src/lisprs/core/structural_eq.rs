use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{is_pointer, ptr};
use crate::lisprs::LispEnv;
use std::collections::VecDeque;

pub struct Eq;

impl LispFunction for Eq {
    fn symbol(&self) -> String {
        "=".to_string()
    }

    fn function(&self, args_idx: usize, env: &LispEnv) -> u64 {
        let memory = env.memory.borrow();
        let first_arg_slot = &memory[args_idx];
        println!("arg cell: {:?}", first_arg_slot);
        // TODO List iterator!!!
        if first_arg_slot.cdr == 0 {
            unimplemented!()
        }

        let second_arg_slot = &memory[ptr(first_arg_slot.cdr)];
        if second_arg_slot.cdr != 0 {
            unimplemented!()
        }

        let mut pending_cells = VecDeque::new();

        // Since the arg slot are defining a list, we'll necessarily have different cdrs,
        // since first_arg_slot will be pointing to second_arg_slot, so we just compare the
        // actual values, i.e. the cars
        if !Eq::compare_half_cells(
            first_arg_slot.car,
            second_arg_slot.car,
            env,
            &mut pending_cells,
        ) {
            return env.nil_key;
        }

        while let Some((left, right)) = pending_cells.pop_front() {
            println!("Left cell: {:?}, Right cell: {:?}", left, right);
            if !Eq::compare_half_cells(left.car, right.car, env, &mut pending_cells) {
                return env.nil_key;
            }

            if !Eq::compare_half_cells(left.cdr, right.cdr, env, &mut pending_cells) {
                return env.nil_key;
            }
        }

        Cell::encode_symbol_name("T").0
    }
}

impl Eq {
    fn compare_half_cells(
        left: u64,
        right: u64,
        env: &LispEnv,
        pending_cells: &mut VecDeque<(Cell, Cell)>,
    ) -> bool {
        if left == right {
            true
        } else if is_pointer(left) && is_pointer(right) {
            if left == env.nil_key && right == env.nil_key {
                return true;
            } else if left == env.nil_key || right == env.nil_key {
                return false;
            }
            // Recursive call
            let left_cell = env.memory.borrow()[ptr(left)].to_owned();
            let right_cell = env.memory.borrow()[ptr(right)].to_owned();
            pending_cells.push_back((left_cell, right_cell));
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::cell::Cell;
    use crate::lisprs::LispEnv;

    #[test]
    fn unequal_short_numbers() {
        let mut env = LispEnv::new();
        let program = env.parse("(= 1 0)").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(0, result.unwrap());
    }

    #[test]
    fn equal_short_numbers() {
        let mut env = LispEnv::new();
        let program = env.parse("(= 3 3)").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
    }

    #[test]
    fn unequal_short_strings() {
        let mut env = LispEnv::new();
        let program = env.parse("(= \"a\" \"b\")").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(0, result.unwrap());
    }

    #[test]
    fn equal_short_strings() {
        let mut env = LispEnv::new();
        let program = env.parse("(= \"c\" \"c\")").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
    }

    #[test]
    fn unequal_single_element_lists() {
        let mut env = LispEnv::new();
        let program = env.parse("(= (3) (5))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(0, result.unwrap());
    }

    #[test]
    fn equal_single_element_lists() {
        let mut env = LispEnv::new();
        let program = env.parse("(= (7) (7))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
    }

    #[test]
    fn unequal_simple_symbols() {
        let mut env = LispEnv::new();
        let program = env.parse("(= a b)").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(0, result.unwrap());
    }

    #[test]
    fn equal_simple_symbols() {
        let mut env = LispEnv::new();
        let program = env.parse("(= c c)").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
    }

    #[test]
    fn equal_evaluated_lists() {
        let mut env = LispEnv::new();
        let program = env.parse("(= (1 (* 4 5) (+ 1 3)) (1 20 4))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
    }

    #[test]
    fn unequal_symbols_with_different_properties() {
        todo!()
    }

    #[test]
    fn equal_symbols_with_identical_properties() {
        todo!()
    }
}
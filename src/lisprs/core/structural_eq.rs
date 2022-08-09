use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{is_pointer, ptr, true_symbol};
use crate::lisprs::LispEnv;
use std::collections::VecDeque;

pub struct Eq;

impl LispFunction for Eq {
    fn symbol(&self) -> String {
        "=".to_string()
    }

    fn function(
        &self,
        args_idx: usize,
        env: &LispEnv,
    ) -> Result<u64, super::super::evaluator::Error> {
        let (first_arg_slot_car, second_arg_slot_car) = {
            let memory = env.memory.state.borrow();
            let first_arg_slot = &memory.mem[args_idx];
            println!("arg cell: {:?}", first_arg_slot);
            // TODO List iterator!!!
            if first_arg_slot.cdr == 0 {
                unimplemented!()
            }

            let second_arg_slot = &memory.mem[ptr(first_arg_slot.cdr)];
            if second_arg_slot.cdr != 0 {
                unimplemented!()
            }
            (first_arg_slot.car, second_arg_slot.car)
        };

        let mut pending_cells = VecDeque::new();

        // Since the arg slot are defining a list, we'll necessarily have different cdrs,
        // since first_arg_slot will be pointing to second_arg_slot, so we just compare the
        // actual values, i.e. the cars
        if !Eq::compare_half_cells(
            env.evaluate_atom(first_arg_slot_car)?,
            env.evaluate_atom(second_arg_slot_car)?,
            env,
            &mut pending_cells,
        ) {
            return Ok(0);
        }

        while let Some((left, right)) = pending_cells.pop_front() {
            println!("Left cell: {:?}, Right cell: {:?}", left, right);
            if !Eq::compare_half_cells(
                env.evaluate_atom(left.car).unwrap(),
                env.evaluate_atom(right.car).unwrap(),
                env,
                &mut pending_cells,
            ) {
                return Ok(0);
            }

            if !Eq::compare_half_cells(
                env.evaluate_atom(left.cdr).unwrap(),
                env.evaluate_atom(right.cdr).unwrap(),
                env,
                &mut pending_cells,
            ) {
                return Ok(0);
            }
        }

        Ok(true_symbol())
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
            let left_cell = env.memory.borrow_mem(ptr(left)).cell.to_owned();
            let right_cell = env.memory.borrow_mem(ptr(right)).cell.to_owned();
            pending_cells.push_back((left_cell, right_cell));
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::is_true;
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
        assert!(is_true(result.unwrap()));
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
        assert!(is_true(result.unwrap()));
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
        assert!(is_true(result.unwrap()));
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
        assert!(is_true(result.unwrap()));
    }

    #[test]
    fn equal_evaluated_lists() {
        let mut env = LispEnv::new();
        let program = env.parse("(= (1 (* 4 5) (+ 1 3)) (1 20 4))").unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert!(is_true(result.unwrap()));
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

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

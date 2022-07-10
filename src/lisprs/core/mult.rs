use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{as_number, is_number, number_pointer};
use crate::lisprs::LispEnv;

pub struct Mult;

impl LispFunction for Mult {
    fn symbol(&self) -> String {
        "*".to_string()
    }

    fn function(&self, args_idx: usize, env: &LispEnv) -> u64 {
        let result = {
            let memory = env.memory.borrow();

            let args = &memory[args_idx];
            let mut result = as_number(env.evaluate_atom(args.car).unwrap());
            let mut current_cell = args;
            while current_cell.cdr != 0 {
                println!("* current cell: {:?}", current_cell);
                let next_cell = &memory[current_cell.cdr_ptr()];
                println!("Next cell: {:?}", next_cell);

                let next_value = env.evaluate_atom(next_cell.car).unwrap();
                if !is_number(next_value) {
                    panic!("Expected a number!");
                }
                println!("Next value: {}", Cell::format_component(next_value));
                result *= as_number(next_value);
                println!("current result: {}", result);

                current_cell = &next_cell;
            }

            result
        };
        // (env.insert_cell(Cell {
        //     car: number_pointer(result.abs() as u64, result < 0),
        //     cdr: 0,
        // }) << 4) as u64
        number_pointer(result)
    }
}

use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{as_number, is_number, number_pointer};
use crate::lisprs::LispEnv;

pub struct Add;

impl LispFunction for Add {
    fn symbol(&self) -> String {
        "+".to_string()
    }

    fn function(&self, args_idx: usize, env: &LispEnv) -> u64 {
        let sum = {
            let memory = env.memory.borrow();
            let args = &memory[args_idx];
            let mut sum = 0;
            let mut current_cell = args;

            loop {
                println!("+ current cell: {:?}", current_cell);

                let value = env.evaluate_atom(current_cell.car).unwrap();
                if !is_number(value) {
                    panic!("Unexpected result in addition");
                }

                sum += as_number(value);
                println!("current sum: {}", sum);

                if current_cell.cdr == 0 {
                    break;
                }
                current_cell = &memory[current_cell.cdr_ptr()];
            }

            sum
        };
        // TODO Return a short nb whenever possible, or encode the result on the heap and
        //      return its pointer
        number_pointer(sum)
    }
}

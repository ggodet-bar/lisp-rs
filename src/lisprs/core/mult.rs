use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::number_pointer;
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
            let mut result = args.as_number();
            let mut current_cell = args;
            while current_cell.cdr != 0 {
                println!("* current cell: {:?}", current_cell);
                let next_cell = &memory[current_cell.cdr_ptr()];
                println!("Next cell: {:?}", next_cell);
                if !next_cell.is_number() {
                    unimplemented!("handle type error");
                }

                result *= next_cell.as_number(); // FIXME Proper conversion with sign bit!
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

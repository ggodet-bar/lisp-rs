use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{is_pointer, ptr};
use crate::lisprs::LispEnv;

pub struct Def;

impl LispFunction for Def {
    fn symbol(&self) -> String {
        "def".to_string()
    }

    fn function(&self, args_idx: usize, env: &LispEnv) -> u64 {
        let value_head = match env.get_list_length((args_idx as u64) << 4) {
            2 => {
                let (value_head, symbol_cell_idx) = {
                    let memory = env.memory.borrow();
                    let args = &memory[args_idx];
                    println!("arg cell: {:?}", args);

                    (memory[args.cdr_ptr()].car, args.car_ptr())
                };

                let name_ptr = env.memory.borrow()[symbol_cell_idx].car;
                env.append_property(env.internal_symbols_key, name_ptr, value_head);
                value_head
            }
            3 => {
                let (name_car, arg_list_car, body_car) = {
                    let memory = env.memory.borrow();
                    let name_cell = &memory[args_idx];
                    let name_arg = env.memory.borrow()[ptr(name_cell.car)].car;

                    let arg_list_cell = &memory[ptr(name_cell.cdr)];
                    if !is_pointer(arg_list_cell.car) {
                        panic!("Expected an arg list");
                    }

                    let program_body_cell = &memory[ptr(arg_list_cell.cdr)];

                    (name_arg, arg_list_cell.car, program_body_cell.car)
                };
                let result_ptr = env.allocate_empty_cell();
                {
                    let mut result = &mut env.memory.borrow_mut()[result_ptr];
                    result.car = arg_list_car;
                    result.cdr = body_car;
                }

                let result_ptr = (result_ptr as u64) << 4;
                env.append_property(env.internal_symbols_key, name_car, result_ptr);

                result_ptr
            }
            _ => {
                unimplemented!()
            }
        };

        value_head
    }
}

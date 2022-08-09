use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::list::List;
use crate::lisprs::util::{as_ptr, is_pointer, ptr};
use crate::lisprs::LispEnv;

pub struct Def;

impl LispFunction for Def {
    fn symbol(&self) -> String {
        "def".to_string()
    }

    fn function(
        &self,
        args_idx: usize,
        env: &LispEnv,
    ) -> Result<u64, super::super::evaluator::Error> {
        let arg_values = List::as_list(as_ptr(args_idx), &env)
            .iter()
            .collect::<Vec<u64>>();
        let value_head = match arg_values.len() {
            2 => {
                let symbol_ptr = arg_values[0];
                let symbol_name_ptr = env.memory.borrow_mem(ptr(symbol_ptr)).cell.car;
                let symbol_value_ptr = arg_values[1];

                let prop_slot = env.append_property_to_stack(symbol_name_ptr, symbol_value_ptr);
                println!("Appended property to slot {}", ptr(prop_slot));
                symbol_value_ptr
            }
            3 => {
                let (name_car, arg_list_car, body_car) = {
                    let memory = &env.memory.state.borrow();
                    let name_cell = &memory.mem[args_idx];
                    let name_arg = memory.mem[ptr(name_cell.car)].car;

                    let arg_list_cell = &memory.mem[ptr(name_cell.cdr)];
                    if !is_pointer(arg_list_cell.car) {
                        panic!("Expected an arg list");
                    }

                    let program_body_cell = &memory.mem[ptr(arg_list_cell.cdr)];

                    (name_arg, arg_list_cell.car, program_body_cell.car)
                };
                let result_ptr = env.insert_cell(Cell {
                    car: arg_list_car,
                    cdr: body_car,
                });

                let result_ptr = (result_ptr as u64) << 4;
                env.append_property_to_stack(name_car, result_ptr);

                result_ptr
            }
            _ => {
                unimplemented!()
            }
        };

        Ok(value_head)
    }
}

use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::LispEnv;

pub struct Symbols;

impl LispFunction for Symbols {
    fn symbol(&self) -> String {
        "symbols".to_string()
    }

    fn function(&self, args_idx: usize, env: &LispEnv) -> u64 {
        if args_idx == 0 {
            let symbol_name = {
                let first_symbol_slot = &env.memory.borrow()[env.namespaces_idx];
                if first_symbol_slot.cdr != 0 {
                    unimplemented!("actual list of namespaces!")
                }

                // let first_symbol = &env.memory.borrow()[ptr(first_symbol_slot.car)];
                env.symbol_name(first_symbol_slot.car).unwrap()
            };

            let result_idx = env.allocate_empty_cell();
            let mut result_cell = &mut env.memory.borrow_mut()[result_idx];
            println!("Symbol name is {}", symbol_name);
            result_cell.car = Cell::encode_symbol_name(&symbol_name).0;
            (result_idx as u64) << 4
        } else {
            unimplemented!()
        }
    }
}

use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{as_number, ptr};
use crate::lisprs::LispEnv;

pub struct Put;

impl LispFunction for Put {
    fn symbol(&self) -> String {
        "pub".to_string()
    }

    fn function(&self, args_idx: usize, env: &LispEnv) -> u64 {
        let (symbol_name, symbol_cell_car, property_name_cell_car, property_value) = {
            let memory = env.memory.borrow();
            let args = &memory[args_idx];
            println!("arg cell: {:?}", args);
            let symbol_cell = &memory[ptr(args.car)];
            let symbol_name = Cell::decode_symbol_name(symbol_cell.car);
            let property_name_slot = &memory[ptr(args.cdr)];
            let property_name_cell = &memory[ptr(property_name_slot.car)];
            let property_name = Cell::decode_symbol_name(property_name_cell.car);
            let property_value_slot = &memory[ptr(property_name_slot.cdr)];
            let property_value = property_value_slot.car; // for now we'll assume a short number is encoded in the car
            println!(
                "property name is {}, and value is {:?}",
                property_name,
                as_number(property_value)
            );

            (
                symbol_name,
                symbol_cell.car,
                property_name_cell.car,
                property_value,
            )
        };
        let property_ptr = env
            .get_property(env.internal_symbols_key, &symbol_name)
            .unwrap_or_else(|| env.append_property(env.internal_symbols_key, symbol_cell_car, 0));
        env.append_property(property_ptr, property_name_cell_car, property_value)
    }
}

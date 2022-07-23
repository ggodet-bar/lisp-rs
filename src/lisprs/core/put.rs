use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::{as_number, is_pointer, is_symbol_ptr, ptr};
use crate::lisprs::LispEnv;

pub struct Put;

impl LispFunction for Put {
    fn symbol(&self) -> String {
        "put".to_string()
    }

    fn function(&self, args_idx: usize, env: &LispEnv) -> u64 {
        let (symbol_name, symbol_cell_car, property_name_cell_car, property_value) = {
            let memory = env.memory.borrow();
            let args = &memory[args_idx];
            println!("arg cell: {:?}", args);
            let mut symbol_cell = &memory[ptr(args.car)];

            if is_pointer(args.car) && is_symbol_ptr(symbol_cell.car) {
                if Cell::decode_symbol_name(memory[ptr(symbol_cell.car)].car) == "quote" {
                    let symbol_slot = memory[dbg!(ptr(symbol_cell.cdr))].car;
                    symbol_cell = &memory[dbg!(ptr(symbol_slot))];
                }
            }
            let symbol_name = Cell::decode_symbol_name(symbol_cell.car);

            let property_name_slot = &memory[ptr(args.cdr)];
            let property_name_cell = &memory[ptr(property_name_slot.car)];
            let property_name = Cell::decode_symbol_name(property_name_cell.car);
            let property_value_slot = &memory[ptr(property_name_slot.cdr)];
            let property_value = property_value_slot.car; // for now we'll assume a short number is encoded in the car
            println!(
                "property name is {}, and value is {:?}, appending to {}",
                property_name,
                as_number(property_value),
                symbol_name
            );

            (
                symbol_name,
                symbol_cell.car,
                property_name_cell.car,
                property_value,
            )
        };
        let property_ptr = env
            .get_property_value(env.internal_symbols_key, &symbol_name)
            .unwrap_or_else(|| env.append_property_to_stack(symbol_cell_car, 0));
        println!(
            "Will append to property at {}",
            Cell::format_component(property_ptr)
        );
        env.append_property(property_ptr, property_name_cell_car, property_value)
    }
}

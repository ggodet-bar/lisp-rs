use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::symbol::Symbol;
use crate::lisprs::LispEnv;

pub struct Symbols;

impl LispFunction for Symbols {
    fn symbol(&self) -> String {
        "symbols".to_string()
    }

    fn function(
        &self,
        args_idx: usize,
        env: &LispEnv,
    ) -> Result<u64, super::super::evaluator::Error> {
        if args_idx == 0 {
            let symbol_name = {
                let first_symbol_slot = env.memory.borrow_mem(env.namespaces_idx).cell;
                if first_symbol_slot.cdr != 0 {
                    unimplemented!("actual list of namespaces!")
                }

                // let first_symbol = &env.memory.borrow()[ptr(first_symbol_slot.car)];
                let first_symbol = Symbol::as_symbol(first_symbol_slot.car, env);
                first_symbol.name().unwrap()
            };

            let result_idx = env.allocate_empty_cell();
            let result_cell = &mut env.memory.borrow_mem_mut(result_idx);
            println!("Symbol name is {}", symbol_name);
            result_cell.cell.car = Cell::encode_symbol_name(&symbol_name).0;
            Ok((result_idx as u64) << 4)
        } else {
            unimplemented!()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::cell::Cell;
    use crate::lisprs::util::{is_pointer, ptr};
    use crate::lisprs::LispEnv;

    #[test]
    fn list_single_namespace() {
        let mut env = LispEnv::new();
        let program = env.parse("(symbols)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_pointer(result));

        let root_cell = &env.memory.borrow_mem(ptr(result));
        assert_eq!(Cell::encode_symbol_name("_lisprs").0, root_cell.cell.car);
        assert_eq!(0, root_cell.cell.cdr);
    }
}

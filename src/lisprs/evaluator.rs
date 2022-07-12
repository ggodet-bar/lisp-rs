use crate::lisprs::cell::Cell;
use crate::lisprs::util::{as_ptr, is_number, is_pointer, is_symbol_ptr, ptr};
use crate::lisprs::LispEnv;

#[derive(PartialEq, Debug)]
pub struct Error;

impl LispEnv {
    pub(crate) fn evaluate_atom(&self, statement: u64) -> Result<u64, Error> {
        if statement == 0 {
            // simple shortcut to stop unnecessary recursions on nil cells
            Ok(0)
        } else if is_number(statement) {
            Ok(statement)
        } else if is_symbol_ptr(statement) {
            // TODO Should check in the current context!
            let symbol_cell_car = self.memory.borrow()[ptr(statement)].car;
            if let Some(value) = self.get_property_value(
                self.internal_symbols_key,
                &Cell::decode_symbol_name(symbol_cell_car),
            ) {
                println!(
                    "Found value for {}: {}",
                    Cell::decode_symbol_name(symbol_cell_car),
                    value
                );
                // returned value will be a SLOT, not the property itself
                self.evaluate_atom(value)
            } else {
                println!(
                    "Did not find value for {}",
                    Cell::decode_symbol_name(symbol_cell_car)
                );
                Ok(statement)
            }
        } else if is_pointer(statement) {
            // Then it's a list
            let list_head = self.memory.borrow()[ptr(statement)].clone();
            if is_number(list_head.car) {
                let mut previous_cell_idx = 0_usize;
                let mut current_cell = list_head;
                let mut new_head = 0_usize;
                loop {
                    let statement_result = self.evaluate_atom(current_cell.car)?;
                    let new_cell_idx = self.insert_cell(Cell {
                        car: statement_result,
                        cdr: 0,
                    });
                    if new_head == 0 {
                        new_head = new_cell_idx;
                    }
                    if previous_cell_idx != 0 {
                        let mut previous_cell = &mut self.memory.borrow_mut()[previous_cell_idx];
                        previous_cell.cdr = as_ptr(new_cell_idx);
                    }

                    if current_cell.cdr == 0 {
                        break;
                    } else {
                        current_cell = self.memory.borrow()[ptr(current_cell.cdr)].clone();
                        previous_cell_idx = new_cell_idx;
                    }
                }

                // for now, return the whole list as such
                Ok(as_ptr(new_head))
            } else if is_symbol_ptr(list_head.car) {
                let symbol_name_ptr = self.memory.borrow()[ptr(list_head.car)].car;
                let symbol_name = Cell::decode_symbol_name(symbol_name_ptr);
                println!("Resolving symbol {}", symbol_name);
                if let Some(function) = self.functions.get(&symbol_name) {
                    println!(
                        "Calling function {} on memory idx {}",
                        symbol_name,
                        ptr(list_head.cdr)
                    );
                    Ok(function.function(ptr(list_head.cdr), self))
                } else if let Some(value_or_func) =
                    self.get_property(self.internal_symbols_key, &symbol_name)
                {
                    if is_pointer(value_or_func) {
                        // TODO For now we won't bother that `value_or_func` should probably be a
                        //      symbol pointer, since we have [val | name]
                        let value_cell = self.memory.borrow()[ptr(value_or_func)].clone();
                        println!("Target cell: {:?}", value_cell);
                        if is_pointer(value_cell.car) && value_cell.cdr == symbol_name_ptr {
                            let prog_def_cell = self.memory.borrow()[ptr(value_cell.car)].clone();
                            let params_list_ptr = dbg!(prog_def_cell.car);
                            let prog_body = prog_def_cell.cdr;
                            let arg_list_ptr = list_head.cdr;
                            // TODO Create a proper frame in which to do the symbol matching
                            if self.get_list_length(params_list_ptr)
                                != self.get_list_length(arg_list_ptr)
                            {
                                unimplemented!("Param/arg mismatch");
                            }
                            let params_list_ptr = self.memory.borrow()[ptr(params_list_ptr)].car;
                            let first_param = self.memory.borrow()[ptr(params_list_ptr)].car;
                            let first_arg = self.memory.borrow()[ptr(arg_list_ptr)].car;
                            println!(
                                "Assigning value {} to param {}",
                                Cell::format_component(first_arg),
                                Cell::format_component(first_param)
                            );
                            self.append_property(self.internal_symbols_key, first_param, first_arg);
                            self.print_memory();
                            // panic!(
                            //     "FOUND A PROGRAM with params {}, body {} and params {}",
                            //     Cell::format_component(params_list_ptr),
                            //     Cell::format_component(prog_body),
                            //     Cell::format_component(arg_list_ptr),
                            // );
                            self.evaluate_atom(prog_body)
                        } else {
                            println!("Found value: {}", Cell::format_component(value_or_func));
                            self.evaluate_atom(value_cell.car)
                        }
                    } else {
                        println!("Found value: {}", Cell::format_component(value_or_func));
                        self.evaluate_atom(value_or_func)
                    }
                } else {
                    println!("Didn't find function for {}", symbol_name);
                    Ok(symbol_name_ptr)
                }
            } else if is_pointer(list_head.car) {
                println!("Found pointer to {}", ptr(list_head.car));
                let result = self.evaluate_atom(list_head.car)?;
                if list_head.cdr == 0 {
                    return Ok(result);
                }
                self.evaluate_atom(list_head.cdr)
            } else {
                unreachable!()
            }
        } else {
            unreachable!()
        }
    }

    pub fn evaluate(&self, statement_ptr: usize) -> Result<u64, Error> {
        self.evaluate_atom(as_ptr(statement_ptr))
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::cell::Cell;
    use crate::lisprs::util::{
        as_number, is_number, is_pointer, is_symbol_ptr, number_pointer, ptr,
    };
    use crate::lisprs::LispEnv;

    #[test]
    fn single_number_as_itself() {
        let env = LispEnv::new();
        assert_eq!(Ok(number_pointer(1)), env.evaluate_atom(number_pointer(1)));
    }

    #[test]
    fn symbol_as_itself() {
        let mut env = LispEnv::new();
        let program = env.parse("a").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(Cell::encode_symbol_name("a").0, result);
    }

    #[test]
    fn number_list_as_itself() {
        let mut env = LispEnv::new();
        let program = env.parse("(1 2 3)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_pointer(result));
        assert_eq!(3, env.get_list_length(result));

        let list = &env.memory.borrow()[ptr(result)];
        assert_eq!(number_pointer(1), list.car);

        let entry = &env.memory.borrow()[ptr(list.cdr)];
        assert_eq!(number_pointer(2), entry.car);

        let entry = &env.memory.borrow()[ptr(entry.cdr)];
        assert_eq!(number_pointer(3), entry.car);
    }

    #[test]
    fn eval_operation_in_sublist() {
        let mut env = LispEnv::new();
        let program = env.parse("(2 (* 3 6))").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_pointer(result));
        assert_eq!(2, env.get_list_length(result));
        let list_head = &env.memory.borrow()[ptr(result)];
        assert_eq!(number_pointer(2), list_head.car);

        let list_tail = &env.memory.borrow()[ptr(list_head.cdr)];
        assert!(is_number(list_tail.car));
        assert_eq!(number_pointer(18), list_tail.car);
    }

    #[test]
    fn evaluate_very_small_program() {
        let mut env = LispEnv::new();
        let program = env.parse("(def r 10)\nr").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(10, as_number(result));
    }

    #[test]
    fn evaluate_small_program() {
        let mut env = LispEnv::new();
        let program = env.parse("(def r 10)\n(* pi (* r r))").unwrap();
        let result = env.evaluate(program);

        let result = result.unwrap();
        env.print_memory();
        assert_eq!(300, as_number(result));
    }

    #[test]
    fn store_function_def() {
        let mut env = LispEnv::new();
        let program = env.parse("(def foo (X) X)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        // Stored as a dot list, with car -> args list and cdr -> body
        if let Some(foo_def) = env.get_property_value(env.internal_symbols_key, "foo") {
            assert_eq!(result, foo_def);
            let foo_def_cell = &env.memory.borrow()[ptr(foo_def)];
            assert!(is_pointer(foo_def_cell.car));
            let arg_list_cell = &env.memory.borrow()[ptr(foo_def_cell.car)];
            assert!(is_pointer(arg_list_cell.car));
            assert_eq!(1, env.get_list_length(arg_list_cell.car));

            let first_arg = &env.memory.borrow()[ptr(arg_list_cell.car)];
            assert_eq!("X", Cell::decode_symbol_name(first_arg.car));

            assert_ne!(0, foo_def_cell.cdr);
            assert!(is_pointer(foo_def_cell.cdr));
            assert!(is_symbol_ptr(foo_def_cell.cdr));

            let prog_body = &env.memory.borrow()[ptr(foo_def_cell.cdr)];
            assert_eq!("X", Cell::decode_symbol_name(prog_body.car));
        } else {
            panic!("inconsistent state");
        }
    }

    #[test]
    fn resolve_value_of_global_symbol() {
        let mut env = LispEnv::new();
        let program = env.parse("(def X NIL)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        // Returns the property SLOT, not the value itself!
        assert_eq!(
            "NIL",
            Cell::decode_symbol_name(env.memory.borrow()[ptr(result)].car)
        );

        let program = env.parse("X").unwrap();
        let result = env.evaluate(program);
        env.print_memory();
        assert!(result.is_ok());
        assert_eq!(0, result.unwrap());
    }

    #[test]
    fn assign_property_to_existing_symbol() {
        let mut env = LispEnv::new();
        let program = env.parse("(def X NIL)").unwrap();
        assert!(env.evaluate(program).is_ok());

        let program = env.parse("(put 'X 'a 1)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_ne!(0, result);

        todo!()
    }

    #[test]
    fn assign_property_to_new_symbol() {
        let mut env = LispEnv::new();
        let program = env.parse("(put 'X 'a 1)").unwrap(); // puts a=1 into X
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_ne!(0, result);

        env.print_memory();
        assert!(env.global_scope_contains_property("X"));

        let x_prop = env.get_property(env.internal_symbols_key, "X").unwrap();
        assert_ne!(0, x_prop);
        assert!(env.get_property_value(dbg!(x_prop), "a").is_some());
    }

    #[test]
    fn call_small_program() {
        let mut env = LispEnv::new();
        let program = env.parse("(def foo (X) X)\n(foo 42)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(42, as_number(result));
    }

    #[test]
    fn parse_fibonacci_function() {
        let mut env = LispEnv::new();
        let program = env
            .parse(
                r#"
    (def fib (N)
    	(if (<= N 1) N (+ (fib (- N 1)) (fib (- N 2)))))
    (fib 10)"#,
            )
            .unwrap();
        // returns the nth item in the Fibonacci sequence
        let result = env.evaluate(program);
        println!("Res: {:?}", result);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(number_pointer(55), result);
    }
}

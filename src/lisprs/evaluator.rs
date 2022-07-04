use crate::lisprs::cell::Cell;
use crate::lisprs::util::{is_number, is_pointer, is_symbol_ptr, ptr};
use crate::lisprs::LispEnv;

#[derive(PartialEq, Debug)]
pub struct Error;

impl LispEnv {
    pub(crate) fn evaluate_atom(&self, statement: u64) -> Result<u64, Error> {
        if is_number(statement) {
            return Ok(statement);
        } else if is_symbol_ptr(statement) {
            // TODO Should check in the current context!
            let symbol_cell = &self.memory.borrow()[ptr(statement)];
            return if let Some(value) = self.get_property(
                self.internal_symbols_key,
                &Cell::decode_symbol_name(symbol_cell.car),
            ) {
                Ok(value)
            } else {
                Ok(statement)
            };
        } else if is_pointer(statement) {
            // Then it's a list
            let list_head = &self.memory.borrow()[ptr(statement)];
            if is_number(list_head.car) {
                // for now, return the whole list as such
                return Ok(statement);
            } else if is_symbol_ptr(list_head.car) {
                let symbol_name_ptr = self.memory.borrow()[ptr(list_head.car)].car;
                let symbol_name = Cell::decode_symbol_name(symbol_name_ptr);
                if let Some(function) = self.functions.get(&symbol_name) {
                    println!(
                        "Calling function {} on memory idx {}",
                        symbol_name,
                        ptr(list_head.cdr)
                    );
                    return Ok(function.function(ptr(list_head.cdr), self));
                }
            }
            unimplemented!()
        }

        unreachable!()
    }

    pub fn evaluate(&self, statement_ptr: usize) -> Result<u64, Error> {
        let program_cell = &self.memory.borrow()[statement_ptr];
        if !program_cell.is_list() {
            return Err(Error);
        }

        self.evaluate_atom(program_cell.car)
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
        assert!(is_symbol_ptr(result));
        assert_eq!(
            Cell::encode_symbol_name("a").0,
            env.memory.borrow()[ptr(result)].car
        );
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
    fn evaluate_simple_addition() {
        let mut env = LispEnv::new();
        let program = env.parse("(+ 1 2)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(number_pointer(3), result);
    }

    #[test]
    fn evaluate_simple_multiplication() {
        let mut env = LispEnv::new();
        let program = env.parse("(* 3 4)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        env.print_memory();

        let result = result.unwrap();
        assert_eq!(number_pointer(12), result);
    }

    #[test]
    fn parse_nested_operation_1() {
        let mut env = LispEnv::new();
        let program = env.parse("(+ (+ 1 2) 4)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(7, as_number(result));
    }

    #[test]
    fn parse_nested_operation_2() {
        let mut env = LispEnv::new();
        let program = env.parse("(+ (+ 1 2) (+ 3 (+ 4 5 6)))").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(21, as_number(result));
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
        assert_eq!(300, as_number(result));
    }

    #[test]
    fn store_function_def() {
        let mut env = LispEnv::new();
        let program = env.parse("(def foo (X) X)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        let result = result.unwrap();
        println!("Result ptr: {}", result);
        // Could be stored as a dot list, with car -> args list and cdr -> body?
        env.print_memory();
        if let Some(foo_def) = env.get_property(env.internal_symbols_key, "foo") {
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
        let result = env.parse("(def X NIL)");
        assert!(result.is_ok());

        env.print_memory();
        let result = result.unwrap();
        assert_eq!(0, result);

        let result = env.parse("X");
        assert!(result.is_ok());
        assert_eq!(0, result.unwrap());
    }

    #[test]
    fn assign_property_to_existing_symbol() {
        let mut env = LispEnv::new();
        assert!(env.parse("(def X NIL)").is_ok());

        let result = env.parse("(put 'X 'a 1)");
        assert!(result.is_ok());
        todo!()
    }

    #[test]
    fn assign_property_to_new_symbol() {
        let mut env = LispEnv::new();
        let result = env.parse("(put 'X 'a 1)"); // puts a=1 into X
        assert!(result.is_ok());

        env.print_memory();

        todo!()

        // let result = result.unwrap();
        // assert!(is_pointer(result));
        //
        // assert!(env.global_scope_contains_property("X"));
    }

    //
    //     #[test]
    //     fn call_small_program() {
    //         let mut env = LispEnv::new();
    //         let result = env.parse("(def foo (X) X)\n(foo 42)");
    //         assert!(result.is_ok());
    //         let result = result.unwrap();
    //         println!("Result ptr: {}", ptr(result));
    //         env.print_memory();
    //         assert_eq!(42, as_number(result));
    //
    //         // TODO Detect that the symbol references a program, and applies the arguments to the program
    //     }
    //
    //     #[test]
    //     fn parse_fibonacci_function() {
    //         let mut env = LispEnv::new();
    //         let result = env.parse(
    //             r#"
    // (def fib (N)
    // 	(if (<= N 1) N (+ (fib (- N 1)) (fib (- N 2)))))
    // (fib 10)"#,
    //         );
    //         println!("Res: {:?}", result);
    //         assert!(result.is_ok());
    //
    //         let result = result.unwrap();
    //     }
}

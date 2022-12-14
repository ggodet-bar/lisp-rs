use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::MAX_CYCLES;
use crate::lisprs::symbol::Symbol;
use crate::lisprs::util::{as_ptr, is_number, is_pointer, is_symbol_ptr, ptr};
use crate::lisprs::LispEnv;
use log::*;

#[derive(PartialEq, Debug)]
pub struct Error;

impl LispEnv {
    fn call_function(&self, function_cell: Cell, arg_list_ptr: u64) -> Result<u64, Error> {
        trace!(
            "Calling function {:?} with arg ptr {}",
            function_cell,
            Cell::format_component(arg_list_ptr)
        );
        let params_list_ptr = function_cell.car;
        let prog_body = function_cell.cdr;
        let arg_list_ptr = arg_list_ptr;
        // TODO Create a proper frame in which to do the symbol matching
        if self.get_list_length(params_list_ptr) != self.get_list_length(arg_list_ptr) {
            unimplemented!("Param/arg mismatch");
        }
        let (first_param, first_arg) = {
            let mem = self.memory.state.borrow();
            let first_param = mem.mem[ptr(params_list_ptr)].car;
            // Param is probably a symbol, so we dereference its name
            let first_param = mem.mem[ptr(first_param)].car;
            let first_arg = mem.mem[ptr(arg_list_ptr)].car;

            (first_param, first_arg)
        };
        let first_arg_result = self.evaluate_atom(first_arg).unwrap();
        let frame = self.allocate_frame();
        trace!("New frame ptr: {}", ptr(frame.symbol_map_ptr));
        trace!(
            "Assigning value {} to param {}",
            Cell::format_component(first_arg_result),
            Cell::format_component(first_param)
        );
        frame.append_property(first_param, first_arg_result);
        let result = self.evaluate_atom(prog_body)?;
        trace!("Function result is {}", Cell::format_component(result));
        frame.deallocate();

        Ok(result)
    }

    fn evaluate_symbol(&self, statement: u64) -> Result<u64, Error> {
        let (symbol_cell_car, stack_symbols) = {
            let mem = self.memory.state.borrow();
            let symbol_cell_car = mem.mem[ptr(statement)].car;
            let last_stack_idx = self.get_last_cell_idx(as_ptr(self.stack_frames));
            let last_frame_ptr = mem.mem[last_stack_idx].car;
            let stack_symbols = Symbol::as_symbol(mem.mem[ptr(last_frame_ptr)].car, self);

            (symbol_cell_car, stack_symbols)
        };

        // let symbol_name = Cell::decode_symbol_name(symbol_cell_car);
        trace!("Resolving value of symbol {}", symbol_cell_car);
        if let Some(value) = stack_symbols.get_property_value_by_ptr(symbol_cell_car) {
            trace!(
                "Found value for {}: {}",
                symbol_cell_car,
                Cell::format_component(value)
            );
            // returned value will be a SLOT, not the property itself
            self.evaluate_atom(value)
        } else {
            trace!("Did not find value for {}", symbol_cell_car);
            Ok(statement)
        }
    }

    fn evaluate_list(&self, statement: u64) -> Result<u64, Error> {
        let list_head = self.memory.borrow_mem(ptr(statement)).cell.clone();
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
                    let mut previous_cell = &mut self.memory.borrow_mem_mut(previous_cell_idx);
                    previous_cell.cell.cdr = as_ptr(new_cell_idx);
                }

                if current_cell.cdr == 0 {
                    break;
                } else {
                    current_cell = self.memory.borrow_mem(ptr(current_cell.cdr)).cell.clone();
                    previous_cell_idx = new_cell_idx;
                }
            }

            Ok(as_ptr(new_head))
        } else if is_symbol_ptr(list_head.car) {
            let (frame_symbols, symbol_name_ptr) = {
                let mem = self.memory.state.borrow();
                let symbol_name_ptr = mem.mem[ptr(list_head.car)].car;
                // let symbol_name = Cell::decode_symbol_name(symbol_name_ptr);
                let current_frame_slot = self.get_last_cell_idx(as_ptr(self.stack_frames));
                let current_frame = mem.mem[current_frame_slot].car;
                let frame_symbols = Symbol::as_symbol(mem.mem[ptr(current_frame)].car, self);
                (frame_symbols, symbol_name_ptr)
            };
            trace!("Resolving symbol {}", symbol_name_ptr);
            if let Some(function) = self.functions.get(&symbol_name_ptr) {
                trace!(
                    "Calling function {} on memory idx {}",
                    symbol_name_ptr,
                    ptr(list_head.cdr)
                );
                function.function(ptr(list_head.cdr), self)
            } else if let Some(value_or_func) = frame_symbols
                .get_property_value_by_ptr(symbol_name_ptr)
                .or_else(|| self.global_map().get_property_value_by_ptr(symbol_name_ptr))
            {
                if is_pointer(value_or_func) {
                    // TODO For now we won't bother that `value_or_func` should probably be a
                    //      symbol pointer, since we have [val | name]
                    let value_cell = self.memory.borrow_mem(ptr(value_or_func)).cell.clone();
                    trace!("Target cell: {:?}", value_cell);
                    if is_pointer(value_cell.car)
                        && is_pointer(value_cell.cdr)
                        && !value_cell.is_nil()
                    {
                        self.call_function(value_cell, list_head.cdr)
                    } else {
                        trace!("Found value: {}", Cell::format_component(value_or_func));
                        self.evaluate_atom(value_cell.car)
                    }
                } else {
                    trace!("Found value: {}", Cell::format_component(value_or_func));
                    self.evaluate_atom(value_or_func)
                }
            } else {
                trace!("Didn't find value/function for {}", symbol_name_ptr);
                Ok(statement)
            }
        } else if is_pointer(list_head.car) {
            trace!("Found pointer to {}", ptr(list_head.car));
            let result = self.evaluate_atom(list_head.car)?;
            if list_head.cdr == 0 {
                return Ok(result);
            }
            self.evaluate_atom(list_head.cdr)
        } else {
            unreachable!()
        }
    }

    pub(crate) fn evaluate_atom(&self, statement: u64) -> Result<u64, Error> {
        self.memory.state.borrow_mut().cycle_count += 1;
        if MAX_CYCLES != 0 && self.memory.state.borrow().cycle_count > MAX_CYCLES {
            panic!("Forced exit");
        }

        // if *self.cycle_count.borrow() % GC_PERIOD == 0 {
        //     self.run_garbage_collector();
        // }

        trace!("Evaluating statement {}", Cell::format_component(statement));

        if statement == 0 {
            // simple shortcut to stop unnecessary recursions on nil cells
            Ok(0)
        } else if is_number(statement) {
            Ok(statement)
        } else if is_symbol_ptr(statement) {
            self.evaluate_symbol(statement)
        } else if is_pointer(statement) {
            self.evaluate_list(statement)
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
    use crate::lisprs::list::List;
    use crate::lisprs::symbol::Symbol;
    use crate::lisprs::util::{
        as_number, is_number, is_pointer, is_symbol_ptr, number_pointer, ptr,
    };
    use crate::lisprs::LispEnv;
    use log::*;

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
    fn unify_symbol_references_in_same_scope() {
        let mut env = LispEnv::new();
        let program = env.parse("(a a a)").unwrap();
        let result = env.evaluate(program);
        assert!(result.is_ok());

        env.print_memory();
        let result = result.unwrap();
        let symbol_ptrs = List::as_list(result, &env).iter().collect::<Vec<u64>>();
        assert_eq!(symbol_ptrs[0], symbol_ptrs[1]);
        assert_eq!(symbol_ptrs[0], symbol_ptrs[2]);
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

        let list = env.memory.borrow_mem(ptr(result));
        assert_eq!(number_pointer(1), list.cell.car);

        let entry = env.memory.borrow_mem(ptr(list.cell.cdr));
        assert_eq!(number_pointer(2), entry.cell.car);

        let entry = env.memory.borrow_mem(ptr(entry.cell.cdr));
        assert_eq!(number_pointer(3), entry.cell.car);
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
        let list_head = &env.memory.borrow_mem(ptr(result));
        assert_eq!(number_pointer(2), list_head.cell.car);

        let list_tail = &env.memory.borrow_mem(ptr(list_head.cell.cdr));
        assert!(is_number(list_tail.cell.car));
        assert_eq!(number_pointer(18), list_tail.cell.car);
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
        if let Some(foo_def) = env
            .global_map()
            .get_property_value_by_ptr(Cell::encode_symbol_name("foo").0)
        {
            assert_eq!(result, foo_def);
            let foo_def_cell = &env.memory.borrow_mem(ptr(foo_def));
            assert!(is_pointer(foo_def_cell.cell.car));
            let arg_list_cell = &env.memory.borrow_mem(ptr(foo_def_cell.cell.car));
            assert!(is_pointer(arg_list_cell.cell.car));
            assert_eq!(1, env.get_list_length(arg_list_cell.cell.car));

            let first_arg = &env.memory.borrow_mem(ptr(arg_list_cell.cell.car));
            assert_eq!("X", Cell::decode_symbol_name(first_arg.cell.car));

            assert_ne!(0, foo_def_cell.cell.cdr);
            assert!(is_pointer(foo_def_cell.cell.cdr));
            assert!(is_symbol_ptr(foo_def_cell.cell.cdr));

            let prog_body = &env.memory.borrow_mem(ptr(foo_def_cell.cell.cdr));
            assert_eq!("X", Cell::decode_symbol_name(prog_body.cell.car));
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
            Cell::decode_symbol_name(env.memory.borrow_mem(ptr(result)).cell.car)
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

        let x_prop = env.global_map().get_property_by_name("X").unwrap();
        assert_ne!(0, x_prop);
        let x_symbol = Symbol::as_symbol(x_prop, &env);
        assert!(x_symbol.get_property_value_by_name("a").is_some());
    }

    #[test]
    fn call_small_program() {
        let mut env = LispEnv::new();
        let program = env.parse("(def foo (X) X)\n(foo 42)").unwrap();
        trace!("-----");
        let result = env.evaluate(program);
        assert!(result.is_ok());

        env.print_memory();
        let result = result.unwrap();
        assert_eq!(42, as_number(result));
    }

    #[test]
    fn eval_simple_recursion_terminator() {
        let mut env = LispEnv::new();
        let program = env
            .parse(
                r#"
    (def simprec (N)
    	(
    	    if (<= N 1) N (simprec (- N 1))
    	)
    )
    (simprec 1)"#,
            )
            .unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(as_number(result.unwrap()), 1);
    }

    #[test]
    fn eval_simple_recursion_many_iterations() {
        let mut env = LispEnv::new();
        let program = env
            .parse(
                r#"
    (def simprec (N)
    	(
    	    if (<= N 1) N (simprec (- N 1))
    	)
    )
    (simprec 10)"#,
            )
            .unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(as_number(result.unwrap()), 1);
    }

    #[test]
    fn eval_simple_recursion_combined_with_operation() {
        let mut env = LispEnv::new();
        let program = env
            .parse(
                r#"
    (def simprec (N)
    	(
    	    if (<= N 1) N (+ 2 (simprec (- N 1)))
    	)
    )
    (simprec 10)"#,
            )
            .unwrap();

        let result = env.evaluate(program);
        assert!(result.is_ok());
        assert_eq!(as_number(result.unwrap()), 19);
    }

    #[test]
    fn eval_fibonacci_function_second_entry() {
        let mut env = LispEnv::new();
        let program = env
            .parse(
                r#"
    (def fib (N)
    	(if (<= N 1) N (+ (fib (- N 1)) (fib (- N 2)))))
    (fib 2)"#,
            )
            .unwrap();
        // returns the nth item in the Fibonacci sequence
        trace!("------");
        let result = env.evaluate(program);
        trace!("Res: {:?}", result);
        assert!(result.is_ok());

        let result = result.unwrap();
        trace!("Result: {}", Cell::format_component(result));

        assert_eq!(1, as_number(result));
    }

    #[test]
    fn eval_fibonacci_function_third_entry() {
        let mut env = LispEnv::new();
        let program = env
            .parse(
                r#"
    (def fib (N)
    	(if (<= N 1) N (+ (fib (- N 1)) (fib (- N 2)))))
    (fib 3)"#,
            )
            .unwrap();
        // returns the nth item in the Fibonacci sequence
        trace!("------");
        let result = env.evaluate(program);
        trace!("Res: {:?}", result);
        assert!(result.is_ok());

        let result = result.unwrap();
        trace!("Result: {}", Cell::format_component(result));

        assert_eq!(2, as_number(result));
    }

    #[test]
    fn eval_fibonacci_function_fourth_entry() {
        let mut env = LispEnv::new();
        let program = env
            .parse(
                r#"
    (def fib (N)
    	(if (<= N 1) N (+ (fib (- N 1)) (fib (- N 2)))))
    (fib 4)"#,
            )
            .unwrap();
        // returns the nth item in the Fibonacci sequence
        trace!("------");
        let result = env.evaluate(program);
        trace!("Res: {:?}", result);
        assert!(result.is_ok());

        let result = result.unwrap();
        trace!("Result: {}", Cell::format_component(result));

        assert_eq!(3, as_number(result));
    }

    #[test]
    fn eval_fibonacci_function_fifth_entry() {
        let mut env = LispEnv::new();
        let program = env
            .parse(
                r#"
    (def fib (N)
    	(if (<= N 1) N (+ (fib (- N 1)) (fib (- N 2)))))
    (fib 5)"#,
            )
            .unwrap();
        // returns the nth item in the Fibonacci sequence
        trace!("------");
        let result = env.evaluate(program);
        trace!("Res: {:?}", result);
        assert!(result.is_ok());

        let result = result.unwrap();
        trace!("Result: {}", Cell::format_component(result));

        assert_eq!(5, as_number(result));
    }

    #[test]
    fn eval_fibonacci_function_tenth_entry() {
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
        trace!("------");
        let result = env.evaluate(program);
        trace!("Res: {:?}", result);
        assert!(result.is_ok());

        let result = result.unwrap();
        trace!("Result: {}", Cell::format_component(result));

        env.print_memory();
        assert_eq!(55, as_number(result));
        println!("Memory size: {}", env.memory_size());
    }
}

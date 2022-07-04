use crate::lisprs::cell::Cell;
use crate::lisprs::util::{is_number, is_pointer, ptr};
use crate::lisprs::LispEnv;
use pest::iterators::{Pair, Pairs};
use pest::Parser as PestParser;
use pest_derive::Parser;
use std::fmt::Debug;

#[derive(Parser)]
#[grammar = "./lisprs/lisp.pest"]
pub struct LispGrammar;

impl LispEnv {
    /// Parses the statement into memory and returns a pointer to its position or its direct value,
    /// or an error if parsing failed
    fn parse_atom(&mut self, atom: Pair<Rule>) -> Result<u64, pest::error::Error<Rule>> {
        Ok(match atom.as_rule() {
            Rule::number => self.encode_number(atom.as_str()),
            Rule::symbol => {
                let symbol_name = atom.as_str();
                println!("Allocating symbol {}", symbol_name);
                self.allocate_symbol(Some(symbol_name), self.nil_key)
            }
            Rule::sexpr => self.parse_list(atom.into_inner())?,
            Rule::quoted_atom => {
                // We normalize it as a list
                let list_content = self.parse_atom(atom.into_inner().next().unwrap())?;
                let quote_list_ptr = self.allocate_empty_cell();
                let quote_content_ptr = self.allocate_empty_cell();
                {
                    let quote_ptr = self.allocate_symbol(Some("quote"), 0);
                    let quote_list_cell = &mut self.memory.borrow_mut()[quote_list_ptr];
                    quote_list_cell.car = quote_ptr;
                    quote_list_cell.set_cdr_pointer(quote_content_ptr)
                }
                {
                    let quote_content_cell = &mut self.memory.borrow_mut()[quote_content_ptr];
                    quote_content_cell.car = list_content;
                }

                (quote_list_ptr as u64) << 4
            }
            Rule::string => Cell::encode_symbol_name(atom.as_str()).0,
            _ => unimplemented!("Rule: {}", atom.as_str()),
        })
    }

    /// Returns an optional pointer to the evaluation result, or whether the following should be left
    /// unevaluated (i.e., due to a quote)
    fn eval_atom(
        &mut self,
        atom: Pair<Rule>,
        eval: bool,
        list_level: usize,
    ) -> Result<(Option<u64>, bool), pest::error::Error<Rule>> {
        if !eval {
            println!("Not evaluating the following atom: {}", atom.as_str());
        }
        let cell_value = match atom.as_rule() {
            Rule::number => (Some(self.encode_number(atom.as_str())), false),
            Rule::symbol => {
                let symbol_name = atom.as_str();
                if self.functions.contains_key(symbol_name) && eval {
                    println!("Pushing op {}", symbol_name);
                    self.call_stack.push_back(Some(symbol_name.to_string()));
                    (None, false)
                } else if symbol_name == "quote" {
                    (None, true)
                } else if self.global_scope_contains_property(symbol_name) {
                    println!("Global scope does contain property {}", symbol_name);
                    let (property_ptr, do_eval) = (
                        self.get_property(self.internal_symbols_key, symbol_name),
                        false,
                    );

                    if let Some(property_ptr) = property_ptr {
                        let property_cell = &self.memory.borrow()[ptr(property_ptr)];
                        if property_cell.cdr != 0 {
                            // then this is a program
                            self.call_stack.push_back(Some(symbol_name.to_string()));
                            return Ok((None, false));
                        }
                    }

                    (property_ptr, do_eval)
                } else {
                    println!("Allocating symbol {}", symbol_name);
                    (
                        Some(self.allocate_symbol(Some(symbol_name), self.nil_key)),
                        false,
                    )
                }
            }
            Rule::sexpr => (
                Some(self.eval_list(atom.into_inner(), list_level + 1)? as u64),
                false,
            ),
            Rule::quoted_atom => {
                self.eval_atom(atom.into_inner().next().unwrap(), false, list_level)?
            }
            Rule::string => (Some(Cell::encode_symbol_name(atom.as_str()).0), false),
            _ => unimplemented!("Rule: {}", atom.as_str()),
        };

        Ok(cell_value)
    }

    /// Returns the pointer to the list
    fn parse_list(&mut self, atoms: Pairs<Rule>) -> Result<u64, pest::error::Error<Rule>> {
        println!("--- LIST atoms {:?}", atoms);
        let mut result = 0_u64; // pointer to nil
        let mut list_tail_ptr = 0_usize;

        for atom in atoms {
            let atom_value = self.parse_atom(atom)?;
            let new_cell_idx = self.insert_cell(Cell {
                car: atom_value,
                cdr: 0,
            });
            println!("Appending cell at idx {}", new_cell_idx);
            if result == 0 {
                result = (new_cell_idx as u64) << 4; // then result acts as the list head
            }

            if list_tail_ptr != 0 {
                let mut last_cell = &mut self.memory.borrow_mut()[list_tail_ptr];
                last_cell.cdr = (new_cell_idx as u64) << 4;
            }

            list_tail_ptr = new_cell_idx;
        }

        Ok(result)
    }

    fn eval_list(
        &mut self,
        atoms: Pairs<Rule>,
        level: usize,
    ) -> Result<u64, pest::error::Error<Rule>> {
        // The list eval currently creates a new list with each element being evaluated

        println!("--- LIST atoms {:?}", atoms);

        let mut result = 0_u64; // pointer to nil
        let mut last_cell_ptr = None;
        let mut left_next_unevaluated = false;

        for (idx, atom) in atoms.enumerate() {
            if left_next_unevaluated {
                return self.eval_atom(atom, false, level).map(|val| val.0.unwrap());
            }
            match self.eval_atom(atom, true, level)? {
                (Some(atom_value), _) => {
                    let new_cell_idx = self.insert_cell(Cell {
                        car: atom_value,
                        cdr: 0,
                    });
                    println!("Appending cell at idx {}", new_cell_idx);
                    if result == 0 {
                        result = new_cell_idx as u64; // then result acts as the list head
                    }
                    if let Some(last_cell_ptr) = last_cell_ptr {
                        self.memory.borrow_mut()[last_cell_ptr].set_cdr_pointer(new_cell_idx);
                    }
                    last_cell_ptr = Some(new_cell_idx);
                }
                (_, true) => {
                    left_next_unevaluated = true;
                }
                _ => (),
            }
            if idx == 0 && self.call_stack.len() < level {
                // in that case no symbol was pushed to the stack (after having eval'ed the first
                // item in the list), so we pad it with a None
                println!("PADDING");
                self.call_stack.push_back(None);
            }
        }

        println!(
            "Result: {}, {:?}",
            result,
            &self.memory.borrow()[result as usize]
        );

        if let Some(Some(fn_name)) = self.call_stack.pop_back() {
            println!("About to apply function {}", fn_name);
            self.print_memory();
            result = if let Some(function) = self.functions.get(&fn_name) {
                function.function(result as usize, &self)
            } else if let Some(function_ptr) =
                self.get_property(self.internal_symbols_key, &fn_name)
            {
                // TODO We first need to create a context in which we create variables by mapping
                //      param list to the arg list. Those variables should be in a separate stack!
                //      Then we should run the evaluation by pointing at the function body, which
                //      isn't currently possible as we parse and eval on the fly, instead of building
                //      first an in-memory representation of our program (using symbols and raw
                //      values), and then proceeding to its execution.
                todo!("Handle function call from heap");
            } else {
                panic!("No corresponding symbol");
            };
            self.print_memory();
            println!(
                "New result: {} (ptr: {}, nb: {})",
                result,
                is_pointer(result),
                is_number(result)
            );
            Ok(result)
        } else {
            Ok(result << 4) // we necessarily have a pointer to a list
        }
    }

    // Returns memory index of the head of the parsed statements list
    pub fn parse(&mut self, input: &str) -> Result<usize, pest::error::Error<Rule>> {
        let root = LispGrammar::parse(Rule::lisp, input)?
            .next()
            .unwrap()
            .into_inner();

        println!("Root: {:?}", root);
        let mut statements_list_head_ptr = 0_usize;
        let mut current_statement_ptr = 0_usize;
        for statement in root {
            if statement.as_rule() == Rule::EOI {
                continue;
            }

            let statement_val = self.parse_atom(statement)?;
            let parsed_statements_ptr = self.insert_cell(Cell {
                car: statement_val,
                cdr: 0,
            });

            if statements_list_head_ptr == 0 {
                statements_list_head_ptr = parsed_statements_ptr;
            }

            if current_statement_ptr != 0 {
                self.memory.borrow_mut()[current_statement_ptr].cdr =
                    (parsed_statements_ptr as u64) << 4;
            }

            current_statement_ptr = parsed_statements_ptr;
        }

        Ok(statements_list_head_ptr)
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::cell::Cell;
    use crate::lisprs::parser::LispEnv;
    use crate::lisprs::util::{as_number, is_number, is_pointer, is_symbol_ptr, ptr};

    #[test]
    fn parse_empty_list_and_return_nil() {
        let mut env = LispEnv::new();
        let result = env.parse("()");
        assert!(result.is_ok());

        let statements = result.unwrap();
        assert_eq!(1, env.get_list_length((statements as u64) << 4));
        assert_eq!(0_u64, env.memory.borrow()[statements].car);
    }

    #[test]
    fn parse_symbol_in_list() {
        let mut env = LispEnv::new();
        let result = env.parse("(a)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(1, env.get_list_length((result as u64) << 4));

        let statement = &env.memory.borrow()[result];
        assert!(is_pointer(statement.car));

        let cell = &env.memory.borrow()[ptr(statement.car)];
        assert!(cell.is_list());
        assert!(is_symbol_ptr(cell.car));

        let first_element = &env.memory.borrow()[cell.car_ptr()];
        assert!(first_element.is_number());
        assert_eq!("a", Cell::decode_symbol_name(first_element.car));
    }

    #[test]
    fn parse_list_of_single_short_number() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let result = env.parse("(1)");
        assert!(result.is_ok());
        let result = result.unwrap();

        env.print_memory();
        // The result payload consists of a list of a single statement, pointing at a list with a
        // single value
        assert_eq!(original_memory_size + 2, env.memory.borrow().len());

        let first_statement = &env.memory.borrow()[result];
        assert!(is_pointer(first_statement.car));

        let cell = &env.memory.borrow()[ptr(first_statement.car)];
        assert!(cell.is_list());
        assert_eq!(env.encode_number("1") as u64, cell.car);
        assert_eq!(0, cell.cdr);
    }

    #[test]
    fn parse_list_of_two_numbers() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let result = env.parse("(1 2)");
        assert!(result.is_ok());
        assert_eq!(original_memory_size + 3, env.memory.borrow().len());

        let first_statement = &env.memory.borrow()[result.unwrap()];
        assert!(is_pointer(first_statement.car));

        let list_head = &env.memory.borrow()[ptr(first_statement.car)];
        assert!(list_head.is_list());
        assert_eq!(env.encode_number("1") as u64, list_head.car);

        let list_tail = &env.memory.borrow()[list_head.cdr_ptr()];
        assert!(list_tail.is_list());
        assert_eq!(env.encode_number("2") as u64, list_tail.car);
        assert_eq!(list_tail.cdr, 0);
    }

    #[test]
    fn parse_nested_list() {
        let mut env = LispEnv::new();
        let result = env.parse("((a))");
        assert!(result.is_ok());

        let first_statement = &env.memory.borrow()[result.unwrap()];

        let list_head = &env.memory.borrow()[ptr(first_statement.car)];
        assert!(is_pointer(list_head.car));
        assert_eq!(0, list_head.cdr);

        let nested_list_head = &env.memory.borrow()[ptr(list_head.car)];
        assert!(nested_list_head.is_list());
        assert!(is_symbol_ptr(nested_list_head.car));
        assert_eq!(0, nested_list_head.cdr);

        let symbol = &env.memory.borrow()[ptr(nested_list_head.car)];
        assert_eq!("a", Cell::decode_symbol_name(symbol.car));
    }

    #[test]
    fn parse_quoted_number() {
        let mut env = LispEnv::new();
        let result = env.parse("'1");
        // parsed as (quote 1)
        assert!(result.is_ok());

        let first_statement_ptr = env.memory.borrow()[result.unwrap()].car;
        let first_statement = &env.memory.borrow()[ptr(first_statement_ptr)];
        assert!(first_statement.is_list());
        assert!(is_symbol_ptr(first_statement.car));
        assert_ne!(0, first_statement.cdr);

        let symbol_cell = &env.memory.borrow()[ptr(first_statement.car)];
        assert_eq!(Cell::encode_symbol_name("quote").0, symbol_cell.car);

        let number_cell = &env.memory.borrow()[ptr(first_statement.cdr)];
        assert!(is_number(number_cell.car));
        assert_eq!(1, as_number(number_cell.car));
        assert_eq!(0, number_cell.cdr);
    }

    #[test]
    fn parse_quoted_symbol_with_quote_mark() {
        let mut env = LispEnv::new();
        let result = env.parse("'a");
        assert!(result.is_ok());
        // should be rewritten as `(quote a)`

        let first_statement_ptr = env.memory.borrow()[result.unwrap()].car;
        let first_statement = &env.memory.borrow()[ptr(first_statement_ptr)];
        assert!(first_statement.is_list());
        assert!(is_symbol_ptr(first_statement.car));
        assert_ne!(0, first_statement.cdr);

        let quote_symbol_cell = &env.memory.borrow()[ptr(first_statement.car)];
        assert_eq!(Cell::encode_symbol_name("quote").0, quote_symbol_cell.car);

        let symbol_slot_cell = &env.memory.borrow()[ptr(first_statement.cdr)];
        assert!(is_symbol_ptr(symbol_slot_cell.car));
        assert_eq!(0, symbol_slot_cell.cdr);

        let symbol_cell = &env.memory.borrow()[ptr(symbol_slot_cell.car)];
        assert_eq!("a", Cell::decode_symbol_name(symbol_cell.car));
        assert_eq!(0, symbol_cell.cdr);
    }

    #[test]
    fn parse_quoted_symbol_with_quote_function() {
        let mut env = LispEnv::new();
        let result = env.parse("(quote a)");
        assert!(result.is_ok());

        env.print_memory();
        let first_statement_ptr = env.memory.borrow()[result.unwrap()].car;
        let first_statement = &env.memory.borrow()[ptr(first_statement_ptr)];
        assert!(first_statement.is_list());
        assert!(is_symbol_ptr(first_statement.car));
        assert_eq!(
            Cell::encode_symbol_name("quote").0,
            env.memory.borrow()[ptr(first_statement.car)].car
        );
        assert_ne!(0, first_statement.cdr);

        let symbol_slot_cell = &env.memory.borrow()[ptr(first_statement.cdr)];
        assert!(is_symbol_ptr(symbol_slot_cell.car));
        assert_eq!(0, symbol_slot_cell.cdr);

        let symbol_cell = &env.memory.borrow()[ptr(symbol_slot_cell.car)];
        assert_eq!("a", Cell::decode_symbol_name(symbol_cell.car));
        assert_eq!(0, symbol_cell.cdr);
    }

    #[test]
    fn reuse_symbols_within_global_scope() {
        let mut env = LispEnv::new();
        let result = env.parse("(a a a)");
        assert!(result.is_ok());

        env.print_memory();
        let first_statement_ptr = env.memory.borrow()[result.unwrap()].car;
        let first_statement = &env.memory.borrow()[ptr(first_statement_ptr)];
        assert!(first_statement.is_list());
        assert!(is_symbol_ptr(first_statement.car));
        assert_eq!(
            Cell::encode_symbol_name("a").0,
            env.memory.borrow()[ptr(first_statement.car)].car
        );

        let second_entry = &env.memory.borrow()[ptr(first_statement.cdr)];
        assert!(is_symbol_ptr(second_entry.car));
        assert_eq!(
            Cell::encode_symbol_name("a").0,
            env.memory.borrow()[ptr(second_entry.car)].car
        );

        let third_entry = &env.memory.borrow()[ptr(second_entry.cdr)];
        assert!(is_symbol_ptr(third_entry.car));
        assert_eq!(
            Cell::encode_symbol_name("a").0,
            env.memory.borrow()[ptr(third_entry.car)].car
        );

        assert_eq!(first_statement.car, second_entry.car);
        assert_eq!(first_statement.car, third_entry.car);
    }

    //     #[test]
    //     fn parse_quoted_symbol_in_list() {
    //         let mut env = LispEnv::new();
    //         let result = env.parse("('a)");
    //         assert!(result.is_ok());
    //
    //         let result = result.unwrap();
    //         assert!(!is_symbol_ptr(result));
    //         assert!(is_pointer(result));
    //
    //         let first_slot = &env.memory.borrow()[ptr(result)];
    //         assert!(is_symbol_ptr(first_slot.car));
    //         assert_eq!(0, first_slot.cdr);
    //
    //         let first_cell = &env.memory.borrow()[ptr(first_slot.car)];
    //         assert_eq!("a", Cell::decode_symbol_name(first_cell.car));
    //     }
    //
    //     #[test]
    //     fn parse_quoted_list() {
    //         let mut env = LispEnv::new();
    //         let result = env.parse("'(a b c)");
    //         assert!(result.is_ok());
    //
    //         let result = result.unwrap();
    //         assert!(!is_symbol_ptr(result));
    //         assert!(is_pointer(result));
    //
    //         // FIXME Result should point directly at the first cell, and not create an indirection
    //
    //         let first_slot = &env.memory.borrow()[ptr(result)];
    //         assert!(is_symbol_ptr(first_slot.car));
    //         assert_ne!(0, first_slot.cdr);
    //
    //         let second_slot = &env.memory.borrow()[ptr(first_slot.cdr)];
    //         assert!(is_symbol_ptr(second_slot.car));
    //         assert_ne!(0, second_slot.cdr);
    //
    //         let third_slot = &env.memory.borrow()[ptr(second_slot.cdr)];
    //         assert!(is_symbol_ptr(third_slot.car));
    //         assert_eq!(0, third_slot.cdr);
    //     }
    //
    //     #[test]
    //     fn parse_nested_quoted_symbol() {
    //         let mut env = LispEnv::new();
    //         let result = env.parse("(quote (quote (quote a)))");
    //         assert!(result.is_ok());
    //
    //         // expecting `('('(a)))`
    //         // or rather expecting `(quote (quote a))`??
    //
    //         let result = result.unwrap();
    //         assert!(is_pointer(result));
    //
    //         env.print_memory();
    //
    //         let root_cell = &env.memory.borrow()[ptr(result)];
    //         println!("Root cell: {:?}", root_cell);
    //         assert!(is_symbol_ptr(root_cell.car));
    //         assert_ne!(0, root_cell.cdr);
    //
    //         let first_cell = &env.memory.borrow()[ptr(root_cell.car)];
    //         assert_eq!("quote", Cell::decode_symbol_name(first_cell.car));
    //
    //         let second_slot = &env.memory.borrow()[ptr(root_cell.cdr)];
    //         assert!(!is_symbol_ptr(second_slot.car));
    //         assert_eq!(0, second_slot.cdr);
    //
    //         let second_list = &env.memory.borrow()[ptr(second_slot.car)];
    //         assert!(is_symbol_ptr(second_list.car));
    //         assert_ne!(0, second_list.cdr);
    //
    //         let second_cell = &env.memory.borrow()[ptr(second_list.car)];
    //         // actually as part of the second list
    //         assert_eq!("quote", Cell::decode_symbol_name(second_cell.car));
    //         assert_eq!(0, second_cell.cdr);
    //
    //         let third_slot = &env.memory.borrow()[ptr(second_list.cdr)];
    //         assert!(!is_symbol_ptr(third_slot.car));
    //         assert_eq!(0, third_slot.cdr);
    //
    //         let third_list = &env.memory.borrow()[ptr(third_slot.car)];
    //         assert!(is_symbol_ptr(third_list.car));
    //         assert_eq!(0, third_list.cdr);
    //
    //         let third_cell = &env.memory.borrow()[ptr(third_list.car)];
    //         // actually as part of the third list
    //         assert_eq!("a", Cell::decode_symbol_name(third_cell.car));
    //         assert_eq!(0, third_cell.cdr);
    //     }

    #[test]
    fn get_list_length() {
        let mut env = LispEnv::new();
        let list_head = env.parse("(1 2)").unwrap();
        let first_statement = &env.memory.borrow()[list_head];
        assert_eq!(2, env.get_list_length(first_statement.car));
    }

    #[test]
    fn parse_small_program() {
        let mut env = LispEnv::new();
        let result = env.parse("(def r 10)\n(* pi (* r r))");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(2, env.get_list_length((result as u64) << 4));

        let statements = &env.memory.borrow()[result];
        assert_eq!(3, env.get_list_length(statements.car));

        let second_statement = &env.memory.borrow()[ptr(statements.cdr)];
        assert_eq!(3, env.get_list_length(second_statement.car));
    }

    //
    //     #[test]
    //     fn list_single_namespace() {
    //         let mut env = LispEnv::new();
    //         let result = env.parse("(symbols)");
    //         assert!(result.is_ok());
    //
    //         let result = result.unwrap();
    //         assert!(is_pointer(result));
    //
    //         let root_cell = &env.memory.borrow()[ptr(result)];
    //         assert_eq!(Cell::encode_symbol_name("_lisprs").0, root_cell.car);
    //         assert_eq!(0, root_cell.cdr);
    //     }
    //
    //     #[test]
    //     fn encode_short_number_in_returned_pointer() {
    //         let env = LispEnv::new();
    //         let short_number = env.encode_number("1");
    //         assert_eq!(0b10010, short_number);
    //     }
    //
    //     #[test]
    //     fn set_cell_pointer() {
    //         let mut cell = Cell::empty();
    //         cell.set_cdr_pointer(12345);
    //         assert_eq!(cell.cdr, (12345 as u64) << 4);
    //     }
    //
    //     #[test]
    //     fn encode_symbol_name() {
    //         let encoded = Cell::encode_symbol_name("NIL").0;
    //         let expected = 0b0010_u64 | (b'L' as u64) << 24 | (b'I' as u64) << 16 | (b'N' as u64) << 8;
    //         assert_eq!(expected, encoded);
    //     }
    //
    //     #[test]
    //     fn encode_long_symbol_name() {
    //         let (encoded, rest) = Cell::encode_symbol_name("abcdefghijklmnop");
    //         let expected = 0_u64
    //             | (b'a' as u64)
    //             | (b'b' as u64) << 8
    //             | (b'c' as u64) << 16
    //             | (b'd' as u64) << 24
    //             | (b'e' as u64) << 32
    //             | (b'f' as u64) << 40
    //             | (b'g' as u64) << 48
    //             | (b'h' as u64) << 56;
    //         assert_eq!(expected, encoded);
    //         assert_eq!("ijklmnop".as_bytes(), rest);
    //     }
    //
    //     #[test]
    //     fn encode_short_symbol_name() {
    //         let (val, _) = Cell::encode_symbol_name("a");
    //         assert_eq!(24834_u64, val);
    //     }
    //
    //     #[test]
    //     fn decode_short_symbol_name() {
    //         assert_eq!("a", Cell::decode_symbol_name(24834_u64));
    //     }
    //
    //     #[test]
    //     fn decode_symbol_name() {
    //         assert_eq!("nil", Cell::decode_symbol_name(1818848770_u64));
    //     }
    //
    //     #[test]
    //     fn global_scope_is_allocated() {
    //         let env = LispEnv::new();
    //         assert_ne!(0, env.internal_symbols_key);
    //
    //         let scope_root = &env.memory.borrow()[ptr(env.internal_symbols_key)];
    //         assert_eq!(0, scope_root.cdr);
    //         assert!(is_pointer(scope_root.car));
    //
    //         let scope_name = &env.memory.borrow()[ptr(scope_root.car)];
    //         assert_ne!(0, scope_name.car);
    //         assert_eq!(Cell::encode_symbol_name("_lisprs").0, scope_name.cdr);
    //         assert!(env.property_count(env.internal_symbols_key) > 0);
    //     }
    //
    //     #[test]
    //     fn append_property_to_symbol() {
    //         let env = LispEnv::new();
    //         let symbol_ptr = env.allocate_symbol(Some("symb"), 0);
    //
    //         let original_mem_size = env.memory.borrow().len();
    //         let name_ptr = Cell::encode_symbol_name("foo").0;
    //         let prop_slot = env.append_property(symbol_ptr, name_ptr, number_pointer(10, false));
    //         assert_eq!(original_mem_size + 3, env.memory.borrow().len());
    //         // 2 cells for the prop and its value, and another cell for the "_lisprs" name that's moved
    //         // in a separate cell
    //         assert_ne!(0, prop_slot);
    //
    //         // expected symbol structure:
    //         //  symb:
    //         //    foo: 10
    //         // cell-wise:
    //         // [symb_name_ptr | nil]
    //         //    -> [foo_cell_slot (1st item in list) | "symb"]
    //         //          -> [foo_cell_ptr | nil]
    //         //                -> [10 | "foo"]
    //
    //         let root_cell = &env.memory.borrow()[symbol_ptr as usize >> 4];
    //         assert_eq!(0, root_cell.cdr);
    //         assert_eq!((symbol_ptr >> 4) + 3, root_cell.car >> 4);
    //
    //         let symbol_name_cell = &env.memory.borrow()[(symbol_ptr as usize >> 4) + 3];
    //         assert_eq!(Cell::encode_symbol_name("symb").0, symbol_name_cell.cdr);
    //
    //         let prop_slot_cell = &env.memory.borrow()[ptr(symbol_name_cell.car)];
    //         assert_eq!(0, prop_slot_cell.cdr);
    //
    //         let prop_ptr = env.memory.borrow()[ptr(prop_slot)].car;
    //         let prop_cell = &env.memory.borrow()[ptr(prop_ptr)];
    //         assert_eq!(10, as_number(prop_cell.car));
    //         assert_eq!(Cell::encode_symbol_name("foo").0, prop_cell.cdr);
    //
    //         assert_eq!(1, env.property_count(symbol_ptr));
    //     }
    //
    //     #[test]
    //     fn append_another_property_to_symbol() {
    //         let env = LispEnv::new();
    //         let symbol_ptr = env.allocate_symbol(Some("symb"), 0);
    //
    //         let first_name_ptr = Cell::encode_symbol_name("foo").0;
    //         let first_prop_slot =
    //             env.append_property(symbol_ptr, first_name_ptr, number_pointer(10, false));
    //
    //         let second_name_ptr = Cell::encode_symbol_name("bar").0;
    //         let second_prop_slot =
    //             env.append_property(symbol_ptr, second_name_ptr, number_pointer(42, false));
    //         assert_ne!(first_prop_slot, second_prop_slot);
    //
    //         // expected symbol structure:
    //         //  symb:
    //         //    foo: 10
    //         //    bar: 42
    //         // cell-wise:
    //         // [symb_name_ptr | nil]
    //         //    -> [1st property slot | "symb"]
    //         //          -> [foo_cell_ptr | bar_cell_slot] -> [bar_cell_ptr | nil]
    //         //                   -> [10 | "foo"]                -> [42 | "bar"]
    //
    //         let first_prop_ptr = env.memory.borrow()[ptr(first_prop_slot)].car;
    //         let foo_cell = &env.memory.borrow()[ptr(first_prop_ptr)];
    //         assert_eq!(first_name_ptr, foo_cell.cdr);
    //         assert_eq!(10, as_number(foo_cell.car));
    //
    //         let second_prop_ptr = env.memory.borrow()[ptr(second_prop_slot)].car;
    //         let bar_cell = &env.memory.borrow()[ptr(second_prop_ptr)];
    //         assert_eq!(second_name_ptr, bar_cell.cdr);
    //         assert_eq!(42, as_number(bar_cell.car));
    //
    //         let property_root_ptr = env.memory.borrow()[ptr(symbol_ptr)].car;
    //         let property_root_cell = &env.memory.borrow()[ptr(property_root_ptr)];
    //         assert_eq!(Cell::encode_symbol_name("symb").0, property_root_cell.cdr);
    //
    //         let foo_slot_cell = &env.memory.borrow()[ptr(property_root_cell.car)];
    //         assert_eq!(first_prop_ptr, foo_slot_cell.car);
    //
    //         let bar_slot_cell = &env.memory.borrow()[ptr(foo_slot_cell.cdr)];
    //         assert_eq!(second_prop_ptr, bar_slot_cell.car);
    //         assert_eq!(0, bar_slot_cell.cdr);
    //     }
    //
    //     #[test]
    //     fn assign_symbol_value_to_symbol() {
    //         // expected symbol structure:
    //         //  symb:
    //         //    foo: bar
    //         // cell-wise:
    //         // [symb_name_ptr | nil]
    //         //    -> [property slot | "symb"]
    //         //          -> [foo_cell_ptr | nil]
    //         //                 ->  [foo_name_ptr | bar_cell_ptr] -> ["bar" | nil]
    //         //                           -> [nil | "foo"]
    //         unimplemented!()
    //     }
    //
    //     #[test]
    //     fn append_symbol_property_to_symbol() {
    //         let env = LispEnv::new();
    //         let root_symbol_ptr = env.allocate_symbol(Some("symb"), 0);
    //         let property_symbol_ptr = env.allocate_symbol(Some("bar"), 0);
    //         let property_val_ptr = env.append_property(
    //             root_symbol_ptr,
    //             Cell::encode_symbol_name("bar").0,
    //             property_symbol_ptr,
    //         );
    //
    //         // expected symbol structure:
    //         //  symb:
    //         //    foo:
    //         //      bar:
    //         // cell-wise:
    //         // [symb_name_ptr | nil]
    //         //    -> [foo_cell_slot (1st item in list) | "symb"]
    //         //          -> [nil | foo_cell_ptr] -> [foo_name_ptr | nil]
    //         //                                           -> [bar_cell_ptr | "foo"]
    //         //                                                   -> [nil | bar_cell_ptr] -> ["bar" | nil]
    //
    //         assert_ne!(0, property_val_ptr);
    //     }
    //
    //     #[test]
    //     fn assign_property_to_nested_symbol() {
    //         let env = LispEnv::new();
    //         let symbol_ptr = env.allocate_symbol(Some("symb"), 0);
    //         let first_name_ptr = Cell::encode_symbol_name("foo").0;
    //         let first_prop_ptr = env.append_property(symbol_ptr, first_name_ptr, 0);
    //         println!("Foo prop ptr is {}", ptr(first_prop_ptr));
    //         env.print_memory();
    //         // FIXME The issue is that the property 'foo' is not a symbol. What should be returned should
    //         //       be the property slot, which happens to be structured like a symbol
    //         // expected symbol structure:
    //         // symb:
    //         //   foo:
    //         // cell-wise:
    //         // [symb_name_ptr | nil]
    //         //    -> [foo_cell_slot (1st item in list) | "symb"]
    //         //          -> [foo_cell_ptr | nil]
    //         //                    -> [nil | "foo"]
    //         let nested_prop_slot = env.append_property(
    //             first_prop_ptr,
    //             Cell::encode_symbol_name("bar").0,
    //             number_pointer(42, false),
    //         );
    //         println!("Bar prop slot is {}", ptr(nested_prop_slot));
    //         env.print_memory();
    //         // expected symbol structure:
    //         // symb:
    //         //   foo:
    //         //    bar: 42
    //         // cell-wise:
    //         // [symb_name_ptr | nil]
    //         //    -> [foo_cell_slot (1st item in list) | "symb"]
    //         //          -> [foo_cell_ptr | nil]
    //         //                    -> [bar_cell_slot | "foo"]
    //         //                              -> [bar_cell_ptr | nil]
    //         //                                      -> [42 | bae]
    //
    //         assert_ne!(0, nested_prop_slot);
    //         let nested_prop_ptr = env.memory.borrow()[ptr(nested_prop_slot)].car;
    //         let bar_cell = &env.memory.borrow()[ptr(nested_prop_ptr)];
    //         assert_eq!(42, as_number(bar_cell.car));
    //         assert_eq!(Cell::encode_symbol_name("bar").0, bar_cell.cdr);
    //     }
    //
    //     #[test]
    //     fn resolve_simple_symbol_name() {
    //         let env = LispEnv::new();
    //         let symbol_ptr = env.allocate_symbol(Some("symb"), 0);
    //         assert_eq!(Some("symb".to_string()), env.symbol_name(symbol_ptr));
    //     }
    //
    //     #[test]
    //     fn resolve_complex_symbol_name() {
    //         let env = LispEnv::new();
    //         let symbol_ptr = env.allocate_symbol(Some("symb"), 0);
    //         let first_name_ptr = Cell::encode_symbol_name("foo").0;
    //         env.append_property(symbol_ptr, first_name_ptr, number_pointer(10, false));
    //         assert_eq!(Some("symb".to_string()), env.symbol_name(symbol_ptr));
    //     }
    //
    //     #[test]
    //     fn property_is_in_global_scope() {
    //         let env = LispEnv::new();
    //         let original_mem_size = env.memory.borrow().len();
    //         let name_ptr = Cell::encode_symbol_name("foo").0;
    //         let prop_ptr = env.append_property(
    //             env.internal_symbols_key,
    //             name_ptr,
    //             number_pointer(10, false),
    //         );
    //         assert!(env.global_scope_contains_property("foo"));
    //     }
    //
    //     #[test]
    //     fn get_property_value() {
    //         let env = LispEnv::new();
    //         let symb_ptr = env.allocate_symbol(Some("foo"), 0);
    //         let name_ptr = Cell::encode_symbol_name("bar").0;
    //         let prop_ptr = env.append_property(symb_ptr, name_ptr, number_pointer(10, false));
    //         assert_eq!(
    //             Some(number_pointer(10, false)),
    //             env.get_property(symb_ptr, "bar")
    //         );
    //     }
    //
    //     mod structural_equality {
    //         use super::super::*;
    //
    //         #[test]
    //         fn unequal_short_numbers() {
    //             let mut env = LispEnv::new();
    //             let result = env.parse("(= 1 0)");
    //             assert!(result.is_ok());
    //             assert_eq!(0, result.unwrap());
    //         }
    //
    //         #[test]
    //         fn equal_short_numbers() {
    //             let mut env = LispEnv::new();
    //             let result = env.parse("(= 3 3)");
    //             assert!(result.is_ok());
    //             assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
    //         }
    //
    //         #[test]
    //         fn unequal_short_strings() {
    //             let mut env = LispEnv::new();
    //             let result = env.parse("(= \"a\" \"b\")");
    //             assert!(result.is_ok());
    //             assert_eq!(0, result.unwrap());
    //         }
    //
    //         #[test]
    //         fn equal_short_strings() {
    //             let mut env = LispEnv::new();
    //             let result = env.parse("(= \"c\" \"c\")");
    //             assert!(result.is_ok());
    //             assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
    //         }
    //
    //         #[test]
    //         fn unequal_single_element_lists() {
    //             let mut env = LispEnv::new();
    //             let result = env.parse("(= (3) (5))");
    //             assert!(result.is_ok());
    //             assert_eq!(0, result.unwrap());
    //         }
    //
    //         #[test]
    //         fn equal_single_element_lists() {
    //             let mut env = LispEnv::new();
    //             let result = env.parse("(= (7) (7))");
    //             assert!(result.is_ok());
    //             assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
    //         }
    //
    //         #[test]
    //         fn unequal_simple_symbols() {
    //             let mut env = LispEnv::new();
    //             let result = env.parse("(= a b)");
    //             assert!(result.is_ok());
    //             assert_eq!(0, result.unwrap());
    //         }
    //
    //         #[test]
    //         fn equal_simple_symbols() {
    //             let mut env = LispEnv::new();
    //             let result = env.parse("(= c c)");
    //             assert!(result.is_ok());
    //             assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
    //         }
    //
    //         #[test]
    //         fn equal_evaluated_lists() {
    //             let mut env = LispEnv::new();
    //             let result = env.parse("(= (1 (* 4 5) (+ 1 3)) (1 20 4))");
    //             assert!(result.is_ok());
    //             assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
    //         }
    //
    //         #[test]
    //         fn unequal_symbols_with_different_properties() {
    //             todo!()
    //         }
    //
    //         #[test]
    //         fn equal_symbols_with_identical_properties() {
    //             todo!()
    //         }
    //     }
}

use crate::lisprs::cell::Cell;
use crate::lisprs::util::as_ptr;
use crate::lisprs::LispEnv;
use log::*;
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
                trace!("Allocating symbol {}", symbol_name);
                // if self.get_property(self.internal_symbols_key)
                self.allocate_symbol(Some(symbol_name), self.nil_key).ptr()
            }
            Rule::sexpr => self.parse_list(atom.into_inner())?,
            Rule::dotted_list => {
                let mut inner = atom.into_inner();
                let first_term = self.parse_atom(inner.next().unwrap())?;
                let second_term = self.parse_atom(inner.next().unwrap())?;
                as_ptr(self.insert_cell(Cell {
                    car: first_term,
                    cdr: second_term,
                }))
            }
            Rule::quoted_atom => {
                // We normalize it as a list
                let list_content = self.parse_atom(atom.into_inner().next().unwrap())?;
                let quote_list_ptr = self.allocate_empty_cell();
                let quote_content_ptr = self.allocate_empty_cell();
                {
                    let quote_ptr = self.allocate_symbol(Some("quote"), 0).ptr();
                    let quote_list_cell = &mut self.memory.borrow_mut()[quote_list_ptr];
                    quote_list_cell.car = quote_ptr;
                    quote_list_cell.set_cdr_pointer(quote_content_ptr)
                }
                {
                    let quote_content_cell = &mut self.memory.borrow_mut()[quote_content_ptr];
                    quote_content_cell.car = list_content;
                }

                as_ptr(quote_list_ptr)
            }
            Rule::string => Cell::encode_symbol_name(atom.as_str()).0,
            _ => unimplemented!("Rule: {}", atom.as_str()),
        })
    }

    /// Returns the pointer to the list
    fn parse_list(&mut self, atoms: Pairs<Rule>) -> Result<u64, pest::error::Error<Rule>> {
        // trace!("--- LIST atoms {:?}", atoms);
        let mut result = 0_u64; // pointer to nil
        let mut list_tail_ptr = 0_usize;

        for atom in atoms {
            let atom_value = self.parse_atom(atom)?;
            let new_cell_idx = self.insert_cell(Cell {
                car: atom_value,
                cdr: 0,
            });
            // trace!("Appending cell at idx {}", new_cell_idx);
            if result == 0 {
                result = as_ptr(new_cell_idx); // then result acts as the list head
            }

            if list_tail_ptr != 0 {
                let mut last_cell = &mut self.memory.borrow_mut()[list_tail_ptr];
                last_cell.cdr = as_ptr(new_cell_idx);
            }

            list_tail_ptr = new_cell_idx;
        }

        Ok(result)
    }

    // Returns memory index of the head of the parsed statements list
    pub fn parse(&mut self, input: &str) -> Result<usize, pest::error::Error<Rule>> {
        let root = LispGrammar::parse(Rule::lisp, input)?
            .next()
            .unwrap()
            .into_inner();

        trace!("Root: {:?}", root);
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
                self.memory.borrow_mut()[current_statement_ptr].cdr = as_ptr(parsed_statements_ptr);
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
    use crate::lisprs::util::{as_number, as_ptr, is_number, is_pointer, is_symbol_ptr, ptr};

    #[test]
    fn parse_empty_list_and_return_nil() {
        let mut env = LispEnv::new();
        let result = env.parse("()");
        assert!(result.is_ok());

        let statements = result.unwrap();
        assert_eq!(1, env.get_list_length(as_ptr(statements)));
        assert_eq!(0_u64, env.memory.borrow()[statements].car);
    }

    #[test]
    fn parse_symbol_in_list() {
        let mut env = LispEnv::new();
        let result = env.parse("(a)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(1, env.get_list_length(as_ptr(result)));

        let statement = &env.memory.borrow()[result];
        assert!(is_pointer(statement.car));

        let cell = &env.memory.borrow()[ptr(statement.car)];
        assert!(cell.is_list());
        assert!(is_symbol_ptr(cell.car));

        let first_element = &env.memory.borrow()[cell.car_ptr()];
        assert!(is_number(first_element.car));
        assert_eq!("a", Cell::decode_symbol_name(first_element.car));
    }

    #[test]
    fn parse_list_of_single_short_number() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let result = env.parse("(1)");
        assert!(result.is_ok());
        let result = result.unwrap();

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
    fn parse_dotted_list() {
        let mut env = LispEnv::new();
        let result = env.parse("(1 . 2)");
        assert!(result.is_ok());

        let first_statement = &env.memory.borrow()[result.unwrap()];

        let list_head = &env.memory.borrow()[ptr(first_statement.car)];
        assert_eq!(1, as_number(list_head.car));
        assert_eq!(2, as_number(list_head.cdr));
    }

    #[test]
    fn parse_nested_dotted_list() {
        let mut env = LispEnv::new();
        let result = env.parse("(1 . (2 . (3 . NIL)))");
        assert!(result.is_ok());

        let first_statement = &env.memory.borrow()[result.unwrap()];

        let list_head = &env.memory.borrow()[ptr(first_statement.car)];
        assert_eq!(1, as_number(list_head.car));
        assert!(is_pointer(list_head.cdr));

        let second_cell = &env.memory.borrow()[ptr(list_head.cdr)];
        assert_eq!(2, as_number(second_cell.car));
        assert!(is_pointer(second_cell.cdr));

        let third_cell = &env.memory.borrow()[ptr(second_cell.cdr)];
        assert_eq!(3, as_number(third_cell.car));
        assert!(is_symbol_ptr(third_cell.cdr));

        let final_symbol_cell = &env.memory.borrow()[ptr(third_cell.cdr)];
        assert_eq!(Cell::encode_symbol_name("NIL").0, final_symbol_cell.car);
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
    fn do_not_symbols_within_global_scope_while_parsing() {
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

        assert_ne!(first_statement.car, second_entry.car);
        assert_ne!(first_statement.car, third_entry.car);

        // We should actually only rationalize this when evaluating the list, otherwise we'll end up
        // having to resolve frame allocations during the parsing phase...
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
    //         trace!("Root cell: {:?}", root_cell);
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
    fn parse_small_program() {
        let mut env = LispEnv::new();
        let result = env.parse("(def r 10)\n(* pi (* r r))");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(2, env.get_list_length(as_ptr(result)));

        let statements = &env.memory.borrow()[result];
        assert_eq!(3, env.get_list_length(statements.car));

        let second_statement = &env.memory.borrow()[ptr(statements.cdr)];
        assert_eq!(3, env.get_list_length(second_statement.car));
    }
}

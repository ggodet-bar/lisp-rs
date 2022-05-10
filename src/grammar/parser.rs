use pest::iterators::Pairs;
use pest::Parser as PestParser;
use pest_derive::Parser;
use slab::Slab;
use std::cell::RefCell;
use std::cmp::min;
use std::collections::{HashMap, VecDeque};
use std::fmt::{Debug, Formatter, Write};
use std::str::FromStr;

#[derive(Clone, PartialEq)]
pub struct Cell {
    car: u64,
    cdr: u64,
}

impl Debug for Cell {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_list() {
            let val = if self.is_number() {
                format!("Num[{}]", self.as_number())
            } else if is_symbol_ptr(self.car) {
                format!("SymbolPtr:[{}]", self.car_ptr())
            } else {
                format!("ListPtr:[{}]", self.car_ptr())
            };
            f.write_fmt(format_args!("Cell[List {}, next: {}]", val, self.cdr_ptr()))
        } else {
            f.write_fmt(format_args!(
                "Cell{{ car: {}, cdr: {}}}",
                self.car, self.cdr
            ))
        }
    }
}

impl Cell {
    pub fn empty() -> Self {
        Self { car: 0, cdr: 0 }
    }

    pub fn is_nil(&self) -> bool {
        self.car == Cell::encode_symbol_name("nil").0 && self.cdr == 0 // by convention nil is the first entry, so its addr is 0
    }

    pub fn is_list(&self) -> bool {
        self.cdr & 0b1110 == 0 // CDR is a pointer
    }

    pub fn is_number(&self) -> bool {
        // FIXME Won't take big numbers into account, would need the env
        self.car & 0b10 > 0
    }

    pub fn as_number(&self) -> i64 {
        // FIXME Naive implementation, won't take big numbers into account
        (self.car >> 4) as i64 * if self.car & 0b1000 > 0 { -1 } else { 1 }
    }

    pub fn set_pointer(&mut self, raw_addr: usize) {
        self.cdr = (raw_addr as u64) << 4;
    }

    pub fn car_ptr(&self) -> usize {
        ptr(self.car)
    }

    pub fn cdr_ptr(&self) -> usize {
        ptr(self.cdr)
    }

    // // NOTE returns only the first 8 characters, for now
    // pub fn symbol_name(&self) -> &str {
    //
    // }

    pub fn decode_symbol_name(val: u64) -> String {
        let mut buffer: [u8; 8] = [0; 8];
        let mut buffer_len = 8;
        for shift in 0..8 {
            let char_byte = (val >> (8 * shift) & 0xff) as u8;
            buffer[shift] = char_byte as u8;

            if char_byte == 0 {
                buffer_len = shift;
                break;
            }
        }

        String::from_utf8(buffer[0..buffer_len].to_vec()).unwrap_or(String::from("***ERR***"))
    }

    pub fn encode_symbol_name(name: &str) -> (u64, &[u8]) {
        let mut result = 0_u64;
        let byte_representation = name.as_bytes();
        for (idx, b) in byte_representation[0..min(8, byte_representation.len())]
            .iter()
            .enumerate()
        {
            result |= (*b as u64) << idx;
        }

        (
            result,
            if byte_representation.len() > 8 {
                &byte_representation[8..]
            } else {
                &[]
            },
        )
    }
}

pub fn is_symbol_ptr(val: u64) -> bool {
    val & 0b1110 == 0b1000
}

pub fn is_pointer(val: u64) -> bool {
    val & 0b0110 == 0
}

pub fn ptr(val: u64) -> usize {
    if !is_pointer(val) {
        panic!("Not a pointer!");
    }

    (val >> 4) as usize
}

fn number_pointer(payload: u64, sign: bool) -> u64 {
    let sign_bit = if sign { 0b1000 } else { 0b0000 };
    payload << 4 | sign_bit | 0b010
}

#[derive(Parser)]
#[grammar = "./grammar/lisp.pest"]
pub struct LispGrammar;

enum Record {
    /// Returns the index in memory where the result is stored
    Function(Box<dyn Fn(usize, &LispEnv) -> usize>),
    Variable(Cell),
}

type Memory = RefCell<Slab<Cell>>;

pub struct LispEnv {
    memory: Memory,
    nil_key: u64,
    /// Initially an anonymous symbol with a nil value, should receive all the internal symbols of
    /// created during the environment lifetime.
    internal_symbols_key: u64,
    /// Function pointer returns whether the cell should be added to the heap or is a copy
    functions: HashMap<String, Record>,
    call_stack: VecDeque<String>,
}

impl LispEnv {
    fn allocate_nil(&self) -> usize {
        let nil_key = {
            let mut memory = self.memory.borrow_mut();
            let nil_entry = memory.vacant_entry();
            let nil_key = nil_entry.key();
            let nil = Cell {
                car: Cell::encode_symbol_name("nil").0,
                cdr: nil_key as u64,
            };
            nil_entry.insert(nil);
            nil_key
        };
        self.memory.borrow_mut().insert(Cell {
            car: nil_key as u64,
            cdr: nil_key as u64,
        });

        nil_key
    }

    /// Returns a symbol pointer
    fn allocate_symbol(&self, name: Option<&str>, value_ptr: usize) -> u64 {
        let cell_key = self.allocate_empty_cell();
        let cell = &mut self.memory.borrow_mut()[cell_key];
        if let Some(name) = name {
            let (name_fragment, rest) = Cell::encode_symbol_name(name);
            if rest.is_empty() {
                cell.car = name_fragment;
            } else {
                unimplemented!("name is big number");
            }
        };
        // let cell = &mut self.memory.borrow_mut()[cell_key];
        // cell.cdr = (value_ptr as u64) << 4 | 0b1000;
        // cell.car = cell_tail_key.unwrap_or(0) as u64;
        // call.cdr = value_ptr;

        (cell_key as u64) << 4 | 0b1000
    }

    fn allocate_empty_cell(&self) -> usize {
        self.memory.borrow_mut().insert(Cell::empty())
    }

    fn encode_number(&self, s: &str) -> u64 {
        let truncated = if s.contains(".") {
            // unimplemented!("decimal numbers");
            // FIXME For now we'll truncate
            s.split_once('.').unwrap().0
        } else {
            s
        };
        let (sign, rest) = if truncated.starts_with("-") {
            (true, &truncated[1..])
        } else {
            (false, truncated)
        };

        let payload = u64::from_str(rest).unwrap();

        number_pointer(payload, sign)
    }

    fn insert_cell(&self, cell: Cell) -> usize {
        self.memory.borrow_mut().insert(cell)
    }

    fn print_memory(&self) {
        for (idx, cell) in &*self.memory.borrow() {
            println!("{}: {:?}", idx, cell);
        }
    }

    pub fn new() -> Self {
        let mut env = Self {
            memory: RefCell::new(Slab::<Cell>::with_capacity(1024)),
            nil_key: 0,
            internal_symbols_key: 0,
            functions: HashMap::new(),
            call_stack: VecDeque::new(),
        };
        env.nil_key = env.allocate_nil() as u64;
        env.internal_symbols_key = env.allocate_symbol(None, env.nil_key as usize) as u64;
        env.functions.insert(
            "+".to_string(),
            Record::Function(Box::new(|args_idx, env| {
                let sum = {
                    let memory = env.memory.borrow();

                    println!("Arg idx: {}", args_idx);
                    let args = &memory[args_idx];
                    let mut sum = args.as_number();
                    let mut current_cell = args;

                    while current_cell.cdr != 0 {
                        println!("+ current cell: {:?}", current_cell);
                        let next_cell = &memory[current_cell.cdr_ptr()];
                        println!("Next cell: {:?}", next_cell);
                        if !next_cell.is_number() {
                            unimplemented!("handle type error");
                        }

                        sum += next_cell.as_number(); // FIXME Proper conversion with sign bit!
                        println!("current sum: {}", sum);

                        current_cell = &next_cell;
                    }

                    sum
                };
                env.insert_cell(Cell {
                    car: number_pointer(sum.abs() as u64, sum < 0),
                    cdr: 0,
                })
                // env.allocate_symbol(None, env.nil_key as usize) as u64;
                // let memory = &mut env.memory.borrow_mut();
                // memory.a
                // (Cell::from((sum.abs() as u64, sum < 0)), true)
            })),
        );
        env.functions.insert(
            "*".to_string(),
            Record::Function(Box::new(|args_idx, env| {
                let result = {
                    let memory = env.memory.borrow();

                    let args = &memory[args_idx];
                    let mut result = args.as_number();
                    let mut current_cell = args;
                    while current_cell.cdr != 0 {
                        println!("* current cell: {:?}", current_cell);
                        let next_cell = &memory[current_cell.cdr_ptr()];
                        println!("Next cell: {:?}", next_cell);
                        if !next_cell.is_number() {
                            unimplemented!("handle type error");
                        }

                        result *= next_cell.as_number(); // FIXME Proper conversion with sign bit!
                        println!("current result: {}", result);

                        current_cell = &next_cell;
                    }

                    result
                };
                env.insert_cell(Cell {
                    car: number_pointer(result.abs() as u64, result < 0),
                    cdr: 0,
                })
            })),
        );
        env.functions.insert(
            "def".to_string(),
            Record::Function(Box::new(|args_idx, env| {
                let (value_head, symbol_cell_idx) = {
                    let memory = env.memory.borrow();
                    let args = &memory[args_idx];
                    println!("arg cell: {:?}", args);

                    (memory[args.cdr_ptr()].car, args.car_ptr())
                };

                let memory = &mut env.memory.borrow_mut();
                let mut symbol_cell = &mut memory[symbol_cell_idx];
                println!("Symbol cell: {:?}", symbol_cell);
                symbol_cell.cdr = value_head;
                println!(
                    "Updated symbol cell {}: {}",
                    Cell::decode_symbol_name(symbol_cell.car),
                    symbol_cell.cdr
                );
                // TODO Super rough conversion
                // if !symbol_cell.is_symbol_ptr() {
                //     panic!("NOT A SYMBOL");
                // }

                // FIXME We assume for now that the variable name is less than 8 characters
                // let first_letter = char::from((symbol_cell.car & 0xff) as u8);
                // println!("First letter: {}", first_letter);

                // We reuse the symbol without a value to point to the value cell, and we then add
                // the symbol to the index of internal symbols (currently as a list)
                // symbol_cell.cdr = arg_list_cell_car << 4 | 0b1000;

                // todo!("Insert the symbol into the internal index/registry!")

                symbol_cell_idx
            })),
        );
        // env.functions.insert(
        //     "pi".to_string(),
        //     Record::Variable(Cell::number("3.141592653589793")),
        // );
        // FIXME `list` is probably not a primitive, but is used now in order to get a consistent
        // call stack
        // env.functions.insert(
        //     "list".to_string(),
        //     Box::new(|args, env| (args.to_owned(), false)),
        // );
        env
    }

    fn eval_list(&mut self, atoms: Pairs<Rule>) -> Result<usize, pest::error::Error<Rule>> {
        println!("--- LIST atoms {:?}", atoms);

        let mut list_head = None;
        let mut last_cell_ptr = None;

        for atom in atoms {
            let cell_value = match atom.as_rule() {
                Rule::number => self.encode_number(atom.as_str()),
                Rule::symbol => {
                    if self.functions.contains_key(atom.as_str()) {
                        println!("Pushing op {}", atom.as_str());
                        self.call_stack.push_back(atom.as_str().to_string());
                        continue;
                    } else {
                        self.allocate_symbol(Some(atom.as_str()), self.nil_key as usize)
                    }
                }
                Rule::sexpr => (self.eval_list(atom.into_inner())? as u64) << 4,
                _ => unimplemented!(),
            };

            let new_cell_idx = if is_pointer(cell_value) && !is_symbol_ptr(cell_value) {
                cell_value as usize >> 4 // we're reusing the list/symbol?
            } else {
                self.insert_cell(Cell {
                    car: cell_value,
                    cdr: 0,
                })
            };

            if list_head.is_none() {
                list_head = Some(new_cell_idx);
            }
            if let Some(last_cell_ptr) = last_cell_ptr {
                self.memory.borrow_mut()[last_cell_ptr].set_pointer(new_cell_idx);
            }
            last_cell_ptr = Some(new_cell_idx);
        }

        if list_head.is_none() {
            list_head = Some(0); // empty list, pointing to nil
        }

        println!(
            "List head: {:?}, {:?}",
            list_head,
            &self.memory.borrow()[list_head.unwrap()]
        );

        if let Some(fn_name) = self.call_stack.pop_front() {
            println!("About to apply record {}", fn_name);
            self.print_memory();
            list_head = Some(match &self.functions[&fn_name] {
                Record::Function(function) => function(list_head.unwrap(), &self),
                Record::Variable(val) => self.insert_cell(val.to_owned()),
            });
            self.print_memory();
            println!("New list head: {:?}", list_head);

            // if new_cell {
            //     list_head = self.insert_cell(result);
            // }
        }

        Ok(list_head.unwrap())
    }

    pub fn eval(&mut self, input: &str) -> Result<Cell, pest::error::Error<Rule>> {
        let root = LispGrammar::parse(Rule::lisp, input)?
            .next()
            .unwrap()
            .into_inner();
        println!("Root: {:?}", root);
        let mut result = Cell::empty();
        for statement in root {
            if statement.as_rule() == Rule::EOI {
                continue;
            }

            let atoms = statement.into_inner();
            let list_head = self.eval_list(atoms)?;

            result = self.memory.borrow()[list_head].to_owned();
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use crate::grammar::parser::{is_symbol_ptr, ptr, Cell, LispEnv};

    #[test]
    fn parse_empty_list() {
        let mut env = LispEnv::new();
        let result = env.eval("()");
        assert!(result.is_ok());

        let list = result.unwrap();
        assert_eq!(Cell::encode_symbol_name("nil").0, list.car);
        assert_eq!(env.nil_key, list.cdr);
    }

    #[test]
    fn empty_list_is_nil() {
        let mut env = LispEnv::new();
        let result = env.eval("()").unwrap();
        assert!(result.is_nil());
    }

    #[test]
    fn parse_symbol() {
        let mut env = LispEnv::new();
        let result = env.eval("(a)");
        assert!(result.is_ok());

        env.print_memory();

        let result = result.unwrap();
        assert!(result.is_list());
        assert!(is_symbol_ptr(result.car));

        let first_element = &env.memory.borrow()[result.car_ptr()];
        assert!(!first_element.is_number());
        assert_eq!("a", Cell::decode_symbol_name(first_element.car));
    }

    #[test]
    fn encode_short_symbol_name() {
        let (val, _) = Cell::encode_symbol_name("a");
        assert_eq!(97_u64, val);
    }

    #[test]
    fn decode_short_symbol_name() {
        assert_eq!("a", Cell::decode_symbol_name(97_u64));
    }

    // #[test]
    // fn parse_string() {
    //     assert!(LispEnv::eval("(\"a\")").is_ok());
    // }
    //
    #[test]
    fn parse_list_of_single_short_number() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let result = env.eval("(1)");
        assert!(result.is_ok());
        assert_eq!(original_memory_size + 1, env.memory.borrow().len());

        let result = result.unwrap();
        assert!(result.is_list());

        env.print_memory();
        assert_eq!(env.encode_number("1") as u64, result.car);
        assert_eq!(0, result.cdr);
    }

    #[test]
    fn parse_list_of_two_numbers() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let result = env.eval("(1 2)");
        assert!(result.is_ok());
        assert_eq!(original_memory_size + 2, env.memory.borrow().len());

        env.print_memory();
        let list_head = result.unwrap();
        assert!(list_head.is_list());

        assert_eq!(env.encode_number("1") as u64, list_head.car);

        let list_tail = &env.memory.borrow()[list_head.cdr_ptr()];
        assert!(list_tail.is_list());

        assert_eq!(env.encode_number("2") as u64, list_tail.car);
        assert_eq!(list_tail.cdr, 0);
    }

    #[test]
    fn parse_simple_operation() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let result = env.eval("(+ 1 2)");
        assert!(result.is_ok());
        assert_eq!(original_memory_size + 3, env.memory.borrow().len());
        // the 2 values in the operation + the result

        let result = result.unwrap();
        println!("{:?}", result);
        assert!(result.is_number());
        assert_eq!(3, result.as_number());
    }

    #[test]
    fn parse_nested_operation_1() {
        let mut env = LispEnv::new();
        let result = env.eval("(+ (+ 1 2) 3)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(result.is_number());
        assert_eq!(6, result.as_number());
    }

    #[test]
    fn parse_nested_operation_2() {
        let mut env = LispEnv::new();
        let result = env.eval("(+ (+ 1 2) (+ 3 (+ 4 5 6)))");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(result.is_number());
        assert_eq!(21, result.as_number());
    }

    #[test]
    fn parse_multiplication() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let result = env.eval("(* 2 3 6)");
        assert!(result.is_ok());
        assert_eq!(original_memory_size + 4, env.memory.borrow().len());
        // the 3 values in the operation + the result

        let result = result.unwrap();
        assert!(result.is_number());
        assert_eq!(36, result.as_number());
    }

    #[test]
    fn parse_very_small_program() {
        let mut env = LispEnv::new();
        let result = env.eval("(def r 10)\n(r)");
        assert!(result.is_ok());

        env.print_memory();
        let result = result.unwrap();
        assert!(result.is_number());
        assert_eq!(10, result.as_number());
    }

    #[test]
    fn parse_small_program() {
        let mut env = LispEnv::new();
        let result = env.eval("(def r 10)\n(* pi (* r r))");
        assert!(result.is_ok());

        let result = result.unwrap();
    }

    #[test]
    fn parse_fibonacci_function() {
        let mut env = LispEnv::new();
        let result = env.eval(
            r#"
(def fib (N)
	(if (<= N 1) N (+ (fib (- N 1)) (fib (- N 2)))))"#,
        );
        println!("Res: {:?}", result);
        assert!(result.is_ok());

        let result = result.unwrap();
    }

    #[test]
    fn encode_short_number_in_returned_pointer() {
        let env = LispEnv::new();
        let short_number = env.encode_number("1");
        assert_eq!(0b10010, short_number);
    }

    #[test]
    fn set_cell_pointer() {
        let mut cell = Cell::empty();
        cell.set_pointer(12345);
        assert_eq!(cell.cdr, (12345 as u64) << 4);
    }

    #[test]
    fn encode_symbol_name() {
        let encoded = Cell::encode_symbol_name("nil").0;
        let expected = 0_u64 | (b'l' as u64) << 2 | (b'i' as u64) << 1 | (b'n' as u64);
        assert_eq!(expected, encoded);
    }

    #[test]
    fn encode_long_symbol_name() {
        let (encoded, rest) = Cell::encode_symbol_name("abcdefghijklmnop");
        let expected = 0_u64
            | (b'a' as u64)
            | (b'b' as u64) << 1
            | (b'c' as u64) << 2
            | (b'd' as u64) << 3
            | (b'e' as u64) << 4
            | (b'f' as u64) << 5
            | (b'g' as u64) << 6
            | (b'h' as u64) << 7;
        assert_eq!(expected, encoded);
        assert_eq!("ijklmnop".as_bytes(), rest);
    }
}

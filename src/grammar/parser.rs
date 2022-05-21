use pest::iterators::{Pair, Pairs};
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
                format!(
                    "Num[{}] | Raw[{}] | ASCII[{}]",
                    self.as_number(),
                    self.car,
                    Cell::decode_symbol_name(self.car)
                )
            } else if is_symbol_ptr(self.car) {
                format!("SymbolPtr:[{}]", self.car_ptr())
            } else {
                format!("Cell{{car: {}}}", self.car)
            };
            f.write_fmt(format_args!("Cell[List {}, next: {}]", val, self.cdr_ptr()))
        } else {
            let car_str = if is_number(self.car) {
                format!(
                    "Num[{}] | Raw[{}] | ASCII[{}]",
                    as_number(self.car),
                    self.car,
                    Cell::decode_symbol_name(self.car)
                )
            } else if is_symbol_ptr(self.car) {
                format!("SymbolPtr:[{}]", self.car_ptr())
            } else {
                self.car.to_string()
            };
            let cdr_str = if is_number(self.cdr) {
                format!(
                    "Num[{}] | Raw[{}] | ASCII[{}]",
                    as_number(self.cdr),
                    self.cdr,
                    Cell::decode_symbol_name(self.cdr)
                )
            } else if is_symbol_ptr(self.cdr) {
                format!("SymbolPtr:[{}]", self.cdr_ptr())
            } else {
                self.cdr.to_string()
            };
            f.write_fmt(format_args!("Cell{{car: {}, cdr: {}}}", car_str, cdr_str))
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
        is_number(self.car)
    }

    pub fn as_number(&self) -> i64 {
        as_number(self.car)
    }

    pub fn set_car_pointer(&mut self, raw_addr: usize) {
        self.car = (raw_addr as u64) << 4;
    }

    pub fn set_cdr_pointer(&mut self, raw_addr: usize) {
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
            result |= (*b as u64) << idx * 8;
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

pub fn is_number(val: u64) -> bool {
    val & 0b10 > 0
}

pub fn as_number(val: u64) -> i64 {
    // FIXME Naive implementation, won't take big numbers into account
    (val >> 4) as i64 * if val & 0b1000 > 0 { -1 } else { 1 }
}

pub fn is_symbol_ptr(val: u64) -> bool {
    val & 0b1110 == 0b1000
}

pub fn is_pointer(val: u64) -> bool {
    val & 0b0110 == 0
}

pub fn ptr(val: u64) -> usize {
    if !is_pointer(val) {
        panic!("Not a pointer: {}!", val);
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

type Memory = RefCell<Slab<Cell>>;

pub struct LispEnv {
    memory: Memory,
    nil_key: u64,
    /// Initially an anonymous symbol with a nil value, should receive all the internal symbols of
    /// created during the environment lifetime.
    internal_symbols_key: u64,

    functions: HashMap<String, Box<dyn Fn(usize, &LispEnv) -> u64>>,
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

    /// Returns an encoded pointer to the property entry (cf `prop_val`, below)
    fn append_property(&self, symbol_ptr: u64, name_ptr: u64, val: u64) -> u64 {
        let symbol_ptr = ptr(symbol_ptr);
        if !self.memory.borrow().contains(symbol_ptr) {
            panic!("Inconsistent pointer {}", symbol_ptr);
        }

        {
            let mut root_cell = &mut self.memory.borrow_mut()[symbol_ptr];
            if !is_pointer(root_cell.car) {
                // Then we need to rearrange the cell to describe a non-unitary symbol
            }
        }

        // initially the symbol could be [ name | val ], and we want to have
        // [name_ptr | val]
        //      -> [prop_val_ptr | name ]
        //              -> [prop_val | prop_name_ptr]
        //                      -> [prop_name | nil]
        // to add new properties, we just need to climb down the pointer list and replace the nil

        // TODO For now we'll assume that there won't be any duplicate keys
        let name_cell_idx = self.allocate_empty_cell();
        let prop_val_cell_idx = self.allocate_empty_cell();
        let prop_name_cell_idx = self.allocate_empty_cell();
        let symbol_name = {
            let mut symbol_cell = &mut self.memory.borrow_mut()[symbol_ptr];
            let name_ptr = symbol_cell.car;
            symbol_cell.set_car_pointer(name_cell_idx);

            name_ptr
        };
        {
            let mut name_cell = &mut self.memory.borrow_mut()[name_cell_idx];
            name_cell.set_car_pointer(prop_val_cell_idx);
            name_cell.cdr = symbol_name;
        }
        {
            let mut prop_val_cell = &mut self.memory.borrow_mut()[prop_val_cell_idx];
            prop_val_cell.car = val;
            // prop_val_cell.cdr = Cell::encode_symbol_name(name).0;
            prop_val_cell.set_cdr_pointer(prop_name_cell_idx);
        }
        {
            let mut prop_name_cell = &mut self.memory.borrow_mut()[prop_name_cell_idx];
            prop_name_cell.car = name_ptr;
        }

        (prop_val_cell_idx as u64) << 4
    }

    fn print_memory(&self) {
        for (idx, cell) in &*self.memory.borrow() {
            println!("{}: {:?}", idx, cell);
        }
    }

    fn global_scope_contains_property(&self, name: &str) -> bool {
        // TODO for now we'll only assume a single property under _lisprs_
        let root_cell = &self.memory.borrow()[self.internal_symbols_key as usize >> 4];
        if !is_pointer(root_cell.car) {
            return false;
        }

        let name_cell = &self.memory.borrow()[root_cell.car as usize >> 4];
        let first_prop_val_cell = &self.memory.borrow()[name_cell.car as usize >> 4];
        let first_prop_name_cell = &self.memory.borrow()[first_prop_val_cell.cdr as usize >> 4];

        Cell::encode_symbol_name(name).0 == first_prop_name_cell.car
    }

    fn get_property(&self, symbol_ptr: u64, key: &str) -> Option<u64> {
        let root_cell = &self.memory.borrow()[symbol_ptr as usize >> 4];
        if !is_pointer(root_cell.car) {
            return None;
        }

        let encoded_name = Cell::encode_symbol_name(key).0;

        let name_cell = &self.memory.borrow()[root_cell.car as usize >> 4];
        let mut next_entry_ptr = name_cell.car;
        while next_entry_ptr != 0 {
            let prop_val = &self.memory.borrow()[next_entry_ptr as usize >> 4];
            let prop_name = &self.memory.borrow()[prop_val.cdr as usize >> 4];

            if encoded_name == prop_name.car {
                return Some(prop_val.car);
            }

            next_entry_ptr = prop_name.cdr;
        }

        None
    }

    pub fn property_count(&self, symbol_ptr: u64) -> usize {
        let root_cell = &self.memory.borrow()[ptr(symbol_ptr)];
        if !is_pointer(root_cell.car) {
            return 0;
        }

        let name_cell = &self.memory.borrow()[root_cell.car as usize >> 4];
        let mut next_entry_ptr = name_cell.car;
        let mut count = 0;
        while next_entry_ptr != 0 {
            let prop_val = &self.memory.borrow()[next_entry_ptr as usize >> 4];
            let prop_name = &self.memory.borrow()[prop_val.cdr as usize >> 4];

            count += 1;

            next_entry_ptr = prop_name.cdr;
        }

        count
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
        env.internal_symbols_key =
            env.allocate_symbol(Some("_lisprs_"), env.nil_key as usize) as u64;
        env.functions.insert(
            "+".to_string(),
            Box::new(|args_idx, env| {
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
                // (env.insert_cell(Cell {
                //     car: number_pointer(sum.abs() as u64, sum < 0),
                //     cdr: 0,
                // }) << 4) as u64 // we return a generic pointer
                // TODO Return a short nb whenever possible, or encode the result on the heap and
                //      return its pointer
                number_pointer(sum.abs() as u64, sum < 0)
            }),
        );
        env.functions.insert(
            "*".to_string(),
            Box::new(|args_idx, env| {
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
                // (env.insert_cell(Cell {
                //     car: number_pointer(result.abs() as u64, result < 0),
                //     cdr: 0,
                // }) << 4) as u64
                number_pointer(result.abs() as u64, result < 0)
            }),
        );
        env.functions.insert(
            "def".to_string(),
            Box::new(|args_idx, env| {
                let (value_head, symbol_cell_idx) = {
                    let memory = env.memory.borrow();
                    let args = &memory[args_idx];
                    println!("arg cell: {:?}", args);

                    (memory[args.cdr_ptr()].car, args.car_ptr())
                };

                let name_ptr = env.memory.borrow()[symbol_cell_idx].car;
                env.append_property(env.internal_symbols_key, name_ptr, value_head);
                value_head
            }),
        );
        env.append_property(
            env.internal_symbols_key,
            Cell::encode_symbol_name("pi").0,
            env.encode_number("3.141592653589793"),
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

    fn eval_atom(&mut self, atom: Pair<Rule>) -> Result<Option<u64>, pest::error::Error<Rule>> {
        let cell_value = match atom.as_rule() {
            Rule::number => Some(self.encode_number(atom.as_str())),
            Rule::symbol => {
                if self.functions.contains_key(atom.as_str()) {
                    println!("Pushing op {}", atom.as_str());
                    self.call_stack.push_back(atom.as_str().to_string());
                    None
                } else if self.global_scope_contains_property(atom.as_str()) {
                    self.get_property(self.internal_symbols_key, atom.as_str())
                } else {
                    println!("Allocating symbol {}", atom.as_str());
                    Some(self.allocate_symbol(Some(atom.as_str()), self.nil_key as usize))
                }
            }
            Rule::sexpr => Some(self.eval_list(atom.into_inner())? as u64),
            Rule::quoted_atom => {
                Some(self.allocate_symbol(Some(atom.into_inner().as_str()), self.nil_key as usize))
            }
            _ => unimplemented!("Rule: {}", atom.as_str()),
        };

        Ok(cell_value)
    }

    fn eval_list(&mut self, atoms: Pairs<Rule>) -> Result<u64, pest::error::Error<Rule>> {
        // The list eval currently creates a new list with each element being evaluated

        println!("--- LIST atoms {:?}", atoms);

        let mut result = 0_u64; // pointer to nil
        let mut last_cell_ptr = None;

        for atom in atoms {
            if let Some(atom_value) = self.eval_atom(atom)? {
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
        }

        println!(
            "Result: {}, {:?}",
            result,
            &self.memory.borrow()[result as usize]
        );

        if let Some(fn_name) = self.call_stack.pop_front() {
            println!("About to apply function {}", fn_name);
            self.print_memory();
            result = self.functions[&fn_name](result as usize, &self);
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

    pub fn eval(&mut self, input: &str) -> Result<u64, pest::error::Error<Rule>> {
        let root = LispGrammar::parse(Rule::lisp, input)?
            .next()
            .unwrap()
            .into_inner();
        println!("Root: {:?}", root);
        let mut result = 0_u64;
        for statement in root {
            if statement.as_rule() == Rule::EOI {
                continue;
            }

            result = self.eval_atom(statement)?.unwrap();
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use crate::grammar::parser::{
        as_number, is_number, is_pointer, is_symbol_ptr, number_pointer, ptr, Cell, LispEnv,
    };

    #[test]
    fn parse_empty_list() {
        let mut env = LispEnv::new();
        let result = env.eval("()");
        assert!(result.is_ok());

        let list = result.unwrap();
        assert_eq!(0_u64, list);
        // assert_eq!(Cell::encode_symbol_name("nil").0, list.car);
        // assert_eq!(env.nil_key, list.cdr);
    }

    // #[test]
    // fn empty_list_is_nil() {
    //     let mut env = LispEnv::new();
    //     let result = env.eval("()").unwrap();
    //     assert!(result.is_nil());
    // }

    #[test]
    fn parse_symbol() {
        let mut env = LispEnv::new();
        let result = env.eval("(a)");
        assert!(result.is_ok());

        let result = result.unwrap();
        // assert!(result.is_list());
        // assert!(is_symbol_ptr(result.car));
        assert!(is_pointer(result));

        // let first_element = &env.memory.borrow()[result.car_ptr()];
        // assert!(!first_element.is_number());
        // assert_eq!("a", Cell::decode_symbol_name(first_element.car));
    }

    #[test]
    fn parse_quoted_symbol() {
        let mut env = LispEnv::new();
        let result = env.eval("'a");
        assert!(result.is_ok());

        let result = result.unwrap();
        env.print_memory();
        assert!(is_symbol_ptr(result));
    }

    #[test]
    fn assign_property_to_symbol() {
        let mut env = LispEnv::new();
        let result = env.eval("(put 'X 'a 1)"); // puts a=1 into X
        println!("{:?}", result);
        assert!(result.is_ok());

        env.print_memory();

        let result = result.unwrap();
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

        env.print_memory();
        let result = result.unwrap();
        println!("{:?}", result);
        assert!(is_pointer(result));
        // assert!(result.is_list());
        // assert_eq!(env.encode_number("1") as u64, result.car);
        // assert_eq!(0, result.cdr);
    }

    #[test]
    fn parse_list_of_two_numbers() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let result = env.eval("(1 2)");
        assert!(result.is_ok());
        assert_eq!(original_memory_size + 2, env.memory.borrow().len());

        let list_head = result.unwrap();
        assert!(is_pointer(list_head));

        let list_head = &env.memory.borrow()[list_head as usize >> 4];
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
        env.print_memory();
        assert_eq!(original_memory_size + 2, env.memory.borrow().len());
        // the 2 values in the operation (result is directly returned as a short number)

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(3, as_number(result));
    }

    #[test]
    fn parse_nested_operation_1() {
        let mut env = LispEnv::new();
        let result = env.eval("(+ (+ 1 2) 4)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(7, as_number(result));
    }

    #[test]
    fn parse_nested_operation_2() {
        let mut env = LispEnv::new();
        let result = env.eval("(+ (+ 1 2) (+ 3 (+ 4 5 6)))");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(21, as_number(result));
    }

    #[test]
    fn parse_multiplication() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let result = env.eval("(* 2 3 6)");
        assert!(result.is_ok());
        assert_eq!(original_memory_size + 3, env.memory.borrow().len());
        // the 3 values in the operation (result is returned as a short number)

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(36, as_number(result));
    }

    #[test]
    fn parse_very_small_program() {
        let mut env = LispEnv::new();
        let result = env.eval("(def r 10)\nr");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
        assert_eq!(10, as_number(result));
    }

    #[test]
    fn parse_small_program() {
        let mut env = LispEnv::new();
        let result = env.eval("(def r 10)\n(* pi (* r r))");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert_eq!(300, as_number(result));
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
        cell.set_cdr_pointer(12345);
        assert_eq!(cell.cdr, (12345 as u64) << 4);
    }

    #[test]
    fn encode_symbol_name() {
        let encoded = Cell::encode_symbol_name("nil").0;
        let expected = 0_u64 | (b'l' as u64) << 16 | (b'i' as u64) << 8 | (b'n' as u64);
        assert_eq!(expected, encoded);
    }

    #[test]
    fn encode_long_symbol_name() {
        let (encoded, rest) = Cell::encode_symbol_name("abcdefghijklmnop");
        let expected = 0_u64
            | (b'a' as u64)
            | (b'b' as u64) << 8
            | (b'c' as u64) << 16
            | (b'd' as u64) << 24
            | (b'e' as u64) << 32
            | (b'f' as u64) << 40
            | (b'g' as u64) << 48
            | (b'h' as u64) << 56;
        assert_eq!(expected, encoded);
        assert_eq!("ijklmnop".as_bytes(), rest);
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

    #[test]
    fn decode_symbol_name() {
        assert_eq!("nil", Cell::decode_symbol_name(7104878_u64));
    }

    #[test]
    fn global_scope_is_allocated() {
        let env = LispEnv::new();
        assert_ne!(0, env.internal_symbols_key);

        let scope_root = &env.memory.borrow()[ptr(env.internal_symbols_key)];
        assert_eq!(0, scope_root.cdr);
        assert!(is_pointer(scope_root.car));

        let scope_name = &env.memory.borrow()[ptr(scope_root.car)];
        assert_ne!(0, scope_name.car);
        assert_eq!(Cell::encode_symbol_name("_lisprs_").0, scope_name.cdr);
        assert!(env.property_count(env.internal_symbols_key) > 0);
    }

    #[test]
    fn append_property_to_symbol() {
        let env = LispEnv::new();
        let symbol_ptr = env.allocate_symbol(Some("symb"), 0);

        let original_mem_size = env.memory.borrow().len();
        let name_ptr = Cell::encode_symbol_name("foo").0;
        let prop_ptr = env.append_property(symbol_ptr, name_ptr, number_pointer(10, false));
        assert_eq!(original_mem_size + 3, env.memory.borrow().len());
        // 2 cells for the prop and its value, and another cell for the "_lisprs_" name that's moved
        // in a separate cell
        assert_ne!(0, prop_ptr);

        let root_cell = &env.memory.borrow()[symbol_ptr as usize >> 4];
        assert_eq!(0, root_cell.cdr);
        assert_eq!((symbol_ptr >> 4) + 1, root_cell.car >> 4);

        let symbol_name_cell = &env.memory.borrow()[(symbol_ptr as usize >> 4) + 1];
        assert_eq!(Cell::encode_symbol_name("symb").0, symbol_name_cell.cdr);
        assert_eq!(prop_ptr, symbol_name_cell.car);

        let prop_val_cell = &env.memory.borrow()[prop_ptr as usize >> 4];
        assert_eq!(10, as_number(prop_val_cell.car));
        assert_eq!((symbol_ptr >> 4) + 3, prop_val_cell.cdr >> 4);

        let prop_name_cell = &env.memory.borrow()[(symbol_ptr as usize >> 4) + 3];
        assert_eq!(Cell::encode_symbol_name("foo").0, prop_name_cell.car);
        assert_eq!(0, prop_name_cell.cdr);

        assert_eq!(1, env.property_count(symbol_ptr));
    }

    #[test]
    fn append_another_property_to_symbol() {
        let env = LispEnv::new();
        let symbol_ptr = env.allocate_symbol(Some("symb"), 0);

        let first_name_ptr = Cell::encode_symbol_name("foo").0;
        let first_prop_ptr =
            env.append_property(symbol_ptr, first_name_ptr, number_pointer(10, false));
        let original_mem_size = env.memory.borrow().len();

        let second_name_ptr = Cell::encode_symbol_name("bar").0;
        let second_prop_ptr =
            env.append_property(symbol_ptr, second_name_ptr, number_pointer(42, false));
        assert_ne!(0, second_prop_ptr);

        let first_name_cell_ptr = env.memory.borrow()[ptr(first_prop_ptr)].cdr;
        let first_name_cell = &env.memory.borrow()[ptr(first_name_cell_ptr)];
        assert_eq!(first_name_cell.cdr, second_prop_ptr);
        assert_eq!(2, env.property_count(symbol_ptr));
    }

    #[test]
    fn property_is_in_global_scope() {
        let env = LispEnv::new();
        let original_mem_size = env.memory.borrow().len();
        let name_ptr = Cell::encode_symbol_name("foo").0;
        let prop_ptr = env.append_property(
            env.internal_symbols_key,
            name_ptr,
            number_pointer(10, false),
        );
        assert!(env.global_scope_contains_property("foo"));
    }

    #[test]
    fn get_property_value() {
        let env = LispEnv::new();
        let original_mem_size = env.memory.borrow().len();
        let name_ptr = Cell::encode_symbol_name("foo").0;
        let prop_ptr = env.append_property(
            env.internal_symbols_key,
            name_ptr,
            number_pointer(10, false),
        );
        assert_eq!(
            Some(number_pointer(10, false)),
            env.get_property(env.internal_symbols_key, "foo")
        );
    }
}

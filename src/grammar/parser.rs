use pest::iterators::Pairs;
use pest::Parser as PestParser;
use pest_derive::Parser;
use slab::Slab;
use std::cmp::min;
use std::collections::{HashMap, VecDeque};
use std::str::FromStr;

#[derive(Clone, Debug, PartialEq)]
pub struct Cell {
    car: u64,
    cdr: u64,
}

impl Cell {
    pub fn empty() -> Self {
        Self { car: 0, cdr: 0 }
    }

    pub fn is_nil(&self) -> bool {
        self.car == Cell::symbol_name("nil").0 && self.cdr == 0 // by convention nil is the first entry, so its addr is 0
    }

    pub fn is_list(&self) -> bool {
        self.cdr & 0b1110 == 0 // CDR is a pointer
    }

    pub fn number(s: &str) -> Self {
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
        Cell::from((payload, sign))
    }

    pub fn is_number(&self) -> bool {
        // FIXME Won't take big numbers into account, would need the env
        self.car == 0 && self.cdr & 0b10 > 0
    }

    pub fn as_number(&self) -> i64 {
        // FIXME Naive implementation, won't take big numbers into account
        (self.cdr >> 4) as i64 * if self.cdr & 0b1000 > 0 { -1 } else { 1 }
    }

    pub fn set_pointer(&mut self, raw_addr: usize) {
        self.cdr = (raw_addr as u64) << 4;
    }

    pub fn is_symbol(&self) -> bool {
        self.cdr & 0b1110 == 0b1000
    }

    pub fn symbol_name(name: &str) -> (u64, &[u8]) {
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

    pub fn ptr(&self) -> usize {
        if self.cdr & 0b1110 != 0 {
            panic!("Not a pointer!");
        }

        (self.cdr >> 4) as usize
    }
}

impl From<(u64, bool)> for Cell {
    fn from((payload, sign_bit): (u64, bool)) -> Self {
        let sign_bit = if sign_bit { 0b1000 } else { 0b0000 };
        let payload = payload << 4 | sign_bit | 0b010;
        Cell {
            car: 0,
            cdr: payload,
        }
    }
}

#[derive(Parser)]
#[grammar = "./grammar/lisp.pest"]
pub struct LispGrammar;

enum Record {
    Function(Box<dyn Fn(&Cell, &LispEnv) -> (Cell, bool)>),
    Variable(Cell),
}

pub struct LispEnv {
    memory: Slab<Cell>,
    nil_key: u64,
    /// Function pointer returns whether the cell should be added to the heap or is a copy
    functions: HashMap<String, Record>,
    call_stack: VecDeque<String>,
}

impl LispEnv {
    fn allocate_nil(&mut self) -> usize {
        let nil_key = {
            let nil_entry = self.memory.vacant_entry();
            let nil_key = nil_entry.key();
            let nil = Cell {
                car: Cell::symbol_name("nil").0,
                cdr: nil_key as u64,
            };
            nil_entry.insert(nil);
            nil_key
        };
        self.memory.insert(Cell {
            car: nil_key as u64,
            cdr: nil_key as u64,
        });

        nil_key
    }

    fn allocate_symbol(&mut self, name: Option<&str>, value_ptr: usize) -> usize {
        let cell_key = self.allocate_empty_cell();
        let cell_tail_key = name.map(|name| {
            let cell_tail_key = self.allocate_empty_cell();
            let cell_tail = &mut self.memory[cell_tail_key];

            let (name_fragment, rest) = Cell::symbol_name(name);
            if rest.is_empty() {
                cell_tail.cdr = name_fragment;
            } else {
                unimplemented!("name is big number");
            }
            cell_tail_key
        });
        let cell = &mut self.memory[cell_key];
        cell.cdr = (value_ptr as u64) << 4 | 0b1000;
        cell.car = cell_tail_key.unwrap_or(0) as u64;

        cell_key
    }

    fn allocate_empty_cell(&mut self) -> usize {
        self.memory.insert(Cell::empty())
    }

    fn insert_cell(&mut self, cell: Cell) -> usize {
        self.memory.insert(cell)
    }

    fn print_memory(&self) {
        for (idx, cell) in &self.memory {
            println!("{}: {:?}", idx, cell);
        }
    }

    pub fn new() -> Self {
        let mut env = Self {
            memory: Slab::<Cell>::with_capacity(1024),
            nil_key: 0,
            functions: HashMap::new(),
            call_stack: VecDeque::new(),
        };
        env.nil_key = env.allocate_nil() as u64;
        env.functions.insert(
            "+".to_string(),
            Record::Function(Box::new(|args, env| {
                let mut sum = env.memory[args.car as usize].as_number();
                let mut current_cell = &env.memory[args.ptr()];
                while !current_cell.is_nil() {
                    println!("+ current cell: {:?}", current_cell);
                    let value_cell = &env.memory[current_cell.car as usize];
                    println!("Value cell: {:?}", value_cell);
                    if !value_cell.is_number() {
                        unimplemented!("handle type error");
                    }

                    sum += (value_cell.cdr >> 4) as i64; // FIXME Proper conversion with sign bit!
                    println!("current sum: {}", sum);
                    current_cell = &env.memory[current_cell.ptr()];
                }
                (Cell::from((sum.abs() as u64, sum < 0)), true)
            })),
        );
        env.functions.insert(
            "*".to_string(),
            Record::Function(Box::new(|args, env| {
                let mut current_cell = args;
                let mut result = env.memory[args.car as usize].as_number();
                let mut current_cell = &env.memory[args.ptr()];
                while !current_cell.is_nil() {
                    println!("* current cell: {:?}", current_cell);
                    // FIXME Get the car as the initial result (SAME FOR ADD)
                    let value_cell = &env.memory[current_cell.car as usize];
                    println!("Value cell: {:?}", value_cell);
                    if !value_cell.is_number() {
                        unimplemented!("handle type error: {:?}", value_cell);
                    }

                    result *= (value_cell.cdr >> 4) as i64; // FIXME Proper conversion with sign bit!
                    println!("current result: {}", result);
                    current_cell = &env.memory[current_cell.ptr()];
                }
                (Cell::from((result.abs() as u64, result < 0)), true)
            })),
        );
        env.functions.insert(
            "def".to_string(),
            Record::Function(Box::new(|args, env| {
                println!("arg cell: {:?}", args);
                let symbol_cell = &env.memory[args.car as usize];
                println!("Symbol cell: {:?}", symbol_cell);
                if !symbol_cell.is_symbol() {
                    panic!("NOT A SYMBOL");
                }

                let symbol_name_cell = &env.memory[symbol_cell.car as usize];
                let first_letter = char::from((symbol_name_cell.cdr & 0xff) as u8);
                println!("First letter: {}", first_letter);

                let list_cell = &env.memory[args.ptr()];
                let value_cell = &env.memory[list_cell.car as usize];
                let value = value_cell.as_number();
                println!("Value to be assigned: {}", value);

                // env.allocate_symbol()
                // FIXME
                todo!("LispEnv should actually be &mut")
            })),
        );
        env.functions.insert(
            "pi".to_string(),
            Record::Variable(Cell::number("3.141592653589793")),
        );
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
            let result_cell_key = match atom.as_rule() {
                Rule::number => {
                    // if idx == 0 {
                    //     self.call_stack.push_back("list".to_string());
                    // }
                    Some(self.insert_cell(Cell::number(atom.as_str())))
                }
                Rule::symbol => {
                    if self.functions.contains_key(atom.as_str()) {
                        println!("Pushing op {}", atom.as_str());
                        self.call_stack.push_back(atom.as_str().to_string());
                        None
                    } else {
                        let cell_idx =
                            self.allocate_symbol(Some(atom.as_str()), self.nil_key as usize);
                        println!("symbol cell: {}", cell_idx);
                        Some(cell_idx)
                    }
                }
                Rule::sexpr => Some(self.eval_list(atom.into_inner())?),
                _ => unimplemented!(),
            };
            if let Some(res_key) = result_cell_key {
                let list_cell_key = self.allocate_empty_cell();
                self.memory[list_cell_key].car = res_key as u64;
                if let Some(list_ptr) = last_cell_ptr {
                    self.memory[list_ptr].set_pointer(list_cell_key);
                }
                last_cell_ptr = Some(list_cell_key);

                if list_head.is_none() {
                    list_head = Some(list_cell_key);
                }
            }
        }

        // Complete the list with nil
        if let Some(list_ptr) = last_cell_ptr {
            let last_cell = &mut self.memory[list_ptr];
            last_cell.cdr = self.nil_key as u64;
        } else {
            list_head = Some(self.nil_key as usize);
        }

        let mut list_head = list_head.unwrap();
        println!("List head: {:?}, {:?}", list_head, &self.memory[list_head]);

        if let Some(fn_name) = self.call_stack.pop_front() {
            println!("About to apply record {}", fn_name);
            self.print_memory();
            let (result, new_cell) = match &self.functions[&fn_name] {
                Record::Function(function) => function(&self.memory[list_head], &self),
                Record::Variable(val) => (val.to_owned(), true),
            };
            println!("{:?}", result);
            if new_cell {
                list_head = self.insert_cell(result);
            }
        }

        Ok(list_head)
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

            result = self.memory[list_head].to_owned();
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use crate::grammar::parser::{Cell, LispEnv};

    #[test]
    fn parse_empty_list() {
        let mut env = LispEnv::new();
        let result = env.eval("()");
        assert!(result.is_ok());

        let list = result.unwrap();
        assert_eq!(Cell::symbol_name("nil").0, list.car);
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

        let result = result.unwrap();
        assert!(result.is_list());

        let first_element = &env.memory[result.car as usize];
        assert!(first_element.is_symbol());
        assert!(!first_element.is_number());

        let name_cell = &env.memory[first_element.car as usize];
        let first_letter = char::from((name_cell.cdr & 0xff) as u8);
        assert_eq!('a', first_letter);
    }

    // #[test]
    // fn parse_string() {
    //     assert!(LispEnv::eval("(\"a\")").is_ok());
    // }
    //
    #[test]
    fn parse_list_of_single_short_number() {
        let mut env = LispEnv::new();
        let result = env.eval("(1)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(result.is_list());

        let first_element = &env.memory[result.car as usize];
        assert_eq!(Cell::number("1"), *first_element);
        assert!(env.memory[result.cdr as usize].is_nil());
    }

    #[test]
    fn parse_list_of_two_numbers() {
        let mut env = LispEnv::new();
        let result = env.eval("(1 2)");
        assert!(result.is_ok());

        let list_head = result.unwrap();
        assert!(list_head.is_list());

        let first_element = &env.memory[list_head.car as usize];
        assert_eq!(Cell::number("1"), *first_element);

        let list_tail = &env.memory[list_head.ptr()];
        assert!(list_tail.is_list());

        let second_element = &env.memory[list_tail.car as usize];
        assert_eq!(Cell::number("2"), *second_element);
        assert_eq!(list_tail.cdr, 0);
    }

    #[test]
    fn parse_simple_operation() {
        let mut env = LispEnv::new();
        let result = env.eval("(+ 1 2)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(result.is_number());
        assert_eq!(3, result.as_number());
    }

    #[test]
    fn parse_nested_operation() {
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
        let result = env.eval("(* 2 3 6)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(result.is_number());
        assert_eq!(36, result.as_number());
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
    fn encode_short_number() {
        let number = Cell::number("1");
        assert_eq!(0, number.car);
        assert_eq!(0b10010, number.cdr);
        assert!(number.is_number());
        assert!(!number.is_symbol());
    }

    #[test]
    fn set_cell_pointer() {
        let mut cell = Cell::empty();
        cell.set_pointer(12345);
        assert_eq!(cell.cdr, (12345 as u64) << 4);
    }

    #[test]
    fn encode_symbol_name() {
        let encoded = Cell::symbol_name("nil").0;
        let expected = 0_u64 | (b'l' as u64) << 2 | (b'i' as u64) << 1 | (b'n' as u64);
        assert_eq!(expected, encoded);
    }

    #[test]
    fn encode_long_symbol_name() {
        let (encoded, rest) = Cell::symbol_name("abcdefghijklmnop");
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

use crate::grammar::cell::Cell;
use crate::grammar::util::{as_number, is_number, is_pointer, is_symbol_ptr, number_pointer, ptr};
use pest::iterators::{Pair, Pairs};
use pest::Parser as PestParser;
use pest_derive::Parser;
use slab::Slab;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::fmt::Debug;
use std::str::FromStr;

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
    /// Pointer to an in-memory list of namespaces within the current evaluation scope.
    namespaces_idx: usize,

    functions: HashMap<String, Box<dyn Fn(usize, &LispEnv) -> u64>>,
    call_stack: VecDeque<Option<String>>,
}

impl LispEnv {
    fn allocate_nil(&self) -> usize {
        let nil_key = {
            let mut memory = self.memory.borrow_mut();
            let nil_entry = memory.vacant_entry();
            let nil_key = nil_entry.key();
            let nil = Cell {
                car: Cell::encode_symbol_name("NIL").0,
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
    fn allocate_symbol(&self, name: Option<&str>, value_ptr: u64) -> u64 {
        let cell_key = self.allocate_empty_cell();
        {
            let cell = &mut self.memory.borrow_mut()[cell_key];
            if let Some(name) = name {
                let (name_fragment, rest) = Cell::encode_symbol_name(name);
                println!("Name frag: {:#b}", name_fragment);
                if rest.is_empty() {
                    cell.car = name_fragment;
                } else {
                    unimplemented!("name is big number");
                }
            };
            cell.cdr = value_ptr;
        }

        println!("Symbol allocated at idx {}", cell_key);

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

    /// Returns an encoded pointer to the property __slot__, i.e. the cell which points at the
    /// effective property entry. Since that cell and its immediate child are effectively structured
    /// as a symbol, it is therefore quite trivial to generate nested symbol structures.
    fn append_property(&self, symbol_ptr: u64, prop_name_ptr: u64, prop_val: u64) -> u64 {
        let symbol_ptr = ptr(symbol_ptr);
        if !self.memory.borrow().contains(symbol_ptr) {
            panic!("Inconsistent pointer {}", symbol_ptr);
        }

        // initially the symbol would be [ name | val ], and we want to have
        // [name_ptr | val]
        //      -> [1st_prop_slot | name ]
        //              -> [prop_ptr | nil]
        //                      -> [prop_val | prop_name]
        // to add new properties, we just need to climb down the pointer list and replace the nil

        // TODO For now we'll assume that there won't be any duplicate keys

        let prop_slot_idx = self.allocate_empty_cell();
        let prop_cell_idx = self.allocate_empty_cell();
        {
            self.memory.borrow_mut()[prop_slot_idx].set_car_pointer(prop_cell_idx);
            let mut prop_cell = &mut self.memory.borrow_mut()[prop_cell_idx];
            prop_cell.car = prop_val;
            prop_cell.cdr = prop_name_ptr;
        }

        {
            let root_cell_car = self.memory.borrow()[symbol_ptr].car;
            if is_pointer(root_cell_car) {
                let name_cell_car = self.memory.borrow()[ptr(root_cell_car)].car;
                println!(
                    "Symbol name is {}",
                    Cell::decode_symbol_name(self.memory.borrow()[ptr(root_cell_car)].cdr)
                );
                let mut current_property_slot_ptr = name_cell_car;
                loop {
                    println!(
                        "Current property slot ptr: {:#b}",
                        current_property_slot_ptr
                    );
                    let next_prop_ptr = self.memory.borrow()[ptr(current_property_slot_ptr)].cdr;
                    if next_prop_ptr == 0 {
                        self.memory.borrow_mut()[ptr(current_property_slot_ptr)]
                            .set_cdr_pointer(prop_slot_idx);
                        break;
                    }
                    // let prop_name = &mut self.memory.borrow_mut()[ptr(next_prop_ptr)];
                    //
                    // if prop_name.cdr == 0 {
                    //     prop_name.set_cdr_pointer(prop_slot_idx);
                    //     break;
                    // }
                    current_property_slot_ptr = next_prop_ptr;
                }
            } else {
                // in that case root_cell_car contains the symbol name
                // Then we need to rearrange the cell to describe a non-unitary symbol
                let name_cell_idx = self.allocate_empty_cell();
                self.memory.borrow_mut()[symbol_ptr].set_car_pointer(name_cell_idx);
                println!(
                    "New root cell car: {:#b}",
                    self.memory.borrow()[symbol_ptr].car
                );
                {
                    let mut name_cell = &mut self.memory.borrow_mut()[name_cell_idx];
                    name_cell.set_car_pointer(prop_slot_idx);
                    name_cell.cdr = root_cell_car;
                }
            }
        };

        (prop_slot_idx as u64) << 4
    }

    fn symbol_name(&self, symbol_ptr: u64) -> Option<String> {
        if !is_symbol_ptr(symbol_ptr) {
            panic!("Not a symbol pointer!");
        }

        let root_cell = &self.memory.borrow()[ptr(symbol_ptr)];
        if root_cell.car == 0 {
            None
        } else if is_number(root_cell.car) {
            Some(Cell::decode_symbol_name(root_cell.car))
        } else {
            let prop_cell = &self.memory.borrow()[ptr(root_cell.car)];
            Some(Cell::decode_symbol_name(prop_cell.cdr)) // assuming a short number name
        }
    }

    fn print_memory(&self) {
        for (idx, cell) in &*self.memory.borrow() {
            println!("{}: {:?}", idx, cell);
        }
    }

    fn global_scope_contains_property(&self, name: &str) -> bool {
        self.get_property(self.internal_symbols_key, name).is_some()
    }

    /// Returns an optional pointer to the property value cell
    fn get_property(&self, symbol_ptr: u64, key: &str) -> Option<u64> {
        let root_cell = &self.memory.borrow()[ptr(symbol_ptr)];
        if !is_pointer(root_cell.car) {
            return None;
        }

        let encoded_name = Cell::encode_symbol_name(key).0;

        let name_cell = &self.memory.borrow()[ptr(root_cell.car)];
        let mut next_entry_ptr = name_cell.car;
        while next_entry_ptr != 0 {
            let slot_cell = &self.memory.borrow()[ptr(next_entry_ptr)];
            let prop_cell = &self.memory.borrow()[ptr(slot_cell.car)];

            if encoded_name == prop_cell.cdr {
                return Some(prop_cell.car);
            }

            next_entry_ptr = slot_cell.cdr;
        }

        None
    }

    pub fn property_count(&self, symbol_ptr: u64) -> usize {
        let root_cell = &self.memory.borrow()[ptr(symbol_ptr)];
        if !is_symbol_ptr(root_cell.car) {
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

    pub fn get_list_length(&self, list_ptr: u64) -> usize {
        if !is_pointer(list_ptr) {
            return 0;
        }
        let mut cell_cdr = self.memory.borrow()[ptr(list_ptr)].cdr;

        let mut len = 1;
        while cell_cdr != 0 {
            cell_cdr = self.memory.borrow()[ptr(cell_cdr)].cdr;
            len += 1;
        }

        return len;
    }

    fn compare_half_cells(
        &self,
        left: u64,
        right: u64,
        pending_cells: &mut VecDeque<(Cell, Cell)>,
    ) -> bool {
        if left == right {
            true
        } else if is_pointer(left) && is_pointer(right) {
            if left == self.nil_key && right == self.nil_key {
                return true;
            } else if left == self.nil_key || right == self.nil_key {
                return false;
            }
            // Recursive call
            let left_cell = self.memory.borrow()[ptr(left)].to_owned();
            let right_cell = self.memory.borrow()[ptr(right)].to_owned();
            pending_cells.push_back((left_cell, right_cell));
            true
        } else {
            false
        }
    }

    pub fn new() -> Self {
        let mut env = Self {
            memory: RefCell::new(Slab::<Cell>::with_capacity(1024)),
            nil_key: 0,
            internal_symbols_key: 0,
            namespaces_idx: 0,
            functions: HashMap::new(),
            call_stack: VecDeque::new(),
        };
        env.nil_key = env.allocate_nil() as u64;
        env.internal_symbols_key = env.allocate_symbol(Some("_lisprs"), env.nil_key) as u64;
        env.namespaces_idx = env.allocate_empty_cell();
        {
            let namespaces_cell = &mut env.memory.borrow_mut()[env.namespaces_idx];
            namespaces_cell.car = env.internal_symbols_key;
        }
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
                let value_head = match dbg!(env.get_list_length((args_idx as u64) << 4)) {
                    2 => {
                        let (value_head, symbol_cell_idx) = {
                            let memory = env.memory.borrow();
                            let args = &memory[args_idx];
                            println!("arg cell: {:?}", args);

                            (memory[args.cdr_ptr()].car, args.car_ptr())
                        };

                        let name_ptr = env.memory.borrow()[symbol_cell_idx].car;
                        env.append_property(env.internal_symbols_key, name_ptr, value_head);
                        value_head
                    }
                    3 => {
                        let (name_car, arg_list_car, body_car) = {
                            let memory = env.memory.borrow();
                            let name_cell = &memory[args_idx];
                            let name_arg = env.memory.borrow()[ptr(name_cell.car)].car;

                            let arg_list_cell = &memory[ptr(name_cell.cdr)];
                            if !is_pointer(arg_list_cell.car) {
                                panic!("Expected an arg list");
                            }

                            let program_body_cell = &memory[ptr(arg_list_cell.cdr)];

                            (name_arg, arg_list_cell.car, program_body_cell.car)
                        };
                        let result_ptr = env.allocate_empty_cell();
                        {
                            let mut result = &mut env.memory.borrow_mut()[result_ptr];
                            result.car = arg_list_car;
                            result.cdr = body_car;
                        }

                        let result_ptr = (result_ptr as u64) << 4;
                        env.append_property(env.internal_symbols_key, name_car, result_ptr);

                        result_ptr
                    }
                    _ => {
                        unimplemented!()
                    }
                };

                value_head
            }),
        );
        env.functions.insert(
            "put".to_string(),
            Box::new(|args_idx, env| {
                let (symbol_name, symbol_cell_car, property_name_cell_car, property_value) = {
                    let memory = env.memory.borrow();
                    let args = &memory[args_idx];
                    println!("arg cell: {:?}", args);
                    let symbol_cell = &memory[ptr(args.car)];
                    let symbol_name = Cell::decode_symbol_name(symbol_cell.car);
                    let property_name_slot = &memory[ptr(args.cdr)];
                    let property_name_cell = &memory[ptr(property_name_slot.car)];
                    let property_name = Cell::decode_symbol_name(property_name_cell.car);
                    let property_value_slot = &memory[ptr(property_name_slot.cdr)];
                    let property_value = property_value_slot.car; // for now we'll assume a short number is encoded in the car
                    println!(
                        "property name is {}, and value is {:?}",
                        property_name,
                        as_number(property_value)
                    );

                    (
                        symbol_name,
                        symbol_cell.car,
                        property_name_cell.car,
                        property_value,
                    )
                };
                let property_ptr = env
                    .get_property(env.internal_symbols_key, &symbol_name)
                    .unwrap_or_else(|| {
                        env.append_property(env.internal_symbols_key, symbol_cell_car, 0)
                    });
                env.append_property(property_ptr, property_name_cell_car, property_value)
            }),
        );
        env.functions.insert(
            "symbols".to_string(),
            Box::new(|args_idx, env| {
                if args_idx == 0 {
                    let symbol_name = {
                        let first_symbol_slot = &env.memory.borrow()[env.namespaces_idx];
                        if first_symbol_slot.cdr != 0 {
                            unimplemented!("actual list of namespaces!")
                        }

                        // let first_symbol = &env.memory.borrow()[ptr(first_symbol_slot.car)];
                        env.symbol_name(first_symbol_slot.car).unwrap()
                    };

                    let result_idx = env.allocate_empty_cell();
                    let mut result_cell = &mut env.memory.borrow_mut()[result_idx];
                    println!("Symbol name is {}", symbol_name);
                    result_cell.car = Cell::encode_symbol_name(&symbol_name).0;
                    (result_idx as u64) << 4
                } else {
                    unimplemented!()
                }
            }),
        );
        env.functions.insert(
            "=".to_string(),
            Box::new(|args_idx, env| {
                let memory = env.memory.borrow();
                let first_arg_slot = &memory[args_idx];
                println!("arg cell: {:?}", first_arg_slot);
                // TODO List iterator!!!
                if first_arg_slot.cdr == 0 {
                    unimplemented!()
                }

                let second_arg_slot = &memory[ptr(first_arg_slot.cdr)];
                if second_arg_slot.cdr != 0 {
                    unimplemented!()
                }

                let mut pending_cells = VecDeque::new();

                // Since the arg slot are defining a list, we'll necessarily have different cdrs,
                // since first_arg_slot will be pointing to second_arg_slot, so we just compare the
                // actual values, i.e. the cars
                if !env.compare_half_cells(
                    first_arg_slot.car,
                    second_arg_slot.car,
                    &mut pending_cells,
                ) {
                    return env.nil_key;
                }

                while let Some((left, right)) = pending_cells.pop_front() {
                    println!("Left cell: {:?}, Right cell: {:?}", left, right);
                    if !env.compare_half_cells(left.car, right.car, &mut pending_cells) {
                        return env.nil_key;
                    }

                    if !env.compare_half_cells(left.cdr, right.cdr, &mut pending_cells) {
                        return env.nil_key;
                    }
                }

                Cell::encode_symbol_name("T").0
            }),
        );
        env.append_property(
            env.internal_symbols_key,
            Cell::encode_symbol_name("NIL").0,
            env.nil_key,
        );
        env.append_property(
            env.internal_symbols_key,
            Cell::encode_symbol_name("pi").0,
            env.encode_number("3.141592653589793"),
        );
        // FIXME `list` is probably not a primitive, but is used now in order to get a consistent
        // call stack
        // env.functions.insert(
        //     "list".to_string(),
        //     Box::new(|args, env| (args.to_owned(), false)),
        // );
        env
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
                function(result as usize, &self)
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

            match self.eval_atom(statement, true, 0)? {
                (Some(val), false) => result = val,
                _ => unimplemented!(),
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use crate::grammar::cell::Cell;
    use crate::grammar::parser::LispEnv;
    use crate::grammar::util::{
        as_number, is_number, is_pointer, is_symbol_ptr, number_pointer, ptr,
    };

    #[test]
    fn parse_empty_list_and_return_nil() {
        let mut env = LispEnv::new();
        let result = env.eval("()");
        assert!(result.is_ok());

        let list = result.unwrap();
        assert_eq!(0_u64, list);
    }

    #[test]
    fn parse_symbol() {
        let mut env = LispEnv::new();
        let result = env.eval("(a)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_pointer(result));

        let cell = &env.memory.borrow()[ptr(result)];
        assert!(cell.is_list());
        assert!(is_symbol_ptr(cell.car));

        let first_element = &env.memory.borrow()[cell.car_ptr()];
        assert!(first_element.is_number());
        assert_eq!("a", Cell::decode_symbol_name(first_element.car));
    }

    #[test]
    fn parse_nested_list() {
        let mut env = LispEnv::new();
        let result = env.eval("((a))");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_pointer(result));

        let cell = &env.memory.borrow()[ptr(result)];
        assert!(cell.is_list());
        assert!(is_pointer(cell.car));
        assert_eq!(0, cell.cdr);

        let nested_list = &env.memory.borrow()[ptr(cell.car)];
        assert!(is_symbol_ptr(nested_list.car));
        assert_eq!(0, nested_list.cdr);

        let symbol = &env.memory.borrow()[ptr(nested_list.car)];
        assert_eq!("a", Cell::decode_symbol_name(symbol.car));
    }

    #[test]
    fn parse_quoted_number() {
        let mut env = LispEnv::new();
        let result = env.eval("'1");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_number(result));
    }

    #[test]
    fn parse_quoted_symbol_with_quote_mark() {
        let mut env = LispEnv::new();
        let result = env.eval("'a");
        assert!(result.is_ok());
        // should be rewritten as `(quote a)`

        let result = result.unwrap();
        assert!(is_symbol_ptr(result));

        let symbol_cell = &env.memory.borrow()[ptr(result)];
        assert_eq!("a", Cell::decode_symbol_name(symbol_cell.car));
        assert_eq!(0, symbol_cell.cdr);
    }

    #[test]
    fn parse_quoted_symbol_with_quote_function() {
        let mut env = LispEnv::new();
        let result = env.eval("(quote a)");
        assert!(result.is_ok());

        env.print_memory();
        let result = result.unwrap();
        assert!(is_symbol_ptr(result));

        let symbol_cell = &env.memory.borrow()[ptr(result)];
        assert_eq!("a", Cell::decode_symbol_name(symbol_cell.car));
        assert_eq!(0, symbol_cell.cdr);
    }

    #[test]
    fn parse_quoted_symbol_in_list() {
        let mut env = LispEnv::new();
        let result = env.eval("('a)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(!is_symbol_ptr(result));
        assert!(is_pointer(result));

        let first_slot = &env.memory.borrow()[ptr(result)];
        assert!(is_symbol_ptr(first_slot.car));
        assert_eq!(0, first_slot.cdr);

        let first_cell = &env.memory.borrow()[ptr(first_slot.car)];
        assert_eq!("a", Cell::decode_symbol_name(first_cell.car));
    }

    #[test]
    fn parse_quoted_list() {
        let mut env = LispEnv::new();
        let result = env.eval("'(a b c)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(!is_symbol_ptr(result));
        assert!(is_pointer(result));

        // FIXME Result should point directly at the first cell, and not create an indirection

        let first_slot = &env.memory.borrow()[ptr(result)];
        assert!(is_symbol_ptr(first_slot.car));
        assert_ne!(0, first_slot.cdr);

        let second_slot = &env.memory.borrow()[ptr(first_slot.cdr)];
        assert!(is_symbol_ptr(second_slot.car));
        assert_ne!(0, second_slot.cdr);

        let third_slot = &env.memory.borrow()[ptr(second_slot.cdr)];
        assert!(is_symbol_ptr(third_slot.car));
        assert_eq!(0, third_slot.cdr);
    }

    #[test]
    fn parse_nested_quoted_symbol() {
        let mut env = LispEnv::new();
        let result = env.eval("(quote (quote (quote a)))");
        assert!(result.is_ok());

        // expecting `('('(a)))`
        // or rather expecting `(quote (quote a))`??

        let result = result.unwrap();
        assert!(is_pointer(result));

        env.print_memory();

        let root_cell = &env.memory.borrow()[ptr(result)];
        println!("Root cell: {:?}", root_cell);
        assert!(is_symbol_ptr(root_cell.car));
        assert_ne!(0, root_cell.cdr);

        let first_cell = &env.memory.borrow()[ptr(root_cell.car)];
        assert_eq!("quote", Cell::decode_symbol_name(first_cell.car));

        let second_slot = &env.memory.borrow()[ptr(root_cell.cdr)];
        assert!(!is_symbol_ptr(second_slot.car));
        assert_eq!(0, second_slot.cdr);

        let second_list = &env.memory.borrow()[ptr(second_slot.car)];
        assert!(is_symbol_ptr(second_list.car));
        assert_ne!(0, second_list.cdr);

        let second_cell = &env.memory.borrow()[ptr(second_list.car)];
        // actually as part of the second list
        assert_eq!("quote", Cell::decode_symbol_name(second_cell.car));
        assert_eq!(0, second_cell.cdr);

        let third_slot = &env.memory.borrow()[ptr(second_list.cdr)];
        assert!(!is_symbol_ptr(third_slot.car));
        assert_eq!(0, third_slot.cdr);

        let third_list = &env.memory.borrow()[ptr(third_slot.car)];
        assert!(is_symbol_ptr(third_list.car));
        assert_eq!(0, third_list.cdr);

        let third_cell = &env.memory.borrow()[ptr(third_list.car)];
        // actually as part of the third list
        assert_eq!("a", Cell::decode_symbol_name(third_cell.car));
        assert_eq!(0, third_cell.cdr);
    }

    #[test]
    fn resolve_value_of_global_symbol() {
        let mut env = LispEnv::new();
        let result = env.eval("(def X NIL)");
        assert!(result.is_ok());

        env.print_memory();
        let result = result.unwrap();
        assert_eq!(0, result);

        let result = env.eval("X");
        assert!(result.is_ok());
        assert_eq!(0, result.unwrap());
    }

    #[test]
    fn assign_property_to_existing_symbol() {
        let mut env = LispEnv::new();
        assert!(env.eval("(def X NIL)").is_ok());

        let result = env.eval("(put 'X 'a 1)");
        assert!(result.is_ok());
    }

    #[test]
    fn assign_property_to_new_symbol() {
        let mut env = LispEnv::new();
        let result = env.eval("(put 'X 'a 1)"); // puts a=1 into X
        assert!(result.is_ok());

        env.print_memory();

        let result = result.unwrap();
        assert!(is_pointer(result));

        assert!(env.global_scope_contains_property("X"));
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

        let cell = &env.memory.borrow()[ptr(result)];
        assert!(cell.is_list());
        assert_eq!(env.encode_number("1") as u64, cell.car);
        assert_eq!(0, cell.cdr);
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
    fn get_list_length() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let list_head = env.eval("(1 2)").unwrap();
        assert_eq!(2, env.get_list_length(list_head));
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
    fn eval_operation_in_sublist() {
        let mut env = LispEnv::new();
        let original_memory_size = env.memory.borrow().len();
        let result = env.eval("(2 (* 3 6))");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_pointer(result));
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
    fn store_small_program() {
        let mut env = LispEnv::new();
        let result = env.eval("(def foo (X) X)");
        assert!(result.is_ok());
        let result = result.unwrap();
        println!("Result ptr: {}", ptr(result));
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
    fn call_small_program() {
        let mut env = LispEnv::new();
        let result = env.eval("(def foo (X) X)\n(foo 42)");
        assert!(result.is_ok());
        let result = result.unwrap();
        println!("Result ptr: {}", ptr(result));
        env.print_memory();
        assert_eq!(42, as_number(result));

        // TODO Detect that the symbol references a program, and applies the arguments to the program
    }

    #[test]
    fn parse_fibonacci_function() {
        let mut env = LispEnv::new();
        let result = env.eval(
            r#"
(def fib (N)
	(if (<= N 1) N (+ (fib (- N 1)) (fib (- N 2)))))
(fib 10)"#,
        );
        println!("Res: {:?}", result);
        assert!(result.is_ok());

        let result = result.unwrap();
    }

    #[test]
    fn list_single_namespace() {
        let mut env = LispEnv::new();
        let result = env.eval("(symbols)");
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(is_pointer(result));

        let root_cell = &env.memory.borrow()[ptr(result)];
        assert_eq!(Cell::encode_symbol_name("_lisprs").0, root_cell.car);
        assert_eq!(0, root_cell.cdr);
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
        let encoded = Cell::encode_symbol_name("NIL").0;
        let expected = 0b0010_u64 | (b'L' as u64) << 24 | (b'I' as u64) << 16 | (b'N' as u64) << 8;
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
        assert_eq!(24834_u64, val);
    }

    #[test]
    fn decode_short_symbol_name() {
        assert_eq!("a", Cell::decode_symbol_name(24834_u64));
    }

    #[test]
    fn decode_symbol_name() {
        assert_eq!("nil", Cell::decode_symbol_name(1818848770_u64));
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
        assert_eq!(Cell::encode_symbol_name("_lisprs").0, scope_name.cdr);
        assert!(env.property_count(env.internal_symbols_key) > 0);
    }

    #[test]
    fn append_property_to_symbol() {
        let env = LispEnv::new();
        let symbol_ptr = env.allocate_symbol(Some("symb"), 0);

        let original_mem_size = env.memory.borrow().len();
        let name_ptr = Cell::encode_symbol_name("foo").0;
        let prop_slot = env.append_property(symbol_ptr, name_ptr, number_pointer(10, false));
        assert_eq!(original_mem_size + 3, env.memory.borrow().len());
        // 2 cells for the prop and its value, and another cell for the "_lisprs" name that's moved
        // in a separate cell
        assert_ne!(0, prop_slot);

        // expected symbol structure:
        //  symb:
        //    foo: 10
        // cell-wise:
        // [symb_name_ptr | nil]
        //    -> [foo_cell_slot (1st item in list) | "symb"]
        //          -> [foo_cell_ptr | nil]
        //                -> [10 | "foo"]

        let root_cell = &env.memory.borrow()[symbol_ptr as usize >> 4];
        assert_eq!(0, root_cell.cdr);
        assert_eq!((symbol_ptr >> 4) + 3, root_cell.car >> 4);

        let symbol_name_cell = &env.memory.borrow()[(symbol_ptr as usize >> 4) + 3];
        assert_eq!(Cell::encode_symbol_name("symb").0, symbol_name_cell.cdr);

        let prop_slot_cell = &env.memory.borrow()[ptr(symbol_name_cell.car)];
        assert_eq!(0, prop_slot_cell.cdr);

        let prop_ptr = env.memory.borrow()[ptr(prop_slot)].car;
        let prop_cell = &env.memory.borrow()[ptr(prop_ptr)];
        assert_eq!(10, as_number(prop_cell.car));
        assert_eq!(Cell::encode_symbol_name("foo").0, prop_cell.cdr);

        assert_eq!(1, env.property_count(symbol_ptr));
    }

    #[test]
    fn append_another_property_to_symbol() {
        let env = LispEnv::new();
        let symbol_ptr = env.allocate_symbol(Some("symb"), 0);

        let first_name_ptr = Cell::encode_symbol_name("foo").0;
        let first_prop_slot =
            env.append_property(symbol_ptr, first_name_ptr, number_pointer(10, false));

        let second_name_ptr = Cell::encode_symbol_name("bar").0;
        let second_prop_slot =
            env.append_property(symbol_ptr, second_name_ptr, number_pointer(42, false));
        assert_ne!(first_prop_slot, second_prop_slot);

        // expected symbol structure:
        //  symb:
        //    foo: 10
        //    bar: 42
        // cell-wise:
        // [symb_name_ptr | nil]
        //    -> [1st property slot | "symb"]
        //          -> [foo_cell_ptr | bar_cell_slot] -> [bar_cell_ptr | nil]
        //                   -> [10 | "foo"]                -> [42 | "bar"]

        let first_prop_ptr = env.memory.borrow()[ptr(first_prop_slot)].car;
        let foo_cell = &env.memory.borrow()[ptr(first_prop_ptr)];
        assert_eq!(first_name_ptr, foo_cell.cdr);
        assert_eq!(10, as_number(foo_cell.car));

        let second_prop_ptr = env.memory.borrow()[ptr(second_prop_slot)].car;
        let bar_cell = &env.memory.borrow()[ptr(second_prop_ptr)];
        assert_eq!(second_name_ptr, bar_cell.cdr);
        assert_eq!(42, as_number(bar_cell.car));

        let property_root_ptr = env.memory.borrow()[ptr(symbol_ptr)].car;
        let property_root_cell = &env.memory.borrow()[ptr(property_root_ptr)];
        assert_eq!(Cell::encode_symbol_name("symb").0, property_root_cell.cdr);

        let foo_slot_cell = &env.memory.borrow()[ptr(property_root_cell.car)];
        assert_eq!(first_prop_ptr, foo_slot_cell.car);

        let bar_slot_cell = &env.memory.borrow()[ptr(foo_slot_cell.cdr)];
        assert_eq!(second_prop_ptr, bar_slot_cell.car);
        assert_eq!(0, bar_slot_cell.cdr);
    }

    #[test]
    fn assign_symbol_value_to_symbol() {
        // expected symbol structure:
        //  symb:
        //    foo: bar
        // cell-wise:
        // [symb_name_ptr | nil]
        //    -> [property slot | "symb"]
        //          -> [foo_cell_ptr | nil]
        //                 ->  [foo_name_ptr | bar_cell_ptr] -> ["bar" | nil]
        //                           -> [nil | "foo"]
        unimplemented!()
    }

    #[test]
    fn append_symbol_property_to_symbol() {
        let env = LispEnv::new();
        let root_symbol_ptr = env.allocate_symbol(Some("symb"), 0);
        let property_symbol_ptr = env.allocate_symbol(Some("bar"), 0);
        let property_val_ptr = env.append_property(
            root_symbol_ptr,
            Cell::encode_symbol_name("bar").0,
            property_symbol_ptr,
        );

        // expected symbol structure:
        //  symb:
        //    foo:
        //      bar:
        // cell-wise:
        // [symb_name_ptr | nil]
        //    -> [foo_cell_slot (1st item in list) | "symb"]
        //          -> [nil | foo_cell_ptr] -> [foo_name_ptr | nil]
        //                                           -> [bar_cell_ptr | "foo"]
        //                                                   -> [nil | bar_cell_ptr] -> ["bar" | nil]

        assert_ne!(0, property_val_ptr);
    }

    #[test]
    fn assign_property_to_nested_symbol() {
        let env = LispEnv::new();
        let symbol_ptr = env.allocate_symbol(Some("symb"), 0);
        let first_name_ptr = Cell::encode_symbol_name("foo").0;
        let first_prop_ptr = env.append_property(symbol_ptr, first_name_ptr, 0);
        println!("Foo prop ptr is {}", ptr(first_prop_ptr));
        env.print_memory();
        // FIXME The issue is that the property 'foo' is not a symbol. What should be returned should
        //       be the property slot, which happens to be structured like a symbol
        // expected symbol structure:
        // symb:
        //   foo:
        // cell-wise:
        // [symb_name_ptr | nil]
        //    -> [foo_cell_slot (1st item in list) | "symb"]
        //          -> [foo_cell_ptr | nil]
        //                    -> [nil | "foo"]
        let nested_prop_slot = env.append_property(
            first_prop_ptr,
            Cell::encode_symbol_name("bar").0,
            number_pointer(42, false),
        );
        println!("Bar prop slot is {}", ptr(nested_prop_slot));
        env.print_memory();
        // expected symbol structure:
        // symb:
        //   foo:
        //    bar: 42
        // cell-wise:
        // [symb_name_ptr | nil]
        //    -> [foo_cell_slot (1st item in list) | "symb"]
        //          -> [foo_cell_ptr | nil]
        //                    -> [bar_cell_slot | "foo"]
        //                              -> [bar_cell_ptr | nil]
        //                                      -> [42 | bae]

        assert_ne!(0, nested_prop_slot);
        let nested_prop_ptr = env.memory.borrow()[ptr(nested_prop_slot)].car;
        let bar_cell = &env.memory.borrow()[ptr(nested_prop_ptr)];
        assert_eq!(42, as_number(bar_cell.car));
        assert_eq!(Cell::encode_symbol_name("bar").0, bar_cell.cdr);
    }

    #[test]
    fn resolve_simple_symbol_name() {
        let env = LispEnv::new();
        let symbol_ptr = env.allocate_symbol(Some("symb"), 0);
        assert_eq!(Some("symb".to_string()), env.symbol_name(symbol_ptr));
    }

    #[test]
    fn resolve_complex_symbol_name() {
        let env = LispEnv::new();
        let symbol_ptr = env.allocate_symbol(Some("symb"), 0);
        let first_name_ptr = Cell::encode_symbol_name("foo").0;
        env.append_property(symbol_ptr, first_name_ptr, number_pointer(10, false));
        assert_eq!(Some("symb".to_string()), env.symbol_name(symbol_ptr));
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
        let symb_ptr = env.allocate_symbol(Some("foo"), 0);
        let name_ptr = Cell::encode_symbol_name("bar").0;
        let prop_ptr = env.append_property(symb_ptr, name_ptr, number_pointer(10, false));
        assert_eq!(
            Some(number_pointer(10, false)),
            env.get_property(symb_ptr, "bar")
        );
    }

    mod structural_equality {
        use super::super::*;

        #[test]
        fn unequal_short_numbers() {
            let mut env = LispEnv::new();
            let result = env.eval("(= 1 0)");
            assert!(result.is_ok());
            assert_eq!(0, result.unwrap());
        }

        #[test]
        fn equal_short_numbers() {
            let mut env = LispEnv::new();
            let result = env.eval("(= 3 3)");
            assert!(result.is_ok());
            assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
        }

        #[test]
        fn unequal_short_strings() {
            let mut env = LispEnv::new();
            let result = env.eval("(= \"a\" \"b\")");
            assert!(result.is_ok());
            assert_eq!(0, result.unwrap());
        }

        #[test]
        fn equal_short_strings() {
            let mut env = LispEnv::new();
            let result = env.eval("(= \"c\" \"c\")");
            assert!(result.is_ok());
            assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
        }

        #[test]
        fn unequal_single_element_lists() {
            let mut env = LispEnv::new();
            let result = env.eval("(= (3) (5))");
            assert!(result.is_ok());
            assert_eq!(0, result.unwrap());
        }

        #[test]
        fn equal_single_element_lists() {
            let mut env = LispEnv::new();
            let result = env.eval("(= (7) (7))");
            assert!(result.is_ok());
            assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
        }

        #[test]
        fn unequal_simple_symbols() {
            let mut env = LispEnv::new();
            let result = env.eval("(= a b)");
            assert!(result.is_ok());
            assert_eq!(0, result.unwrap());
        }

        #[test]
        fn equal_simple_symbols() {
            let mut env = LispEnv::new();
            let result = env.eval("(= c c)");
            assert!(result.is_ok());
            assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
        }

        #[test]
        fn equal_evaluated_lists() {
            let mut env = LispEnv::new();
            let result = env.eval("(= (1 (* 4 5) (+ 1 3)) (1 20 4))");
            assert!(result.is_ok());
            assert_eq!(Cell::encode_symbol_name("T").0, result.unwrap());
        }

        #[test]
        fn unequal_symbols_with_different_properties() {
            todo!()
        }

        #[test]
        fn equal_symbols_with_identical_properties() {
            todo!()
        }
    }
}

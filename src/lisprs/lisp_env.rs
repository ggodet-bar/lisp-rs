use crate::lisprs::cell::Cell;
use crate::lisprs::core::CORE_FUNCTIONS;
use crate::lisprs::util::{is_number, is_pointer, is_symbol_ptr, number_pointer, ptr};
use slab::Slab;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::str::FromStr;

pub trait LispFunction: Sync {
    fn symbol(&self) -> String;
    fn function(&self, arg_idx: usize, env: &LispEnv) -> u64;
}

type Memory = RefCell<Slab<Cell>>;

pub struct LispEnv {
    pub(crate) memory: Memory,
    pub(crate) nil_key: u64,
    /// Initially an anonymous symbol with a nil value, should receive all the internal symbols of
    /// created during the environment lifetime.
    pub(crate) internal_symbols_key: u64,
    /// Pointer to an in-memory list of namespaces within the current evaluation scope.
    pub(crate) namespaces_idx: usize,

    pub(crate) functions: HashMap<String, &'static dyn LispFunction>,
    pub(crate) call_stack: VecDeque<Option<String>>,
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
    pub fn allocate_symbol(&self, name: Option<&str>, value_ptr: u64) -> u64 {
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

    pub fn allocate_empty_cell(&self) -> usize {
        self.memory.borrow_mut().insert(Cell::empty())
    }

    pub fn encode_number(&self, s: &str) -> u64 {
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

        number_pointer(payload as i64)
    }

    pub fn insert_cell(&self, cell: Cell) -> usize {
        self.memory.borrow_mut().insert(cell)
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
        for core_function in CORE_FUNCTIONS {
            env.functions.insert(core_function.symbol(), *core_function);
        }
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

    /// Returns an encoded pointer to the property __slot__, i.e. the cell which points at the
    /// effective property entry. Since that cell and its immediate child are effectively structured
    /// as a symbol, it is therefore quite trivial to generate nested symbol structures.
    pub fn append_property(&self, symbol_ptr: u64, prop_name_ptr: u64, prop_val: u64) -> u64 {
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

    pub fn symbol_name(&self, symbol_ptr: u64) -> Option<String> {
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

    pub(crate) fn print_memory(&self) {
        for (idx, cell) in &*self.memory.borrow() {
            println!("{}: {:?}", idx, cell);
        }
    }

    pub(crate) fn global_scope_contains_property(&self, name: &str) -> bool {
        self.get_property(self.internal_symbols_key, name).is_some()
    }

    /// Returns an optional pointer to the property value cell
    pub fn get_property(&self, symbol_ptr: u64, key: &str) -> Option<u64> {
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
}

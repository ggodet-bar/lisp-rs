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

        number_pointer(i64::from_str(truncated).unwrap())
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
                    "Target symbol name is {}",
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
        self.get_property_value(self.internal_symbols_key, name)
            .is_some()
    }

    /// Returns an optional pointer to the property **slot**
    pub fn get_property(&self, symbol_ptr: u64, key: &str) -> Option<u64> {
        let root_cell = &self.memory.borrow()[dbg!(ptr(symbol_ptr))];
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
                return Some(slot_cell.car);
            }

            next_entry_ptr = slot_cell.cdr;
        }

        None
    }

    /// Returns an optional pointer to the property value cell
    pub fn get_property_value(&self, symbol_ptr: u64, key: &str) -> Option<u64> {
        self.get_property(symbol_ptr, key)
            .map(|slot_car| self.memory.borrow()[ptr(slot_car)].car)
    }

    pub fn property_count(&self, symbol_ptr: u64) -> usize {
        let root_cell = &self.memory.borrow()[dbg!(ptr(symbol_ptr))];
        if !is_pointer(root_cell.car) {
            return 0;
        }

        let name_cell = &self.memory.borrow()[ptr(root_cell.car)];
        let mut next_entry_ptr = name_cell.car;
        let mut count = 0;
        while next_entry_ptr != 0 {
            let prop_val = &self.memory.borrow()[ptr(next_entry_ptr)];
            let prop_name = &self.memory.borrow()[ptr(prop_val.cdr)];

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lisprs::util::as_number;

    #[test]
    fn list_single_namespace() {
        let mut env = LispEnv::new();
        let program = env.parse("(symbols)").unwrap();
        let result = env.evaluate(program);
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
        let prop_slot = env.append_property(symbol_ptr, name_ptr, number_pointer(10));
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

        let root_cell = &env.memory.borrow()[ptr(symbol_ptr)];
        assert_eq!(0, root_cell.cdr);
        assert_eq!(ptr(symbol_ptr) + 3, ptr(root_cell.car));

        let symbol_name_cell = &env.memory.borrow()[ptr(symbol_ptr) + 3];
        assert_eq!(Cell::encode_symbol_name("symb").0, symbol_name_cell.cdr);

        let prop_slot_cell = &env.memory.borrow()[ptr(symbol_name_cell.car)];
        assert_eq!(0, prop_slot_cell.cdr);

        let prop_ptr = env.memory.borrow()[ptr(prop_slot)].car;
        let prop_cell = &env.memory.borrow()[ptr(prop_ptr)];
        assert_eq!(10, as_number(prop_cell.car));
        assert_eq!(Cell::encode_symbol_name("foo").0, prop_cell.cdr);

        env.print_memory();
        assert_eq!(1, env.property_count(symbol_ptr));
    }

    #[test]
    fn append_another_property_to_symbol() {
        let env = LispEnv::new();
        let symbol_ptr = env.allocate_symbol(Some("symb"), 0);

        let first_name_ptr = Cell::encode_symbol_name("foo").0;
        let first_prop_slot = env.append_property(symbol_ptr, first_name_ptr, number_pointer(10));

        let second_name_ptr = Cell::encode_symbol_name("bar").0;
        let second_prop_slot = env.append_property(symbol_ptr, second_name_ptr, number_pointer(42));
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
            number_pointer(42),
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
        env.append_property(symbol_ptr, first_name_ptr, number_pointer(10));
        assert_eq!(Some("symb".to_string()), env.symbol_name(symbol_ptr));
    }

    #[test]
    fn property_is_in_global_scope() {
        let env = LispEnv::new();
        let name_ptr = Cell::encode_symbol_name("foo").0;
        env.append_property(env.internal_symbols_key, name_ptr, number_pointer(10));
        assert!(env.global_scope_contains_property("foo"));
    }

    #[test]
    fn get_property_value() {
        let env = LispEnv::new();
        let symb_ptr = env.allocate_symbol(Some("foo"), 0);
        let name_ptr = Cell::encode_symbol_name("bar").0;
        env.append_property(symb_ptr, name_ptr, number_pointer(10));
        assert_eq!(
            Some(number_pointer(10)),
            env.get_property_value(symb_ptr, "bar")
        );
    }
}

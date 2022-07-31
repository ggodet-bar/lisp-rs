use crate::lisprs::cell::Cell;
use crate::lisprs::core::CORE_FUNCTIONS;
use crate::lisprs::frame::Frame;
use crate::lisprs::symbol::Symbol;
use crate::lisprs::util::{as_ptr, is_pointer, number_pointer, ptr};
use crate::lisprs::Assets;
use log::*;
use slab::Slab;
use std::cell::RefCell;
use std::collections::HashMap;
use std::str::FromStr;

/// TEMP: Max number of evaluation cycles before the evaluation is forcibly stopped. Used to
///       debug stack overflows (0 means unlimited).
pub const MAX_CYCLES: usize = 0;

/// Defines how many statements should be evaluated before triggering a garbage collection.
pub const GC_PERIOD: usize = 5000;

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

    /// Pointer to the in-memory list of function stacks built on top of the global namespace. A
    /// frame is defined a list cell whose CAR points at a local symbol map.
    pub(crate) stack_frames: usize,

    /// The function name is encoded so we don't need to decode every time we get a name pointer.
    pub(crate) functions: HashMap<u64, &'static dyn LispFunction>,

    /// cf MAX_CYCLES
    pub(crate) cycle_count: RefCell<usize>,
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
    pub fn allocate_symbol(&self, name: Option<&str>, value_ptr: u64) -> Symbol<'_> {
        Symbol::allocate(name, value_ptr, &self)
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
            stack_frames: 0,
            functions: HashMap::new(),
            cycle_count: RefCell::new(0),
        };
        env.nil_key = env.allocate_nil() as u64;
        env.internal_symbols_key = env.allocate_symbol(Some("_lisprs"), env.nil_key).ptr();
        env.namespaces_idx = env.insert_cell(Cell {
            car: env.internal_symbols_key,
            cdr: 0,
        });
        let root_frame = env.insert_cell(Cell {
            car: env.internal_symbols_key,
            cdr: 0,
        });
        env.stack_frames = env.insert_cell(Cell {
            car: as_ptr(root_frame),
            cdr: 0,
        });

        for core_function in CORE_FUNCTIONS {
            env.functions.insert(
                Cell::encode_symbol_name(&core_function.symbol()).0,
                *core_function,
            );
        }

        let symbols_map = Symbol::as_symbol(env.internal_symbols_key, &env);
        symbols_map.append_property(Cell::encode_symbol_name("NIL").0, env.nil_key);
        symbols_map.append_property(
            Cell::encode_symbol_name("pi").0,
            env.encode_number("3.141592653589793"),
        );

        env.load_core_library().unwrap();

        env
    }

    fn load_core_library(&mut self) -> Result<(), ()> {
        for file in Assets::iter() {
            trace!("Load {}", file.as_ref());
            let raw = Assets::get(file.as_ref()).unwrap().data;
            let contents = std::str::from_utf8(&raw).unwrap();

            let program = self.parse(contents).unwrap();
            let _result = self.evaluate(program).unwrap();
        }

        Ok(())
    }

    pub fn allocate_frame(&self) -> Frame {
        Frame::allocate(&self)
    }

    /// Appends the property to the last entry of the frame stack
    pub fn append_property_to_stack(&self, prop_name_ptr: u64, prop_val: u64) -> u64 {
        let stack_tail_car = {
            let stack_head_cell = &self.memory.borrow()[self.stack_frames];
            let last_frame_ptr = stack_head_cell.iter(self).last().unwrap();
            trace!("Will append to stack idx {}", ptr(last_frame_ptr));
            self.memory.borrow()[ptr(last_frame_ptr)].car
            // remember that this returns the last VALUE, mot the last list SLOT!
        };

        let symbol_map = Symbol::as_symbol(stack_tail_car, self);
        symbol_map.append_property(prop_name_ptr, prop_val)
    }

    pub(crate) fn print_memory(&self) {
        for (idx, cell) in &*self.memory.borrow() {
            println!("{}: {:?}", idx, cell);
        }
    }

    /// Returns the size of the used memory, in bytes
    pub(crate) fn memory_size(&self) -> usize {
        self.memory.borrow().len() * 16
        // counts the number of cells, with a single cell containing 2 * u64
    }

    pub(crate) fn global_scope_contains_property(&self, name: &str) -> bool {
        let global_symbol = Symbol::as_symbol(self.internal_symbols_key, self);
        global_symbol
            .get_property_value_by_ptr(Cell::encode_symbol_name(name).0)
            .is_some()
    }

    pub fn get_last_cell_idx(&self, list_ptr: u64) -> usize {
        if !is_pointer(list_ptr) {
            return 0;
        }

        let mut previous_cell_idx = ptr(list_ptr);
        let mut cell_cdr = self.memory.borrow()[previous_cell_idx].cdr;

        while cell_cdr != 0 {
            previous_cell_idx = ptr(cell_cdr);
            cell_cdr = self.memory.borrow()[previous_cell_idx].cdr;
        }

        return previous_cell_idx;
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

    pub fn global_map(&self) -> Symbol {
        Symbol::as_symbol(self.internal_symbols_key, &self)
    }

    pub fn run_garbage_collector(&self) {
        trace!("Running GC");

        let memory = &mut self.memory.borrow_mut();
        memory.retain(|_key, val| !val.is_deallocated())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lisprs::util::as_number;

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
        assert!(env.global_map().property_count() > 0);
    }

    #[test]
    fn append_property_to_symbol() {
        let env = LispEnv::new();
        let symbol = env.allocate_symbol(Some("symb"), 0);

        let original_mem_size = env.memory.borrow().len();
        let name_ptr = Cell::encode_symbol_name("foo").0;
        let prop_slot = symbol.append_property(name_ptr, number_pointer(10));
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

        let root_cell = &env.memory.borrow()[symbol.idx()];
        assert_eq!(0, root_cell.cdr);
        assert_eq!(symbol.idx() + 3, ptr(root_cell.car));

        let symbol_name_cell = &env.memory.borrow()[symbol.idx() + 3];
        assert_eq!(Cell::encode_symbol_name("symb").0, symbol_name_cell.cdr);

        let prop_slot_cell = &env.memory.borrow()[ptr(symbol_name_cell.car)];
        assert_eq!(0, prop_slot_cell.cdr);

        let prop_ptr = env.memory.borrow()[ptr(prop_slot)].car;
        let prop_cell = &env.memory.borrow()[ptr(prop_ptr)];
        assert_eq!(10, as_number(prop_cell.car));
        assert_eq!(Cell::encode_symbol_name("foo").0, prop_cell.cdr);
        assert_eq!(1, symbol.property_count());
    }

    #[test]
    fn append_another_property_to_symbol() {
        let env = LispEnv::new();
        let symbol = env.allocate_symbol(Some("symb"), 0);

        let first_name_ptr = Cell::encode_symbol_name("foo").0;
        let first_prop_slot = symbol.append_property(first_name_ptr, number_pointer(10));

        let second_name_ptr = Cell::encode_symbol_name("bar").0;
        let second_prop_slot = symbol.append_property(second_name_ptr, number_pointer(42));
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

        let property_root_ptr = env.memory.borrow()[symbol.idx()].car;
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
        let root_symbol = env.allocate_symbol(Some("symb"), 0);
        let property_symbol = env.allocate_symbol(Some("bar"), 0);
        let property_val_ptr =
            root_symbol.append_property(Cell::encode_symbol_name("bar").0, property_symbol.ptr());

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
        let symbol = env.allocate_symbol(Some("symb"), 0);
        let first_name_ptr = Cell::encode_symbol_name("foo").0;
        let first_prop_ptr = symbol.append_property(first_name_ptr, 0);
        trace!("Foo prop ptr is {}", ptr(first_prop_ptr));
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
        let prop_symbol = Symbol::as_symbol(first_prop_ptr, &env);
        let nested_prop_slot =
            prop_symbol.append_property(Cell::encode_symbol_name("bar").0, number_pointer(42));
        trace!("Bar prop slot is {}", ptr(nested_prop_slot));
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
    fn property_is_in_global_scope() {
        let env = LispEnv::new();
        let name_ptr = Cell::encode_symbol_name("foo").0;
        env.global_map()
            .append_property(name_ptr, number_pointer(10));
        assert!(env.global_scope_contains_property("foo"));
    }

    #[test]
    fn get_property_value() {
        let env = LispEnv::new();
        let symb = env.allocate_symbol(Some("foo"), 0);
        let name_ptr = Cell::encode_symbol_name("bar").0;
        symb.append_property(name_ptr, number_pointer(10));
        assert_eq!(
            Some(number_pointer(10)),
            symb.get_property_value_by_name("bar")
        );
    }

    #[test]
    fn get_list_length() {
        let mut env = LispEnv::new();
        let list_head = env.parse("(1 2)").unwrap();
        let first_statement = env.memory.borrow()[list_head].car;
        assert_eq!(2, env.get_list_length(first_statement));
    }

    #[test]
    fn get_last_list_idx_single_cell() {
        let mut env = LispEnv::new();
        let list_head = env.parse("(1)").unwrap();
        let first_statement = env.memory.borrow()[list_head].car;
        let last_idx = env.get_last_cell_idx(first_statement);
        assert_eq!(1, as_number(env.memory.borrow_mut()[last_idx].car));
    }

    #[test]
    fn get_last_list_idx_many_items() {
        let mut env = LispEnv::new();
        let list_head = env.parse("(1 2 3)").unwrap();
        let first_statement = env.memory.borrow()[list_head].car;
        let last_idx = env.get_last_cell_idx(first_statement);
        assert_eq!(3, as_number(env.memory.borrow_mut()[last_idx].car));
    }

    #[test]
    fn cadr_from_stdlib() {
        let mut env = LispEnv::new();
        let program = env.parse("(cadr (1 2 3))").unwrap();
        let result = env.evaluate(program).unwrap();
        assert_eq!(2, as_number(result));
    }

    #[test]
    fn root_stack_points_frame_points_to_global_scope() {
        let env = LispEnv::new();
        let root_stack_cell = &env.memory.borrow()[env.stack_frames];
        assert_eq!(0, root_stack_cell.cdr);
        assert_ne!(env.internal_symbols_key, root_stack_cell.car);
        assert!(is_pointer(root_stack_cell.car));

        let frame_cell = &env.memory.borrow()[ptr(root_stack_cell.car)];
        assert_eq!(frame_cell.car, env.internal_symbols_key);
    }
}

use crate::lisprs::cell::Cell;
use crate::lisprs::lisp_env::BorrowedCell;
use crate::lisprs::symbol::Symbol;
use crate::lisprs::util::{as_ptr, ptr};
use crate::lisprs::LispEnv;
use log::*;
use std::cell::Ref;

/// A stack frame has the following structure:
///
/// ```
/// [frame_map_ptr | 0]
///     -> [map_name_ptr | 0]
///             -> [prop_list_ptr | "_frame_"]
/// ```
///
/// or initially, before the symbols are copied over to the frame:
///
/// ```
/// [frame_map_ptr | 0]
///     -> ["_frame_" | 0]
/// ```
pub struct Frame<'a> {
    frame_ptr: u64,
    pub(crate) symbol_map_ptr: u64,
    previous_frame_idx: usize,
    env: &'a LispEnv,
}

impl<'a> Frame<'a> {
    /// Allocates a new execution frame, adds it to frames stack, and returns the new pointer
    /// to this new frame map and to the previous frame cell (for deallocation purposes).
    pub fn allocate(env: &'a LispEnv) -> Self {
        let (first_frame_ptr, last_frame_ptr) = {
            let mem = env.memory.state.borrow();
            let first_frame_cell = mem.mem[env.stack_frames].clone();
            let first_frame_ptr = first_frame_cell.car;
            let last_frame_idx = env.get_last_cell_idx(as_ptr(env.stack_frames));
            let last_frame_ptr = mem.mem[last_frame_idx].car;
            // Pointing at the previous frame will allow us to search through the properties more efficiently
            (first_frame_ptr, last_frame_ptr)
        };

        let frame_map = Symbol::allocate(Some("_frame_"), 0, &env);
        let new_frame = env.insert_cell(Cell {
            car: frame_map.ptr(),
            cdr: last_frame_ptr,
        });
        let new_slot = env.insert_cell(Cell {
            car: as_ptr(new_frame),
            cdr: 0,
        });

        if last_frame_ptr != first_frame_ptr {
            // we're skipping the global symbols, which is far too big to copy every time

            // Remember that `last` will return the last VALUE of the iterator, not the last SLOT
            // pointer!
            // let last_frame_ptr = env.memory.borrow()[env.stack_frames]
            //     .iter(env)
            //     .last()
            //     .unwrap();
            trace!("--- fetching last stack ptr");
            // self.print_memory();

            // FIXME Smarter symbol handling:
            //       1. Frame contains a pointer to its previous frame, hence to every previous map
            //       2. Looking up a symbol involves scanning the frames, in reverse order
            //       3. Appending adds to the local map only

            let property_values = {
                let mem = env.memory.state.borrow();

                let frame_symbol_map = Symbol::as_symbol(mem.mem[ptr(last_frame_ptr)].car, env);
                let symbol_map_properties_ptr = frame_symbol_map.properties_ptr();
                let cell = BorrowedCell::new(Ref::clone(&mem), ptr(symbol_map_properties_ptr));

                cell.iter()
                    .map(|property_ptr| {
                        let prop_cell = &mem.mem[ptr(property_ptr)];
                        (prop_cell.cdr, prop_cell.car)
                        // FIXME Super simple copy, actually requires deep copies.
                    })
                    .collect::<Vec<_>>()
            };
            for (prop_name, prop_val) in property_values {
                frame_map.append_property(prop_name, prop_val);
            }
        }

        let last_frame_idx = env.get_last_cell_idx(as_ptr(env.stack_frames));
        env.memory
            .borrow_mem_mut(last_frame_idx)
            .cell
            .set_cdr_pointer(new_slot);

        Self {
            frame_ptr: as_ptr(new_frame),
            symbol_map_ptr: frame_map.ptr(),
            previous_frame_idx: last_frame_idx,
            env: &env,
        }
    }

    pub fn symbol_map(&self) -> Symbol<'a> {
        Symbol::as_symbol(self.symbol_map_ptr, self.env)
    }

    /// Appends the property to the last entry of the frame stack
    pub fn append_property(&self, prop_name_ptr: u64, prop_val: u64) -> u64 {
        let frame_map = Symbol::as_symbol(self.symbol_map_ptr, self.env);
        frame_map.append_property(prop_name_ptr, prop_val)
    }

    pub fn deallocate(self) {
        self.env
            .memory
            .borrow_mem_mut(self.previous_frame_idx)
            .cell
            .cdr = 0; // frame deallocation
        self.symbol_map().deallocate();
        self.env
            .memory
            .state
            .borrow_mut()
            .mem
            .remove(ptr(self.frame_ptr));
        trace!("Deallocated frame {}", ptr(self.symbol_map_ptr));
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::cell::Cell;
    use crate::lisprs::util::{is_symbol_ptr, ptr};
    use crate::lisprs::LispEnv;

    #[test]
    fn new_frame_returns_with_current_and_previous_pointers() {
        let env = LispEnv::new();
        let frame = env.allocate_frame();
        assert!(is_symbol_ptr(frame.symbol_map_ptr));
        assert_eq!(env.stack_frames, frame.previous_frame_idx);

        let head_stack_cdr = env.memory.borrow_mem(env.stack_frames).cell.cdr;
        let stack_slot_cell = &env.memory.borrow_mem(ptr(head_stack_cdr));
        assert_eq!(0, stack_slot_cell.cell.cdr);

        let frame_cell = &env.memory.borrow_mem(ptr(stack_slot_cell.cell.car));
        assert_eq!(frame_cell.cell.car, frame.symbol_map_ptr);
    }

    #[test]
    fn new_frame_copies_symbols_does_not_copy_symbols_from_global_map() {
        let env = LispEnv::new();
        let frame = env.allocate_frame();
        let root_symbol_map_size = env.global_map().property_count();
        assert_ne!(0, root_symbol_map_size);
        assert_eq!(0, frame.symbol_map().property_count());
    }

    #[test]
    fn new_frame_copies_symbol_from_non_root_frame() {
        let env = LispEnv::new();
        let frame = env.allocate_frame();
        frame.append_property(Cell::encode_symbol_name("foo").0, 10);
        frame.append_property(Cell::encode_symbol_name("bar").0, 42);
        frame.append_property(Cell::encode_symbol_name("foobar").0, 24);
        assert_eq!(3, frame.symbol_map().property_count());

        let top_frame = env.allocate_frame();
        assert_eq!(3, top_frame.symbol_map().property_count());
        assert_eq!(
            Some(10),
            top_frame.symbol_map().get_property_value_by_name("foo")
        );
        assert_eq!(
            Some(42),
            top_frame.symbol_map().get_property_value_by_name("bar")
        );
        assert_eq!(
            Some(24),
            top_frame.symbol_map().get_property_value_by_name("foobar")
        );
    }
}

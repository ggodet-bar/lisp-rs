use crate::lisprs::cell::Cell;
use crate::lisprs::util::{as_ptr, ptr};
use crate::lisprs::LispEnv;
use log::*;

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
    pub(crate) symbol_map_ptr: u64,
    previous_frame_idx: usize,
    env: &'a LispEnv,
}

impl<'a> Frame<'a> {
    /// Allocates a new execution frame, adds it to frames stack, and returns the new pointer
    /// to this new frame map and to the previous frame cell (for deallocation purposes).
    pub fn allocate(env: &'a LispEnv) -> Self {
        let frame_map_ptr = env.allocate_symbol(Some("_frame_"), 0);
        let new_frame = env.insert_cell(Cell {
            car: frame_map_ptr,
            cdr: 0,
        });
        let new_slot = env.insert_cell(Cell {
            car: as_ptr(new_frame),
            cdr: 0,
        });

        {
            // Remember that `last` will return the last VALUE of the iterator, not the last SLOT
            // pointer!
            let last_frame_ptr = env.memory.borrow()[env.stack_frames]
                .iter(env)
                .last()
                .unwrap();
            trace!("--- fetching last stack ptr");
            // self.print_memory();
            let frame_symbol_map_ptr = env.memory.borrow()[ptr(last_frame_ptr)].car;
            let symbol_map_properties_ptr = env.symbol_properties(frame_symbol_map_ptr);

            let property_pointers = env.memory.borrow()[ptr(symbol_map_properties_ptr)]
                .iter(env)
                .collect::<Vec<u64>>();
            for property_ptr in property_pointers {
                let (prop_name, prop_val) = {
                    let prop_cell = &env.memory.borrow()[ptr(property_ptr)];
                    (prop_cell.cdr, prop_cell.car)
                };
                // FIXME Super simple copy, actually requires deep copies.
                // self.print_memory();
                env.append_property(frame_map_ptr, prop_name, prop_val);
            }
        }

        let last_frame_idx = env.get_last_cell_idx(as_ptr(env.stack_frames));
        env.memory.borrow_mut()[last_frame_idx].set_cdr_pointer(new_slot);

        Self {
            symbol_map_ptr: frame_map_ptr,
            previous_frame_idx: last_frame_idx,
            env: &env,
        }
    }

    pub fn symbol_map_ptr(&self) -> u64 {
        self.symbol_map_ptr
    }

    /// Appends the property to the last entry of the frame stack
    pub fn append_property(&self, prop_name_ptr: u64, prop_val: u64) -> u64 {
        self.env
            .append_property(self.symbol_map_ptr, prop_name_ptr, prop_val)
    }

    pub fn deallocate(self) {
        self.env.memory.borrow_mut()[self.previous_frame_idx].cdr = 0; // frame deallocation

        // FIXME flag the frame and its symbol map as reclaimable
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

        let head_stack_cdr = env.memory.borrow()[env.stack_frames].cdr;
        let stack_slot_cell = &env.memory.borrow()[ptr(head_stack_cdr)];
        assert_eq!(0, stack_slot_cell.cdr);

        let frame_cell = &env.memory.borrow()[ptr(stack_slot_cell.car)];
        assert_eq!(frame_cell.car, frame.symbol_map_ptr);
    }

    #[test]
    fn new_frame_copies_symbols_from_previous_frame() {
        let env = LispEnv::new();
        let frame = env.allocate_frame();
        let root_symbol_map_size = env.property_count(env.internal_symbols_key);
        assert_ne!(0, root_symbol_map_size);
        assert_eq!(
            env.property_count(frame.symbol_map_ptr),
            root_symbol_map_size
        );

        let root_prop_names_ptr = env.symbol_properties(env.internal_symbols_key);
        let list_head_cell = &env.memory.borrow()[ptr(root_prop_names_ptr)];
        let root_prop_names = list_head_cell
            .iter(&env)
            .map(|prop_ptr| env.memory.borrow()[ptr(prop_ptr)].cdr)
            .map(|name| Cell::decode_symbol_name(name))
            .collect::<Vec<String>>();

        let frame_prop_cell =
            &env.memory.borrow()[ptr(env.symbol_properties(frame.symbol_map_ptr))];
        let frame_prop_names = frame_prop_cell
            .iter(&env)
            .map(|prop_ptr| env.memory.borrow()[ptr(prop_ptr)].cdr)
            .map(|name| Cell::decode_symbol_name(name))
            .collect::<Vec<String>>();
        assert_eq!(root_prop_names, frame_prop_names);
    }
}

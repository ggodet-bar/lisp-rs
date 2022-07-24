use crate::lisprs::cell::Cell;
use crate::lisprs::symbol::Symbol;
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
    frame_ptr: u64,
    pub(crate) symbol_map_ptr: u64,
    previous_frame_idx: usize,
    env: &'a LispEnv,
}

impl<'a> Frame<'a> {
    /// Allocates a new execution frame, adds it to frames stack, and returns the new pointer
    /// to this new frame map and to the previous frame cell (for deallocation purposes).
    pub fn allocate(env: &'a LispEnv) -> Self {
        let frame_map = Symbol::allocate(Some("_frame_"), 0, &env);
        let new_frame = env.insert_cell(Cell {
            car: frame_map.ptr(),
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

            let frame_symbol_map =
                Symbol::as_symbol(env.memory.borrow()[ptr(last_frame_ptr)].car, env);
            let symbol_map_properties_ptr = frame_symbol_map.properties_ptr();

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
                frame_map.append_property(prop_name, prop_val);
            }
        }

        let last_frame_idx = env.get_last_cell_idx(as_ptr(env.stack_frames));
        env.memory.borrow_mut()[last_frame_idx].set_cdr_pointer(new_slot);

        Self {
            frame_ptr: as_ptr(new_frame),
            symbol_map_ptr: frame_map.ptr(),
            previous_frame_idx: last_frame_idx,
            env: &env,
        }
    }

    // pub fn as_frame(frame_ptr: u64, env: &'a LispEnv) -> Self {
    //     let frame_cell = &env.memory.borrow()[ptr(frame_ptr)];
    //     Frame {
    //         symbol_map_ptr: frame_cell.car,
    //         previous_frame_idx: xxx,
    //         env,
    //     }
    // }

    pub fn symbol_map(&self) -> Symbol<'a> {
        Symbol::as_symbol(self.symbol_map_ptr, self.env)
    }

    /// Appends the property to the last entry of the frame stack
    pub fn append_property(&self, prop_name_ptr: u64, prop_val: u64) -> u64 {
        let frame_map = Symbol::as_symbol(self.symbol_map_ptr, self.env);
        frame_map.append_property(prop_name_ptr, prop_val)
    }

    pub fn deallocate(self) {
        self.env.memory.borrow_mut()[self.previous_frame_idx].cdr = 0; // frame deallocation
        self.symbol_map().deallocate();
        self.env.memory.borrow_mut()[ptr(self.frame_ptr)].deallocate();
        trace!("Deallocated frame {}", ptr(self.symbol_map_ptr));
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::cell::Cell;
    use crate::lisprs::list::List;
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
        let root_symbol_map_size = env.global_map().property_count();
        assert_ne!(0, root_symbol_map_size);
        assert_eq!(frame.symbol_map().property_count(), root_symbol_map_size);

        let root_prop_names_ptr = env.global_map().properties_ptr();
        let list_head_cell = List::as_list(root_prop_names_ptr, &env);
        let root_prop_names = list_head_cell
            .iter()
            .map(|prop_ptr| env.memory.borrow()[ptr(prop_ptr)].cdr)
            .map(|name| Cell::decode_symbol_name(name))
            .collect::<Vec<String>>();

        let frame_prop_cell = List::as_list(frame.symbol_map().properties_ptr(), &env);
        let frame_prop_names = frame_prop_cell
            .iter()
            .map(|prop_ptr| env.memory.borrow()[ptr(prop_ptr)].cdr)
            .map(|name| Cell::decode_symbol_name(name))
            .collect::<Vec<String>>();
        assert_eq!(root_prop_names, frame_prop_names);
    }
}

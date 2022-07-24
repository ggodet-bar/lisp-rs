use crate::lisprs::cell::Cell;
use crate::lisprs::util::{as_ptr, is_number, is_pointer, is_symbol_ptr, ptr};
use crate::lisprs::LispEnv;
use log::*;

pub struct Symbol<'a> {
    ptr: u64,
    env: &'a LispEnv,
}

impl<'a> Symbol<'a> {
    pub fn allocate(name: Option<&str>, value_ptr: u64, env: &'a LispEnv) -> Self {
        let cell_key = env.insert_cell({
            let name_ptr = if let Some(name) = name {
                let (name_fragment, rest) = Cell::encode_symbol_name(name);
                // trace!("Name frag: {:#b}", name_fragment);
                if !rest.is_empty() {
                    unimplemented!("name is big number");
                }

                name_fragment
            } else {
                0
            };

            Cell {
                car: name_ptr,
                cdr: value_ptr,
            }
        });
        // trace!("Symbol allocated at idx {}", cell_key);

        Self {
            ptr: (cell_key as u64) << 4 | 0b1000,
            env,
        }
    }

    pub fn as_symbol(symbol_ptr: u64, env: &'a LispEnv) -> Self {
        if !is_symbol_ptr(symbol_ptr) {
            panic!("Not a symbol ptr: {}", symbol_ptr);
        }

        Self {
            ptr: symbol_ptr,
            env,
        }
    }

    /// Returns an encoded pointer to the property __slot__, i.e. the cell which points at the
    /// effective property entry. Since that cell and its immediate child are effectively structured
    /// as a symbol, it is therefore quite trivial to generate nested symbol structures.
    pub fn append_property(&self, prop_name_ptr: u64, prop_val: u64) -> u64 {
        // initially the symbol would be [ name | val ], and we want to have
        // [name_ptr | val]
        //      -> [1st_prop_slot | name ]
        //              -> [prop_ptr | nil]
        //                      -> [prop_val | prop_name]
        // to add new properties, we just need to climb down the pointer list and replace the nil

        // TODO For now we'll assume that there won't be any duplicate keys

        let property_name = Cell::decode_symbol_name(prop_name_ptr);
        trace!(
            "Appending {}: {} to idx {}",
            property_name,
            Cell::format_component(prop_val),
            self.ptr()
        );
        if let Some(property_slot_ptr) = self.get_property_by_ptr(prop_name_ptr) {
            trace!("Replacing symbol value at {}", ptr(property_slot_ptr));
            self.env.memory.borrow_mut()[ptr(property_slot_ptr)].car = prop_val;

            return property_slot_ptr;
        }

        let prop_slot_idx = self.env.allocate_empty_cell();
        let prop_cell_idx = self.env.allocate_empty_cell();
        {
            self.env.memory.borrow_mut()[prop_slot_idx].set_car_pointer(prop_cell_idx);
            let mut prop_cell = &mut self.env.memory.borrow_mut()[prop_cell_idx];
            prop_cell.car = prop_val;
            prop_cell.cdr = prop_name_ptr;
        }

        {
            let properties_head_ptr = self.properties_ptr();
            if properties_head_ptr != 0 {
                let last_prop_cell_idx = self.env.get_last_cell_idx(properties_head_ptr);
                self.env.memory.borrow_mut()[last_prop_cell_idx].set_cdr_pointer(prop_slot_idx);
            } else {
                // in that case root_cell_car contains the symbol name
                // Then we need to rearrange the cell to describe a non-unitary symbol
                let root_cell_name = self.env.memory.borrow()[self.idx()].car;
                let name_cell_idx = self.env.insert_cell(Cell {
                    car: as_ptr(prop_slot_idx),
                    cdr: root_cell_name,
                });
                self.env.memory.borrow_mut()[self.idx()].car = as_ptr(name_cell_idx);
            }
        };

        (prop_slot_idx as u64) << 4
    }

    pub fn name(&self) -> Option<String> {
        let root_cell = &self.env.memory.borrow()[self.idx()];
        if root_cell.car == 0 {
            None
        } else if is_number(root_cell.car) {
            Some(Cell::decode_symbol_name(root_cell.car))
        } else {
            let prop_cell = &self.env.memory.borrow()[ptr(root_cell.car)];
            Some(Cell::decode_symbol_name(prop_cell.cdr)) // assuming a short number name
        }
    }

    /// Returns an optional pointer to the property **slot**
    pub fn get_property_by_ptr(&self, name_ptr: u64) -> Option<u64> {
        if self.ptr == 0 {
            return None;
        }

        let property_head_ptr = self.properties_ptr();
        if property_head_ptr == 0 {
            return None;
        }

        let prop_list_head = &self.env.memory.borrow()[ptr(property_head_ptr)];
        prop_list_head.iter(self.env).find(|property_ptr| {
            let prop_cell = &self.env.memory.borrow()[ptr(*property_ptr)];
            name_ptr == prop_cell.cdr
        })
    }

    pub fn get_property_by_name(&self, name: &str) -> Option<u64> {
        self.get_property_by_ptr(Cell::encode_symbol_name(name).0)
    }

    pub fn get_property_value_by_name(&self, name: &str) -> Option<u64> {
        self.get_property_value_by_ptr(Cell::encode_symbol_name(name).0)
    }

    /// Returns an optional pointer to the property value cell
    pub fn get_property_value_by_ptr(&self, name_ptr: u64) -> Option<u64> {
        self.get_property_by_ptr(name_ptr)
            .map(|slot_car| self.env.memory.borrow()[ptr(slot_car)].car)
    }

    pub fn ptr(&self) -> u64 {
        self.ptr
    }

    pub fn idx(&self) -> usize {
        ptr(self.ptr)
    }

    /// Returns a pointer to the head of the symbol's property list, if any.
    /// A typical symbol structure will be as follows:
    ///
    /// ```
    /// [symb_name_ptr | nil]
    ///    -> [symb_list_ptr | "symb"]
    ///          -> [1st_symb_ptr | nil]
    ///                -> [10 | "foo"]
    ///```
    pub fn properties_ptr(&self) -> u64 {
        let root_cell = &self.env.memory.borrow()[self.idx()];
        if root_cell.car == 0 || !is_pointer(root_cell.car) {
            return 0;
        }

        let name_cell = &self.env.memory.borrow()[ptr(root_cell.car)];
        name_cell.car
    }

    pub fn property_count(&self) -> usize {
        let property_list_head = self.properties_ptr();
        if property_list_head == 0 {
            return 0;
        }
        self.env.get_list_length(property_list_head)
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::cell::Cell;
    use crate::lisprs::util::number_pointer;
    use crate::lisprs::LispEnv;

    #[test]
    fn resolve_simple_symbol_name() {
        let env = LispEnv::new();
        let symbol = env.allocate_symbol(Some("symb"), 0);
        assert_eq!(Some("symb".to_string()), symbol.name());
    }

    #[test]
    fn resolve_complex_symbol_name() {
        let env = LispEnv::new();
        let symbol = env.allocate_symbol(Some("symb"), 0);
        let first_name_ptr = Cell::encode_symbol_name("foo").0;
        symbol.append_property(first_name_ptr, number_pointer(10));
        assert_eq!(Some("symb".to_string()), symbol.name());
    }
}

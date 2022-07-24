use crate::lisprs::util::{as_number, as_ptr, is_number, is_symbol_ptr, ptr};
use std::cmp::min;
use std::fmt::{Debug, Formatter};

#[derive(Clone, PartialEq)]
pub struct Cell {
    pub car: u64,
    pub cdr: u64,
}

impl Debug for Cell {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "Cell{{car: {}, cdr: {}}}",
            Cell::format_component(self.car),
            Cell::format_component(self.cdr)
        ))
    }
}

impl Cell {
    pub(crate) fn format_component(val: u64) -> String {
        if is_number(val) {
            format!(
                "Num[{}] | Raw[{}] | ASCII[{}]",
                as_number(val),
                val,
                Cell::decode_symbol_name(val)
            )
        } else if is_symbol_ptr(val) {
            format!("SymbolPtr[{}] | Raw[{}]", ptr(val), val)
        } else {
            format!("Ptr[{}] | Raw[{}]", ptr(val), val)
        }
    }

    pub fn empty() -> Self {
        Self { car: 0, cdr: 0 }
    }

    pub fn is_list(&self) -> bool {
        self.cdr & 0b1110 == 0 // CDR is a pointer
    }

    pub fn is_nil(&self) -> bool {
        self.car == 0 && self.cdr == 0
    }

    pub fn set_car_pointer(&mut self, raw_addr: usize) {
        self.car = as_ptr(raw_addr);
    }

    pub fn set_cdr_pointer(&mut self, raw_addr: usize) {
        self.cdr = as_ptr(raw_addr);
    }

    pub fn car_ptr(&self) -> usize {
        ptr(self.car)
    }

    pub fn cdr_ptr(&self) -> usize {
        ptr(self.cdr)
    }

    pub fn decode_symbol_name(val: u64) -> String {
        let mut buffer: [u8; 7] = [0; 7];
        let mut buffer_len = 7;
        for shift in 0..7 {
            let char_byte = (val >> (8 * (shift + 1)) & 0xff) as u8;
            buffer[shift] = char_byte as u8;
            if char_byte == 0 {
                buffer_len = shift;
                break;
            }
        }

        String::from_utf8(buffer[0..buffer_len].to_vec()).unwrap_or(String::from("***ERR***"))
    }

    #[inline]
    pub fn encode_symbol_name(name: &str) -> (u64, &[u8]) {
        let mut result = 0b0010_u64; // starting with a short number, for now
        let byte_representation = name.as_bytes();
        if byte_representation.len() > 7 {
            unimplemented!()
        }

        for (idx, b) in byte_representation[0..min(7, byte_representation.len())]
            .iter()
            .enumerate()
        {
            result |= (*b as u64) << (idx + 1) * 8;
        }

        (result, &[])
    }

    pub fn deallocate(&mut self) {
        self.car |= 0b1;
        self.cdr |= 0b1;
    }

    pub fn is_deallocated(&self) -> bool {
        self.car & 0b1 == 0b1 && self.cdr & 0b1 == 0b1
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::cell::Cell;

    #[test]
    fn set_cell_pointer() {
        let mut cell = Cell::empty();
        cell.set_cdr_pointer(12345);
        assert_eq!(cell.cdr, (12345 as u64) << 4);
    }
}

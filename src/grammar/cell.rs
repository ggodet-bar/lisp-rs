use crate::grammar::util::{as_number, is_number, is_symbol_ptr, ptr};
use std::cmp::min;
use std::fmt::{Debug, Formatter};

#[derive(Clone, PartialEq)]
pub struct Cell {
    pub car: u64,
    pub cdr: u64,
}

impl Debug for Cell {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_list() {
            let val = if is_symbol_ptr(self.car) {
                format!("SymbolPtr:[{}]", self.car_ptr())
            } else {
                let number_prefix = if self.is_number() {
                    format!("Num[{}] | ", self.as_number())
                } else {
                    "".to_string()
                };
                format!(
                    "Cell{{{}Raw[{}] | ASCII[{}]}}",
                    number_prefix,
                    self.car,
                    Cell::decode_symbol_name(self.car)
                )
            };
            f.write_fmt(format_args!("Cell[List {}, next: {}]", val, self.cdr_ptr()))
        } else {
            let car_str = if is_number(self.car) {
                format!(
                    "Num[{}] | Raw[{}] | ASCII[{}]",
                    as_number(self.car),
                    self.car,
                    Cell::decode_symbol_name(self.car)
                )
            } else if is_symbol_ptr(self.car) {
                format!("SymbolPtr:[{}]", self.car_ptr())
            } else {
                self.car.to_string()
            };
            let cdr_str = if is_number(self.cdr) {
                format!(
                    "Num[{}] | Raw[{}] | ASCII[{}]",
                    as_number(self.cdr),
                    self.cdr,
                    Cell::decode_symbol_name(self.cdr)
                )
            } else if is_symbol_ptr(self.cdr) {
                format!("SymbolPtr:[{}]", self.cdr_ptr())
            } else {
                self.cdr.to_string()
            };
            f.write_fmt(format_args!("Cell{{car: {}, cdr: {}}}", car_str, cdr_str))
        }
    }
}

impl Cell {
    pub fn empty() -> Self {
        Self { car: 0, cdr: 0 }
    }

    pub fn is_nil(&self) -> bool {
        self.car == Cell::encode_symbol_name("nil").0 && self.cdr == 0 // by convention nil is the first entry, so its addr is 0
    }

    pub fn is_list(&self) -> bool {
        self.cdr & 0b1110 == 0 // CDR is a pointer
    }

    pub fn is_number(&self) -> bool {
        // FIXME Won't take big numbers into account, would need the env
        is_number(self.car)
    }

    pub fn as_number(&self) -> i64 {
        as_number(self.car)
    }

    pub fn set_car_pointer(&mut self, raw_addr: usize) {
        self.car = (raw_addr as u64) << 4;
    }

    pub fn set_cdr_pointer(&mut self, raw_addr: usize) {
        self.cdr = (raw_addr as u64) << 4;
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

        (
            result,
            &[]
            // if byte_representation.len() > 8 {
            //     &byte_representation[8..]
            // } else {
            //     &[]
            // },
        )
    }
}

pub fn is_number(val: u64) -> bool {
    val & 0b10 > 0
}

pub fn as_number(val: u64) -> i64 {
    // FIXME Naive implementation, won't take big numbers into account
    (val >> 4) as i64 * if val & 0b1000 > 0 { -1 } else { 1 }
}

pub fn is_symbol_ptr(val: u64) -> bool {
    val & 0b1110 == 0b1000
}

pub fn is_pointer(val: u64) -> bool {
    val & 0b0110 == 0
}

pub fn ptr(val: u64) -> usize {
    if !is_pointer(val) {
        panic!("Not a pointer: {:#b}!", val);
    }

    (val >> 4) as usize
}

pub fn number_pointer(payload: u64, sign: bool) -> u64 {
    let sign_bit = if sign { 0b1000 } else { 0b0000 };
    payload << 4 | sign_bit | 0b010
}

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

pub fn number_pointer(payload: i64) -> u64 {
    let sign_bit = if payload < 0 { 0b1000 } else { 0b0000 };
    (payload.abs() as u64) << 4 | sign_bit | 0b010
}

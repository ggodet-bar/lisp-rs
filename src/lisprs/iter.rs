use crate::lisprs::lisp_env::BorrowedCell;
use crate::lisprs::util::ptr;
use std::iter::Iterator;

pub struct CellIter<'a> {
    pub(crate) next_cell_ptr: Option<u64>,
    pub(crate) root_cell: BorrowedCell<'a>,
}

impl<'a> Iterator for CellIter<'a> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next_cell_ptr) = self.next_cell_ptr.as_mut() {
            if *next_cell_ptr == 0 {
                return None;
            }
            let new_cell = &self.root_cell.inner_ref.mem[ptr(*next_cell_ptr)];
            *next_cell_ptr = new_cell.cdr;
            Some(new_cell.car)
        } else {
            self.next_cell_ptr = Some(self.root_cell.cell.cdr);
            Some(self.root_cell.cell.car)
        }
    }
}

pub struct CellSlotIter<'a> {
    pub(crate) next_cell_ptr: Option<u64>,
    pub(crate) root_cell: BorrowedCell<'a>,
}

impl<'a> Iterator for CellSlotIter<'a> {
    type Item = (u64, u64); // second value is the cell slot ptr

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next_cell_ptr) = self.next_cell_ptr.as_mut() {
            if *next_cell_ptr == 0 {
                return None;
            }
            let new_cell = &self.root_cell.inner_ref.mem[ptr(*next_cell_ptr)];
            *next_cell_ptr = new_cell.cdr;
            Some((new_cell.car, *next_cell_ptr))
        } else {
            self.next_cell_ptr = Some(self.root_cell.cell.cdr);
            Some((self.root_cell.cell.car, self.root_cell.cell.cdr))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lisprs::util::{as_number, ptr};
    use crate::lisprs::LispEnv;

    #[test]
    fn over_basic_list() {
        let mut env = LispEnv::new();
        let program = env.parse("(1 2 3 4)").unwrap();
        let list_ptr = env.memory.borrow_mem(program).cell.car;
        let list_cell = env.memory.borrow_mem(ptr(list_ptr));

        let cell_values = list_cell
            .iter()
            .map(|car| as_number(car))
            .collect::<Vec<i64>>();
        assert_eq!([1_i64, 2_i64, 3_i64, 4_i64].to_vec(), cell_values);
    }

    #[test]
    fn over_nested_lists() {
        let mut env = LispEnv::new();
        let program = env.parse("(1 2 (3 2 1) (4 5 6) 7)").unwrap();
        let list_ptr = env.memory.borrow_mem(program).cell.car;
        let list_cell = env.memory.borrow_mem(ptr(list_ptr));

        assert_eq!(5, list_cell.iter().count());
    }
}

use crate::lisprs::cell::Cell;
use crate::lisprs::util::ptr;
use crate::lisprs::LispEnv;
use std::iter::Iterator;

pub struct CellIter<'a> {
    next_cell_ptr: Option<u64>,
    root_cell: &'a Cell,
    env: &'a LispEnv,
}

impl<'a> Iterator for CellIter<'a> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next_cell_ptr) = self.next_cell_ptr.as_mut() {
            if *next_cell_ptr == 0 {
                return None;
            }
            let new_cell = &self.env.memory.borrow()[ptr(dbg!(*next_cell_ptr))];
            *next_cell_ptr = new_cell.cdr;
            Some(new_cell.car)
        } else {
            self.next_cell_ptr = Some(dbg!(self.root_cell.cdr));
            Some(self.root_cell.car)
        }
    }
}

impl Cell {
    pub fn iter<'a>(&'a self, lisp_env: &'a LispEnv) -> CellIter<'a> {
        CellIter {
            next_cell_ptr: None,
            root_cell: &self,
            env: lisp_env,
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
        let list_ptr = env.memory.borrow()[program].car;
        let list_cell = &env.memory.borrow()[ptr(list_ptr)];

        let cell_values = list_cell
            .iter(&env)
            .map(|car| as_number(car))
            .collect::<Vec<i64>>();
        assert_eq!([1_i64, 2_i64, 3_i64, 4_i64].to_vec(), cell_values);
    }

    #[test]
    fn over_nested_lists() {
        let mut env = LispEnv::new();
        let program = env.parse("(1 2 (3 2 1) (4 5 6) 7)").unwrap();
        let list_ptr = env.memory.borrow()[program].car;
        let list_cell = &env.memory.borrow()[ptr(list_ptr)];

        assert_eq!(5, list_cell.iter(&env).count());
    }
}

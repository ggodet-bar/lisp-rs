use crate::lisprs::iter::{CellIter, CellSlotIter};
use crate::lisprs::util::ptr;
use crate::lisprs::LispEnv;

pub struct List<'a> {
    ptr: u64,
    env: &'a LispEnv,
}

impl<'a> List<'a> {
    pub fn as_list(ptr: u64, env: &'a LispEnv) -> Self {
        Self { ptr, env }
    }

    pub fn iter(&self) -> CellIter {
        CellIter {
            next_cell_ptr: None,
            root_cell: self.env.memory.borrow()[ptr(self.ptr)].clone(),
            env: self.env,
        }
    }

    pub fn iter_slots(&self) -> CellSlotIter {
        CellSlotIter {
            next_cell_ptr: None,
            root_cell: self.env.memory.borrow()[ptr(self.ptr)].clone(),
            env: self.env,
        }
    }
}

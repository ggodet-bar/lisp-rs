use crate::lisprs::lisp_env::LispFunction;
use crate::lisprs::util::as_ptr;
use crate::lisprs::LispEnv;

pub struct Quote;

impl LispFunction for Quote {
    fn symbol(&self) -> String {
        "quote".to_string()
    }

    fn function(
        &self,
        args_idx: usize,
        _env: &LispEnv,
    ) -> Result<u64, super::super::evaluator::Error> {
        Ok(as_ptr(args_idx))
    }
}

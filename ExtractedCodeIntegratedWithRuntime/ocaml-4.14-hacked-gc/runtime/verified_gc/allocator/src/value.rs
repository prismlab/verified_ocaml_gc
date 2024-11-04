use std::{
    fmt::{self, Debug},
    ops::Deref,
};

use crate::{
    bp_val,
    colors::BLUE,
    hd_bp,
    header::Header,
    utils::{field_val, get_next, next_in_mem},
};

pub const VAL_NULL: Value = Value(0);

#[derive(PartialEq, Eq, PartialOrd, Clone, Copy)]
#[repr(transparent)]
pub struct Value(pub usize);

impl Value {
    pub fn get_header(&self) -> &mut Header {
        #[cfg(debug_assertions)]
        assert_ne!(*self, VAL_NULL, "Value is null, can't get header");

        let f = field_val(*self, -1);
        let bp = Value(bp_val!(f) as usize);
        hd_bp!(bp.0 as *mut u8)
    }

    // Just performs pointer addition
    pub fn get_next_from_size(&self) -> Value {
        next_in_mem(self)
    }

    pub fn is_ptr(&self) -> bool {
        self.0 & 1usize == 0usize
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == VAL_NULL {
            f.debug_struct("Value").field("val", &"null").finish()
        } else {
            f.debug_struct("Value")
                .field("val", &self.0)
                .field("next", &{
                    if self.get_header().get_color() == BLUE {
                        format!("{:?}", get_next(self).0)
                    } else {
                        "[NA]This Value is NotFree".to_string()
                    }
                })
                .field("header", &self.get_header())
                .finish()
        }
    }
}

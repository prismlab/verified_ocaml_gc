use crate::{header::Header, value::Value, word::Wsize};

// Pool is a circular linked list(Doubly Linked List)
#[repr(C)]
#[derive(Debug)]
pub struct Pool {
    pub(super) pool_wo_sz: Wsize,
    pub(super) prev: *mut Pool,
    pub(super) next: *mut Pool,
    pub(super) filler: Value,
    pub(super) hd: Header,
    pub(super) first_field: Value,
}

impl Pool {
    //
    pub fn get_header_size_from_pool_wo_sz(pool_wo_sz: Wsize) -> Wsize {
        pool_wo_sz - Wsize::from_bytesize(std::mem::size_of::<Pool>()) + Wsize::new(1)
    }

    pub fn insert_right_after_left(left: *mut Pool, right: *mut Pool) {
        unsafe {
            let cur_left_next = (*left).next;
            (*right).next = cur_left_next;
            (*cur_left_next).prev = right;
            (*right).prev = left;
            (*left).next = right;
        }
    }
    pub fn get_next_raw(&self) -> *mut Pool {
        self.next
    }
    pub fn get_prev_raw(&self) -> *mut Pool {
        self.prev
    }

    pub fn get_next_raw_from_raw(ptr: &*mut Pool) -> *mut Pool {
        unsafe { (**ptr).get_next_raw() }
    }
    pub fn get_prev_raw_from_raw(ptr: &*mut Pool) -> *mut Pool {
        unsafe { (**ptr).get_prev_raw() }
    }
    pub fn get_range(&self) -> (usize, usize) {
        let first_out_of_range_value =
            std::ptr::addr_of!(*self) as usize + self.pool_wo_sz.to_bytesize();
        let first_header = std::ptr::addr_of!(self.hd) as usize;
        (first_header, first_out_of_range_value)
    }
}

pub struct PoolIter<'a> {
    start: *mut Pool,
    cur_pool: &'a mut Pool,
}

impl<'a> PoolIter<'a> {
    pub fn new(head_pool: &*mut Pool) -> Self {
        Self {
            start: *head_pool,
            cur_pool: unsafe { &mut **head_pool },
        }
    }
}

pub struct PoolIterVal(*mut Pool);
impl PoolIterVal {
    pub fn get_pool_mut(&mut self) -> &mut Pool {
        unsafe { &mut *self.0 }
    }
    pub fn get_pool(&self) -> &Pool {
        unsafe { &*self.0 }
    }
}

impl Iterator for PoolIter<'_> {
    type Item = PoolIterVal;
    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.cur_pool.next {
            return None;
        }
        let next = self.cur_pool.next;
        self.cur_pool = unsafe { &mut *next };
        Some(PoolIterVal(next))
    }
}

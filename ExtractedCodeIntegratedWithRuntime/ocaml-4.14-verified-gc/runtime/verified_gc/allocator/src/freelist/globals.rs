use std::sync::Once;

use crate::{
    colors::BLUE,
    freelist::pool::Pool,
    header::Header,
    utils::val_bp,
    value::{Value, VAL_NULL},
    word::Wsize,
};

#[repr(C)]
pub struct SentinelType {
    pub(super) filler1: Value,
    pub(super) h: Header,
    pub(super) first_field: Value,
    pub(super) filler2: Value,
}

static mut SENTINEL: SentinelType = SentinelType {
    filler1: Value(0),
    h: Header::new(1, BLUE, 0),
    first_field: VAL_NULL,
    filler2: Value(0),
};

#[derive(Debug)]
#[repr(C)]
pub struct NfGlobals {
    // this will always have the total words in freelist
    pub(super) cur_wsz: Wsize,
    // this always points to one value throughout the
    // program(SENTINEL.first_field specifically)
    pub(super) nf_head: Value,
    // keeps track of point where we last left off, this is what makes next fit next fit
    pub(super) nf_prev: Value,

    // always points to the last free block inside alloc function(after one call to one
    // nf_expand_heap though). This can be assumed in all the exposed functions
    // Internally it can sometimes point to VAL_NULL as well, but that gets fixed in next fit
    // iteration which reaches NULL once, the value whose next value is NULL is nf_last
    //
    // After sweep, nf_last may end up pointing to VAL_NULL. But in alloc, since we anyway have to
    // iterate over the free list, we'll end up assigning nf_last properly anyway. At the time of
    // need, get_next(nf_last) will always be a valid call basically
    pub(super) nf_last: Value,

    // Points to the pool head(will be some global variable's address). This one will never change
    // value. The actual pools will be added via calls to nf_expand_heap
    pub(super) pool_head: *mut Pool,
    // Doing get_next on this nf_head, nf_prev and nf_head should always be valid, this is to be maintained
}

impl NfGlobals {
    #[inline(always)]
    pub fn get() -> &'static mut Self {
        static mut FIRST_POOL: Pool = Pool {
            pool_wo_sz: Wsize::new(0),
            prev: std::ptr::null_mut(),
            next: std::ptr::null_mut(),
            filler: Value(0),
            hd: Header::new(0, BLUE, 0),
            first_field: Value(0),
        };
        static mut NF_GLOBAL: NfGlobals = NfGlobals {
            cur_wsz: Wsize::new(0),
            nf_head: Value(0),
            nf_prev: Value(0),
            nf_last: Value(0),
            pool_head: std::ptr::null_mut(),
        };
        static ONCE: Once = Once::new();

        ONCE.call_once(|| {
            unsafe {
                // Circular linked list invariant
                FIRST_POOL.next = std::ptr::addr_of_mut!(FIRST_POOL);
                FIRST_POOL.prev = FIRST_POOL.next;

                NF_GLOBAL.nf_head = val_bp(std::ptr::addr_of_mut!(SENTINEL.first_field) as *mut u8);
                NF_GLOBAL.nf_last = NF_GLOBAL.nf_head;
                NF_GLOBAL.nf_prev = NF_GLOBAL.nf_head;
                NF_GLOBAL.pool_head = FIRST_POOL.next;
            };
        });

        unsafe { &mut NF_GLOBAL }
    }
}

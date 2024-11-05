#![allow(clippy::mut_from_ref)]
mod colors;
mod freelist;
mod header;
mod mark;
mod utils;
mod value;
mod word;

use std::sync::Once;

use freelist::allocator::{get_global_allocator, AllocatorStats};
use mark::Marker;
use utils::field_val;
use value::{Value, VAL_NULL};
use word::Wsize;

pub const DEFAULT_COLOR: colors::Color = colors::BLUE;
pub const DEFAULT_TAG: u8 = 0;

#[cfg(debug_assertions)]
static mut MEM_RANGES: Vec<(usize, usize)> = vec![];

#[repr(C)]
#[derive(Clone)]
pub struct HeapRange {
    pub first_header: usize,
    pub rightmost_value: usize,
}

#[no_mangle]
pub extern "C" fn alloc(wo_sz: std::ffi::c_ulonglong) -> *mut u8 {
    let mut mem = get_global_allocator().nf_allocate(Wsize::new(wo_sz as usize));

    #[cfg(feature = "check_invariants")]
    get_global_allocator().verify_nf_last_invariant();
    #[cfg(feature = "no_expand_heap")]
    if get_global_allocator().get_num_of_expansions() == 1 {
        return field_val(Value(mem as usize), 1).0 as *mut u8;
    }

    if Value(mem as usize) == VAL_NULL {
        // add new block and allocate
        get_global_allocator().nf_expand_heap(Wsize::new(wo_sz as usize));

        #[cfg(debug_assertions)]
        unsafe {
            MEM_RANGES.push(get_global_allocator().get_start_end_after_heap_expand());
        }

        mem = get_global_allocator().nf_allocate(Wsize::new(wo_sz as usize));
    }

    #[cfg(feature = "check_invariants")]
    get_global_allocator().verify_nf_last_invariant();

    field_val(Value(mem as usize), 1).0 as *mut u8
}

#[no_mangle]
pub extern "C" fn dealloc(bp: *mut u8) {
    let val_bp = Value(bp as usize);
    let hd_bp = field_val(Value(bp as usize), -1);

    if hd_bp == VAL_NULL {
        return;
    }

    #[cfg(debug_assertions)]
    {
        let bp_as_usize = bp as usize;
        if !unsafe { &MEM_RANGES }
            .iter()
            .any(|r| r.0 <= bp_as_usize && bp_as_usize <= r.1)
        {
            panic!(
                "Invalid Memory, Got mem address: {}\n Valid memory addresses: {:?}",
                bp_as_usize,
                unsafe { &MEM_RANGES }
            );
        }
    }

    get_global_allocator().nf_deallocate(val_bp);

    #[cfg(feature = "check_invariants")]
    get_global_allocator().verify_nf_last_invariant();
}

#[no_mangle]
pub extern "C" fn sweep() {
    get_global_allocator().nf_sweep();
}

#[no_mangle]
pub extern "C" fn get_heap_range() -> HeapRange {
    #[cfg(feature = "no_expand_heap")]
    {
        let ranges = get_global_allocator()
            .get_pool_iter()
            .map(|p| {
                let pool = p.get_pool();
                let range = pool.get_range();
                HeapRange {
                    first_header: range.0,
                    rightmost_value: range.1,
                }
            })
            .collect::<Vec<HeapRange>>();
        return ranges.get(0).unwrap().clone();
    }
    panic!("Not implemented for multiple pools")
}

#[no_mangle]
pub extern "C" fn get_freelist_head() -> usize {
    get_global_allocator().get_nf_head().0
}

#[no_mangle]
pub extern "C" fn get_allocator_stats() -> AllocatorStats {
    get_global_allocator().get_stats()
}

#[no_mangle]
pub extern "C" fn mark(val: Value) {
    static mut GLOBAL_MARKER: Marker = Marker { stack: vec![] };
    static ONCE: Once = Once::new();

    ONCE.call_once(|| {
        unsafe {
            GLOBAL_MARKER = Marker::new(Some(get_allocator_stats().min_expansion_wsz));
        };
    });
    unsafe {
        GLOBAL_MARKER.mark(val);
    }
}

#[cfg(test)]
mod tests {

    use crate::{
        alloc, dealloc,
        freelist::{allocator::get_global_allocator, fl::FreeList},
        utils::whsize_wosize,
    };

    #[test]
    fn tests() {
        // 1st allocation
        let req1: usize = 1024 * 8;
        let allocd_mem1 = alloc(req1 as u64);
        assert_ne!(allocd_mem1, std::ptr::null_mut());
        // traverse_fl(|v| println!("{:?}", v));
        assert_eq!(
            FreeList::new(get_global_allocator().get_globals_mut())
                .nf_iter()
                .count(),
            1
        );

        let total_sz_after_1_alloc: usize = FreeList::new(get_global_allocator().get_globals_mut())
            .nf_iter()
            .map(|v| *whsize_wosize(v.get_cur().get_header().get_wosize()).get_val())
            .sum();

        // Still 1, because we caused a split in free list
        assert_eq!(
            FreeList::new(get_global_allocator().get_globals_mut())
                .nf_iter()
                .count(),
            1
        );

        assert_eq!(
            FreeList::new(get_global_allocator().get_globals_mut())
                .nf_iter()
                .map(|v| *whsize_wosize(v.get_cur().get_header().get_wosize()).get_val())
                .sum::<usize>(),
            total_sz_after_1_alloc
        );

        // 2nd allocation
        let req2 = 1024;
        let allocd_mem2 = alloc(req2 as u64);
        assert_ne!(allocd_mem2, std::ptr::null_mut());

        assert_eq!(
            FreeList::new(get_global_allocator().get_globals_mut())
                .nf_iter()
                .map(|v| *whsize_wosize(v.get_cur().get_header().get_wosize()).get_val())
                .sum::<usize>(),
            total_sz_after_1_alloc - (req2 + 1)
        );

        // Freeing both

        dealloc(allocd_mem1);

        // The allocd_mem2 is missing for the merge to happen
        assert_eq!(
            FreeList::new(get_global_allocator().get_globals_mut())
                .nf_iter()
                .count(),
            2
        );

        dealloc(allocd_mem2);

        // Should be 1 now, due to merge
        assert_eq!(
            FreeList::new(get_global_allocator().get_globals_mut())
                .nf_iter()
                .count(),
            1
        );

        // //since it's first fit this should pass
        // assert_eq!(alloc(256 * 1024), alloc_mem);
    }
}

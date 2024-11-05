pub mod allocator;
pub mod fl;
mod globals;
pub mod pool;

#[cfg(test)]
mod tests {
    use crate::{
        colors::{BLACK, BLUE, WHITE},
        freelist::pool::Pool,
        header::Header,
        pool_val,
        utils::{self, field_val, whsize_wosize},
        val_hp,
        value::{Value, VAL_NULL},
        word::Wsize,
        DEFAULT_TAG,
    };

    use super::{allocator::NfAllocator, fl::FreeList};

    #[test]
    fn allocate_for_heap_expansion_test() {
        let request_wo_sz = 1024;
        let layout = utils::get_layout(Wsize::new(request_wo_sz));
        let memory = NfAllocator::allocate_for_heap_expansion(&layout);
        assert_eq!(
            memory.get_header().get_wosize(),
            Pool::get_header_size_from_pool_wo_sz(Wsize::new(request_wo_sz))
        );

        assert_eq!(memory.get_header().get_color(), BLUE);
        assert_eq!(
            pool_val!(memory).pool_wo_sz,
            Wsize::from_bytesize(layout.size())
        );

        unsafe { std::alloc::dealloc(pool_val!(memory) as *mut Pool as *mut u8, layout) };
    }

    #[test]
    fn test() {
        let mut allocator = NfAllocator::new();

        // nothing present in freelist
        assert!(FreeList::new(allocator.get_globals_mut()).nf_iter().count() == 0);

        let intended_expansion_size = Wsize::new(1024 * 1024); // Expand the heap with a chunk of size
                                                               // 1024*1024 words i.e (1024**2) *
                                                               // WORD_SIZE bytes

        let (layout, _actual_expansion_size) =
            utils::get_layout_and_actual_expansion_size(intended_expansion_size);

        let actual_expansion_size = Wsize::from_bytesize(layout.size());

        // no pool block is there, there's only the one which is fixed and is not used in iter
        assert_eq!(allocator.get_pool_iter().count(), 0);

        // nf_expand_heap heap will actually allocate for size=actual_expansion_size instead of
        // intended_expansion_size
        allocator.nf_expand_heap(intended_expansion_size);

        let pool_leader_wsz =
            whsize_wosize(Pool::get_header_size_from_pool_wo_sz(actual_expansion_size));
        assert_eq!(allocator.get_globals_mut().cur_wsz, pool_leader_wsz,);

        // 1 chunk is present in freelist after expansion
        assert_eq!(
            FreeList::new(allocator.get_globals_mut()).nf_iter().count(),
            1
        );

        // 1 pool block has been added as well
        assert_eq!(allocator.get_pool_iter().count(), 1);
        // this asserts invariant [ pool list being sorted]
        allocator.check_pool_list_invariant();

        let mut allocations = vec![
            Some(allocator.nf_allocate(Wsize::new(1024))), // allocates 1024 + 1 word
            Some(allocator.nf_allocate(Wsize::new(1024))), // allocates 1024 + 1 word
        ];

        // initial size -(1024 + 1 word( ret by whsize_wosize) allocated twice)
        let cur_wsz = pool_leader_wsz - ((whsize_wosize(Wsize::new(1024))) * 2);

        assert_eq!(allocator.get_globals().cur_wsz, cur_wsz);

        let to_be_freed = allocations.get_mut(0).unwrap().take().unwrap();
        assert!(allocations.get(0).unwrap().is_none());

        let allocatable_memory_left = FreeList::new(allocator.get_globals_mut())
            .nf_iter()
            .fold(Wsize::new(0), |acc, x| {
                acc + x.get_cur().get_header().get_wosize()
            });

        //The following allocation will force the empty block case in nf_allocate_block
        let hp = allocator.nf_allocate(allocatable_memory_left - Wsize::new(1));

        assert_eq!(
            val_hp!(hp).get_header().get_wosize(),
            allocatable_memory_left - Wsize::new(1)
        );
        //Assert the size of empty block that lies 1 word before hp
        assert_eq!(
            Value(hp as usize).get_header().get_wosize(), // treat hp as val, it'll treat empty
            // block as it's header
            Wsize::new(0)
        );
        allocations.push(Some(hp));

        // This must've made the free list empty
        assert_eq!(allocator.get_globals().cur_wsz, Wsize::new(0));
        assert_eq!(
            FreeList::new(allocator.get_globals_mut())
                .nf_iter()
                .fold(Wsize::new(0), |acc, x| {
                    acc + x.get_cur().get_header().get_wosize()
                }),
            Wsize::new(0)
        );
        assert_eq!(
            FreeList::new(allocator.get_globals_mut()).nf_iter().count(),
            0
        );

        // Freeing the first allocation
        let to_be_freed_header = val_hp!(to_be_freed).get_header().clone();
        allocator.nf_deallocate(val_hp!(to_be_freed));

        assert_eq!(
            allocator.get_globals().cur_wsz,
            to_be_freed_header.get_wosize() + Wsize::new(1)
        );

        let allocatable_memory_left = to_be_freed_header.get_wosize();

        FreeList::new(allocator.get_globals_mut()).nf_iter().count();

        // Allocating exactly allocatable_memory_left will again empty the freelist
        let hp = allocator.nf_allocate(allocatable_memory_left);

        assert_ne!(hp, std::ptr::null_mut());
        assert_eq!(allocator.get_globals().cur_wsz, Wsize::new(0));
        assert_eq!(
            FreeList::new(allocator.get_globals_mut())
                .nf_iter()
                .fold(Wsize::new(0), |acc, x| {
                    acc + x.get_cur().get_header().get_wosize()
                }),
            Wsize::new(0)
        );

        // Calling nf_expand_heap one more time.
        // Currently there's one pool block and free list is empty

        allocator.nf_expand_heap(intended_expansion_size);

        assert_eq!(
            FreeList::new(allocator.get_globals_mut()).nf_iter().count(),
            1
        );
        assert_eq!(allocator.get_globals().cur_wsz, pool_leader_wsz);

        assert_eq!(allocator.get_pool_iter().count(), 2);
        allocator.check_pool_list_invariant();

        let mut pool_block_count = 2;
        let mut freelist_node_count = 1;
        // checking the pool invariant 10 more times
        for i in 1..=10 {
            pool_block_count += 1;
            freelist_node_count += 1;
            allocator.nf_expand_heap(intended_expansion_size);
            assert_eq!(
                FreeList::new(allocator.get_globals_mut()).nf_iter().count(),
                freelist_node_count
            );
            assert_eq!(allocator.get_globals().cur_wsz, pool_leader_wsz * (i + 1));

            assert_eq!(allocator.get_pool_iter().count(), pool_block_count);
            allocator.check_pool_list_invariant();
        }
    }

    #[test]
    fn sweep_test() {
        let mut allocator = NfAllocator::new();
        let _ = allocator.nf_expand_heap(Wsize::new(10)); // This'll add a new pool,
                                                          // $MIN_EXPANSION_WORSIZE  words will be
                                                          // malloc'd

        let initial_cur_wsz = allocator.get_globals().cur_wsz;
        // Allocation 1
        let mut allocation_sizes = vec![];
        let mut allocated_values = vec![];
        let hp = allocator.nf_allocate(Wsize::new(10));

        assert_ne!(hp, std::ptr::null_mut());
        allocation_sizes.push(Wsize::new(10));
        let mem = val_hp!(hp);
        assert_eq!(mem.get_header().get_color(), WHITE);
        allocated_values.push(mem);

        // Allocation 2
        let hp = allocator.nf_allocate(Wsize::new(20));
        assert_ne!(hp, std::ptr::null_mut());
        allocation_sizes.push(Wsize::new(20));
        let mem = val_hp!(hp);
        assert_eq!(mem.get_header().get_color(), WHITE);
        allocated_values.push(mem);

        let wsz_not_in_fl = allocation_sizes
            .iter()
            .map(|x| whsize_wosize(*x))
            .fold(Wsize::new(0), |acc, e| acc + e);

        assert_eq!(
            FreeList::new(allocator.get_globals_mut()).nf_iter().count(),
            1
        );
        assert_eq!(
            allocator.get_globals().cur_wsz,
            initial_cur_wsz - wsz_not_in_fl
        );

        // This marks all the allocated values as unreachable
        for val in allocated_values {
            *val.get_header() =
                Header::new(*val.get_header().get_wosize().get_val(), WHITE, DEFAULT_TAG);
        }

        allocator.nf_sweep();

        assert_eq!(
            FreeList::new(allocator.get_globals_mut()).nf_iter().count(),
            1
        );
        assert_eq!(allocator.get_globals().cur_wsz, initial_cur_wsz);

        // Preparing for 2nd sweep
        //
        // Allocating and marking some nodes white this time(not all of it)

        allocation_sizes = vec![];
        allocated_values = vec![];

        allocation_sizes.push(Wsize::new(20));
        allocation_sizes.push(Wsize::new(30));
        allocation_sizes.push(Wsize::new(40));
        allocation_sizes.push(Wsize::new(50));

        for sz in &allocation_sizes {
            let val = val_hp!(allocator.nf_allocate(*sz));
            let hd = val.get_header().clone();
            // Make all of them reachable initially
            *val.get_header() = Header::new(*hd.get_wosize().get_val(), BLACK, hd.get_tag());
            allocated_values.push(val);
        }

        assert_eq!(
            FreeList::new(allocator.get_globals_mut()).nf_iter().count(),
            1
        );
        // we'll mark two values as unreachable
        //
        // allocated_values[0] and allocated_values[2]

        let hd = allocated_values.get_mut(0).unwrap().get_header().clone();
        *allocated_values.get_mut(0).unwrap().get_header() =
            Header::new(*hd.get_wosize().get_val(), WHITE, hd.get_tag());

        let hd = allocated_values.get_mut(2).unwrap().get_header().clone();
        *allocated_values.get_mut(2).unwrap().get_header() =
            Header::new(*hd.get_wosize().get_val(), WHITE, hd.get_tag());

        allocator.nf_sweep();

        assert_eq!(
            FreeList::new(allocator.get_globals_mut()).nf_iter().count(),
            3
        );
        assert_eq!(
            allocator.get_globals().cur_wsz,
            initial_cur_wsz
                - whsize_wosize(*allocation_sizes.get(1).unwrap())
                - whsize_wosize(*allocation_sizes.get(3).unwrap())
        );

        // Heap right now is something like this
        // FFFF****FFFF****FFFF
        // where,
        // * -> Not Free
        // F -> Free
        //
        //let allocs = allocated_values vector
        //
        //
        // Freeing allocs[1] will make the free list something like this
        // FFFF****FFFFFFFFFF
        // It should force a merge
        // To free allocs[1], we'll make allocs[3] black,allocs[1] is already white after the last
        // sweep
        let hd = allocated_values.get_mut(3).unwrap().get_header().clone();
        *allocated_values.get_mut(3).unwrap().get_header() =
            Header::new(*hd.get_wosize().get_val(), BLACK, hd.get_tag());

        allocator.nf_sweep();

        assert_eq!(
            FreeList::new(allocator.get_globals_mut()).nf_iter().count(),
            2
        );
        assert_eq!(
            allocator.get_globals().cur_wsz,
            initial_cur_wsz - whsize_wosize(*allocation_sizes.get(3).unwrap())
        );

        let mut last = Value(0);
        for ele in FreeList::new(allocator.get_globals_mut()).nf_iter() {
            last = ele.get_cur();
        }

        // Manually changing the globals to test that nf_sweep assigns them properly
        allocator.get_globals_mut().nf_prev = last;
        allocator.get_globals_mut().nf_last = last;

        allocator.nf_sweep();
        assert_eq!(allocator.get_globals().nf_last, VAL_NULL);
        // nf_last will be fixed to correct value when we actually need it

        assert_eq!(
            FreeList::new(allocator.get_globals_mut()).nf_iter().count(),
            1
        );

        assert_eq!(allocator.get_globals().cur_wsz, initial_cur_wsz);
        let only_val_in_fl = FreeList::new(allocator.get_globals_mut())
            .nf_iter()
            .next()
            .unwrap()
            .get_cur();

        assert_eq!(allocator.get_globals().nf_prev, only_val_in_fl);
        assert_eq!(allocator.get_globals().nf_last, only_val_in_fl);
    }
}

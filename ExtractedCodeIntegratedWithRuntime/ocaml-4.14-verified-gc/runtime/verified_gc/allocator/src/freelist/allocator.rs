use std::alloc::Layout;

use crate::{
    bp_val,
    colors::{BLACK, BLUE, WHITE},
    freelist::{fl::FreeList, pool::Pool},
    hd_hp,
    header::Header,
    hp_val, pool_val,
    utils::{
        self, field_val, get_layout_and_actual_expansion_size, get_next, get_pool_mut, val_bp,
        whsize_wosize, wosize_whsize,
    },
    val_hp,
    value::{Value, VAL_NULL},
    word::Wsize,
    DEFAULT_TAG,
};

use super::{
    globals::{NfGlobals, SentinelType},
    pool::{PoolIter, PoolIterVal},
};

#[repr(C)]
pub struct AllocatorStats {
    pub cur_free_wsz: usize,
    pub total_wsz: usize,
    pub min_expansion_wsz: usize,
}

pub struct NfAllocator {
    globals: NfGlobals,
    #[cfg(debug_assertions)]
    last_expandheap_start_end: (usize, usize),
    num_of_heap_expansions: usize,
}

impl NfAllocator {
    pub fn new() -> Self {
        let sentinel = Box::leak(Box::new(SentinelType {
            filler1: Value(0),
            h: Header::new(0, BLUE, DEFAULT_TAG),
            first_field: VAL_NULL,
            filler2: Value(0),
        }));
        let sentinel_head = val_bp(std::ptr::addr_of_mut!(sentinel.first_field) as *mut u8);

        let pool = Box::leak(Box::new(Pool {
            pool_wo_sz: Wsize::new(0),
            prev: std::ptr::null_mut(),
            next: std::ptr::null_mut(),
            filler: Value(0),
            hd: Header::new(0, BLUE, DEFAULT_TAG),
            first_field: Value(0),
        }));

        let pool_addr = std::ptr::addr_of_mut!(*pool);
        // Circular linked list invariant
        pool.next = pool_addr;
        pool.prev = pool_addr;

        Self {
            globals: NfGlobals {
                cur_wsz: Wsize::new(0),
                nf_head: sentinel_head,
                nf_prev: sentinel_head,
                nf_last: sentinel_head,
                pool_head: pool_addr,
            },
            #[cfg(debug_assertions)]
            last_expandheap_start_end: (0usize, 0usize),
            num_of_heap_expansions: 0usize,
        }
    }

    pub fn get_pool_iter(&self) -> PoolIter {
        // at all times pool_head will point to valid pool(the global one with static lifetime or
        // the one gotten through Box::leak)
        PoolIter::new(&self.get_globals().pool_head)
    }

    #[inline(always)]
    pub fn get_globals_mut(&mut self) -> &mut NfGlobals {
        &mut self.globals
    }
    #[inline(always)]
    pub fn get_globals(&self) -> &NfGlobals {
        &self.globals
    }

    #[inline(always)]
    pub fn get_nf_head(&self) -> Value {
        self.globals.nf_head
    }

    #[inline(always)]
    #[cfg(debug_assertions)]
    pub fn get_start_end_after_heap_expand(&self) -> (usize, usize) {
        self.last_expandheap_start_end
    }

    #[inline(always)]
    pub fn get_num_of_expansions(&self) -> usize {
        self.num_of_heap_expansions
    }

    #[cfg(feature = "check_invariants")]
    fn check_nf_allocate_block_invariant(&mut self, prev: Value, cur: Value, wh_sz: Wsize) {
        assert!(
            (prev == self.get_globals().nf_head && cur == *get_next(&prev)) || (prev.0 < cur.0),
            "[nf_allocate_block] prev<cur invariant broken"
        );
        assert!(
            whsize_wosize(cur.get_header().get_wosize()) >= wh_sz,
            "The invariant(block size should be enough) to be maintained is broken. to_be_allocated block doesnt have enough size to satisfy the request."
        );
    }

    fn nf_allocate_block(&mut self, prev: Value, cur: Value, wh_sz: Wsize) -> *mut Header {
        let hd_sz = cur.get_header().get_wosize();

        #[cfg(feature = "check_invariants")]
        self.check_nf_allocate_block_invariant(prev, cur, wh_sz);

        if *cur.get_header().get_wosize().get_val() < (wh_sz.get_val() + 1) {
            // If we're here, the size of header is exactly wh_sz or wo_sz[=wosize_whsize(wh_sz)]
            // This is only ever called from nf_allocate, we will never be breaking this invariant.
            // So the size of header can only be these two values
            //
            // # equals wo_sz
            //
            // We'll change the header to size zero inside this branch. But later on before
            // returning,it's changed back to wo_sz(the requested size)
            //
            // # equals to wh_sz
            //
            // We'll change the header to have size 0 in this branch. The next header right after
            // it is what we must return. IMP: this must be handled while merging. Any value that
            // we get, it might be succeeding an empty block header,so that check must be made.
            //
            //
            // The reason we're setting the header here is so that we can actually merge it later.
            // If we dont keep track of this header's 0 size, we wont know it's useless later on
            // and it will forever create a gap which wont be merged.
            //

            self.get_globals_mut().cur_wsz -= whsize_wosize(cur.get_header().get_wosize());
            *get_next(&prev) = *get_next(&cur);

            cur.get_header().set_wosize(Wsize::new(0));
            cur.get_header().set_color(WHITE); // This will be overwritten if it
                                               // was given wrong header, else
                                               // this'll be the empty block(which
                                               // is rightly always
                                               // unreachable(WHITE))

            // If the pointer we returned was nf_last, we change nf_last
            // This way we're always keeping track of nf_last properly
            if cur == self.get_globals().nf_last {
                self.get_globals_mut().nf_last = prev;
                *get_next(&self.get_globals().nf_last) = VAL_NULL;
            }
        } else {
            self.get_globals_mut().cur_wsz -= wh_sz;
            *cur.get_header() = Header::new(
                cur.get_header().get_wosize().get_val() - wh_sz.get_val(),
                BLUE,
                DEFAULT_TAG,
            );
        }

        // since we always split and return the right half,we must calculate the offset at which we split.
        //
        // case wo_sz == hd_sz => -1, this causes the cur.get_header() to have right size
        //
        // case wh_sz == hd_sz => 0, empty block is already there, it'll put header for block to be
        // returned properly
        //
        // case hd_sz >= wh_sz + 1 => positive value, the split block will have proper header
        let offset = *hd_sz.get_val() as isize - *wh_sz.get_val() as isize;

        // Set the header for the memory that we'll be returning, IMP: Make it have WHITE color,
        // if it's reachable, it'll be made white by the  sweep
        let val = field_val(cur, offset + 1);
        val.get_header()
            .set_wosize(Wsize::new(*wosize_whsize(wh_sz).get_val()));
        val.get_header().set_color(WHITE);

        self.get_globals_mut().nf_prev = prev;

        field_val(cur, offset).0 as *mut Header
    }

    pub fn nf_allocate(&mut self, wo_sz: Wsize) -> *mut Header {
        assert!(*wo_sz.get_val() >= 1);
        let it = FreeList::new(self.get_globals_mut()).find_next(wo_sz);
        match it {
            None => VAL_NULL.0 as *mut Header,
            Some(it) => {
                self.nf_allocate_block(it.get_actual_prev(), it.get_cur(), whsize_wosize(wo_sz))
            }
        }
    }

    // We assume this never fails
    pub fn allocate_for_heap_expansion(request_layout: &Layout) -> Value {
        let no_of_bytes_in_layout = request_layout.size();
        let no_of_words_in_layout = Wsize::from_bytesize(no_of_bytes_in_layout);

        // Assuming this'll never fail
        let mut mem_hd = unsafe {
            let mem = std::alloc::alloc_zeroed(*request_layout);
            #[cfg(debug_assertions)]
            {
                Self::mem_write(
                    mem as *mut Header,
                    *no_of_words_in_layout.get_val(),
                    Header::new(0, BLUE, DEFAULT_TAG),
                );
            }
            mem as *mut u8
        };
        // let mut mem_hd = unsafe { std::alloc::alloc_zeroed(*request_layout) };

        #[cfg(feature = "check_invariants")]
        assert_ne!(
            mem_hd,
            std::ptr::null_mut(),
            "Heap expansion never failing invariant failed"
        );

        let pool = get_pool_mut(&mut mem_hd);
        pool.pool_wo_sz = no_of_words_in_layout;
        pool.next = std::ptr::addr_of_mut!(*pool);
        pool.prev = std::ptr::addr_of_mut!(*pool);
        pool.hd = Header::new(
            // Should have size = no_of_words_in_layout - sizeof(Pool) + 1 word(considering the first_field field)
            *Pool::get_header_size_from_pool_wo_sz(no_of_words_in_layout).get_val(),
            BLUE,
            DEFAULT_TAG,
        );

        // field_val(val_bp(mem_hd), 4) would also work, it's guaranteed to be at  4th index since
        // we're using repr(C)
        Value(std::ptr::addr_of_mut!(pool.first_field) as usize)
    }

    pub fn nf_expand_heap(&mut self, request_wo_sz: Wsize) {
        let (layout, _) = utils::get_layout_and_actual_expansion_size(request_wo_sz);

        let memory = Self::allocate_for_heap_expansion(&layout);

        #[cfg(debug_assertions)]
        {
            let hp_as_usize = field_val(memory, -1).0;
            self.last_expandheap_start_end = (
                hp_as_usize,
                hp_as_usize + memory.get_header().get_wosize().to_bytesize(),
            );
        }

        self.num_of_heap_expansions += 1;

        // self.nf_add_block(field_val(mem_hd_val, 1));
        self.nf_add_pool(pool_val!(memory));

        #[cfg(feature = "check_invariants")]
        self.check_pool_list_invariant();

        self.nf_add_block(memory)
    }

    pub fn check_pool_list_invariant(&mut self) {
        let head_next_raw = Pool::get_next_raw_from_raw(&self.get_globals().pool_head);
        let head_prev_raw = Pool::get_prev_raw_from_raw(&self.get_globals().pool_head);

        assert_eq!(
            Pool::get_next_raw_from_raw(&head_prev_raw),
            self.get_globals().pool_head
        );
        assert_eq!(
            Pool::get_prev_raw_from_raw(&head_next_raw),
            self.get_globals().pool_head
        );

        let mut prev = head_next_raw;
        assert!(
            self.get_pool_iter().skip(1).all(|mut x| {
                let cur_ptr = std::ptr::addr_of_mut!(*x.get_pool_mut());
                let res = prev < cur_ptr;
                let next = Pool::get_next_raw_from_raw(&cur_ptr);
                assert_eq!(
                    Pool::get_next_raw_from_raw(&prev),
                    cur_ptr,
                    "Linking pools not done correctly"
                );
                assert_eq!(
                    Pool::get_prev_raw_from_raw(&next),
                    cur_ptr,
                    "Linking pools not done correctly"
                );
                prev = cur_ptr;
                res
            }),
            "Pool pointers laid out in sorted order invariant broken",
        );
    }

    fn nf_add_pool(&mut self, pool: &mut Pool) {
        let this_pool_addr = std::ptr::addr_of_mut!(*pool);

        // CASES possible
        // 1) There's just the pool_head in pool. It'll be pointing to itself
        //      1.i) If the pointer value of pool_head is greater than the
        //      this_pool_addr pointer, it'll be inserted after the pool_head correctly, via
        //      B1 branch
        //      1.ii) If the pointer value of pool head is less than this_pool_addr pointer,
        //      It'll go B3 branch and we'll insert it correctly there
        //  2) If there's some other pools apart from pool_head
        //      2.i) B1 will handle the case correctly
        //      2.ii) B2 will handle the cases of inserting to somewhere in between and at the end
        //        as well
        //      2.iii) B3 should never hit in this particular case
        //
        //

        let head_next_raw = Pool::get_next_raw_from_raw(&self.get_globals().pool_head);

        if head_next_raw > this_pool_addr {
            // B1
            //
            // Must go right after head then. pool_head never changes
            Pool::insert_right_after_left(self.get_globals().pool_head, this_pool_addr);
            return;
        }

        if let Some(mut it) = self
            .get_pool_iter()
            .find(|x| this_pool_addr < x.get_pool().get_next_raw())
        {
            //B2
            Pool::insert_right_after_left(
                std::ptr::addr_of_mut!(*it.get_pool_mut()),
                this_pool_addr,
            );
        } else {
            //B3
            Pool::insert_right_after_left(self.get_globals().pool_head, this_pool_addr);
        }
    }

    fn nf_add_block(&mut self, val: Value) {
        let it = FreeList::new(self.get_globals_mut())
            .nf_iter()
            .find(|e| e.get_cur() > val && e.get_prev() < val);
        self.get_globals_mut().cur_wsz += whsize_wosize(val.get_header().get_wosize());
        match it {
            None => {
                // means its the last most address
                *get_next(&self.get_globals().nf_last) = val;
                self.get_globals_mut().nf_last = val;
                *get_next(&self.get_globals().nf_last) = VAL_NULL;
            }
            Some(it) => {
                *get_next(&val) = it.get_cur();
                *get_next(&it.get_actual_prev()) = val;
            }
        }
    }
    #[cfg(feature = "check_invariants")]
    pub fn verify_nf_last_invariant(&mut self) {
        assert!(
            FreeList::new(self.get_globals_mut())
                .nf_iter()
                .all(|it| it.get_prev() < it.get_cur()),
            "Sorted free list invariant broken"
        );

        let largest_cur_val = FreeList::new(self.get_globals_mut())
            .nf_iter()
            .fold(Value(0), |acc, e| Value(acc.0.max(e.get_cur().0)));

        // This is only valid because of the iteration done right before though
        let nf_last = get_global_allocator().get_globals().nf_last;
        let nf_head = get_global_allocator().get_globals().nf_head;
        assert!(
            (nf_last == nf_head) || largest_cur_val == nf_last,
            "NfLast == LargestValueInFreeList Invariant failed.\nNfLast:{nf_last:?}\nLargestInFreeList:{largest_cur_val:?}\n",
        );
    }

    #[cfg(not(feature = "no_merge"))]
    fn merge_and_update_global(&mut self, left: Value, right: Value) {
        let merged = utils::try_merge(left, right);
        if merged {
            if self.get_globals().nf_last == right {
                self.get_globals_mut().nf_last = left;
            }
            if self.get_globals().nf_prev == right {
                self.get_globals_mut().nf_prev = left;
            }
        }
    }

    pub fn nf_deallocate(&mut self, val: Value) {
        self.get_globals_mut().cur_wsz += whsize_wosize(val.get_header().get_wosize());

        *val.get_header() =
            Header::new(*val.get_header().get_wosize().get_val(), BLUE, DEFAULT_TAG);

        if val > self.get_globals().nf_last {
            let prev = self.get_globals().nf_last;
            *get_next(&self.get_globals().nf_last) = val;
            self.get_globals_mut().nf_last = val;

            #[cfg(not(feature = "no_merge"))]
            self.merge_and_update_global(prev, val);

            *get_next(&self.get_globals().nf_last) = VAL_NULL;
            return;
        }

        if *get_next(&self.get_globals().nf_head) == VAL_NULL
            || val.0 < get_next(&self.get_globals().nf_head).0
        {
            let prev_first = *get_next(&self.get_globals().nf_head);

            *get_next(&self.get_globals().nf_head) = val;
            *get_next(&val) = prev_first;

            if prev_first != VAL_NULL {
                #[cfg(not(feature = "no_merge"))]
                self.merge_and_update_global(val, prev_first);
            } else {
                // We must set nf_last to be val as *get_next( nf_head) == VAL_NULL => the list was
                // empty. Must change nf_last
                self.get_globals_mut().nf_last = val;
                *get_next(&self.get_globals().nf_last) = VAL_NULL;
            }
            return;
        }

        if let Some(it) = FreeList::new(self.get_globals_mut())
            .nf_iter()
            .find(|it| it.get_cur() > val && it.get_prev() < val)
        {
            *get_next(&val) = it.get_cur();
            *get_next(&it.get_actual_prev()) = val;
            #[cfg(not(feature = "no_merge"))]
            {
                self.merge_and_update_global(val, it.get_cur());
                self.merge_and_update_global(it.get_actual_prev(), val);
            }
        } else {
            unreachable!(
                "Shouldnt have hit this branch. Start Debugging🤕!!\n ===> Dellocation Request for: {val:?}\n Globals: {:?}\n",
                self.get_globals(),
            );
        }
    }

    pub fn nf_sweep(&mut self) {
        let all_pools = self.get_pool_iter().collect::<Vec<PoolIterVal>>();
        let mut work_done = vec![];

        for mut it in all_pools {
            work_done.push(self.sweep(it.get_pool_mut()));
        }
    }
    fn mem_write(mem: *mut Header, sz: usize, hd: Header) {
        for i in 0..sz {
            unsafe {
                *mem.add(i) = hd.clone();
            }
        }
    }

    fn sweep(&mut self, pool: &mut Pool) -> Wsize {
        let mut cur_hp = std::ptr::addr_of_mut!(pool.hd);
        let (_, limit) = pool.get_range();

        let sweeped_wsz = Wsize::new(0);

        let mut last_free_block = self.get_globals().nf_head;
        let mut last_empty_val = Value(0);

        while (cur_hp as usize) < limit {
            let cur_hd = hd_hp!(cur_hp);
            let mut cur_val = val_hp!(cur_hp);
            // println!(
            //     "Val: {:#x?} has color: {:?}, tag: {:?}, sz: {:?}",
            //     cur_val.0,
            //     cur_hd.get_color(),
            //     cur_hd.get_tag(),
            //     cur_hd.get_wosize().get_val()
            // );
            match cur_hd.get_color() {
                BLACK => {
                    // Live
                    *cur_hd = Header::new(
                        *cur_hd.get_wosize().get_val(),
                        WHITE, // Black -> White
                        cur_hd.get_tag(),
                    );
                }
                WHITE => {
                    // Dead

                    // last_free_block is always something in which get_next is valid
                    // If the first block we encounter itself is WHITE, the get_next call in
                    // B1 branch in nf_merge is valid

                    #[cfg(debug_assertions)]
                    {
                        // The content can be cleared safely and be reset to all empty blocks,
                        // because WHITE implies the memory is not in use. This will always end up going
                        // back to the free list for further allocation so it's fine.
                        Self::mem_write(
                            cur_val.0 as *mut Header,
                            *cur_val.get_header().get_wosize().get_val(),
                            Header::new(0, BLUE, DEFAULT_TAG),
                        );
                    }

                    self.nf_merge(&mut cur_val, &mut last_empty_val, &mut last_free_block);
                }
                BLUE => {
                    // In free list
                    last_free_block = val_hp!(cur_hp);
                }
                _ => {
                    unreachable!(
                        "Nothing should have Gray color in sweep phase, cur_val: {cur_val:?}"
                    )
                }
            }
            cur_hp = hp_val!(cur_val.get_next_from_size());
        }
        sweeped_wsz
    }
    fn nf_merge(
        &mut self,
        cur_val: &mut Value,
        last_empty_val: &mut Value,
        last_free_block: &mut Value,
    ) {
        self.get_globals_mut().cur_wsz += whsize_wosize(cur_val.get_header().get_wosize());

        // [B1]
        // If last_empty_val is adjacent to cur
        if std::ptr::eq(bp_val!(last_empty_val), hp_val!(cur_val) as _) {
            self.get_globals_mut().cur_wsz += whsize_wosize(Wsize::new(0)); //to account for the empty
                                                                            //block
            *last_empty_val.get_header() = Header::new(
                *whsize_wosize(cur_val.get_header().get_wosize()).get_val(),
                WHITE, // it's still WHITE, we'll make it BLUE after inserting to fl
                DEFAULT_TAG,
            );
            *cur_val = last_empty_val.clone();
        }

        // [B2]
        // get_next on last_free_block is safe because we've made sure in nf_sweep that it has
        // BLUE color
        if *get_next(last_free_block) == cur_val.get_next_from_size() {
            let next_free_block = *get_next(last_free_block);

            *cur_val.get_header() = Header::new(
                *(cur_val.get_header().get_wosize()
                    + whsize_wosize(next_free_block.get_header().get_wosize()))
                .get_val(),
                BLUE,
                DEFAULT_TAG,
            );

            // Change last_free_block's next correctly
            *get_next(last_free_block) = *get_next(&next_free_block);

            if next_free_block == self.get_globals().nf_prev {
                self.get_globals_mut().nf_prev = *last_free_block;
            }
            self.get_globals_mut().nf_last = VAL_NULL;
        }

        // [B3]
        if last_free_block.get_next_from_size() == *cur_val {
            *last_free_block.get_header() = Header::new(
                *(last_free_block.get_header().get_wosize()
                    + whsize_wosize(cur_val.get_header().get_wosize()))
                .get_val(),
                BLUE,
                DEFAULT_TAG,
            );
        } else if cur_val.get_header().get_wosize() != Wsize::new(0) {
            // [B4]
            *cur_val.get_header() = Header::new(
                *cur_val.get_header().get_wosize().get_val(),
                BLUE,
                DEFAULT_TAG,
            );
            *get_next(&cur_val) = *get_next(last_free_block);
            *get_next(last_free_block) = *cur_val;
            *last_free_block = *cur_val;
        } else {
            // [B5]
            self.get_globals_mut().cur_wsz -= whsize_wosize(Wsize::new(0));
            *last_empty_val = *cur_val;
        }
    }

    pub fn get_stats(&self) -> AllocatorStats {
        static mut MIN_EXPANSION_WSZ_AS_USIZE: usize = 0usize;
        static ONCE: std::sync::Once = std::sync::Once::new();
        ONCE.call_once(|| unsafe {
            let (_, min_expansion_wsz) = get_layout_and_actual_expansion_size(Wsize::new(0));
            MIN_EXPANSION_WSZ_AS_USIZE = *min_expansion_wsz.get_val();
        });

        let total_pool_wsz = self
            .get_pool_iter()
            .map(|pool| {
                whsize_wosize(Pool::get_header_size_from_pool_wo_sz(
                    pool.get_pool().pool_wo_sz,
                ))
            })
            .fold(Wsize::new(0), |acc, e| acc + e);

        let cur_wsz = self.get_globals().cur_wsz;
        AllocatorStats {
            cur_free_wsz: *cur_wsz.get_val(),
            total_wsz: *total_pool_wsz.get_val(),
            min_expansion_wsz: unsafe { MIN_EXPANSION_WSZ_AS_USIZE },
        }
    }
}

static mut GLOBAL_ALLOC: NfAllocator = NfAllocator {
    globals: NfGlobals {
        cur_wsz: Wsize::new(0),
        nf_head: Value(0),
        nf_prev: Value(0),
        nf_last: Value(0),
        pool_head: std::ptr::null_mut(),
    },
    #[cfg(debug_assertions)]
    last_expandheap_start_end: (0usize, 0usize),
    num_of_heap_expansions: 0usize,
};

#[inline(always)]
pub fn get_global_allocator() -> &'static mut NfAllocator {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| unsafe {
        GLOBAL_ALLOC.globals.cur_wsz = NfGlobals::get().cur_wsz;
        GLOBAL_ALLOC.globals.nf_head = NfGlobals::get().nf_head;
        GLOBAL_ALLOC.globals.nf_prev = NfGlobals::get().nf_prev;
        GLOBAL_ALLOC.globals.nf_last = NfGlobals::get().nf_last;
        GLOBAL_ALLOC.globals.pool_head = NfGlobals::get().pool_head;
    });

    unsafe { &mut GLOBAL_ALLOC }
}

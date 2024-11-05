#include "Impl_GC_closure_infix_ver3.h"
#include <stddef.h>
#include <stdint.h>

#include <assert.h>

#define CAML_INTERNALS
#include "../caml/misc.h"
#include "../caml/mlvalues.h"
#include "../caml/roots.h"

// Handwritten
//
// Needed for the workaround when calling caml_do_roots, we need this
// information inside the function we pass to it. Hence, we need to resort to
// this.
uint64_t *st = NULL;
uint64_t *st_top = NULL;

// To add extra bound checks
uint64_t hs = 0; // Heap Start
uint64_t he = 0; // Heap End

// This is to interface with the allocator
struct HeapRange {
  size_t first_header;
  size_t rightmost_value;
};

// runtime defines alloc to be caml_alloc, we don't want that here
#undef alloc

extern uint8_t *alloc(unsigned long long);
extern size_t get_freelist_head();
extern struct HeapRange get_heap_range();

void darken_root(value root, value *root_ptr) {
  assert(root == *root_ptr);
  // Ensures we don't ever try to darken a pointer that is not part of our heap,
  // because runtime does too many things and there's a possibility of this
  // happening(we have noticed it)
  if (Is_block(root) && Wosize_val(root) > 0 && root >= hs && root < he) {
    Impl_GC_closure_infix_ver3_push_to_stack(NULL, st, st_top,
                                             (uint64_t)Hp_val(root));
  }
}

void mark_and_sweep_aux(uint8_t *g, uint64_t h_list_length,
                        uint64_t free_list_start_ptr,
                        uint64_t free_list_end_ptr) {

  // Handwritten: Allocating enough memory for our stack
  st = KRML_HOST_CALLOC((uint32_t)h_list_length * 10, sizeof(uint64_t));

  st_top = KRML_HOST_CALLOC((uint32_t)1U, sizeof(uint64_t));

  uint64_t *h_index_buf = KRML_HOST_CALLOC((uint32_t)1U, sizeof(uint64_t));
  *h_index_buf = free_list_start_ptr;

  caml_do_roots(darken_root, 1);

  Impl_GC_closure_infix_ver3_mark_heap7(g, st, st_top);

  // Sets the previous pointer appropriately for sweep
  uint64_t freelist_starting_value = get_freelist_head();

  uint64_t prev_ptr = (uint64_t)freelist_starting_value;

  Impl_GC_closure_infix_ver3_sweep1_with_free_list1(g, h_index_buf, &prev_ptr,
                                                    free_list_end_ptr);

  // Makes sure we're pointing to right places after sweep, expected by
  // allocator that the last free pointer should point to null
  *(uint64_t *)prev_ptr = 0U;

  KRML_HOST_FREE(st);
  KRML_HOST_FREE(st_top);
  KRML_HOST_FREE(h_index_buf);
}

void mark_and_sweep(uint64_t xheap_start, uint64_t heap_end) {

  hs = xheap_start;
  he = heap_end;
  /* printf("About to collect\n"); */

  mark_and_sweep_aux(NULL, 1024 * 1024, xheap_start, heap_end);

  /* printf("Finished collection\n"); */
}

void verified_gc() {
  caml_gc_message(0x20, "Triggering GC\n");
  Caml_state->_stat_major_collections++;
  mark_and_sweep(get_heap_range().first_header + 8U,
                 get_heap_range().rightmost_value);
}

void *verified_allocate(mlsize_t wsize) {
  /* printf("Allocation request for %lld\n", wsize); */
  uint8_t *mem = alloc(wsize);
  int oom_count = 0;

again:
  if (((uintptr_t)mem - sizeof(uintptr_t)) == 0) {
    oom_count++;
    if (oom_count == 2) {
      // Exit
      caml_fatal_error("Allocator OOM");
    }

    verified_gc();
    mem = alloc(wsize);
    goto again;
  }
  return mem - 8U;
}

CAMLprim value caml_trigger_verified_gc(value v) {
  verified_gc();
  return Val_unit;
}

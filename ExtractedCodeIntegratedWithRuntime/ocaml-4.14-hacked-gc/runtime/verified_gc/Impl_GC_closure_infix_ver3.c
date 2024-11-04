#include "Impl_GC_closure_infix_ver3.h"

#include "internal/FStar.h"
#include "internal/Spec.h"

#include <assert.h>

krml_checked_int_t Impl_GC_closure_infix_ver3_op_Bang(uint64_t x) {
  return FStar_UInt64_v(x);
}

uint64_t Impl_GC_closure_infix_ver3_getColor(uint64_t h) {
  uint64_t c_ = h >> 8U;
  return c_ & 3ULL;
}

uint64_t Impl_GC_closure_infix_ver3_makeHeader(uint64_t wz, uint64_t c,
                                               uint64_t tg) {
  return Spec_GC_infix_closure_ver3_makeHeader(wz, c, tg);
}

uint64_t
Impl_GC_closure_infix_ver3_read_word_from_byte_buffer(uint8_t *g,
                                                      uint64_t byte_index) {
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(byte_index));
  return load64_le(g + x1);
}

void Impl_GC_closure_infix_ver3_write_word_to_byte_buffer(uint8_t *g,
                                                          uint64_t byte_index,
                                                          uint64_t v) {
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(byte_index));
  store64_le(g + x1, v);
}

bool Impl_GC_closure_infix_ver3_isPointer(uint64_t v_id, uint8_t *g) {
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(v_id));
  return (load64_le(g + x1) & 1ULL) == 0ULL;
}

uint64_t Impl_GC_closure_infix_ver3_wosize_of_block(uint64_t v_id, uint8_t *g) {
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(v_id));
  uint64_t index = load64_le(g + x1);
  uint64_t wz = Spec_GC_infix_closure_ver3_getWosize(index);
  return wz;
}

uint64_t Impl_GC_closure_infix_ver3_color_of_block(uint64_t v_id, uint8_t *g) {
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(v_id));
  uint64_t index = load64_le(g + x1);
  uint64_t cl = Spec_GC_infix_closure_ver3_getColor(index);
  return cl;
}

uint64_t Impl_GC_closure_infix_ver3_tag_of_block(uint64_t v_id, uint8_t *g) {
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(v_id));
  uint64_t index = load64_le(g + x1);
  uint64_t tg = Spec_GC_infix_closure_ver3_getTag(index);
  return tg;
}

void Impl_GC_closure_infix_ver3_colorHeader1(uint8_t *g, uint64_t v_id,
                                             uint64_t c) {
  uint64_t wz = Impl_GC_closure_infix_ver3_wosize_of_block(v_id, g);
  uint64_t tg = Impl_GC_closure_infix_ver3_tag_of_block(v_id, g);
  uint64_t h_val = Spec_GC_infix_closure_ver3_makeHeader(wz, c, tg);
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(v_id));
  store64_le(g + x1, h_val);
}

void Impl_GC_closure_infix_ver3_push_to_stack(uint8_t *g, uint64_t *st,
                                              uint64_t *st_len, uint64_t elem) {
  uint64_t i = *st_len;
  uint64_t f_elem = Spec_GC_infix_closure_ver3_f_address(elem);
  st[FStar_UInt32_uint_to_t(FStar_UInt64_v(i))] = f_elem;
  st_len[0U] = *st_len + 1ULL;
  Impl_GC_closure_infix_ver3_colorHeader1(g, elem,
                                          Spec_GC_infix_closure_ver3_gray);
}

uint64_t Impl_GC_closure_infix_ver3_read_succ_impl(uint8_t *g, uint64_t h_index,
                                                   uint64_t i) {
  uint64_t succ_index = h_index + i * 8ULL;
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(succ_index));
  uint64_t succ = load64_le(g + x1);
  return succ;
}

uint64_t Impl_GC_closure_infix_ver3_parent_closure_of_infix_object_impl(
    uint8_t *g, uint64_t h_index, uint64_t i) {
  uint64_t succ = Impl_GC_closure_infix_ver3_read_succ_impl(g, h_index, i);
  uint64_t h_addr_succ = Spec_GC_infix_closure_ver3_hd_address(succ);
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(h_addr_succ));
  uint64_t h_addr_succ_val = load64_le(g + x1);
  uint64_t wosize = Spec_GC_infix_closure_ver3_getWosize(h_addr_succ_val);
  uint64_t parent_succ = succ - wosize * 8ULL;
  uint64_t h_addr_parent = Spec_GC_infix_closure_ver3_hd_address(parent_succ);
  return h_addr_parent;
}

void Impl_GC_closure_infix_ver3_darken_helper_impl(uint8_t *g, uint64_t *st,
                                                   uint64_t *st_len,
                                                   uint64_t hdr_id) {
  if (Impl_GC_closure_infix_ver3_color_of_block(hdr_id, g) ==
      Spec_GC_infix_closure_ver3_white)
    Impl_GC_closure_infix_ver3_push_to_stack(g, st, st_len, hdr_id);
}

void Impl_GC_closure_infix_ver3_darken_body(uint8_t *g, uint64_t *st,
                                            uint64_t *st_len, uint64_t h_index,
                                            uint64_t wz, uint64_t i) {
  KRML_MAYBE_UNUSED_VAR(wz);
  uint64_t succ_index = h_index + i * 8ULL;
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(succ_index));
  uint64_t succ = load64_le(g + x1);
  if (Impl_GC_closure_infix_ver3_isPointer(succ_index, g)) {
    uint64_t h_addr_succ = Spec_GC_infix_closure_ver3_hd_address(succ);
    if (Impl_GC_closure_infix_ver3_tag_of_block(h_addr_succ, g) == 249ULL) {
      uint64_t parent_hdr =
          Impl_GC_closure_infix_ver3_parent_closure_of_infix_object_impl(
              g, h_index, i);
      Impl_GC_closure_infix_ver3_darken_helper_impl(g, st, st_len, parent_hdr);
    } else
      Impl_GC_closure_infix_ver3_darken_helper_impl(g, st, st_len, h_addr_succ);
  }
}

void Impl_GC_closure_infix_ver3_darken(uint8_t *g, uint64_t *st,
                                       uint64_t *st_len, uint64_t h_index,
                                       uint64_t wz) {
  for (uint32_t i = 1U; i < FStar_UInt32_uint_to_t(FStar_UInt64_v(wz + 1ULL));
       i++)
    Impl_GC_closure_infix_ver3_darken_body(
        g, st, st_len, h_index, wz, FStar_UInt64_uint_to_t(FStar_UInt32_v(i)));
}

void Impl_GC_closure_infix_ver3_darken1(uint8_t *g, uint64_t *st,
                                        uint64_t *st_len, uint64_t h_index,
                                        uint64_t wz, uint64_t j) {
  for (uint32_t i = FStar_UInt32_uint_to_t(FStar_UInt64_v(j));
       i < FStar_UInt32_uint_to_t(FStar_UInt64_v(wz + 1ULL)); i++)
    Impl_GC_closure_infix_ver3_darken_body(
        g, st, st_len, h_index, wz, FStar_UInt64_uint_to_t(FStar_UInt32_v(i)));
}

uint64_t Impl_GC_closure_infix_ver3_closinfo_val_impl(uint8_t *g,
                                                      uint64_t f_addr) {
  uint64_t hdr_f_addr = Spec_GC_infix_closure_ver3_hd_address(f_addr);
  uint64_t wz = Impl_GC_closure_infix_ver3_wosize_of_block(hdr_f_addr, g);
  KRML_MAYBE_UNUSED_VAR(wz);
  uint64_t offst1 = 8ULL;
  uint64_t s1 = f_addr + offst1;
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(s1));
  uint64_t clos_info = load64_le(g + x1);
  return clos_info;
}

uint64_t Impl_GC_closure_infix_ver3_start_env_clos_info(uint8_t *g,
                                                        uint64_t f_addr) {
  uint64_t clos_info = Impl_GC_closure_infix_ver3_closinfo_val_impl(g, f_addr);
  uint64_t start_env =
      Spec_GC_infix_closure_ver3_extract_start_env_bits_(clos_info);
  return start_env;
}

void Impl_GC_closure_infix_ver3_darken_wrapper_impl(uint8_t *g, uint64_t *st,
                                                    uint64_t *st_len,
                                                    uint64_t h_x, uint64_t wz) {
  if (Impl_GC_closure_infix_ver3_tag_of_block(h_x, g) == 247ULL) {
    uint64_t x = Spec_GC_infix_closure_ver3_f_address(h_x);
    uint64_t start_env = Impl_GC_closure_infix_ver3_start_env_clos_info(g, x);
    uint64_t start_env_plus_one = start_env + 1ULL;
    Impl_GC_closure_infix_ver3_darken1(g, st, st_len, h_x, wz,
                                       start_env_plus_one);
  } else if (Impl_GC_closure_infix_ver3_tag_of_block(h_x, g) ==
             (uint64_t)249U) {
    // Handwritten to handle a very weird edge-case
    wz = *(uint64_t *)h_x >> 10;
    h_x = h_x - wz * 8;
    wz = *(uint64_t *)h_x >> 10;
    assert(Impl_GC_closure_infix_ver3_tag_of_block(h_x, g) == 247);
    Impl_GC_closure_infix_ver3_darken_wrapper_impl(g, st, st_len, h_x, wz);
  } else
    Impl_GC_closure_infix_ver3_darken1(g, st, st_len, h_x, wz, 1ULL);
}

void Impl_GC_closure_infix_ver3_mark_heap_body1_impl(uint8_t *g, uint64_t *st,
                                                     uint64_t *st_len) {
  st_len[0U] = *st_len - 1ULL;
  uint64_t x = st[FStar_UInt32_uint_to_t(FStar_UInt64_v(*st_len))];
  uint64_t h_x = Spec_GC_infix_closure_ver3_hd_address(x);
  Impl_GC_closure_infix_ver3_colorHeader1(g, h_x,
                                          Spec_GC_infix_closure_ver3_black);
  uint64_t wz = Impl_GC_closure_infix_ver3_wosize_of_block(h_x, g);
  uint64_t tg = Impl_GC_closure_infix_ver3_tag_of_block(h_x, g);
  if (tg < 251ULL)
    Impl_GC_closure_infix_ver3_darken_wrapper_impl(g, st, st_len, h_x, wz);
}

void Impl_GC_closure_infix_ver3_mark_heap7(uint8_t *g, uint64_t *st,
                                           uint64_t *st_len) {
  while (*st_len > 0ULL)
    Impl_GC_closure_infix_ver3_mark_heap_body1_impl(g, st, st_len);
}

void Impl_GC_closure_infix_ver3_colorHeader3(uint8_t *g, uint64_t v_id,
                                             uint64_t c) {
  uint64_t wz = Impl_GC_closure_infix_ver3_wosize_of_block(v_id, g);
  uint64_t tg = Impl_GC_closure_infix_ver3_tag_of_block(v_id, g);
  uint64_t h_val = Spec_GC_infix_closure_ver3_makeHeader(wz, c, tg);
  uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(v_id));
  store64_le(g + x1, h_val);
}

void Impl_GC_closure_infix_ver3_sweep_body_helper_with_free_list1(
    uint8_t *g, uint64_t *f_index, uint64_t *free_list_ptr) {
  uint64_t f_index_val = *f_index;
  uint64_t h_index = Spec_GC_infix_closure_ver3_hd_address(f_index_val);
  uint64_t c = Impl_GC_closure_infix_ver3_color_of_block(h_index, g);
  uint64_t wz = Impl_GC_closure_infix_ver3_wosize_of_block(h_index, g);
  // Handwritten, to handle 0 sized blocks
  if (wz == 0) {
    return;
  }

  if (c == Spec_GC_infix_closure_ver3_white ||
      c == Spec_GC_infix_closure_ver3_blue) {
    Impl_GC_closure_infix_ver3_colorHeader3(g, h_index,
                                            Spec_GC_infix_closure_ver3_blue);
    uint64_t free_list_ptr_val = *free_list_ptr;
    /* Begin Handwritten code */
    // This is coalescing logic to improve sweep performance. The sweep we've
    // verified doesn't perform coalescing, which is problematic for benchmarks.
    // To get past that, we do this.
    uint64_t cur_wosize = Impl_GC_closure_infix_ver3_wosize_of_block(
        Spec_GC_infix_closure_ver3_hd_address(free_list_ptr_val), g);
    uint64_t next = free_list_ptr_val + cur_wosize * 8 + 8 /* header */;
    if (next == f_index_val) {

      uint64_t next_wosize = Impl_GC_closure_infix_ver3_wosize_of_block(
          Spec_GC_infix_closure_ver3_hd_address(f_index_val), g);
      ((uint64_t *)free_list_ptr_val)[-1] =
          Spec_GC_infix_closure_ver3_makeHeader(
              cur_wosize + next_wosize + 1, Spec_GC_infix_closure_ver3_blue, 0);
    } else {
      uint32_t x1 = FStar_UInt32_uint_to_t(FStar_UInt64_v(free_list_ptr_val));
      store64_le(g + x1, f_index_val);
      free_list_ptr[0U] = f_index_val;
    }
    /* End Handwritten code */
  } else
    Impl_GC_closure_infix_ver3_colorHeader3(g, h_index,
                                            Spec_GC_infix_closure_ver3_white);
}

void Impl_GC_closure_infix_ver3_sweep1_with_free_list1(
    uint8_t *g, uint64_t *f_index, uint64_t *free_list_ptr,
    uint64_t limit // manually added to enforce bound while going through the
                   // free list

) {
  // Handwritten
  //
  // Removing the below check and replacing with the right check. This check
  // comes in due to the configuration used in proofs
  /* while (*f_index < 1024ULL) { */
  while (*f_index < limit) {
    uint64_t f_index_val = *f_index;
    uint64_t h_index_val = Spec_GC_infix_closure_ver3_hd_address(f_index_val);
    uint64_t wz = Impl_GC_closure_infix_ver3_wosize_of_block(h_index_val, g);
    uint64_t h_index_new = h_index_val + (wz + 1ULL) * 8ULL;
    uint64_t f_index_new = h_index_new + 8ULL;
    Impl_GC_closure_infix_ver3_sweep_body_helper_with_free_list1(g, f_index,
                                                                 free_list_ptr);
    f_index[0U] = f_index_new;
  }
}

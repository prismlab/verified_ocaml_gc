#ifndef __Impl_GC_closure_infix_ver3_H
#define __Impl_GC_closure_infix_ver3_H

#include "internal/alias.h"
#include <stdint.h>

krml_checked_int_t Impl_GC_closure_infix_ver3_op_Bang(uint64_t x);

typedef uint8_t *Impl_GC_closure_infix_ver3_heap;

typedef uint64_t Impl_GC_closure_infix_ver3_addr;

typedef uint64_t *Impl_GC_closure_infix_ver3_stack;

typedef uint64_t *Impl_GC_closure_infix_ver3_usize_buffer;

typedef void *Impl_GC_closure_infix_ver3_disjoint;

typedef void *Impl_GC_closure_infix_ver3_modified2;

typedef void *Impl_GC_closure_infix_ver3_modified3;

typedef void *Impl_GC_closure_infix_ver3_stack_props;

typedef uint64_t *Impl_GC_closure_infix_ver3_st_top;

uint64_t Impl_GC_closure_infix_ver3_getColor(uint64_t h);

uint64_t Impl_GC_closure_infix_ver3_makeHeader(uint64_t wz, uint64_t c,
                                               uint64_t tg);

uint64_t
Impl_GC_closure_infix_ver3_read_word_from_byte_buffer(uint8_t *g,
                                                      uint64_t byte_index);

void Impl_GC_closure_infix_ver3_write_word_to_byte_buffer(uint8_t *g,
                                                          uint64_t byte_index,
                                                          uint64_t v);

bool Impl_GC_closure_infix_ver3_isPointer(uint64_t v_id, uint8_t *g);

uint64_t Impl_GC_closure_infix_ver3_wosize_of_block(uint64_t v_id, uint8_t *g);

uint64_t Impl_GC_closure_infix_ver3_color_of_block(uint64_t v_id, uint8_t *g);

uint64_t Impl_GC_closure_infix_ver3_tag_of_block(uint64_t v_id, uint8_t *g);

void Impl_GC_closure_infix_ver3_colorHeader1(uint8_t *g, uint64_t v_id,
                                             uint64_t c);

void Impl_GC_closure_infix_ver3_push_to_stack(uint8_t *g, uint64_t *st,
                                              uint64_t *st_len, uint64_t elem);

uint64_t Impl_GC_closure_infix_ver3_read_succ_impl(uint8_t *g, uint64_t h_index,
                                                   uint64_t i);

uint64_t Impl_GC_closure_infix_ver3_parent_closure_of_infix_object_impl(
    uint8_t *g, uint64_t h_index, uint64_t i);

void Impl_GC_closure_infix_ver3_darken_helper_impl(uint8_t *g, uint64_t *st,
                                                   uint64_t *st_len,
                                                   uint64_t hdr_id);

void Impl_GC_closure_infix_ver3_darken_body(uint8_t *g, uint64_t *st,
                                            uint64_t *st_len, uint64_t h_index,
                                            uint64_t wz, uint64_t i);

void Impl_GC_closure_infix_ver3_darken(uint8_t *g, uint64_t *st,
                                       uint64_t *st_len, uint64_t h_index,
                                       uint64_t wz);

void Impl_GC_closure_infix_ver3_darken1(uint8_t *g, uint64_t *st,
                                        uint64_t *st_len, uint64_t h_index,
                                        uint64_t wz, uint64_t j);

uint64_t Impl_GC_closure_infix_ver3_closinfo_val_impl(uint8_t *g,
                                                      uint64_t f_addr);

uint64_t Impl_GC_closure_infix_ver3_start_env_clos_info(uint8_t *g,
                                                        uint64_t f_addr);

void Impl_GC_closure_infix_ver3_darken_wrapper_impl(uint8_t *g, uint64_t *st,
                                                    uint64_t *st_len,
                                                    uint64_t h_x, uint64_t wz);

void Impl_GC_closure_infix_ver3_mark_heap_body1_impl(uint8_t *g, uint64_t *st,
                                                     uint64_t *st_len);

void Impl_GC_closure_infix_ver3_mark_heap7(uint8_t *g, uint64_t *st,
                                           uint64_t *st_len);

void Impl_GC_closure_infix_ver3_colorHeader3(uint8_t *g, uint64_t v_id,
                                             uint64_t c);

void Impl_GC_closure_infix_ver3_sweep_body_helper_with_free_list1(
    uint8_t *g, uint64_t *f_index, uint64_t *free_list_ptr);

void Impl_GC_closure_infix_ver3_sweep1_with_free_list1(
    uint8_t *g, uint64_t *f_index, uint64_t *free_list_ptr,
    uint64_t limit // manually added to enforce bound while going through the
                   // free list

);

#define __Impl_GC_closure_infix_ver3_H_DEFINED
#endif

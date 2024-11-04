#ifndef __internal_Spec_H
#define __internal_Spec_H

#include "../Spec.h"
#include "LowStar_Prims.h"
#include "alias.h"
#include <stdint.h>

typedef Prims_list__uint64_t *Spec_Graph3_vertex_list;

krml_checked_int_t FStar_List_Tot_Base_length___uint64_t___uint64_t_(
    Prims_list___uint64_t___uint64_t_ *uu___);

Spec_Graph3_edge FStar_List_Tot_Base_index___uint64_t___uint64_t_(
    Prims_list___uint64_t___uint64_t_ *l, krml_checked_int_t i);

Prims_list___uint64_t___uint64_t_ *FStar_Seq_Base_slice____uint64_t___uint64_t_(
    Prims_list___uint64_t___uint64_t_ *s, krml_checked_int_t i,
    krml_checked_int_t j);

Prims_list__uint64_t *
FStar_List_Tot_Base_append__uint64_t(Prims_list__uint64_t *x,
                                     Prims_list__uint64_t *y);

Prims_list__uint64_t *FStar_Seq_Base_create__uint64_t(krml_checked_int_t len,
                                                      uint64_t v);

Prims_list__uint64_t *
Spec_Graph3_successors_fn2(uint64_t i, Prims_list___uint64_t___uint64_t_ *e);

Prims_list__uint64_t *Spec_Graph3_successors(Spec_Graph3_graph_state g,
                                             uint64_t i);

krml_checked_int_t
FStar_List_Tot_Base_length__uint64_t(Prims_list__uint64_t *uu___);

bool Spec_Graph3_is_emptySet(Prims_list__uint64_t *s);

uint64_t FStar_List_Tot_Base_index__uint64_t(Prims_list__uint64_t *l,
                                             krml_checked_int_t i);

uint64_t Spec_Graph3_get_last_elem(Spec_Graph3_graph_state g,
                                   Prims_list__uint64_t *s);

Prims_list__uint64_t *FStar_Seq_Base_slice___uint64_t(Prims_list__uint64_t *s,
                                                      krml_checked_int_t i,
                                                      krml_checked_int_t j);

Prims_list__uint64_t *Spec_Graph3_get_first(Spec_Graph3_graph_state g,
                                            Prims_list__uint64_t *s);

krml_checked_int_t
FStar_Seq_Properties_count__uint64_t(uint64_t x, Prims_list__uint64_t *s);

Prims_list__uint64_t *
Spec_Graph3_insert_to_vertex_set(Spec_Graph3_graph_state g, uint64_t x,
                                 Prims_list__uint64_t *s);

Prims_list__uint64_t *
Spec_Graph3_union_vertex_sets_snoc(Spec_Graph3_graph_state g,
                                   Prims_list__uint64_t *l1,
                                   Prims_list__uint64_t *l2);

Prims_list__uint64_t *Spec_Graph3_union_vertex_sets(Spec_Graph3_graph_state g,
                                                    Prims_list__uint64_t *l1,
                                                    Prims_list__uint64_t *l2);

Prims_list__uint64_t *Spec_Graph3_successor_push_itr1(Prims_list__uint64_t *l,
                                                      Prims_list__uint64_t *vl,
                                                      Prims_list__uint64_t *st,
                                                      krml_checked_int_t j);

Prims_list__uint64_t *
Spec_Graph3_remove_all_instances_of_vertex_from_vertex_set_cons(
    Prims_list__uint64_t *l, Prims_list__uint64_t *vl);

Prims_list__uint64_t *
Spec_Graph3_remove_all_instances_of_vertex_from_vertex_set(
    Prims_list__uint64_t *l, Prims_list__uint64_t *vl);

extern uint64_t Spec_GC_infix_closure_ver3_blue;

extern uint64_t Spec_GC_infix_closure_ver3_white;

extern uint64_t Spec_GC_infix_closure_ver3_gray;

extern uint64_t Spec_GC_infix_closure_ver3_black;

uint64_t Spec_GC_infix_closure_ver3_getWosize(uint64_t h);

uint64_t Spec_GC_infix_closure_ver3_getColor(uint64_t h);

uint64_t Spec_GC_infix_closure_ver3_getTag(uint64_t h);

uint64_t Spec_GC_infix_closure_ver3_makeHeader(uint64_t wz, uint64_t c,
                                               uint64_t tg);

uint64_t Spec_GC_infix_closure_ver3_hd_address(uint64_t st_index);

uint64_t Spec_GC_infix_closure_ver3_f_address(uint64_t h_index);

uint64_t Spec_GC_infix_closure_ver3_extract_start_env_bits_(uint64_t clos_info);

#define __internal_Spec_H_DEFINED
#endif

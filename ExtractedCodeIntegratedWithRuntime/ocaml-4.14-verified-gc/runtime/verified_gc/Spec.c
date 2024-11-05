#include "internal/Spec.h"

#include "internal/LowStar_Prims.h"

typedef Prims_list___uint64_t___uint64_t_ *edge_list;

krml_checked_int_t FStar_List_Tot_Base_length___uint64_t___uint64_t_(
    Prims_list___uint64_t___uint64_t_ *uu___) {
  if (uu___->tag == Prims_Nil)
    return (krml_checked_int_t)0;
  else if (uu___->tag == Prims_Cons) {
    Prims_list___uint64_t___uint64_t_ *tl1 = uu___->tl;
    return Prims_op_Addition(
        (krml_checked_int_t)1,
        FStar_List_Tot_Base_length___uint64_t___uint64_t_(tl1));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static krml_checked_int_t
length___uint64_t___uint64_t_(Prims_list___uint64_t___uint64_t_ *s) {
  return FStar_List_Tot_Base_length___uint64_t___uint64_t_(s);
}

static Prims_list__uint64_t *empty__uint64_t(void) {
  Prims_list__uint64_t *buf = KRML_HOST_MALLOC(sizeof(Prims_list__uint64_t));
  buf[0U] = ((Prims_list__uint64_t){.tag = Prims_Nil});
  return buf;
}

static uint64_t fst__uint64_t_uint64_t(Spec_Graph3_edge x) { return x.fst; }

static Spec_Graph3_edge
hd___uint64_t___uint64_t_(Prims_list___uint64_t___uint64_t_ *uu___) {
  if (uu___->tag == Prims_Cons)
    return uu___->hd;
  else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static Prims_list___uint64_t___uint64_t_ *
tail___uint64_t___uint64_t_(Prims_list___uint64_t___uint64_t_ *uu___) {
  if (uu___->tag == Prims_Cons)
    return uu___->tl;
  else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static Prims_list___uint64_t___uint64_t_ *(*tl___uint64_t___uint64_t_)(
    Prims_list___uint64_t___uint64_t_ *x0) = tail___uint64_t___uint64_t_;

Spec_Graph3_edge FStar_List_Tot_Base_index___uint64_t___uint64_t_(
    Prims_list___uint64_t___uint64_t_ *l, krml_checked_int_t i) {
  if (i == (krml_checked_int_t)0)
    return hd___uint64_t___uint64_t_(l);
  else
    return FStar_List_Tot_Base_index___uint64_t___uint64_t_(
        tl___uint64_t___uint64_t_(l),
        Prims_op_Subtraction(i, (krml_checked_int_t)1));
}

static Spec_Graph3_edge
index___uint64_t___uint64_t_(Prims_list___uint64_t___uint64_t_ *s,
                             krml_checked_int_t i) {
  return FStar_List_Tot_Base_index___uint64_t___uint64_t_(s, i);
}

static Spec_Graph3_edge
head___uint64_t___uint64_t_(Prims_list___uint64_t___uint64_t_ *s) {
  return index___uint64_t___uint64_t_(s, (krml_checked_int_t)0);
}

static uint64_t snd__uint64_t_uint64_t(Spec_Graph3_edge x) { return x.snd; }

static Prims_list___uint64_t___uint64_t_ *
tl___uint64_t___uint64_t_0(Prims_list___uint64_t___uint64_t_ *s) {
  return tl___uint64_t___uint64_t_(s);
}

static Prims_list___uint64_t___uint64_t_ *
_cons___uint64_t___uint64_t_(Spec_Graph3_edge x,
                             Prims_list___uint64_t___uint64_t_ *s) {
  Prims_list___uint64_t___uint64_t_ *buf =
      KRML_HOST_MALLOC(sizeof(Prims_list___uint64_t___uint64_t_));
  buf[0U] = ((Prims_list___uint64_t___uint64_t_){
      .tag = Prims_Cons, .hd = x, .tl = s});
  return buf;
}

static Spec_Graph3_edge
hd___uint64_t___uint64_t_0(Prims_list___uint64_t___uint64_t_ *s) {
  return hd___uint64_t___uint64_t_(s);
}

Prims_list___uint64_t___uint64_t_ *FStar_Seq_Base_slice____uint64_t___uint64_t_(
    Prims_list___uint64_t___uint64_t_ *s, krml_checked_int_t i,
    krml_checked_int_t j) {
  if (Prims_op_GreaterThan(i, (krml_checked_int_t)0))
    return FStar_Seq_Base_slice____uint64_t___uint64_t_(
        tl___uint64_t___uint64_t_0(s),
        Prims_op_Subtraction(i, (krml_checked_int_t)1),
        Prims_op_Subtraction(j, (krml_checked_int_t)1));
  else if (j == (krml_checked_int_t)0) {
    Prims_list___uint64_t___uint64_t_ *buf =
        KRML_HOST_MALLOC(sizeof(Prims_list___uint64_t___uint64_t_));
    buf[0U] = ((Prims_list___uint64_t___uint64_t_){.tag = Prims_Nil});
    return buf;
  } else
    return _cons___uint64_t___uint64_t_(
        hd___uint64_t___uint64_t_0(s),
        FStar_Seq_Base_slice____uint64_t___uint64_t_(
            tl___uint64_t___uint64_t_0(s), i,
            Prims_op_Subtraction(j, (krml_checked_int_t)1)));
}

static Prims_list___uint64_t___uint64_t_ *(*slice___uint64_t___uint64_t_)(
    Prims_list___uint64_t___uint64_t_ *x0, krml_checked_int_t x1,
    krml_checked_int_t x2) = FStar_Seq_Base_slice____uint64_t___uint64_t_;

static Prims_list___uint64_t___uint64_t_ *
tail___uint64_t___uint64_t_0(Prims_list___uint64_t___uint64_t_ *s) {
  return slice___uint64_t___uint64_t_(s, (krml_checked_int_t)1,
                                      length___uint64_t___uint64_t_(s));
}

Prims_list__uint64_t *
FStar_List_Tot_Base_append__uint64_t(Prims_list__uint64_t *x,
                                     Prims_list__uint64_t *y) {
  if (x->tag == Prims_Nil)
    return y;
  else if (x->tag == Prims_Cons) {
    Prims_list__uint64_t *tl1 = x->tl;
    uint64_t a1 = x->hd;
    Prims_list__uint64_t *buf = KRML_HOST_MALLOC(sizeof(Prims_list__uint64_t));
    buf[0U] = ((Prims_list__uint64_t){
        .tag = Prims_Cons,
        .hd = a1,
        .tl = FStar_List_Tot_Base_append__uint64_t(tl1, y)});
    return buf;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static Prims_list__uint64_t *append__uint64_t(Prims_list__uint64_t *s1,
                                              Prims_list__uint64_t *s2) {
  return FStar_List_Tot_Base_append__uint64_t(s1, s2);
}

static Prims_list__uint64_t *_cons__uint64_t(uint64_t x,
                                             Prims_list__uint64_t *s) {
  Prims_list__uint64_t *buf = KRML_HOST_MALLOC(sizeof(Prims_list__uint64_t));
  buf[0U] = ((Prims_list__uint64_t){.tag = Prims_Cons, .hd = x, .tl = s});
  return buf;
}

Prims_list__uint64_t *FStar_Seq_Base_create__uint64_t(krml_checked_int_t len,
                                                      uint64_t v) {
  if (len == (krml_checked_int_t)0) {
    Prims_list__uint64_t *buf = KRML_HOST_MALLOC(sizeof(Prims_list__uint64_t));
    buf[0U] = ((Prims_list__uint64_t){.tag = Prims_Nil});
    return buf;
  } else
    return _cons__uint64_t(
        v, FStar_Seq_Base_create__uint64_t(
               Prims_op_Subtraction(len, (krml_checked_int_t)1), v));
}

static Prims_list__uint64_t *cons__uint64_t(uint64_t x,
                                            Prims_list__uint64_t *s) {
  return append__uint64_t(
      FStar_Seq_Base_create__uint64_t((krml_checked_int_t)1, x), s);
}

Prims_list__uint64_t *
Spec_Graph3_successors_fn2(uint64_t i, Prims_list___uint64_t___uint64_t_ *e) {
  if (length___uint64_t___uint64_t_(e) == (krml_checked_int_t)0)
    return empty__uint64_t();
  else {
    uint64_t f = fst__uint64_t_uint64_t(head___uint64_t___uint64_t_(e));
    uint64_t s = snd__uint64_t_uint64_t(head___uint64_t___uint64_t_(e));
    Prims_list__uint64_t *sl_ =
        Spec_Graph3_successors_fn2(i, tail___uint64_t___uint64_t_0(e));
    if (f == i) {
      Prims_list__uint64_t *sl = cons__uint64_t(s, sl_);
      return sl;
    } else
      return sl_;
  }
}

Prims_list__uint64_t *Spec_Graph3_successors(Spec_Graph3_graph_state g,
                                             uint64_t i) {
  Prims_list___uint64_t___uint64_t_ *e = g.edge_set;
  return Spec_Graph3_successors_fn2(i, e);
}

krml_checked_int_t
FStar_List_Tot_Base_length__uint64_t(Prims_list__uint64_t *uu___) {
  if (uu___->tag == Prims_Nil)
    return (krml_checked_int_t)0;
  else if (uu___->tag == Prims_Cons) {
    Prims_list__uint64_t *tl1 = uu___->tl;
    return Prims_op_Addition((krml_checked_int_t)1,
                             FStar_List_Tot_Base_length__uint64_t(tl1));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static krml_checked_int_t length__uint64_t(Prims_list__uint64_t *s) {
  return FStar_List_Tot_Base_length__uint64_t(s);
}

bool Spec_Graph3_is_emptySet(Prims_list__uint64_t *s) {
  if (length__uint64_t(s) == (krml_checked_int_t)0)
    return true;
  else
    return false;
}

static uint64_t hd__uint64_t(Prims_list__uint64_t *uu___) {
  if (uu___->tag == Prims_Cons)
    return uu___->hd;
  else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static Prims_list__uint64_t *tail__uint64_t(Prims_list__uint64_t *uu___) {
  if (uu___->tag == Prims_Cons)
    return uu___->tl;
  else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static Prims_list__uint64_t *(*tl__uint64_t)(Prims_list__uint64_t *x0) =
    tail__uint64_t;

uint64_t FStar_List_Tot_Base_index__uint64_t(Prims_list__uint64_t *l,
                                             krml_checked_int_t i) {
  if (i == (krml_checked_int_t)0)
    return hd__uint64_t(l);
  else
    return FStar_List_Tot_Base_index__uint64_t(
        tl__uint64_t(l), Prims_op_Subtraction(i, (krml_checked_int_t)1));
}

static uint64_t index__uint64_t(Prims_list__uint64_t *s, krml_checked_int_t i) {
  return FStar_List_Tot_Base_index__uint64_t(s, i);
}

uint64_t Spec_Graph3_get_last_elem(Spec_Graph3_graph_state g,
                                   Prims_list__uint64_t *s) {
  KRML_MAYBE_UNUSED_VAR(g);
  return index__uint64_t(
      s, Prims_op_Subtraction(length__uint64_t(s), (krml_checked_int_t)1));
}

static Prims_list__uint64_t *tl__uint64_t0(Prims_list__uint64_t *s) {
  return tl__uint64_t(s);
}

static uint64_t hd__uint64_t0(Prims_list__uint64_t *s) {
  return hd__uint64_t(s);
}

Prims_list__uint64_t *FStar_Seq_Base_slice___uint64_t(Prims_list__uint64_t *s,
                                                      krml_checked_int_t i,
                                                      krml_checked_int_t j) {
  if (Prims_op_GreaterThan(i, (krml_checked_int_t)0))
    return FStar_Seq_Base_slice___uint64_t(
        tl__uint64_t0(s), Prims_op_Subtraction(i, (krml_checked_int_t)1),
        Prims_op_Subtraction(j, (krml_checked_int_t)1));
  else if (j == (krml_checked_int_t)0) {
    Prims_list__uint64_t *buf = KRML_HOST_MALLOC(sizeof(Prims_list__uint64_t));
    buf[0U] = ((Prims_list__uint64_t){.tag = Prims_Nil});
    return buf;
  } else
    return _cons__uint64_t(hd__uint64_t0(s),
                           FStar_Seq_Base_slice___uint64_t(
                               tl__uint64_t0(s), i,
                               Prims_op_Subtraction(j, (krml_checked_int_t)1)));
}

static Prims_list__uint64_t *(*slice__uint64_t)(
    Prims_list__uint64_t *x0, krml_checked_int_t x1,
    krml_checked_int_t x2) = FStar_Seq_Base_slice___uint64_t;

Prims_list__uint64_t *Spec_Graph3_get_first(Spec_Graph3_graph_state g,
                                            Prims_list__uint64_t *s) {
  KRML_MAYBE_UNUSED_VAR(g);
  Prims_list__uint64_t *s_ = slice__uint64_t(
      s, (krml_checked_int_t)0,
      Prims_op_Subtraction(length__uint64_t(s), (krml_checked_int_t)1));
  if (Prims_op_GreaterThan(length__uint64_t(s_), (krml_checked_int_t)0))
    return s_;
  else
    return s_;
}

static uint64_t head__uint64_t(Prims_list__uint64_t *s) {
  return index__uint64_t(s, (krml_checked_int_t)0);
}

static Prims_list__uint64_t *tail__uint64_t0(Prims_list__uint64_t *s) {
  return slice__uint64_t(s, (krml_checked_int_t)1, length__uint64_t(s));
}

krml_checked_int_t
FStar_Seq_Properties_count__uint64_t(uint64_t x, Prims_list__uint64_t *s) {
  if (length__uint64_t(s) == (krml_checked_int_t)0)
    return (krml_checked_int_t)0;
  else if (head__uint64_t(s) == x)
    return Prims_op_Addition(
        (krml_checked_int_t)1,
        FStar_Seq_Properties_count__uint64_t(x, tail__uint64_t0(s)));
  else
    return FStar_Seq_Properties_count__uint64_t(x, tail__uint64_t0(s));
}

static bool mem__uint64_t(uint64_t x, Prims_list__uint64_t *l) {
  return Prims_op_GreaterThan(FStar_Seq_Properties_count__uint64_t(x, l),
                              (krml_checked_int_t)0);
}

static Prims_list__uint64_t *snoc__uint64_t(Prims_list__uint64_t *s,
                                            uint64_t x) {
  return append__uint64_t(
      s, FStar_Seq_Base_create__uint64_t((krml_checked_int_t)1, x));
}

static Prims_list__uint64_t *
insert_to_vertex_set_snoc(uint64_t x, Prims_list__uint64_t *s) {
  if (mem__uint64_t(x, s))
    return s;
  else if (length__uint64_t(s) == (krml_checked_int_t)0) {
    Prims_list__uint64_t *s_ =
        FStar_Seq_Base_create__uint64_t((krml_checked_int_t)1, x);
    return s_;
  } else {
    Prims_list__uint64_t *s_ = snoc__uint64_t(s, x);
    return s_;
  }
}

Prims_list__uint64_t *
Spec_Graph3_insert_to_vertex_set(Spec_Graph3_graph_state g, uint64_t x,
                                 Prims_list__uint64_t *s) {
  KRML_MAYBE_UNUSED_VAR(g);
  return insert_to_vertex_set_snoc(x, s);
}

Prims_list__uint64_t *
Spec_Graph3_union_vertex_sets_snoc(Spec_Graph3_graph_state g,
                                   Prims_list__uint64_t *l1,
                                   Prims_list__uint64_t *l2) {
  if (length__uint64_t(l1) == (krml_checked_int_t)0)
    return l2;
  else if (mem__uint64_t(head__uint64_t(l1), l2))
    return Spec_Graph3_union_vertex_sets_snoc(g, tail__uint64_t0(l1), l2);
  else {
    Prims_list__uint64_t *u =
        Spec_Graph3_union_vertex_sets_snoc(g, tail__uint64_t0(l1), l2);
    if (length__uint64_t(u) == (krml_checked_int_t)0)
      return FStar_Seq_Base_create__uint64_t((krml_checked_int_t)1,
                                             head__uint64_t(l1));
    else
      return snoc__uint64_t(
          Spec_Graph3_union_vertex_sets_snoc(g, tail__uint64_t0(l1), l2),
          head__uint64_t(l1));
  }
}

Prims_list__uint64_t *Spec_Graph3_union_vertex_sets(Spec_Graph3_graph_state g,
                                                    Prims_list__uint64_t *l1,
                                                    Prims_list__uint64_t *l2) {
  return Spec_Graph3_union_vertex_sets_snoc(g, l1, l2);
}

static Prims_list__uint64_t *push_to_stack_graph1(Prims_list__uint64_t *st,
                                                  uint64_t x) {
  if (length__uint64_t(st) == (krml_checked_int_t)0) {
    Prims_list__uint64_t *stk_ =
        FStar_Seq_Base_create__uint64_t((krml_checked_int_t)1, x);
    return stk_;
  } else {
    Prims_list__uint64_t *st_ = snoc__uint64_t(st, x);
    return st_;
  }
}

static Prims_list__uint64_t *successor_push_body1(Prims_list__uint64_t *l,
                                                  Prims_list__uint64_t *vl,
                                                  Prims_list__uint64_t *st,
                                                  krml_checked_int_t j) {
  uint64_t succ = index__uint64_t(l, j);
  if (!mem__uint64_t(succ, vl) && !mem__uint64_t(succ, st)) {
    Prims_list__uint64_t *st_ = push_to_stack_graph1(st, succ);
    return st_;
  } else
    return st;
}

Prims_list__uint64_t *Spec_Graph3_successor_push_itr1(Prims_list__uint64_t *l,
                                                      Prims_list__uint64_t *vl,
                                                      Prims_list__uint64_t *st,
                                                      krml_checked_int_t j) {
  if (Prims_op_GreaterThanOrEqual(j, length__uint64_t(l)))
    return st;
  else {
    krml_checked_int_t j_ = Prims_op_Addition(j, (krml_checked_int_t)1);
    Prims_list__uint64_t *st_ = successor_push_body1(l, vl, st, j);
    Prims_list__uint64_t *st__ =
        Spec_Graph3_successor_push_itr1(l, vl, st_, j_);
    return st__;
  }
}

Prims_list__uint64_t *
Spec_Graph3_remove_all_instances_of_vertex_from_vertex_set_cons(
    Prims_list__uint64_t *l, Prims_list__uint64_t *vl) {
  if (length__uint64_t(l) == (krml_checked_int_t)0)
    return empty__uint64_t();
  else if (mem__uint64_t(head__uint64_t(l), vl))
    return Spec_Graph3_remove_all_instances_of_vertex_from_vertex_set_cons(
        tail__uint64_t0(l), vl);
  else {
    Prims_list__uint64_t *u =
        Spec_Graph3_remove_all_instances_of_vertex_from_vertex_set_cons(
            tail__uint64_t0(l), vl);
    if (mem__uint64_t(head__uint64_t(l), u))
      return u;
    else {
      Prims_list__uint64_t *u_ = cons__uint64_t(head__uint64_t(l), u);
      return u_;
    }
  }
}

Prims_list__uint64_t *
Spec_Graph3_remove_all_instances_of_vertex_from_vertex_set(
    Prims_list__uint64_t *l, Prims_list__uint64_t *vl) {
  return Spec_Graph3_remove_all_instances_of_vertex_from_vertex_set_cons(l, vl);
}

// Modified: Had to change the color values slightly, which is fine because they
// are constants and we don't rely on their values anywhere
uint64_t Spec_GC_infix_closure_ver3_white = 0ULL;

uint64_t Spec_GC_infix_closure_ver3_gray = 1ULL;

uint64_t Spec_GC_infix_closure_ver3_blue = 2ULL;

uint64_t Spec_GC_infix_closure_ver3_black = 3ULL;

uint64_t Spec_GC_infix_closure_ver3_getWosize(uint64_t h) { return h >> 10U; }

uint64_t Spec_GC_infix_closure_ver3_getColor(uint64_t h) {
  uint64_t c_ = h >> 8U;
  return c_ & 3ULL;
}

uint64_t Spec_GC_infix_closure_ver3_getTag(uint64_t h) { return h & 255ULL; }

uint64_t Spec_GC_infix_closure_ver3_makeHeader(uint64_t wz, uint64_t c,
                                               uint64_t tg) {
  uint64_t l1 = wz << 10U;
  uint64_t l2 = c << 8U;
  uint64_t l3 = tg << 0U;
  return l1 + l2 + l3;
}

uint64_t Spec_GC_infix_closure_ver3_hd_address(uint64_t st_index) {
  return st_index - 8ULL;
}

uint64_t Spec_GC_infix_closure_ver3_f_address(uint64_t h_index) {
  return h_index + 8ULL;
}

uint64_t
Spec_GC_infix_closure_ver3_extract_start_env_bits_(uint64_t clos_info) {
  uint64_t l1 = clos_info << 8U;
  return l1 >> 9U;
}

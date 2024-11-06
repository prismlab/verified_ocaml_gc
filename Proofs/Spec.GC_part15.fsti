module Spec.GC_part15

include Spec.GC_part14

open FStar.Seq
open FStar.Seq.Base

open FStar.Mul

open FStar.Endianness

//Machine integer
module Usize = FStar.UInt64

module U8 = FStar.UInt8

module U32 = FStar.UInt32

//Graph module
module G = Spec.Graph3

//DFS module
module D = DFS2


let props_reach (g:heap{well_formed_heap2 g /\
                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)})
                (g1:heap{well_formed_heap2 g1 /\
                        (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)})
                (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})
                (root_set : seq Usize.t{root_props g root_set})
                (f_index: Usize.t {f_id f_index /\
                                    Seq.mem (hd_address f_index) (objects2 0UL g1) /\
                                    isBlackObject1 (hd_address f_index) g1 /\
                                    G.vertex_mem f_index (create_graph_from_heap g).vertices /\
                                    (create_graph_from_heap g == create_graph_from_heap g1)})
                =
   (exists o (z1: G.reach (create_graph_from_heap g) o f_index) . Seq.mem o root_set /\
                  G.reachfunc (create_graph_from_heap g) o f_index z1)


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


#restart-solver

let succ_reach_transitive_lemma1_from_graph (g:heap{well_formed_heap2 g})
                                            (x: Usize.t)
                                            (o: Usize.t)
                            : Lemma
                                   (requires ((all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                             (let grph = create_graph_from_heap g in
                                             G.mem_graph_vertex grph o /\
                                             G.mem_graph_vertex grph x /\
                                             (exists (p: (G.reach grph o x)). G.reachfunc grph o x p))))
                                   (ensures
                                              (let grph = create_graph_from_heap g in
                                              (forall y. G.vertex_mem y (G.successors grph x) ==>
                                                  (exists (r1: G.reach grph o y).G.reachfunc grph o y r1)))) =

  let grph = create_graph_from_heap g in
  G.succ_reach_transitive_lemma1 grph o x;
  ()



#restart-solver

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000 --query_stats --using_facts_from '* -FStar.Seq' --split_queries on_failure"

(*All black objects in the heap resulted after mark is reachable from a root set, where the root set satisfies the reachability
  pre-conditions with respect to visited set and stack*)
/// XXX KC: This proof is flaky.
let all_black_objs_after_mark_is_reachable (g:heap{well_formed_heap2 g})
                                                  (st: seq Usize.t {stack_props_func g st})
                                                  (vl: seq Usize.t {vl_props_func g vl})
                                                  (root_set : seq Usize.t{root_props g root_set})

                 : Lemma
                   (requires  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                              (forall i x. Seq.mem x (get_allocated_block_addresses g) /\
                                           (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                           (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\

                              (
                                let allocs_g = get_allocated_block_addresses g in
                                let ff_address_g = first_field_addresses_of_allocated_blocks g allocs_g in
                                 (G.subset_vertices st ff_address_g) /\
                                 (G.subset_vertices vl ff_address_g) /\
                                 (G.subset_vertices root_set ff_address_g)) /\

                              (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                              (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\

                              (let grph = create_graph_from_heap g in
                              (forall o x (z2: G.reach grph o x). (G.reachfunc grph o x z2) /\ Seq.mem o root_set ==>
                               (Seq.mem x vl \/ (exists y (z3: G.reach grph y x). G.reachfunc grph y x z3 /\ Seq.mem y st))) /\

                               //Pre-condition to call dfs_backward lemma
                               (forall c b (r_cb: G.reach grph c b). (Seq.mem c vl /\ G.reachfunc grph c b r_cb /\ ~(c = b)) ==>
                                  (Seq.mem b vl \/ Seq.mem b st \/ (exists d. Seq.mem d st /\
                                   Seq.mem d (G.vertices_in_path grph c b r_cb)))) /\

                               //Pre-condition to call dfs_forward lemma
                               (forall x. Seq.mem x st ==> (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1))/\
                               (forall x. Seq.mem x vl ==> (exists o (z1: G.reach grph o x). Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)))

                   )
                  (ensures ( let grph = create_graph_from_heap g in
                             let g1 = mark5 g st in
                                 (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)))) =

  let grph = create_graph_from_heap g in
  let g1 = mark5 g st in
  dfs_mark_equivalence_lemma g st vl 3UL 2UL;
  assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                 Seq.mem x (D.dfs grph
                                            st
                                            vl)));
  D.dfs_equality_lemma grph st vl;

  assert (D.dfs grph st vl == D.dfs7 grph st vl);
  D.dfs7_lemma_backward grph st vl root_set;
  D.dfs_lemma_forward grph st vl root_set;

  assert ((forall x. Seq.mem x (D.dfs grph st vl) <==> (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)));

  assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 ==>
                (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)));
  ()

(*All successors of a black object in the heap after mark is reachable from some object in the root set if root set satisfies the
  reachability preconditions with respect to visited set and stack*)


#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries always"

open FStar.Classical

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let black_field_props (g:heap{well_formed_heap2 g /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)})
                      (g1:heap{well_formed_heap2 g1 /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)})
                      (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})
                      (root_set : seq Usize.t{root_props g root_set})
                      (f_index: Usize.t {f_id f_index /\
                                         Seq.mem (hd_address f_index) (objects2 0UL g1) /\
                                         isBlackObject1 (hd_address f_index) g1 /\
                                        Seq.mem f_index (create_graph_from_heap g).vertices /\
                                        create_graph_from_heap g == create_graph_from_heap g1}) =

(forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==>
                                       (exists o (z1: G.reach (create_graph_from_heap g) o x). Seq.mem o root_set /\
                                                      G.reachfunc (create_graph_from_heap g) o x z1) ==>
                                        Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1)


let black_field_props1 (g:heap{well_formed_heap2 g /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)})
                      (g1:heap{well_formed_heap2 g1 /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)})
                      (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})
                      (root_set : seq Usize.t{root_props g root_set})
                      (f_index: Usize.t {f_id f_index /\
                                         Seq.mem (hd_address f_index) (objects2 0UL g1) /\
                                         isBlackObject1 (hd_address f_index) g1 /\
                                        Seq.mem f_index (create_graph_from_heap g).vertices /\
                                        create_graph_from_heap g == create_graph_from_heap g1}) =

(forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==>
                      Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1)


#restart-solver

#restart-solver

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

let field_ptrs_of_a_black_obj_after_mark_is_black  (g:heap{well_formed_heap2 g /\
                                                          (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)})
                                                   (g1:heap{well_formed_heap2 g1 /\
                                                            (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)})
                                                   (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})
                                                   (vl: seq Usize.t {vl_props_func g vl})
                                                   (root_set : seq Usize.t{root_props g root_set})
                                                   (f_index: Usize.t {f_id f_index /\
                                                                      Seq.mem (hd_address f_index) (objects2 0UL g1) /\
                                                                      isBlackObject1 (hd_address f_index) g1 /\
                                                                      Seq.mem f_index (create_graph_from_heap g).vertices /\
                                                                      create_graph_from_heap g == create_graph_from_heap g1})
                 : Lemma
                   (requires  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1) /\
                              (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\

                              (
                                let allocs_g = get_allocated_block_addresses g in
                                let ff_address_g = first_field_addresses_of_allocated_blocks g allocs_g in
                                 (G.subset_vertices st ff_address_g) /\
                                 (G.subset_vertices vl ff_address_g) /\
                                 (G.subset_vertices root_set ff_address_g)) /\

                              (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                              (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\

                              (let grph = create_graph_from_heap g in
                              (forall o x (z2: G.reach grph o x). (G.reachfunc grph o x z2) /\ Seq.mem o root_set ==>
                               (Seq.mem x vl \/ (exists y (z3: G.reach grph y x). G.reachfunc grph y x z3 /\ Seq.mem y st))) /\

                               //Pre-condition to call dfs_backward lemma
                               (forall c b (r_cb: G.reach grph c b). (Seq.mem c vl /\ G.reachfunc grph c b r_cb /\ ~(c = b)) ==>
                                  (Seq.mem b vl \/ Seq.mem b st \/ (exists d. Seq.mem d st /\
                                   Seq.mem d (G.vertices_in_path grph c b r_cb)))) /\

                               //Pre-condition to call dfs_forward lemma
                               (forall x. Seq.mem x st ==> (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1))/\
                               (forall x. Seq.mem x vl ==> (exists o (z1: G.reach grph o x). Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)))

                   )
                  (ensures (black_field_props1 g g1 st root_set f_index)) =
  all_black_objs_after_mark_is_reachable g st vl root_set;
  let grph = create_graph_from_heap g in
  (*assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)));
  assert (Seq.mem (hd_address f_index) (objects2 0UL g1) /\
                   isBlackObject1 (hd_address f_index) g1);

  assert (Seq.mem f_index (create_graph_from_heap g).vertices);
  assert (create_graph_from_heap g == create_graph_from_heap g1);
  assert ((exists o (z1: G.reach grph o f_index) . Seq.mem o root_set /\
                                                   G.reachfunc grph o f_index z1));*)

  //Bring the witness of an o, to assert the reachability of successors of f_index
   let _ = exists_elim
           (forall y. Seq.mem y (G.successors (create_graph_from_heap g) f_index) ==>
                                                  (exists o (r1: G.reach (create_graph_from_heap g) o y).
                                                     Seq.mem o root_set /\ G.reachfunc (create_graph_from_heap g) o y r1))
           ()
           (fun (o:hp_addr{Seq.mem o root_set /\
                         (exists (z1: G.reach (create_graph_from_heap g) o f_index).
                             Seq.mem o root_set /\ G.reachfunc (create_graph_from_heap g) o f_index z1)}) ->

              assert (G.mem_graph_vertex grph o);
              assert (Seq.mem f_index grph.vertices);
              assert (G.mem_graph_vertex grph f_index);
              assert (exists (p: (G.reach grph o f_index)). G.reachfunc grph o f_index p);
              let _ = succ_reach_transitive_lemma1_from_graph g f_index o in
              ()) in
  assert ((forall y. Seq.mem y (G.successors (create_graph_from_heap g) f_index) ==>
                                                  (exists o (r1: G.reach (create_graph_from_heap g) o y).
                                                     Seq.mem o root_set /\ G.reachfunc (create_graph_from_heap g) o y r1)));


  (*assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                          G.reachfunc grph o x z1)));

  assert ((forall x. Seq.mem x (G.successors grph f_index) ==>
                                       (exists o (z1: G.reach grph o x). Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)));

  assert ((forall x. (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                G.reachfunc grph o x z1) ==>
                                Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1
                                       ));

  //assume (forall x. Seq.mem x (G.successors grph f_index) ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);

  assert (black_field_props g g1 st root_set f_index);

  assert (black_field_props1 g g1 st root_set f_index);

  (*assert (forall y. Seq.mem y (G.successors (create_graph_from_heap g) f_index) ==>
                                       (Seq.mem y (objects2 0UL g2)) /\ isBlackObject1 y g2);*)*)

  ()

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let black_pointer (g:heap{well_formed_heap2 g /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)})
                      (g1:heap{well_formed_heap2 g1 /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)})
                      (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})

                      (f_index: Usize.t) =

 f_id f_index /\
  Seq.mem (hd_address f_index) (objects2 0UL g1) /\
  isBlackObject1 (hd_address f_index) g1 /\
  Seq.mem f_index (create_graph_from_heap g).vertices /\
  create_graph_from_heap g == create_graph_from_heap g1

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let black_field_props1_all (g:heap{well_formed_heap2 g /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)})
                      (g1:heap{well_formed_heap2 g1 /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)})
                      (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})
                      (root_set : seq Usize.t{root_props g root_set}) =

forall (x:Usize.t). black_pointer g g1 st x ==> black_field_props1 g g1 st root_set x

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

#restart-solver

#restart-solver

let field_ptrs_black_all  (g:heap{well_formed_heap2 g /\
                                                          (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)})
                                                   (g1:heap{well_formed_heap2 g1 /\
                                                            (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)})
                                                   (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})
                                                   (vl: seq Usize.t {vl_props_func g vl})
                                                   (root_set : seq Usize.t{root_props g root_set})

                 : Lemma
                   (requires  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1) /\
                              (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\

                              (
                                let allocs_g = get_allocated_block_addresses g in
                                let ff_address_g = first_field_addresses_of_allocated_blocks g allocs_g in
                                 (G.subset_vertices st ff_address_g) /\
                                 (G.subset_vertices vl ff_address_g) /\
                                 (G.subset_vertices root_set ff_address_g)) /\

                              (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                              (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\

                              (let grph = create_graph_from_heap g in
                              (forall o x (z2: G.reach grph o x). (G.reachfunc grph o x z2) /\ Seq.mem o root_set ==>
                               (Seq.mem x vl \/ (exists y (z3: G.reach grph y x). G.reachfunc grph y x z3 /\ Seq.mem y st))) /\

                               //Pre-condition to call dfs_backward lemma
                               (forall c b (r_cb: G.reach grph c b). (Seq.mem c vl /\ G.reachfunc grph c b r_cb /\ ~(c = b)) ==>
                                  (Seq.mem b vl \/ Seq.mem b st \/ (exists d. Seq.mem d st /\
                                   Seq.mem d (G.vertices_in_path grph c b r_cb)))) /\

                               //Pre-condition to call dfs_forward lemma
                               (forall x. Seq.mem x st ==> (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1))/\
                               (forall x. Seq.mem x vl ==> (exists o (z1: G.reach grph o x). Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)))

                   )
                   (ensures (black_field_props1_all g g1 st root_set))=

 Classical.forall_intro (Classical.move_requires (field_ptrs_of_a_black_obj_after_mark_is_black g g1 st vl root_set));
 assert (forall (x:Usize.t). black_pointer g g1 st x ==> black_field_props1 g g1 st root_set x);
 assert (black_field_props1_all g g1 st root_set);
 ()


#reset-options "--z3rlimit 500"



let field_reads_equal_lemma1 (g:heap{Seq.length (objects2 0UL g) > 0})
                             (g':heap)
                             (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                             (x:hp_addr{Seq.mem x (objects2 0UL g) /\ x <> h_index})
                             (y:hp_addr{Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword)})
                  : Lemma
                    (requires (objects2 0UL g == objects2 0UL g') /\

                              (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                    (ensures (read_word g y == read_word g' y)) =
 assert (~(Seq.mem y (objects2 0UL g)));
 assert (y <> h_index);
 assert (read_word g y == read_word g' y);
 assert (Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y);
()

let field_reads_equal_h_index_lemma1 (g:heap{Seq.length (objects2 0UL g) > 0})
                                     (g':heap)
                                     (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                     (y:hp_addr{Usize.v y >= Usize.v h_index + Usize.v mword /\
                                       Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword)})
                  : Lemma
                    (requires (objects2 0UL g == objects2 0UL g') /\
                              (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                    (ensures (read_word g y == read_word g' y)) =
assert (~(Seq.mem y (objects2 0UL g)));
assert (y <> h_index);
assert (read_word g y == read_word g' y);
()

#restart-solver

let field_reads_all_equal_lemma1 (g:heap{Seq.length (objects2 0UL g) > 0})
                                 (g':heap)
                                 (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                 (x:hp_addr{Seq.mem x (objects2 0UL g) /\ x <> h_index})
                      : Lemma
                        (requires (objects2 0UL g == objects2 0UL g') /\
                              (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                        (ensures (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                        read_word g y == read_word g' y)) =
 Classical.forall_intro (Classical.move_requires (field_reads_equal_lemma1 g g' h_index x))


#restart-solver

let field_reads_all_equal_h_index_lemma1 (g:heap{Seq.length (objects2 0UL g) > 0})
                                         (g':heap)
                                         (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                            : Lemma
                              (requires (objects2 0UL g == objects2 0UL g') /\
                                        (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                              (ensures (forall y. Usize.v y >= Usize.v h_index + Usize.v mword /\
                                             Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword) ==>
                                                   read_word g y == read_word g' y)) =
 Classical.forall_intro (Classical.move_requires (field_reads_equal_h_index_lemma1 g g' h_index))

#restart-solver

let field_reads_all_equal_for_all_objects_lemma1 (g:heap{Seq.length (objects2 0UL g) > 0})
                                                 (g':heap)
                                                 (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                 :Lemma
                                 (requires (objects2 0UL g == objects2 0UL g') /\
                                          (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))

                                 (ensures (forall x y. Seq.mem x (get_allocated_block_addresses g) ==>
                                               (Usize.v y >= Usize.v x + Usize.v mword /\
                                               Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y)))  =
Classical.forall_intro (Classical.move_requires (field_reads_all_equal_lemma1 g g' h_index));
(field_reads_all_equal_h_index_lemma1 g g' h_index);
assert (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y);

assert (forall x y. Seq.mem x (objects2 0UL g) ==>
                     (Usize.v y >= Usize.v x + Usize.v mword /\
                      Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y));
assert (forall x y. Seq.mem x (get_allocated_block_addresses g) ==>
                     (Usize.v y >= Usize.v x + Usize.v mword /\
                      Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y));

()

let field_reads_equal (g:heap{Seq.length (objects2 0UL g) > 0})
                      (g':heap{Seq.length (objects2 0UL g') > 0}) =

  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                                     read_word g y == read_word g' y)


let field_reads_equal_new_lemma (g:heap{Seq.length (objects2 0UL g) > 0})
                                (g':heap)
                                (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                        : Lemma
                          (requires (objects2 0UL g == objects2 0UL g') /\
                                    (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                               Seq.mem x (get_allocated_block_addresses g)))
                          (ensures field_reads_equal g g') =
 field_reads_all_equal_for_all_objects_lemma1 g g' h_index;
 assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g));
 assert (field_reads_equal g g');
 ()


#restart-solver


#reset-options "--z3rlimit 500"

#restart-solver

#restart-solver

 let colorHeader3_black_object_colored_white_lemma (v_id:hp_addr)
                                                   (g:heap{Seq.length (objects2 0UL g) > 0})
                                                   (c:color)
                         : Lemma
                           (requires (c == white) /\
                                     (mem v_id (objects2 0UL g)) /\
                                     (color_of_object1 v_id g == black))

                           (ensures  (let g' = colorHeader3 v_id g c in
                                      let allocs = (get_allocated_block_addresses g) in
                                      let allocs' = (get_allocated_block_addresses g') in
                                      (forall x. Seq.mem x allocs' ==>
                                                 Seq.mem x allocs) /\
                                      (forall x. Seq.mem x allocs' ==>
                                                 getWosize(read_word g x) == getWosize(read_word g' x)) /\
                                      (forall x. Seq.mem x allocs' ==>
                                                 getTag(read_word g x) == getTag(read_word g' x)) /\
                                      field_reads_equal g g')) =
  let allocs = get_allocated_block_addresses g in
  let g' = colorHeader3 v_id g c in
  assert (heap_remains_same_except_index_v_id v_id g g');

  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    getWosize(read_word g x) == getWosize(read_word g' x));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    getTag(read_word g x) == getTag(read_word g' x));

  field_reads_equal_new_lemma g g' v_id;
  assert (field_reads_equal g g');
  ()


let colorHeader3_white_object_colored_blue_lemma1  (v_id:hp_addr)
                                                   (g:heap{Seq.length (objects2 0UL g) > 0})
                                                   (c:color)
                         : Lemma
                           (requires (c == blue) /\
                                     (mem v_id (objects2 0UL g)) /\
                                     (color_of_object1 v_id g == white)
                                     )
                           (ensures  (let g' = colorHeader3 v_id g c in
                                      (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                           getWosize(read_word g x) == getWosize(read_word g' x)) /\
                                      (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                           getTag(read_word g x) == getTag(read_word g' x)) /\
                                      (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                           Seq.mem x (get_allocated_block_addresses g)) /\
                                      field_reads_equal g g')) =
  let allocs = get_allocated_block_addresses g in
  let g' = colorHeader3 v_id g c in
  assert (heap_remains_same_except_index_v_id v_id g g');
  assert ((Seq.mem v_id (get_allocated_block_addresses g)));
  assert (~(Seq.mem v_id (get_allocated_block_addresses g')));
  assert  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\
                         Usize.v y >= Usize.v x + Usize.v mword /\
                         Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                                     read_word g y == read_word g' y);

  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    getWosize(read_word g x) == getWosize(read_word g' x));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    getTag(read_word g x) == getTag(read_word g' x));

  ()



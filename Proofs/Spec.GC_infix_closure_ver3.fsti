/// ---------------------------------------------------------------------------------------------------------------------------------------------------------------
/// GC with closure and infix tag checks
/// ---------------------------------------------------------------------------------------------------------------------------------------------------------------

module Spec.GC_infix_closure_ver3

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

#reset-options "--z3rlimit 1000 --z3seed 42 --query_stats --using_facts_from '* -FStar.Seq' --split_queries always"

(*All black objects in the heap resulted after mark is reachable from a root set, where the root set satisfies the reachability
  pre-conditions with respect to visited set and stack*)
/// XXX KC: This proof is flaky.
let all_black_objs_after_mark_is_reachable (g:heap{well_formed_heap2 g})
                                                  (st: seq Usize.t {stack_props_func g st})
                                                  (vl: seq Usize.t {vl_props_func g vl})
                                                  (root_set : seq Usize.t{root_props g root_set})
                                                  (c:color{c == 3UL})
                                                  (c1:color{c1 == 2UL})

                 : Lemma
                   (requires  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
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
                  (ensures ( let grph = create_graph_from_heap g in
                             let g1 = mark5 g st in
                                 (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)))) =

  let grph = create_graph_from_heap g in
  let g1 = mark5 g st in
  dfs_mark_equivalence_lemma g st vl c c1;
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

                                                   (c:color{c == 3UL})
                                                   (c1:color{c1 == 2UL})
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
  all_black_objs_after_mark_is_reachable g st vl root_set c c1;
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

                                                   (c:color{c == 3UL})
                                                   (c1:color{c1 == 2UL})

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

 Classical.forall_intro (Classical.move_requires (field_ptrs_of_a_black_obj_after_mark_is_black g g1 st vl root_set c c1));
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

#reset-options "--split_queries always"

let colorHeader3_blue_object_colored_blue_lemma1  (v_id:hp_addr)
                                                  (g:heap{Seq.length (objects2 0UL g) > 0})
                                                  (c:color)
                         : Lemma
                           (requires (c == blue) /\
                                     (mem v_id (objects2 0UL g)) /\
                                     (color_of_object1 v_id g == blue)
                                     )
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
  assert (~(Seq.mem v_id (get_allocated_block_addresses g)));
  assert (~(Seq.mem v_id (get_allocated_block_addresses g')));

  (*Field reads of all allocated blocks in g' remains the same between g and g'*)
  assert  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\
                         Usize.v y >= Usize.v x + Usize.v mword /\
                         Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                                     read_word g y == read_word g' y);
  (*assert (forall (x:Usize.t {Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). x <> v_id ==>
                  read_word g x == read_word g' x);*)

  (*The the header reads of all allocated objects in g' renains the same between g and g'*)
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                  read_word g x == read_word g' x);

  (*All allocated objects in g' is present as allocated objects in g*)
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g));

  ()

#reset-options "--z3rlimit 500"

let write_word_to_blue_object_field_lemma3 (g:heap{write_word_to_blue_object_field_lemma_props1 g /\
                                                   Seq.length (objects2 0UL g) > 0})
                                           (x:hp_addr{first_field_of_blue g x})
                                           (v:hp_addr{first_field_of_any g v})
                          : Lemma
                            (requires True)

                             (ensures  (let g' = write_word g x v in
                                        (objects2 0UL g == objects2 0UL g') /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\
                                        (forall p. Seq.mem p (get_allocated_block_addresses g') ==>
                                                   read_word g' p ==  read_word g p) /\
                                        (Seq.length (objects2 0UL g') > 0) /\
                                         field_reads_equal g g')) =
  let g' = write_word g x v in
  write_word_lemma1 g x v;
  fields_not_mem_objs_lemma g g' (hd_address x) x;

  assert(~(Seq.mem x (objects2 0UL g)));
  assert(~(Seq.mem x (get_allocated_block_addresses g)));
  write_word_to_blue_object_field_lemma g x v;

  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                    Seq.mem x (get_allocated_block_addresses g'));

  (*This assert ensures that, the header value remains the same between the two heaps with a field write*)
  assert (header_value_does_not_change_with_a_field_write g x v);

  assert (forall p. Seq.mem p (objects2 0UL g) ==> read_word (write_word g x v) p ==  read_word g p);

  assert (forall p. Seq.mem p (get_allocated_block_addresses g) ==> read_word (write_word g x v) p ==  read_word g p);

  assert (forall p. Seq.mem p (get_allocated_block_addresses g') ==> read_word g' p ==  read_word g p);

  (*This assert ensures that, the field reads of all non-blue objects remains the same between the two heaps*)
  assert (write_to_the_firstfield_of_blue_object_preserves_the_field_reads_of_all_non_blue_objects g x v);

  assert (field_reads_equal g g');
  ()

#restart-solver

let sweep_body_with_free_list_well_formedness_parts_lemma1
                              (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\
                                     write_word_to_blue_object_field_lemma_props1 g})
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\
                                                Seq.mem (hd_address f_index) (objects2 0UL g)})
                              (fp:hp_addr{Usize.v fp >= Usize.v mword /\
                                           Seq.mem (hd_address fp) (objects2 0UL g) /\
                                           color_of_object1 (hd_address fp) g == blue /\
                                          (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                          Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
              : Lemma
                (requires True)

                (ensures (let g' =  fst (sweep_body_with_free_list g f_index fp) in
                                      let allocs' = (get_allocated_block_addresses g') in
                                       (forall x. Seq.mem x allocs' ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\

                                        (forall x. Seq.mem x allocs' ==>
                                                   getWosize(read_word g' x) == getWosize(read_word g x)) /\
                                        (forall x. Seq.mem x allocs' ==>
                                                   getTag(read_word g' x) == getTag(read_word g x)) /\
                                        (Seq.length (objects2 0UL g') > 0) /\
                                         field_reads_equal g g')) =
 let h_index = hd_address f_index in
 let c = getColor (read_word g h_index) in

 if (c = white || c = blue) then
 (
   let g' = colorHeader3 h_index g blue in
  if c = white then
   (
      colorHeader3_white_object_colored_blue_lemma1 h_index g blue;
      let allocs' = get_allocated_block_addresses g' in
      assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                   getWosize(read_word g x) == getWosize(read_word g' x)) /\
              (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                           getTag(read_word g x) == getTag(read_word g' x)) /\
              (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                    Seq.mem x (get_allocated_block_addresses g)) /\
              field_reads_equal g g');
      assert (Seq.length (objects2 0UL g') > 0);

      let g1 = write_word g' fp f_index in
      write_word_to_blue_object_field_lemma g' fp f_index;
      write_word_to_blue_object_field_lemma3 g' fp f_index;

      assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                                                   Seq.mem x (get_allocated_block_addresses g')) /\
                                        (forall p. Seq.mem p (get_allocated_block_addresses g1) ==>
                                                   read_word g1 p ==  read_word g' p) /\
                                        (Seq.length (objects2 0UL g1) > 0) /\
                                         field_reads_equal g' g1);
      assert (Seq.length (objects2 0UL g1) > 0);
      assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                                                   Seq.mem x (get_allocated_block_addresses g)));
      assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                       getWosize(read_word g1 x) == getWosize(read_word g x)));
      assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                       getTag(read_word g1 x) == getTag(read_word g x)));
      assert (field_reads_equal g g1);
      ()
   )
   else
   (
    colorHeader3_blue_object_colored_blue_lemma1 h_index g blue;
    let allocs' = get_allocated_block_addresses g' in

    assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                   getWosize(read_word g x) == getWosize(read_word g' x)) /\
              (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                           getTag(read_word g x) == getTag(read_word g' x)) /\
              (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                    Seq.mem x (get_allocated_block_addresses g)) /\
              field_reads_equal g g');

    let g1 = write_word g' fp f_index in
    write_word_to_blue_object_field_lemma g' fp  f_index;
    write_word_to_blue_object_field_lemma3 g' fp f_index;

    assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                                                   Seq.mem x (get_allocated_block_addresses g')) /\
                                        (forall p. Seq.mem p (get_allocated_block_addresses g1) ==>
                                                   read_word g1 p ==  read_word g' p) /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                                                   getWosize(read_word g1 x) == getWosize(read_word g' x)) /\
                                        (Seq.length (objects2 0UL g1) > 0) /\
                                         field_reads_equal g' g1);
    assert (Seq.length (objects2 0UL g1) > 0);
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                                                   Seq.mem x (get_allocated_block_addresses g)));
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                       getWosize(read_word g1 x) == getWosize(read_word g x)));
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                       getTag(read_word g1 x) == getTag(read_word g x)));
    assert (field_reads_equal g g1);
    ()
   )
 )
 else
 (
   assert (c == black);
   let g' = colorHeader3 h_index g white in
   colorHeader3_black_object_colored_white_lemma h_index g white;
   let allocs = (get_allocated_block_addresses g) in
   let allocs' = (get_allocated_block_addresses g') in
   assert ((forall x. Seq.mem x allocs' ==>
                              Seq.mem x allocs) /\
           (forall x. Seq.mem x allocs' ==>
                               getWosize(read_word g x) == getWosize(read_word g' x)) /\
          (forall x. Seq.mem x allocs' ==>
                                getTag(read_word g x) == getTag(read_word g' x)) /\
                                      field_reads_equal g g');

   assert (Seq.length (objects2 0UL g') > 0);

   assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) (*/\
          (forall p. Seq.mem p (get_allocated_block_addresses g') ==>
                                                   read_word g' p ==  read_word g p)*) /\
          (Seq.length (objects2 0UL g') > 0) /\
           field_reads_equal g g');
   ()
 )

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let rec sweep_with_free_list3_well_formedness_part_lemma1
                              (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0)})

                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)/\
                                             (Seq.length (objects2 (hd_address f_index) g) > 0)
                              })

                             (fp:hp_addr{Usize.v fp >= Usize.v mword /\
                                         Seq.mem (hd_address fp) (objects2 0UL g) /\
                                         color_of_object1 (hd_address fp) g == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
                         : Lemma
                           (requires ( forall p. Seq.mem p (objects2 0UL g) ==> Usize.v (getWosize (read_word g p)) > 0))
                           (ensures (let g' =  fst (sweep_with_free_list3 g f_index fp) in
                                      let allocs' = (get_allocated_block_addresses g') in
                                       (forall x. Seq.mem x allocs' ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\

                                        (forall x. Seq.mem x allocs' ==>
                                                   getWosize(read_word g' x) == getWosize(read_word g x)) /\
                                        (forall x. Seq.mem x allocs' ==>
                                                   getTag(read_word g' x) == getTag(read_word g x)) /\
                                        (Seq.length (objects2 0UL g') > 0) /\
                                         field_reads_equal g g'))
                             (decreases (heap_size - Usize.v f_index)) =

 let h_index = hd_address f_index in
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let f_index_new =  Usize.add h_index_new mword in
 wosize_plus_one_times_mword_multiple_of_mword wz;
 assert (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0);
 //assert (Usize.v h_index_new % Usize.v mword == 0);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index_new mword;

 let g', fp' = sweep_body_with_free_list g f_index fp in
 sweep_body_with_free_list_lemma5 g f_index fp;

 let allocs' = get_allocated_block_addresses g' in
 sweep_body_with_free_list_well_formedness_parts_lemma1 g f_index fp;

 assert((forall x. Seq.mem x allocs' ==>
                   Seq.mem x (get_allocated_block_addresses g)) /\
        (forall x. Seq.mem x allocs' ==>
                   getWosize(read_word g' x) == getWosize(read_word g x)) /\
        (forall x. Seq.mem x allocs' ==>
                   getTag(read_word g' x) == getTag(read_word g x)) /\
        (Seq.length (objects2 0UL g') > 0) /\
        field_reads_equal g g');

 if Usize.v f_index_new >= heap_size then
 (

   objects2_cons_lemma2 h_index g;

   objects2_sweep_lemma3 h_index g;
   assert (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g)));
   assert (~(Seq.mem h_index_new (objects2 h_index g)));
   objects2_sweep_lemma4 h_index g;
   assert (~(Seq.mem h_index_new (objects2 h_index g)) /\ (Seq.length (objects2 (hd_address f_index) g) > 0) ==> Seq.length (objects2 h_index g) == 1);
   assert (Seq.length (objects2 h_index g) == 1);
   objects2_property_lemma g h_index;

   ()

 )
 else
 (
   objects2_mem_lemma1_app1 h_index g;
   objects2_length_lemma3 g' h_index h_index_new;
   let g'',fp'' = sweep_with_free_list3 g' f_index_new fp' in
   sweep_with_free_list3_well_formedness_part_lemma1 g' f_index_new fp';

   let allocs'' = get_allocated_block_addresses g'' in
   assert((forall x. Seq.mem x allocs'' ==>
                   Seq.mem x (get_allocated_block_addresses g')) /\
        (forall x. Seq.mem x allocs'' ==>
                   getWosize(read_word g'' x) == getWosize(read_word g' x)) /\
        (forall x. Seq.mem x allocs'' ==>
                   getTag(read_word g'' x) == getTag(read_word g' x)) /\
        (Seq.length (objects2 0UL g'') > 0) /\
        field_reads_equal g' g'');

  assert((forall x. Seq.mem x allocs'' ==>
                   Seq.mem x (get_allocated_block_addresses g)) /\
        (forall x. Seq.mem x allocs'' ==>
                   getWosize(read_word g'' x) == getWosize(read_word g x)) /\
        (forall x. Seq.mem x allocs'' ==>
                   getTag(read_word g'' x) == getTag(read_word g x)) /\
        (Seq.length (objects2 0UL g'') > 0) /\
        field_reads_equal g g'');
   ()


)
(*Proved the following for sweep
   1. The allocated object set after sweep is a subset of the allocated object set before sweep
   2. The wosize and tag of allocated object set remains the same with respect to their original values
   3. The field reads of allocated objects stayed back after sweep, is preserved after the sweep
 Proved the following after mark
   1. All field pointers of all black objects after mark is colored black
   2. All black objects <===> white after sweep

 For proving two properties of well-formedness, the sweep properties are sufficient.
 For proving the field points to allocated objs property, we need to prove the color of the field pointers are white.
 This can be proved from the mark property. But that alone is not sufficient, because the field points to blocks to is a
 recusrsive function, hence an induction proof is necessary.*)

(*Invariants and Specifications for incremental GC based on Yuasa write barrier
   1. The old reference is greyed ===> they are put to mark stack ----> Done by write barrier
   2. The new allocations are colored black

  Weak Tri-color invariant
  All black to white ==> pointed by a grey node through a chain of white references*)
(*ISMM - GC papers, co-located with PLDI
  Functional high performance computiong - workshop at ICFP, they think about GC
  Encrypted heap. How do we garbage collect?
  Combine GC with reference counting, how do you combine both in the same set up?
  80% research oriented, 20% engineering.*)


(*#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver*)

#reset-options "--z3rlimit 500"

let sweep_body_with_free_list_well_formedness_parts_lemma1_pre
                              (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\
                                     write_word_to_blue_object_field_lemma_props1 g})

                              (fp:hp_addr{Usize.v fp >= Usize.v mword /\
                                           Seq.mem (hd_address fp) (objects2 0UL g) /\
                                           color_of_object1 (hd_address fp) g == blue /\
                                          (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                          Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
                              (g':heap{g' == fst (sweep_body_with_free_list g mword fp)}) =
 let allocs' = (get_allocated_block_addresses g') in
                                       (forall x. Seq.mem x allocs' ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\

                                        (forall x. Seq.mem x allocs' ==>
                                                   getWosize(read_word g' x) == getWosize(read_word g x)) /\
                                        (forall x. Seq.mem x allocs' ==>
                                                   getTag(read_word g' x) == getTag(read_word g x)) /\
                                        (Seq.length (objects2 0UL g') > 0) /\
                                         field_reads_equal g g'


#restart-solver
#restart-solver

let pre_condition_sweep (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\
                         write_word_to_blue_object_field_lemma_props1 g}) =
let f_index = mword in
                                      let h_index = hd_address f_index in
                                      let wz =  getWosize (read_word g h_index) in
                                      let h_index_new = Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword)  in
                                      let f_index_new =  Usize.add h_index_new mword in
                                       (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g))) /\
                                       (~(Seq.mem h_index_new (objects2 h_index g)) /\ (Seq.length (objects2 (hd_address f_index) g) > 0) ==>
                                       Seq.length (objects2 h_index g) == 1)

#reset-options "--z3rlimit 500"

let field_reads_of_allocs_of_two_heaps_are_equal  (g:heap{Seq.length (objects2 0UL g) > 0})
                                                  (g':heap{Seq.length (objects2 0UL g') > 0})

                                                  (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g')) /\

                                                                  (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g' x)))})=
      (forall x y. Seq.mem x f' /\
                   Usize.v y >= Usize.v x + Usize.v mword /\
                   Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                                     read_word g y == read_word g' y)



#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let sweep_body_with_free_list_well_formedness_lemma
                              (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\
                                     write_word_to_blue_object_field_lemma_props1 g})
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)/\
                                             (Seq.length (objects2 (hd_address f_index) g) > 0)
                              })
                              (fp:hp_addr{Usize.v fp >= Usize.v mword /\
                                           Seq.mem (hd_address fp) (objects2 0UL g) /\
                                           color_of_object1 (hd_address fp) g == blue /\
                                          (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                          Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
              : Lemma
                (requires  (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                          (check_well_formed_closure_objs g (get_allocated_block_addresses g) == true))
                (ensures  (well_formed_heap2 (fst (sweep_with_free_list3 g mword fp)))) =
  let g' = (fst (sweep_with_free_list3 g mword fp)) in
  assert (forall x. Seq.mem x (objects2 0UL g) ==> Usize.v (getWosize (read_word g x)) > 0);

  sweep_with_free_list3_well_formedness_part_lemma1 g mword fp;
  assert (let allocs' = (get_allocated_block_addresses g') in
          (forall x. Seq.mem x allocs' ==>
                            Seq.mem x (get_allocated_block_addresses g)) /\

          (forall x. Seq.mem x allocs' ==>
                            getWosize(read_word g' x) == getWosize(read_word g x)) /\
          (forall x. Seq.mem x allocs' ==>
                            getTag(read_word g' x) == getTag(read_word g x)) /\
          (Seq.length (objects2 0UL g') > 0) /\
          field_reads_equal g g');
  check_well_formed_closure_objs_lemma2 g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
  assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g)) /\
        (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                   getWosize (read_word g x) == getWosize (read_word g' x)));
  assert (field_reads_of_allocs_of_two_heaps_are_equal g g' (get_allocated_block_addresses g'));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
  check_all_block_fields_within_limit2_lemma_for_sweep g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
  assert (check_all_block_fields_within_limit2 g' (get_allocated_block_addresses g'));
  assert (check_well_formed_closure_objs g' (get_allocated_block_addresses g'));

  (*Prove this*)
  assume (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    is_fields_points_to_blocks2 x g' (getWosize (read_word g' x)) (get_allocated_block_addresses g'));

  assert ((check_fields_points_to_blocks2 g' (get_allocated_block_addresses g')));
  assert (well_formed_heap2 g');
  ()

(*************************************REMOVE SWEEP WITH FREELIST AND COALESCING************************************************)
(*Sweep with freelist and coalescing*)
let sweep_body_with_free_list_and_coalescing (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ write_word_to_blue_object_field_lemma_props1 g})
                                             (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\
                                                              Seq.mem (hd_address f_index) (objects2 0UL g)})
                                             (fp:hp_addr{Usize.v fp >= Usize.v mword /\
                                                         Seq.mem (hd_address fp) (objects2 0UL g) /\
                                                         color_of_object1 (hd_address fp) g == blue /\
                                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
            : Tot (p:heap_heap_addr_pair) =

 let h_index = hd_address f_index in
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white || c = blue) then
 (
   let g' = colorHeader3 h_index g blue in
   assert (objects2 0UL g == objects2 0UL g');

   assert (Usize.v fp % Usize.v mword == 0);

   let hd_fp = hd_address fp in
   let fp_wz_sz = getWosize (read_word g' hd_fp) in
   let fp_wz_sz' = getWosize (read_word g hd_fp) in
   assert (fp_wz_sz == fp_wz_sz');
   let fp_color = getColor (read_word g' hd_fp) in
   assert (fp_color == blue);
   let fp_wz_sz_plus_one = Usize.add fp_wz_sz 1UL in
   let next_obj_offset = Usize.mul fp_wz_sz_plus_one mword in
   let next_obj = Usize.add fp next_obj_offset in
   if (next_obj = f_index) then
   (
     let hd_f_index = hd_address f_index in
     let f_index_wz = getWosize (read_word g' hd_f_index) in
     let f_index_wz' = getWosize (read_word g hd_f_index) in
     assert (f_index_wz == f_index_wz');
     assert (Seq.mem hd_fp (objects2 0UL g') /\ Seq.mem hd_f_index (objects2 0UL g));
     let new_wz = Usize.add fp_wz_sz f_index_wz in
     let tg = getTag (read_word g' hd_fp) in

     assert (Usize.v new_wz <= Usize.v max_wosize);
     let h = makeHeader new_wz fp_color tg in
     let g1 = write_word g' hd_fp h in
     write_word_lemma g' hd_fp h;
     write_word_lemma1 g' hd_fp h;
     assert (forall (i:hp_addr). i <> hd_fp ==> getWosize (read_word g1 i) == getWosize (read_word g' i));
     assert (forall (i:Usize.t{Usize.v i < heap_size /\ Usize.v i % 8 == 0}). i <> hd_fp ==>  getWosize (read_word g' i) == getWosize (read_word g1 i));
     assert (Usize.v new_wz < heap_size);
     let fp_color1 = getColor (read_word g1 hd_fp) in
     assert (fp_color1 == blue);
     let wd_sz = getWosize (read_word g1 hd_fp) in
     assert (wd_sz == new_wz);
     assert (Usize.v new_wz > 0);
     assert (Seq.length (objects2 0UL g) > 0);
     assert (Seq.length (objects2 0UL g') > 0);
     assert (Seq.mem hd_fp (objects2 0UL g));
     assert (Seq.mem hd_fp (objects2 0UL g'));
     assert (Seq.length (objects2 0UL g') > 0);
     assert (Usize.v (getWosize (read_word g' hd_fp)) > 0);
     assert (Usize.v (getWosize (read_word g1 hd_fp)) > 0);
     assert (Usize.v hd_fp + ((Usize.v (getWosize (read_word g1 hd_fp)) +  1) * Usize.v mword) <= heap_size);
     let hd_fp_next =  Usize.add hd_fp (Usize.mul (Usize.add (getWosize (read_word g1 hd_fp)) 1UL) mword) in
     assert (Usize.v hd_fp_next <= heap_size);
     assert (forall x. Seq.mem x (objects2 0UL g') /\ x <> hd_fp ==>  getWosize (read_word g' x) == getWosize (read_word g1 x));
     assert (forall x. Seq.mem x (objects2 0UL g') ==> Usize.v (getWosize (read_word g' x)) > 0);
     assert (forall x. Seq.mem x (objects2 0UL g') /\ x <> hd_fp ==> Usize.v (getWosize (read_word g1 x)) > 0);
     assert (Usize.v (getWosize (read_word g1 hd_fp)) > 0);
     assume (forall x. Seq.mem x (objects2 0UL g') ==> Usize.v x + Usize.v (getWosize (read_word g' x)) < heap_size);//Prove this from obects2 set construction
     assert (forall x. Seq.mem x (objects2 0UL g') /\ x <> hd_fp ==>  Usize.v x + Usize.v (getWosize (read_word g' x)) < heap_size);
     assert (Usize.v hd_fp + Usize.v (getWosize (read_word g' hd_fp)) < heap_size);
     assert (Usize.v hd_fp + Usize.v (getWosize (read_word g1 hd_fp)) < heap_size);
     assert (forall x. Seq.mem x (objects2 0UL g') /\ x <> hd_fp ==>  Usize.v x + Usize.v (getWosize (read_word g1 x)) < heap_size);
     (g1,fp)

   )
   else
   (
     let g1 = write_word g' fp f_index in
     //write_word_to_blue_object_field_lemma1 g' fp f_index;
     write_word_to_blue_object_field_lemma g' fp  f_index;
     //assert (well_formed_heap2 g1);
     assert (objects2 0UL g == objects2 0UL g');
     assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
     (g1,f_index)

   )
 )
 else
 (
   assert (c == black);
   let g' = colorHeader3 h_index g white in
   assert (objects2 0UL g == objects2 0UL g');

   //assert (well_formed_heap2 g');
   assert (Usize.v fp >= Usize.v mword);
   //assert (is_valid_header (hd_address fp) g');
   assert (color_of_object1 (hd_address fp) g == blue);
   assert (color_of_object1 (hd_address fp) g' == blue);
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   (g',fp)
 )

#restart-solver

#push-options "--split_queries always"


let rec sweep_with_free_list_coalescing (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0)})

                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)(*/\
                                             (Seq.length (objects2 (hd_address f_index) g) > 0)*)
                              })

                             (fp:hp_addr{Usize.v fp >= Usize.v mword /\
                                         Seq.mem (hd_address fp) (objects2 0UL g) /\
                                         color_of_object1 (hd_address fp) g == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
          : Tot (p:heap_heap_addr_pair)
           (decreases (heap_size - Usize.v f_index)) =

 let h_index = hd_address f_index in
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let f_index_new =  Usize.add h_index_new mword in
 wosize_plus_one_times_mword_multiple_of_mword wz;
 assert (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0);
 assert (Usize.v h_index_new % Usize.v mword == 0);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index_new mword;

 assert (Usize.v (Usize.add h_index_new mword) % Usize.v mword == 0);
 assert (Usize.v f_index_new % Usize.v mword == 0);

 let g', fp' = sweep_body_with_free_list_and_coalescing g f_index fp in
 assume (noGreyObjects g' /\ (Seq.length (objects2 0UL g') > 0));
 assume (Usize.v fp' >= Usize.v mword /\
        Seq.mem (hd_address fp') (objects2 0UL g') /\
        color_of_object1 (hd_address fp') g' == blue /\
       (forall x y. Seq.mem x (objects2 0UL g') /\ Seq.mem y (objects2 0UL g') ==>
                         Usize.v (getWosize (read_word g' x)) + Usize.v (getWosize (read_word g' y)) < heap_size));

 if Usize.v f_index_new >= heap_size then
 (
   (g',fp')
 )
 else
 (
   //assert (h_index_new = hd_address f_index_new);
   assert (Usize.v f_index_new < heap_size);
   assert (Usize.v f_index_new >= Usize.v mword);
   assert (UInt.fits (Usize.v f_index_new - Usize.v mword) Usize.n);

   assert (Seq.length (objects2 0UL g) > 0 /\ Seq.mem h_index (objects2 0UL g));
   objects2_mem_lemma1_app1 h_index g;
   assert (Seq.mem h_index_new (objects2 0UL g));
   //assume (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   assert (h_index_new <> h_index);
   //assert (Seq.mem h_index_new (objects2 0UL g'));


   assert (Usize.v f_index_new >= Usize.v mword);
   //assert (Seq.mem h_index_new (objects2 0UL g'));
   assert (Usize.v f_index_new % Usize.v mword == 0);
   assert (Usize.v f_index_new < heap_size);
   assert (is_hp_addr f_index_new);
   assert (Usize.v h_index_new < heap_size);
   assert (Seq.length (objects2 0UL g') > 0);

   assume (mem (hd_address f_index_new) (objects2 0UL g'));
   let g'',fp'' = sweep_with_free_list_coalescing g' f_index_new fp' in
   (g'',fp'')
 )


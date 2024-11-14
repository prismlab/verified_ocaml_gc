module Spec.GC_part03

include Spec.GC_part02_02

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

let valid_header_lemma (g: heap {well_formed_heap2 g})
                       (g':heap {well_formed_heap2 g'})
                       (v_id: hp_addr {is_valid_header1 v_id g})
                       (c:color)
               : Lemma
                 (requires (getWosize  (read_word g v_id) == getWosize (read_word g' v_id)) /\
                           (getTag     (read_word g v_id) == getTag    (read_word g' v_id)) /\
                           (c == white \/ c == gray \/ c == black) /\
                           (get_allocated_block_addresses g == get_allocated_block_addresses g') /\

                           (heap_remains_same_except_index_v_id v_id g g'))
                 (ensures (is_valid_header1 v_id g')) =
assert (Seq.mem v_id (get_allocated_block_addresses g));
assert (Seq.mem v_id (get_allocated_block_addresses g'));
assert (is_valid_header1 v_id g');
()


#restart-solver

#restart-solver

#restart-solver

let h_index_field_index_mword_multiple_lemma (g:heap{well_formed_heap2 g})
                                             (h_index: hp_addr{is_valid_header1 h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) =

max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()

let h_index_field_index_mword_multiple_lemma5 (g:heap{Seq.length (objects2 0UL g) > 0})
                                             (h_index: hp_addr{Seq.mem h_index (get_allocated_block_addresses g)})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\
                                                           is_fields_within_limit1 h_index wz /\
                                                          is_fields_contents_within_limit2 h_index wz g)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) =
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()

let fieldaddress_within_limits_lemma (g:heap{well_formed_heap2 g})
                                     (x:hp_addr{is_valid_header1 x g /\ Seq.mem x (get_allocated_block_addresses g)})
                                     (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))})
                          : Lemma
                            (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                            (ensures (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) =
 h_index_field_index_mword_multiple_lemma g x (getWosize (read_word g x)) i


#restart-solver

#restart-solver


 let fieldaddress_within_limits_lemma5 (g:heap{Seq.length (objects2 0UL g) > 0})
                                     (x:hp_addr{Seq.mem x (get_allocated_block_addresses g)})
                                     (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))})
                          : Lemma
                            (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                            (ensures (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) =
 h_index_field_index_mword_multiple_lemma5 g x (getWosize (read_word g x)) i



let fieldaddress_within_limits_lemma_x_i_all(g:heap{well_formed_heap2 g})
                                             (x:hp_addr{is_valid_header1 x g /\ Seq.mem x (get_allocated_block_addresses g)})
                           : Lemma
                             (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                             (ensures (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) =
Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma g x))


let fieldaddress_within_limits_lemma_x_i_all5(g:heap{Seq.length (objects2 0UL g) > 0})
                                             (x:hp_addr{Seq.mem x (get_allocated_block_addresses g)})
                           : Lemma
                             (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                             (ensures (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) =
Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma5 g x))


let fieldaddress_within_limits_lemma_x_all (g:heap{well_formed_heap2 g})
                                    : Lemma
                                      (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                                      (ensures (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) =
 Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma_x_i_all g))


let fieldaddress_within_limits_lemma_x_all5 (g:heap{Seq.length (objects2 0UL g) > 0})
                                    : Lemma
                                      (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                                      (ensures (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) =
 Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma_x_i_all5 g))


#restart-solver

#reset-options "--z3rlimit 100 --split_queries always --z3seed 1"

let colorHeader1_alloc_colors_lemma  (v_id:hp_addr)
                                     (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g})
                                     (c:color)
                         : Lemma
                           (requires (c == white \/ c == gray \/ c == black))
                           (ensures well_formed_heap2 (colorHeader1 v_id g c) /\ is_valid_header1 v_id (colorHeader1 v_id g c) /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses (colorHeader1 v_id g c))) =
 let wz = getWosize (read_word g v_id) in
 let tg = getTag (read_word g v_id) in
 let h = makeHeader wz c tg in
 let h_index = v_id in

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 assert (g' == colorHeader1 v_id g c);
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.length (objects2 0UL g') > 0);
 get_allocated_block_addresses_lemma g g' v_id c;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 check_all_block_fields_within_limit2_lemma g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
 assert (check_all_block_fields_within_limit2 g' (get_allocated_block_addresses g'));
 fieldaddress_within_limits_lemma_x_all g;
 assert  (forall i x.  Seq.mem x (get_allocated_block_addresses g)  /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
 check_fields_points_to_blocks2_lemma  g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
 assert  (check_fields_points_to_blocks2 g' (get_allocated_block_addresses g'));
 check_well_formed_closure_objs_lemma g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
 assert (check_well_formed_closure_objs g' (get_allocated_block_addresses g'));
 assert (well_formed_heap2 g');
 valid_header_lemma g g' v_id c;
 assert (is_valid_header1 v_id g');
 ()

type stack = s:seq Usize.t {forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size}

type stack_heap_pair = stack & heap


#reset-options "--z3rlimit 500"

#push-options "--z3rlimit 50"

#restart-solver

#push-options "--split_queries always"

let stack_props_func (g:heap{well_formed_heap2 g})
                     (st: seq Usize.t ) =
     G.is_vertex_set st /\
     (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
     (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
     (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag) /\
     (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g) /\
     (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>  Seq.mem x st)

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000"

#restart-solver

let seq_lemmas_empty (g:heap{well_formed_heap2 g})
                     (st: seq Usize.t {stack_props_func g st})

                     (x: hp_addr{is_valid_header1 x g /\
                                ~(Seq.mem (f_address x) st) /\
                                 (Usize.v (tag_of_object1 x g) <> infix_tag)})
             :Lemma
              (requires (Seq.length st == 0))
              (ensures (let stk' = Seq.create 1 (f_address x) in
                       (Seq.mem (f_address x) (Seq.create 1 (f_address x))) /\
                       (G.is_vertex_set stk') /\
                       (Seq.length stk' == 1) /\
                       (~(exists y. Seq.mem y stk' /\ y <> (f_address x))) /\
                       (forall y. Seq.mem y st \/ y == (f_address x) ==> Seq.mem y stk'))) =
let stk' = Seq.create 1 (f_address x) in
G.is_vertex_set_lemma2 stk';
assert (G.is_vertex_set stk');
assert (Seq.length stk' == 1);
assert (~(exists y. Seq.mem y stk' /\ y <> (f_address x)));
assert (forall y. Seq.mem y st \/ y == (f_address x) ==> Seq.mem y stk');
()

let seq_lemmas_non_empty (g:heap{well_formed_heap2 g})
                     (st: seq Usize.t {stack_props_func g st})

                     (x: hp_addr{is_valid_header1 x g /\
                                ~(Seq.mem (f_address x) st) /\
                                 (Usize.v (tag_of_object1 x g) <> infix_tag)})
             :Lemma
              (requires ~(Seq.length st == 0))
              (ensures Seq.length st > 0) =
()

#restart-solver

let seq_lemmas_non_empty_snoc (g:heap{well_formed_heap2 g})
                     (st: seq Usize.t {stack_props_func g st})

                     (x: hp_addr{is_valid_header1 x g /\
                                ~(Seq.mem (f_address x) st) /\
                                 (Usize.v (tag_of_object1 x g) <> infix_tag)})
              :Lemma
              (requires (Seq.length st > 0))
              (ensures (let st' = snoc st (f_address x) in
                        (forall y. Seq.mem y st \/ y == (f_address x) ==> Seq.mem y st') /\
                        (Seq.length st' == Seq.length st + 1))) =
lemma_tail_snoc st (f_address x);
lemma_mem_snoc st (f_address x);
()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


#restart-solver

#restart-solver

#restart-solver
let push_to_stack2  (g:heap{well_formed_heap2 g})
                    (st: seq Usize.t {stack_props_func g st})

                    (x: hp_addr{is_valid_header1 x g /\
                                ~(Seq.mem (f_address x) st) /\
                                 (Usize.v (tag_of_object1 x g) <> infix_tag)
                                })
                   : Tot (st': stack_heap_pair{well_formed_heap2 (snd st') /\
                                       (forall x. Seq.mem x st ==> Seq.mem x (fst st')) /\

                                       Seq.mem (f_address x) (fst st') /\

                                       Seq.length (fst st') == Seq.length st + 1 /\

                                       stack_props_func (snd st') (fst st')}) =
if Seq.length st = 0 then
(
   assert (Usize.v (tag_of_object1 x g) <> infix_tag);
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in
   colorHeader1_alloc_colors_lemma x g gray;
   assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
   assert (Usize.v (tag_of_object1 x g') <> infix_tag);
   assert (Usize.v (tag_of_object1 (hd_address f_x) g') <> infix_tag);
   assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
   seq_lemmas_empty g st x;
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';

   assert (objects2 0UL g == objects2 0UL g');
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>  Seq.mem x st);
   assert (Seq.length stk' == 1);
   assert (~(exists y. Seq.mem y stk' /\ y <> f_x));
   assert (forall y. Seq.mem y stk' ==> color_of_object1 (hd_address y) g' == gray);
   assert (forall y. Seq.mem y stk' ==> Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g');
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==>  Seq.mem x st);
   assert (forall y. Seq.mem y stk' ==> Seq.mem y st \/ y == f_x);
   assert (forall y. Seq.mem y st \/ y == f_x ==> Seq.mem y stk');
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g ==> Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g');
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> (Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g) \/
                                                                                                    (hd_address y) == x);
   assert (hd_address f_x == x);
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> Seq.mem y st \/
                                                                                                    (hd_address y) == x);

   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> Seq.mem y stk');

   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x stk');

   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x stk');
   assert (heap_remains_same_except_index_v_id x g g');
   assert (forall x. Seq.mem x stk' ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);

   assert (well_formed_heap2 g' /\
                                       (forall x. Seq.mem x st ==> Seq.mem x stk') /\

                                       Seq.mem (f_address x) stk' /\

                                       Seq.length stk' == Seq.length st + 1 /\

                                       stack_props_func g' stk');
   (stk', g')
)

else
(
  assert (Usize.v (tag_of_object1 x g) <> infix_tag);
  let f_x = f_address x in
  seq_lemmas_non_empty g st x;
  assert (Seq.length st > 0);
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x;
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in
  colorHeader1_alloc_colors_lemma x g gray;
  assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
  assert (Usize.v (tag_of_object1 x g') <> infix_tag);
  assert (Usize.v (tag_of_object1 (hd_address f_x) g') <> infix_tag);
  assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
  objects2_equal_lemma 0UL g g';

  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st');
  seq_lemmas_non_empty_snoc g st x;
  assert (forall y. Seq.mem y st \/ y == f_x ==> Seq.mem y st');
  assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g ==> Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g');
  assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> (Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g) \/
                                                                                                    (hd_address y) == x);
  assert (hd_address f_x == x);
  assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> Seq.mem y st \/
                                                                                                    (hd_address y) == x);
  assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> Seq.mem y st');

  assert (forall y. Seq.mem y st' ==> Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g');
  assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x st');


  assert (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g);
  assert (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g');

  assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x st');
  assert (heap_remains_same_except_index_v_id x g g');
  assert (forall x. Seq.mem x st' ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
  assert (well_formed_heap2 g' /\
                                       (forall x. Seq.mem x st ==> Seq.mem x st') /\

                                       Seq.mem (f_address x) st' /\

                                       Seq.length st' == Seq.length st + 1 /\

                                       stack_props_func g' st');
  (st',g')
)

#reset-options "--z3rlimit 500"


let field_limits_allocated_blocks_lemma (g:heap{well_formed_heap2 g})
                    : Lemma
                      (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)))) =
 assert (well_formed_heap2 g);
 let objs = objects2 0UL g in
 assert (forall x. Seq.mem x objs ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 assert (G.subset_vertices (get_allocated_block_addresses g) objs);
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 ()

#restart-solver

let field_contents_within_limits_allocated_blocks_lemma (g:heap{well_formed_heap2 g})
                                            : Lemma
                                              (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) =
 assert (well_formed_heap2 g);
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g
                                                             );
 ()

let valid_succ_color_lemma (g:heap{well_formed_heap2 g})
                           (succ:hp_addr{is_valid_header1 succ g})

                  : Lemma
                    (requires True)
                    (ensures (color_of_object1 succ g == white ==> ~(isGrayObject1 succ g) /\
                                                                 ~(isBlackObject1 succ g))) = ()

#restart-solver

let vl_props_func (g:heap{well_formed_heap2 g})
                  (vl: seq Usize.t ) =
  (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
  (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) (*/\
  (forall x. Seq.mem x vl ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag)*) /\
  (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
  (G.is_vertex_set vl) /\
  (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==>  Seq.mem x vl)

let is_alloc_color (g:heap{well_formed_heap2 g})
                   (succ:hp_addr{is_valid_header1 succ g}) =
  (color_of_object1 succ g == white \/
   color_of_object1 succ g == gray \/
   color_of_object1 succ g == black)

let valid_succ_color_lemma1 (g:heap{well_formed_heap2 g})
                            (st: seq Usize.t{stack_props_func g st})

                            (vl: seq Usize.t {vl_props_func g st})

                            (succ:hp_addr{is_valid_header1 succ g})

                   : Lemma
                    (requires (is_alloc_color g succ))
                    (ensures ~(color_of_object1 succ g == white) ==> Seq.mem (f_address succ) st \/ Seq.mem (f_address succ) vl) = ()

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let push_to_stack2_heap_state_lemma  (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{stack_props_func g st})

                                    (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st)  /\
                                                (Usize.v (tag_of_object1 x g) <> infix_tag)
                                               })

                  : Lemma
                    (ensures (heap_remains_same_except_index_v_id x g (snd (push_to_stack2 g st x)))) = ()

let push_to_stack2_field_size_lemma (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{stack_props_func g st})

                                    (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st)  /\
                                                (Usize.v (tag_of_object1 x g) <> infix_tag)
                                               })

                  : Lemma
                    (ensures (forall (y:Usize.t{Usize.v y < heap_size /\  Usize.v y % Usize.v mword == 0}). (getWosize (read_word g y)) ==
                                               (getWosize (read_word (snd (push_to_stack2 g st x)) y)))) = ()

#restart-solver

#restart-solver

#reset-options "--z3rlimit 500"

let push_to_stack2_lemma (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{stack_props_func g st})

                                     (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st) /\ (color_of_object1 x g == white) /\
                                                 (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                })
                     : Lemma
                     (ensures (get_allocated_block_addresses g == get_allocated_block_addresses (snd (push_to_stack2 g st x)))) =
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';

   assert (objects2 0UL g == objects2 0UL g');
   get_allocated_block_addresses_lemma g g' x 2UL;
   ()
)

else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x;
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in
  objects2_equal_lemma 0UL g g';
  colorHeader1_alloc_colors_lemma x g gray;

  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st');
  get_allocated_block_addresses_lemma g g' x 2UL;
  ()
)

#restart-solver

#restart-solver

//#reset-options "--z3rlimit 5000 --query_stats"

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"


let parent_closure_of_infix_object (g:heap{well_formed_heap2 g})
                                   (h_index:hp_addr{is_valid_header1 h_index g})
                                   (i:Usize.t{(Usize.v i < Usize.v (getWosize (read_word g h_index)) + 1 /\ Usize.v i >= 1) /\
                                               isPointer (succ_index_fn g h_index i) g /\
                                               (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag)
                                             })
                  : Tot (parent_hdr:hp_addr{is_valid_header1 parent_hdr g /\
                                            (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n) /\
                                            (Usize.v parent_hdr + Usize.v mword < heap_size) /\
                                            (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                                            (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag)}) =
 assert (well_formed_heap2 g);
 assert (Seq.length (objects2 0UL g) > 0  /\
                                          (check_all_block_fields_within_limit2 g (get_allocated_block_addresses g)) /\
                                          (check_fields_points_to_blocks2 g (get_allocated_block_addresses g)) /\
                                          (check_well_formed_closure_objs g (get_allocated_block_addresses g)));
 assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
 assert  (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g));
 assert (is_fields_points_to_blocks2 h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
 assert (is_fields_points_to_blocks2_post_condition h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));

 assert ((Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) == infix_tag) /\
        (UInt.fits (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) -
                                                   (Usize.v (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) * Usize.v mword)) Usize.n) /\
          (
                                                       (let actual_succ = (Usize.sub (read_word g (Usize.add h_index (Usize.mul i mword)))
                                                       (Usize.mul (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) mword)) in
                                                        (Usize.v actual_succ >= Usize.v mword) /\
                                                        (is_hp_addr actual_succ) /\
                                                        (Usize.v (tag_of_object1 (hd_address actual_succ) g) == closure_tag) /\
                                                        (Seq.mem (hd_address actual_succ) (get_allocated_block_addresses g)))));


 let actual_succ = Usize.sub (read_word g (Usize.add h_index (Usize.mul i mword)))
                                                       (Usize.mul (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) mword) in
 let hdr_actual_succ = hd_address actual_succ in
 assert (is_valid_header1 hdr_actual_succ g);
 assert (UInt.fits (Usize.v hdr_actual_succ + Usize.v mword) Usize.n);
 assert (Usize.v hdr_actual_succ + Usize.v mword < heap_size);
 assert (Usize.v (tag_of_object1 hdr_actual_succ g) == closure_tag);
 assert (Usize.v (tag_of_object1 hdr_actual_succ g) <> infix_tag);
 hdr_actual_succ

let stack_mem_lemma (g:heap{well_formed_heap2 g})
                    (st: seq Usize.t{stack_props_func g st})
                    (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                     ~(isGrayObject1 hdr_id g)})
          : Lemma
            (ensures (~(Seq.mem (f_address hdr_id) st))) =
 assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
 assert (~(Seq.mem (f_address hdr_id) st));
 ()

#restart-solver

#restart-solver

let darken_helper(g:heap{well_formed_heap2 g})
                 (st: seq Usize.t{stack_props_func g st})
                 (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                  (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)})
           : Tot (st_hp:stack_heap_pair{well_formed_heap2 (snd st_hp) /\

                                         stack_props_func (snd st_hp) (fst st_hp) /\

                                         (forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) == getWosize (read_word (snd st_hp) x)) /\

                                         (objects2 0UL g ==  objects2 0UL (snd st_hp)) /\

                                         (Seq.length g == Seq.length (snd st_hp)) /\

                                         (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\

                                         (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))}) =
 if (color_of_object1 hdr_id g = white) then
(
   assert (is_valid_header hdr_id g);
   valid_succ_color_lemma g hdr_id;

   assert (~(isGrayObject1 hdr_id g) /\ ~(isBlackObject1 hdr_id g));
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
   assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
   stack_mem_lemma g st hdr_id;
   assert (Usize.v hdr_id + Usize.v mword < heap_size);
   assert (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n);
   assert (~(Seq.mem (f_address hdr_id) st));
   let st', g' = push_to_stack2 g st hdr_id  in
   push_to_stack2_heap_state_lemma g st hdr_id;
   push_to_stack2_field_size_lemma g st hdr_id;
   assert (G.is_vertex_set st');

   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');

   assert (color_of_object1 hdr_id g == white);
   push_to_stack2_lemma g st hdr_id;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));

   (st', g')
)
else
(
  (st,g)
)

#reset-options "--z3rlimit 500"

#restart-solver
(*#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let fieldPush_spec_body   (g:heap{well_formed_heap2 g})
                          (st: seq Usize.t{stack_props_func g st})
                          (h_index:hp_addr{is_valid_header1 h_index g})
                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                          (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                     : Pure (stack_heap_pair)
                      (requires True)
                      (ensures fun st_hp -> well_formed_heap2 (snd st_hp) /\

                                         stack_props_func (snd st_hp) (fst st_hp) /\

                                         (forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) == getWosize (read_word (snd st_hp) x)) /\

                                         (objects2 0UL g ==  objects2 0UL (snd st_hp)) /\
                                         (is_hp_addr (Usize.(h_index +^ (i *^ mword)))) /\

                                         (Seq.length g == Seq.length (snd st_hp)) /\

                                         (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\

                                         (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))) =
 assert (well_formed_heap2 g);

   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;

   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);

   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);

  let succ_index = Usize.add h_index (Usize.mul i mword) in

  assert (Usize.v succ_index < heap_size);

  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);

  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);

  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));


   if isPointer succ_index g  then
    (
      let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        if color_of_object1 parent_hdr g = white  then
        (
          assert (is_valid_header parent_hdr g);
          valid_succ_color_lemma g parent_hdr;

          assert (~(isGrayObject1 parent_hdr g) /\ ~(isBlackObject1 parent_hdr g));
          assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
          assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
          stack_mem_lemma g st parent_hdr;
          assert (Usize.v parent_hdr + Usize.v mword < heap_size);
          assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
          assert (~(Seq.mem (f_address parent_hdr) st));
          let st', g' = push_to_stack2 g st parent_hdr  in
          push_to_stack2_heap_state_lemma g st parent_hdr;
          push_to_stack2_field_size_lemma g st parent_hdr;
          assert (G.is_vertex_set st');

          objects2_equal_lemma 0UL g g';
          assert (objects2 0UL g == objects2 0UL g');

          assert (color_of_object1 parent_hdr g == white);
          push_to_stack2_lemma g st parent_hdr;

          assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
          assert ((Seq.length g == Seq.length g'));

         (st', g')
      )
      else
      (
          (st,g)
      )
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        if color_of_object1 h_addr_succ g = white  then
        (
          assert (is_valid_header h_addr_succ g);
          valid_succ_color_lemma g h_addr_succ;

          assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
          assert (~(Seq.mem (f_address h_addr_succ) st));
          assert (~(Seq.mem succ st));

          assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);

          let st', g' = push_to_stack2 g st  h_addr_succ in
          push_to_stack2_heap_state_lemma g st h_addr_succ;
          push_to_stack2_field_size_lemma g st h_addr_succ;
          assert (G.is_vertex_set st');
          assert (well_formed_heap2 g' /\
              (forall x. Seq.mem x st ==> Seq.mem x st') /\

              (Seq.mem succ st') /\

              Seq.length st' == Seq.length st + 1 /\

              (forall y. Seq.mem y st' ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

              (forall y. Seq.mem y st' ==> Usize.v y % Usize.v mword == 0) /\

              (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g') /\

              (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st') /\

              (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st'));

         assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));


         objects2_equal_lemma 0UL g g';
         assert (objects2 0UL g == objects2 0UL g');

         assert (color_of_object1 h_addr_succ g == white);
         push_to_stack2_lemma g st h_addr_succ;

         assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
         assert ((Seq.length g == Seq.length g'));

         (st', g')
      )
      else
      (
          (st,g)
      )
    )
   )
  else
   (
       (st,g)
   )
*)

#reset-options "--z3rlimit 1000"

let fieldPush_spec_body1  (g:heap{well_formed_heap2 g})
                          (st: seq Usize.t{stack_props_func g st})
                          (h_index:hp_addr{is_valid_header1 h_index g})
                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                          (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                     : Pure (stack_heap_pair)
                      (requires True)
                      (ensures fun st_hp -> well_formed_heap2 (snd st_hp) /\

                                         stack_props_func (snd st_hp) (fst st_hp) /\

                                         (forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) == getWosize (read_word (snd st_hp) x)) /\

                                         (objects2 0UL g ==  objects2 0UL (snd st_hp)) (*/\
                                         (is_hp_addr (Usize.(h_index +^ (i *^ mword))))*) /\

                                         (Seq.length g == Seq.length (snd st_hp)) /\

                                         (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\

                                         (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))) =

 assert (well_formed_heap2 g);

   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;

   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);

   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);

  let succ_index = Usize.add h_index (Usize.mul i mword) in

  assert (Usize.v succ_index < heap_size);

  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);

  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);

  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));


   if isPointer succ_index g  then
    (
      let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        assert (Usize.v parent_hdr + Usize.v mword < heap_size);
        assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
        let st', g' = darken_helper g st parent_hdr in
        (st',g')
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        (st',g')
      )
   )
  else
   (
       (st,g)
   )

#restart-solver

let rec fieldPush_spec1   (g:heap{well_formed_heap2 g})
                          (st: seq Usize.t{stack_props_func g st})
                          (h_index:hp_addr{is_valid_header1 h_index g})
                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                          (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
         : Pure (stack_heap_pair)
         (requires True)
         (ensures fun st_hp -> (well_formed_heap2 (snd st_hp)) /\
                            (Seq.length g == Seq.length (snd st_hp)) /\

                            (stack_props_func (snd st_hp) (fst st_hp)) /\

                            (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\
                            (objects2 0UL g == objects2 0UL (snd st_hp)) /\

                            get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))

         (decreases ((Usize.v wz + 1) - Usize.v i)) =
 if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       st_hp
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body1 g st h_index wz i in
       fieldPush_spec1 g' st' h_index wz i'
    )

let slice_mem_helper_lemma (s: seq Usize.t{(Seq.length s) > 0})
                           (s': seq Usize.t{Seq.equal s' (Seq.slice s 0 (Seq.length s - 1))})
                           (x:Usize.t)
                  : Lemma
                    (requires (Seq.mem x s'))
                    (ensures (Seq.mem x s)) =
 Seq.lemma_mem_snoc s' (Seq.index s (Seq.length s - 1))

let slice_mem_lemma (s: seq Usize.t{(Seq.length s) > 0})
                    (s': seq Usize.t{Seq.equal s' (Seq.slice s 0 (Seq.length s - 1))})
                : Lemma
                  (ensures (forall x. Seq.mem x s' ==> Seq.mem x s))=
Classical.forall_intro (Classical.move_requires (slice_mem_helper_lemma s s'))

let all_mem_st_mem_st__except_v_id_in_stack (v_id:hp_addr)
                                            (st:stack)
                                            (st':stack) = (forall x. Seq.mem x st' /\ x <> v_id ==> Seq.mem x st)

#restart-solver

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

let extract_start_env_bits' (clos_info:Usize.t)
               : Tot (strt_env: Usize.t{strt_env == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul})=
 let l1 = Usize.shift_left clos_info 8ul in
 let r1 = Usize.shift_right l1 9ul in
 assert (r1 == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul);
 r1

#restart-solver

#restart-solver

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


(*closinfo_val1 gives assertion failure if (is_hp_addr (Usize.add f_addr (Usize.mul 1UL mword))) condition is not added before the result of post condition. Either we can
  add it as a post condition before the result or as a pre-condition. Post condition is preferable, otherwise we need to ensure the precondition before calling the function.*)
let start_env_clos_info (g:heap{well_formed_heap2 g})
                        (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                  (is_valid_header1 (hd_address f_addr) g) /\
                                  (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                                  (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2)})
                 : Tot (start_env:hp_addr{(Usize.v start_env >= Usize.v (extract_start_env_bits ((*closinfo_val1*) closinfo_val_from_closure_object g f_addr))) /\
                                          (Usize.v start_env + 1 <= Usize.v (wosize_of_object1 (hd_address f_addr) g)) /\
                                           Usize.v start_env >= 1}) =
  let clos_info = (*closinfo_val1*) closinfo_val_from_closure_object g f_addr in
  let start_env = extract_start_env_bits clos_info in
  (*assert ((is_hp_addr (Usize.add f_addr (Usize.mul 1UL mword))) /\
           (clos_info == read_word g (Usize.add f_addr (Usize.mul 1UL mword))));
  assert (start_env == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul);
  assert (start_env == Usize.shift_right (Usize.shift_left (read_word g (Usize.add f_addr (Usize.mul 1UL mword))) 8ul) 9ul);
  assert (is_hp_addr start_env);
  let hdr_f_addr = hd_address f_addr in
  assert (is_valid_header1 hdr_f_addr g);
  let wz = wosize_of_object1 hdr_f_addr g in
  assert (Usize.v start_env <= Usize.v wz);
  assert (Usize.v start_env >= Usize.v (extract_start_env_bits ((*closinfo_val1*) closinfo_val_from_closure_object g f_addr)));
  assert (Usize.v start_env >= 1);*)
  start_env



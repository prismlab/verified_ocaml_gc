module Spec.GC_part11

include Spec.GC_part10

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


#restart-solver 

#reset-options "--z3rlimit 100 --split_queries always"

let darken_helper_lemma (g:heap{well_formed_heap2 g})
                        (st: seq Usize.t{stack_props_func g st})
                        (h_index:hp_addr{is_valid_header1 h_index g})
                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                         
                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                        (j:Usize.t)
                        (vl: seq Usize.t{vl_props_func g vl})
                        (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                  (Usize.v (tag_of_object1 hdr_id g) <> infix_tag) /\
                                  (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n)})
                        (succ:hp_addr{succ == f_address hdr_id})
                  : Lemma
                    (requires  (h_index_within_limits g h_index) /\
                               (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                  
                               (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\

                                
                                                      
                               (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                               (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                  (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                         
                                                  (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) ==
                                                    succ) /\
                                                  (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                  (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                    (ensures fst (darken_helper g st hdr_id) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j)) = 
let succ1 = f_address hdr_id in
let succ2 = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
assert (succ1 == succ2);
if (color_of_object1 hdr_id g = white) then
(
   let succ_index = Usize.add h_index (Usize.mul i mword) in
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
   assert (~(Seq.mem (f_address hdr_id) vl));
   //assert (f_address hdr_id == read_word g succ_index);
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
   fieldaddress_within_limits_lemma_x_all g;
   //test_allocs g h_index wz;
   assert (Seq.mem hdr_id (get_allocated_block_addresses g));
   let succ' = f_address hdr_id in
   let succ'' = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
   assert (succ' == succ'');
   push_to_stack_heap_and_push_to_graph_equality_lemma1 g st hdr_id vl;
   let st1 = G.push_to_stack_graph1 vl st succ in
   assert (st' == G.push_to_stack_graph1 vl st succ);
   let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j) in
   assert (st'' == G.push_to_stack_graph1 vl st succ);
   assert (st'' == st1);
   assert (st' == st1);
   assert (st' == st'');
   assert (fst (push_to_stack2 g st hdr_id) == st'');
   assert (fst (darken_helper g st hdr_id) == st'');
   assert (fst (darken_helper g st hdr_id) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
   ()
)
else
(
  let st' = st in
  let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st  (Usize.v j) in
  assert (~(color_of_object1 hdr_id g = white));
  assert ((isGrayObject1 hdr_id g) \/ (isBlackObject1 hdr_id g));
  gray_black_stack_vl_mem_lemma g st hdr_id succ vl;
  assert ((Seq.mem (f_address hdr_id) st) \/ (Seq.mem (f_address hdr_id) vl));
  assert (st'' == st);
  //assert (st'' == st');
  assert (fst (darken_helper g st hdr_id) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
  ()
)

#restart-solver

#restart-solver 

#restart-solver

#restart-solver 

#restart-solver

#restart-solver

let fieldPush_spec_body_successor_push_body_equivalence_lemma2 (g:heap{well_formed_heap2 g})
                                                               (st: seq Usize.t{stack_props_func g st})
                                                               (h_index:hp_addr{is_valid_header1 h_index g})
                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                         
                                                               (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                               (j:Usize.t)
                                                               (vl: seq Usize.t{vl_props_func g vl}) 
                                        : Lemma
                                        (requires (h_index_within_limits g h_index) /\
                                                  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                  
                                                  (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                      
                                                  (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                  (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                  (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                  (let succ_index = Usize.add h_index (Usize.mul i mword) in
                                                   (isPointer succ_index g  /\
                                                   (Usize.v (read_word g succ_index) >= Usize.v mword) /\
                                                   (Usize.v (tag_of_object1 (hd_address (read_word g succ_index)) g) <> infix_tag) ==> 
                                                         (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         read_word g succ_index)) /\

                                                   (isPointer succ_index g  /\
                                                   (Usize.v (read_word g succ_index) >= Usize.v mword) /\
                                                   (Usize.v (tag_of_object1 (hd_address (read_word g succ_index)) g) == infix_tag) ==> 
                                                         (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         f_address (parent_closure_of_infix_object g h_index i)))) /\
                                                         
                                                    
                                                  (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                  (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                                          
                                          (ensures (fst (fieldPush_spec_body1 g st h_index wz i) == 
                                                       ( if (isPointer(Usize.add h_index (Usize.mul i mword)) g) then
                                                                (
                                                                      G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) 
                                                                                              (vl) 
                                                                                              (st) 
                                                                                              (Usize.v j)
                                                                )
                                                               else
                                                                (
                                                                      st
                                                                )))) =

assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   fieldaddress_within_limits_lemma_x_all g;
       
   let succ_index = Usize.add h_index (Usize.mul i mword) in
       
   max_wosize_times_mword_multiple_of_mword i;
   sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);

   assert (Usize.v succ_index % Usize.v mword == 0);
   assert (is_hp_addr succ_index);

   lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8); 
   let succ_h = read_word g succ_index in
   let succ_g = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
   assert (succ_h == read_word g succ_index);
   if isPointer succ_index g  then
    (
       //assume (succ_h == succ_g);
       let h_addr_succ = hd_address succ_h in
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
          let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j) in
          assert (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         f_address (parent_closure_of_infix_object g h_index i));
          let succ = f_address parent_hdr in
          let succ1 = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
          darken_helper_lemma g st h_index wz i j vl parent_hdr succ;
          assert (st' == st'');
          assert (fst (fieldPush_spec_body1 g st h_index wz i) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
          ()
          (*assert (succ == succ1);
          darken_helper_lemma g st h_index wz i j vl parent_hdr succ;
          assert (st' == st'');
          assert (fst (fieldPush_spec_body1 g st h_index wz i) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
          ()*)
          
       )
       else
       (
         assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
         let st', g' = darken_helper g st h_addr_succ in
         let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j) in
         let succ1 = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
         let succ = f_address h_addr_succ in
         assert (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                          read_word g succ_index);
         assert ((Usize.v (tag_of_object1 (hd_address (read_word g succ_index)) g) <> infix_tag) ==> 
                                                         (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         read_word g succ_index));
         darken_helper_lemma g st h_index wz i j vl h_addr_succ succ;
         assert (fst (darken_helper g st h_addr_succ) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
         assert (st' == st'');
         assert (fst (fieldPush_spec_body1 g st h_index wz i) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
         ()
         //assert (succ == succ1);
         (*assert (st' == st'');
         assert (fst (fieldPush_spec_body1 g st h_index wz i) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
         ()*)
         
         
       )
    )
   else
   (
     ()
   )

#restart-solver 

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000"


let create_succcessors_for_h_index_lemma_rec_lemma_non_infix (g:heap{well_formed_heap2 g}) 
                                                            (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                            (wz: wosize{valid_wosize g h_index wz})
                         
                                                            (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                            (i':Usize.t{Usize.v i' == Usize.v i + 1})
                          :Lemma
                           (ensures (isPointer (Usize.add h_index (Usize.mul i mword)) g /\ 
                                       Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) <> infix_tag ==> 
                                       create_successors_list_for_h_index g h_index wz i == Seq.cons (read_word g (Usize.add h_index (Usize.mul i mword)))
                                       (create_successors_list_for_h_index g h_index wz i'))) =
()

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let rec create_succcessors_for_h_index_lemma1 (g:heap{well_formed_heap2 g}) 

                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header1 h_index g})
                                           
                                             (wz: wosize{(wz == getWosize (read_word g h_index))})

                                            
                         
                                             (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                                             (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})

                                             (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})

                                             (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })

                                             (wz1: wosize{(wz1 == getWosize (read_word g' h_index))})
                          : Lemma
                          (requires 
                                    (objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    (wz == wz1) /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g') /\
                                    (forall j x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                    (forall j x.  Seq.mem x (get_allocated_block_addresses g') /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g' x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)
                                    )
                          (ensures (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       seq_empty_lemma ();
       assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
       ()
    )
  else
   (
     field_reads_all_equal_for_all_objects_lemma g g' v_id;
     field_reads_all_equal_h_index_lemma g g' v_id;
     let succ_index = Usize.add h_index (Usize.mul i mword) in

     assert (Usize.v i < Usize.v wz + 1);
    

     assert (is_fields_within_limit1 h_index wz);

     assert (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size);

     assert (Usize.v i < Usize.v wz + 1);

     assert (Usize.v h_index + (Usize.v i * Usize.v mword) < heap_size);
     
     assert (Usize.v succ_index < heap_size);
     
     field_limits_allocated_blocks_lemma g;
     field_contents_within_limits_allocated_blocks_lemma g;
     fieldaddress_within_limits_lemma_x_all g;
     
     max_wosize_times_mword_multiple_of_mword i;
     sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);

     //assert (Usize.v succ_index < heap_size);
     
      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);

      lemma_len_slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8); 
      
      let succ1 = read_word g' succ_index in
      assert (succ1 == read_word g' succ_index);
      assert (Usize.v succ_index >= Usize.v h_index + Usize.v mword /\
             Usize.v succ_index <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword));
      assert (succ == succ1);
      let i' = Usize.(i +^ 1UL) in
      if isPointer succ_index g  then
      (
          let h_addr_succ = hd_address succ in
          let f_index = f_address h_index in
          f_address_hp_address_lemma h_index;
          assert (hd_address f_index == h_index);
          assert (read_word g (Usize.add h_index (Usize.mul i mword)) == read_word g' (Usize.add h_index (Usize.mul i mword)));
          colorHeader1_tags_lemma v_id g c g';
          assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g == tag_of_object1 x g');
          assert (Usize.v (tag_of_object1 h_addr_succ g) == Usize.v (tag_of_object1 h_addr_succ g'));
          //test_allocs g h_index wz;
          (*assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
          assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
          assert (Seq.mem (hd_address succ) (objects2 0UL g));
          assert (is_valid_header (hd_address succ) g);

          
          assert (Seq.mem h_index (get_allocated_block_addresses g));*)
         if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
         (
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           let parent_hdr1 = parent_closure_of_infix_object g' h_index i in
           field_limits_allocated_blocks_lemma g;
           field_contents_within_limits_allocated_blocks_lemma g;
           field_limits_allocated_blocks_lemma g';
           field_contents_within_limits_allocated_blocks_lemma g';
           field_points_to_blocks_allocs_lemma g;
           field_points_to_blocks_allocs_lemma g';
           assert (allocs_props_g g h_index);
           assert (allocs_props_g g' h_index);
           assert (parent_closure_index_props g' h_index i);
           colorHeader1_wosize_lemma v_id g c g';
           parent_closure_of_infix_object_lemma  g h_index i v_id c g';
           assert (parent_hdr == parent_hdr1);
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
          
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
           assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
           
           let s_list' = create_successors_list_for_h_index g h_index wz i' in
           let s_list'' = create_successors_list_for_h_index g' h_index wz1 i' in
           create_succcessors_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;
           assert (create_successors_list_for_h_index g h_index wz i' == create_successors_list_for_h_index g' h_index wz1 i');
           let parent_succ = f_address parent_hdr in
           lemma_tl parent_succ s_list'; 
        
           let s_list = Seq.cons parent_succ s_list' in 
           let s_list1 = Seq.cons parent_succ s_list'' in
           assert (s_list == s_list1);
           assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
           ()
         )
         else 
         (
          let s_list' = create_successors_list_for_h_index g h_index wz i' in
          let s_list'' = create_successors_list_for_h_index g' h_index wz1 i' in
          create_succcessors_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;
          assert (create_successors_list_for_h_index g h_index wz i' == create_successors_list_for_h_index g' h_index wz1 i');

          lemma_tl succ s_list'; 
          lemma_tl succ s_list''; 
        
          let s_list = Seq.cons succ s_list' in 
          let s_list1 = Seq.cons succ s_list'' in 
          assert (s_list == s_list1);
          create_succcessors_for_h_index_lemma_rec_lemma_non_infix g h_index wz i i';
          create_succcessors_for_h_index_lemma_rec_lemma_non_infix g' h_index wz1 i i';
          assert (s_list == create_successors_list_for_h_index g h_index wz i);
          assert (isPointer succ_index g');
          assert ((Usize.v (tag_of_object1 h_addr_succ g') <> infix_tag));
          assert (create_successors_list_for_h_index g' h_index wz1 i == Seq.cons (read_word g' (Usize.add h_index (Usize.mul i mword)))
                                       (create_successors_list_for_h_index g' h_index wz1 i'));
                                       
          //assert ( s_list1 == create_successors_list_for_h_index g' h_index wz1 i);
          assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
          ()
         )
          
      )
      else
      (
        let s_list' = create_successors_list_for_h_index g h_index wz i' in

        create_succcessors_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;

        assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
       
        ()
      )
  )

#restart-solver 


#restart-solver 

#reset-options "--z3rlimit 500"

#restart-solver 

let push_to_stack2_create_successors_for_h_index_lemma  (g:heap{well_formed_heap2 g})
                                                        (st: seq Usize.t {stack_props_func g st})
                                    
                    
                                                        (x: hp_addr{is_valid_header1 x g /\
                                                                   ~(Seq.mem (f_address x) st) /\
                                                                   (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                                   })  
                                                       (c:color{c == 2UL})

                                                       (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header1 h_index g})

                                                       (wz: wosize{wz == getWosize (read_word g h_index)})
                                                       (wz1: wosize{(wz1 == getWosize (read_word (snd (push_to_stack2 g st x)) h_index))})

                                                
                                                       (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                     : Lemma
                                        (requires (wz == wz1) /\ 
                                                  (is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                  (color_of_object1 x g == white) /\
                                                  (Seq.mem x (get_allocated_block_addresses g)) /\
                                                  
                                                  (h_index_within_limits g h_index) (*/\
                                                  (h_index_within_limits (snd (push_to_stack2 g st x)) h_index)*))
                                        (ensures create_successors_list_for_h_index g h_index wz i == 
                                                   create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i) = 

if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in

   
   let g' = colorHeader1 x g gray in 

   assert (well_formed_heap2 g');
    
    objects2_equal_lemma 0UL g g';
    
    get_allocated_block_addresses_lemma g g' x c;
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))));
    assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
    //colorHeader1_Lemma x g c; 

    assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
    fieldaddress_within_limits_lemma_x_all g;

    assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
    //well_formed_allocated_blocks_lemma g x c g';
    

    //assert (well_formed_allocated_blocks g');
    
    //assert (Seq.mem f_x stk');
    G.is_vertex_set_lemma2 stk';
    assert (G.is_vertex_set stk');
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))));
    assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
    fieldaddress_within_limits_lemma_x_all g';
    
    create_succcessors_for_h_index_lemma1 g h_index wz i x c g' wz1;
    assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
    assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i);
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
   get_allocated_block_addresses_lemma g g' x c;
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))));
    assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
    //colorHeader1_Lemma x g c; 

    assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
    fieldaddress_within_limits_lemma_x_all g;

    assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
    
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))));
    assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
    fieldaddress_within_limits_lemma_x_all g';
    
    //well_formed_allocated_blocks_lemma g x c g';
    

    //assert (well_formed_allocated_blocks g');
    
    G.snoc_unique_lemma f_x st;
    assert (G.is_vertex_set st');
   
   
    create_succcessors_for_h_index_lemma1 g h_index wz i x c g' wz1;
    assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
    assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i);
    ()
 )

#restart-solver 

#restart-solver

let darken_helper_create_successors_for_h_index_lemma (g:heap{well_formed_heap2 g})
                                                      (st: seq Usize.t{stack_props_func g st})
                                                      (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header1 h_index g})
                                                      (c:color{c == 2UL})
                                                      (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                                                        (Usize.v (tag_of_object1 hdr_id g) <> infix_tag) /\
                                                                        (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n)})
                                                      (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                                      (wz1: wosize{(wz1 == getWosize (read_word (snd (darken_helper g st hdr_id)) h_index))})
                                                      (j:Usize.t{Usize.v j <= Usize.v wz + 1 /\ Usize.v j >= 1})
                                                      
         
                                                      
          : Lemma
            (requires (wz == wz1) /\
                      (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                      (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (darken_helper g st hdr_id))) 
                                                                                             (snd (darken_helper g st hdr_id))) /\
                      (h_index_within_limits g h_index))
                      
            (ensures (create_successors_list_for_h_index g h_index wz j == 
                                    create_successors_list_for_h_index (snd (darken_helper g st hdr_id)) h_index wz1 j)) = 
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
   push_to_stack2_create_successors_for_h_index_lemma g st hdr_id c h_index wz wz1 j;
   ()
)
else
(
   ()
)

#restart-solver 

#restart-solver

let fieldPush_spec_body_create_successors_for_h_index_lemma  (g:heap{well_formed_heap2 g})
                                                             (st: seq Usize.t{stack_props_func g st})
                                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header1 h_index g })
                                                             (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                                             (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})  
                                                             (wz1: wosize{wz1 == getWosize (read_word (snd (fieldPush_spec_body1 g st h_index wz i)) h_index) 
                                                                                   })
                                                            (c:color{c == 2UL})
                                                            (j:Usize.t{Usize.v j <= Usize.v wz + 1 /\ Usize.v j >= 1})
                                                                    
                                      : Lemma
                                        (requires (wz == wz1) /\ 
                                                  
                                                  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                    (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i))) 
                                                                                                          (snd (fieldPush_spec_body1 g st h_index wz i))) /\
                                                  (h_index_within_limits g h_index))
                                        (ensures (create_successors_list_for_h_index g h_index wz j == 
                                                     create_successors_list_for_h_index (snd (fieldPush_spec_body1 g st h_index wz i)) h_index wz1 j)) =

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
        assert (well_formed_heap2 g');
        field_limits_allocated_blocks_lemma g';
        assert (Seq.mem parent_hdr (get_allocated_block_addresses g));
        
        darken_helper_create_successors_for_h_index_lemma g st h_index c parent_hdr wz wz1 j;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        field_limits_allocated_blocks_lemma g';
        assert (Seq.mem h_addr_succ (get_allocated_block_addresses g));
        
        darken_helper_create_successors_for_h_index_lemma g st h_index c h_addr_succ wz wz1 j;
        ()
        
      )
   )
  else
   ( 
       ()
   )

#restart-solver

#restart-solver 

#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#restart-solver 

let graph_successors_create_from_an_index_equivalence_lemma  (g:heap{well_formed_heap2 g})
                                                             (st: seq Usize.t{stack_props_func g st})
                                                           
                                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})

                                                             (wz: wosize{wz == getWosize (read_word g h_index)})

                                                             (j:Usize.t{Usize.v j < Usize.v wz + 1 /\ Usize.v j >= 1})

                                                                
                                                                                     
                                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                                                 (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                                                 (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                                                 (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                                
                                                              (i:Usize.t {Usize.v i <= Seq.length f})
                                                              
                                                              (g': heap {well_formed_heap2 g' /\
                                                                            g' == (snd (fieldPush_spec_body1 g st h_index wz j))})
                                                              (wz1: wosize{wz1 == getWosize (read_word g' h_index)})
                                                              (f1: seq Usize.t)

                                             : Lemma
                                               (requires (wz == wz1) /\ (f == f1) /\
                                                         (h_index_within_limits g h_index)  /\
                                                         (h_index_within_limits g' h_index) /\
                                                         (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                                         (all_field_address_are_word_aligned (get_allocated_block_addresses g') g') /\
                                                          (let grph = create_graph_from_heap g' in
                                                              let l = G.successors grph (f_address h_index) in
                                                              (f1 == l) /\ (Seq.length f1 <= Usize.v wz1)))
                                               (ensures graph_successors_create_from_an_index g h_index f i == graph_successors_create_from_an_index g' h_index f1 i) = ()

#restart-solver 

#reset-options "--z3rlimit 500"

#restart-solver

#restart-solver

let stack_properties   (g:heap{well_formed_heap2 g})
                       (st: seq Usize.t) =
  G.is_vertex_set st /\  (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                                  Seq.mem x st)

let vl_properties(g:heap{well_formed_heap2 g})
                 (vl: seq Usize.t) =
  (G.is_vertex_set vl) /\  (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl)
                                                                     
let h_index_properties (g:heap{well_formed_heap2 g})
                        (h_index:hp_addr) =
   Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\ (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                 is_valid_header h_index g

#restart-solver 

#restart-solver


let slice_length_props (g:heap{well_formed_heap2 g}) =
     (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)

let slice_length_props_lemma (g:heap{well_formed_heap2 g})
                       (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}) 
                : Lemma 
                  (ensures length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)=
 
lemma_len_slice g (Usize.v t) ((Usize.v t) + (Usize.v mword));
()

let slice_length_props_all_lemma (g:heap{well_formed_heap2 g}) 
                : Lemma
                  (ensures (slice_length_props g)) =
 Classical.forall_intro (Classical.move_requires (slice_length_props_lemma  g))   


let lemma_len_slice_invoke1 (g:heap{well_formed_heap2 g})
                           (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0})
                : Lemma
                  (ensures (length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)) =
lemma_len_slice g (Usize.v t) ((Usize.v t) + (Usize.v mword));
()

let lemma_len_slice_invoke_all1 (g:heap{well_formed_heap2 g})
                : Lemma
                  (ensures (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)) =
Classical.forall_intro (Classical.move_requires (lemma_len_slice_invoke g))

let create_succcessors_for_h_index_lemma5_helper (g:heap{well_formed_heap2 g})
                                                  (g':heap{well_formed_heap2 g'}) 
                                                  (h_index:hp_addr {Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                    is_valid_header1 h_index g /\
                                                                     is_valid_header1 h_index g'})
                                                 (wz:wosize{(Usize.v wz == Usize.v (getWosize (read_word g h_index)))})=
                                                     
 (forall i. Usize.v i >= 1 /\ Usize.v i <= Usize.v wz + 1 ==> is_hp_addr (Usize.add h_index (Usize.mul i mword)) /\
                                                      read_word g (Usize.add h_index (Usize.mul i mword)) ==
                                                      read_word g' (Usize.add h_index (Usize.mul i mword)))

#restart-solver

let fieldPush_spec_successor_push_itr_equivalence_lemma2_pre_props  (g:heap{well_formed_heap2 g})
                                                                        (st: seq Usize.t{stack_props_func g st})
                                                                        (h_index:hp_addr{ Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                               (Usize.v h_index % Usize.v mword == 0) /\
                                                                               is_valid_header1 h_index g})
                                                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                                                        (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                        (j:Usize.t)
                                                                        (vl: seq Usize.t{vl_props_func g vl}) 
                                                                         =
(h_index_within_limits g h_index) /\
(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
(Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
(Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
(Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
(graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                          (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
(forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
(forall x. Seq.mem x vl ==> ~(Seq.mem x st))

#restart-solver 

let fieldPush_spec_successor_push_itr_equivalence_lemma2_post_props  (g:heap{well_formed_heap2 g /\
                                                                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)})
                                                                        (st: seq Usize.t{stack_props_func g st})
                                                                        (h_index:hp_addr{ Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                               (Usize.v h_index % Usize.v mword == 0) /\
                                                                               is_valid_header1 h_index g /\
                                                                               (h_index_within_limits g h_index) /\
                                                                               (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices)})
                                                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index)) /\
                                                                                   Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz}) 
                                                                        (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                        (j:Usize.t{(Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)))})
                                                                        (vl: seq Usize.t{vl_props_func g vl /\
                                                                                         (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                                                         (forall x. Seq.mem x vl ==> ~(Seq.mem x st))}) 
                                                                         =
((fst (fieldPush_spec1 g st h_index wz i)) ==  G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index))
                                                                                  (vl)
                                                                                  (st)
                                                                                  (Usize.v j))

let length_less_than_or_equal_lemma (s:seq Usize.t)
                                    (j:Usize.t)
            : Lemma
              (requires Usize.v j <= Seq.length s /\ ~(Usize.v j == Seq.length s))
              (ensures Usize.v j < Seq.length s) = ()
              
#restart-solver

let push_to_stack2_vl_props_lemma (g:heap{well_formed_heap2 g})
                                  (st: seq Usize.t{stack_props_func g st})
                                    
                                  (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st) /\ (color_of_object1 x g == white) /\
                                                 (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                })
                                  (vl: seq Usize.t{vl_props_func g vl}) 
                     : Lemma
                     (ensures (vl_props_func (snd (push_to_stack2 g st x)) vl)) =
assert (vl_props_func g vl);
assert ((forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
        (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==>  Seq.mem x vl));
push_to_stack2_visited_list_valid_header_lemma g st x vl;
push_to_stack_mem_lemma_black_nodes_visited_list_lemma g st x vl;
assert (vl_props_func (snd (push_to_stack2 g st x)) vl);
()

let fieldPush_spec_body_vl_props_lemma  (g:heap{well_formed_heap2 g})
                                        (st: seq Usize.t{stack_props_func g st})
                                        (h_index:hp_addr{is_valid_header1 h_index g})
                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                        (vl: seq Usize.t{vl_props_func g vl}) 
                            : Lemma
                              (ensures (vl_props_func (snd (fieldPush_spec_body1 g st h_index wz i)) vl)) =
fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;
assert (vl_props_func (snd (fieldPush_spec_body1 g st h_index wz i)) vl);
()

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver

let h_index_field_within_heap_size (g:heap{well_formed_heap2 g})
                                       
                                   (h_index:hp_addr{ Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                         (Usize.v h_index % Usize.v mword == 0) /\
                                                         is_valid_header1 h_index g})
                                   (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                   (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                        : Lemma
                          (ensures (Usize.v h_index + (Usize.v i * Usize.v mword) < heap_size)) =
assert (well_formed_heap2 g);
assert (is_valid_header1 h_index g);
assert (Seq.mem h_index (get_allocated_block_addresses g));
field_limits_allocated_blocks_lemma g;
assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
assert (Usize.v wz == Usize.v (getWosize (read_word g h_index)));
assert (is_fields_within_limit1 h_index wz);
()

#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries always" (BE CAREFUL IN USING SPLIT QUERIES --- SOMETIMES IT CAUSES UNDEFINED BEHAVIOUR)

#restart-solver

//#reset-options "--z3rlimit 1000"

#restart-solver

#push-options "--split_queries always"


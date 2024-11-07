module Spec.GC_part09

include Spec.GC_part08

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

#restart-solver 

#restart-solver


#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver


#restart-solver 

#restart-solver 

let darken_helper_black_nodes_mem_lemma(g:heap{well_formed_heap2 g})
                                       (st: seq Usize.t{stack_props_func g st})
                                       (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                               (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
          : Lemma
            (ensures (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                           Seq.mem y (get_black_block_addresses (snd (darken_helper g st hdr_id)) 
                                                                (get_allocated_block_addresses (snd (darken_helper g st hdr_id)))))) = 
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
   push_to_stack2_lemma_black_nodes1 g st hdr_id;
   assert (G.is_vertex_set st');
          
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');

   assert (color_of_object1 hdr_id g == white);
   push_to_stack2_lemma g st hdr_id;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   ()
)
else
(
   ()
)

#restart-solver 

let fieldPush_spec_body_lemma_black_nodes_mem_lemma_props (g:heap{well_formed_heap2 g})
                                                          (st: seq Usize.t{stack_props_func g st})
                                                          (h_index:hp_addr{is_valid_header1 h_index g})
                                                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                                          (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) =
  (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                          Seq.mem y (get_black_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)))))
                                                              

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let fieldPush_spec_body_black_nodes_mem_lemma (g:heap{well_formed_heap2 g})
                                              (st: seq Usize.t{stack_props_func g st})
                                              (h_index:hp_addr{is_valid_header1 h_index g})
                                              (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                              (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                             
                        : Lemma
                          (ensures (fieldPush_spec_body_lemma_black_nodes_mem_lemma_props g st h_index wz i)) = 

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

  lemma_len_slice g (Usize.v  succ_index) ((Usize.v succ_index) + (Usize.v mword));
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
        darken_helper_black_nodes_mem_lemma g st parent_hdr;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        darken_helper_black_nodes_mem_lemma g st h_addr_succ;
        ()
      )
   )
  else
   ( 
       ()
   )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

#restart-solver 

#restart-solver

let darken_helper_valid_header_visited_set_lemma (g:heap{well_formed_heap2 g})
                                                      (st: seq Usize.t{stack_props_func g st})
                                                      (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                                                      (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
                                                      (vl: seq Usize.t{vl_props_func g vl})
         : Lemma
           (ensures ((forall y. Seq.mem y vl ==> is_valid_header1 (hd_address y) (snd (darken_helper g st hdr_id))))) = 

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
   push_to_stack2_visited_list_valid_header_lemma g st hdr_id vl;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   ()
)
else
(
   ()
)

let fieldPush_spec_body_valid_header_visited_set_lemma  (g:heap{well_formed_heap2 g})
                                                        (st: seq Usize.t{stack_props_func g st})
                                                        (h_index:hp_addr{is_valid_header1 h_index g})
                                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                        (vl: seq Usize.t{vl_props_func g vl}) 
                            : Lemma
                              (ensures ((forall y. Seq.mem y vl ==> is_valid_header1 (hd_address y) (snd (fieldPush_spec_body1 g st h_index wz i))))) =

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
        darken_helper_valid_header_visited_set_lemma g st parent_hdr vl;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        darken_helper_valid_header_visited_set_lemma g st h_addr_succ vl;
        ()
      )
   )
  else
   ( 
       ()
   )

#restart-solver 

#restart-solver

let darken_helper_black_nodes_visited_set_lemma (g:heap{well_formed_heap2 g})
                                                (st: seq Usize.t{stack_props_func g st})
                                                (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                                                      (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
                                                (vl: seq Usize.t{vl_props_func g vl})
         : Lemma
           (ensures (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (darken_helper g st hdr_id))) /\ 
                                                  isBlackObject1 (hd_address y) (snd (darken_helper g st hdr_id)) <==>  
                                                                                           Seq.mem y vl)) = 
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
  push_to_stack_mem_lemma_black_nodes_visited_list_lemma  g st hdr_id vl;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   ()
)
else
(
   ()
)

let fieldPush_spec_body_black_nodes_visited_set_lemma (g:heap{well_formed_heap2 g})
                                                      (st: seq Usize.t{stack_props_func g st})
                                                      (h_index:hp_addr{is_valid_header1 h_index g})
                                                      (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                                      (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                      (vl: seq Usize.t{vl_props_func g vl}) 
                            : Lemma
                              (ensures (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (fieldPush_spec_body1 g st h_index wz i))) /\ 
                                                  isBlackObject1 (hd_address y) (snd (fieldPush_spec_body1 g st h_index wz i)) <==>  
                                                                                           Seq.mem y vl)) = 
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
        darken_helper_black_nodes_visited_set_lemma g st parent_hdr vl;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        darken_helper_black_nodes_visited_set_lemma g st h_addr_succ vl;
        ()
      )
   )
  else
   ( 
       ()
   )


#restart-solver 

#restart-solver

#restart-solver

let darken_helper_graph_lemma (g:heap{well_formed_heap2 g})
                              (st: seq Usize.t{stack_props_func g st})
                              (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                               (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
         : Lemma
           (requires (
                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g))) 
                                     
           (ensures (create_graph_from_heap g == create_graph_from_heap (snd (darken_helper g st hdr_id)))) =  

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

   
   push_to_stack2_graph_lemma g st hdr_id;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   ()
)
else
(
   ()
)

#restart-solver 

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let fieldPush_spec_body_graph_lemma (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{stack_props_func g st})
                                    (h_index:hp_addr{is_valid_header1 h_index g})
                                    (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                    (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (requires (
                                     (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                     
                                     (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8) /\
                                 
                               (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice (snd (fieldPush_spec_body1 g st h_index wz i)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)))
                                     
                          (ensures (create_graph_from_heap g == create_graph_from_heap (snd (fieldPush_spec_body1 g st h_index wz i)))) = 

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
  
  
  let allocs = get_allocated_block_addresses g in
  fieldaddress_within_limits_lemma_x_all g;
  assert (forall i x.  Seq.mem x allocs /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
 
  
                                          
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
        assert (Seq.mem parent_hdr (get_allocated_block_addresses g));
        
        darken_helper_graph_lemma g st parent_hdr;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        assert (Seq.mem h_addr_succ (get_allocated_block_addresses g));
        
        darken_helper_graph_lemma g st h_addr_succ;
        ()
      )
   )
  else
   ( 
       ()
   )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

let fieldPush_spec1_fields_lemma1_props (g:heap{well_formed_heap2 g})
                                            (st: seq Usize.t{stack_props_func g st})
                                            (h_index:hp_addr{is_valid_header1 h_index g})
                                            (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                            (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1}) =
 (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g t) == 
                                                                                   getWosize (read_word (snd (fieldPush_spec1 g st h_index wz i)) t)) /\
                   (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (fieldPush_spec1 g st h_index wz i)) y)



#restart-solver

//#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

let rec fieldPush_spec1_fields_lemma1 (g:heap{well_formed_heap2 g})
                                      (st: seq Usize.t{stack_props_func g st})
                                      (h_index:hp_addr{is_valid_header1 h_index g})
                                      (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                      (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
          :Lemma
          (ensures (fieldPush_spec1_fields_lemma1_props g st h_index wz i))
          (decreases ((Usize.v wz + 1) - Usize.v i)) =

if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       
       assert (fieldPush_spec1_fields_lemma1_props g st h_index wz i);
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body g st h_index wz i in
       (*assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
                                         Seq.mem x st'));*)
       fieldPush_spec_body_fields_lemma g st h_index wz i;
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st_hp = fieldPush_spec1 g' st' h_index wz i' in
       fieldPush_spec1_fields_lemma1 g' st' h_index wz i';
       ()
    )

#restart-solver

#restart-solver

let rec fieldPush_spec1_black_nodes_lemma1 (g:heap{well_formed_heap2 g})
                                           (st: seq Usize.t{stack_props_func g st})
                                           (h_index:hp_addr{is_valid_header1 h_index g})
                                           (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                           (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (ensures (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses  (snd (fieldPush_spec1 g st h_index wz i))
                                                                         (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i))))))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body1 g st h_index wz i in
       

       fieldPush_spec_body_black_nodes_mem_lemma g st h_index wz i;
       fieldPush_spec_body1_black_nodes_lemma g st h_index wz i;
       (*assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                          Seq.mem y (get_black_block_addresses g' 
                                                              (get_allocated_block_addresses g')));*)
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st_hp = fieldPush_spec1 g' st' h_index wz i' in
       fieldPush_spec1_black_nodes_lemma1 g' st' h_index wz i';
       (*assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses (snd st_hp) (get_allocated_block_addresses (snd st_hp))));
                                                                         
       
       
       assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses (snd (fieldPush_spec1 g' st' h_index wz i')) 
                                                      (get_allocated_block_addresses (snd (fieldPush_spec1 g' st' h_index wz i')))));
       
       assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses (snd (fieldPush_spec1 g st h_index wz i)) 
                                                      (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i)))));*)
       ()
    )

#restart-solver 

#restart-solver

let lemma_len_slice_invoke (g:heap{well_formed_heap2 g})
                           (t:hp_addr)
                : Lemma
                  (ensures (length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)) =
lemma_len_slice g (Usize.v t) ((Usize.v t) + (Usize.v mword));
()

let lemma_len_slice_invoke_all (g:heap{well_formed_heap2 g})
                : Lemma
                  (ensures (forall (t:hp_addr(*{Usize.v t < heap_size /\ Usize.v t % 8 == 0}*)).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)) =
Classical.forall_intro (Classical.move_requires (lemma_len_slice_invoke g))

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let rec fieldPush_spec1_graph_lemma (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{stack_props_func g st})
                                    (h_index:hp_addr{is_valid_header1 h_index g})
                                    (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                    (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (requires (
                                     (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                     (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i))) 
                                                    (snd (fieldPush_spec1 g st h_index wz i)))))
                          
                          (ensures (create_graph_from_heap g == create_graph_from_heap (snd (fieldPush_spec1 g st h_index wz i)))) 
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       fieldPush_fieldPush_spec_body_lemma1 g st h_index wz i;
       assert (g == snd (fieldPush_spec1 g st h_index wz i));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i >= 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st', g' = fieldPush_spec_body1 g st h_index wz i in
       
       
       (*assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
                                         Seq.mem x st'));*)
       
       let st'', g'' = fieldPush_spec1 g' st' h_index wz i' in
       field_limits_allocated_blocks_lemma g'';
       field_contents_within_limits_allocated_blocks_lemma g'';
       lemma_len_slice_invoke_all g;
       lemma_len_slice_invoke_all g';
       (*assert (forall (t:hp_addr). length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8);
                                 
       assert (forall (t:hp_addr). length (slice (snd (fieldPush_spec_body1 g st h_index wz i)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8);*)
                                 
       fieldPush_spec_body_graph_lemma g st h_index wz i;
       fieldaddress_within_limits_lemma_x_all g'';
       assert (all_field_address_are_word_aligned (get_allocated_block_addresses g'') g'');
       fieldPush_spec1_graph_lemma g' st' h_index wz i';
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       ()
  )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

#restart-solver

let arithmetic_lemma (i:Usize.t)
                     (wz:wosize)
            : Lemma
              (requires (Usize.v i < Usize.v wz + 1))
              (ensures (Usize.v i <= Usize.v wz)) = 
 assert (Usize.v i < Usize.v wz + 1);
 assert (Usize.v i <= Usize.v wz);
 ()

#restart-solver 

let arithmetic_lemma1 (i:Usize.t)
                     (wz:wosize)
            : Lemma
              (requires (Usize.v i <= Usize.v wz))
              (ensures (Usize.v i - 1 < Usize.v wz)) = 
 assert (Usize.v i <= Usize.v wz);
 assert (Usize.v i - 1 < Usize.v wz);
 ()


#restart-solver

#restart-solver 

let h_index_within_limits (g: heap {well_formed_heap2 g})
                          (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g}) = 
 (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
 (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
   (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                          (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) 

#restart-solver 

#restart-solver

//#push-options "--z3rlimit 500"

#restart-solver

let seq_empty_slice_lemma (f:seq Usize.t)
                          (i:Usize.t {Usize.v i == Seq.length f})
            : Lemma
              (ensures Seq.empty #Usize.t == Seq.slice f (Usize.v i) (Seq.length f)) =
()

let seq_cons_slice_lemma (succ: Usize.t)
                         (f: seq Usize.t)
                         (rest_of_list: seq Usize.t)
                         (i:Usize.t {Usize.v i < Seq.length f})
                         (i':Usize.t {Usize.v i' == Usize.v i  + 1})
            : Lemma
              (requires (rest_of_list == Seq.slice f (Usize.v i') (Seq.length f)) /\
                        (succ == Seq.index f (Usize.v i)))
              (ensures  (Seq.cons succ rest_of_list == Seq.slice f (Usize.v i) (Seq.length f)) /\
                        (Seq.head (Seq.cons succ rest_of_list) == succ) /\
                        (Seq.tail (Seq.cons succ rest_of_list) == rest_of_list)) =
()

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let rec graph_successors_create_from_an_index (g: heap {well_formed_heap2 g})
                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     
                                                                                     h_index_within_limits g h_index})
                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                              (i:Usize.t {Usize.v i <= Seq.length f}) 
                                  : Tot (s_list': seq Usize.t{s_list' == Seq.slice f (Usize.v i) (Seq.length f)})
                              (decreases (Seq.length f - Usize.v i))= 
if Usize.v i = Seq.length f then
 (
   
    seq_empty_slice_lemma f i;
    Seq.empty #Usize.t
 )
 else
 (
   let succ = Seq.index f (Usize.v i) in
   let i' = Usize.add i 1UL in
   let rest_of_list = graph_successors_create_from_an_index g h_index f i' in
   assert (rest_of_list == Seq.slice f (Usize.v i') (Seq.length f));
   lemma_tl  succ rest_of_list;
   let s_list' = Seq.cons succ rest_of_list in
   seq_cons_slice_lemma succ f rest_of_list i i';
   assert (s_list' == Seq.slice f (Usize.v i) (Seq.length f));
   s_list'
 )

let graph_successors_create_from_an_index_lemma (g: heap {well_formed_heap2 g})
                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     
                                                                                     h_index_within_limits g h_index})
                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                    (i:Usize.t {Usize.v i < Seq.length f}) 
                                  : Lemma
                                    (requires (Seq.length (graph_successors_create_from_an_index g h_index f i) > 0))
                                    (ensures (Seq.head (graph_successors_create_from_an_index g h_index f i) == Seq.index f (Usize.v i))) = 

if Usize.v i = Seq.length f then
 (
   
    seq_empty_slice_lemma f i;
    ()
 )
 else
 (
   let succ = Seq.index f (Usize.v i) in
   let i' = Usize.add i 1UL in
   let rest_of_list = graph_successors_create_from_an_index g h_index f i' in
   assert (rest_of_list == Seq.slice f (Usize.v i') (Seq.length f));
   lemma_tl  succ rest_of_list;
   let s_list' = Seq.cons succ rest_of_list in
   seq_cons_slice_lemma succ f rest_of_list i i';
   assert (s_list' == Seq.slice f (Usize.v i) (Seq.length f));
   ()
 )

let graph_successors_create_from_an_index_lemma1 (g: heap {well_formed_heap2 g})
                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g  /\
                                                                                     h_index_within_limits g h_index})
                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                    (i:Usize.t {Usize.v i < Seq.length f}) 
                                                    (i': Usize.t {Usize.v i' == Usize.v i + 1})
                                  : Lemma
                                    (requires (Seq.length (graph_successors_create_from_an_index g h_index f i) > 0))
                                    (ensures (Seq.tail (graph_successors_create_from_an_index g h_index f i) == (graph_successors_create_from_an_index g h_index f i'))) =

if Usize.v i = Seq.length f then
 (
   
    seq_empty_slice_lemma f i;
    ()
 )
 else
 (
   let succ = Seq.index f (Usize.v i) in
   let i' = Usize.add i 1UL in
   let rest_of_list = graph_successors_create_from_an_index g h_index f i' in
   assert (rest_of_list == Seq.slice f (Usize.v i') (Seq.length f));
   lemma_tl  succ rest_of_list;
   let s_list' = Seq.cons succ rest_of_list in
   seq_cons_slice_lemma succ f rest_of_list i i';
   assert (s_list' == Seq.slice f (Usize.v i) (Seq.length f));
   ()
 )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

let head_content_successor_list_in_heap_props (g:heap{well_formed_heap2 g}) 

                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g  /\
                                                                                     h_index_within_limits g h_index})
                                         
                                              (wz: wosize{valid_wosize g h_index wz})
                         
                                              (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1 /\
                                                         (is_hp_addr (Usize.add h_index (Usize.mul i mword)))}) =
 ((*if succ of h_index at index i is a pointer*)
   isPointer_succ g h_index wz i ==>
   (*if the succ points to an infix object*)
          Usize.v (tag_succ g h_index wz i) == infix_tag  ==> 
     (*then head of succ_list starting at index i is the object address of the parent closure of the infix object*)
     Seq.head (create_successors_list_for_h_index g h_index wz i) ==
       f_address (parent_closure_of_infix_object g h_index i)) /\
 
 ((*if succ of h_index at index i is a pointer*)
   isPointer_succ g h_index wz i ==>
   (*if the succ points to an object whose tag is not infix tag*)
          Usize.v (tag_succ g h_index wz i) <> infix_tag  ==> 
     (*then head of succ_list starting at index i is the object address of succ*)
     Seq.head (create_successors_list_for_h_index g h_index wz i) ==
       get_succ_value g h_index wz i)     

let create_successors_list_for_h_index_from_i_index_lemma (g:heap{well_formed_heap2 g}) 

                                                          (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g  /\
                                                                                     h_index_within_limits g h_index})
                                         
                                                          (wz: wosize{valid_wosize g h_index wz})
                         
                                                          (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                   : Lemma
                                     (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                     (ensures head_content_successor_list_in_heap_props g h_index wz i) = 
()



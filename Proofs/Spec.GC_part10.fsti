module Spec.GC_part10

include Spec.GC_part09

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

#reset-options "--z3rlimit 1000 --split_queries always"

let create_successors_list_for_h_index_from_i_index_lemma_tail_helper (g:heap{well_formed_heap2 g}) 

                                                                      (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g  /\
                                                                                     h_index_within_limits g h_index})
                                         
                                                                      (wz: wosize{valid_wosize g h_index wz})
                         
                                                                      (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                                   
                                    : Lemma
                                      (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\ (isPointer(Usize.add h_index (Usize.mul i mword)) g))
                                      (ensures (create_successors_list_for_h_index g h_index wz i <> Seq.empty) /\ 
                                                 Seq.length (create_successors_list_for_h_index g h_index wz i) > 0) = ()

#restart-solver 

#restart-solver

let create_successors_list_for_h_index_from_i_index_lemma_tail (g:heap{well_formed_heap2 g}) 

                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g  /\
                                                                                     h_index_within_limits g h_index})
                                         
                                                               (wz: wosize{valid_wosize g h_index wz})
                         
                                                               (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                               (i':Usize.t{Usize.v i' == Usize.v i + 1}) 
                                    : Lemma
                                      (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\ (isPointer(Usize.add h_index (Usize.mul i mword)) g) /\
                                                 Seq.length (create_successors_list_for_h_index g h_index wz i) > 0)
                                      (ensures Seq.tail (create_successors_list_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i') =

if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
       
       ()
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 
           ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
        
      let s_list' = create_successors_list_for_h_index g h_index wz i' in
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
           let parent_succ = f_address parent_hdr in
           lemma_tl parent_succ s_list'; 
        
           let s_list = Seq.cons parent_succ s_list' in 
        
           assert (Seq.head s_list == parent_succ);

           ()
         )
         else
         (
           
           lemma_tl succ s_list'; 
        
           let s_list = Seq.cons succ s_list' in 
        
           assert (Seq.head s_list == succ);

           ()
         )
      )
      else
      (
       
        ()
      )
    )

#restart-solver 

#restart-solver 

#restart-solver

let slice_lemma (#a:Type)
                (s:seq a)
       : Lemma 
         (ensures s == Seq.slice s 0 (Seq.length s)) = ()


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

let graph_successors_create_from_index_0_equals_graph_successors (g: heap {well_formed_heap2 g})
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                                                 
                                        : Lemma
                                          (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                    (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                    (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index))) /\
                                                    0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)))
                                          (ensures G.successors (create_graph_from_heap g) (f_address h_index) == 
                                                    graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL) = 
let s_list' =  graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL in
assert (s_list' == Seq.slice (G.successors (create_graph_from_heap g) (f_address h_index)) 0 (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))));
slice_lemma (G.successors (create_graph_from_heap g) (f_address h_index));
assert (G.successors (create_graph_from_heap g) (f_address h_index) == 
         Seq.slice (G.successors (create_graph_from_heap g) (f_address h_index)) 0 (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))));
assert (G.successors (create_graph_from_heap g) (f_address h_index) == 
         graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL);
()

#restart-solver 

#restart-solver 

#reset-options "--z3rlimit 500"


let graph_successors_from_0_and_heap_field_pointers_from_1_are_equal (g: heap {well_formed_heap2 g})
                                                                     (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                               
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                    (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                    (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index))) /\
                                                    0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                    Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
                                                    Usize.v (tag_of_object1 h_index g) <> closure_tag)
                                  (ensures graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) = 

graph_successors_create_from_index_0_equals_graph_successors g h_index;
assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
assert (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
              (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0);
assert (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);

graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
assert (Usize.v (tag_of_object1 h_index g) < no_scan_tag);
assert (Usize.v (tag_of_object1 h_index g) <> closure_tag);
assert (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
()

#push-options "--split_queries always"

#restart-solver

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


let graph_successors_from_0_and_heap_field_pointers_from_1_are_equal1 (g: heap {well_formed_heap2 g})
                                                                      (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                               
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                    (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                    (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index))) /\
                                                    0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                    Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
                                                    Usize.v (tag_of_object1 h_index g) == closure_tag)
                                  (ensures (let start_env = start_env_clos_info g (f_address h_index) in
                                            let start_env_plus_one = Usize.add start_env 1UL in
                                               graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 
                                                                                             (start_env_plus_one))) = 
graph_successors_create_from_index_0_equals_graph_successors g h_index;
assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
assert (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
              (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0);
assert (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);

graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
assert (Usize.v (tag_of_object1 h_index g) < no_scan_tag);
assert (Usize.v (tag_of_object1 h_index g) == closure_tag);
(*assert (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 
                                                (start_env_clos_info g (f_address h_index)));*)
()

#reset-options "--z3rlimit 500"
#push-options "--split_queries always"

let create_successors_list_for_h_index_recursing_property_lemma (g: heap {well_formed_heap2 g})
                                                                (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                         
                                                                (wz: wosize{valid_wosize g h_index wz})
                         
                                                                (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                                (i':Usize.t{Usize.v i' == Usize.v i + 1}) 
                                       : Lemma
                                         (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                         (ensures ~(isPointer(Usize.add h_index (Usize.mul i mword)) g) ==> create_successors_list_for_h_index g h_index wz i == 
                                                                                create_successors_list_for_h_index g h_index wz i') = ()

let successors_list_recursing_props (g: heap {well_formed_heap2 g})
                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                         
                                    (wz: wosize{valid_wosize g h_index wz})
                         
                                    (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                    (i':Usize.t{Usize.v i' == Usize.v i + 1 /\ (is_hp_addr (get_succ_address g h_index wz i))}) =
 (isPointer_succ g h_index wz i ==> 
       Usize.v (tag_succ g h_index wz i) == infix_tag  ==> 
           create_successors_list_for_h_index g h_index wz i == 
           Seq.cons  (f_address (parent_closure_of_infix_object g h_index i)) (create_successors_list_for_h_index g h_index wz i')) /\
 
 (isPointer_succ g h_index wz i ==> 
      Usize.v (tag_succ g h_index wz i) <> infix_tag  ==> 
           create_successors_list_for_h_index g h_index wz i == 
           Seq.cons  (get_succ_value g h_index wz i) (create_successors_list_for_h_index g h_index wz i'))

let create_successors_list_for_h_index_recursing_property_lemma1 (g:heap{well_formed_heap2 g}) 

                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                         
                                                                 (wz: wosize{valid_wosize g h_index wz})
                         
                                                                 (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                                 (i':Usize.t{Usize.v i' == Usize.v i + 1})
                                       : Lemma
                                         (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                         (ensures (successors_list_recursing_props g h_index wz i i')) =
()

let create_successors_list_for_h_index_recursing_property_lemma2 (g:heap{well_formed_heap2 g}) 
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                           
                                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                 (i:Usize.t{Usize.v i == Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                        : Lemma
                                          (ensures create_successors_list_for_h_index g h_index wz i == Seq.empty) = ()

#restart-solver

let create_successors_list_for_h_index_recursing_property_lemma3 (g:heap{well_formed_heap2 g}) 
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                           
                                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                 (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                 (i':Usize.t{Usize.v i' == Usize.v i + 1})
                                        : Lemma
                                          (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                          (ensures (create_successors_list_for_h_index g h_index wz i == Seq.empty) ==> 
                                                      create_successors_list_for_h_index g h_index wz i' == Seq.empty) = ()

let create_successors_list_for_h_index_recursing_property_lemma4 (g:heap{well_formed_heap2 g}) 
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                           
                                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                 (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                
                                        : Lemma
                                          (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                          (ensures (create_successors_list_for_h_index g h_index wz i == Seq.empty) ==> 
                                                       ~(isPointer(Usize.add h_index (Usize.mul i mword)) g)) = ()

#restart-solver

let seq_cons_non_empty_lemma (s:seq Usize.t)
                             (x:Usize.t)
                             (s':seq Usize.t{s' == Seq.cons x s})
         : Lemma
           (ensures ~(s' == Seq.empty)) =
 ()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

let graph_successors_create_from_an_index_empty_lemma (g: heap {well_formed_heap2 g})
                                                      (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                                      (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                      (i:Usize.t {Usize.v i <= Seq.length f})
                            : Lemma
                              (ensures (graph_successors_create_from_an_index g h_index f i) == Seq.empty ==>
                                             Usize.v i == Seq.length f) = 
if Usize.v i = Seq.length f then
 (
   
    seq_empty_slice_lemma f i;
    let s = Seq.empty #Usize.t in
    assert (s == graph_successors_create_from_an_index g h_index f i);
    assert (s == Seq.empty);
    assert (Usize.v i == Seq.length f);
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
   seq_cons_non_empty_lemma rest_of_list succ s_list';
   assert (~(s_list' == Seq.empty));
   ()
 )

let create_successors_list_for_h_index_i_equals_wz_plus_one_implies_succ_list_from_j_is_empty (g:heap{well_formed_heap2 g})
                                                                                              (st: seq Usize.t{stack_props_func g st})
                         
                                                                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                              is_valid_header1 h_index g /\
                                                                                                              h_index_within_limits g h_index})
                                           
                                                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                               (i:Usize.t{Usize.v i == Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                               (j:Usize.t)
                                          : Lemma
                                            (requires 
                                                      
                                            
                                                       h_index_within_limits g h_index /\
                                                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                       (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                       (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                       (Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                       (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                       (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i))
                                            (ensures Usize.v j == Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) = 
 create_successors_list_for_h_index_recursing_property_lemma2 g h_index wz i;
 assert (create_successors_list_for_h_index g h_index wz i == Seq.empty);
 assert ((graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) == Seq.empty);
 graph_successors_create_from_an_index_empty_lemma g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j;
 assert (Usize.v j == Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)));
 ()

#restart-solver

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j (g:heap{well_formed_heap2 g})
                                                                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                              is_valid_header1 h_index g /\
                                                                                                              h_index_within_limits g h_index})
                                           
                                                                                              (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                              (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                              (j:Usize.t) 
                                               : Lemma
                                                 (requires  (h_index_within_limits g h_index /\
                                                           (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                           (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                           (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                           (Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                           (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                           (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                           Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0))
                                            (ensures (let s_heap_i = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) in
                                                      let s_graph_j = (graph_successors_create_from_an_index g h_index 
                                                                          (G.successors (create_graph_from_heap g) (f_address h_index)) j) in
                                                       let hd = Seq.head s_heap_i in
                                                       let hd1 = Seq.head s_graph_j in
                                                      
                                                       let tl = Seq.tail s_heap_i in
                                                       let tl1 = Seq.tail s_graph_j in
                                                       (hd == hd1) /\ (tl == tl1))) = ()
                                                      
#reset-options "--z3rlimit 1000"

#restart-solver

let i_times_mword_multiple_of_mword (i:Usize.t{Usize.v i <= Usize.v max_wosize})
                     :Lemma 
                      (ensures (Usize.v (Usize.mul i mword) % Usize.v mword == 0)) = ()

#restart-solver

#restart-solver 

#restart-solver

#restart-solver

let field_ptr_construct (g:heap{well_formed_heap2 g}) 

                        (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                        (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                        is_valid_header1 h_index g /\
                                        h_index_within_limits g h_index})
                                           
                        (wz: wosize{wz == getWosize (read_word g h_index) /\ h_index_within_limits g h_index})
                         
                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
              : Tot (s:hp_addr{Usize.v s == Usize.v h_index + (Usize.v i * Usize.v mword)})=
  let s = (Usize.add h_index (Usize.mul i mword)) in
  i_times_mword_multiple_of_mword i;
  assert (Usize.v (Usize.mul i mword) % Usize.v mword == 0);
  assert (Usize.v h_index % Usize.v mword == 0);
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword); 
  assert (Usize.v s % Usize.v mword == 0);
  assert (Usize.v s < heap_size);
  assert (is_hp_addr s);
  s

let cons_length_lemma3 (#a:Type)
                       (s:seq a)
                       (s_cons:a)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s) > 0))=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ;
 assert (Seq.length s' > 0);
 ()

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver


#restart-solver

#push-options "--split_queries always"

#restart-solver

#restart-solver

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j1 (g:heap{well_formed_heap2 g})
                                                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                              is_valid_header1 h_index g /\
                                                                                                              h_index_within_limits g h_index})
                                           
                                                                                                (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                                (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                                (j:Usize.t) 
                                                    : Lemma
                                            (requires 
                                            
                                                       h_index_within_limits g h_index /\
                                                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                       (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                       (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                       (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                       (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                       (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                        (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                        (isPointer(Usize.add h_index (Usize.mul i mword)) g) /\
                                                        (Usize.v (tag_succ g h_index wz i) <> infix_tag) /\ 
                                                        Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0
                                                     )
                                              (ensures (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                        read_word g (Usize.add h_index (Usize.mul i mword)))) = 
 graph_successors_create_from_an_index_lemma g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j;
 create_successors_list_for_h_index_from_i_index_lemma g h_index wz i; 
 create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j g h_index wz i j;
 assert (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         read_word g (Usize.add h_index (Usize.mul i mword)));
 ()

(*Create a lemma similar to the above to handle the case when the field pointer points to an infix object*)

#restart-solver 

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j3 (g:heap{well_formed_heap2 g})
                                                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                              is_valid_header1 h_index g /\
                                                                                                              h_index_within_limits g h_index})
                                           
                                                                                                (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                                (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                                (j:Usize.t) 
                                                    : Lemma
                                            (requires  h_index_within_limits g h_index /\
                                                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                       (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                       (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                       (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                       (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                       (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                        (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                        (isPointer(Usize.add h_index (Usize.mul i mword)) g) /\
                                                        (Usize.v (tag_succ g h_index wz i) == infix_tag) /\ 
                                                        Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0
                                                     )
                                              (ensures (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         f_address (parent_closure_of_infix_object g h_index i))) =
graph_successors_create_from_an_index_lemma g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j;
create_successors_list_for_h_index_from_i_index_lemma g h_index wz i; 
create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j g h_index wz i j;
assert (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         f_address (parent_closure_of_infix_object g h_index i));
                                            
()

#reset-options "--z3rlimit 1000"
#restart-solver


#restart-solver

#push-options "--split_queries always"

#push-options "--z3rlimit 1000"

#restart-solver

let create_successors_list_for_h_index_pointer_lemma (g:heap{well_formed_heap2 g}) 

                                           (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header1 h_index g})
                                           
                                           (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                           (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})

                       : Lemma
                         (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x)))) /\
                                   (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) /\
                                   (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                            (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                            (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                   (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                   (isPointer (field_ptr_construct g h_index wz i) g))
                         (ensures (Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0))
                         
                         (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
       
       ()
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 
           ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
        
      let s_list' = create_successors_list_for_h_index g h_index wz i' in
      if isPointer succ_index g  then
      (
        
         let h_addr_succ = hd_address succ in
         (*test_allocs g h_index wz;
         assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
         assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
         assert (Seq.mem (hd_address succ) (objects2 0UL g));
         assert (is_valid_header (hd_address succ) g);

         assert (well_formed_allocated_blocks g);
         assert (Seq.mem h_index (get_allocated_block_addresses g));*)
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
           let parent_succ = f_address parent_hdr in
           lemma_tl parent_succ s_list'; 
        
           let s_list = Seq.cons parent_succ s_list' in 
        
           assert (Seq.head s_list == parent_succ);

           ()
         )
         else
         (
           
           lemma_tl succ s_list'; 
        
           let s_list = Seq.cons succ s_list' in 
        
           assert (Seq.head s_list == succ);

           ()
         )
      )
      else
      (
       
        ()
      )
    )

#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver  

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j2 (g:heap{well_formed_heap2 g})
                                                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                               is_valid_header1 h_index g})
                                           
                                                                                                (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                                (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                                (j:Usize.t) 
                                               : 
                                          Lemma
                                            (requires (h_index_within_limits g h_index) /\
                                                      (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                      (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                      
                                                      (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                      (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                      (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                      (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                      (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                      (isPointer(Usize.add h_index (Usize.mul i mword)) g)
                                                     )
                                             (ensures (let i' = Usize.add i 1UL in
                                                       let j' = Usize.add j 1UL in
                                                       (graph_successors_create_from_an_index g h_index ((G.successors (create_graph_from_heap g) (f_address h_index))) j' == 
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i')))  = 
 let i' = Usize.add i 1UL in
 let j' = Usize.add j 1UL in

 let s_heap_i = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) in
 let s_graph_j =  (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) in
 
 let sl = (G.successors (create_graph_from_heap g) (f_address h_index)) in
 assert (s_heap_i == s_graph_j);
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;

 create_successors_list_for_h_index_pointer_lemma g h_index wz i;
 assert (Seq.length s_heap_i > 0);
 assert (Seq.length s_graph_j > 0);
  
 let tl = Seq.tail s_heap_i in
 let tl1 = Seq.tail s_graph_j in
 create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j g h_index wz i j;
 assert (tl == tl1);
 let s_graph_j1 =  (graph_successors_create_from_an_index g h_index sl j') in
 graph_successors_create_from_an_index_lemma1 g h_index sl j j';
 assert (tl1 == s_graph_j1);
 let s_heap_i1 = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i') in
 create_successors_list_for_h_index_from_i_index_lemma_tail g h_index wz i i';
 assert (tl ==  s_heap_i1);
 assert (s_graph_j1 == s_heap_i1);
 assert (graph_successors_create_from_an_index g h_index sl j' == create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');
 ()

#restart-solver 

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"


#restart-solver

#restart-solver


#restart-solver

let fieldPush_spec_body_successor_push_body_equivalence_lemma3 (g:heap{well_formed_heap2 g})
                                                               (st: seq Usize.t{stack_props_func g st})
                                                               (h_index:hp_addr{is_valid_header1 h_index g})
                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                         
                                                               (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                               
                                                               (vl: seq Usize.t{vl_props_func g vl}) 
                                : Lemma
                                  (requires ((h_index_within_limits g h_index) /\
                                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                             (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                      
                                                     
                                             (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                 
                                             (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                             ( ~(isPointer(Usize.add h_index (Usize.mul i mword)) g)) /\
                                                  
                                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                                        (ensures (fst (fieldPush_spec_body g st h_index wz i) == st)) = ()
                                                  
#restart-solver

#restart-solver 

#push-options "--split_queries always"

#restart-solver

let gray_black_stack_vl_mem_lemma (g:heap{well_formed_heap2 g})
                                  (st: seq Usize.t{stack_props_func g st})
                                  (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                                   (Usize.v (tag_of_object1 hdr_id g) <> infix_tag) /\
                                                   (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n)})
                                  (succ:hp_addr{succ == f_address hdr_id})
                                  (vl: seq Usize.t{vl_props_func g vl})
                   : Lemma
                     (requires (isGrayObject1 hdr_id g) \/ (isBlackObject1 hdr_id g))
                     (ensures (Seq.mem succ st) \/ (Seq.mem succ vl)) =

 assert (stack_props_func g st);
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==> Seq.mem x st);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g ==> Seq.mem (f_address x) st);

 assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g ==> Seq.mem (f_address x) vl);
 assert ((isGrayObject1 hdr_id g) \/ (isBlackObject1 hdr_id g));
 assert (Seq.mem hdr_id (objects2 0UL g));
 assert (Seq.mem (f_address hdr_id) st \/ Seq.mem (f_address hdr_id) vl);
 assert (Seq.mem succ st \/ Seq.mem succ vl);
 ()

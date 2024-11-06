module Spec.GC_part13

include Spec.GC_part12

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

#reset-options " --z3rlimit 1000"

#push-options "--split_queries always"

let graph_succs_length_lemma (g:heap{well_formed_heap2 g
                                    })
                            
                             (x:Usize.t{ Usize.v x >= Usize.v mword /\ Usize.v x < heap_size /\
                                        (Usize.v x % Usize.v mword == 0) /\
                                        Seq.mem (hd_address x) (get_allocated_block_addresses g)}) 
                     : Lemma
                       (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                 (Seq.mem x ((create_graph_from_heap g)).vertices))
                       (ensures (let grph = create_graph_from_heap g in
                                 let sl = G.successors grph x in
                                 (Seq.length sl >= 0)))= ()



#restart-solver

#push-options " --z3rlimit 1000"

#restart-solver

let fieldPush_spec1_black_nodes_lemma3  (g:heap{well_formed_heap2 g})
                                        (st: seq Usize.t{stack_props_func g st})
                                        (h_index:hp_addr{ Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                               (Usize.v h_index % Usize.v mword == 0) /\
                                                                               is_valid_header1 h_index g})
                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                        (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (ensures (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>
                                         Seq.mem y (objects2 0UL  (snd (fieldPush_spec1 g st h_index wz i))) /\
                                                                         (isBlackObject1 y  (snd (fieldPush_spec1 g st h_index wz i))))) = 
fieldPush_spec1_black_nodes_lemma1 g st h_index wz i;
()

#restart-solver

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#push-options "--split_queries always"

#restart-solver

let darken_wrapper_lemma (g:heap{well_formed_heap2 g})
                         (st: seq Usize.t{stack_props_func g st})
                         (h_index:hp_addr{is_valid_header1 h_index g})
                         (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
            : Lemma 
              (requires Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
                        
                        (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                        (let g1 = snd (darken_wrapper g st h_index wz) in
                           well_formed_heap2 g1 /\
                           
                           (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)))
               (ensures (let g1 = snd (darken_wrapper g st h_index wz) in
                           (create_graph_from_heap g == create_graph_from_heap g1) /\
                           (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  Seq.mem y (objects2 0UL g1) /\ (isBlackObject1 y g1)))) =
 if (Usize.v (tag_of_object1 h_index g) = closure_tag) then
   (
     assert (Usize.v wz >= 2);

     let v_id = f_address h_index in
     
     let start_env = start_env_clos_info g v_id in

     assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address v_id) g)) /\
             Usize.v start_env >= 1);
     let start_env_plus_one = Usize.add start_env 1UL in
     let st1, g1 = fieldPush_spec1 g st h_index wz start_env_plus_one in
     
     let grph1 = create_graph_from_heap g in
     let grph3 = create_graph_from_heap g1 in
     fieldPush_spec1_graph_lemma g st h_index wz start_env_plus_one;
     
     assert (grph1 == grph3);
     fieldPush_spec1_black_nodes_lemma3 g st h_index wz start_env_plus_one;
     assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  Seq.mem y (objects2 0UL g1) /\ (isBlackObject1 y g1));
     ()
   )
   else
   (
     let st1, g1 = fieldPush_spec1 g st h_index wz 1UL in
     assert (G.is_vertex_set st1);
     assert (Seq.length g == Seq.length g1);
     assert (well_formed_heap2 g1);
     assert (forall x. Seq.mem x st1 ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
     assert (forall x. Seq.mem x st1 ==> is_valid_header (hd_address x) g1);
     assert (forall x. Seq.mem x st1 ==> Usize.v x % Usize.v mword == 0);
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isGrayObject1 (hd_address x) g1 <==>
                                                Seq.mem x st1);
     assert (forall x. Seq.mem x st ==> Seq.mem x st1);
  
     assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
     assert (objects2 0UL g == objects2 0UL g1);
     assert (objects2 0UL g == objects2 0UL g1);
     assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
     (*field_limits_allocated_blocks_lemma g1;
     field_contents_within_limits_allocated_blocks_lemma g1;
     fieldaddress_within_limits_lemma_x_all1 g1;
     fieldPush_spec1_well_formed_allocated_blocks_lemma g st h_index wz 1UL;*)
    
     assert (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1);
     let grph1 = create_graph_from_heap g in
     let grph3 = create_graph_from_heap g1 in
     fieldPush_spec1_graph_lemma g st h_index wz 1UL;
     
     assert (grph1 == grph3);
     fieldPush_spec1_black_nodes_lemma3 g st h_index wz 1UL;
     assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  Seq.mem y (objects2 0UL g1) /\ (isBlackObject1 y g1));
     ()
   )          
 
#restart-solver       

#restart-solver

#restart-solver

#restart-solver

let dfs_mark_equivalence_body_lemma1 (g:heap{well_formed_heap2 g}) 
                                     (st: seq Usize.t {stack_props_func g st})
                                     (vl: seq Usize.t {vl_props_func g vl}) 
                                    (c:color{c == 3UL})
                          : Lemma
                   (requires (~(G.is_emptySet st)) /\
                             
                             
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                             (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses (snd ( mark5_body g st))) (snd ( mark5_body g st))) /\
                             (G.subset_vertices st (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             (G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             
                             (Seq.length st > 0) /\
                            
                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                                           
                             
                   (ensures (*graph equivalence*)(create_graph_from_heap g == create_graph_from_heap (snd ( mark5_body g st))) /\
                            (*visited set equivalence*) (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (mark5_body g st))) /\ 
                                                           isBlackObject1 (hd_address y) (snd (mark5_body g st)) <==> 
                                                               Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)))) = 

assert (~(G.is_emptySet st));
let v_id = Seq.index st (Seq.length st - 1) in
 seq_index_lemma st;
 assert (v_id == Seq.index st (Seq.length st - 1));
 let s = Seq.slice st 0 (Seq.length st - 1) in
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
 seq_slice_lemma st;
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g);
 G.is_vertex_set_lemma3 st;
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 assert (Seq.mem h_v_id (get_allocated_block_addresses g));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 let g' = colorHeader5 h_v_id g black in
 colorHeader5_lemma h_v_id g black;
 assert (color_of_object1 h_v_id g' == black);
 colorHeader1_alloc_colors_lemma h_v_id g black;
 assert (well_formed_heap2 g');
 objects2_equal_lemma 0UL g g';
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 stack_slice_only_has_gray_color_lemma g st v_id c;
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g'  <==>  Seq.mem x s);
 let wz = wosize_of_object1 h_v_id g' in
 assert (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);
 let grph1 = create_graph_from_heap g in
 field_limits_allocated_blocks_lemma g';
 field_contents_within_limits_allocated_blocks_lemma g';
 fieldaddress_within_limits_lemma_x_all1 g';
 
 
 assert (all_field_address_are_word_aligned (get_allocated_block_addresses g') g');
 
 let grph2 = create_graph_from_heap g' in
 create_graph_from_heap_lemma g h_v_id c;
 assert (grph1 == grph2);
 (*compare with dfs_body---------------------------------------------------------------------------------------------------------------*)
   let x = G.get_last_elem grph1 st in
   assert (x == Seq.index st (Seq.length st - 1));
   assert (x == v_id);

   let xs = G.get_first grph1 st in
   assert (Seq.equal xs (Seq.slice st 0 (Seq.length st - 1)));
   seq_slice_transitive_lemma st s xs;
   assert (s == xs);
   let vl' = G.insert_to_vertex_set grph1 x vl in
   assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size /\
          (Usize.v h_v_id % Usize.v mword == 0));
   assert (is_valid_header h_v_id g);
   assert (isGrayObject1  h_v_id g);
   assert (Seq.mem h_v_id (get_allocated_block_addresses g));
   assert (h_v_id == hd_address v_id);
   f_address_hp_address_lemma h_v_id;
   assert (f_address h_v_id == v_id);
   assert (~(Seq.mem v_id vl));
   assert (~(Seq.mem (f_address h_v_id) vl));
   visited_list_lemma g vl h_v_id;
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> Seq.mem y vl');
   assert (vl' == (snd (D.dfs_body (create_graph_from_heap g) st vl)));
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> 
                   Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)));
   
  let tg = tag_of_object1 h_v_id g' in
  if (Usize.v tg < no_scan_tag) then
  (
    let st1, g1 = darken_wrapper g' s h_v_id wz in
    assert (well_formed_heap2 g1);
    field_limits_allocated_blocks_lemma g1;
    field_contents_within_limits_allocated_blocks_lemma g1;
    fieldaddress_within_limits_lemma_x_all1 g1;
    
    darken_wrapper_lemma g' s h_v_id wz;
    assert ((create_graph_from_heap g' == create_graph_from_heap g1) /\
           (forall y. Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g' <==>  Seq.mem y (objects2 0UL g1) /\ (isBlackObject1 y g1)));
    
    assert (forall y. Seq.mem (hd_address y) (objects2 0UL g1) /\ isBlackObject1 (hd_address y) g1 <==> 
                   Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)));

    assert (g1 == snd (mark5_body g st));
    assert (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (mark5_body g st))) /\ isBlackObject1 (hd_address y) (snd (mark5_body g st)) <==> 
                   Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)));
    ()
  )
  else
  (
    ()
  )

#restart-solver 

let dfs_mark_equivalence_body_lemma1_v1 (g:heap{well_formed_heap2 g}) 
                                        (st: seq Usize.t {stack_props_func g st})
                                        (vl: seq Usize.t {vl_props_func g vl}) 
                                        (c:color{c == 3UL})
                          : Lemma
                   (requires (~(G.is_emptySet st)) /\
                             
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                             (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses (snd ( mark5_body1 g st))) (snd ( mark5_body1 g st))) /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses (snd ( mark5_body g st))) (snd ( mark5_body g st))) /\
                             (G.subset_vertices st (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             (G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             
                             (Seq.length st > 0) /\
                            
                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                                           
                             
                   (ensures (*graph equivalence*)(create_graph_from_heap g == create_graph_from_heap (snd ( mark5_body1 g st))) /\
                            (*visited set equivalence*) (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (mark5_body1 g st))) /\ 
                                                           isBlackObject1 (hd_address y) (snd (mark5_body1 g st)) <==> 
                                                               Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)))) = 
 dfs_mark_equivalence_body_lemma1 g st vl c;
 mark_body_mark_body1_lemma g st;
 ()

#restart-solver

#restart-solver

let darken_wrapper_helper_lemma (g:heap{well_formed_heap2 g})
                                (st: seq Usize.t{stack_props_func g st})
                                (h_index:hp_addr{is_valid_header1 h_index g})
                                (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                                (vl: seq Usize.t{vl_props_func g vl /\  (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                                       (forall x. Seq.mem x vl ==> ~(Seq.mem x st))})
                                                                                        
                                (c:color{Usize.v c == 2})
         : Lemma
         (requires Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
                   (h_index_within_limits g h_index) /\
                   (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                   (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                   (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                   (0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))))
         (ensures (fst (darken_wrapper g st h_index wz) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index)) 
                                                                                  vl
                                                                                  st 
                                                                                  0)) =
 if (Usize.v (tag_of_object1 h_index g) = closure_tag) then
   (
     assert (Usize.v wz >= 2);

     let v_id = f_address h_index in
     
     let start_env = start_env_clos_info g v_id in

     assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address v_id) g)) /\
             Usize.v start_env >= 1);
     let start_env_plus_one = Usize.add start_env 1UL in
     let st1, g1 = fieldPush_spec1 g st h_index wz start_env_plus_one in
     assert ((all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
             (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
             (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index))) /\
             0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) /\
             Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
             Usize.v (tag_of_object1 h_index g) == closure_tag);
     graph_successors_from_0_and_heap_field_pointers_from_1_are_equal1 g h_index;
     assert (fieldPush_spec_successor_push_itr_equivalence_lemma2_pre_props g st h_index wz start_env_plus_one 0UL vl);
     fieldPush_spec_successor_push_itr_equivalence_lemma2 g st h_index wz start_env_plus_one 0UL vl c;
     assert ((fst (fieldPush_spec1 g st h_index wz start_env_plus_one)) ==  G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index))
                                                                                  (vl)
                                                                                  (st)
                                                                                   0);
     assert (fst (darken_wrapper g st h_index wz) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index)) 
                                                                                  vl
                                                                                  st 
                                                                                  0);
     ()
     
   )
   else
   (
     let st1, g1 = fieldPush_spec1 g st h_index wz 1UL in
     graph_successors_from_0_and_heap_field_pointers_from_1_are_equal g h_index;
     assert (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
     
     fieldPush_spec_successor_push_itr_equivalence_lemma2 g st h_index wz 1UL 0UL vl c;
     assert ((fst (fieldPush_spec1 g st h_index wz 1UL)) ==  G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index))
                                                                                  (vl)
                                                                                  (st)
                                                                                   0);
     assert (fst (darken_wrapper g st h_index wz) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index)) 
                                                                                  vl
                                                                                  st 
                                                                                  0);
     ()
   )

#restart-solver

#restart-solver

#restart-solver

let dfs_mark_equivalence_body_lemma (g:heap{well_formed_heap2 g}) 
                                    (st: seq Usize.t {stack_props_func g st})
                                    (vl: seq Usize.t {vl_props_func g vl}) 
                                    (c:color{c == 3UL})
                                    (c1:color{Usize.v c1 == 2})
                          : Lemma
                   (requires (~(G.is_emptySet st)) /\
                             
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                             (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses (snd ( mark5_body g st))) (snd ( mark5_body g st))) /\
                             (G.subset_vertices st (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             (G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             
                             (Seq.length st > 0) /\
                            
                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                                           
                             
                   (ensures (*stack equivalence*) fst ( mark5_body g st) == fst (D.dfs_body (create_graph_from_heap g) st vl)) = 
assert (~(G.is_emptySet st));
 let v_id = Seq.index st (Seq.length st - 1) in
 seq_index_lemma st;
 assert (v_id == Seq.index st (Seq.length st - 1));
 let s = Seq.slice st 0 (Seq.length st - 1) in
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
 seq_slice_lemma st;
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g);
 G.is_vertex_set_lemma3 st;
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 assert (Seq.mem h_v_id (get_allocated_block_addresses g));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 let g' = colorHeader5 h_v_id g black in
 colorHeader5_lemma h_v_id g black;
 assert (color_of_object1 h_v_id g' == black);
 colorHeader1_alloc_colors_lemma h_v_id g black;
 assert (well_formed_heap2 g');
 objects2_equal_lemma 0UL g g';
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 stack_slice_only_has_gray_color_lemma g st v_id c;
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g'  <==>  Seq.mem x s);
 let wz = wosize_of_object1 h_v_id g' in
 assert (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);
 let grph1 = create_graph_from_heap g in
 field_limits_allocated_blocks_lemma g';
 field_contents_within_limits_allocated_blocks_lemma g';
 fieldaddress_within_limits_lemma_x_all1 g';
 
 
 assert (all_field_address_are_word_aligned (get_allocated_block_addresses g') g');
 
 let grph2 = create_graph_from_heap g' in
 create_graph_from_heap_lemma g h_v_id c;
 assert (grph1 == grph2);
 (*compare with dfs_body---------------------------------------------------------------------------------------------------------------*)
   let x = G.get_last_elem grph1 st in
   assert (x == Seq.index st (Seq.length st - 1));
   assert (x == v_id);

   let xs = G.get_first grph1 st in
   assert (Seq.equal xs (Seq.slice st 0 (Seq.length st - 1)));
   seq_slice_transitive_lemma st s xs;
   assert (s == xs);
   let vl' = G.insert_to_vertex_set grph1 x vl in
   assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size /\
          (Usize.v h_v_id % Usize.v mword == 0));
   assert (is_valid_header h_v_id g);
   assert (isGrayObject1  h_v_id g);
   assert (Seq.mem h_v_id (get_allocated_block_addresses g));
   assert (h_v_id == hd_address v_id);
   f_address_hp_address_lemma h_v_id;
   assert (f_address h_v_id == v_id);
   assert (~(Seq.mem v_id vl));
   assert (~(Seq.mem (f_address h_v_id) vl));
   visited_list_lemma g vl h_v_id;
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> Seq.mem y vl');
   assert (vl' == (snd (D.dfs_body (create_graph_from_heap g) st vl)));
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> 
                   Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)));

  let _ = G.get_last_mem_lemma grph1 st in
  assert (~(Seq.mem x xs));
  let sl = G.successors grph1 x in
  let _ = G.insert_to_vertex_set_mem_negation_lemma grph1 x vl xs in
  is_vertex_set_slice g st;
  is_vertex_set_vl_after_insert1 g vl x;
  mutual_exclusion_lemma st vl;
  mutual_exclusion_lemma3 g x s vl;
  let tg = tag_of_object1 h_v_id g' in
  if (Usize.v tg < no_scan_tag) then
  (
    let st1, g1 = darken_wrapper g' s h_v_id wz in
    assert (well_formed_heap2 g1);
    field_limits_allocated_blocks_lemma g1;
    field_contents_within_limits_allocated_blocks_lemma g1;
    fieldaddress_within_limits_lemma_x_all1 g1;

    let r' = G.successor_push_itr1 sl vl' xs 0 in
    G.successor_push_itr1_subset_lemma grph1 sl vl' xs 0;
    graph_successors_length_lemma g' h_v_id;
    assert (h_v_id == hd_address v_id);
    test_helper5 h_v_id;
    assert (v_id == f_address h_v_id);
    assert (f_address h_v_id == x);
    assert (Seq.mem x grph2.vertices);
    assert (Seq.length sl <= Usize.v (getWosize (read_word g' h_v_id)));
    graph_succs_length_lemma g' x;
    assert (0 <= Seq.length sl); 
    assert ((all_field_address_are_word_aligned (get_allocated_block_addresses g') g') /\
            (Seq.mem (f_address h_v_id) (create_graph_from_heap g').vertices) /\
            (Seq.length (G.successors (create_graph_from_heap g') (f_address h_v_id)) <= Usize.v (getWosize (read_word g' h_v_id))) /\
            0 <= Seq.length (G.successors (create_graph_from_heap g') (f_address h_v_id)) /\
            Usize.v (tag_of_object1 h_v_id g') < no_scan_tag
           );
   
    let st1, g1 = darken_wrapper g' s h_v_id wz in
    assert  (Usize.v (tag_of_object1 h_v_id g') < no_scan_tag /\
                   (h_index_within_limits g' h_v_id) /\
                   (all_field_address_are_word_aligned (get_allocated_block_addresses g') g') /\
                   (Seq.mem (f_address h_v_id) (create_graph_from_heap g').vertices) /\
                   (Seq.length (G.successors (create_graph_from_heap g') (f_address h_v_id)) <= Usize.v wz) /\
                   (0 <= Seq.length (G.successors (create_graph_from_heap g') (f_address h_v_id))));
    
    visited_list_lemma g vl h_v_id;
    assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> Seq.mem y vl');
    assert ((forall x. Seq.mem x vl' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
           (forall x. Seq.mem x vl' ==> Usize.v x % Usize.v mword == 0));
    assert (G.is_vertex_set vl');
    assert (forall x. Seq.mem x vl' ==> is_valid_header (hd_address x) g');
    assert (vl_props_func g' vl');
    assert  ((forall x. Seq.mem x s ==> ~(Seq.mem x vl')) /\
            (forall x. Seq.mem x vl' ==> ~(Seq.mem x s)));
    assert (stack_props_func g' s);
    
    darken_wrapper_helper_lemma g' s h_v_id wz vl' c1;
    assert (fst (darken_wrapper g' s h_v_id wz) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_v_id)) 
                                                                                  vl'
                                                                                  s 
                                                                                  0);
    assert (fst (mark5_body1 g st) == fst (darken_wrapper g' s h_v_id wz));
    assert (st1 == r'); 
    assert (fst (D.dfs_body grph1 st vl) == r');
    assert (fst ( mark5_body1 g st) == st1);
    assert (fst ( mark5_body1 g st) == fst (D.dfs_body (create_graph_from_heap g) st vl));
    
    ()
    
  )
  else
  (
    graph_successors_heap_create_successor_list_equivalence_lemma g h_v_id;
    assert (Usize.v (tag_of_object1 h_v_id g) == Usize.v (tag_of_object1 h_v_id g'));
    assert (Usize.v (tag_of_object1 h_v_id g) >= no_scan_tag);
    assert (G.successors (create_graph_from_heap g) (f_address h_v_id) == Seq.empty #UInt64.t);
    let r' = G.successor_push_itr1 sl vl' xs 0 in
    test_helper5 h_v_id;
    assert (v_id == f_address h_v_id);
    assert (f_address h_v_id == x);
    assert (sl == Seq.empty #UInt64.t);
    length_empty_lemma sl;
    assert (Seq.length sl == 0);
    G.successor_push_itr1_lemma1 sl vl' xs 0; 
    assert (G.successor_push_itr1 sl vl' xs 0 == xs);
    assert (r' == xs);
    assert (fst (D.dfs_body grph1 st vl) == r');
    assert (fst ( mark5_body g st) == xs);
    assert (fst ( mark5_body g st) == fst (D.dfs_body (create_graph_from_heap g) st vl));
    ()
  )

#reset-options "--z3rlimit 500"

#restart-solver

let cardinal_diff (g:heap{well_formed_heap2 g}) 
         : Tot (diff:int{(diff =  G.cardinal1(get_allocated_block_addresses g) - G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g))) /\
                        diff >= 0})=
 let card_allocs = G.cardinal1(get_allocated_block_addresses g) in
 let card_blacks = G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g)) in
 let diff = card_allocs - card_blacks in
 assert (diff >= 0);
 diff

let cardinal_diff_lemma (g:heap{well_formed_heap2 g})
                        (g':heap{well_formed_heap2 g'})
             : Lemma 
               (requires (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                         (Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g')) > 
                            Seq.length (get_black_block_addresses g (get_allocated_block_addresses g))))
               (ensures (cardinal_diff g > cardinal_diff g')) = ()


let neg_empty_lemma (s:seq Usize.t{G.is_vertex_set s})
                    
            : Lemma
              (requires (~(G.is_emptySet s)))
              (ensures Seq.length s > 0) = ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries always"

#restart-solver

let rec dfs_mark_equivalence_lemma  (g:heap{well_formed_heap2 g}) 
                                    (st: seq Usize.t {stack_props_func g st})
                                    (vl: seq Usize.t {vl_props_func g vl}) 

                                    (c:color{c == 3UL})
                                    (c1:color{c1 == 2UL})
                                
                 : Lemma
                   (requires  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                              (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                              
                              (G.subset_vertices st (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                              (G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\ 
                              (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                              (forall x. Seq.mem x vl ==> ~(Seq.mem x st))
                              
                   )
                          
                   (ensures (forall x. Seq.mem (hd_address x) (objects2 0UL (mark5 g st)) /\ isBlackObject1 (hd_address x) (mark5 g st) <==>
                                 Seq.mem x (D.dfs (create_graph_from_heap g)
                                            st
                                            vl))) 
                   (decreases %[cardinal_diff g;
                                Seq.length st])= 

if (G.is_emptySet st) then
   (
      ()
   )
 else
   (
     neg_empty_lemma st;
     assert (Seq.length st > 0);
     let st', g' = mark5_body g st in
     let v_id = Seq.index st (Seq.length st - 1) in
     seq_index_lemma st;
     assert (v_id == Seq.index st (Seq.length st - 1));
     let s = Seq.slice st 0 (Seq.length st - 1) in
     seq_index_lemma1 st;
     assert (Seq.mem v_id st);
     assert (Usize.v v_id >= Usize.v mword);
     stack_slice_only_has_gray_color_lemma g st v_id 3UL;
     mark5_body_black_nodes_lemma g st;
     let g1 = mark5 g' st' in
     mark_mark_body_lemma g st;
     assert (mark5 g st == mark5 g' st');
     let grph1 = create_graph_from_heap g in
     let _ = G.negation_nonEmpty_implies_empty st in
     assert (G.nonEmpty_set st);
     let st1,vl1 = D.dfs_body grph1 st vl in
     
     field_limits_allocated_blocks_lemma g';
     field_contents_within_limits_allocated_blocks_lemma g';
     fieldaddress_within_limits_lemma_x_all1 g';
     assert (all_field_address_are_word_aligned (get_allocated_block_addresses g') g');
     
     dfs_mark_equivalence_body_lemma1 g st vl c;
     dfs_mark_equivalence_body_lemma g st vl c c1;
     assert (st' == st1);

     let grph2 = create_graph_from_heap g' in
     assert (grph1 == grph2);
     assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> 
                                                     Seq.mem y vl1);
                                                              
     let vl2 = D.dfs grph1 st1 vl1 in
     D.dfs_lemma grph1 st vl ;
     assert (D.dfs grph1 st vl == D.dfs grph1 st1 vl1);
     assert (G.subset_vertices st' (first_field_addresses_of_allocated_blocks g' (get_allocated_block_addresses g')));
     assert (G.subset_vertices vl1 (first_field_addresses_of_allocated_blocks g' (get_allocated_block_addresses g')));
     assert ((forall x. Seq.mem x st' ==> ~(Seq.mem x vl1)) /\
             (forall x. Seq.mem x vl1 ==> ~(Seq.mem x st')));
     assert  ((forall x. Seq.mem x vl1 ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
              (forall x. Seq.mem x vl1 ==> Usize.v x % Usize.v mword == 0));
     assert  (forall x. Seq.mem x vl1 ==> is_valid_header (hd_address x) g');
     
     cardinal_diff_lemma g g';
     assert (cardinal_diff g > cardinal_diff g'); 

     dfs_mark_equivalence_lemma g' st' vl1 c c1;
     ()
   )

#restart-solver 

let noGreyObjects1 (g:heap{well_formed_heap2 g}) = 
   (forall (x:hp_addr{UInt.fits (Usize.v x - Usize.v mword) Usize.n }). Seq.mem (hd_address x) (objects2 0UL g) ==> ~(color_of_object1 (hd_address x) g == gray)) 

let noGreyObjects (g:heap(*{well_formed_heap2 g}*)) = (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray))

let heap_heap_addr_pair = heap & hp_addr

#restart-solver

#reset-options "--z3rlimit 500"

#push-options "--split_queries always"


#restart-solver

let colorHeader3  (v_id:hp_addr)  
                  (g:heap(*{well_formed_heap2 g /\ is_valid_header1 v_id g}*){(Seq.length (objects2 0UL g) > 0) /\ (Seq.mem v_id (objects2 0UL g))}) 
                  (c:color)
             : Tot (g': heap{Seq.length g == Seq.length g' /\
                             (length (slice g' (Usize.v v_id) ((Usize.v v_id) + (Usize.v mword))) = 8) /\
                             read_word g' v_id == makeHeader (wosize_of_object1 v_id g) (c) (tag_of_object1 v_id g) /\
                            heap_remains_same_except_index_v_id v_id g g' /\
                            color_of_object1 v_id g' == c /\
                            wosize_of_object1 v_id g' == wosize_of_object1 v_id g /\
                            tag_of_object1 v_id g' == tag_of_object1 v_id g /\
                            objects2 0UL g == objects2 0UL g' (*/\
                            well_formed_heap2 g' /\ is_valid_header v_id g'*)}) =
 let wz = getWosize (read_word g v_id) in
 let tg = getTag (read_word g v_id) in  
 let h = makeHeader wz c tg in
 assert (wz == getWosize h);
 assert (c == getColor h);
 assert (tg == getTag h);
 assert (Usize.v v_id >= 0);
 assert (Usize.v v_id < heap_size);
 assert (Usize.v v_id < Seq.length g);
 //assert (well_formed_heap2 g);
 let h_index = v_id in
 assert (Seq.mem h_index (objects2 0UL g));
 
// assert (Seq.length (objects2 0UL g) > 0);

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 

 assert (heap_remains_same_except_index_v_id h_index g g');

 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.mem v_id (objects2 0UL g'));
 //assert (is_fields_contents_within_limit2 v_id wz g);
 assert (Seq.length g == Seq.length g');
 lemma_len_slice g' (Usize.v  v_id) ((Usize.v  v_id) + (Usize.v mword));
 assert (read_word g' v_id == makeHeader (wosize_of_object1 v_id g) (c) (tag_of_object1 v_id g));
 assert (heap_remains_same_except_index_v_id v_id g g');
 assert (color_of_object1 v_id g' == c /\
                            wosize_of_object1 v_id g' == wosize_of_object1 v_id g /\
                            tag_of_object1 v_id g' == tag_of_object1 v_id g /\
                            objects2 0UL g == objects2 0UL g');
 g'
 
#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver
(*This lemma can be called in the black branch of sweep body to prove parts of the well-formedness lemma*)
let colorHeader3_well_formed_parts_lemma  (v_id:hp_addr)  
                                          (g:heap{Seq.length (objects2 0UL g) > 0}) 
                                          (c:color)
                         : Lemma
                           (requires (c == white \/ c == gray \/ c == black) /\
                                     (mem v_id (objects2 0UL g)) /\
                                     (color_of_object1 v_id g == white \/ color_of_object1 v_id g == gray \/ 
                                     color_of_object1 v_id g == black) /\
                                     (let allocs = (get_allocated_block_addresses g) in
                                      (check_all_block_fields_within_limit2 g allocs) /\
                                      (check_well_formed_closure_objs g allocs)))
                           
                           (ensures   (let g' = (colorHeader3 v_id g c) in
                                       let allocs' = (get_allocated_block_addresses g') in
                                      (check_all_block_fields_within_limit2 g' allocs') /\
                                      (check_well_formed_closure_objs g' allocs') /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses g'))) =
 let wz = getWosize (read_word g v_id) in
 let tg = getTag (read_word g v_id) in  
 let h = makeHeader wz c tg in
 let h_index = v_id in

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.length (objects2 0UL g') > 0);

 
 get_allocated_block_addresses_lemma g g' v_id c;
 
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 fieldaddress_within_limits_lemma_x_all5 g;

 assert ((forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0));

 (*The below assume is true at this point. Because with additional effort, it can be proved that, changing the color
   of an object header does not change the field values between the heaps. It is already proved that except the color of the
   object whose color is being changed, remains the same between the two heaps*)
 assume ((get_allocated_block_addresses g == get_allocated_block_addresses g')  /\
                                            (objects2 0UL g ==
                                             objects2 0UL g') /\
                                            
        (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x)) /\
        (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                                      Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y));

 check_all_block_fields_within_limit2_lemma g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
 assert (check_all_block_fields_within_limit2 g' (get_allocated_block_addresses g'));
 
 
 check_well_formed_closure_objs_lemma g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g'); 
 assert (check_well_formed_closure_objs g' (get_allocated_block_addresses g'));

 assert (let g' = (colorHeader3 v_id g c) in
                                       let allocs' = (get_allocated_block_addresses g') in
                                      (check_all_block_fields_within_limit2 g' allocs') /\
                                      (check_well_formed_closure_objs g' allocs') /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses g'));
 

 assert ((check_all_block_fields_within_limit2 g' (get_allocated_block_addresses g')) /\
         (check_well_formed_closure_objs g' (get_allocated_block_addresses g')) /\
         (get_allocated_block_addresses g == get_allocated_block_addresses g'));
 ()

#restart-solver

let write_word_replacement_lemma1 (byte_array: heap)
                                 (byte_index: hp_addr)
                                 (value: UInt64.t)
            : Lemma
              (ensures (forall (i:hp_addr). read_word (write_word byte_array byte_index value) byte_index == value)) = ()

#reset-options "--z3rlimit 500"

let write_word_before_start_lemma1 (byte_array: heap)
                                   (byte_index: hp_addr)
                                   (value: UInt64.t)
                      : Lemma
                        (ensures (forall (i:hp_addr). Usize.v i >= 0 /\  Usize.v i < Usize.v byte_index /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) i == read_word byte_array i)) = 
 replace_range_before_start_all_lemma byte_array byte_index (FStar.Endianness.le_of_uint64 value)

let write_word_lemma1 (byte_array: heap)
                     (byte_index: hp_addr)
                     (value: UInt64.t)
                : Lemma 
                  ((forall (i:hp_addr). read_word (write_word byte_array byte_index value) i == (
                                                           if Usize.v i = Usize.v byte_index then
                                                                  value 
                                                             else 
                                                                read_word byte_array i))) = 
write_word_replacement_lemma1 byte_array byte_index value;  
write_word_before_start_lemma byte_array byte_index value;
write_word_after_start_end_lemma byte_array byte_index value;
()

let write_word_lemma3 (byte_array: heap)
                     (byte_index: hp_addr)
                     (value: UInt64.t)
                : Lemma 
                  (forall (i:hp_addr). Usize.v i <> Usize.v byte_index ==> read_word (write_word byte_array byte_index value) i == read_word byte_array i) =
 write_word_lemma1 byte_array byte_index value;
 ()
                                                                

let write_word_lemma5 (byte_array: heap)
                     (byte_index: hp_addr)
                     (value: UInt64.t)
                : Lemma 
                  (forall (i:hp_addr). Usize.v i == Usize.v byte_index ==> read_word (write_word byte_array byte_index value) i == value) =
 write_word_lemma1 byte_array byte_index value;
 ()

let write_word_after_start_end_lemma1 (byte_array: heap)
                                     (byte_index: hp_addr)
                                     (value: UInt64.t)
                      : Lemma
                        (ensures (forall (i:hp_addr). (Usize.v i >= ((Usize.v byte_index) + Usize.v mword)) /\ (Usize.v i < length byte_array) /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) i == read_word byte_array i)) =
 replace_range_after_start_end_all_lemma byte_array byte_index (FStar.Endianness.le_of_uint64 value)

let fields_not_mem_objs_lemma (g:heap(*{well_formed_heap2 g}*))
                              (g':heap)
                              (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                              (y:hp_addr{Usize.v y >= Usize.v h_index + Usize.v mword /\
                                       Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword)})
                  : Lemma
                    (ensures ~(Seq.mem y (objects2 0UL g))) = 
assert (~(Seq.mem y (objects2 0UL g)));
()

#restart-solver

(*val objects2_equal_lemma5 :  (g:heap(*{well_formed_heap2 g}*){Seq.length (objects2 0UL g) > 0})-> 
                             (g':heap)->
                             (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})->
                      Lemma
                       (requires (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word g' p) ==  getWosize (read_word g p)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index))*)

#restart-solver


  
let objects2_equal_lemma1_app (g:heap(*{well_formed_heap2 g}*){Seq.length (objects2 0UL g) > 0}) 
                              (g':heap)
                              
                   :   Lemma
                       (requires (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word g' p) ==  getWosize (read_word g p)))
                       (ensures (objects2 0UL g == objects2 0UL g'))= 
 objects2_equal_lemma5 g g' 0UL;
 assert (objects2 0UL g == objects2 0UL g');
 ()

#restart-solver 

#restart-solver 
            
let objects_color_equivalence_lemma (g:heap(*{well_formed_heap2 g}*))
                                    (x:hp_addr{(*is_valid_header x g /\ *)color_of_object1 x g == blue})
                                    (p:hp_addr{(*is_valid_header p g /\ *) color_of_object1 p g <> blue})
                     : Lemma
                       (ensures p <> x) = () 
                       
#restart-solver 

let objects_color_equivalence_lemma_all (g:heap(*{well_formed_heap2 g}*))
                                        (x:hp_addr{(*is_valid_header x g /\*) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                                       
                      : Lemma
                       (ensures (forall p. (*is_valid_header p g /\ *) color_of_object1 p g <> blue ==> p <> x)) = 
Classical.forall_intro (objects_color_equivalence_lemma g x) 

#restart-solver

let objects_fields_lemma (g:heap(*{well_formed_heap2 g}*))
                         (x:hp_addr{(*is_valid_header x g /\ *)Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                         (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                         (p:hp_addr{(*is_valid_header p g /\*)Seq.mem p (objects2 0UL g) /\  p <> x})
                         (j:hp_addr{Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword)})
                        
                  : Lemma
                    (ensures (Usize.v j <> Usize.v i)) = 
if (Usize.v p > Usize.v x) then
(
  assert (Usize.v p > Usize.v x);
  assert (Usize.v j > Usize.v x);
  assert (Usize.v j > Usize.v i);
  assert (Usize.v j <> Usize.v i);
  ()
)
else
(
  assert (Usize.v p < Usize.v x);
  assert (Usize.v j <> Usize.v x);
  assert (Usize.v j <> Usize.v i);
  ()
)

let objects_fields_lemma_all (g:heap(*{well_formed_heap2 g}*))
                             (x:hp_addr{(*is_valid_header x g /\ *) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                             (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                             (p:hp_addr{(*is_valid_header p g /\*) Seq.mem p (objects2 0UL g) /\  p <> x})
                   : Lemma
                     (ensures (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i)) = 
 Classical.forall_intro (objects_fields_lemma g x i p)

#restart-solver

let objects_fields_lemma_all1 (g:heap(*{well_formed_heap2 g}*))
                              (x:hp_addr{(*is_valid_header x g /\*)Seq.mem x (objects2 0UL g) /\  color_of_object1 x g == blue})
                              (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                            
                   : Lemma
                     (ensures (forall p. (*is_valid_header p g*) Seq.mem p (objects2 0UL g)  /\ p <> x ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i))) = 
Classical.forall_intro (objects_fields_lemma_all g x i)  


let objects_fields_lemma_all1_app (g:heap(*{well_formed_heap2 g}*))
                                  (x:hp_addr{(*is_valid_header x g /\*) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                                  (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                     : Lemma
                     (ensures (forall p. (*is_valid_header p g /\*) Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> 
                                    (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i))) = 
objects_color_equivalence_lemma_all g x;
objects_fields_lemma_all1 g x i ;
()   

let objects_fields_lemma_all1_app1 (g:heap(*{well_formed_heap2 g}*))
                                  (x:hp_addr{(*is_valid_header x g /\*) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                                  (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                     : Lemma
                     (ensures (forall p. (*is_valid_header p g /\*) Seq.mem p (objects2 0UL g) /\  p <> x ==> 
                                    (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i))) = 
objects_fields_lemma_all1 g x i ;
()   

#restart-solver 

#restart-solver 

#restart-solver 

#restart-solver 


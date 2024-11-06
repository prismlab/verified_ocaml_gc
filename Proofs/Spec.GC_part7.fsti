module Spec.GC_part7

include Spec.GC_part6

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


let create_edge_pairs_for_h_index_lemma_rec_lemma_infix (g:heap{well_formed_heap2 g}) 
                                                            (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                            (wz: wosize{valid_wosize g h_index wz})
                         
                                                            (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                            (i':Usize.t{Usize.v i' == Usize.v i + 1})
                          :Lemma
                           (ensures (isPointer (Usize.add h_index (Usize.mul i mword)) g /\ 
                     Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) == infix_tag ==> 
                              create_edge_pairs_for_h_index g h_index wz i == Seq.cons ((f_address h_index),(f_address (parent_closure_of_infix_object g h_index i))) 
                                                              (create_edge_pairs_for_h_index g h_index wz i'))) =
()

let create_edge_pairs_for_h_index_lemma_rec_lemma_non_infix (g:heap{well_formed_heap2 g}) 
                                                            (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                            (wz: wosize{valid_wosize g h_index wz})
                         
                                                            (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                            (i':Usize.t{Usize.v i' == Usize.v i + 1})
                          :Lemma
                           (ensures (isPointer (Usize.add h_index (Usize.mul i mword)) g /\ 
                                       Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) <> infix_tag ==> 
                                       create_edge_pairs_for_h_index g h_index wz i == Seq.cons ((f_address h_index),(read_word g (Usize.add h_index (Usize.mul i mword)))) (create_edge_pairs_for_h_index g h_index wz i'))) =
()

let colorHeader1_tags_lemma  (v_id:hp_addr)  
                             (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                             (c:color)
                             (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })
            : Lemma
              (ensures ((forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g == tag_of_object1 x g'))) =
()

let colorHeader1_wosize_lemma  (v_id:hp_addr)  
                             (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                             (c:color)
                             (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })
            : Lemma
              (ensures ((forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). wosize_of_object1 x g == wosize_of_object1 x g'))) =
()

let allocs_props_g (g:heap{well_formed_heap2 g})
                   (h_index:hp_addr{is_valid_header1 h_index g}) =
  (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g /\
                                                       is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g))

#restart-solver

#reset-options "--z3rlimit 1000 --split_queries always"

let parent_closure_index_props (g:heap{well_formed_heap2 g})
                               (h_index:hp_addr{is_valid_header1 h_index g})
                               (i:Usize.t) =
 (Usize.v i < Usize.v (getWosize (read_word g h_index)) + 1 /\ Usize.v i >= 1) /\
                                               isPointer (succ_index_fn g h_index i) g /\
                                               (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag)

let field_points_to_blocks_allocs_lemma (g:heap{well_formed_heap2 g})
                                            : Lemma
                                              (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) 
                                              (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                                          is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g))) = 
 assert (well_formed_heap2 g);
 assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
 ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#push-options "--split_queries always"

#restart-solver


let parent_closure_of_infix_object_lemma (g:heap{well_formed_heap2 g})
                                         (h_index:hp_addr{is_valid_header1 h_index g})
                                         (i:Usize.t{parent_closure_index_props g h_index i}) 
                                         (v_id:hp_addr{is_valid_header1 v_id g}) 
                                         (c:color)
                                         (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) /\ is_valid_header1 h_index g' })
                                         
                   : Lemma
                     (requires (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                allocs_props_g g h_index /\
                                allocs_props_g g' h_index /\
                                parent_closure_index_props g' h_index i /\
                                (let succ_index = Usize.add h_index (Usize.mul i mword) in
                                  (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8) /\
                                  (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8) /\
                                  (read_word g succ_index = read_word g' succ_index) /\
                                  wosize_of_object1 (hd_address (read_word g succ_index)) g = wosize_of_object1 (hd_address (read_word g succ_index)) g'))
                       
                     (ensures (parent_closure_of_infix_object g h_index i == parent_closure_of_infix_object g' h_index i)) =
 assert (well_formed_heap2 g);
 assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
 
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 assert  (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                               is_fields_contents_within_limit2 x (getWosize (read_word g x)) g /\
                      is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g));
 assert (is_fields_points_to_blocks2 h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
 assert (is_fields_points_to_blocks2_post_condition h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
 let succ_index = Usize.add h_index (Usize.mul i mword) in
 lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
 lemma_len_slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
 let succ = read_word g succ_index in
 let succ1 = read_word g' succ_index in
 assert (succ == succ1);
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
 let hdr_succ = hd_address succ in
 let wsize_succ = wosize_of_object1 hdr_succ g in
 let wsize_succ_offset = Usize.mul wsize_succ mword in
 let actual_succ = Usize.sub succ wsize_succ_offset in

 let hdr_actual_succ = hd_address actual_succ in
 assert (hdr_actual_succ == parent_closure_of_infix_object g h_index i);
 let wsize_succ1 = wosize_of_object1 hdr_succ g' in
 assert (wsize_succ == wsize_succ1);
 assert (is_valid_header1 h_index g');
 assert ((Usize.v i < Usize.v (getWosize (read_word g' h_index)) + 1 /\ Usize.v i >= 1) /\
                                               isPointer (succ_index_fn g' h_index i) g' /\
                                               (UInt.fits (Usize.v (read_succ g' h_index i) - Usize.v mword) Usize.n) /\
                                               (Usize.v (tag_of_object1 (hd_address (read_succ g' h_index i)) g') == infix_tag));
 assert (parent_closure_of_infix_object g' h_index i == parent_closure_of_infix_object g h_index i);
 ()
  


#restart-solver


#restart-solver

#push-options "--split_queries always"

#restart-solver

let get_allocs_props (g:heap{well_formed_heap2 g}) =
    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
    (forall j x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)

#restart-solver 

#restart-solver

//#reset-options "--z3rlimit 1000"

#restart-solver

let rec create_edge_pairs_for_h_index_lemma1 (g:heap{well_formed_heap2 g}) 
                                             (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                             (wz: wosize{valid_wosize g h_index wz})
                         
                                             (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                                             (v_id:hp_addr{is_valid_header1 v_id g})

                                             (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})

                                             (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })

                                             (wz1: wosize{(wz1 == getWosize (read_word g' h_index))})
                                             
                        : Lemma
                          (requires (objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    (wz == wz1) /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                    (get_allocs_props g) /\ (get_allocs_props g')
                                    
                                    )
                          (ensures (create_edge_pairs_for_h_index g h_index wz i == create_edge_pairs_for_h_index g' h_index wz1 i))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 
if Usize.v i = Usize.v wz + 1 then
    (
       let e = Seq.empty #G.edge in
       length_empty_generic_lemma e;
       assert (Seq.length e == 0);
       (*assert ((Seq.length e == (Usize.v wz + 1) - Usize.v i));*)
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
      lemma_len_slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 
           ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      let succ1 = read_word g' succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
      succ_index_lemma g h_index wz i;
      assert (~(Seq.mem succ_index (objects2 0UL g)));
      assert (Seq.mem v_id (objects2 0UL g));
      assert (succ_index <> v_id);
      assert (succ == succ1);
       
      assert (Usize.v succ_index < heap_size);
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
        
      let e' = create_edge_pairs_for_h_index g h_index wz i' in
      let e1 = create_edge_pairs_for_h_index g' h_index wz1 i' in
      
      create_edge_pairs_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;
      assert (e' == e1);
      if isPointer succ_index g  then
      (
        
         assert (isPointer succ_index g');
         let h_addr_succ = hd_address succ in
        
         let f_index = f_address h_index in
         f_address_hp_address_lemma h_index;
         assert (hd_address f_index == h_index);
         assert (read_word g (Usize.add h_index (Usize.mul i mword)) == read_word g' (Usize.add h_index (Usize.mul i mword)));
         colorHeader1_tags_lemma v_id g c g';
         assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g == tag_of_object1 x g');
         assert (Usize.v (tag_of_object1 h_addr_succ g) == Usize.v (tag_of_object1 h_addr_succ g'));
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
           assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
           let parent_succ = f_address parent_hdr in
           let edge_pair = (f_index,parent_succ) in
           assert (hd_address (fst edge_pair) == h_index);
           assert (fst edge_pair == f_index);
           assert (snd edge_pair == parent_succ);
           assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
           assert (well_formed_heap2 g);
           assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
           assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                        is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g));
           assert (Seq.mem h_index (get_allocated_block_addresses g));
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
                                                        (Seq.mem (hd_address actual_succ) (get_allocated_block_addresses g)))
           ));
           assert (hd_address parent_succ == parent_hdr);
           assert (parent_hdr ==  parent_closure_of_infix_object g h_index i);
           assert (is_valid_header1 parent_hdr g);
           assert (parent_hdr == (hd_address (snd edge_pair)));
           assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
           lemma_tl edge_pair e'; 
        
           let e = Seq.cons edge_pair e' in 
           cons_property_lemma5 g h_index e' edge_pair;
           create_edge_pairs_for_h_index_lemma_rec_lemma_infix g' h_index wz1 i i';
           assert (isPointer (Usize.add h_index (Usize.mul i mword)) g' /\ 
                     Usize.v (tag_of_object1 (hd_address (read_word g' (Usize.add h_index (Usize.mul i mword)))) g') == infix_tag ==> 
             create_edge_pairs_for_h_index g' h_index wz1 i == Seq.cons (f_index,(f_address (parent_closure_of_infix_object g' h_index i))) 
                                                              (create_edge_pairs_for_h_index g' h_index wz1 i'));
           ()
         )
         else
         (

           let edge_pair = (f_index,succ) in
           let edge_pair1 = (f_index,succ1) in
           assert (hd_address (fst edge_pair) == h_index);
           assert (fst edge_pair == f_index);
           assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
           assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
           lemma_tl edge_pair e'; 
        
           let e = Seq.cons edge_pair e' in 
           let e2 = Seq.cons edge_pair1 e1 in 
           cons_property_lemma5 g h_index e' edge_pair;
           assert (edge_pair == edge_pair1);
           assert (e == e2);
           assert (create_edge_pairs_for_h_index g h_index wz i == e);
           create_edge_pairs_for_h_index_lemma_rec_lemma_non_infix g' h_index wz1 i i';
           assert (isPointer (Usize.add h_index (Usize.mul i mword)) g' /\ 
                     Usize.v (tag_of_object1 (hd_address (read_word g' (Usize.add h_index (Usize.mul i mword)))) g') <> infix_tag ==> 
                         create_edge_pairs_for_h_index g' h_index wz1 i == Seq.cons (f_index,succ1) (create_edge_pairs_for_h_index g' h_index wz1 i'));
           assert (create_edge_pairs_for_h_index g' h_index wz1 i == e2);
           ()
         )
      )
      else
      (
        ()
      )
    )

//#reset-options "--z3rlimit 1000"

#restart-solver

let well_formed_closure_objs_lemma (g:heap{well_formed_heap2 g})
                                   (hd:hp_addr{is_valid_header1 hd g}) 
                    : Lemma
                      (requires Usize.v (tag_of_object1 hd g) < no_scan_tag /\
                                Usize.v (tag_of_object1 hd g) = closure_tag) 
                      (ensures (Usize.v (wosize_of_object1 hd g) >= 2 /\
                                is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) /\
                                Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) + 1 <= Usize.v (wosize_of_object1 hd g) /\
                                Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) >= 1)) =
 assert (check_well_formed_closure_objs g (get_allocated_block_addresses g));
 assert (closure_obj_props1 g (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> Usize.v (tag_of_object1 x g) = closure_tag ==> 
                              Usize.v (wosize_of_object1 x g) >= 2 /\
                              is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) /\
                              Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) + 1 <= Usize.v (wosize_of_object1 x g) /\
                              Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) >= 1);
 assert (Seq.mem hd (get_allocated_block_addresses g));
 assert (Usize.v (wosize_of_object1 hd g) >= 2 /\
         is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) /\
         Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) + 1 <= Usize.v (wosize_of_object1 hd g) /\
         Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) >= 1);
 ()

#reset-options "--z3rlimit 100"


let colorHeader_props_lemma (g:heap{well_formed_heap2 g}) 
                            (v_id:hp_addr{is_valid_header1 v_id g})
                            (c:color{c == 3UL \/ c == 2UL \/ c == 1UL}) 
                            (g':heap{well_formed_heap2 g'})
                 : Lemma 
                   (requires (Seq.equal g' (colorHeader1 v_id g c)))
                   (ensures  (g' == colorHeader1 v_id g c)) =
 ()

(*let create_edge_list_from_heap_rec_lemma  (g:heap{well_formed_heap2 g}) 
                                          (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                            within_heap_all f /\
                                                            multiple_of_mword_all f /\
                                                            all_valid_headers f g /\
                                                            (G.is_vertex_set f) /\
                                                            all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                            all_field_address_are_word_aligned  f g})
                                           
                                          
                        : Lemma
                          (requires (Seq.length f > 0) /\
                                    Usize.v (tag_of_object1 (Seq.head f) g) < no_scan_tag /\
                                    Usize.v (tag_of_object1 (Seq.head f) g) = closure_tag)
                          (ensures create_edge_list_from_heap1 g f == 
                                     Seq.append (create_edge_pairs_for_h_index g (Seq.head f) (getWosize (read_word g (Seq.head f))) 
                                     (Usize.add (start_env_clos_info g (f_address (Seq.head f))) 1UL)) (create_edge_list_from_heap1 g (Seq.tail f))) =
 admit()
*)

let seq_head_tail_equality_lemma (f: seq Usize.t)
                                 (f1: seq Usize.t)
                 : Lemma
                   (requires (Seq.length f > 0) /\
                             (f == f1))
                   (ensures (Seq.head f == Seq.head f1) /\
                            (Seq.tail f == Seq.tail f1)) =
()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#push-options "--split_queries always"

#restart-solver

let rec create_edge_list_from_heap_lemma  (g:heap{well_formed_heap2 g}) 
                                          (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                            within_heap_all f /\
                                                            multiple_of_mword_all f /\
                                                            all_valid_headers f g /\
                                                            (G.is_vertex_set f) /\
                                                            all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                            all_field_address_are_word_aligned  f g})
                                           
                                           (v_id:hp_addr{is_valid_header1 v_id g})
                                           
                                           (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                                           
                                           (g':heap{well_formed_heap2 g' /\ Seq.equal g' (colorHeader1 v_id g c)})
                                           (f1: seq Usize.t {all_mem_of_allocated_blocks f1 g' /\
                                                             within_heap_all f1 /\
                                                             multiple_of_mword_all f1 /\
                                                             all_valid_headers f1 g' /\
                                                             (G.is_vertex_set f1) /\
                                                             all_objects_and_their_field_pointers_are_within_heap_size f1 g' /\
                                                             all_field_address_are_word_aligned f1 g'})
                          : Lemma
                           (requires (f == f1))
                           (ensures (create_edge_list_from_heap1 g f == create_edge_list_from_heap1 g' f1))
                           (decreases (Seq.length f)) = 
if length f = 0 then 
 (
   let e = Seq.empty #G.edge in
   seq_empty_lemma ();
   
   
   seq_empty_lemma1 f;
   
   ()
 )
 else
 (
   
   seq_non_empty_lemma f;
   let hd = Seq.head f in
   let hd1 = Seq.head f1 in
   assert (is_hp_addr hd);
   can_shift_forward_lemma f g hd;
   assert (Usize.v hd + Usize.v mword < heap_size);
   let tl = Seq.tail f in
   let tl1 = Seq.tail f1 in
   
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));
   
   assert (Seq.length f > Seq.length tl);
   assert (Seq.length f > Seq.length (Seq.tail f));
   length_fn_lemma f;
   assert (length_fn f > length_fn (Seq.tail f));
   assert (length_fn f > length_fn tl);

   seq_head_tail_equality_lemma f f1;
   
   let rest_of_f = create_edge_list_from_heap1 g tl in
   let rest_of_f1 = create_edge_list_from_heap1 g' tl in
   create_edge_list_from_heap_lemma g tl v_id c g' tl;
   assert (create_edge_list_from_heap1 g tl == create_edge_list_from_heap1 g' tl);
   
   let tg = tag_of_object1 hd g in
   colorHeader1_tags_lemma v_id g c g';
   
   if (Usize.v tg < no_scan_tag) then 
   (
     let wz = getWosize (read_word g hd) in
     let wz1 = getWosize (read_word g' hd) in
     let f_id = f_address hd in
     f_address_lemma tl hd;
     assert (forall y. Seq.mem y tl ==> f_address hd <> f_address y);
     assert (hd_address f_id == hd);
     
     colorHeader1_wosize_lemma v_id g c g';
     colorHeader1_alloc_colors_lemma v_id g c;
     colorHeader_props_lemma g v_id c g';
     
     
     field_limits_allocated_blocks_lemma g;
     field_contents_within_limits_allocated_blocks_lemma g;
     fieldaddress_within_limits_lemma_x_all g;
     
     if (Usize.v tg = closure_tag) then
     (
       assert (is_valid_header1 hd g /\
               Usize.v (tag_of_object1 hd g) < no_scan_tag /\
               Usize.v (tag_of_object1 hd g) = closure_tag);
       well_formed_closure_objs_lemma g hd;
       assert (Usize.v wz >= 2);
       assert (Usize.v f_id >= Usize.v mword);
       assert (is_valid_header1 hd g);
       assert (is_valid_header1 (hd_address f_id) g);
       assert (Usize.v (tag_of_object1 (hd_address f_id) g) == closure_tag);
       let start_env = start_env_clos_info g f_id in
       let start_env_plus_one = Usize.add start_env 1UL in

       assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address f_id) g)) /\
             Usize.v start_env >= 1);
       let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz start_env_plus_one in
       //colorHeader1_wosize_lemma v_id g c g';
       assert (wz == wz1);
       assert (Usize.v start_env_plus_one <= Usize.v wz1 + 1 /\ Usize.v start_env_plus_one >= 1);
       let edge_pairs_for_hd1 = create_edge_pairs_for_h_index g' hd wz1 start_env_plus_one in
       //colorHeader1_alloc_colors_lemma v_id g c;
       //colorHeader_props_lemma g v_id c g';
       assert (g' == colorHeader1 v_id g c);
       assert ((objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    (wz == wz1) /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses g'));
       assert ((get_allocs_props g) /\ (get_allocs_props g'));
       create_edge_pairs_for_h_index_lemma1 g hd wz start_env_plus_one v_id c g' wz1;
       
       
       let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
       Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
       assert (edge_pairs_for_hd == edge_pairs_for_hd1);
       assert (rest_of_f == rest_of_f1);

       let f2 = Seq.append (edge_pairs_for_hd1) (rest_of_f1) in
  
   
       Seq.lemma_mem_append (edge_pairs_for_hd1) (rest_of_f1);
       assert (f' == f2);
       assert (f' == create_edge_list_from_heap1 g f);
       assert (hd == hd1);
       assert (tl == tl1);
       let start_env1 = start_env_clos_info g' f_id in
       start_env_clos_info_lemma g f_id v_id c;
       assert (start_env == start_env1);
       assert (f2 == create_edge_list_from_heap1 g' f1);
       assert (create_edge_list_from_heap1 g f == create_edge_list_from_heap1 g' f1);
       ()
     )
     else
     (
       let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz 1UL in
       let edge_pairs_for_hd1 = create_edge_pairs_for_h_index g' hd1 wz1 1UL in
       
       let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
       let f2 = Seq.append (edge_pairs_for_hd1) (rest_of_f1) in 
   
       Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
       Seq.lemma_mem_append (edge_pairs_for_hd1) (rest_of_f1);
       assert (hd == hd1);
       assert (tl == tl1);


       assert (wz == wz1);
       create_edge_pairs_for_h_index_lemma1 g hd wz 1UL v_id c g' wz1;
       assert (edge_pairs_for_hd ==  edge_pairs_for_hd1);
       assert (rest_of_f == rest_of_f1);
       assert (f' == f2);
       assert (f' == create_edge_list_from_heap1 g f);
       assert (f2 == create_edge_list_from_heap1 g' f1);
       assert (create_edge_list_from_heap1 g f == create_edge_list_from_heap1 g' f1);
       ()
     )
   )
   else
   (
     (*branch type checked when other branches are commented out*)
     let edge_pairs_for_hd = Seq.empty #G.edge in
     let edge_pairs_for_hd1 = Seq.empty #G.edge in
     seq_empty_lemma ();
     
     let f_id = f_address hd in
     assert (hd_address f_id == hd);
   
    
     let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
     let f2 = Seq.append (edge_pairs_for_hd1) (rest_of_f1) in
  
   
     Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
     Seq.lemma_mem_append (edge_pairs_for_hd1) (rest_of_f1);
   
   
     
     Seq.append_empty_l rest_of_f;
     Seq.append_empty_l rest_of_f1;
     
     assert (f' == rest_of_f);
     assert (f2 == rest_of_f1);
     assert (f' == f2);
     assert (f' == create_edge_list_from_heap1 g f);
     assert (f2 == create_edge_list_from_heap1 g' f1);
     assert (create_edge_list_from_heap1 g f == create_edge_list_from_heap1 g' f1);
     ()
   )
)

#reset-options "--z3rlimit 500"


let create_edge_list_for_graph_lemma (g:heap{well_formed_heap2 g}) 
                                     (v_id:hp_addr{is_valid_header1 v_id g})
                                     (c:color{c == 3UL \/ c== 2UL \/ c == 1UL})
                    : Lemma 
                      (requires (well_formed_heap2(colorHeader1 v_id g c)))
                      (ensures (create_edge_list_for_graph g == create_edge_list_for_graph (colorHeader1 v_id g c))) = 
  let allocs = get_allocated_block_addresses g in

  field_limits_allocated_blocks_lemma g;
  field_contents_within_limits_allocated_blocks_lemma g;
  fieldaddress_within_limits_lemma_x_all g;
  
  let f  = create_edge_list_from_heap1 g allocs in
  
  let g' = colorHeader1 v_id g c in
  let allocs' = get_allocated_block_addresses g' in
  colorHeader1_alloc_colors_lemma v_id g c;
  
  assert (allocs == allocs');

  field_limits_allocated_blocks_lemma g';
  field_contents_within_limits_allocated_blocks_lemma g';
  fieldaddress_within_limits_lemma_x_all g';
  
  let f' = create_edge_list_from_heap1 g' allocs' in
  
  create_edge_list_from_heap_lemma g allocs v_id c g' allocs';
  assert (f == f');
  ()

let can_be_shift_forward_lemma (wz:Usize.t{Usize.v wz > 0})
               (x:Usize.t{Usize.v x + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size})
          : Lemma
            (ensures (Usize.v x + Usize.v mword < heap_size)) = 
assert (Usize.v wz > 0);
assert (Usize.v x + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size);
assert (Usize.v x + Usize.v mword < heap_size);
()

let can_be_shift_forward_lemma1  (g:heap{well_formed_heap2 g})
                                 (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                            within_heap_all f /\
                                                            multiple_of_mword_all f /\
                                                            all_valid_headers f g /\
                                                            (G.is_vertex_set f) /\
                                                            all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                            all_field_address_are_word_aligned  f g})
                           : Lemma
                             (ensures  (forall x. Seq.mem x f ==> Usize.v x + Usize.v mword < heap_size)) = 
 assert (forall x. Seq.mem x f ==> Usize.v (getWosize (read_word g x)) > 0);
 assert (forall x. Seq.mem x f ==> Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1) < heap_size);
 assert (forall x. Seq.mem x f ==> Usize.v x + Usize.v mword < heap_size);
 ()

#restart-solver 

let create_graph_from_heap_lemma (g:heap {well_formed_heap2 g})
                                 (v_id:hp_addr{is_valid_header1 v_id g})
                                 (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                         : Lemma 
                           (requires (well_formed_heap2 (colorHeader1 v_id g c) /\
                                      (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)))
                           (ensures (create_graph_from_heap g == create_graph_from_heap (colorHeader1 v_id g c))) = 
 let f = get_allocated_block_addresses g in 
 assert ((all_mem_of_allocated_blocks f g) /\
          (within_heap_all f) /\
          (multiple_of_mword_all f) /\
          (all_valid_headers f g) /\
          (G.is_vertex_set f));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 can_be_shift_forward_lemma1 g f;
 assert (can_be_shifted_forward f);
 assert (all_objects_and_their_field_pointers_are_within_heap_size f g);
 assert (all_field_address_are_word_aligned f g); 
 let ff_allocs = first_field_addresses_of_allocated_blocks g f in 

 let g' = colorHeader1 v_id g c in
 let f' = get_allocated_block_addresses g' in
 get_allocated_block_addresses_lemma g g' v_id c;
 assert (f == f');

 field_limits_allocated_blocks_lemma g';
 field_contents_within_limits_allocated_blocks_lemma g';
 fieldaddress_within_limits_lemma_x_all g';
 can_be_shift_forward_lemma1 g' f';
 assert (can_be_shifted_forward f');
 let ff_allocs' = first_field_addresses_of_allocated_blocks g' f' in 
 first_field_addresses_of_allocated_blocks_lemma g f g' f';
 assert (ff_allocs == ff_allocs');
 
 create_edge_list_for_graph_lemma g v_id c;
 assert (create_edge_list_for_graph g == create_edge_list_for_graph g');
 
 let grph1 = create_graph_from_heap g in
 let grph2 = create_graph_from_heap g' in
 assert (grph1 == grph2);
 ()


#restart-solver 

//#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let create_graph_from_heap_lemma_gray (g:heap {well_formed_heap2 g})
                                 (v_id:hp_addr{is_valid_header1 v_id g})
                           : Lemma 
                           (requires (well_formed_heap2 (colorHeader1 v_id g 2UL) /\
                                      (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)))
                           (ensures (create_graph_from_heap g == create_graph_from_heap (colorHeader1 v_id g 2UL))) =
 create_graph_from_heap_lemma g v_id 2UL

#reset-options "--z3rlimit 500"

let tail_cons (#a:eqtype)
              (s: seq a)
              (x: a)
        : Lemma
          (ensures (Seq.tail (Seq.cons x s) == s)) = 
 lemma_tl x s;
 ()
          
let cons_length_lemma2 (#a:Type)
                       (s:seq a)
                       (s_cons:a)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s)) > 0)=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ; 
 ()

let cons_length_lemma1 (#a:Type)
                       (s:seq a)
                       (s_cons:a)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s)) == Seq.length s + 1)=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ; 
 ()



#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let rec create_successors_pick_second_lemma (g:heap{well_formed_heap2 g}) 
                                            (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                            (wz: wosize{valid_wosize g h_index wz})
                         
                                            (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                           : Lemma
                             (ensures (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == 
                                          create_successors_list_for_h_index g h_index wz i))
                             (decreases ((Usize.v wz + 1) - Usize.v i)) = 
if Usize.v i = Usize.v wz + 1 then
(
  seq_empty_lemma ();
  assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);
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
  let e' = create_edge_pairs_for_h_index g h_index wz i' in
  create_successors_pick_second_lemma g h_index wz i';
  assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i') == create_successors_list_for_h_index g h_index wz i');
  if isPointer succ_index g  then
      (
        
         let h_addr_succ = hd_address succ in
        
         let f_index = f_address h_index in
         f_address_hp_address_lemma h_index;
         assert (hd_address f_index == h_index);
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
           cons_length_lemma2 s_list' parent_succ;
           Seq.head_cons parent_succ s_list';
        
           assert (Seq.head s_list == parent_succ);

           let edge_pair = (f_index,parent_succ) in
           lemma_tl edge_pair e'; 
           let e = Seq.cons edge_pair e' in 
        
           cons_length_lemma2 e' edge_pair;
           Seq.head_cons  edge_pair e'; 
           assert (Seq.head e == edge_pair);
           assert (s_list == Seq.cons parent_succ (G.pick_second e'));
           assert (Seq.cons parent_succ (G.pick_second e') == s_list);

           assert (parent_succ == snd (edge_pair));

           assert (Seq.cons (snd edge_pair) (G.pick_second e') == s_list);

           cons_length_lemma1 e' edge_pair; 
           assert (Seq.length e > 0);

           tail_cons e' edge_pair;
           assert (Seq.tail e == e');

           G.pick_second_lemma e;
      
           assert (G.pick_second e == Seq.cons (snd edge_pair) (G.pick_second e'));

           assert (G.pick_second e == s_list);
           assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);

           ()
         )
         else
         (
           
           lemma_tl succ s_list'; 
        
           let s_list = Seq.cons succ s_list' in 
           cons_length_lemma2 s_list' succ;
           Seq.head_cons succ s_list';
        
           assert (Seq.head s_list == succ);

           let edge_pair = (f_index,succ) in
           lemma_tl edge_pair e'; 
           let e = Seq.cons edge_pair e' in 
        
           cons_length_lemma2 e' edge_pair;
           Seq.head_cons  edge_pair e'; 
           assert (Seq.head e == edge_pair);
           assert (s_list == Seq.cons succ (G.pick_second e'));
           assert (Seq.cons succ (G.pick_second e') == s_list);

           assert (succ == snd (edge_pair));

           assert (Seq.cons (snd edge_pair) (G.pick_second e') == s_list);

           cons_length_lemma1 e' edge_pair; 
           assert (Seq.length e > 0);

           tail_cons e' edge_pair;
           assert (Seq.tail e == e');

           G.pick_second_lemma e;
      
           assert (G.pick_second e == Seq.cons (snd edge_pair) (G.pick_second e'));

           assert (G.pick_second e == s_list);
           assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);

        
           assert (Seq.head s_list == succ);

           ()
         )
      )
      else
      (
       
        assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i') == create_successors_list_for_h_index g h_index wz i');
        assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);
        ()
      )
)

let succ_props_pre (g: heap {well_formed_heap2 g})
                   (h_index:hp_addr{is_valid_header1 h_index g}) =
 (is_fields_within_limit1 h_index (getWosize (read_word g h_index)) /\
  is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g /\                                                                    
 (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
            (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\                                                       
 (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
 (Seq.mem (f_address h_index) ((create_graph_from_heap g).vertices)))

#restart-solver 

#reset-options "--z3rlimit 500"

#restart-solver

let succ_props (g: heap {well_formed_heap2 g})
               (h_index:hp_addr{is_valid_header1 h_index g /\
                                succ_props_pre g h_index}) =                                        
   (*1*) (Usize.v (tag_of_object1 h_index g) < no_scan_tag ==> 
            (Usize.v (tag_of_object1 h_index g) == closure_tag) ==>
                                                
               (let f_id = f_address h_index in
                let start_of_env = start_env_clos_info g f_id in
                let start_of_env_plus_one = Usize.add start_of_env 1UL in
                   (G.successors (create_graph_from_heap g) (f_address h_index) == 
                      create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one))) /\
                                  
   (*2*)  (Usize.v (tag_of_object1 h_index g) < no_scan_tag ==>
            (Usize.v (tag_of_object1 h_index g) <> closure_tag) ==>
                   (G.successors (create_graph_from_heap g) (f_address h_index) == 
                      create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL)) /\
                                           
   (*3*)  (Usize.v (tag_of_object1 h_index g) >= no_scan_tag ==> 
                   (G.successors (create_graph_from_heap g) (f_address h_index) == Seq.empty #UInt64.t))    


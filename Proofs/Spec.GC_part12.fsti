module Spec.GC_part12

include Spec.GC_part11

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

//#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq' --split_queries always" //XXX KC: works!


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"
#restart-solver

let rec fieldPush_spec_successor_push_itr_equivalence_lemma2 (g:heap{well_formed_heap2 g})
                                                             (st: seq Usize.t{stack_props_func g st})
                                                             (h_index:hp_addr{ Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                               (Usize.v h_index % Usize.v mword == 0) /\
                                                                               is_valid_header1 h_index g})
                                                             (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                                                             (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                             (j:Usize.t)
                                                             (vl: seq Usize.t{vl_props_func g vl})
                                                             (c:color{Usize.v c == 2})
                                           : Lemma
                                             (requires fieldPush_spec_successor_push_itr_equivalence_lemma2_pre_props g st h_index wz i j vl)

                                            (ensures   fieldPush_spec_successor_push_itr_equivalence_lemma2_post_props g st h_index wz i j vl)
                                            (decreases ((Usize.v wz + 1) - Usize.v i))  =
  let grph = create_graph_from_heap g in
  let l = G.successors grph (f_address h_index) in
  graph_successors_length_lemma g h_index;
  graph_successors_mem_lemma g h_index;
  assert (Seq.length l <= Usize.v (getWosize (read_word g h_index)));
  assert (forall x. Seq.mem x  l ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));
 if Usize.v i = Usize.v wz + 1 then
  (
    create_successors_list_for_h_index_i_equals_wz_plus_one_implies_succ_list_from_j_is_empty g st h_index wz i j;
    assert (Usize.v j == Seq.length l);
    let st' = G.successor_push_itr1 l vl st (Usize.v j) in
    G.successor_push_itr1_lemma1 l vl st (Usize.v j);
    assert (st' == st);
    assert (fst (fieldPush_spec1 g st h_index wz i) == st);
    assert (G.successor_push_itr1 l vl st (Usize.v j) == st);
    ()
  )
  else
  (
    let i' = Usize.add i 1UL in
    assert (Usize.v i < Usize.v wz + 1);
    assert (Seq.length (objects2 0UL g) > 0);
    h_index_field_within_heap_size g h_index wz i;
    //assume (UInt.fits (Usize.v h_index + (Usize.v i * Usize.v mword)) Usize.n);
    assert (Usize.v h_index + (Usize.v i * Usize.v mword) < heap_size);
    let succ_index = Usize.add h_index (Usize.mul i mword) in

    assert (Usize.v succ_index < heap_size);
    max_wosize_times_mword_multiple_of_mword i;
    sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
    assert (Usize.v succ_index % Usize.v mword == 0);
    assert (is_hp_addr succ_index);
    //let succ = read_word g succ_index in
    let st', g' = fieldPush_spec_body1 g st h_index wz i in
    arithmetic_lemma i wz;
    assert (Usize.v i <= Usize.v wz);
    arithmetic_lemma1 i wz;
    assert (Usize.v i - 1 < Usize.v wz);
    //assert (Seq.length l <= Usize.v wz);
   // assert (Usize.v j <= Seq.length l);
    if (Usize.v j = Seq.length l) then
    (
       let l' = (graph_successors_create_from_an_index g h_index l j) in
       assert (l' == Seq.empty);
       length_empty_lemma l';
       assert (Seq.length l' == 0);
       (*This means starting from index i if we scan the fields of h_index, we will not get any field pointers.
         So even if we call fieldPush_spec_body, it will return the
        stack as unaffected. There is no point in recursively continuing the fieldPush at this point.*)

        assert (Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) == 0);
        create_successors_list_for_h_index_recursing_property_lemma3 g h_index wz i i';
        assert ((create_successors_list_for_h_index g h_index wz i == Seq.empty) ==>
             (create_successors_list_for_h_index g h_index wz i' == Seq.empty));

        assert ((graph_successors_create_from_an_index g h_index l j) ==
             (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i));
       (*Essential pre-condition to continue the recursive call*)
       (*---------------------------------------------------------------------------------------------------------------------------------------*)
       assert ((graph_successors_create_from_an_index g h_index l j) ==
               (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i'));
       let st_gr = G.successor_push_itr1 l vl st (Usize.v j) in
       G.successor_push_itr1_lemma1 l vl st (Usize.v j);
       assert (st_gr == st);

       create_successors_list_for_h_index_recursing_property_lemma4  g h_index wz i;
        //This is required to establish that fieldPush_spec_body returns the stack as unchanged as the field value is not a pointer
        //---------------------------------------------------------------------------------------------------------------------------------------
       assert (~(isPointer(Usize.add h_index (Usize.mul i mword)) g));
       fieldPush_spec_body_successor_push_body_equivalence_lemma3 g st h_index wz i vl;

       assert (st' == st);
       slice_length_props_all_lemma g;
       slice_length_props_all_lemma g';
       assert (slice_length_props g);
       assert (slice_length_props g');
       //fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
       fieldPush_spec_body_graph_lemma g st h_index wz i;
       //assert (well_formed_allocated_blocks g');
       //fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
       let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
       let st2 = G.successor_push_itr1 l vl st (Usize.v j) in
        let wz' = getWosize (read_word g' h_index) in
       assert (wz == wz');
       assert (objects2 0UL g == objects2 0UL g');
       fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
       fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;
       (*Essential pre-condition to continue the recursive call*)
       (*---------------------------------------------------------------------------------------------------------------------------------------*)
       assert ((graph_successors_create_from_an_index g h_index l j) ==
             (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i'));

       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j vl c;
       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st (Usize.v j));
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body1 g st h_index wz i))
                                                                                        (fst (fieldPush_spec_body1 g st h_index wz i))
                                                                                        h_index
                                                                                        wz
                                                                                        i');
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');
       G.successor_push_itr1_lemma1 l vl st (Usize.v j);
       assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 l (vl) (st) (Usize.v j));
       ()
    )
    else
    (
      (*In this branch only, we can invoke (G.successor_push_body1). This is because j should be < Seq.length l *)
       assert (~(Usize.v j == Seq.length l));
       length_less_than_or_equal_lemma l j;
       assert (Usize.v j < Seq.length l);
       assert (Usize.v i < Usize.v wz + 1);

       field_limits_allocated_blocks_lemma g;
       field_contents_within_limits_allocated_blocks_lemma g;
       fieldaddress_within_limits_lemma_x_all g;

       field_limits_allocated_blocks_lemma g';
       field_contents_within_limits_allocated_blocks_lemma g';
       fieldaddress_within_limits_lemma_x_all g';

       assert (is_hp_addr succ_index);
       lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
       assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
       assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
       assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);
       //let succ = read_word g succ_index in
       let succ = get_succ_value g h_index wz i in
       //let b = isPointer succ_index g in
       // 2 cases
       //Case 1: (isPointer(Usize.add h_index (Usize.mul i mword)) g)
        if ((*b*)isPointer succ_index g) then
        (
         let h_addr_succ = hd_address succ in
         //test_allocs g h_index wz;
         //assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
         //assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
         //assert (Seq.mem (hd_address succ) (objects2 0UL g));
         //assert (is_valid_header (hd_address succ) g);

         //assert (well_formed_allocated_blocks g);
         assert (Seq.mem h_index (get_allocated_block_addresses g));

         let tg = tag_of_object1 h_addr_succ g in
         let j' = Usize.add j 1UL in
         (*assert ((forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x)))) /\
                                   (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) /\
                                   (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                            (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                            (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)); *)

           assert (is_hp_addr (Usize.add h_index (Usize.mul i mword)));
           assert (Usize.v (field_ptr_construct g h_index wz i) == Usize.v (Usize.add h_index (Usize.mul i mword)));
           assert (isPointer succ_index g);
           assert (field_ptr_construct g h_index wz i == succ_index);
           assert (isPointer (field_ptr_construct g h_index wz i) g);
           create_successors_list_for_h_index_pointer_lemma g h_index wz i;
           assert (Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0);


           if Usize.v tg = infix_tag then
           (
             (*assert (Usize.v tg == infix_tag);
             create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j3 g h_index wz i j;
             assert (Seq.index l (Usize.v j) == f_address (parent_closure_of_infix_object g h_index i));
             create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j2 g h_index wz i j;
             let st'' = G.successor_push_body1 l vl st (Usize.v j) in
             //fieldPush_spec_body_lemma should ensure that the stack returned by fieldPush_spec_body and successor_push_body are the same
             (*Call fieldPush_spec_body_lemma*)
             fieldPush_spec_body_successor_push_body_equivalence_lemma2 g st h_index wz i j vl;
             assert (st' == st'');
             field_limits_allocated_blocks_lemma g;
             //field_limits_allocated_blocks_lemma g';
             field_contents_within_limits_allocated_blocks_lemma g';
             lemma_len_slice_invoke_all1 g;
             lemma_len_slice_invoke_all1 g';
             assert (Seq.mem h_index (get_allocated_block_addresses g));
             assert (Seq.mem h_index (get_allocated_block_addresses g'));
             assert  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);
             assert (stack_props_func g st);
             assert (Usize.v wz == Usize.v (getWosize (read_word g h_index)));

             //fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
             //assert (well_formed_allocated_blocks g');

             fieldPush_spec_body_graph_lemma g st h_index wz i;
             assert  (create_graph_from_heap g == create_graph_from_heap g');
             //assert (well_formed_allocated_blocks g');
             //fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
             let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
             let st2 = G.successor_push_itr1 l vl st' (Usize.v j') in
             let wz' = getWosize (read_word g' h_index) in
             assert (wz == wz');
             assert (objects2 0UL g == objects2 0UL g');
             assert (vl_props_func g vl);
             assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
             fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
             fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;

         (*Essential pre-condition to continue the recursive call*)
        (*---------------------------------------------------------------------------------------------------------------------------------------*)
        assert (graph_successors_create_from_an_index g h_index l j' ==
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');

        assert ((forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
              (forall x. Seq.mem x vl ==> ~(Seq.mem x st')));
        assert (Usize.v j' <= Seq.length l);

        assert (is_fields_within_limit1 h_index (getWosize (read_word g' h_index)));

        assert (well_formed_heap2 g');
        assert (get_allocated_block_addresses g ==  get_allocated_block_addresses g');
        assert (Seq.mem h_index (get_allocated_block_addresses g));
        assert (Seq.mem h_index (get_allocated_block_addresses g'));
        field_contents_within_limits_allocated_blocks_lemma g';



       assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g' h_index)) g');

       //fieldaddress_within_limits_lemma_x_all g';
       (*assert (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g' h_index)) ==>
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0);*)


       assert (all_field_address_are_word_aligned (get_allocated_block_addresses g') g');
       graph_successors_create_from_an_index_equivalence_lemma g st h_index wz i l j' g' wz' l;
       assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');
       //assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');

       //assert (h_index_within_limits g h_index);

       //assert (well_formed_allocated_blocks g');
       assert (h_index_within_limits g h_index);
       assert (Usize.v i' <= Usize.v wz + 1 /\ Usize.v i' >= 1);
       assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
       assert (wz' == getWosize (read_word (snd (fieldPush_spec_body1 g st h_index wz i)) h_index));
       assert (Usize.v i' <= Usize.v wz + 1 /\ Usize.v i' >= 1);
       fieldPush_spec_body_create_successors_for_h_index_lemma g st h_index wz i wz' c i';

       //create_succcessors_for_h_index_lemma3 g h_index wz i' g' wz';

       assert (graph_successors_create_from_an_index g h_index l j' ==
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');
       assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');


       //create_succcessors_for_h_index_lemma5 g h_index wz st i' i g' wz';
       //fieldPush_spec_body_create_successors_for_h_index_lemma g st h_index wz i wz' 2UL i';
       assert ((create_successors_list_for_h_index g h_index wz i' ==
                create_successors_list_for_h_index g' h_index wz' i'));

       assert (graph_successors_create_from_an_index g' h_index l j' ==
                          create_successors_list_for_h_index g' h_index (getWosize (read_word g' h_index)) i');


       assert ((h_index_within_limits g' h_index) /\
               (all_field_address_are_word_aligned (get_allocated_block_addresses g') g') /\
               (Seq.mem (f_address h_index) (create_graph_from_heap g').vertices) /\
               (Seq.length (G.successors (create_graph_from_heap g') (f_address h_index)) <= Usize.v wz) /\
               (Usize.v j' <= Seq.length (G.successors (create_graph_from_heap g') (f_address h_index))) /\
               (graph_successors_create_from_an_index g' h_index (G.successors (create_graph_from_heap g') (f_address h_index)) j') ==
                                                          (create_successors_list_for_h_index g' h_index (getWosize (read_word g' h_index)) i'));
       assert ((forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
               (forall x. Seq.mem x vl ==> ~(Seq.mem x st')));
       fieldPush_spec_body_vl_props_lemma g st h_index wz i vl;
       assert (vl_props_func g' vl);
       assert (fieldPush_spec_successor_push_itr_equivalence_lemma2_pre_props g' st' h_index wz i' j' vl);
       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j' vl c;

       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st' (Usize.v j'));
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body1 g st h_index wz i))
                                                                                        (fst (fieldPush_spec_body1 g st h_index wz i))
                                                                                        h_index
                                                                                        wz
                                                                                        i');
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');
       G.successor_push_itr1_lemma l vl st (Usize.v j);
       assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 l (vl) (st)  (Usize.v j));
       assert (fst (fieldPush_spec1 g st h_index wz i) ==
                                                            G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index))
                                                                                  (vl)
                                                                                  (st)
                                                                                  (Usize.v j));
       ()*)
       admit()

           )
           else
           (
             assert (Usize.v tg <> infix_tag);
             create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j1 g h_index wz i j;
             //This is the essential precondition for fieldPush_spec body lemma to get the fact that the fieldPush_body and successor_push_body pushes the same field pointer
             //to the stack
             assert (Seq.index l (Usize.v j) ==  read_word g (Usize.add h_index (Usize.mul i mword)));
             create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j2 g h_index wz i j;
             let st'' = G.successor_push_body1 l vl st (Usize.v j) in
             //fieldPush_spec_body_lemma should ensure that the stack returned by fieldPush_spec_body and successor_push_body are the same
             (*Call fieldPush_spec_body_lemma*)
             fieldPush_spec_body_successor_push_body_equivalence_lemma2 g st h_index wz i j vl;
             assert (st' == st'');
             field_limits_allocated_blocks_lemma g;
             //field_limits_allocated_blocks_lemma g';
             field_contents_within_limits_allocated_blocks_lemma g';
             lemma_len_slice_invoke_all1 g;
             lemma_len_slice_invoke_all1 g';
             assert (Seq.mem h_index (get_allocated_block_addresses g));
             assert (Seq.mem h_index (get_allocated_block_addresses g'));
             assert  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);
             assert (stack_props_func g st);
             assert (Usize.v wz == Usize.v (getWosize (read_word g h_index)));

             //fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
             //assert (well_formed_allocated_blocks g');

             fieldPush_spec_body_graph_lemma g st h_index wz i;
             assert  (create_graph_from_heap g == create_graph_from_heap g');
             //assert (well_formed_allocated_blocks g');
             //fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
             let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
             let st2 = G.successor_push_itr1 l vl st' (Usize.v j') in
             let wz' = getWosize (read_word g' h_index) in
             assert (wz == wz');
             assert (objects2 0UL g == objects2 0UL g');
             assert (vl_props_func g vl);
             assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
             fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
             fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;

         (*Essential pre-condition to continue the recursive call*)
        (*---------------------------------------------------------------------------------------------------------------------------------------*)
        assert (graph_successors_create_from_an_index g h_index l j' ==
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');

        assert ((forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
              (forall x. Seq.mem x vl ==> ~(Seq.mem x st')));
        assert (Usize.v j' <= Seq.length l);

        assert (is_fields_within_limit1 h_index (getWosize (read_word g' h_index)));

        assert (well_formed_heap2 g');
        assert (get_allocated_block_addresses g ==  get_allocated_block_addresses g');
        assert (Seq.mem h_index (get_allocated_block_addresses g));
        assert (Seq.mem h_index (get_allocated_block_addresses g'));
        field_contents_within_limits_allocated_blocks_lemma g';



       assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g' h_index)) g');

       //fieldaddress_within_limits_lemma_x_all g';
       (*assert (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g' h_index)) ==>
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0);*)


       assert (all_field_address_are_word_aligned (get_allocated_block_addresses g') g');
       graph_successors_create_from_an_index_equivalence_lemma g st h_index wz i l j' g' wz' l;
       assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');
       //assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');

       //assert (h_index_within_limits g h_index);

       //assert (well_formed_allocated_blocks g');
       assert (h_index_within_limits g h_index);
       assert (Usize.v i' <= Usize.v wz + 1 /\ Usize.v i' >= 1);
       assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
       assert (wz' == getWosize (read_word (snd (fieldPush_spec_body1 g st h_index wz i)) h_index));
       assert (Usize.v i' <= Usize.v wz + 1 /\ Usize.v i' >= 1);
       fieldPush_spec_body_create_successors_for_h_index_lemma g st h_index wz i wz' c i';

       //create_succcessors_for_h_index_lemma3 g h_index wz i' g' wz';

       assert (graph_successors_create_from_an_index g h_index l j' ==
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');
       assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');


       //create_succcessors_for_h_index_lemma5 g h_index wz st i' i g' wz';
       //fieldPush_spec_body_create_successors_for_h_index_lemma g st h_index wz i wz' 2UL i';
       assert ((create_successors_list_for_h_index g h_index wz i' ==
                create_successors_list_for_h_index g' h_index wz' i'));

       assert (graph_successors_create_from_an_index g' h_index l j' ==
                          create_successors_list_for_h_index g' h_index (getWosize (read_word g' h_index)) i');


       fieldPush_spec_body_vl_props_lemma g st h_index wz i vl;
       assert (vl_props_func g' vl);
       assert (fieldPush_spec_successor_push_itr_equivalence_lemma2_pre_props g' st' h_index wz i' j' vl);
       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j' vl c;

       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st' (Usize.v j'));
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body1 g st h_index wz i))
                                                                                        (fst (fieldPush_spec_body1 g st h_index wz i))
                                                                                        h_index
                                                                                        wz
                                                                                        i');
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');
       G.successor_push_itr1_lemma l vl st (Usize.v j);
       assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 l (vl) (st)  (Usize.v j));
       assert (fst (fieldPush_spec1 g st h_index wz i) ==
                                                            G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index))
                                                                                  (vl)
                                                                                  (st)
                                                                                  (Usize.v j));
       ()
       )
        )
        else
        (
              //fieldPush_spec_body returns the stack as unchanged as the field value is not a pointer
       //---------------------------------------------------------------------------------------------------------------------------------------
       //assert (~(b));
       create_successors_list_for_h_index_recursing_property_lemma g h_index wz i i';
       assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g h_index wz i');

       //fieldPush_spec_body_lemma should ensure that the stack is returned as unchanged
       (*Call fieldPush_spec_body_lemma*)
       fieldPush_spec_body_successor_push_body_equivalence_lemma2 g st h_index wz i j vl;
       assert (st == st');

       field_limits_allocated_blocks_lemma g;
       field_contents_within_limits_allocated_blocks_lemma g';
       lemma_len_slice_invoke_all g;
       lemma_len_slice_invoke_all g';
       //assert (forall (t:hp_addr). length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8);

       (*assert (forall (t:hp_addr). length (slice (snd (fieldPush_spec_body1 g st h_index wz i)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8);*)
       //fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
       fieldPush_spec_body_graph_lemma g st h_index wz i;

       //assert (well_formed_allocated_blocks g');
       assert (Seq.mem h_index (get_allocated_block_addresses g));
       assert (Seq.mem h_index (get_allocated_block_addresses g'));
       assert (stack_props_func g' st');
       //fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
       let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
       let st2 = G.successor_push_itr1 l vl st (Usize.v j) in
       let wz' = getWosize (read_word g' h_index) in
       assert (wz == wz');
       assert (objects2 0UL g == objects2 0UL g');

       fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
       fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;



       (*Essential pre-condition to continue the recursive call*)
       (*---------------------------------------------------------------------------------------------------------------------------------------*)
       assert ((graph_successors_create_from_an_index g h_index l j) ==
             (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i'));

       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j vl c;
       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st (Usize.v j));
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body1 g st h_index wz i))
                                                                                        (fst (fieldPush_spec_body1 g st h_index wz i))
                                                                                        h_index
                                                                                        wz
                                                                                        i');
       (*assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');*)
       G.successor_push_itr1_lemma l vl st (Usize.v j);
       (*assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 l (vl) (st) (Usize.v j));*)

       ()

        )

    )
  )

#reset-options "--z3rlimit 1000"

#restart-solver

#restart-solver

#restart-solver

let all_mem_implies_subset (s1:seq Usize.t)
                           (s2:seq Usize.t)
                   : Lemma
                     (requires (G.is_vertex_set s1 /\
                                G.is_vertex_set s2 /\
                                (forall x. Seq.mem x s1 ==> Seq.mem x s2)))
                     (ensures (G.subset_vertices s1 s2)) = ()

#restart-solver

#restart-solver


let all_mem_st_mem_st'_in_stack (st:stack)
                                (st':stack) = (forall x. Seq.mem x st ==> Seq.mem x st')



#restart-solver

#restart-solver

let valid_header_lemma1 (g:heap{well_formed_heap2 g})
                        (i:nat)
                        (succ:seq Usize.t { i <= Seq.length succ  ==>
                                     ((forall x. Seq.mem x (Seq.slice succ i (Seq.length succ)) ==>
                                              Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                      (forall x. Seq.mem x (Seq.slice succ i (Seq.length succ)) ==>
                                              is_valid_header1 x g))})
             : Lemma
               (ensures ((i + 1) <= Seq.length succ ==>
                              ((forall x. Seq.mem x (Seq.slice succ (i + 1) (Seq.length succ)) ==>
                                              Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                      (forall x. Seq.mem x (Seq.slice succ (i + 1) (Seq.length succ)) ==>
                                              is_valid_header1 x g)))) = ()

let color_stack_mem_lemma  (g:heap{well_formed_heap2 g})
                               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                 (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                 (forall x. Seq.mem x st ==> is_valid_header1 x g) /\
                                                 (G.is_vertex_set st) /\
                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                                })
                               (succ:hp_addr{is_valid_header1 succ g /\
                                                (color_of_object1 succ g == white \/
                                                 color_of_object1 succ g == gray \/
                                                 color_of_object1 succ g == black
                                                )})
                   : Lemma
                     (requires (color_of_object1 succ g == white))
                     (ensures (~(isGrayObject1 succ g) /\
                               ~(isBlackObject1 succ g) /\
                               ~(Seq.mem succ st))) = ()

#restart-solver

let slice_property_lemma (g:heap{well_formed_heap2 g})
                         (st: seq Usize.t)
                         (st_top: Usize.t)
                 : Lemma
                   (requires Usize.v st_top <= Seq.length st /\
                             Usize.v st_top > 0 /\
                             (forall x. Seq.mem x (Seq.slice st 0 (Usize.v st_top)) ==>
                                        Usize.v x >= 0 /\ Usize.v x < heap_size))
                   (ensures (forall x. Seq.mem x (Seq.slice st 0 (Usize.v st_top - 1)) ==>
                                         Usize.v x >= 0 /\ Usize.v x < heap_size)) =
 Seq.lemma_slice_snoc st 0 (Usize.v st_top);
 ()

let slice_coloring_lemma (g:heap{well_formed_heap2 g})
                         (g':heap{well_formed_heap2 g'})
                         (v_id: hp_addr{is_valid_header1 v_id g /\
                                      is_valid_header1 v_id g'})
                         (s: seq Usize.t)
                         (s_top:Usize.t{Usize.v s_top <= Seq.length s})
         : Lemma
              (requires (G.is_vertex_set (Seq.slice s 0 (Usize.v s_top)) /\
                        ~(Seq.mem v_id (Seq.slice s 0 (Usize.v s_top))) /\
                         color_of_object1 v_id g' == black /\
                         heap_remains_same_except_index_v_id v_id g g' /\
                         (objects2 0UL g ==
                             objects2 0UL g') /\
                         (get_allocated_block_addresses g ==
                              get_allocated_block_addresses g') /\

                         color_of_object1 v_id g == gray /\
                         (forall y. Seq.mem y (Seq.slice s 0 (Usize.v s_top)) \/
                          (y == v_id) <==> Seq.mem y (objects2 0UL g) /\ isGrayObject1 y g)))
              (ensures ((forall y. Seq.mem y (Seq.slice s 0 (Usize.v s_top)) <==>
                             Seq.mem y (objects2 0UL g') /\ isGrayObject1 y g'))) = ()

#restart-solver

#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver

let h_index_field_index_mword_multiple_lemma2 (g:heap{well_formed_heap2 g})
                                             (h_index: hp_addr{is_valid_header1 h_index g})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) =

max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()

let fieldaddress_within_limits_lemma1 (g:heap{well_formed_heap2 g})
                                     (x:hp_addr{is_valid_header1 x g})
                                     (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))})
                          : Lemma
                            (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                            (ensures (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) =
 h_index_field_index_mword_multiple_lemma2 g x (getWosize (read_word g x)) i

#restart-solver

let fieldaddress_within_limits_lemma_x_i_all1(g:heap{well_formed_heap2 g})
                                             (x:hp_addr{is_valid_header1 x g})
                           : Lemma
                             (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                             (ensures (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) =
Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma1 g x))

#restart-solver

let fieldaddress_within_limits_lemma_x_all1 (g:heap{well_formed_heap2 g})
                                    : Lemma
                                      (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                                      (ensures (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) =
 Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma_x_i_all1 g))

#restart-solver

#restart-solver

#restart-solver


let seq_length_minus_one_is_less_than_seq_length (s:seq Usize.t)
                                 : Lemma
                                   (ensures ((Seq.length s - 1) < Seq.length s)) = ()


#restart-solver

let is_vertex_set_slice (g:heap{well_formed_heap2 g})
                        (st: seq Usize.t{G.is_vertex_set st /\  (~(G.is_emptySet st)) /\
                                         (forall x. Seq.mem x st ==> Seq.mem (hd_address x) (get_allocated_block_addresses g))
                                         })

            : Lemma
              (ensures (G.is_vertex_set (Seq.slice st 0 (Seq.length st - 1)) /\
                       (forall x. Seq.mem x (Seq.slice st 0 (Seq.length st - 1)) ==> Seq.mem (hd_address x) (get_allocated_block_addresses g)))) =
 G.is_vertex_set_lemma3 st;
 slice_mem_lemma st (Seq.slice st 0 (Seq.length st - 1));
 assert (G.is_vertex_set (Seq.slice st 0 (Seq.length st - 1)));
 ()

#restart-solver

#restart-solver

let test_helper (y:hp_addr{(Usize.v y + Usize.v mword < heap_size)})
    : Lemma
      (ensures (hd_address (f_address y) == y)) =
let f_y = f_address y in
let y' = hd_address f_y in
assert (y' == y);
()

let test_helper1 (s1:seq Usize.t)
                 (s2:seq Usize.t)
                 (y:Usize.t)
         : Lemma
           (requires (forall x. Seq.mem x s1 ==> Seq.mem x s2 \/ x == y) /\ Seq.mem y s2)
           (ensures (forall x. Seq.mem x s1 ==> Seq.mem x s2)) = ()

#restart-solver

let test_helper3 (s1:seq Usize.t{(forall x. Seq.mem x s1 ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                 (forall x. Seq.mem x s1 ==> Usize.v x % Usize.v mword == 0)})
                 (s2:seq Usize.t)
                 (y:hp_addr{(Usize.v y + Usize.v mword < heap_size)})
         : Lemma
           (requires (forall x. Seq.mem x s1 ==> Seq.mem (hd_address x) s2 \/ x == (f_address y)) /\ Seq.mem (hd_address (f_address y)) s2)
           (ensures (forall x. Seq.mem x s1 ==> Seq.mem (hd_address x) s2)) =
()

#restart-solver

let test_helper5 (y:hp_addr{(Usize.v y + Usize.v mword < heap_size)})
       : Lemma
         (ensures (forall x. hd_address x == y ==> x == f_address y)) = ()

#restart-solver

#restart-solver

let test29 (g:heap{well_formed_heap2 g})
           (y:hp_addr{Seq.mem y (get_allocated_block_addresses g)})
           (vl: seq Usize.t{vl_props_func g vl})
       : Lemma
         (requires  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                    ~(Seq.mem (f_address y) vl))
         (ensures True) =
 let allocs = get_allocated_block_addresses g in
 fieldaddress_within_limits_lemma_x_all g;
 let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in
 assert (forall x. Seq.mem x allocs <==> Seq.mem (f_address x) ff_allocs);
 assert (forall x. Seq.mem x ff_allocs <==> Seq.mem (hd_address x) allocs);
 assert (forall x. Seq.mem (hd_address x) allocs ==> Seq.mem x ff_allocs);
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) (objects2 0UL g));
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) allocs);
 assert (forall x. Seq.mem x vl ==> Seq.mem (f_address (hd_address x)) ff_allocs);
 assert (forall x. Seq.mem x vl ==> Seq.mem x ff_allocs);
 let grph = create_graph_from_heap g in
 assert (Seq.mem y allocs);
 assert (Seq.mem (f_address y) ff_allocs);
 assert (Seq.mem (f_address y) grph.vertices);
 assert (G.subset_vertices vl (grph.vertices));
 let f_y = f_address y in
 let vl' = G.insert_to_vertex_set grph f_y vl in
 let g' = colorHeader1 y g black in
 assert (forall x. Seq.mem x vl ==> Seq.mem x vl');
 assert (Seq.mem f_y vl');
 assert (isBlackObject1 y g');
 colorHeader1_subset_lemma y g;

 let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
 let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in

 assert (forall x. Seq.mem x blacks ==>  Seq.mem x blacks');

 assert (forall x. Seq.mem x blacks <==> Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g);
 assert (forall x. Seq.mem x blacks' <==> Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g');

 assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g ==> Seq.mem x blacks');
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g ==> Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g');

 G.insert_to_vertex_set_lemma grph f_y vl;
 assert (~(exists x. (Seq.mem x vl') /\ ~(Seq.mem x vl) /\ x <> f_y));
 colorHeader1_mem_lemma y g;

 assert (~(exists x. (Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g') /\
                ~(Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g) /\
                                    (x <> y)));
 objects2_equal_lemma 0UL g g';
 assert (G.is_vertex_set vl');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl);
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g);
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) (objects2 0UL g') /\ isBlackObject1 (hd_address x) g');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g ==> Seq.mem x vl);
 assert (Seq.mem f_y vl' /\ isBlackObject1 y g');
 assert (~(exists x. (Seq.mem x vl') /\ ~(Seq.mem x vl) /\ x <> f_y));
 assert (~(exists x. (Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g') /\
                ~(Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g) /\
                                    (x <> y)));
 assert (forall x. Seq.mem x vl' <==> Seq.mem x vl \/ x == f_y);
 assert (forall x. Seq.mem x vl' ==> Seq.mem x vl \/ x == f_y);
 assert (forall x. Seq.mem x vl' ==> (Seq.mem (hd_address x) (objects2 0UL g') /\ isBlackObject1 (hd_address x) g') \/ x == f_y);
 assert (Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g');
 test_helper y;
 assert (hd_address (f_address y) == y);
 assert (forall x. Seq.mem x vl' ==> Seq.mem (hd_address x) blacks' \/ x == f_y);
 assert (Seq.mem y blacks');
 assert (Seq.mem (hd_address (f_address y)) blacks');
 assert (f_y == f_address y);
 assert (Seq.mem (hd_address f_y) blacks');
 test_helper3 vl' blacks' y;
 assert (forall x. Seq.mem x vl' ==> Seq.mem (hd_address x) blacks');
 assert (forall x. Seq.mem x vl \/ x == f_y ==> Seq.mem x vl');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g ==> Seq.mem x vl);
 assert (forall x. Seq.mem (hd_address x) blacks ==> Seq.mem x vl);
 assert (forall x. Seq.mem x blacks' ==>  Seq.mem x blacks \/ x == y);
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) blacks);
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) blacks');
 assert (forall x. Seq.mem (hd_address x) blacks \/ x == f_y ==> Seq.mem x vl');
 assert (forall x. Seq.mem x blacks \/ x == y ==> Seq.mem x blacks');
 assert (Seq.mem (hd_address f_y) blacks');
 assert (forall x. Seq.mem x blacks \/ x == y <==> Seq.mem x blacks');
 assert (forall x. Seq.mem (hd_address x) blacks \/ (hd_address x) == y <==> Seq.mem (hd_address x) blacks');
 test_helper5 y;
 assert (forall x. hd_address x == y ==> (x == f_address y));
 assert (forall x. Seq.mem (hd_address x) blacks \/ x == (f_address y) <==> Seq.mem (hd_address x) blacks');
 assert (forall x. Seq.mem (hd_address x) blacks' ==> Seq.mem x vl');
 assert (forall x. Seq.mem (hd_address x) blacks' <==> Seq.mem x vl');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isBlackObject1 (hd_address x) g' <==> Seq.mem x vl');
 ()

#restart-solver

let visited_list_lemma (g:heap{well_formed_heap2 g})
                       (vl: seq Usize.t{vl_props_func g vl})
                       (x: Usize.t{Usize.v x >= 0 /\ Usize.v x < heap_size /\
                                   (Usize.v x % Usize.v mword == 0) /\
                                 is_valid_header1 x g /\
                                 isGrayObject1 x g /\
                                 ~(Seq.mem (f_address x) vl)})

             : Lemma
               (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                          (Seq.mem (f_address x) (create_graph_from_heap g).vertices) /\
                          (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))

               (ensures (let grph = create_graph_from_heap g in
                         let f_x = f_address x in
                         let vl' = G.insert_to_vertex_set grph f_x vl in
                         let g' = colorHeader1 x g black in
                         let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
                         (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> Seq.mem y vl') /\
                         (forall y. Seq.mem (hd_address y) blacks' <==> Seq.mem y vl')

                        )) =
let allocs = get_allocated_block_addresses g in
assert (G.is_vertex_set allocs); // This assert is required
assert (all_field_address_are_word_aligned allocs g);
fieldaddress_within_limits_lemma_x_all g;
let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in
assert (forall y. Seq.mem y allocs <==> Seq.mem (f_address y) ff_allocs);
assert (forall y. Seq.mem y ff_allocs <==> Seq.mem (hd_address y) allocs);
assert (forall y. Seq.mem (hd_address y) allocs ==> Seq.mem y ff_allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) (objects2 0UL g));
assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem (f_address (hd_address y)) ff_allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem y ff_allocs);
let grph = create_graph_from_heap g in
assert (Seq.mem x allocs);
assert (Seq.mem (f_address x) ff_allocs);
assert (Seq.mem (f_address x) grph.vertices);
assert (G.subset_vertices vl (grph.vertices));
let f_x = f_address x in
let vl' = G.insert_to_vertex_set grph f_x vl in
let g' = colorHeader1 x g black in
assert (forall x. Seq.mem x vl ==> Seq.mem x vl');
assert (Seq.mem f_x vl');
assert (isBlackObject1 x g');
colorHeader1_subset_lemma x g;
let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
assert (forall y. Seq.mem y blacks ==>  Seq.mem y blacks');

 assert (forall y. Seq.mem y blacks <==> Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g);
 assert (forall y. Seq.mem y blacks' <==> Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g');

 assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g ==> Seq.mem y blacks');
 assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g ==> Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g');

 G.insert_to_vertex_set_lemma grph f_x vl;
 assert (~(exists y. (Seq.mem y vl') /\ ~(Seq.mem y vl) /\ y <> f_x));
 colorHeader1_mem_lemma x g;
 assert (~(exists y. (Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g') /\
                ~(Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g) /\
                                    (x <> y)));

 objects2_equal_lemma 0UL g g';
 assert (G.is_vertex_set vl');
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isBlackObject1 (hd_address y) g <==> Seq.mem y vl);
 assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) (objects2 0UL g) /\ isBlackObject1 (hd_address y) g);
 assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g');
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isBlackObject1 (hd_address y) g ==> Seq.mem y vl);
 assert (Seq.mem f_x vl' /\ isBlackObject1 x g');
 test_helper x;
 assert (hd_address (f_address x) == x);
 assert (forall y. Seq.mem y vl' ==> Seq.mem (hd_address y) blacks' \/ y == f_x);
 assert (Seq.mem x blacks');
 assert (Seq.mem (hd_address (f_address x)) blacks');
 assert (f_x == f_address x);
 assert (Seq.mem (hd_address f_x) blacks');
 test_helper3 vl' blacks' x;
 assert (forall y. Seq.mem y vl' ==> Seq.mem (hd_address y) blacks');
 assert (forall y. Seq.mem y vl \/ y == f_x ==> Seq.mem y vl');
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isBlackObject1 (hd_address y) g ==> Seq.mem y vl);
 assert (forall y. Seq.mem (hd_address y) blacks ==> Seq.mem y vl);
 assert (forall y. Seq.mem y blacks' ==>  Seq.mem y blacks \/ y == x);
 assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) blacks);
 assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) blacks');
 assert (forall y. Seq.mem (hd_address y) blacks \/ y == f_x ==> Seq.mem y vl');
 assert (forall y. Seq.mem x blacks \/ y == x ==> Seq.mem y blacks');
 assert (Seq.mem (hd_address f_x) blacks');
 assert (forall y. Seq.mem y blacks \/ y == x <==> Seq.mem y blacks');
 assert (forall y. Seq.mem (hd_address y) blacks \/ (hd_address y) == x <==> Seq.mem (hd_address y) blacks');
 test_helper5 x;
 assert (forall y. (hd_address y) == x ==> (y == (f_address x)));
 assert (forall y. Seq.mem (hd_address y) blacks \/ y == (f_address x) <==> Seq.mem (hd_address y) blacks');
 assert (forall y. Seq.mem (hd_address y) blacks' ==> Seq.mem y vl');
 assert (forall y. Seq.mem (hd_address y) blacks' <==> Seq.mem y vl');
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> Seq.mem y vl');
 ()

#restart-solver

let is_vertex_set_vl_after_insert (g:heap{well_formed_heap2 g})
                                  (vl: seq Usize.t{vl_props_func g vl})
                                  (x: Usize.t{Usize.v x >= 0 /\ Usize.v x < heap_size /\
                                             (Usize.v x % Usize.v mword == 0) /\
                                              is_valid_header1 x g /\
                                              isGrayObject1 x g /\
                                              ~(Seq.mem (f_address x) vl)})


                : Lemma
                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                            (Seq.mem (f_address x) (create_graph_from_heap g).vertices) /\
                            (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
                  (ensures (let grph = create_graph_from_heap g in
                            let f_x = f_address x in
                            let vl' = G.insert_to_vertex_set grph f_x vl in
                            (G.is_vertex_set vl') /\
                            (Seq.mem f_x vl') /\
                            (G.subset_vertices vl' (grph.vertices)))) =
let allocs = get_allocated_block_addresses g in
assert (G.is_vertex_set allocs); // This assert is required
assert (all_field_address_are_word_aligned allocs g);
fieldaddress_within_limits_lemma_x_all g;
let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in
assert (forall y. Seq.mem y allocs <==> Seq.mem (f_address y) ff_allocs);
assert (forall y. Seq.mem y ff_allocs <==> Seq.mem (hd_address y) allocs);
assert (forall y. Seq.mem (hd_address y) allocs ==> Seq.mem y ff_allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) (objects2 0UL g));
assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem (f_address (hd_address y)) ff_allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem y ff_allocs);
let grph = create_graph_from_heap g in
assert (Seq.mem x allocs);
assert (Seq.mem (f_address x) ff_allocs);
assert (Seq.mem (f_address x) grph.vertices);
assert (G.subset_vertices vl (grph.vertices));
let f_x = f_address x in
let vl' = G.insert_to_vertex_set grph f_x vl in
assert (G.is_vertex_set vl');
assert (G.subset_vertices vl' (grph.vertices));
assert (Seq.mem f_x vl');
()

#restart-solver

#restart-solver

let mutual_exclusion_lemma (st: seq Usize.t{G.is_vertex_set st /\  (~(G.is_emptySet st))})
                           (vl: seq Usize.t{G.is_vertex_set vl})

                : Lemma
                  (requires  (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                  (ensures ((forall x. Seq.mem x (Seq.slice st 0 (Seq.length st - 1)) ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x (Seq.slice st 0 (Seq.length st - 1))))))) =
 let s = Seq.slice st 0 (Seq.length st - 1) in
 assert ((forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
         (forall x. Seq.mem x vl ==> ~(Seq.mem x st))));
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Seq.mem x st);
 assert (forall x. Seq.mem x s ==> ~(Seq.mem x vl));
 assert (forall x. Seq.mem x vl ==> ~(Seq.mem x s));
 ()

let mutual_exclusion_lemma1 (g:heap{well_formed_heap2 g
                                   })

                            (x:Usize.t{Seq.mem x (get_allocated_block_addresses g)})

                            (s: seq Usize.t)
                            (vl: seq Usize.t)
                : Lemma
                  (requires
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                             (Seq.mem (f_address x) ((create_graph_from_heap g)).vertices) /\
                             (G.is_vertex_set s /\
                                           G.subset_vertices s (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)) /\
                                            ~(Seq.mem (f_address x) s)) /\
                             (G.is_vertex_set vl /\
                                            G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)) /\
                                             ~(Seq.mem (f_address x) vl)) /\
                             (forall y. Seq.mem y s ==> ~(Seq.mem y vl) /\
                             (forall y. Seq.mem y vl ==> ~(Seq.mem y s))) /\
                             (forall i y.  Seq.mem y (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g y))) ==>
                                                    (Usize.v y  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))

                  (ensures (let grph = create_graph_from_heap g in
                            let f_x = f_address x in
                            let vl' = G.insert_to_vertex_set grph f_x vl in
                            (forall y. Seq.mem y vl' ==> ~(Seq.mem y s)) /\
                            (forall y. Seq.mem y s ==> ~(Seq.mem y vl')))) =
let grph = create_graph_from_heap g in
let f_x = f_address x in
let vl' = G.insert_to_vertex_set grph f_x vl in
G.insert_to_vertex_set_mem_negation_lemma grph f_x vl s;
assert (forall y. Seq.mem y vl' ==> ~(Seq.mem y s));
assert (forall y. Seq.mem y s ==> ~(Seq.mem y vl'));
()

#restart-solver

#restart-solver

#restart-solver

#push-options "--split_queries always"

#restart-solver

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let is_vertex_set_vl_after_insert1 (g:heap{well_formed_heap2 g})
                                   (vl: seq Usize.t {(G.is_vertex_set vl) /\
                                          (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                          (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                          (forall x. Seq.mem x vl ==> is_valid_header1 (hd_address x) g) /\
                                          (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl)
                                                    })
                                    (x: Usize.t{Usize.v x >= Usize.v mword /\ Usize.v x < heap_size /\
                                             (Usize.v x % Usize.v mword == 0) /\
                                              is_valid_header1 (hd_address x) g /\
                                              isGrayObject1 (hd_address x) g /\

                                             ~(Seq.mem x vl)})
                  : Lemma
                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                            (Seq.mem x (create_graph_from_heap g).vertices) /\
                            (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
                  (ensures (let grph = create_graph_from_heap g in
                            let vl' = G.insert_to_vertex_set grph x vl in
                            (G.is_vertex_set vl') /\
                            (Seq.mem x vl') /\
                            (G.subset_vertices vl' (grph.vertices)))) =
 let grph = create_graph_from_heap g in
 //let vl' = G.insert_to_vertex_set grph x vl in
 (*assert ((G.is_vertex_set vl') /\
         (Seq.mem x vl') /\
         (G.subset_vertices vl' (grph.vertices)));*)
 ()

#restart-solver

#restart-solver

#push-options "--split_queries always"

#restart-solver

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

//#push-options "--split_queries always"

let mutual_exclusion_lemma3 (g:heap{well_formed_heap2 g
                                   })

                            (x:Usize.t{ Usize.v x >= Usize.v mword /\ Usize.v x < heap_size /\
                                        (Usize.v x % Usize.v mword == 0) /\
                                        Seq.mem (hd_address x) (get_allocated_block_addresses g)})

                            (s: seq Usize.t)
                            (vl: seq Usize.t)
                : Lemma
                  (requires  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                             (Seq.mem x ((create_graph_from_heap g)).vertices) /\

                             (G.is_vertex_set s /\
                                           G.subset_vertices s (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)) /\
                                            ~(Seq.mem x s)) /\
                             (G.is_vertex_set vl /\
                                            G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)) /\
                                             ~(Seq.mem x vl)) /\
                             (forall y. Seq.mem y s ==> ~(Seq.mem y vl) /\
                             (forall y. Seq.mem y vl ==> ~(Seq.mem y s))) /\
                             (forall i y.  Seq.mem y (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g y))) ==>
                                                    (Usize.v y  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))

                  (ensures (let grph = create_graph_from_heap g in
                            let vl' = G.insert_to_vertex_set grph x vl in
                            (forall y. Seq.mem y vl' ==> ~(Seq.mem y s)) /\
                            (forall y. Seq.mem y s ==> ~(Seq.mem y vl')))) =
let grph = create_graph_from_heap g in
let vl' = G.insert_to_vertex_set grph x vl in
G.insert_to_vertex_set_mem_negation_lemma grph x vl s;
assert (forall y. Seq.mem y vl' ==> ~(Seq.mem y s));
assert (forall y. Seq.mem y s ==> ~(Seq.mem y vl'));
()



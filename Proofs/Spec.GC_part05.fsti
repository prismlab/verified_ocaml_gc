module Spec.GC_part05

include Spec.GC_part04

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

#restart-solver

#reset-options "--z3rlimit 100"

let mark5_body_black_nodes_lemma (g:heap{well_formed_heap2 g}) 
                                 (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0})
                                    
    : Lemma
      (requires color_pre_condition g st)
                                    
      (ensures mark5_body_black_nodes_lemma_post_condition g st) = 
assert (~(G.is_emptySet st));
 non_empty_set_lemma g st;
 let v_id = Seq.index st (Seq.length st - 1) in
 let s = Seq.slice st 0 (Seq.length st - 1) in
 assert (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (Usize.v v_id  >= Usize.v mword);
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
   
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Seq.mem x st);
 G.is_vertex_set_lemma3 st;
 assert (forall x. Seq.mem x s ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 let g' = colorHeader5 h_v_id g black in
 colorHeader5_lemma h_v_id g black;
 assert (g' == colorHeader1 h_v_id g black);
 assert (color_of_object1 h_v_id g' == black);
 colorHeader1_alloc_colors_lemma h_v_id g black;
   
 let f = objects2 0UL g in
 let f' = objects2 0UL g' in
 assert (f == f');
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 Seq.lemma_mem_snoc s v_id;
 assert (forall x. Seq.mem x st <==> (x == v_id) \/ Seq.mem x s);
 assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem (hd_address x) (objects2 0UL g) /\
                                                        isGrayObject1 (hd_address x) g);
 
 assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
 assert (color_of_object1 h_v_id g' == 3UL);
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (forall x. Seq.mem x s <==> Seq.mem (hd_address x) (objects2 0UL g') /\
                                                        isGrayObject1 (hd_address x) g');
 
 let wz = wosize_of_object1 h_v_id g' in
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));
 assert (Usize.v wz == Usize.v (getWosize (read_word g' h_v_id)));
 assert (well_formed_heap2 g');
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                             Seq.mem x s);
 assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size);
 assert (Usize.v h_v_id % Usize.v mword == 0);
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));

 assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
 
 let tg = tag_of_object1 h_v_id g' in
 assert (Usize.v tg <> infix_tag);
 assert (check_well_formed_closure_objs g (get_allocated_block_addresses g));
 assert (stack_props_func g st);
 assert (Seq.mem v_id st);
 assert (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g);
 assert (h_v_id == hd_address v_id);

 colorHeader1_subset_lemma h_v_id g;

 (*always use abstrcations whenever seq lemmas are disabled. is_black_subset is defined before seq leamms disabling*)
 assert (is_black_subset g g');

 colorHeader1_black_nodes_lemma  g h_v_id;

 assert (black_objects_length g g');

 if (Usize.v tg < no_scan_tag) then 
 (
   if (Usize.v tg = closure_tag) then
   (
     assert (Usize.v wz >= 2);
     assert (Usize.v v_id >= Usize.v mword);
     assert (is_valid_header1 h_v_id g);
     assert (is_valid_header (hd_address v_id) g);
    
     let start_env = start_env_clos_info g' v_id in

     assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address v_id) g')) /\
             Usize.v start_env >= 1);

     let start_env_plus_one = Usize.add start_env 1UL in
     let st1, g1 = fieldPush_spec1 g' s h_v_id wz (start_env_plus_one) in
     
     fieldPush_spec1_black_nodes_lemma g' s h_v_id wz start_env_plus_one;
     assert (is_black_subset g' g1);
     assert (black_objects_length g g');
     is_black_subset_lemma g' g1;
     assert (black_objects_length1 g' g1);
     is_black_subset_lemma_trans g g' g1;
     assert (black_objects_length g g1);
     assert (mark5_body_black_nodes_lemma_post_condition g st);
     ()
   )
   else
   (
     let st1, g1 = fieldPush_spec1 g' s h_v_id wz 1UL in
     assert (G.is_vertex_set st1);
     assert (Seq.length g == Seq.length g1);
     fieldPush_spec1_black_nodes_lemma g' s h_v_id wz 1UL;
     assert (is_black_subset g' g1);
     assert (black_objects_length g g');
     is_black_subset_lemma g' g1;
     assert (black_objects_length1 g' g1);
     is_black_subset_lemma_trans g g' g1;
     assert (black_objects_length g g1);
     assert (mark5_body_black_nodes_lemma_post_condition g st);
     ()
   )
   
 )
  else
  (
    assert (is_black_subset g g');
    assert (mark5_body_black_nodes_lemma_post_condition g st);
    ()
  )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

let rec mark5 (g:heap{well_formed_heap2 g}) 
              (st: seq Usize.t {stack_props_func g st })
           : Pure (heap)
            (requires True)
            (ensures (fun g' -> well_formed_heap2 g'))
            (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
if (G.is_emptySet st) then
   (
      g
   )
 else
   (
     let st', g' = mark5_body g st in
     let v_id = Seq.index st (Seq.length st - 1) in
     assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
     assert (is_valid_header (hd_address v_id) g);
     stack_slice_only_has_gray_color_lemma g st v_id 3UL;
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g 3UL)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g 3UL)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)));
      
     mark5_body_black_nodes_lemma g st;
     assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
     
     assert (well_formed_heap2 g');
     assert ((forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g') /\
                                                            (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0) /\
                                                            (G.is_vertex_set st') /\
                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                                   Seq.mem x st'));
     
     mark5 g' st'
   )

let mark_body_mark_body1_lemma (g:heap{well_formed_heap2 g}) 
                               (st: seq Usize.t {stack_props_func g st})
                                    
           : Lemma
             (requires (~(G.is_emptySet st)))
             (ensures mark5_body g st == mark5_body1 g st) =
 ()

let rec mark7 (g:heap{well_formed_heap2 g}) 
              (st: seq Usize.t {stack_props_func g st })
           : Pure (heap)
            (requires True)
            (ensures (fun g' -> well_formed_heap2 g'))
            (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
if (G.is_emptySet st) then
   (
      g
   )
 else
   (
     let st', g' = mark5_body1 g st in
     mark_body_mark_body1_lemma g st;
     let v_id = Seq.index st (Seq.length st - 1) in
     assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
     assert (is_valid_header (hd_address v_id) g);
     stack_slice_only_has_gray_color_lemma g st v_id 3UL;
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g 3UL)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g 3UL)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)));
      
     mark5_body_black_nodes_lemma g st;
     assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
     
     assert (well_formed_heap2 g');
     assert ((forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g') /\
                                                            (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0) /\
                                                            (G.is_vertex_set st') /\
                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                                   Seq.mem x st'));
     
     mark7 g' st'
   )

let mark7_mark_body_lemma (g:heap{well_formed_heap2 g}) 
                         (st: seq Usize.t {stack_props_func g st})
                   : Lemma
                     (requires (~(G.is_emptySet st)))
                     (ensures (mark7 g st == mark7 (snd (mark5_body1 g st)) (fst (mark5_body1 g st)))) = ()                                          
                  
let mark7_mark_body_lemma1 (g:heap{well_formed_heap2 g}) 
                          (st: seq Usize.t {stack_props_func g st})
                    : Lemma
                     (requires ((G.is_emptySet st)))
                     (ensures (mark7 g st == g)) = ()   

#restart-solver 

let rec mark7_mark5_lemma (g:heap{well_formed_heap2 g}) 
                      (st: seq Usize.t {stack_props_func g st})
              : Lemma
                (ensures mark7 g st == mark5 g st)
                (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st])= 
 if (G.is_emptySet st) then
   (
     ()
   )
 else
   (
     let st', g' = mark5_body1 g st in
     mark_body_mark_body1_lemma g st;
     let v_id = Seq.index st (Seq.length st - 1) in
     assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
     assert (is_valid_header (hd_address v_id) g);
     stack_slice_only_has_gray_color_lemma g st v_id 3UL;
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g 3UL)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g 3UL)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)));
      
     mark5_body_black_nodes_lemma g st;
     assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
     
     assert (well_formed_heap2 g');
     assert ((forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g') /\
                                                            (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0) /\
                                                            (G.is_vertex_set st') /\
                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                                   Seq.mem x st'));

     mark7_mark5_lemma g' st';
     ()
   )

let stack_less_than_heap_size_when_one_non_gray_exists (g:heap{well_formed_heap2 g})
                                                        (st:seq Usize.t)
                                                        (x:Usize.t)
                                  : Lemma
                                    (requires  stack_props_func g st /\ (Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g <> gray)))
                                    (ensures (Seq.length st < heap_size)) = 

 assert (Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g <> gray));
 assert (~(Seq.mem (f_address x) st));
 let blocks = objects2 0UL g in
 get_block_address_length_lemma g;
 assert (Seq.length blocks <= heap_size);
 assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) blocks);
 assert (G.is_vertex_set st);
 assert (G.is_vertex_set blocks);
 assert (forall x. Seq.mem x st ==> UInt.fits (Usize.v x - Usize.v mword) Usize.n);
 assert (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g); 
 assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) blocks); 
 assert (G.subset_vertices_variant st blocks);
 G.subset_variant_lemma st blocks;
 assert (Seq.length st <= Seq.length blocks);
 assert (Seq.length st <= heap_size);
 if Seq.length st < heap_size then ()
 else
   (
     assert (Seq.length st == heap_size);
     assert (Seq.length st == Seq.length blocks);
     assert  (forall x. Seq.mem x st ==> Seq.mem (hd_address x) blocks);
     assert (forall x. Seq.mem x st ==> is_hp_addr x);
     G.subset_of_each_other1 st blocks;
     assert (forall x. Seq.mem x blocks ==> Seq.mem (f_address x) st);
     assert (Seq.mem (f_address x) st);
     ()
   )     

#restart-solver

let fieldPush_fieldPush_spec_body_lemma (g:heap{well_formed_heap2 g})
                                        (st: seq Usize.t{stack_props_func g st})
                                        (h_index:hp_addr{is_valid_header1 h_index g})
                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                        (i':Usize.t{Usize.v i' == Usize.v i + 1})
                          : Lemma
                         (requires True)
                         (ensures (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                                                        (fst (fieldPush_spec_body1 g st h_index wz i))
                                                                                        h_index 
                                                                                        wz
                                                                                        i')) = ()             
                                       
let fieldPush_fieldPush_spec_body_lemma1 (g:heap{well_formed_heap2 g})
                                          (st: seq Usize.t{stack_props_func g st})
                                          (h_index:hp_addr{is_valid_header1 h_index g})
                                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                                          (i:Usize.t)
                         : Lemma
                         (requires (Usize.v i == Usize.v wz + 1))
                         (ensures g == snd (fieldPush_spec1 g st h_index wz i) /\
                                  st == fst (fieldPush_spec1 g st h_index wz i)) = ()  

let slice_coloring_lemma1 (g:heap{well_formed_heap2 g}) 
                          (g':heap{well_formed_heap2 g'}) 
                          (v_id: hp_addr{is_valid_header1 v_id g /\
                                      is_valid_header1 v_id g'})
                          (s: seq Usize.t)
                          (s_top:Usize.t{Usize.v s_top <= Seq.length s}) 
         : Lemma
              (requires ((G.is_vertex_set (Seq.slice s 0 (Usize.v s_top))) /\
                        (~(Seq.mem (f_address v_id) (Seq.slice s 0 (Usize.v s_top)))) /\
                         (color_of_object1 v_id g' == black) /\
                         (heap_remains_same_except_index_v_id v_id g g') /\
                        ((objects2 0UL g ==
                             objects2 0UL g')) /\
                         (get_allocated_block_addresses g == 
                              get_allocated_block_addresses g') /\
                         
                         (color_of_object1 v_id g == gray) /\
                         (forall y. Seq.mem y (Seq.slice s 0 (Usize.v s_top)) \/
                          (y == (f_address v_id)) <==> Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g)))
              (ensures ((forall y. Seq.mem y (Seq.slice s 0 (Usize.v s_top)) <==>
                             Seq.mem (hd_address y) (objects2 0UL g') /\ isGrayObject1 (hd_address y) g'))) = () 

#restart-solver

#restart-solver

let mark5_body_fieldPush_lemma (g:heap{well_formed_heap2 g}) 
                               (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0  })
                               (v_id:hp_addr{v_id == Seq.index st (Seq.length st - 1) /\ is_valid_header1 (hd_address v_id) g})
                               
                               (g': heap{g' == colorHeader1 (hd_address v_id) g black})
                               (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                               (wz:wosize{wz == wosize_of_object1 (hd_address v_id) g})   
                   : Lemma
                   (requires well_formed_heap2 g' /\
                             (stack_props_func g' s) /\
                             (Usize.v v_id >= Usize.v mword /\ Usize.v v_id < heap_size) /\
                              is_valid_header1 (hd_address v_id) g' /\
                              (Usize.v (tag_of_object1 (hd_address v_id) g') < no_scan_tag) /\
                              (Usize.v  (tag_of_object1 (hd_address v_id) g') <> closure_tag))
                                                  
                   (ensures fst (mark5_body g st) == fst (fieldPush_spec1 g' s (hd_address v_id) wz 1UL) /\
                            snd (mark5_body g st) == snd (fieldPush_spec1 g' s (hd_address v_id) wz 1UL)) = ()    

let mark5_body_fieldPush_lemma1 (g:heap{well_formed_heap2 g}) 
                               (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0  })
                               (v_id:hp_addr{v_id == Seq.index st (Seq.length st - 1) /\ is_valid_header1 (hd_address v_id) g})
                               
                               (g': heap{g' == colorHeader1 (hd_address v_id) g black})
                               (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                               (wz:wosize{wz == wosize_of_object1 (hd_address v_id) g})   
                   : Lemma
                   (requires well_formed_heap2 g' /\
                             (stack_props_func g' s) /\
                             (Usize.v v_id >= Usize.v mword /\ Usize.v v_id < heap_size) /\
                              is_valid_header1 (hd_address v_id) g' /\
                              Usize.v (tag_of_object1 (hd_address v_id) g') >= no_scan_tag)
                                                  
                   (ensures fst (mark5_body g st) == s /\
                            snd (mark5_body g st) == g') = ()                               

#restart-solver 

#restart-solver

let mark5_body_fieldPush_lemma2 (g:heap{well_formed_heap2 g}) 
                               (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0})
                               (v_id:hp_addr{(v_id == Seq.index st (Seq.length st - 1)) /\ (is_valid_header1 (hd_address v_id) g)})
                               
                               (g': heap{g' == colorHeader1 (hd_address v_id) g black})
                               (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                               (wz:wosize{wz == wosize_of_object1 (hd_address v_id) g})   
                   : Lemma
                   (requires well_formed_heap2 g' /\
                             (stack_props_func g' s) /\
                             (Usize.v v_id >= Usize.v mword /\ Usize.v v_id < heap_size) /\
                              (is_valid_header1 (hd_address v_id) g') /\
                              (Usize.v (tag_of_object1 (hd_address v_id) g') < no_scan_tag) /\
                              (Usize.v  (tag_of_object1 (hd_address v_id) g') == closure_tag) /\
                              (Usize.v wz >= 2))
                                                  
                   (ensures (fst (mark5_body g st) == fst (fieldPush_spec1 g' s (hd_address v_id) wz (Usize.add (start_env_clos_info g' v_id) 1UL))) /\
                            (snd (mark5_body g st) == snd (fieldPush_spec1 g' s (hd_address v_id) wz (Usize.add (start_env_clos_info g' v_id) 1UL)))) = ()

let mark_mark_body_lemma (g:heap{well_formed_heap2 g}) 
                         (st: seq Usize.t {stack_props_func g st})
                   : Lemma
                     (requires (~(G.is_emptySet st)))
                     (ensures (mark5 g st == mark5 (snd (mark5_body g st)) (fst (mark5_body g st)))) = () 

let mark_mark_body_lemma1 (g:heap{well_formed_heap2 g}) 
                          (st: seq Usize.t {stack_props_func g st})
                    : Lemma
                     (requires ((G.is_emptySet st)))
                     (ensures (mark5 g st == g)) = ()    


#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

/// ---------------------------------------------------------------------------------------------------------------------------------------------------
/// Graph Construction. The successors for an object with no_scan_tag should be empty. Also incorporate how to deal with closure plus infix objects 
/// ---------------------------------------------------------------------------------------------------------------------------------------------------

let valid_wosize (g:heap{well_formed_heap2 g}) 

                 (h_index:hp_addr{is_valid_header1 h_index g})
                 (wz: wosize) =
  (wz == getWosize (read_word g h_index)) /\ 
  is_fields_within_limit1 h_index wz /\
  is_fields_contents_within_limit2 h_index wz g /\
  (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)

#restart-solver 

let rec create_successors_list_for_h_index (g:heap{well_formed_heap2 g}) 

                                           (h_index:hp_addr{is_valid_header1  h_index g})
                                         
                                           (wz: wosize{valid_wosize g h_index wz})
                         
                                           (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})                 
                                           
                               : Tot (seq Usize.t) 
                         
                                 (decreases ((Usize.v wz + 1) - Usize.v i)) = 
if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
       
       s_list
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

           s_list
         )
         else
         (
           
           lemma_tl succ s_list'; 
        
           let s_list = Seq.cons succ s_list' in 
        
           assert (Seq.head s_list == succ);

           s_list
         )
      )
      else
      (
       
        s_list'
      )
    )

let create_successors_list_for_h_index_base_lemma (g:heap{well_formed_heap2 g}) 

                                                      (h_index:hp_addr{is_valid_header1 h_index g})
                                         
                                                      (wz: wosize{valid_wosize g h_index wz})
                         
                                                      (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})                 
                                      : Lemma
                                        (ensures (Usize.v i == Usize.v wz + 1 ==> create_successors_list_for_h_index g h_index wz i == Seq.empty)) = ()

#restart-solver

#restart-solver

#restart-solver              

let f_address_hp_address_lemma (h_index: hp_addr{UInt.fits (Usize.v h_index + Usize.v mword) Usize.n /\ (Usize.v h_index + Usize.v mword < heap_size)})
                         : Lemma (hd_address (f_address h_index) == h_index) = ()

#restart-solver 

#restart-solver

#restart-solver

let cons_property_lemma3 (g:heap{well_formed_heap2 g}) 

                         (h_index:hp_addr{is_valid_header1 h_index g})
                          (s:seq G.edge{(forall p q. Seq.mem (p,q) s ==> is_hp_addr p /\ (UInt.fits (Usize.v p - Usize.v mword) Usize.n) /\
                                                            is_hp_addr q /\ (UInt.fits (Usize.v q - Usize.v mword) Usize.n) /\
                                                            Seq.mem (hd_address p) (get_allocated_block_addresses g) /\
                                                            Seq.mem (hd_address q) (get_allocated_block_addresses g)) /\
                                        (forall p q. Seq.mem (p,q) s ==> hd_address p == h_index)})
                         
                          (s_cons:G.edge{is_hp_addr (fst s_cons) /\ (UInt.fits (Usize.v (fst s_cons) - Usize.v mword) Usize.n) /\
                                        is_hp_addr (snd s_cons) /\ (UInt.fits (Usize.v (snd s_cons) - Usize.v mword) Usize.n) /\
                                       Seq.mem (hd_address (fst s_cons)) (get_allocated_block_addresses g) /\
                                       Seq.mem (hd_address (snd s_cons)) (get_allocated_block_addresses g) /\
                                       hd_address (fst s_cons) == h_index})
                 : Lemma
                   (ensures (forall x y. Seq.mem (x,y) (Seq.cons s_cons s) ==>  is_hp_addr x /\ (UInt.fits (Usize.v x - Usize.v mword) Usize.n) /\
                                                                           is_hp_addr y /\ (UInt.fits (Usize.v y - Usize.v mword) Usize.n) /\
                                                                           Seq.mem (hd_address x) (get_allocated_block_addresses g) /\
                                                                           Seq.mem (hd_address y) (get_allocated_block_addresses g)) /\
                            (forall x y. Seq.mem (x,y) (Seq.cons s_cons s) ==> hd_address x == h_index)) = 
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 ()

let cons_property_lemma5 (g:heap{well_formed_heap2 g}) 

                         (h_index:hp_addr{is_valid_header1 h_index g})
                         (s:seq G.edge{(forall (p:G.edge). Seq.mem p s ==> is_hp_addr (fst p) /\ (UInt.fits (Usize.v (fst p) - Usize.v mword) Usize.n) /\
                                                            is_hp_addr (snd p) /\ (UInt.fits (Usize.v (snd p) - Usize.v mword) Usize.n) /\
                                                            Seq.mem (hd_address (fst p)) (get_allocated_block_addresses g) /\
                                                            Seq.mem (hd_address (snd p)) (get_allocated_block_addresses g)) /\
                                        (forall (p:G.edge). Seq.mem p s ==> hd_address (fst p) == h_index) /\
                                        (forall (p:G.edge). Seq.mem p s ==> (fst p) == f_address h_index)})
                         
                         (s_cons:G.edge{is_hp_addr (fst s_cons) /\ (UInt.fits (Usize.v (fst s_cons) - Usize.v mword) Usize.n) /\
                                        is_hp_addr (snd s_cons) /\ (UInt.fits (Usize.v (snd s_cons) - Usize.v mword) Usize.n) /\
                                       Seq.mem (hd_address (fst s_cons)) (get_allocated_block_addresses g) /\
                                       Seq.mem (hd_address (snd s_cons)) (get_allocated_block_addresses g) /\
                                       hd_address (fst s_cons) == h_index /\
                                       fst s_cons == f_address h_index})
                 : Lemma
                   (ensures (forall (x:G.edge). Seq.mem x (Seq.cons s_cons s) ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                           is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                           Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                           Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                            (forall (x:G.edge). Seq.mem x (Seq.cons s_cons s) ==> hd_address (fst x) == h_index) /\
                            (forall (x:G.edge). Seq.mem x (Seq.cons s_cons s) ==> (fst x) == f_address h_index)) = 
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 ()

#restart-solver

#restart-solver

#restart-solver

let rec create_edge_pairs_for_h_index (g:heap{well_formed_heap2 g}) 

                                      (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                      (wz: wosize{valid_wosize g h_index wz})
                         
                                      (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                       : Tot (f':seq (G.edge) {
                       
                                               (forall (x:G.edge). Seq.mem x f' ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                                is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                                Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                                Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                                               (forall (x:G.edge). Seq.mem x f' ==> hd_address (fst x) == h_index) /\
                                               (forall (x:G.edge). Seq.mem x f' ==> (fst x) == f_address h_index)}) 
                        (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let e = Seq.empty #G.edge in
       assert (Seq.length e == 0);
       assert ((Seq.length e == (Usize.v wz + 1) - Usize.v i));
       e
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
        
      let e' = create_edge_pairs_for_h_index g h_index wz i' in
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
        
           e
         )
         else
         (

           let edge_pair = (f_index,succ) in
           assert (hd_address (fst edge_pair) == h_index);
           assert (fst edge_pair == f_index);
           assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
           assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
           lemma_tl edge_pair e'; 
        
           let e = Seq.cons edge_pair e' in 
           cons_property_lemma5 g h_index e' edge_pair;
           e
         )
      )
      else
      (
        e'
      )
    )

#restart-solver

#restart-solver                      

let rec create_edge_pairs_for_h_index_length_lemma (g:heap{well_formed_heap2 g}) 

                                                   (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                   (wz: wosize{valid_wosize g h_index wz})
                         
                                                   (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                               : Lemma
                                 (ensures (Seq.length (create_edge_pairs_for_h_index g h_index wz i) <= (Usize.v wz + 1) - Usize.v i))
                                 (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 if Usize.v i = Usize.v wz + 1 then
    (
       let e = Seq.empty #G.edge in
       assert (Seq.length e == 0);
       assert ((Seq.length e == (Usize.v wz + 1) - Usize.v i));
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
        
      let e' = create_edge_pairs_for_h_index g h_index wz i' in
      create_edge_pairs_for_h_index_length_lemma g h_index wz i';
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
        
           ()
         )
         else
         (

           let edge_pair = (f_index,succ) in
           assert (hd_address (fst edge_pair) == h_index);
           assert (fst edge_pair == f_index);
           assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
           assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
           lemma_tl edge_pair e'; 
        
           let e = Seq.cons edge_pair e' in 
           cons_property_lemma5 g h_index e' edge_pair;
           ()
         )
      )
      else
      (
        ()
      )
    )



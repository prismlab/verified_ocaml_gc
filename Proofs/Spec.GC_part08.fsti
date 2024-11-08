module Spec.GC_part08

include Spec.GC_part07

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


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver 

let graph_successors_heap_create_successor_list_equivalence_lemma (g: heap {well_formed_heap2 g})
                                                                  (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g})
                                : Lemma
                                  (requires succ_props_pre g h_index)
                                  
                                  (ensures  succ_props g h_index) = 
 let allocs = get_allocated_block_addresses g in
 assert (G.is_vertex_set allocs);
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 let grph = create_graph_from_heap g in
 let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in 
 assert (Seq.equal (grph.vertices) ff_allocs);
 assert (forall x. Seq.mem x allocs <==> Seq.mem (f_address x) ff_allocs);
 assert (Seq.mem (f_address h_index) (ff_allocs));
 let f_h_index = f_address h_index in 
 G.successors_successors_fn2_connect_lemma grph f_h_index; 
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index grph.edge_set);
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_for_graph g));
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs));
 assert (Seq.mem h_index allocs); 
 let tg = tag_of_object1 h_index g in
 assert (edge_graph_succ_connect3 g allocs (create_edge_list_from_heap1 g allocs));
 if (Usize.v tg < no_scan_tag) then 
 (
   f_address_hp_address_lemma h_index;
   assert (hd_address f_h_index == h_index);
   if (Usize.v tg = closure_tag) then
    (
      let start_env = start_env_clos_info g f_h_index in
      let start_of_env_plus_one = Usize.add start_env 1UL in
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one in 
      
      assert (G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs) ==  G.successors_fn2 f_h_index h_index_edge_list);
                                          
      assert (G.successors grph f_h_index == G.successors_fn2 f_h_index h_index_edge_list);
      G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;

      assert (G.successors_fn2 f_h_index h_index_edge_list ==
              G.pick_second h_index_edge_list);
      create_successors_pick_second_lemma g h_index (getWosize (read_word g h_index)) start_of_env_plus_one;
      
      assert (G.pick_second h_index_edge_list == 
           create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one);
      
      assert (G.successors_fn2 f_h_index h_index_edge_list ==
             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one);
      
      assert (G.successors grph f_h_index ==  
             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one);
      
      assert (G.successors (create_graph_from_heap g) f_h_index == 
              create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one);
      assert (succ_props g h_index);
      ()
    )
    else
    (
      
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL in 
      
      assert (G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs) ==  G.successors_fn2 f_h_index h_index_edge_list);
                                          
      assert (G.successors grph f_h_index == G.successors_fn2 f_h_index h_index_edge_list);
      G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;

      assert (G.successors_fn2 f_h_index h_index_edge_list ==
              G.pick_second h_index_edge_list);
      create_successors_pick_second_lemma g h_index (getWosize (read_word g h_index)) 1UL;
      
      assert (G.pick_second h_index_edge_list == 
           create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
      
      assert (G.successors_fn2 f_h_index h_index_edge_list ==
             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
      
      assert (G.successors grph f_h_index ==  
             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
      
      assert (G.successors (create_graph_from_heap g) f_h_index == 
              create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
      assert (succ_props g h_index);
      ()
    )
      
 )
 else
 (
   assert ( G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs) ==  Seq.empty #UInt64.t);
   assert (G.successors grph f_h_index == Seq.empty #UInt64.t);
   assert (Usize.v (tag_of_object1 h_index g) >= no_scan_tag ==> 
                                                   G.successors (create_graph_from_heap g) (f_address h_index) == Seq.empty #UInt64.t);
   ()
 )

#reset-options "--z3rlimit 500"
#push-options "--split_queries always"


let is_visited   (v_id:hp_addr)
                 (g:heap)
          : Tot (b:bool{b == true <==>  (color_of_object1 v_id g) == black}) =
    if  (color_of_object1 v_id g) = black then true else false

let unvisited  (v_id:hp_addr)
               (g:heap{color_of_object1 v_id g == white \/
                       color_of_object1 v_id g == gray \/
                       color_of_object1 v_id g == black})
         : Tot (b:bool{(b == true <==> (~(is_visited v_id g) /\ ~(isGrayObject1 v_id g))) /\
                        (b == true <==> color_of_object1 v_id g == white)}) =
 if not(is_visited v_id g) && not(isGrayObject1 v_id g) then true
 else
  false 

let unvisited_lemma  (v_id:hp_addr)
                     (g:heap{color_of_object1 v_id g == white \/
                             color_of_object1 v_id g == gray \/
                             color_of_object1 v_id g == black})
            : Lemma
              (requires (color_of_object1 v_id g == gray \/
                         color_of_object1 v_id g == black))
              (ensures (color_of_object1 v_id g <> white)) = () 

let push_to_stack2_lemma_block_address (g:heap{well_formed_heap2 g})
                                       (st: seq Usize.t {stack_props_func g st})
                                       (x: hp_addr{is_valid_header1 x g /\
                                                   ~(Seq.mem (f_address x) st) /\
                                                  (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                  })  
                    : Lemma
                     (ensures (objects2 0UL g == objects2 0UL (snd (push_to_stack2 g st x)))) =
if Seq.length st = 0 then
(
   assert (Usize.v (tag_of_object1 x g) <> infix_tag);
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
   assert (Usize.v (tag_of_object1 x g') <> infix_tag);
   assert (Usize.v (tag_of_object1 (hd_address f_x) g') <> infix_tag);
   assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
   
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   ()
)
    
else
(
  assert (Usize.v (tag_of_object1 x g) <> infix_tag);
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
  assert (Usize.v (tag_of_object1 x g') <> infix_tag);
  assert (Usize.v (tag_of_object1 (hd_address f_x) g') <> infix_tag);
  assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  ()
)         

let push_to_stack2_lemma_valid_header (g:heap{well_formed_heap2 g})
                                      (st: seq Usize.t {stack_props_func g st})
                                      (x: hp_addr{is_valid_header1 x g /\
                                                   ~(Seq.mem (f_address x) st) /\
                                                  (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                  })
                   : Lemma
                     (ensures (forall y. is_valid_header1 y g ==> is_valid_header1 y (snd (push_to_stack2 g st x)))) =
  push_to_stack2_lemma_block_address g st x;
  ()

#restart-solver 

#restart-solver

let text_vl_props (g:heap{well_formed_heap2 g})
                  (vl: seq Usize.t {vl_props_func g vl}) =
 assert (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g);
 assert (forall x. Seq.mem x vl ==> is_valid_header1 (hd_address x) g);
 ()

#restart-solver

#restart-solver

let push_to_stack2_visited_list_valid_header_lemma  (g:heap{well_formed_heap2 g})
                                                    (st: seq Usize.t {stack_props_func g st})
                                                    (x: hp_addr{is_valid_header1 x g /\
                                                                ~(Seq.mem (f_address x) st) /\
                                                                (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                               })
                                                    (vl: seq Usize.t {vl_props_func g vl }) 
                        : Lemma
                          (ensures (forall y. Seq.mem y vl ==> is_valid_header1 (hd_address y) (snd (push_to_stack2 g st x)))) = 
 push_to_stack2_lemma_valid_header g st x; 
 ()

#restart-solver

#restart-solver
let push_to_stack2_lemma_gray_nodes_helper (g:heap{well_formed_heap2 g})
                                           (st: seq Usize.t {stack_props_func g st})
                                           (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st) /\
                                                (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                               })
                                           (y:hp_addr {is_valid_header1 y g /\ isGrayObject1 y g /\ x <> y})
                                      
                     : Lemma
                       (ensures is_valid_header1 y (snd (push_to_stack2 g st x)) /\ isGrayObject1 y (snd (push_to_stack2 g st x))) =
 if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
   assert (is_valid_header1 y g /\ isGrayObject1 y g /\ x <> y);
   assert (is_valid_header1 y g');
   assert (isGrayObject1 y g');
   assert (g' == snd (push_to_stack2 g st x));
   assert (isGrayObject1 y (snd (push_to_stack2 g st x)));
   assert (is_valid_header1 y (snd (push_to_stack2 g st x)));
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
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  assert (is_valid_header1 y g /\ isGrayObject1 y g /\ x <> y);
  assert (is_valid_header1 y g');
  assert (isGrayObject1 y g');
  assert (g' == snd (push_to_stack2 g st x));
  assert (isGrayObject1 y (snd (push_to_stack2 g st x)));
  assert (is_valid_header1 y (snd (push_to_stack2 g st x)));
  ()
)

let push_to_stack2_lemma_gray_nodes (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t {stack_props_func g st})
                                    (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st) /\
                                                (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                               })
                     : Lemma
                     (ensures (forall y. is_valid_header1 y g /\ isGrayObject1 y g /\ x <> y ==> is_valid_header1 y (snd (push_to_stack2 g st x)) /\
                                                                                      isGrayObject1 y (snd (push_to_stack2 g st x)))) = 
Classical.forall_intro (Classical.move_requires (push_to_stack2_lemma_gray_nodes_helper  g st x))

#restart-solver 

#reset-options "--z3rlimit 500" 

#push-options "--split_queries always"

#restart-solver

let colorHeader1_fields_lemma  (v_id:hp_addr)  
                              
                               (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                               (c:color)
             : Lemma 
               (ensures    (*header coloring does not change wosize*)
                           (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word (colorHeader1 v_id g c) x)) /\

                           (*header coloring does not change field values*)
                           (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word (colorHeader1 v_id g c) y)) = 
 let wz = getWosize (read_word g v_id) in
 let tg = getTag (read_word g v_id) in  
 let h = makeHeader wz c tg in
 assert (wz == getWosize h);
 assert (c == getColor h);
 assert (tg == getTag h);
 assert (Usize.v v_id >= 0);
 assert (Usize.v v_id < heap_size);
 assert (Usize.v v_id < Seq.length g);
 assert (well_formed_heap2 g);
 let h_index = v_id in
 assert (Seq.mem h_index (objects2 0UL g));
 assert (Seq.length (objects2 0UL g) > 0);

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 assert (forall (x:hp_addr). x <> h_index ==> read_word g x == read_word g' x);
 assert (heap_remains_same_except_index_v_id h_index g g');
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). x <> h_index ==> getWosize (read_word g x) == getWosize (read_word g' x));
 assert (getWosize (read_word g h_index) == getWosize (read_word g' h_index));
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x));
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.mem v_id (objects2 0UL g'));
 
 assert (is_fields_contents_within_limit2 v_id wz g);
 
 
 assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> v_id ==>
                             read_word g x == read_word g' x);


 field_reads_all_equal_for_all_objects_lemma g g' h_index;
 field_reads_all_equal_h_index_lemma g g' h_index;
 assert ((forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y));
 ()

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000"

#restart-solver

let push_to_stack2_fields_allocated_blocks_lemma (g:heap{well_formed_heap2 g})
                                                 (st: seq Usize.t {stack_props_func g st})
                                                 (x: hp_addr{is_valid_header1 x g /\
                                                              ~(Seq.mem (f_address x) st) /\
                                                             (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                             ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                                             })
            : Lemma
              (ensures (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g t) == 
                                                                                   getWosize (read_word (snd (push_to_stack2 g st x)) t)) /\

                           (*header coloring does not change field values*)
                           (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (push_to_stack2 g st x)) y)) =
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
   colorHeader1_fields_lemma x g gray;
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
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  colorHeader1_fields_lemma x g gray;
  ()
)

#restart-solver

#restart-solver

let seq_not_empty_lemma (#a:eqtype)
                        (s:seq a) 
           : Lemma
             (requires ~(Seq.length s = 0))
             (ensures Seq.length s > 0) =
()

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver 

let is_valid_header_color_lemma (g:heap{well_formed_heap2 g})
                                (y:hp_addr{(is_valid_header y g)})
                 : Lemma
                   (requires (color_of_object1 y g == black \/ color_of_object1 y g == gray \/ color_of_object1 y g == white))
                   (ensures (is_valid_header1 y g)) =
()
                                                                               
#push-options "--split_queries always"

#restart-solver 

let push_to_stack2_lemma_black_nodes_helper (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t {stack_props_func g st})
                                     (x: hp_addr{is_valid_header1 x g /\
                                                              ~(Seq.mem (f_address x) st) /\
                                                             (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                             ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                                             })
                                     (y:hp_addr {is_valid_header1 y g /\ isBlackObject1 y g /\ x <> y})
                     : Lemma
                       (ensures (is_valid_header1 y (snd (push_to_stack2 g st x)) /\ isBlackObject1 y (snd (push_to_stack2 g st x)))) =
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
   assert (is_valid_header1 y g /\ isBlackObject1 y g /\ x <> y);
   colorHeader1_alloc_colors_lemma x g gray;
   assert (heap_remains_same_except_index_v_id x g g');
   assert (color_of_object1 y g' == black);
   assert (isBlackObject1 y g');
   assert (is_valid_header y g);
   assert (is_valid_header y g');
   is_valid_header_color_lemma g' y;
   assert (is_valid_header1 y g');
   assert (g' == snd (push_to_stack2 g st x));
   assert (is_valid_header1 y g' /\ isBlackObject1 y g');
   ()
)
    
else
(
  seq_not_empty_lemma st;
  assert (Seq.length st > 0);
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  get_allocated_block_addresses_lemma g g' x 2UL;
  assert (heap_remains_same_except_index_v_id x g g');
  assert (color_of_object1 y g' == black);
  assert (isBlackObject1 y g');
  assert (is_valid_header y g);
  assert (is_valid_header y g');
  is_valid_header_color_lemma g' y;
  assert (is_valid_header1 y g');
  assert (g' == snd (push_to_stack2 g st x));
  assert (is_valid_header1 y g' /\ isBlackObject1 y g');
  ()
)


let push_to_stack2_lemma_black_nodes (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t {stack_props_func g st})
                                     (x: hp_addr{is_valid_header1 x g /\
                                                              ~(Seq.mem (f_address x) st) /\
                                                             (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                             ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                                             })
                   : Lemma
                     (ensures (forall y. is_valid_header1 y g /\ isBlackObject1 y g /\ x <> y ==> 
                                    is_valid_header1 y (snd (push_to_stack2 g st x)) /\ isBlackObject1 y (snd (push_to_stack2 g st x)))) =
Classical.forall_intro (Classical.move_requires (push_to_stack2_lemma_black_nodes_helper g st x))

#restart-solver 

#restart-solver

#push-options "--z3rlimit 500"

#push-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 4" 


#restart-solver

let colorHeader1_mem_lemma (v_id:hp_addr)  
                           (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g})
                 : Lemma 
                   (ensures (~(exists y. (Seq.mem y (objects2 0UL (colorHeader1 v_id g black)) /\
                                     isBlackObject1 y (colorHeader1 v_id g black)) /\
                                   ~(Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g) /\
                                    (v_id <> y)))) = 
 let g' = colorHeader1 v_id g black in
 colorHeader1_subset_lemma v_id g;
 assert (~(exists y. (Seq.mem y (objects2 0UL (colorHeader1 v_id g black)) /\
                                     isBlackObject1 y (colorHeader1 v_id g black)) /\
                                   ~(Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g) /\
                                    (v_id <> y)));
 ()

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver


let colorHeader1_mem_lemma_gray (v_id:hp_addr{ (Usize.v v_id >= 0 /\ Usize.v v_id < heap_size) /\
                                               (Usize.v v_id % Usize.v mword == 0)})  
                                (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g /\ (color_of_object1 v_id g == white) /\
                                        (is_fields_within_limit1 v_id (getWosize (read_word g v_id)))})
                 : Lemma 
                   (ensures (~(exists y. (Seq.mem y (get_black_block_addresses (colorHeader1 v_id g gray) 
                                                  (get_allocated_block_addresses (colorHeader1 v_id g gray)))) /\
                                    ~(Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)))))) = 
let g' = colorHeader1 v_id g gray in
//assert (well_formed_heap2 g');
    
 objects2_equal_lemma 0UL g g';
    
 colorHeader1_color_Lemma v_id g 2UL;

 (*assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id v_id g g' /\
                                      color_of_object1 v_id g' == 2UL /\
                                      (color_of_object1 v_id g == white \/ color_of_object1 v_id g == gray \/ 
                                      color_of_object1 v_id g == black) /\
                                      wosize_of_object1 v_id g' == wosize_of_object1 v_id g /\
                                      tag_of_object1 v_id g' == tag_of_object1 v_id g /\
                                      is_valid_header v_id g /\ is_valid_header v_id g');*)
    
 get_allocated_block_addresses_lemma g g' v_id 2UL;

 assert ((get_allocated_block_addresses g) == (get_allocated_block_addresses g'));
 let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
 let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
 
 assert (color_of_object1 v_id g <> black);
 assert (color_of_object1 v_id g' <> black);
 
 assert (G.subset_vertices blacks blacks');
 assert (~(exists y. (Seq.mem y blacks') /\ ~(Seq.mem y blacks)));
 ()
 
#restart-solver 

#restart-solver

#restart-solver

let push_to_stack2_mem_lemma_black_nodes (g:heap{well_formed_heap2 g})
                                         (st: seq Usize.t {stack_props_func g st})
                                         (x: hp_addr{is_valid_header1 x g /\
                                                              ~(Seq.mem (f_address x) st) /\
                                                             (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                             ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                             (is_fields_within_limit1 x (getWosize (read_word g x)))}) 
                                    
                     : Lemma 
                     (ensures (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                               Seq.mem y (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x)))))) = 
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
   colorHeader1_color_Lemma x g 2UL;

   (*assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id x g g' /\
                                      color_of_object1 x g' == 2UL /\
                                      (color_of_object1 x g == white \/ color_of_object1 x g == gray \/ 
                                      color_of_object1 x g == black) /\
                                      wosize_of_object1 x g' == wosize_of_object1 x g /\
                                      tag_of_object1 x g' == tag_of_object1 x g /\
                                      is_valid_header x g /\ is_valid_header x g');*)
    
    get_allocated_block_addresses_lemma g g' x 2UL;
    
    let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
    let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
   
    G.is_vertex_set_lemma2 stk';
    assert (color_of_object1 x g == white);
    assert (color_of_object1 x g <> black);
    assert (color_of_object1 x g' <> black);
    assert (heap_remains_same_except_index_v_id x g g');
    assert (forall y. Seq.mem y blacks ==> Seq.mem y blacks');
    assert (G.subset_vertices blacks blacks');
    
    
    colorHeader1_mem_lemma_gray x g;
    assert (~(exists y. (Seq.mem y blacks') /\ ~(Seq.mem y blacks)));
    assert (forall y. Seq.mem y blacks' <==> Seq.mem y blacks);
    assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g');
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
  
  assert (objects2 0UL g == objects2 0UL g');
  
  colorHeader1_color_Lemma x g 2UL;
  get_allocated_block_addresses_lemma g g' x 2UL;
  
  
  let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
  let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
 
  assert (heap_remains_same_except_index_v_id x g g');
  
  colorHeader1_mem_lemma_gray x g;
  assert (~(exists y. (Seq.mem y blacks') /\ ~(Seq.mem y blacks)));
  assert (forall y. Seq.mem y blacks' <==> Seq.mem y blacks);
  assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g');
  ()
 )

#restart-solver

#restart-solver

#restart-solver

#restart-solver

let push_to_stack2_mem_lemma_black_nodes_for_visited_list (g:heap{well_formed_heap2 g})
                                                          (st: seq Usize.t {stack_props_func g st})
                                                          (x: hp_addr{is_valid_header1 x g /\
                                                                       ~(Seq.mem (f_address x) st) /\
                                                                       (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                                       ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (is_fields_within_limit1 x (getWosize (read_word g x)))}) 
                   : Lemma 
                     (ensures (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==> 
                                       Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y (snd (push_to_stack2 g st x)))) = 

push_to_stack2_mem_lemma_black_nodes g st x;
let st1,g1 = push_to_stack2 g st x in
assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                               Seq.mem y (get_black_block_addresses g1 (get_allocated_block_addresses g1)));
assert (forall x. Seq.mem x (get_black_block_addresses g (get_allocated_block_addresses g)) <==> Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g);
assert (forall x. Seq.mem x (get_black_block_addresses g1 (get_allocated_block_addresses g1)) <==> Seq.mem x (objects2 0UL g1) /\ isBlackObject1 x g1);
assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>  Seq.mem x (get_black_block_addresses g1 (get_allocated_block_addresses g1)));
assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>  Seq.mem x (objects2 0UL g1) /\ isBlackObject1 x g1);                                                  
assert (g1 == snd (push_to_stack2 g st x));                                                              
assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  
                                         Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y g1);

assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  
                                         Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y (snd (push_to_stack2 g st x)));                            
()

let push_to_stack_mem_lemma_black_nodes_visited_list_lemma (g:heap{well_formed_heap2 g})
                                                           (st: seq Usize.t {stack_props_func g st})
                                                           (x: hp_addr{is_valid_header1 x g /\
                                                                       ~(Seq.mem (f_address x) st) /\
                                                                       (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                                       ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))}) 
                                                           (vl: seq Usize.t {vl_props_func g vl})
                                    
                                    
                                : Lemma
                                  (ensures (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                            isBlackObject1 (hd_address y) (snd (push_to_stack2 g st x)) <==>  
                                                   Seq.mem y vl)) =
 assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl));
 push_to_stack2_mem_lemma_black_nodes_for_visited_list  g st x;
 assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                                       isBlackObject1 y (snd (push_to_stack2 g st x)));  
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                                       isBlackObject1 (hd_address y) (snd (push_to_stack2 g st x)) <==> Seq.mem y vl);
                                                                        
 ()

#restart-solver

#restart-solver

let push_to_stack_heap_and_push_to_graph_equality_lemma1 (g:heap{well_formed_heap2 g})
                                                         (st: seq Usize.t {stack_props_func g st})
                                                         (x: hp_addr{is_valid_header1 x g /\
                                                                       ~(Seq.mem (f_address x) st) /\
                                                                       (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                                       ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                                         (vl: seq Usize.t {vl_props_func g vl})
                                        : Lemma
                                          (requires 
                                                    
                                                    (~(Seq.mem (f_address x) st) /\ ~(Seq.mem (f_address x) vl)) /\
                                                    (Seq.mem x (get_allocated_block_addresses g)) /\
                                                    (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                    (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                   (ensures (fst (push_to_stack2 g st x) == G.push_to_stack_graph1 vl st (f_address x))) = 
if Seq.length st = 0 then
 (
    let f_x = f_address x in
    let stk' = Seq.create 1 f_x in
    let g' = colorHeader1 x g gray in 
    
   
    G.is_vertex_set_lemma2 stk';
    
    objects2_equal_lemma 0UL g g';

    assert (color_of_object1 x g == white);
    get_allocated_block_addresses_lemma g g' x 2UL;
    assert (Seq.length st == 0);
    //G.push_to_stack_graph_lemma grph vl st x;
    assert (G.push_to_stack_graph1 vl st f_x  == Seq.create 1 f_x);
    assert (stk' == Seq.create 1 f_x);
    assert (G.push_to_stack_graph1 vl st f_x == stk');
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
  
   //assert (objects2 0UL g ==  objects2 0UL g');
   //assert (well_formed_heap2 g');
   //assert (G.is_vertex_set st);
   //assert (~(Seq.mem (f_address x) st));
   G.snoc_unique_lemma f_x st;
   assert (G.is_vertex_set st'); 
   
   assert (Seq.length st > 0);
   //G.push_to_stack_graph_lemma1 grph vl st x;
   assert (G.push_to_stack_graph1 vl st f_x == snoc st f_x);
   ()
 )

#restart-solver

#restart-solver 

#reset-options "--z3rlimit 500"

#push-options "--split_queries always"

#restart-solver

let push_to_stack2_graph_lemma  (g:heap{well_formed_heap2 g})
                                (st: seq Usize.t {stack_props_func g st})
                                (x: hp_addr{is_valid_header1 x g /\
                                            ~(Seq.mem (f_address x) st) /\
                                            (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                            ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                             (Seq.mem x (get_allocated_block_addresses g))})
                     : Lemma 
                     (requires  
                                (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (push_to_stack2 g st x))) (snd (push_to_stack2 g st x))))
                     (ensures (create_graph_from_heap g == create_graph_from_heap ((snd (push_to_stack2 g st x))))) = 

if Seq.length st = 0 then
(
    let f_x = f_address x in
    let stk' = Seq.create 1 f_x in
    let g' = colorHeader1 x g gray in
    
    field_limits_allocated_blocks_lemma g;
    field_contents_within_limits_allocated_blocks_lemma g;
    fieldaddress_within_limits_lemma_x_all g;

    field_limits_allocated_blocks_lemma g';
    field_contents_within_limits_allocated_blocks_lemma g';
    fieldaddress_within_limits_lemma_x_all g';
    
    create_graph_from_heap_lemma_gray g x;
    assert (create_graph_from_heap g == create_graph_from_heap g');
    ()
)
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 

  field_limits_allocated_blocks_lemma g;
  field_contents_within_limits_allocated_blocks_lemma g;
  fieldaddress_within_limits_lemma_x_all g;

  field_limits_allocated_blocks_lemma g';
  field_contents_within_limits_allocated_blocks_lemma g';
  fieldaddress_within_limits_lemma_x_all g';
    
  create_graph_from_heap_lemma_gray g x;
  assert (create_graph_from_heap g == create_graph_from_heap g');
  ()
)   

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let darken_helper_fields_lemma(g:heap{well_formed_heap2 g})
                              (st: seq Usize.t{stack_props_func g st})
                              (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                               (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
          :Lemma
          (requires (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                    length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8) /\
                                 
                    (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                    length (slice (snd (darken_helper g st hdr_id)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8))
          
          (ensures  (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). 
                             getWosize (read_word g t) == getWosize (read_word (snd (darken_helper g st hdr_id)) t)) /\
                             
                             (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (darken_helper g st hdr_id)) y)) =

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
   push_to_stack2_fields_allocated_blocks_lemma g st hdr_id ;
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

#restart-solver

let fieldPush_spec_body_fields_lemma   (g:heap{well_formed_heap2 g})
                                       (st: seq Usize.t{stack_props_func g st})
                                       (h_index:hp_addr{is_valid_header1 h_index g})
                                       (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                       (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                    :Lemma
                     (requires (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8) /\
                                 
                               (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice (snd (fieldPush_spec_body1 g st h_index wz i)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)
                                )
                     (ensures  (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). 
                             getWosize (read_word g t) == getWosize (read_word (snd (fieldPush_spec_body1 g st h_index wz i)) t)) /\
                             
                             (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (fieldPush_spec_body1 g st h_index wz i)) y)) = 

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
        darken_helper_fields_lemma g st parent_hdr;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        darken_helper_fields_lemma g st h_addr_succ;
        ()
      )
   )
  else
   ( 
       ()
   )



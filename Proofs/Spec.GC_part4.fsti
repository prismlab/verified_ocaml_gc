module Spec.GC_part4

include Spec.GC_part3

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

let colorHeader5  (v_id:hp_addr)  
                  (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                  (c:color)
             : Tot (g': heap{g' == colorHeader1 v_id g c}) = 
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
 assert (g' == colorHeader1 v_id g c);
 
 g'

#reset-options "--z3rlimit 1000"

#restart-solver

let colorHeader5_lemma (v_id:hp_addr)  
                  (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                  (c:color)
          : Lemma
            (ensures (Seq.equal (colorHeader5 v_id g c) (colorHeader1 v_id g c))) = ()

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

let start_env_clos_info_helper_lemma (g:heap{well_formed_heap2 g}) 
                              (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                  (is_valid_header1 (hd_address f_addr) g) /\
                                  (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                                  (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2)}) 
                   : Lemma
                     (ensures ~(Seq.mem (Usize.add f_addr (Usize.mul 1UL mword)) (objects2 0UL g))) =
 
  let s = objects2 0UL g in
  assert (forall x y. Seq.mem x s /\ (Usize.v y >= Usize.v x + Usize.v mword) /\ 
                                                   (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1)) ==>
                                                   ~(Seq.mem y s));
                                                   
  
  let next_f_addr = Usize.add f_addr (Usize.mul 1UL mword) in
  let hdr_f_addr = hd_address f_addr in
  assert (Usize.v (wosize_of_object1 hdr_f_addr g) >= 2);
  let next_next_hdr_f_addr = Usize.add hdr_f_addr(Usize.mul 2UL mword) in
  assert (next_f_addr == next_next_hdr_f_addr);
  assert (Seq.mem hdr_f_addr s);
  let wz = getWosize (read_word g hdr_f_addr) in
  assert (Usize.v wz >= 2);
  let sum =  Usize.v hdr_f_addr + (((Usize.v wz  + 1) * Usize.v mword) - 1) in
  assert (Usize.v next_next_hdr_f_addr <= sum);
  (*assert (Usize.v next_next_hdr_f_addr >= Usize.v hdr_f_addr + Usize.v mword);
  assert (~(Seq.mem next_next_hdr_f_addr s));
  assert (~(Seq.mem next_f_addr s));*)
  ()

#restart-solver 

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver


let start_env_clos_info_helper_lemma1 (g:heap{well_formed_heap2 g}) 
                              (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                  (is_valid_header1 (hd_address f_addr) g) /\
                                  (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                                  (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2)}) 
                              (v_id:hp_addr{is_valid_header1 v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})

                              (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                    : Lemma
                      (requires is_hp_addr (Usize.add f_addr (Usize.mul 1UL mword)))
                      (ensures read_word g (Usize.add f_addr (Usize.mul 1UL mword)) == read_word (colorHeader1 v_id g c) (Usize.add f_addr (Usize.mul 1UL mword))) = 
 let next_f_addr = Usize.add f_addr (Usize.mul 1UL mword) in
 let hdr_f_addr = hd_address f_addr in
 assert (Usize.v (wosize_of_object1 hdr_f_addr g) >= 2);
 let next_next_hdr_f_addr = Usize.add hdr_f_addr(Usize.mul 2UL mword) in
 assert (next_f_addr == next_next_hdr_f_addr);
 assert (is_hp_addr next_f_addr);
 assert (is_hp_addr next_next_hdr_f_addr);

 //lemma_len_slice g (Usize.v (Usize.add next_f_addr (Usize.mul 1UL mword))) ((Usize.v (Usize.add next_f_addr (Usize.mul 1UL mword))) + (Usize.v mword));
 let r = read_word g next_f_addr in
 let g' = colorHeader1 v_id g c in
 let r' = read_word g' next_f_addr in
 start_env_clos_info_helper_lemma g f_addr;
 assert (~(Seq.mem next_f_addr (objects2 0UL g)));
 assert (heap_remains_same_except_index_v_id v_id g g');
 assert (v_id <> next_f_addr);
 assert (r == r');
 ()

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

#restart-solver

let start_env_clos_info_lemma (g:heap{well_formed_heap2 g}) 
                              (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                  (is_valid_header1 (hd_address f_addr) g) /\
                                  (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                                  (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2)}) 
                              (v_id:hp_addr{is_valid_header1 v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})

                              (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                      : Lemma
                        (requires well_formed_heap2 (colorHeader1 v_id g c))
                        (ensures (start_env_clos_info g f_addr == start_env_clos_info (colorHeader1 v_id g c) f_addr)) =
  let clos_info = closinfo_val_from_closure_object g f_addr in
  let start_env = extract_start_env_bits clos_info in
  (*assert ((is_hp_addr (Usize.add f_addr (Usize.mul 1UL mword))) /\
           (clos_info == read_word g (Usize.add f_addr (Usize.mul 1UL mword))));*)
  assert (start_env == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul);
  assert (start_env == Usize.shift_right (Usize.shift_left (read_word g (Usize.add f_addr (Usize.mul 1UL mword))) 8ul) 9ul);
  assert (is_hp_addr start_env);
  let hdr_f_addr = hd_address f_addr in
  assert (is_valid_header hdr_f_addr g);
  let wz = wosize_of_object1 hdr_f_addr g in
  assert (Usize.v start_env <= Usize.v wz);
  assert (Usize.v start_env >= Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g f_addr)));
  assert (Usize.v start_env >= 1);
  let g' = colorHeader5 v_id g c in
  colorHeader5_lemma v_id g c;
  let clos_info' = closinfo_val_from_closure_object g' f_addr in
  assert (Usize.v (tag_of_object1 (hd_address f_addr) g') == Usize.v (tag_of_object1 (hd_address f_addr) g));
  assert (Usize.v (wosize_of_object1 (hd_address f_addr) g) == Usize.v (wosize_of_object1 (hd_address f_addr) g'));
  lemma_len_slice g (Usize.v (Usize.add f_addr (Usize.mul 1UL mword))) ((Usize.v (Usize.add f_addr (Usize.mul 1UL mword))) + (Usize.v mword));
  lemma_len_slice g' (Usize.v (Usize.add f_addr (Usize.mul 1UL mword))) ((Usize.v (Usize.add f_addr (Usize.mul 1UL mword))) + (Usize.v mword));
  start_env_clos_info_helper_lemma1  g f_addr v_id c;
  assert (read_word g (Usize.add f_addr (Usize.mul 1UL mword)) == read_word g' (Usize.add f_addr (Usize.mul 1UL mword)));
  //closinfo_val1_lemma g f_addr v_id c;
  closinfo_val_from_closure_object_lemma g f_addr g';
  assert (clos_info == clos_info');
  let start_env' = extract_start_env_bits clos_info' in
  assert (start_env == start_env');
  ()

#restart-solver

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

let non_empty_set_lemma (g:heap{well_formed_heap2 g})
                        (st: seq Usize.t {stack_props_func g st})
     : Lemma
       (requires (~(G.is_emptySet st)))
       (ensures (Seq.length st > 0) /\
                (Seq.mem (Seq.index st (Seq.length st - 1)) st) /\
                Seq.equal (Seq.slice st 0 (Seq.length st - 1)) (Seq.slice st 0 (Seq.length st - 1)) /\
                Seq.equal st (Seq.slice st 0 (Seq.length st)) /\
                (forall x. mem x st <==> x == Seq.index st (Seq.length st - 1) \/ Seq.mem x (slice st 0 (Seq.length st - 1)))) =
assert (Seq.length st > 0);
assert (0 < Seq.length st);
assert (Seq.length st <= Seq.length st);
Seq.lemma_slice_snoc st 0 (Seq.length st);
assert (forall x. mem x (slice st 0 (Seq.length st)) <==> (x = index st ((Seq.length st) - 1) || mem x (slice st 0 ((Seq.length st) - 1))));
assert (forall x. mem x st <==> x == Seq.index st (Seq.length st - 1) \/ Seq.mem x (slice st 0 (Seq.length st - 1)));
()
       
#restart-solver


#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver


let mark5_body (g:heap{well_formed_heap2 g}) 
               (st: seq Usize.t {stack_props_func g st})
                                    
           : Pure (stack_heap_pair)
             (requires (~(G.is_emptySet st)))
             (ensures (fun st_hp -> (Seq.length g == Seq.length (snd st_hp)) /\
                                 well_formed_heap2 (snd st_hp) /\
                                 stack_props_func (snd st_hp) (fst st_hp) /\
                                 (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                                 (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp)))) = 

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
     
     (st1,g1)
   )
   else
   (
     let st1, g1 = fieldPush_spec1 g' s h_v_id wz 1UL in
     assert (G.is_vertex_set st1);
     assert (Seq.length g == Seq.length g1);
     
     (st1,g1)
   )
   
 )
  else
  (
    (s,g')
  )

let darken_wrapper (g:heap{well_formed_heap2 g})
                       (st: seq Usize.t{stack_props_func g st})
                       (h_index:hp_addr{is_valid_header1 h_index g})
                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                          
         : Pure (stack_heap_pair)
         (requires Usize.v (tag_of_object1 h_index g) < no_scan_tag)
         (ensures fun st_hp -> (well_formed_heap2 (snd st_hp)) /\
                            (Seq.length g == Seq.length (snd st_hp)) /\
         
                            (stack_props_func (snd st_hp) (fst st_hp)) /\
                            
                            (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\ 
                            (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                            
                            get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp)) =
 if (Usize.v (tag_of_object1 h_index g) = closure_tag) then
   (
     assert (Usize.v wz >= 2);

     let v_id = f_address h_index in
     
     let start_env = start_env_clos_info g v_id in

     assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address v_id) g)) /\
             Usize.v start_env >= 1);
     let start_env_plus_one = Usize.add start_env 1UL in
     let st1, g1 = fieldPush_spec1 g st h_index wz start_env_plus_one in
     
     (st1,g1)
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
     (st1,g1)
   )

let mark5_body1 (g:heap{well_formed_heap2 g}) 
               (st: seq Usize.t {stack_props_func g st})
                                    
           : Pure (stack_heap_pair)
             (requires (~(G.is_emptySet st)))
             (ensures (fun st_hp -> (Seq.length g == Seq.length (snd st_hp)) /\
                                 well_formed_heap2 (snd st_hp) /\
                                 stack_props_func (snd st_hp) (fst st_hp) /\
                                 (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                                 (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))))=
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

 if (Usize.v tg < no_scan_tag) then 
 (
    let st1, g1 = darken_wrapper g' s h_v_id wz in
     
     (st1,g1)
 )
 else
 (
   (s,g')
 )

#reset-options "--z3rlimit 500"

#restart-solver 

let mark5_body1_darken_wrapper_lemma (g:heap{well_formed_heap2 g}) 
                                     (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0})
                                     (v_id:hp_addr{(v_id == Seq.index st (Seq.length st - 1)) /\ (is_valid_header1 (hd_address v_id) g)})
                               
                                     (g': heap{g' == colorHeader1 (hd_address v_id) g black /\
                                               well_formed_heap2 g'})
                                     (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                                     (wz:wosize{wz == wosize_of_object1 (hd_address v_id) g})   
                   : Lemma
                   (requires (stack_props_func g' s) /\
                             (Usize.v v_id >= Usize.v mword /\ Usize.v v_id < heap_size) /\
                              (is_valid_header1 (hd_address v_id) g') /\
                              (Usize.v (tag_of_object1 (hd_address v_id) g') < no_scan_tag))
                                                  
                   (ensures (fst (mark5_body1 g st) == fst (darken_wrapper g' s (hd_address v_id) wz)) /\
                            (snd (mark5_body1 g st) == snd (darken_wrapper g' s (hd_address v_id) wz))) = ()

let mark5_body1_darken_wrapper_lemma1 (g:heap{well_formed_heap2 g}) 
                                     (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0})
                                     (v_id:hp_addr{(v_id == Seq.index st (Seq.length st - 1)) /\ (is_valid_header (hd_address v_id) g)})
                               
                                     (g': heap{g' == colorHeader1 (hd_address v_id) g black /\
                                               well_formed_heap2 g'})
                                     (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                                     (wz:wosize{wz == wosize_of_object1 (hd_address v_id) g})   
                   : Lemma
                   (requires (stack_props_func g' s) /\
                             (Usize.v v_id >= Usize.v mword /\ Usize.v v_id < heap_size) /\
                              (is_valid_header (hd_address v_id) g') /\
                              (Usize.v (tag_of_object1 (hd_address v_id) g') >=  no_scan_tag))
                                                  
                   (ensures (fst (mark5_body1 g st) == s) /\
                            (snd (mark5_body1 g st) == g')) = ()

#restart-solver 

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


let stack_slice_only_has_gray_color_lemma (g:heap{well_formed_heap2 g}) 
                                          (st: seq Usize.t {stack_props_func g st /\
                                                             Seq.length st > 0
                                                            })
                                          (v_id:hp_addr{v_id == Seq.index st (Seq.length st - 1) /\
                                                        Usize.v v_id >= Usize.v mword /\
                                                        is_valid_header1 (hd_address v_id) g})
                                          (c:color{c == 3UL})
                               : Lemma
                                 (requires True)
                                 
                                 (ensures (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g c)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g c)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)))) = 
 non_empty_set_lemma g st;
 
 let s = Seq.slice st 0 (Seq.length st - 1) in
 assert (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (Usize.v v_id  >= Usize.v mword);
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
   
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
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
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g c)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g c)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)));
 ()


#reset-options "--z3rlimit 500"

let colorHeader1_subset_lemma  (v_id:hp_addr)  
                               (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                        
              : Lemma
                (ensures (forall x. Seq.mem x (get_black_block_addresses g (get_allocated_block_addresses g)) ==>
                                    Seq.mem x (get_black_block_addresses (colorHeader1 v_id g black) 
                                                 (get_allocated_block_addresses (colorHeader1 v_id g black)))) /\
                          G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                            (get_black_block_addresses (colorHeader1 v_id g black) 
                                                 (get_allocated_block_addresses (colorHeader1 v_id g black)))) = 
let g' = colorHeader1 v_id g black in
let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
assert (heap_remains_same_except_index_v_id v_id g g');
assert (color_of_object1 v_id g' == black);
assert (forall x. Seq.mem x blacks /\ x <> v_id ==> Seq.mem x blacks');
assert (forall x. Seq.mem x blacks ==> Seq.mem x blacks');
assert (G.subset_vertices blacks blacks');
()

#restart-solver

let colorHeader1_black_nodes_lemma (g:heap{well_formed_heap2 g}) 
                                   (y:hp_addr{Usize.v y >= 0 /\ Usize.v y < heap_size /\
                                             is_valid_header1 y g /\
                                             color_of_object1 y g <> black
                                          })
           : Lemma
             (ensures Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (colorHeader1 y g black) (get_allocated_block_addresses (colorHeader1 y g black)))) = 
let g' = colorHeader1 y g black in
let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
colorHeader1_alloc_colors_lemma y g black;
colorHeader1_subset_lemma y g;
assert (G.subset_vertices blacks blacks');
 assert (is_valid_header1 y g');
 assert (Seq.mem y blacks');
 assert (~(Seq.mem y blacks));
 assert (Seq.length blacks <= Seq.length blacks');
 if Seq.length blacks < Seq.length blacks' then ()
 else
 (
   assert (Seq.length blacks == Seq.length blacks');
   G.subset_of_each_other blacks blacks';
   assert (G.subset_vertices blacks' blacks);
   assert (forall x. Seq.mem x blacks' ==> Seq.mem x blacks);
   ()
 )

let colorHeader1_color_Lemma (v_id:hp_addr)  
                             (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g /\ color_of_object1 v_id g == white}) 
                             (c:color{c == 2UL})
              : Lemma
                (color_of_object1 v_id (colorHeader1 v_id g c) == 2UL /\
                 color_of_object1 v_id (colorHeader1 v_id g c) <> black /\
                 color_of_object1 v_id g <> black) = ()

#restart-solver 

let push_to_stack2_lemma_black_nodes1 (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{stack_props_func g st})
                                    
                                    (x: hp_addr{is_valid_header1 x g /\
                                                                ~(Seq.mem (f_address x) st) /\ 
                                                                (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                                color_of_object1 x g == white /\
                                                                (*Introduction of the below condition was needed to typecheck*)
                                                                is_fields_within_limit1 x (getWosize (read_word g x))}) 
                                                               
                                                              
                   : Lemma 
                     (ensures G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x))))) = 
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   colorHeader1_alloc_colors_lemma x g gray;
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   colorHeader1_color_Lemma x g 2UL;

   get_allocated_block_addresses_lemma g g' x 2UL;

   assert ((get_allocated_block_addresses g) == (get_allocated_block_addresses g'));
    
   let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
   let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
   G.is_vertex_set_lemma2 stk';
    
   assert (color_of_object1 x g == white);
   assert (color_of_object1 x g <> black);
   assert (color_of_object1 x g' <> black);
   assert (heap_remains_same_except_index_v_id x g g');
   assert (forall y. Seq.mem y blacks ==> Seq.mem y blacks');
   assert (G.subset_vertices blacks blacks');
   assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x)))));
   ()
)
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  colorHeader1_alloc_colors_lemma x g gray;
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  colorHeader1_color_Lemma x g 2UL;

  get_allocated_block_addresses_lemma g g' x 2UL;

  assert ((get_allocated_block_addresses g) == (get_allocated_block_addresses g'));
    
  let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
  let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
  assert (color_of_object1 x g == white);
  assert (color_of_object1 x g <> black);
  assert (color_of_object1 x g' <> black);
  assert (heap_remains_same_except_index_v_id x g g');
  assert (forall y. Seq.mem y blacks ==> Seq.mem y blacks');
  assert (G.subset_vertices blacks blacks');
  assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x)))));
  ()
)

let darken_helper_black_nodes_lemma(g:heap{well_formed_heap2 g})
                                   (st: seq Usize.t{stack_props_func g st})
                                   (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                                   (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
           : Lemma
             (ensures (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                   (get_black_block_addresses (snd (darken_helper g st hdr_id)) 
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

#restart-solver

//#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#reset-options "--z3rlimit 1000"
#restart-solver

let fieldPush_spec_body1_black_nodes_lemma (g:heap{well_formed_heap2 g})
                                          (st: seq Usize.t{stack_props_func g st})
                                          (h_index:hp_addr{is_valid_header1 h_index g})
                                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                          (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                          
                                          
                                          
                        : Lemma
                          (requires G.is_vertex_set (get_black_block_addresses g (get_allocated_block_addresses g)) /\
                                    G.is_vertex_set (get_black_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)))))
                          (ensures G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                   (get_black_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i))))) =
  
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
        darken_helper_black_nodes_lemma g st parent_hdr;
        ()
      )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        darken_helper_black_nodes_lemma g st h_addr_succ;
        ()
      )
 )
 else
 (
   ()
 )

#restart-solver 

let rec fieldPush_spec1_black_nodes_lemma (g:heap{well_formed_heap2 g})
                                          (st: seq Usize.t{stack_props_func g st})
                         
                                          (h_index:hp_addr{is_valid_header1 h_index g})
                                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                          (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                              
                                           
                                           
                        : Lemma
                          (ensures (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (fieldPush_spec1 g st h_index wz i)) 
                                                                               (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i))))))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
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
       let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
       assert (G.is_vertex_set blacks);
       let blacks' = get_black_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i))) in
       assert (G.is_vertex_set blacks');
       assert (G.is_vertex_set (get_black_block_addresses g (get_allocated_block_addresses g)) /\
                                    G.is_vertex_set (get_black_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)))));
       fieldPush_spec_body1_black_nodes_lemma g st h_index wz i;
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
                                         Seq.mem x st'));
       
       let st'', g'' = fieldPush_spec1 g' st' h_index wz i' in
       fieldPush_spec1_black_nodes_lemma g' st' h_index wz i';
       assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                 (get_black_block_addresses g'' (get_allocated_block_addresses g'')));
       ()
    )

#restart-solver

#restart-solver

let color_pre_condition (g:heap{well_formed_heap2 g}) 
                        (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0}) = 
 (forall x. Seq.mem (hd_address x) (objects2 0UL (colorHeader5 (hd_address (Seq.index st (Seq.length st - 1))) g black)) /\ 
           isGrayObject1 (hd_address x) (colorHeader5 (hd_address (Seq.index st (Seq.length st - 1))) g black) <==>
           Seq.mem x (Seq.slice st 0 (Seq.length st - 1)))

let mark5_body_black_nodes_lemma_post_condition (g:heap{well_formed_heap2 g}) 
                                                (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0}) =
 Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st))))


let is_black_subset (g:heap{well_formed_heap2 g})
                    (g':heap{well_formed_heap2 g'}) =
 G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                   (get_black_block_addresses g' (get_allocated_block_addresses g'))

let is_black_subset_lemma (g:heap{well_formed_heap2 g})
                          (g':heap{well_formed_heap2 g'}) 
              : Lemma 
                (requires is_black_subset g g')
                (ensures Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <=
                            Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g'))) =
 ()

let black_objects_length (g:heap{well_formed_heap2 g})
                         (g':heap{well_formed_heap2 g'}) =
  Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
           Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g'))

let black_objects_length1 (g:heap{well_formed_heap2 g})
                         (g':heap{well_formed_heap2 g'}) =
  Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <=
           Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g'))

let is_black_subset_lemma_trans (g:heap{well_formed_heap2 g})
                                (g':heap{well_formed_heap2 g'}) 
                                (g1:heap{well_formed_heap2 g1}) 
               : Lemma
                 (requires (black_objects_length g g') /\ (black_objects_length1 g' g1))
                 (ensures (black_objects_length g g1)) = 
 ()

let seq_slice_lemma (#a:eqtype)
                    (st: seq a{Seq.length st > 0})
              : Lemma
                (ensures  (let s = Seq.slice st 0 (Seq.length st - 1) in
                           Seq.equal s (Seq.slice st 0 (Seq.length st - 1)))) = ()
 
let seq_index_lemma (#a:eqtype)
                    (st: seq a{Seq.length st > 0})
              : Lemma
                (ensures  (let s = Seq.index st (Seq.length st - 1) in
                           s == (Seq.index st (Seq.length st - 1)))) = ()


let seq_slice_transitive_lemma (#a:eqtype)
                               (st: seq a{Seq.length st > 0})
                               (s: seq a)
                               (xs: seq a)
                     : Lemma   
                       (requires (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)) /\
                                  Seq.equal xs (Seq.slice st 0 (Seq.length st - 1))))
                       (ensures (Seq.equal s xs) /\
                                (s == xs)) = () 

let seq_index_lemma1 (#a:eqtype)
                    (st: seq a{Seq.length st > 0})
              : Lemma
                (ensures  (let s = Seq.index st (Seq.length st - 1) in
                          (Seq.mem s st))) = ()
#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver



let test19  (v_id:hp_addr)  
            (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
            (c:color) = 
 let g1 = colorHeader5 v_id g c in
 admit()



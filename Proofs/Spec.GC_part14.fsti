module Spec.GC_part14

include Spec.GC_part13

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

let objects_fields_lemma1 (g:heap(*{well_formed_heap2 g}*))
                          (x:hp_addr{(*is_valid_header x g /\*) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                          (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                          (j:Usize.t{Usize.v j > 1 /\
                                     Usize.v j <= (Usize.v (getWosize (read_word g x)))}) 
                   : Lemma
                    (ensures (Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v i)) = ()
                    
#restart-solver

#reset-options "--z3rlimit 100 --query_stats"
                    
let objects_fields_lemma1_all1 (g:heap(*{well_formed_heap2 g}*))
                               (x:hp_addr{(*is_valid_header x g /\*) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                               (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                    : Lemma
                      (ensures (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g x))}).Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v i)) = 
 Classical.forall_intro (objects_fields_lemma1 g x i);
 ()

#restart-solver

let h_index_field_index_mword_multiple_lemma7 (g:heap(*{well_formed_heap2 g}*))
                                              (h_index: hp_addr{Seq.mem h_index (objects2 0UL g)})
                                              (wz: wosize{((wz == getWosize (read_word g h_index)) /\ 
                                                             is_fields_within_limit1 h_index wz) (*/\
                                                             is_fields_contents_within_limit2 h_index wz g*)})
                                              (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (is_hp_addr (Usize.add h_index (Usize.mul  i mword)))) = 
 
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) < heap_size);
assert (is_hp_addr (Usize.add h_index (Usize.mul  i mword)));
()

#restart-solver 

#restart-solver

let h_index_field_index_all_mword_multiple_lemma7(g:heap(*{well_formed_heap2 g}*))
                                                 (h_index: hp_addr{Seq.mem h_index (objects2 0UL g)})
                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ 
                                                             is_fields_within_limit1 h_index wz) (*/\
                                                             is_fields_contents_within_limit2 h_index wz g*)}) 
                                : Lemma
                                 (ensures (forall (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g h_index))}).
                                          is_hp_addr (Usize.add h_index (Usize.mul i mword)))) = 
Classical.forall_intro (Classical.move_requires (h_index_field_index_mword_multiple_lemma7 g h_index wz));
()

#restart-solver 

#restart-solver 

#restart-solver 

let first_field_of_blue (g:heap(*{well_formed_heap2 g}*))
                        (x:hp_addr) =
   Usize.v x >= Usize.v mword /\ (*is_valid_header (hd_address x) g*) Seq.mem (hd_address x) (objects2 0UL g)  /\ color_of_object1 (hd_address x) g == blue

let first_field_of_any (g:heap(*{well_formed_heap2 g}*))
                       (v:hp_addr) =
                
Usize.v v >= Usize.v mword /\ (*is_valid_header (hd_address v) g*)Seq.mem (hd_address v) (objects2 0UL g)

let header_value_does_not_change_with_a_field_write (g:heap(*{well_formed_heap2 g}*))
                                                    (x:hp_addr{first_field_of_blue g x})
                                                    (v:hp_addr{first_field_of_any g v}) =
    (forall p. Seq.mem p (objects2 0UL g) ==> read_word (write_word g x v) p ==  read_word g p)   
                                           
let objs_remain_the_same_with_a_write_to_first_field (g:heap(*{well_formed_heap2 g}*))
                                                     (x:hp_addr{first_field_of_blue g x})
                                                     (v:hp_addr{first_field_of_any g v}) =
   objects2 0UL g == objects2 0UL (write_word g x v) 

let write_to_the_firstfield_of_blue_object_preserves_the_field_reads_of_all_non_blue_objects (g:heap(*{well_formed_heap2 g}*))
                                                                                             (x:hp_addr{first_field_of_blue g x})
                                                                                             (v:hp_addr{first_field_of_any g v}) =
   (forall p. Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g x v) j == read_word g j))

let write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_objects_other_than_this_object (g:heap(*{well_formed_heap2 g}*))
                                                                                                              (x:hp_addr{first_field_of_blue g x})
                                                                                                              (v:hp_addr{first_field_of_any g v}) =
   (forall p. (*is_valid_header p g*) Seq.mem p (objects2 0UL g) /\ p <> (hd_address x) ==> 
                               (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g x v) j == read_word g j))

let write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_other_fields_of_that_object (g:heap(*{well_formed_heap2 g}*))
                                                                                                            (x:hp_addr{first_field_of_blue g x})
                                                                                                            (v:hp_addr{first_field_of_any g v}) =
  (forall (j:hp_addr). Usize.v j > Usize.v (hd_address x) + Usize.v mword /\
                                     Usize.v j <= Usize.v (hd_address x) + (Usize.v (getWosize (read_word g (hd_address x))) * Usize.v mword) ==>
                                      read_word (write_word g x v) j == read_word g j)

let write_to_first_field_of_a_blue_object_lies_within_heap_limits_of_fields (g:heap(*{well_formed_heap2 g}*))
                                                                            (x:hp_addr{first_field_of_blue g x})
                                                                            (v:hp_addr{first_field_of_any g v}) =

  Usize.v (read_word (write_word g x v) x) >= Usize.v mword /\ Usize.v (read_word (write_word g x v) x) < heap_size


#restart-solver

let field_addresses_are_heap_addresses (g:heap(*{well_formed_heap2 g}*))
                                       (x:hp_addr{Usize.v x >= Usize.v mword /\ (*is_valid_header (hd_address x) g*) Seq.mem (hd_address x) (objects2 0UL g) /\
                                                  color_of_object1 (hd_address x) g == blue})
                                           
                                           
                                       (v:hp_addr{Usize.v v >= Usize.v mword /\ (*is_valid_header (hd_address v) g*) Seq.mem (hd_address v) (objects2 0UL g)}) =
 (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g (hd_address x)))}). 
                                          is_hp_addr (Usize.add (hd_address x) (Usize.mul j mword))) 

let write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_other_fields_of_that_object1 (g:heap(*{well_formed_heap2 g}*))
                                                                                                            (x:hp_addr{first_field_of_blue g x})
                                                                                                            (v:hp_addr{first_field_of_any g v /\
                                                                                                                       field_addresses_are_heap_addresses g x v}) =
 forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g (hd_address x)))}).
                                                     Usize.v (read_word g (Usize.add (hd_address x) (Usize.mul j mword))) == 
                                                     Usize.v (read_word (write_word g x v) (Usize.add (hd_address x) (Usize.mul j mword)))

#restart-solver 

#restart-solver

#restart-solver 

#reset-options "--z3rlimit 500"

#restart-solver

let write_word_to_blue_object_field_lemma_props (g:heap(*{well_formed_heap2 g}*))
                                                (x:hp_addr{first_field_of_blue g x})
                                                (v:hp_addr{first_field_of_any g v}) =
 
 (forall (p:hp_addr). read_word (write_word g x v) p == ( if x = p then
                                                               v 
                                                             else 
                                                               read_word g p))
                                                          

let write_word_to_blue_object_field_lemma_props1 (g:heap(*{well_formed_heap2 g}*)) =
 ( forall p. Seq.mem p (objects2 0UL g) ==> Usize.v (getWosize (read_word g p)) > 0)

let write_word_to_blue_object_field_lemma_props2 (g:heap(*{well_formed_heap2 g}*))
                                                (x:hp_addr{first_field_of_blue g x}) =
  
   (Usize.v (getWosize (read_word g (hd_address x))) > 0) /\
   (Usize.v (getWosize (read_word g (hd_address x))) >= 1)

let write_word_to_blue_object_field_lemma_props3 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 (v:hp_addr{first_field_of_any g v})=
  (forall p. Seq.mem p (objects2 0UL g) ==> read_word (write_word g x v) p ==  read_word g p) /\
  (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word (write_word g x v) p) ==  getWosize (read_word g p))


let write_word_to_blue_object_field_lemma_props4 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 (v:hp_addr{first_field_of_any g v}) =

  (forall (p:hp_addr). p <> x ==> read_word (write_word g x v) p == read_word g p)
  

let write_word_to_blue_object_field_lemma_props5 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 (v:hp_addr{first_field_of_any g v}) =
 (forall p. Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v x)) /\
 (forall p.  Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g x v) j == read_word g j)) /\
 (forall p. Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g x v) j == read_word g j))

let write_word_to_blue_object_field_lemma_props6 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 (v:hp_addr{first_field_of_any g v}) =
                                                 
 (forall p.  Seq.mem p (objects2 0UL g) /\  p <> (hd_address x) ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v x)) /\
 (forall p.  Seq.mem p (objects2 0UL g) /\ p <> (hd_address x) ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g x v) j == read_word g j)) /\
 (forall (j:hp_addr). Usize.v j > Usize.v (hd_address x) + Usize.v mword /\
                                     Usize.v j <= Usize.v (hd_address x) + (Usize.v (getWosize (read_word g (hd_address x))) * Usize.v mword) ==>
                                      read_word (write_word g x v) j == read_word g j)

let write_word_to_blue_object_field_lemma_props7 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 (v:hp_addr{first_field_of_any g v}) =
  (Usize.v v >= Usize.v mword /\ Usize.v v < heap_size) /\
  
  (Usize.v v % Usize.v mword == 0) /\

  (read_word (write_word g x v) x == v) /\

  (Usize.v (read_word (write_word g x v) x) >= Usize.v mword /\ Usize.v (read_word (write_word g x v) x) < heap_size)


let write_word_to_blue_object_field_lemma_props8 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 =
  (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g (hd_address x)))}).Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v x)

let objects_fields_lemma1_all1_props (g:heap(*{well_formed_heap2 g}*))
                                     (x:hp_addr{ Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                                     (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword})  =
                  
 (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g x))}).Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v i)

#restart-solver

let wosize_of_header_of_x (g:heap(*{well_formed_heap2 g}*))
                          (x:hp_addr{first_field_of_blue g x})
            : Tot (wz:wosize{wz == getWosize (read_word g (hd_address x)) /\ (is_fields_within_limit1 (hd_address x) wz)})=
 let wz = getWosize (read_word g (hd_address x)) in
 assert (is_fields_within_limit1 (hd_address x) wz);
 wz


let heap_remains_same_except_index_v_id2  (v_id1:hp_addr)
                                          (v_id2:hp_addr)
                                          (g:heap)
                                          (g':heap{Seq.length g == Seq.length g'}) =
  forall (x:Usize.t {Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). x <> v_id1  /\ x <> v_id2 ==>
           read_word g x == read_word g' x 

let heap_remains_same_except_index_lemma (v_id1:hp_addr)
                                         (v_id2:hp_addr)
                                         (g:heap)
                                         (g':heap{Seq.length g == Seq.length g'})
                                         (g'':heap{Seq.length g == Seq.length g''})
                        : Lemma
                          (requires (heap_remains_same_except_index_v_id v_id1 g g' /\
                                     heap_remains_same_except_index_v_id v_id2 g' g''))
                          (ensures heap_remains_same_except_index_v_id2 v_id1 v_id2 g g'') = ()


#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries always"

#restart-solver

#restart-solver

let write_word_to_blue_object_field_lemma (g:heap(*{well_formed_heap2 g}*){write_word_to_blue_object_field_lemma_props1 g /\ Seq.length (objects2 0UL g) > 0})
                                          (x:hp_addr{first_field_of_blue g x})
                                          (v:hp_addr{first_field_of_any g v})
                          :Lemma 
                          (ensures  (objs_remain_the_same_with_a_write_to_first_field g x v) /\ 
                          
                                    (header_value_does_not_change_with_a_field_write g x v) /\
                                    
                                    (write_to_the_firstfield_of_blue_object_preserves_the_field_reads_of_all_non_blue_objects g x v) /\
                                    
                                    (write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_objects_other_than_this_object g x v) /\
                                    
                                    (write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_other_fields_of_that_object g x v) /\
                                    
                                    (write_to_first_field_of_a_blue_object_lies_within_heap_limits_of_fields g x v) /\
                                    
                                    (field_addresses_are_heap_addresses g x v) /\
                                    (write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_other_fields_of_that_object1 g x v) /\
                                    Seq.length (objects2 0UL (write_word g x v)) > 0
                                    ) = 

  let g' = write_word g x v in
  write_word_lemma1 g x v;
  assert (write_word_to_blue_object_field_lemma_props g x v);
  
  assert (Seq.mem (hd_address x) (objects2 0UL g));
  
  assert (write_word_to_blue_object_field_lemma_props1 g);
  
  assert (write_word_to_blue_object_field_lemma_props2 g x);
  fields_not_mem_objs_lemma g g' (hd_address x) x;
  assert (~(Seq.mem x (objects2 0UL g)));
  
  assert (write_word_to_blue_object_field_lemma_props3 g x v);
  
  objects2_equal_lemma1_app g g';
  assert (objects2 0UL g == objects2 0UL g');
  assert (Seq.length (objects2 0UL g) > 0);
  assert (Seq.length (objects2 0UL g') > 0);
  assert (write_word_to_blue_object_field_lemma_props4 g x v);
  objects_fields_lemma_all1_app g (hd_address x) x;
  assert (write_word_to_blue_object_field_lemma_props5 g x v);
  
 
  objects_fields_lemma_all1_app1 g (hd_address x) x;
  assert (write_word_to_blue_object_field_lemma_props6 g x v);
  
  assert (write_word_to_blue_object_field_lemma_props7 g x v);
  objects_fields_lemma1_all1 g (hd_address x) x;
  assert (objects_fields_lemma1_all1_props g (hd_address x) x);
  
  h_index_field_index_all_mword_multiple_lemma7 g (hd_address x) (wosize_of_header_of_x g x);
  ()



// one more heap untouched by sweep. Any object white in g less than f_index does not point to f_index. 
//g' --> heap after mark, g --> current heap (passing to sweep_body)
//Assume that well-formedness hold for the portion of g less than f_index. f-index = 0, intial; trivially holds
//PT. well_formedness hold for portion of g <= f_index.
//All the cases, B--> white ---> 

#restart-solver 

let sweep_body_with_free_list (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ write_word_to_blue_object_field_lemma_props1 g})
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ 
                                                              Seq.mem (hd_address f_index) (objects2 0UL g)})
                              (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                                         color_of_object1 (hd_address fp) g == blue /\
                                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
           
            : Tot (p:heap_heap_addr_pair{Seq.length (objects2 0UL (fst p)) > 0 /\ noGreyObjects (fst p) /\
                                         (objects2 0UL g == objects2 0UL (fst p)) /\
                                         Usize.v (snd p) >= Usize.v mword /\ 
                                         Seq.mem (hd_address (snd p)) (objects2 0UL (fst p)) /\ 
                                         color_of_object1 (hd_address (snd p)) (fst p) == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL (fst p)) /\ Seq.mem y (objects2 0UL (fst p)) ==>
                                             Usize.v (getWosize (read_word (fst p) x)) + Usize.v (getWosize (read_word (fst p) y)) < heap_size) /\
                                         (forall x. Seq.mem x (objects2 0UL g) /\ x <> (hd_address f_index) ==> Seq.mem x (objects2 0UL (fst p)))}) =
                            
 let h_index = hd_address f_index in
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white || c = blue) then 
 (
   let g' = colorHeader3 h_index g blue in
   assert (objects2 0UL g == objects2 0UL g');
   
   assert (Usize.v fp % Usize.v mword == 0);

   (*let hd_fp = hd_address fp in
   let fp_wz_sz = getWosize (read_word g' hd_fp) in
   let fp_wz_sz' = getWosize (read_word g hd_fp) in
   assert (fp_wz_sz == fp_wz_sz');
   let fp_color = getColor (read_word g' hd_fp) in
   assert (fp_color == blue);
   let fp_wz_sz_plus_one = Usize.add fp_wz_sz 1UL in
   let next_obj_offset = Usize.mul fp_wz_sz_plus_one mword in
   let next_obj = Usize.add fp next_obj_offset in*)
   
   let g1 = write_word g' fp f_index in
   //write_word_to_blue_object_field_lemma1 g' fp f_index;
   write_word_to_blue_object_field_lemma g' fp  f_index;
   //assert (well_formed_heap2 g1);
   assert (objects2 0UL g == objects2 0UL g');
   assert (Seq.length (objects2 0UL g') > 0);
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   assert (noGreyObjects g');
   assert (noGreyObjects g1);
   assert (Usize.v f_index >= Usize.v mword);
   assert (Seq.mem (hd_address f_index) (objects2 0UL g1));
   assert (color_of_object1 (hd_address f_index) g1 == blue);
   assert (forall x y. Seq.mem x (objects2 0UL g1) /\ Seq.mem y (objects2 0UL g1) ==>
                         Usize.v (getWosize (read_word g1 x)) + Usize.v (getWosize (read_word g1 y)) < heap_size);
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g1));
   (g1,f_index)

  
 )
 else
 (
   assert (c == black);
   let g' = colorHeader3 h_index g white in
   assert (objects2 0UL g == objects2 0UL g');
      
   
   assert (Usize.v fp >= Usize.v mword);
   //assert (is_valid_header (hd_address fp) g');
   assert (color_of_object1 (hd_address fp) g == blue);
   assert (color_of_object1 (hd_address fp) g' == blue);
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   assert (noGreyObjects g');
   (g',fp)
 )

#restart-solver

let colorHeader3_lemma  (v_id:hp_addr)  
                        (g:heap(*{well_formed_heap2 g /\ is_valid_header1 v_id g}*){(Seq.length (objects2 0UL g) > 0) /\ (Seq.mem v_id (objects2 0UL g))}) 
                        (c:color)
          : Lemma
            (requires well_formed_heap2 g /\ is_valid_header1 v_id g)
            (ensures colorHeader1 v_id g c == colorHeader3 v_id g c) =
()


let wosize_plus_one_times_mword_multiple_of_mword (wz:wosize)
                     :Lemma 
                      (ensures (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0)) = ()

let well_formedness_first_field_lemma (g:heap{Seq.length (objects2 0UL g) > 0
                                              })
                                      (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)})
                         : Lemma
                           (ensures (~(Seq.mem f_index (objects2 0UL g)))) =
 (*assert (well_formed_heap2 g);*)
 assert (forall x. Seq.mem x (objects2 0UL g) ==> Usize.v (getWosize (read_word g x)) > 0);
 let h_index = hd_address f_index in
 assert (Seq.mem h_index (objects2 0UL g));
 assert (forall x y. Seq.mem x (objects2 0UL g) /\ (Usize.v y >= Usize.v x + Usize.v mword) /\ 
                                                   (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1)) ==>
                                                   ~(Seq.mem y (objects2 0UL g)));
 assert (~(Seq.mem f_index (objects2 0UL g)));                                                
 ()


#reset-options "--z3rlimit 500"

#restart-solver

#push-options "--split_queries always"

#restart-solver

let write_word_length_lemma (byte_array: heap)
                            (byte_index: hp_addr)
                            (value: UInt64.t)
  : Lemma
    (ensures length (write_word byte_array byte_index value) == length byte_array) = ()
 
 
let write_word_heap_lemma (g:heap{ noGreyObjects g})
                          (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\  Seq.mem (hd_address f_index) (objects2 0UL g)})
                          (fp:hp_addr{Usize.v fp >= Usize.v mword /\  Seq.mem (hd_address fp) (objects2 0UL g) /\ color_of_object1 (hd_address fp) g == blue}) 
              : Lemma
                (ensures heap_remains_same_except_index_v_id fp g (write_word g fp f_index)) =
   let g1 = write_word g fp f_index in
   write_word_lemma g fp f_index;
   write_word_length_lemma g fp f_index;
   assert (length g == length g1);
   assert (heap_remains_same_except_index_v_id fp g g1);
   ()

(*val objects2_cons_lemma2 : (h_index: hp_addr)->
                           (g:heap)->
                         
            Lemma 
            (ensures (Seq.length (objects2 h_index g) > 0 /\ 
                        Usize.v (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) >= heap_size ==> 
                          Seq.length (objects2 h_index g) == 1))*)
                          
let wosize_plus_times_mword_multiple_of_mword1 (wz:wosize)
                     :Lemma 
                      (ensures (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0)) = ()

let objects2_mem_lemma1_app (h_index: hp_addr)
                            (g:heap)
                           
                      
          : Lemma 
            (requires (Seq.length (objects2 0UL g) > 0 /\ Seq.mem h_index (objects2 0UL g) /\ 
                        Usize.v (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) < heap_size))
            (ensures (Seq.mem (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) (objects2 0UL g))) = 
  
  let s = objects2 0UL g in
  objects2_mem_lemma1 0UL g;
  let h_index_new = Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword) in
  assert (Usize.v h_index_new < heap_size);
  assert (Seq.mem h_index_new s);
  ()

#restart-solver 

let rec objects_mem_h_index_lemma  (g:heap)
                                   (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                   (l: seq Usize.t {l == objects2 h_index g})
                                   (fp:hp_addr{Usize.v fp >= Usize.v mword /\ Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                               color_of_object1 (hd_address fp) g == blue /\
                                               (~(Seq.mem fp (objects2 0UL g)))
                                                }) 
                      : Lemma
                        (ensures ~(Seq.mem fp (objects2 h_index g)))
                        (decreases (Seq.length l))  =
 if Seq.length l = 0 then ()
else
(
  assert (Seq.length l > 0);
  assert (l == objects2 h_index g);
  let wz =  getWosize (read_word g h_index) in
  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
  if Usize.v h_index_new >= heap_size then
  (
    objects2_cons_lemma2 h_index g;
    assert ((Seq.length (objects2 h_index g) > 0 /\ 
                        Usize.v (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) >= heap_size ==> 
                          Seq.length (objects2 h_index g) == 1));
   
    assert (Seq.mem h_index (objects2 0UL g));
    assert (Seq.length (objects2 h_index g) == 1);
    assert (~(Seq.mem fp (objects2 0UL g)));
    ()
  )
  else
  (
    assert (Usize.v h_index_new < heap_size);
    wosize_plus_times_mword_multiple_of_mword1 wz;
    sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
    assert (Usize.v h_index_new % Usize.v mword == 0);
    assert (is_hp_addr h_index_new);
    objects2_cons_lemma1 h_index g h_index_new;
    assert (Seq.length (objects2 h_index g) > 0 /\  Usize.v h_index_new < heap_size ==> 
                      ((objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g)) /\
                      (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g))));
    let l1 = objects2 h_index_new g in
    assert (l == Seq.cons h_index l1);
    lemma_tl h_index l1;
    assert (l1 == Seq.tail l);
    objects2_mem_lemma1_app h_index g;
    
    assert (Seq.length l1 < Seq.length l);
    objects_mem_h_index_lemma g h_index_new l1 fp;
    assert (~(Seq.mem fp (objects2 h_index_new g)));
    
    assert (fp <> h_index);
    assert (~(Seq.mem fp l1));
    Seq.mem_cons h_index l1;
    assert (~(Seq.mem fp l));
    ()
  )
  
)


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let sweep_body_with_free_list_lemma5 (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ write_word_to_blue_object_field_lemma_props1 g})
                                     (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ 
                                                              Seq.mem (hd_address f_index) (objects2 0UL g)})
                                     (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                                         color_of_object1 (hd_address fp) g == blue /\
                                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
            
            
            :Lemma (ensures ((color_of_object1 (hd_address f_index) g == white \/  color_of_object1 (hd_address f_index) g == blue) <==>
                              color_of_object1 (hd_address f_index) (fst (sweep_body_with_free_list g f_index fp)) == blue) /\
                              
                              (color_of_object1 (hd_address f_index) g == black <==> 
                              color_of_object1 (hd_address f_index) (fst (sweep_body_with_free_list g f_index fp)) == white) /\
                              
                              (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ Usize.v x > Usize.v (hd_address f_index) ==> 
                                        getColor (read_word g x) == getColor (read_word (fst (sweep_body_with_free_list g f_index fp)) x)) /\
                               
                              (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v (hd_address f_index) ==> 
                                        getColor (read_word g x) == getColor (read_word (fst (sweep_body_with_free_list g f_index fp)) x)) /\
                              heap_remains_same_except_index_v_id2 (hd_address f_index) fp g (fst (sweep_body_with_free_list g f_index fp)) /\
                              (objects2 (hd_address f_index) g == objects2 (hd_address f_index) (fst (sweep_body_with_free_list g f_index fp))) /\
                              (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word (fst (sweep_body_with_free_list g f_index fp)) x))) =
 let h_index = hd_address f_index in

 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white || c = blue) then 
 (
   let g' = colorHeader3 h_index g blue in
   assert (objects2 0UL g == objects2 0UL g');
   
   assert (Usize.v fp % Usize.v mword == 0);

   (*let hd_fp = hd_address fp in
   let fp_wz_sz = getWosize (read_word g' hd_fp) in
   let fp_wz_sz' = getWosize (read_word g hd_fp) in
   assert (fp_wz_sz == fp_wz_sz');
   let fp_color = getColor (read_word g' hd_fp) in
   assert (fp_color == blue);
   let fp_wz_sz_plus_one = Usize.add fp_wz_sz 1UL in
   let next_obj_offset = Usize.mul fp_wz_sz_plus_one mword in
   let next_obj = Usize.add fp next_obj_offset in*)

   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   
   let g1 = write_word g' fp f_index in
   write_word_heap_lemma g' f_index fp;
   assert (heap_remains_same_except_index_v_id fp g' (write_word g' fp f_index));
   write_word_to_blue_object_field_lemma g' fp  f_index;
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g1 x));
   assert (color_of_object1 h_index g1 == blue);
   assert ((color_of_object1 h_index g == white \/  color_of_object1 h_index g == blue) <==> color_of_object1 h_index g' == blue);
   assert (color_of_object1 h_index g' == blue <==> color_of_object1 h_index g1 == blue);
   assert ((color_of_object1 h_index g == white \/  color_of_object1 h_index g == blue) <==> color_of_object1 h_index g1 == blue);
   objects2_equal_lemma3 h_index g' g1;
   heap_remains_same_except_index_lemma h_index fp g g' g1;
   assert (heap_remains_same_except_index_v_id2 h_index fp g g1);
   assert (forall x. Seq.mem x (objects2 0UL g') /\ Usize.v x > Usize.v h_index ==> getColor (read_word g' x) == getColor (read_word g1 x));
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g1 x));
   assert (Usize.v h_index >= 0);
   objects2_equal_lemma3 h_index g g';
   assert (objects2 h_index g == objects2 h_index g');
   assert (objects2 h_index g' == objects2 h_index g1);
   objects_mem_h_index_lemma g h_index (objects2 h_index g) fp;
   well_formedness_first_field_lemma g f_index;
   well_formedness_first_field_lemma g fp;
   assert (forall x. Seq.mem x (objects2 h_index g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   assert (forall x. Seq.mem x (objects2 h_index g') /\ Usize.v x > Usize.v h_index ==> getColor (read_word g' x) == getColor (read_word g1 x));
   assert (forall x. Seq.mem x (objects2 h_index g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g1 x));
   assert (color_of_object1 (hd_address f_index) g == black <==> 
                              color_of_object1 (hd_address f_index) (fst (sweep_body_with_free_list g f_index fp)) == white);
   assert ((color_of_object1 (hd_address f_index) g == white \/  color_of_object1 (hd_address f_index) g == blue) <==>
                              color_of_object1 (hd_address f_index) (fst (sweep_body_with_free_list g f_index fp)) == blue);
   
   assert (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ Usize.v x > Usize.v (hd_address f_index) ==> 
                                        getColor (read_word g x) == getColor (read_word (fst (sweep_body_with_free_list g f_index fp)) x));
   
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v (hd_address f_index) ==> 
                                        getColor (read_word g x) == getColor (read_word (fst (sweep_body_with_free_list g f_index fp)) x));
   ()

  
 )
 else
 (
   assert (c == black);
   let g' = colorHeader3 h_index g white in
   assert (objects2 0UL g == objects2 0UL g');
   assert (objects2 0UL g == objects2 0UL g');
   assert (heap_remains_same_except_index_v_id h_index g g');
   
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   assert (color_of_object1 h_index g == black);
   assert (color_of_object1 h_index g' == white);
   assert (color_of_object1 h_index g == black <==> color_of_object1 h_index g' == white);
   assert (objects2 0UL g == objects2 0UL g');
   assert (Seq.mem h_index (objects2 0UL g));
   assert (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word g' x));
   objects2_equal_lemma3 h_index g g';
   assert (objects2 h_index g == objects2 h_index g');
   assert (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word (fst (sweep_body_with_free_list g f_index fp)) x));
   assert (heap_remains_same_except_index_v_id fp g' g');
   heap_remains_same_except_index_lemma h_index fp g g' g'; 
   assert (heap_remains_same_except_index_v_id2 h_index fp g g');
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   assert (objects2 h_index g == objects2 h_index g');
   assert (forall x. Seq.mem x (objects2 h_index g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   ()
 )

#restart-solver 

#restart-solver 

#restart-solver 

#push-options "--split_queries always"

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"


let objects2_property_lemma  (g:heap{(Seq.length (objects2 0UL g) > 0)})
                             (h_index:hp_addr{(Seq.length (objects2 h_index g) == 1)})
               : Lemma
                 (ensures ~(exists y. y <> h_index /\ Seq.mem y ((objects2 h_index g)))) = 
let s = objects2 h_index g in
assert (Seq.length (objects2 h_index g) > 0);
assert (Seq.length (objects2 h_index g) == 1);
assert (Seq.mem h_index (objects2 h_index g));
assert (~(exists y. y <> h_index /\ Seq.mem y ((objects2 h_index g))));
()

let objects2_property_lemma2  (g:heap{(Seq.length (objects2 0UL g) > 0)})
                              (h_index:hp_addr{(Seq.length (objects2 h_index g) > 0)})
               : Lemma
                 (ensures (forall x. Seq.mem x (objects2 h_index g) ==> Usize.v x >= Usize.v h_index)) = ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"
#push-options "--split_queries always"

#restart-solver

#restart-solver


val objects2_sweep_lemma3 : (h_index: hp_addr) ->
                            (g:heap{Seq.length (objects2 0UL g) > 0 /\
                                   Seq.mem h_index (objects2 0UL g)/\ 
                                  (Seq.length (objects2 h_index g) > 0)}) ->
                   Lemma
                   (ensures 
                   (let wz =  getWosize (read_word g h_index) in
                    let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                    let f_index_new =  Usize.add h_index_new mword in
                    Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g))))

val objects2_sweep_lemma4 : (h_index: hp_addr) ->
                           (g:heap{Seq.length (objects2 0UL g) > 0 /\
                                   Seq.mem h_index (objects2 0UL g)/\ 
                                  (Seq.length (objects2 h_index g) > 0)}) ->
                   Lemma
                   (requires 
                     (let wz =  getWosize (read_word g h_index) in
                     let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                     (~(Seq.mem h_index_new (objects2 h_index g)))))
                   
                   (ensures 
                     (let wz =  getWosize (read_word g h_index) in
                     let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                     let f_index_new =  Usize.add h_index_new mword in
                     Seq.length (objects2 h_index g) == 1))


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let rec sweep_with_free_list3 (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0)})
                             
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)/\ 
                                             (Seq.length (objects2 (hd_address f_index) g) > 0)
                              })
                             
                             (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                         color_of_object1 (hd_address fp) g == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
          
          : Tot (p:heap_heap_addr_pair{(Seq.length (objects2 0UL (fst p)) > 0) /\
                                       noGreyObjects (fst p) /\
                                       (Usize.v (snd p) >= Usize.v mword) /\
                                       (objects2 0UL g == objects2 0UL (fst p)) /\
                                       Seq.mem (hd_address (snd p)) (objects2 0UL (fst p)) /\
                                       color_of_object1 (hd_address (snd p)) (fst p) == blue /\
                                       (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word (fst p) x)) /\
                      
                                       (objects2 (hd_address f_index) g == objects2 (hd_address f_index) (fst p)) /\
                                       
                                       (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ color_of_object1 x g == black <==> 
                                             Seq.mem x (objects2 (hd_address f_index) (fst p)) /\ color_of_object1 x (fst p) == white) /\
                                           
                                       (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                                             Seq.mem x (objects2 (hd_address f_index) (fst p)) /\ color_of_object1 x (fst p) == blue) /\
                                       (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v (hd_address f_index) ==> 
                                             getColor (read_word g x) == getColor (read_word (fst p) x))}) 
           (decreases (heap_size - Usize.v f_index)) =

 let h_index = hd_address f_index in
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let f_index_new =  Usize.add h_index_new mword in
 wosize_plus_one_times_mword_multiple_of_mword wz;
 assert (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0);
 //assert (Usize.v h_index_new % Usize.v mword == 0);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index_new mword;

 assert (Usize.v (Usize.add h_index_new mword) % Usize.v mword == 0);
 assert (Usize.v f_index_new % Usize.v mword == 0);
 
 let g', fp' = sweep_body_with_free_list g f_index fp in
 sweep_body_with_free_list_lemma5 g f_index fp;
 assert (noGreyObjects g' /\ (Seq.length (objects2 0UL g') > 0));
 assert (Usize.v fp' >= Usize.v mword /\ 
        Seq.mem (hd_address fp') (objects2 0UL g') /\ 
        color_of_object1 (hd_address fp') g' == blue /\
       (forall x y. Seq.mem x (objects2 0UL g') /\ Seq.mem y (objects2 0UL g') ==>
                         Usize.v (getWosize (read_word g' x)) + Usize.v (getWosize (read_word g' y)) < heap_size));
 assert (Seq.mem (hd_address fp') (objects2 0UL g'));
 assert (color_of_object1 h_index g == white ==> color_of_object1 h_index g' == blue);
 assert (color_of_object1 h_index g == black ==> color_of_object1 h_index g' == white);
 assert (color_of_object1 h_index g == blue ==> color_of_object1 h_index g' == blue);
 assert (color_of_object1 h_index g' <> black);
 assert ((color_of_object1 h_index g == white \/  color_of_object1 h_index g == blue) <==>  color_of_object1 h_index g' == blue);
             
 assert (color_of_object1 h_index g == black <==> color_of_object1 h_index g' == white);
              
 assert (forall x. Seq.mem x (objects2 h_index g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
                                        
 assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x)); 
 if Usize.v f_index_new >= heap_size then
 (
   assert (objects2 (hd_address f_index) g == objects2 (hd_address f_index) g');
   objects2_cons_lemma2 h_index g;
   assert ((Seq.length (objects2 h_index g) > 0 /\ 
                        Usize.v (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) >= heap_size ==> 
                          Seq.length (objects2 h_index g) == 1));
   
   assert (Seq.mem h_index (objects2 0UL g));
   assert (Usize.v h_index + ((Usize.v (getWosize (read_word g h_index)) + 1) *  Usize.v mword) + Usize.v mword  == Usize.v f_index_new);
   assert (Usize.v h_index + ((Usize.v (getWosize (read_word g h_index)) + 1) *  Usize.v mword) == Usize.v h_index_new);
   assert (Usize.v f_index_new >= heap_size);
   assert (Seq.length (objects2 h_index g) > 0);
   objects2_sweep_lemma3 h_index g;
   assert (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g)));
   assert (~(Seq.mem h_index_new (objects2 h_index g)));
   objects2_sweep_lemma4 h_index g;
   assert (~(Seq.mem h_index_new (objects2 h_index g)) /\ (Seq.length (objects2 (hd_address f_index) g) > 0) ==> Seq.length (objects2 h_index g) == 1);
   assert (Seq.length (objects2 h_index g) == 1);
   assert (Seq.mem h_index (objects2 h_index g));
   objects2_property_lemma g h_index;
   assert (~(exists y.  y <> h_index /\ Seq.mem y ((objects2 h_index g))));
   assert (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ color_of_object1 x g == black <==> Seq.mem x (objects2 (hd_address f_index) g') /\ 
                                           color_of_object1 x g' == white);
   assert (forall x. Seq.mem x (objects2 h_index g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                               Seq.mem x (objects2 h_index g') /\ color_of_object1 x g' == blue);
   
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   (g',fp')
 )
 else
 (
   assert (Usize.v f_index_new < heap_size);
   assert (Usize.v f_index_new >= Usize.v mword);
   assert (UInt.fits (Usize.v f_index_new - Usize.v mword) Usize.n);

   assert (Seq.length (objects2 0UL g) > 0 /\ Seq.mem h_index (objects2 0UL g));
   objects2_mem_lemma1_app1 h_index g;
   assert (Seq.mem h_index_new (objects2 0UL g));
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   assert (h_index_new <> h_index);
   assert (Seq.mem h_index_new (objects2 0UL g'));
   
  
   assert (Usize.v f_index_new >= Usize.v mword); 
   //assert (Seq.mem h_index_new (objects2 0UL g'));
   assert (Usize.v f_index_new % Usize.v mword == 0);
   assert (Usize.v f_index_new < heap_size);
   assert (is_hp_addr f_index_new);
   assert (Usize.v h_index_new < heap_size);
   assert (Seq.length (objects2 0UL g') > 0);
   assert (noGreyObjects g' /\ (Seq.length (objects2 0UL g') > 0));
   assert ((Seq.length (objects2 h_index g') > 0) /\ (Usize.v h_index_new < heap_size));
   assert (Seq.length (objects2 0UL g') > 0);
   assert (Seq.mem  h_index (objects2 0UL g'));
   assert (Usize.v h_index_new == (Usize.v h_index +  (Usize.v (getWosize (read_word g h_index)) + 1) * Usize.v mword));
   objects2_length_lemma3 g' h_index h_index_new; 
   let g'',fp'' = sweep_with_free_list3 g' f_index_new fp' in
   objects2_equal_lemma3 h_index g' g'';
   objects2_cons_lemma1 h_index g h_index_new;
   objects2_cons_lemma1 h_index g' h_index_new;
   objects2_cons_lemma1 h_index g'' h_index_new;
   assert (Seq.length (objects2 h_index g) > 0 /\  Usize.v h_index_new < heap_size ==> 
                      ((objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g)) /\
                      (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g))));
                        
   assert (Seq.length (objects2 h_index g) > 0 /\  Usize.v h_index_new < heap_size);
                       
   assert (((objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g)) /\
            (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g))));
   
   assert (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)));

   assert (((objects2 h_index g') == Seq.cons h_index (objects2 h_index_new g')) /\
            (forall x. Seq.mem x (objects2 h_index g') <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g'))));

   assert (((objects2 h_index g'') == Seq.cons h_index (objects2 h_index_new g'')) /\
           (forall x. Seq.mem x (objects2 h_index g'') <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g''))));
   assert  (objects2 (hd_address f_index) g' == objects2 (hd_address f_index) g'');
   assert  (objects2 (hd_address f_index) g == objects2 (hd_address f_index) g');
   
   
   objects2_equal_lemma3 h_index_new g' g'';
   assert (forall x. Seq.mem x (objects2 h_index_new g') /\ color_of_object1 x g' == black <==> Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white);
   objects2_length_lemma3 g h_index h_index_new; 
   objects2_property_lemma2 g h_index_new;
   assert (forall x. Seq.mem x (objects2 h_index_new g) ==> Usize.v x >= Usize.v h_index_new);
   
   
   assert (forall x. Seq.mem x (objects2 h_index_new g) /\ color_of_object1 x g == black <==> Seq.mem x (objects2 h_index_new g') /\ color_of_object1 x g' == black);
   assert (forall x. Seq.mem x (objects2 h_index_new g) /\ color_of_object1 x g == black <==> Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white);

   
   
   
   assert (color_of_object1 h_index g == black <==> color_of_object1 h_index g'' == white);
   assert (forall x. (x == h_index /\  color_of_object1 x g == black) \/ (Seq.mem x (objects2 h_index_new g) /\ color_of_object1 x g == black) <==> 
                   (x == h_index /\  color_of_object1 x g'' == white) \/ (Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white));
   assert (forall x. (x == h_index \/ Seq.mem x (objects2 h_index_new g)) /\ color_of_object1 x g == black <==> 
                   (x == h_index \/ Seq.mem x (objects2 h_index_new g'')) /\ color_of_object1 x g'' == white);
   assert (forall x. Seq.mem x (objects2 h_index g) /\ color_of_object1 x g == black <==> 
                   Seq.mem x (objects2 h_index g'') /\ color_of_object1 x g'' == white);
   
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index_new ==> getColor (read_word g' x) == getColor (read_word g'' x));
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x)); 
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g'' x));
   (g'',fp'')
 )



#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

#restart-solver 

let sweep_with_free_list3_heap_lemma (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0)})
                                     (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                         color_of_object1 (hd_address fp) g == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)}) 
                         : Lemma
                           (requires (let f_index = mword in
                                      let h_index = hd_address f_index in
                                      let wz =  getWosize (read_word g h_index) in
                                      let h_index_new = Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword)  in
                                      let f_index_new =  Usize.add h_index_new mword in
                                       (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g))) /\
                                       (~(Seq.mem h_index_new (objects2 h_index g)) /\ (Seq.length (objects2 (hd_address f_index) g) > 0) ==> Seq.length (objects2 h_index g) == 1)))
                           
                           (ensures(let g1,_ = sweep_with_free_list3 g mword fp in
                           
                                   (forall x. Seq.mem x (objects2 0UL g1) ==>  
                                             color_of_object1 x g1 == white \/  color_of_object1 x g1 == blue) /\
                                   (forall x. Seq.mem x (get_allocated_block_addresses g1) <==> Seq.mem x (objects2 0UL g1) /\
                                   (color_of_object1 x g1 == white)))) =
  let f_index = mword in
  let s = objects2 0UL g in
  assert (Usize.v mword >= Usize.v mword);
  let h_index = hd_address f_index in
  assert (h_index == 0UL);
  assert (Seq.mem (hd_address f_index) (objects2 0UL g));
  assert (Seq.length (objects2 (hd_address f_index) g) > 0);
  let wz =  getWosize (read_word g h_index) in
  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
  let f_index_new =  Usize.add h_index_new mword in
  let g1, fp1 = sweep_with_free_list3 g f_index fp in
  assert (noGreyObjects g1);
  assert (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                                             Seq.mem x (objects2 (hd_address f_index) g1) /\ color_of_object1 x g1 == blue);
  
  assert (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ color_of_object1 x g == black <==> 
                                             Seq.mem x (objects2 (hd_address f_index) g1) /\ color_of_object1 x g1 == white);
  
  assert (forall x. Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                                             Seq.mem x (objects2 0UL g1) /\ color_of_object1 x g1 == blue);
  
  assert (forall x. Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == black <==> 
                                             Seq.mem x (objects2 0UL g1) /\ color_of_object1 x g1 == white);
  
  
  objects2_color_lemma 0UL g;
  assert (forall x. Seq.mem x (objects2 h_index g) ==> ~(color_of_object1 x g == gray));
  assert (forall x. Seq.mem x (objects2 h_index g) ==> color_of_object1 x g == white \/ color_of_object1 x g == black \/ color_of_object1 x g == blue);
  assert (forall x. Seq.mem x (objects2 h_index g1) ==> color_of_object1 x g1 == blue \/ color_of_object1 x g1 == white);
  assert (forall x. Seq.mem x (objects2 0UL g1) ==>  color_of_object1 x g1 == white \/  color_of_object1 x g1 == blue);
  let allocs = get_allocated_block_addresses g1 in
  assert (forall x. Seq.mem x allocs <==> Seq.mem x (objects2 0UL g1) /\
                                   (color_of_object1 x g1 == white \/
                                   color_of_object1 x g1 == black \/
                                   color_of_object1 x g1 == gray));
  assert (forall x. Seq.mem x (objects2 h_index g1) ==> ~(color_of_object1 x g1 == black));

  assert (forall x. Seq.mem x allocs <==> Seq.mem x (objects2 0UL g1) /\
                                   (color_of_object1 x g1 == white));
  ()

let root_props (g:heap{well_formed_heap2 g})
               (root_set: seq Usize.t ) =
     G.is_vertex_set root_set /\
     (forall x. Seq.mem x root_set ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
     (forall x. Seq.mem x root_set ==> Usize.v x % Usize.v mword == 0)

let f_id (f:Usize.t) =
     (Usize.v f >= Usize.v mword /\ Usize.v f < heap_size) /\
     (Usize.v f % Usize.v mword == 0)  

#restart-solver

#restart-solver




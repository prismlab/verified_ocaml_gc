module Spec.GC_part06

include Spec.GC_part05

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

let create_edge_pairs_for_h_index_length_mem_lemma (g:heap{well_formed_heap2 g}) 

                                                   (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                   (wz: wosize{valid_wosize g h_index wz})
                         
                               : Lemma
                               (ensures (
                                         (forall (x:G.edge). Seq.mem x (create_edge_pairs_for_h_index g h_index wz 1UL) ==> 
                                                                                is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                                is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                                Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                                Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                                         (forall (x:G.edge). Seq.mem x (create_edge_pairs_for_h_index g h_index wz 1UL) ==> 
                                                        (hd_address (fst x) == h_index) /\
                                                        (fst x == f_address h_index)) /\
                                                        Seq.length (create_edge_pairs_for_h_index g h_index wz 1UL) <= Usize.v wz)) = 
let e = create_edge_pairs_for_h_index g h_index wz 1UL in
create_edge_pairs_for_h_index_length_lemma g h_index wz 1UL;
assert (Seq.length (create_edge_pairs_for_h_index g h_index wz 1UL) <= Usize.v wz);
()

#restart-solver 

#restart-solver 


let success_fn_test (i:Usize.t)
                    (e:seq (G.edge){(forall x. Seq.mem x e ==> fst x == i)}) =
  let s = G.successors_fn2 i e in
  assert (forall x. Seq.mem x s <==> Seq.mem (i,x) e);
  G.successors_fn2_pick_second_lemma i e;
  assert (G.pick_second e == s);
  ()

#restart-solver 

let within_heap_all (f: seq Usize.t)
 = (forall x. Seq.mem x f ==> Usize.v x < heap_size)

let multiple_of_mword_all (f: seq Usize.t)
=  (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0)

let all_valid_headers (f: seq Usize.t)
                      (g:heap{well_formed_heap2 g})=
 (forall x. Seq.mem x f ==> is_valid_header1 x g)

let all_objects_and_their_field_pointers_are_within_heap_size (f: seq Usize.t)
                                                              (g:heap{well_formed_heap2 g})=
 (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                      is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)

let all_field_address_are_word_aligned (f: seq Usize.t)
                                       (g:heap{well_formed_heap2 g})=
  (forall x. Seq.mem x f ==> (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))

let all_mem_of_allocated_blocks (f: seq Usize.t)
                                (g:heap{well_formed_heap2 g}) =
 (forall x. Seq.mem x f ==> Seq.mem x (get_allocated_block_addresses g))

#restart-solver 


#restart-solver

let can_be_shifted_forward (f: seq Usize.t)
  = forall x. mem x f ==> Usize.v x + Usize.v mword < heap_size

let can_be_shifted_backward (f: seq Usize.t)
  = forall x. mem x f ==> Usize.v x > 0

#restart-solver

#restart-solver

let edge_fst_snd_hdr_mem_allocs (g:heap{well_formed_heap2 g})
                                (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                                (f': seq (G.edge)) =
 (forall (x:G.edge). Seq.mem x f' ==> is_hp_addr (fst x) /\  Usize.v (fst x) >= Usize.v mword /\
                                 is_hp_addr (snd x) /\  Usize.v (snd x) >= Usize.v mword /\
                                 Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                 Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
 (forall (x:G.edge). Seq.mem x f' ==> Seq.mem (hd_address (fst x)) f)

let edge_graph_succ_connect (g:heap{well_formed_heap2 g})
                            (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                            (f': seq (G.edge)) =
  (forall x. Seq.mem x f  /\ (Usize.v (tag_of_object1 x g) < no_scan_tag) ==> G.successors_fn2 (f_address x) f' == 
                                                                       G.successors_fn2 (f_address x) 
                                                                                  (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL)) /\
  
                                                                                                                 
  (forall x. Seq.mem x f  /\ (Usize.v (tag_of_object1 x g) >= no_scan_tag) ==> G.successors_fn2 (f_address x) f' ==  Seq.empty #UInt64.t)

#restart-solver

#reset-options "--z3rlimit 500"


let edge_graph_succ_connect1 (g:heap{well_formed_heap2 g})
                            (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                            (f': seq (G.edge)) =
  (forall (x:Usize.t{Seq.mem x f}). G.successors_fn2 (f_address x) f' == (
                                                                      if (Usize.v (tag_of_object1 x g) < no_scan_tag) then
                                                                        G.successors_fn2 (f_address x) 
                                                                                  (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL)
                                                                      else
                                                                        Seq.empty #UInt64.t
                                                                    ) )   

#restart-solver 

#restart-solver 

let hp_addr_all (f: seq Usize.t)
=  (forall x. Seq.mem x f ==> is_hp_addr x)

#restart-solver 

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq' --split_queries always"

let edge_graph_succ_connect_closure_objs (g:heap{well_formed_heap2 g})
                            (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                            (f': seq (G.edge)) =
   (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) < no_scan_tag) ==>  (Usize.v (tag_of_object1 x g) == closure_tag) ==> 
    ( let f_id = f_address x in
      let start_of_env = start_env_clos_info g f_id in
      let start_env_plus_one = Usize.add start_of_env 1UL in
      let e' = create_edge_pairs_for_h_index g x (getWosize (read_word g x)) start_env_plus_one in
      (G.successors_fn2 (f_address x) f' ==  G.successors_fn2 (f_address x) e')))
      

let edge_graph_succ_connect3 (g:heap{well_formed_heap2 g})
                            (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                            (f': seq (G.edge)) =
  
 
 edge_graph_succ_connect_closure_objs g f f' /\
 (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) < no_scan_tag) ==>  (Usize.v (tag_of_object1 x g) <> closure_tag) ==> 
    G.successors_fn2 (f_address x) f' ==  G.successors_fn2 (f_address x) (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL)) /\
  (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) >= no_scan_tag) ==>
    G.successors_fn2 (f_address x) f' ==  Seq.empty #UInt64.t)      
                                                                                                                                 
#restart-solver

#restart-solver 

let f_address_lemma (tl:seq Usize.t)
                    (hd:hp_addr{Usize.v hd + Usize.v mword < heap_size})
           : Lemma
             (requires (forall y. Seq.mem y tl ==> hd <> y))
             (ensures (forall y. Seq.mem y tl ==> f_address hd <> f_address y)) = ()

#restart-solver 

let can_shift_forward_lemma (f: seq Usize.t)
                            (g:heap{well_formed_heap2 g})
                            (hd: hp_addr{Seq.mem hd f})
              : Lemma
                (requires all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g)
                (ensures (Usize.v hd + Usize.v mword < heap_size)) = ()

#restart-solver

#restart-solver

#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver

#reset-options "--z3rlimit 1000 --split_queries always"

let seq_empty_lemma ()
            : Lemma
              (ensures (Seq.length (Seq.empty #G.edge) == 0) /\ 
                       (~(exists x. Seq.mem x (Seq.empty #G.edge)))) = ()

let seq_empty_lemma1  (f: seq Usize.t)
            : Lemma
              (requires Seq.length f == 0)
              (ensures (~(exists x. Seq.mem x f))) = ()


let seq_non_empty_lemma (f: seq Usize.t)
            : Lemma
              (requires ~(Seq.length f == 0))
              (ensures (Seq.length f > 0) /\
                       (Seq.mem (Seq.head f) f) /\
                       (forall x. Seq.mem x (Seq.tail f) ==> Seq.mem x f) /\
                        (Seq.length (Seq.tail f) < Seq.length f) /\
                        Seq.cons (Seq.head f) (Seq.tail f) == f /\
                        (forall x.Seq.mem x f ==> (x == Seq.head f) \/
                                            Seq.mem x (Seq.tail f))) = ()

let length_fn (f: seq Usize.t) =
   Seq.length f

let length_fn_lemma (f: seq Usize.t{length_fn f > 0}) 
     : Lemma
       (length_fn f > length_fn (Seq.tail f)) = ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"
#push-options "--split_queries always"

#restart-solver

#restart-solver

#restart-solver

let rec create_edge_list_from_heap1   (g:heap{well_formed_heap2 g})
                                      (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                       : Tot
                         (f': seq (G.edge){edge_fst_snd_hdr_mem_allocs g f f' /\ edge_graph_succ_connect3 g f f'})
                         (decreases (*(Seq.length f)*) length_fn f) = 
if length f = 0 then 
 (
   let e = Seq.empty #G.edge in
   seq_empty_lemma ();
   assert (forall (x:G.edge). Seq.mem x e ==> is_hp_addr (fst x) /\  Usize.v (fst x) >= Usize.v mword /\
                                 is_hp_addr (snd x) /\  Usize.v (snd x) >= Usize.v mword /\
                                 Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                 Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
   
   assert (edge_fst_snd_hdr_mem_allocs g f e);
   
   seq_empty_lemma1 f;
   assert (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) >= no_scan_tag) ==>
           G.successors_fn2 (f_address x) e ==  Seq.empty #UInt64.t);
   
   assert (edge_graph_succ_connect3 g f e);
   e
 )
 else
 (
   
   seq_non_empty_lemma f;
   let hd = Seq.head f in
   assert (is_hp_addr hd);
   can_shift_forward_lemma f g hd;
   assert (Usize.v hd + Usize.v mword < heap_size);
   let tl = Seq.tail f in
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));
   
   assert (Seq.length f > Seq.length tl);
   assert (Seq.length f > Seq.length (Seq.tail f));
   length_fn_lemma f;
   assert (length_fn f > length_fn (Seq.tail f));
   assert (length_fn f > length_fn tl);
   
   let rest_of_f = create_edge_list_from_heap1 g tl in
   assert (forall (x:G.edge). Seq.mem x rest_of_f ==> Seq.mem (hd_address (fst x)) tl);
  

   assert (~(exists (x:G.edge). Seq.mem x rest_of_f /\ (hd_address (fst x)) == hd));
   assert (edge_graph_succ_connect3 g tl rest_of_f);

   let tg = tag_of_object1 hd g in
   if (Usize.v tg < no_scan_tag) then 
   (
     let wz = getWosize (read_word g hd) in
     let f_id = f_address hd in
     f_address_lemma tl hd;
     assert (forall y. Seq.mem y tl ==> f_address hd <> f_address y);
     assert (hd_address f_id == hd);
     if (Usize.v tg = closure_tag) then
     (
       assert (Usize.v wz >= 2);
       assert (Usize.v f_id >= Usize.v mword);
       assert (is_valid_header hd g);
       assert (is_valid_header (hd_address f_id) g);
       assert (Usize.v (tag_of_object1 (hd_address f_id) g) == closure_tag);
       let start_env = start_env_clos_info g f_id in
       let start_env_plus_one = Usize.add start_env 1UL in

       assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address f_id) g)) /\
             Usize.v start_env >= 1);
       let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz start_env_plus_one in
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> 
                                                        is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                        is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                        Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                        Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
                                                        
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (hd_address (fst x)) == hd);
       
   
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (fst x == f_id));
       assert (~(Seq.mem hd tl));
       assert (forall y. Seq.mem y tl ==> hd <> y);
       
       assert (forall (x:G.edge) y. Seq.mem y tl /\ Seq.mem x edge_pairs_for_hd ==> (fst x <> f_address y));
       //assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
       G.successors_fn2_pick_second_lemma f_id edge_pairs_for_hd;
   
       assert (G.successors_fn2 f_id edge_pairs_for_hd == G.pick_second edge_pairs_for_hd);
       let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
       Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
   
       assert (~(exists (x:G.edge). Seq.mem x rest_of_f /\ (fst x) == f_id));
       G.successors_fn2_e2_is_successors_fn2_e_if_no_fst_i_in_e1 f_id (edge_pairs_for_hd) (rest_of_f) f';
       assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (edge_pairs_for_hd));
       assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (create_edge_pairs_for_h_index g hd 
                                                                                          (getWosize (read_word g hd))
                                                                                          start_env_plus_one));
       assert (cons hd tl == f);
       assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
       G.successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e'' tl (edge_pairs_for_hd) (rest_of_f) f';
       assert (forall x. Seq.mem x tl ==> (G.successors_fn2 (f_address x) f' == G.successors_fn2 (f_address x) (rest_of_f)));
       assert (forall x. Seq.mem x f ==> x == hd \/ Seq.mem x tl);
       assert (edge_fst_snd_hdr_mem_allocs g f f');
       assert (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) >= no_scan_tag) ==>
               G.successors_fn2 (f_address x) f' ==  Seq.empty #UInt64.t);
       assert (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) < no_scan_tag) ==>  (Usize.v (tag_of_object1 x g) <> closure_tag) ==> 
               G.successors_fn2 (f_address x) f' ==  G.successors_fn2 (f_address x) (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL));
       assert (edge_graph_succ_connect_closure_objs g f f');
       assert (edge_graph_succ_connect3 g f f');
       f'
     )
     else
     (
       let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz 1UL in
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> 
                                                        is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                        is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                        Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                        Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
                                                        
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (hd_address (fst x)) == hd);
       
   
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (fst x == f_id));
       assert (~(Seq.mem hd tl));
       assert (forall y. Seq.mem y tl ==> hd <> y);
       
       assert (forall (x:G.edge) y. Seq.mem y tl /\ Seq.mem x edge_pairs_for_hd ==> (fst x <> f_address y));
       //assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
       G.successors_fn2_pick_second_lemma f_id edge_pairs_for_hd;
   
       assert (G.successors_fn2 f_id edge_pairs_for_hd == G.pick_second edge_pairs_for_hd);
       let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
       Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
   
       assert (~(exists (x:G.edge). Seq.mem x rest_of_f /\ (fst x) == f_id));
       G.successors_fn2_e2_is_successors_fn2_e_if_no_fst_i_in_e1 f_id (edge_pairs_for_hd) (rest_of_f) f';
       assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (edge_pairs_for_hd));
       assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (create_edge_pairs_for_h_index g hd 
                                                                                          (getWosize (read_word g hd))
                                                                                          1UL));
       assert (cons hd tl == f);
       assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
       G.successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e'' tl (edge_pairs_for_hd) (rest_of_f) f';
       assert (forall x. Seq.mem x tl ==> (G.successors_fn2 (f_address x) f' == G.successors_fn2 (f_address x) (rest_of_f)));
       assert (edge_fst_snd_hdr_mem_allocs g f f');
       assert (forall x. Seq.mem x tl  ==> (Usize.v (tag_of_object1 x g) < no_scan_tag) ==>  (Usize.v (tag_of_object1 x g) <> closure_tag) ==> 
               G.successors_fn2 (f_address x) f' ==  G.successors_fn2 (f_address x) (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL));
       assert (forall x. Seq.mem x f ==> x == hd \/ Seq.mem x tl);
       assert (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) < no_scan_tag) ==>  (Usize.v (tag_of_object1 x g) <> closure_tag) ==> 
               G.successors_fn2 (f_address x) f' ==  G.successors_fn2 (f_address x) (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL));
       assert (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) >= no_scan_tag) ==>
               G.successors_fn2 (f_address x) f' ==  Seq.empty #UInt64.t);
       assert (edge_graph_succ_connect_closure_objs g f f');
       assert (edge_graph_succ_connect3 g f f');
       f'
     )
   )
   else
   (
     (*branch type checked when other branches are commented out*)
     let edge_pairs_for_hd = Seq.empty #G.edge in
     seq_empty_lemma ();
     assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (hd_address (fst x)) == hd);
     assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> 
                                                        is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                        is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                        Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                        Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
     
     assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> is_hp_addr (fst x) /\  Usize.v (fst x) >= Usize.v mword /\
                                                           is_hp_addr (snd x) /\  Usize.v (snd x) >= Usize.v mword /\
                                                           Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                           Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
     let f_id = f_address hd in
     assert (hd_address f_id == hd);
   
     assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (fst x == f_id));
     assert (~(Seq.mem hd tl));
     assert (forall y. Seq.mem y tl ==> hd <> y);
     f_address_lemma tl hd;
     assert (forall y. Seq.mem y tl ==> f_address hd <> f_address y);
    
     //assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
    
     G.successors_fn2_pick_second_lemma f_id edge_pairs_for_hd;
   
     assert (G.successors_fn2 f_id edge_pairs_for_hd == G.pick_second edge_pairs_for_hd);
     let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
     Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
   
     assert (~(exists (x:G.edge). Seq.mem x rest_of_f /\ (fst x) == f_id));
     G.successors_fn2_e2_is_successors_fn2_e_if_no_fst_i_in_e1 f_id (edge_pairs_for_hd) (rest_of_f) f';
     assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (edge_pairs_for_hd));
     assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (Seq.empty #G.edge));
     assert (cons hd tl == f);
     assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
     G.successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e'' tl (edge_pairs_for_hd) (rest_of_f) f';
     assert (forall x. Seq.mem x tl ==> (G.successors_fn2 (f_address x) f' == G.successors_fn2 (f_address x) (rest_of_f)));
     assert (append (edge_pairs_for_hd) (rest_of_f) == f');
     assert (edge_fst_snd_hdr_mem_allocs g tl rest_of_f);
     Seq.append_empty_l rest_of_f;
     assert (f' == rest_of_f);
     assert (edge_fst_snd_hdr_mem_allocs g tl rest_of_f);
     assert (edge_fst_snd_hdr_mem_allocs g f f');
     assert (forall x. Seq.mem x f ==> x == hd \/ Seq.mem x tl);
     assert (edge_graph_succ_connect_closure_objs g f f');
     assert (edge_graph_succ_connect3 g f f');
     f'
   )
)

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver 

let rec first_field_addresses_of_allocated_blocks   (g:heap{well_formed_heap2 g})
                                                    (f: seq Usize.t 
                                                      { 
                                                       (all_mem_of_allocated_blocks f g) /\
                                                       (within_heap_all f) /\
                                                       (multiple_of_mword_all f) /\
                                                       (all_valid_headers f g) /\
                                                       (G.is_vertex_set f) /\
                                                       (all_objects_and_their_field_pointers_are_within_heap_size f g) /\
                                                       (all_field_address_are_word_aligned f g) /\
                                                       (can_be_shifted_forward f)
                                                       }
                                                     ) 
                       : Tot (f':seq Usize.t{(within_heap_all f') /\
                                             (multiple_of_mword_all f') /\
                                             (can_be_shifted_backward f')  /\
                                             (forall x. Seq.mem x f' <==> Seq.mem (hd_address x) f) /\
                                             (forall x. Seq.mem x f <==> Seq.mem (f_address x) f') /\
                                             (Seq.length f == Seq.length f') /\
                                             (G.is_vertex_set f') /\
                                             (forall x. Seq.mem x f' ==> Seq.mem (hd_address x) (get_allocated_block_addresses g))}) 
                         (decreases Seq.length f) = 

if length f = 0 then 
 (
   let f' = Seq.empty #Usize.t in
   G.is_vertex_set_lemma1 f';
   f'
 )
 else
 (
   let hd = Seq.head f in
   let tl = Seq.tail f in
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));
   
   let rest_of_f = first_field_addresses_of_allocated_blocks g tl in
  
   let f_id = f_address hd in
   assert (hd_address f_id == hd);

   lemma_tl f_id rest_of_f;
   let f' = Seq.cons f_id rest_of_f in
   assert (within_heap_all f);
   assert (within_heap_all rest_of_f);
   assert (within_heap_all f');
   let hd' = Seq.head f' in
   let tl' = Seq.tail f' in
   assert (hd' == f_id);
   assert (tl' == rest_of_f);
   assert (~(mem (head f') (tail f')));
   G.is_vertex_set_cons f_id rest_of_f;
   assert (G.is_vertex_set f');
   assert (forall x. Seq.mem x f' <==> Seq.mem (hd_address x) f);
   assert (forall x. Seq.mem x f <==> Seq.mem (f_address x) f');
   assert (can_be_shifted_backward f');
   assert (forall x. Seq.mem x f' ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));
   f'
  )

#restart-solver 

#restart-solver                                             
                         
let rec first_field_addresses_of_allocated_blocks_lemma   (g:heap{well_formed_heap2 g})
                                                          (f: seq Usize.t 
                                                             { 
                                                               (all_mem_of_allocated_blocks f g) /\
                                                               (within_heap_all f) /\
                                                               (multiple_of_mword_all f) /\
                                                               (all_valid_headers f g) /\
                                                               (G.is_vertex_set f) /\
                                                               (all_objects_and_their_field_pointers_are_within_heap_size f g) /\
                                                               (all_field_address_are_word_aligned f g) /\
                                                               (can_be_shifted_forward f)
                                                             }
                                                           )
                                                           (g':heap{well_formed_heap2 g'})
                                                           (f': seq Usize.t 
                                                             { 
                                                               (all_mem_of_allocated_blocks f' g') /\
                                                               (within_heap_all f') /\
                                                               (multiple_of_mword_all f') /\
                                                               (all_valid_headers f' g') /\
                                                               (G.is_vertex_set f') /\
                                                               (all_objects_and_their_field_pointers_are_within_heap_size f' g') /\
                                                               (all_field_address_are_word_aligned f' g') /\
                                                               (can_be_shifted_forward f')
                                                             }
                                                           )
                            : Lemma
                              (requires f == f')
                              (ensures first_field_addresses_of_allocated_blocks g f == first_field_addresses_of_allocated_blocks g' f') 
                              (decreases Seq.length f) =
if length f = 0 then 
 (
   let f' = Seq.empty #Usize.t in
   G.is_vertex_set_lemma1 f';
   ()
 )
 else
 (
   let hd = Seq.head f in
   let tl = Seq.tail f in
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));

   let hd' = Seq.head f' in
   let tl' = Seq.tail f' in
   G.is_vertex_set_lemma f';
   assert (G.is_vertex_set tl');
   
   G.is_vertex_set_lemma4 f';
   assert (~(Seq.mem hd tl'));
   let rest_of_f = first_field_addresses_of_allocated_blocks g tl in
   
   assert (tl == tl');
   assert (hd == hd');
   assert ((all_mem_of_allocated_blocks tl' g') /\
                                                               (within_heap_all tl') /\
                                                               (multiple_of_mword_all tl') /\
                                                               (all_valid_headers tl' g') /\
                                                               (G.is_vertex_set tl') /\
                                                               (all_objects_and_their_field_pointers_are_within_heap_size tl' g') /\
                                                               (all_field_address_are_word_aligned tl' g'));
   
   assert (can_be_shifted_forward tl');
   let rest_of_f' = first_field_addresses_of_allocated_blocks g' tl' in
   
   first_field_addresses_of_allocated_blocks_lemma g tl g' tl';
   
   assert (rest_of_f == rest_of_f');
  
   let f_id = f_address hd in
   let f_id' = f_address hd' in
   assert (hd_address f_id == hd);
   assert (f_id == f_id');

   lemma_tl f_id rest_of_f;
   let f1 = Seq.cons f_id rest_of_f in
   
   lemma_tl f_id' rest_of_f';
   let f2 = Seq.cons f_id' rest_of_f' in

   assert (f1 == f2);
   ()
 )

#reset-options "--z3rlimit 1000"

#restart-solver

#restart-solver

let create_edge_list_for_graph (g:heap{well_formed_heap2 g}) 
               : Tot
                 (f': seq (G.edge){(forall (x:G.edge). Seq.mem x f' ==> is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                   is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                   Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                   Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g))}) =
let allocs = get_allocated_block_addresses g in
  assert ((forall x. Seq.mem x allocs ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                       (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                       (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                       (forall x. Seq.mem x allocs ==> is_valid_header x g) /\
                                                       (G.is_vertex_set allocs));
  assert (forall x. Seq.mem x allocs ==> is_fields_within_limit1 x (getWosize (read_word g x)));
  assert (forall x. Seq.mem x allocs ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
  fieldaddress_within_limits_lemma_x_all g;
  assert (forall x. Seq.mem x allocs ==> (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0));
  let f' = create_edge_list_from_heap1 g allocs in
  assert (forall (x:G.edge). Seq.mem x f' ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                           is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                           Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                           Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));                                               
                                                                   
                                                                    
                                           
  f'

let create_graph_from_heap (g:heap {well_formed_heap2 g}) 
                   : Pure (G.graph_state #unit #unit)
                    (requires all_field_address_are_word_aligned (get_allocated_block_addresses g) g)
                    (ensures fun f -> (G.is_vertex_set f.vertices) /\
                                   (Seq.equal (f.vertices) (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)))) = 
let f = get_allocated_block_addresses g in 
  assert ((all_mem_of_allocated_blocks f g) /\
          (within_heap_all f) /\
          (multiple_of_mword_all f) /\
          (all_valid_headers f g) /\
          (G.is_vertex_set f));
  assert (can_be_shifted_forward f);
  fieldaddress_within_limits_lemma_x_all g;
  assert (all_objects_and_their_field_pointers_are_within_heap_size f g);
  assert (all_field_address_are_word_aligned f g);                                               
  let ff_allocs = first_field_addresses_of_allocated_blocks g f in  
  assert (forall x. Seq.mem x ff_allocs ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));
  let e = create_edge_list_for_graph g in
  
  assert (forall x. Seq.mem x f <==> Seq.mem (f_address x) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (hd_address (fst x)) f);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (f_address (hd_address (fst x))) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (fst x) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (hd_address (snd x)) f);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (f_address (hd_address (snd x))) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (snd x) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (fst x) ff_allocs /\
                                       Seq.mem (snd x) ff_allocs);
  {
    vertices  = ff_allocs;
    edge_set  = e;
  }

#restart-solver 

#restart-solver 

#push-options "--z3rlimit 500"

#restart-solver

let create_edge_pairs_for_h_index_length_mem_lemma1 (g:heap{well_formed_heap2 g}) 

                                                    (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                    (wz: wosize{valid_wosize g h_index wz})
                                                    (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                         
                               : Lemma
                               (ensures (
                                         (forall (x:G.edge). Seq.mem x (create_edge_pairs_for_h_index g h_index wz i) ==> 
                                                                                is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                                is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                                Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                                Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                                         (forall (x:G.edge). Seq.mem x (create_edge_pairs_for_h_index g h_index wz i) ==> 
                                                        (hd_address (fst x) == h_index) /\
                                                        (fst x == f_address h_index)) /\
                                                        Seq.length (create_edge_pairs_for_h_index g h_index wz i) <= (Usize.v wz + 1) - Usize.v i)) = 
let e = create_edge_pairs_for_h_index g h_index wz i in
create_edge_pairs_for_h_index_length_lemma g h_index wz i;
()

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver


#restart-solver

#push-options "--split_queries always"

#restart-solver

#reset-options "--z3rlimit 1000"

let graph_successors_mem_lemma (g: heap {well_formed_heap2 g })
                               (h_index:hp_addr{is_valid_header1 h_index g})
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g))
                                  (ensures (forall x. Seq.mem x  (G.successors (create_graph_from_heap g) (f_address h_index)) ==> 
                                                         Seq.mem (hd_address x) (get_allocated_block_addresses g))) = 
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
 
 assert (forall x. Seq.mem x allocs  ==>(Usize.v (tag_of_object1 x g) >= no_scan_tag) ==> 
              G.successors_fn2 (f_address x) (create_edge_list_from_heap1 g allocs) ==  Seq.empty #UInt64.t);

 if (Usize.v tg < no_scan_tag) then 
 (
    if (Usize.v tg = closure_tag) then
    (
      let start_env = start_env_clos_info g f_h_index in
      let start_env_plus_one = Usize.add start_env 1UL in
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) start_env_plus_one in 
      create_edge_pairs_for_h_index_length_mem_lemma1 g h_index (getWosize (read_word g h_index)) start_env_plus_one;
      G.pick_second_mem_lemma grph h_index_edge_list;
      ()
    )
    else
    (
      
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL in 
      G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;
      create_edge_pairs_for_h_index_length_mem_lemma g h_index (getWosize (read_word g h_index));
      G.pick_second_mem_lemma grph h_index_edge_list;
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

#reset-options "--z3rlimit 100"


let length_empty_lemma (s:seq UInt64.t)
                : Lemma
                  (requires s == Seq.empty)
                  (ensures (Seq.length s == 0)) = ()
                  
let mem_empty_lemma (s:seq UInt64.t)
              : Lemma
                (requires s == Seq.empty)
                (ensures (~(exists x. Seq.mem x s))) = ()

let cons_mem_property_lemma (s:seq UInt64.t)
                            (elem: UInt64.t)
               : Lemma
                 (requires (forall x. Seq.mem x s ==> Usize.v x > 0 /\ Usize.v x < heap_size) /\
                           (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0) /\
                           (forall x. Seq.mem x s ==> is_hp_addr x) /\
                           
                           (Usize.v elem > 0 /\ Usize.v elem < heap_size) /\
                           (Usize.v elem % Usize.v mword == 0) /\
                           (is_hp_addr elem))
                (ensures ( (forall x. Seq.mem x (cons elem s) ==> Usize.v x > 0 /\ Usize.v x < heap_size) /\
                           (forall x. Seq.mem x (cons elem s) ==> Usize.v x % Usize.v mword == 0) /\
                           (forall x. Seq.mem x (cons elem s) ==> is_hp_addr x))) =
                           
 mem_cons elem s;
 ()

#push-options "--z3rlimit 1000"

#restart-solver

let cons_length_lemma (s:seq Usize.t)
                      (s_cons:Usize.t)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s)) == Seq.length s + 1)=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ; 
 ()


#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"


#restart-solver

#restart-solver

#restart-solver

#restart-solver

let graph_successors_length_lemma (g: heap {well_formed_heap2 g})
                                  (h_index:hp_addr{is_valid_header1 h_index g})
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g))
                                  (ensures (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= 
                                                Usize.v (getWosize (read_word g h_index)))) =
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
 
 assert (forall x. Seq.mem x allocs  ==>(Usize.v (tag_of_object1 x g) >= no_scan_tag) ==> 
              G.successors_fn2 (f_address x) (create_edge_list_from_heap1 g allocs) ==  Seq.empty #UInt64.t);

 if (Usize.v tg < no_scan_tag) then 
 (
    if (Usize.v tg = closure_tag) then
    (
      let start_env = start_env_clos_info g f_h_index in
      let start_env_plus_one = Usize.add start_env 1UL in
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) start_env_plus_one in 
      G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;
      create_edge_pairs_for_h_index_length_mem_lemma1 g h_index (getWosize (read_word g h_index)) start_env_plus_one;
      G.pick_second_length_lemma h_index_edge_list;
      
      assert (Usize.v start_env >= 1);
      assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address f_h_index) g)));  
      assert (wosize_of_object1 (hd_address f_h_index) g == getWosize (read_word g (hd_address f_h_index)));
      assert (hd_address f_h_index == h_index);
      assert (wosize_of_object1 (hd_address f_h_index) g == getWosize (read_word g h_index));
      
      assert (Seq.length h_index_edge_list <=  Usize.v (getWosize (read_word g h_index)));
      assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs));
      assert (edge_graph_succ_connect3 g allocs (create_edge_list_from_heap1 g allocs));
      assert (G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs) == G.successors_fn2 f_h_index h_index_edge_list);
      assert (Seq.length (G.successors_fn2 f_h_index h_index_edge_list) == Seq.length h_index_edge_list);
      assert (Seq.length (G.successors_fn2 f_h_index h_index_edge_list) <= Usize.v (getWosize (read_word g h_index)));
      assert (Seq.length (G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs)) <= Usize.v (getWosize (read_word g h_index)));
      assert (Seq.length (G.successors grph f_h_index) <= Usize.v (getWosize (read_word g h_index)));
      ()
    )
    else
    (
      
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL in 
      G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;
      create_edge_pairs_for_h_index_length_mem_lemma g h_index (getWosize (read_word g h_index));
      G.pick_second_length_lemma h_index_edge_list;
      assert (Seq.length (G.successors_fn2 f_h_index h_index_edge_list) <= 
                            Usize.v (getWosize (read_word g h_index)));
      assert (Seq.length (G.successors grph f_h_index) <= Usize.v (getWosize (read_word g h_index)));
      ()
    )
      
 )
 else
 (
  length_empty_lemma (Seq.empty #UInt64.t);
  ()
 )


#reset-options "--z3rlimit 500"
#push-options "--split_queries always"


let size_less_heap_size_lemma (g:heap{well_formed_heap2 g})

                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header1 h_index g 
                                                            })
                                           
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                             (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                  : Lemma
                    (requires (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size))
                    (ensures (Usize.v (Usize.add h_index (Usize.mul i mword))< heap_size)) =  ()

#restart-solver 

#restart-solver 

let i_value_lemma (wz:Usize.t)
                  (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1}) 
           : Lemma
             (requires (Usize.v i <> Usize.v wz + 1)) 
             (ensures (Usize.v i < Usize.v wz + 1)) =
 ()

let length_empty_generic_lemma (#a:Type)
                                (s:seq a)
                : Lemma
                  (requires s == Seq.empty)
                  (ensures (Seq.length s == 0)) = ()

#restart-solver

let succ_index_lemma (g:heap{well_formed_heap2 g}) 
                     (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                     (wz: wosize{valid_wosize g h_index wz})
                         
                     (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
          : Lemma
            (ensures ~(Seq.mem (Usize.add h_index (Usize.mul i mword)) (objects2 0UL g))) =
let succ_index = Usize.add h_index (Usize.mul i mword) in
assert (Usize.v succ_index >= Usize.v h_index + Usize.v mword);
assert (Usize.v succ_index <= Usize.v h_index + (((Usize.v (getWosize (read_word g h_index)) + 1) * Usize.v mword) - 1));
assert ((forall x y. Seq.mem x (objects2 0UL g) /\  (Usize.v y >= Usize.v x + Usize.v mword) /\ 
                                                   (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1)) ==>
                                                   ~(Seq.mem y (objects2 0UL g))));
assert (Seq.mem h_index (objects2 0UL g));
assert (~(Seq.mem succ_index (objects2 0UL g)));
()



module Spec.GC_part02_02

open FStar.Seq
open FStar.Seq.Base

open FStar.Mul (*Always use & operator to create pairs or tuples. Because opening this module interpret * as multiplication*)

open FStar.Classical
open FStar.FunctionalExtensionality

//Machine integer
module Usize = FStar.UInt64

open Spec.GC_part01
open Spec.GC_part02_01

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let wosize_plus_times_mword_multiple_of_mword (wz:wosize)
                     :Lemma
                      (ensures (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0)) = ()

#restart-solver
#restart-solver

#reset-options "--query_stats --z3rlimit 50000"

let objects2_cons_lemma1 h_index g h_index_new =
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in

 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in // possible next header = h_index + (wz + 1) * mword. Eg. h_index = 0; wz = 1; mword = 8;
                                                                               // h_index_new = 0 + (1 + 1) * 8 = 0 + 16 = 16. h_index range in g = 0......7
                                                                               // first field range in g = 8......15. Only one field. So next header starts at 16
 if Usize.v h_index_new <= heap_size then //valid heap condition
  (
    if Usize.v h_index_new = heap_size then // h_index_new == heap_size --> The last block is h_index, So just create a singleton with h_index and return.
    (
       assert (Usize.v h_index_new == heap_size);
       let f = Seq.create 1 h_index in

       G.is_vertex_set_lemma2 f;
       assert (Seq.length f > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f);
       assert (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)));
       ()
    )
    else
    (

      assert (Usize.v h_index_new < heap_size); // h_index_new < heap_size, still more blocks to explore, hence recurse.
      wosize_plus_times_mword_multiple_of_mword wz;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert (Usize.v h_index_new % Usize.v mword == 0);
      assert (is_hp_addr h_index_new);
      let f' =  objects2 h_index_new g in
      objects2_mem_lemma1 h_index_new g;
      if length f' = 0 then
      (
        assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
        admit (); //FIXME KC
        ()
      )
       else
       (
         lemma_tl h_index f';
         let f'' = cons h_index f' in
         assert (Seq.length f'' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f'');
         G.is_vertex_set_cons h_index f';
         //assert (Seq.length f'' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f'');
         let objs = objects2 h_index g in

         assert (Seq.length objs > 0 /\
                        Usize.v h_index_new < heap_size ==>
                         objs == Seq.cons h_index (objects2 h_index_new g));
        admit (); //FIXME KC
        assert (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)))
       )
    )
  )
  else
  (
    assert (Usize.v h_index_new > heap_size); //h_index_new is greater than heap_size means the last object size exceeds the heap.
    let f' = Seq.empty in
    assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
    assert (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)));
    ()
  )

#restart-solver

let rec objects2_equal_lemma5 g g' h_index =
  let wz =  getWosize (read_word g h_index) in
  let wz1 =  getWosize (read_word g' h_index) in
  assert (wz == wz1);
  assert (Usize.v wz > 0);
  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
  if Usize.v h_index_new <= heap_size then //valid heap condition
  (
    if Usize.v h_index_new = heap_size then // h_index_new == heap_size --> The last block is h_index, So just create a singleton with h_index and return.
    (
       assert (Usize.v h_index_new == heap_size);
       let f = Seq.create 1 h_index in

       G.is_vertex_set_lemma2 f;
       ()
    )
    else
    (
      assert (Usize.v h_index_new < heap_size); // h_index_new < heap_size, still more blocks to explore, hence recurse.
      wosize_plus_times_mword_multiple_of_mword3 wz;
      assert (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0);
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert ((Usize.v h_index + Usize.v (Usize.mul (Usize.add wz 1UL) mword)) % Usize.v mword == 0);
      assert (h_index_new ==  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword));
      assert (Usize.v h_index_new == Usize.v h_index + Usize.v (Usize.mul (Usize.add wz 1UL) mword));
      assert (Usize.v h_index_new % Usize.v mword == 0);
      assert (is_hp_addr h_index_new);
      objects2_mem_lemma1_app1 h_index g;
      assert (Seq.mem  h_index_new (objects2 0UL g));
      //assert (is_valid_header h_index_new g);
      let f' =  objects2 h_index_new g in
      objects2_equal_lemma5 g g' h_index_new;
      if length f' = 0 then ()
       else
       (
         lemma_tl h_index f';
         let f'' = cons h_index f' in
         assert (Seq.length f'' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f'');
         G.is_vertex_set_cons h_index f';
         ()
       )
    )
  )
  else
  (
    assert (Usize.v h_index_new > heap_size); //h_index_new is greater than heap_size means the last object size exceeds the heap.
    ()
  )



#restart-solver

#restart-solver

#restart-solver

let objects2_cons_lemma2 h_index g = ()

let objects2_length_lemma3 g h_index h_index_new =
  let wz =  getWosize (read_word g h_index) in
  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in

  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in // possible next header = h_index + (wz + 1) * mword. Eg. h_index = 0; wz = 1; mword = 8;
                                                                               // h_index_new = 0 + (1 + 1) * 8 = 0 + 16 = 16. h_index range in g = 0......7
                                                                               // first field range in g = 8......15. Only one field. So next header starts at 16
  if Usize.v h_index_new <= heap_size then //valid heap condition
  (
    if Usize.v h_index_new = heap_size then // h_index_new == heap_size --> The last block is h_index, So just create a singleton with h_index and return.
    (
       assert (Usize.v h_index_new == heap_size);
       let f = Seq.create 1 h_index in

       G.is_vertex_set_lemma2 f;
       assert (Seq.length f > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f);
       assert (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)));
       ()
    )
    else
    (
      assert (Usize.v h_index_new < heap_size); // h_index_new < heap_size, still more blocks to explore, hence recurse.
      wosize_plus_times_mword_multiple_of_mword wz;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert (Usize.v h_index_new % Usize.v mword == 0);
      assert (is_hp_addr h_index_new);
      let f' =  objects2 h_index_new g in
      objects2_mem_lemma1 h_index_new g;
      if length f' = 0 then
      (
        assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');

        ()

      )
       else
       (
         lemma_tl h_index f';
         let f'' = cons h_index f' in
         assert (Seq.length f'' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f'');
         G.is_vertex_set_cons h_index f';
         assert (Seq.length f'' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f'');
         assert (Seq.length (objects2 h_index g) > 0 /\
                        Usize.v h_index_new < heap_size ==>
                         (objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g));
         assert (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)));
         assert (Seq.length f' > 0);
         ()
       )
    )
  )
  else
  (
    assert (Usize.v h_index_new > heap_size); //h_index_new is greater than heap_size means the last object size exceeds the heap.
    let f' = Seq.empty in
    assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
    assert (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)));
    ()
  )



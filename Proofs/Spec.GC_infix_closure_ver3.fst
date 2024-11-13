module Spec.GC_infix_closure_ver3

open FStar.Seq
open FStar.Seq.Base

open FStar.Mul (*Always use & operator to create pairs or tuples. Because opening this module interpret * as multiplication*)

open FStar.Classical
open FStar.FunctionalExtensionality

//Machine integer
module Usize = FStar.UInt64

open Spec.GC_part01
open Spec.GC_part02_01
open Spec.GC_part02_02

#restart-solver

#reset-options "--z3rlimit 500"


(* The assume in sweep_with_free_list3 can be removed with the help of the below three lemmas
    assume (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g)));*)
let objects2_sweep_lemma1  (h_index: hp_addr)
                           (g:heap{Seq.length (objects2 0UL g) > 0 /\
                                   Seq.mem h_index (objects2 0UL g)/\
                                  (Seq.length (objects2 h_index g) > 0)})
                  :Lemma
                   (ensures (let wz =  getWosize (read_word g h_index) in
                             let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                             let f_index_new =  Usize.add h_index_new mword in
                             Usize.v f_index_new <> heap_size)) = ()

#restart-solver

let wosize_plus_one_times_mword_multiple_of_mword5 (wz:wosize)
                     :Lemma
                      (ensures (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0)) = ()

let objects2_sweep_lemma2  (h_index: hp_addr)
                           (g:heap{Seq.length (objects2 0UL g) > 0 /\
                                   Seq.mem h_index (objects2 0UL g)/\
                                  (Seq.length (objects2 h_index g) > 0)})
                  :Lemma
                  (requires (let wz =  getWosize (read_word g h_index) in
                             let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                             let f_index_new =  Usize.add h_index_new mword in
                             Usize.v f_index_new <> heap_size))
                   (ensures
                   (let wz =  getWosize (read_word g h_index) in
                    let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                    let f_index_new =  Usize.add h_index_new mword in
                    Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g)))) =
let wz =  getWosize (read_word g h_index) in
let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
assert (Seq.mem h_index (objects2 0UL g));
assert (Seq.length (objects2 0UL g) > 0);
assert (Seq.length (objects2 0UL g) > 0 ==>
            (forall x. Seq.mem x (objects2 0UL g) ==> Usize.v (getWosize (read_word g x)) > 0));
assert  (forall x. Seq.mem x (objects2 0UL g) ==> Usize.v (getWosize (read_word g x)) > 0);
assert (Usize.v (getWosize (read_word g h_index)) > 0);

assert (Usize.v wz > 0);
let f_index_new =  Usize.add h_index_new mword in
 wosize_plus_one_times_mword_multiple_of_mword5 wz;
 assert (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0);

 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index_new mword;

 assert (Usize.v (Usize.add h_index_new mword) % Usize.v mword == 0);
 assert (Usize.v f_index_new % Usize.v mword == 0);
 if Usize.v h_index_new <= heap_size then //valid heap condition
  (
    if Usize.v h_index_new = heap_size then
    (
      assert (Seq.length (objects2 h_index g) == 1);
      assert (Seq.mem h_index (objects2 h_index g));
      assert (~(Seq.mem h_index_new (objects2 h_index g)));
      assert (Usize.v f_index_new >= heap_size);
      ()
    )
    else
    (
      assert (Usize.v h_index_new < heap_size);
      assert (Usize.v f_index_new < heap_size \/
              Usize.v f_index_new == heap_size (*\/
              Usize.v f_index_new > heap_size*)) ;
      if Usize.v f_index_new < heap_size then
      (
        ()
      )
      else
      (
        assert (Usize.v f_index_new == heap_size);
        ()
      )
    )
  )
 else
 (
   assert (Seq.length (objects2 h_index g) > 0);
   ()
 )

let objects2_sweep_lemma3  (h_index: hp_addr)
                           (g:heap{Seq.length (objects2 0UL g) > 0 /\
                                   Seq.mem h_index (objects2 0UL g)/\
                                  (Seq.length (objects2 h_index g) > 0)})
                  :Lemma
                   (ensures
                   (let wz =  getWosize (read_word g h_index) in
                    let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                    let f_index_new =  Usize.add h_index_new mword in
                    Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g)))) =
objects2_sweep_lemma1 h_index g;
objects2_sweep_lemma2 h_index g;
()


#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

(* The below lemma will be used to remove the assume in sweep_with_free_list3
   assume (~(Seq.mem h_index_new (objects2 h_index g)) /\
         (Seq.length (objects2 (hd_address f_index) g) > 0) ==>
           Seq.length (objects2 h_index g) == 1);*)

 let objects2_sweep_lemma4  (h_index: hp_addr)
                           (g:heap{Seq.length (objects2 0UL g) > 0 /\
                                   Seq.mem h_index (objects2 0UL g)/\
                                  (Seq.length (objects2 h_index g) > 0)})
                  :Lemma
                   (requires
                     (let wz =  getWosize (read_word g h_index) in
                     let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                     (~(Seq.mem h_index_new (objects2 h_index g)))))

                   (ensures
                     (let wz =  getWosize (read_word g h_index) in
                     let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                     let f_index_new =  Usize.add h_index_new mword in
                     Seq.length (objects2 h_index g) == 1)) =
let wz =  getWosize (read_word g h_index) in
let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
if Usize.v wz = 0 then
(
  ()
)
else
(
  if Usize.v h_index_new <= heap_size then
  (
    if Usize.v h_index_new = heap_size then
    (
      ()
    )
    else
    (
      assert (Usize.v h_index_new < heap_size);
      let f_index_new =  Usize.add h_index_new mword in
      assert (Usize.v h_index_new < heap_size);
      wosize_plus_times_mword_multiple_of_mword3 wz;
      assert (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0);
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert ((Usize.v h_index + Usize.v (Usize.mul (Usize.add wz 1UL) mword)) % Usize.v mword == 0);
      assert (h_index_new ==  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword));
      assert (Usize.v h_index_new == Usize.v h_index + Usize.v (Usize.mul (Usize.add wz 1UL) mword));
      assert (Usize.v h_index_new % Usize.v mword == 0);

      assert ((~(Seq.mem h_index_new (objects2 h_index g))));
      assert (is_hp_addr h_index_new);
      let f' =  objects2 h_index_new g in
      lemma_tl h_index f';
      let f'' = cons h_index f' in
      assert (f'' == objects2 h_index g);
      assert ((~(Seq.mem h_index_new (objects2 h_index g))));
      assert (forall x. Seq.mem x (objects2 h_index g) ==> Usize.v x >= Usize.v h_index);
      assert  ((forall x y. Seq.mem x (objects2 h_index g) /\
                                                   (Usize.v y >= Usize.v x + Usize.v mword) /\
                                                   (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1)) ==>
                                                   ~(Seq.mem y (objects2 h_index g))));
      assert (Seq.length f' == 0);
      assert (Seq.length (cons h_index f') == 1);
      assert (Seq.length f'' == 1);
      ()
    )
  )
  else
  (
    ()
  )
)

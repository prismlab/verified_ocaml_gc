module Spec.GC_part01

open FStar.Seq
open FStar.Seq.Base

open FStar.Mul (*Always use & operator to create pairs or tuples. Because opening this module interpret * as multiplication*)

open FStar.Classical
open FStar.FunctionalExtensionality

//Machine integer
module Usize = FStar.UInt64

let max_wosize_lemma () =
   assert (Usize.v (Usize.shift_left 1UL 54ul) == pow2 54 % pow2 64);
   Math.Lemmas.pow2_lt_compat 64 54;
   Math.Lemmas.small_mod (pow2 54) (pow2 64)

let max_color_size_lemma () =
   assert (Usize.v (Usize.shift_left 1UL 2ul) == pow2 2 % pow2 64);
   Math.Lemmas.pow2_lt_compat 64 2;
   Math.Lemmas.small_mod (pow2 2) (pow2 64)

let max_tag_size_lemma () =
   assert (Usize.v (Usize.shift_left 1UL 8ul) == pow2 8 % pow2 64);
   Math.Lemmas.pow2_lt_compat 64 8;
   Math.Lemmas.small_mod (pow2 8) (pow2 64)

let is_size_fits_after_subtraction x y = UInt.fits (Usize.v x - Usize.v y) Usize.n

let getWosize h =
 let _ = max_wosize_lemma () in
 let _ = assert (Usize.v max_wosize = pow2 54 - 1) in
 let wz = Usize.shift_right h 10ul in
 assert (Usize.v wz == Usize.v h/ pow2 10);
 assert (Usize.v wz <= Usize.v max_wosize);
 assert (Usize.v wz >= 0);
 wz

let getColor h =
 let _ = max_color_size_lemma () in
 let _ = assert (Usize.v max_color = pow2 2 - 1) in
 let c' = Usize.shift_right h 8ul in
 let c = Usize.logand c' 3UL in
 assert (Usize.v c' == Usize.v h/ pow2 8);
 assert (Usize.v c' <= pow2 64/pow2 8);
 Math.Lemmas.pow2_minus 64 8;
 assert (Usize.v c' <= pow2 56);
 UInt.logand_le #64 (Usize.v c') 3;
 assert (Usize.v c <= Usize.v c');

 assert (Usize.v c <= Usize.v max_color);
 assert (Usize.v  h <= UInt.max_int 64);
 assert (Usize.v h <= pow2 64 - 1);
 assert (Usize.v c <=  pow2 64 - 1);
 assert (Usize.v max_color <= pow2 64 - 1);
 c

let getTag h =
 let _ = max_tag_size_lemma () in
 assert (Usize.v max_tag = pow2 8 - 1);
 let t = Usize.logand h 255UL in
 UInt.logand_le #64 (Usize.v h) 255;
 assert (Usize.v max_tag <= pow2 8 - 1);
 assert (Usize.v t <= 255);
 assert (Usize.v t <= Usize.v max_tag);
 t

let color_of_object1 v_id g =

  let hd_val = read_word g v_id in
  let c = getColor (hd_val) in
  c

let wosize_of_object1 v_id g =

  let hd_val = read_word g v_id in
  let w = getWosize (hd_val) in
  w

let tag_of_object1 v_id g =

  let hd_val = read_word g v_id in
  let t = getTag (hd_val) in
  t

let isBlueObject1 v_id g =
 if color_of_object1 v_id g = blue then true
 else
  false

let isWhiteObject1 v_id g =
 if color_of_object1 v_id g = white then true
 else
  false

let isGrayObject1 v_id g =
  if color_of_object1 v_id g = gray then true
 else
  false

let isBlackObject1 v_id g =
   if color_of_object1 v_id g = black then true
 else
  false

open FStar.UInt

#push-options "--z3rlimit 500 --fuel 0 --ifuel 1" (*Be careful to use this. Always set fuel limits to default or higher if
                                                 recursive calls dont work as expected*)

#push-options "--split_queries always"

let makeHeader wz c tg =
 let l1 = Usize.shift_left wz 10ul in
 let l2 = Usize.shift_left c 8ul in
 let l3 = Usize.shift_left tg 0ul in
 assert (Usize.v l1 == Usize.v wz * pow2 10 % pow2 64);

 //First prove wz, c and tag are less than the power of maximum shift needed to create max_wosize, max_color and max_tag
 max_wosize_lemma();
 max_color_size_lemma();
 max_tag_size_lemma ();
 assert (Usize.v wz < pow2 54);
 assert (Usize.v c < pow2 2);
 assert (Usize.v tg < pow2 8);

 //Prove that wz shifted to left 10 positions is less than pow2 32. So when we take mod of pow2 32, the shift will not overflow
// Math.Lemmas.lemma_mult_lt_right (pow2 10) (Usize.v wz) (pow2 22);
 assert (pow2 10 > 0);
 assert ((Usize.v wz) <  (pow2 54));
 assert ((Usize.v wz) * pow2 10 < pow2 54 * pow2 10);
 Math.Lemmas.pow2_plus 54 10;
 assert (Usize.v wz * pow2 10 < pow2 64);
// Math.Lemmas.small_mod (Usize.v wz * pow2 10) (pow2 32);
 assert (Usize.v l1 == Usize.v wz * pow2 10);


 assert (Usize.v l2 == Usize.v c * pow2 8);
 assert (Usize.v l3 == Usize.v tg * pow2 0);

 let s = Usize.add (Usize.add l1 l2) l3 in
 assert (Usize.v s < pow2 64);
 assert (Usize.v l1 < pow2 64);
 assert (Usize.v l2 < pow2 64);
 assert (Usize.v l3 < pow2 64);

 let l1' = Usize.shift_right l1 10ul in
 let l2' = Usize.shift_right l2 10ul in
 let l3' = Usize.shift_right l3 10ul in
 assert (Usize.v l1' == Usize.v l1 /pow2 10);
 assert (Usize.v l2' == Usize.v l2 /pow2 10);
 assert (Usize.v l3' == Usize.v l3 /pow2 10);

 assert (Usize.v l1' == (Usize.v wz * pow2 10)/pow2 10);
 Math.Lemmas.cancel_mul_div (Usize.v wz) (pow2 10);
 assert (Usize.v l1' == Usize.v wz);

 assert (Usize.v l2' == Usize.v c * (pow2 8/pow2 10));

 assert (pow2 8 < pow2 10);
 assert (Usize.v l3' == Usize.v tg * (pow2 0/pow2 10));
 let s1' =  Usize.shift_right s 10ul in
 assert (s1' == getWosize s);
 assert (Usize.v s1' == Usize.v l1' + Usize.v l2' + Usize.v l3');
 assert (Usize.v s1' == Usize.v wz);
 assert (getWosize s == wz);

 let s2 = Usize.shift_right s 8ul in

 let l1'' = Usize.shift_right l1 8ul in
 let l2'' = Usize.shift_right l2 8ul in
 let l3'' = Usize.shift_right l3 8ul in
 assert (Usize.v l1'' == Usize.v l1 /pow2 8);
 assert (Usize.v l2'' == Usize.v l2 /pow2 8);
 assert (Usize.v l3'' == Usize.v l3 /pow2 8);

 assert (Usize.v l1'' == (Usize.v wz * pow2 10)/pow2 8);
 Math.Lemmas.pow2_minus 10 8;
 assert (Usize.v l1'' == Usize.v wz * pow2 2);

 assert (Usize.v l2'' == (Usize.v c * pow2 8 )/pow2 8);
 Math.Lemmas.cancel_mul_div (Usize.v c) (pow2 8);
 assert (Usize.v l2'' == Usize.v c);

 assert (Usize.v l3'' == (Usize.v tg * pow2 0)/pow2 8);
 assert (Usize.v l3'' == 0);

 assert (Usize.v s == Usize.v l1 + Usize.v l2 + Usize.v l3);
 assert (s2 == Usize.shift_right s 8ul);
 assert (Usize.v s2 == (Usize.v l1 + Usize.v l2 + Usize.v l3)/pow2 8);
 assert (Usize.v s2 == (Usize.v wz * pow2 10 + Usize.v c * pow2 8 + Usize.v tg * pow2 0)/pow2 8);
 assert (Usize.v s2 == ((Usize.v wz * pow2 10)/pow2 8) + ((Usize.v c * pow2 8)/pow2 8) + ((Usize.v tg * pow2 0)/pow2 8));
 assert (Usize.v s2 == ((Usize.v wz * pow2 10)/pow2 8) + ((Usize.v c * pow2 8)/pow2 8));
 assert (Usize.v s2 == ((Usize.v wz * pow2 10)/pow2 8) + Usize.v c);
 assert (Usize.v s2 == (Usize.v wz * pow2 2) + Usize.v c);

 //assert (Usize.v s2 == Usize.v l1'' + Usize.v l2'' + Usize.v l3'');

 let s2' = Usize.logand s2 3UL in

 assert (pow2 2 - 1 == 3);
 logand_mask #64 (Usize.v s2) 2;
 assert (Usize.v s2' == Usize.v s2 % pow2 2);
 assert (Usize.v c < pow2 2);
 assert ((Usize.v wz * pow2 2) % pow2 2 == 0);
 assert (Usize.v s2' == Usize.v c);

 let s3' = Usize.logand s 255UL in
 logand_mask #64 (Usize.v s) 8;

 assert (s2' == c);
 assert (s3' == tg);
 assert (getColor s == s2');
 assert (getTag s == s3');
 assert (getColor s == c);
 assert (getTag s == tg);

 s

#pop-options

#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"

let isPointer v_id g =
  if Usize.logand (read_word g v_id) 1UL = 0UL then true else false

let is_fields_within_limit1 h_index wz =
 //let s = Usize.add h_index (Usize.mul wz mword) in
 let s1 = Usize.add wz 1UL in // s1 = (wz + 1)
 let s2 = Usize.mul s1 mword in //s2 = (s1 * mword)
 let s3 = Usize.sub s2 1UL in // s3 = s2 - 1 = (s1 * mword) - 1 = ((wz + 1) * mword) - 1
 let s =  Usize.add h_index s3 in // s = h_index + s3 = h_index + ((wz + 1) * mword) - 1
 if (Usize.v s < heap_size) then
    true
  else
    false

#push-options "--split_queries always"

let rec is_fields_contents_within_limit2 h_index wz g =
    if (Usize.v wz = 0) then true
    else
      (
        assert (Usize.v wz > 0);
        let s = Usize.add h_index (Usize.mul wz mword) in
        let wz' = Usize.sub wz 1UL in
        if (isPointer s g) then
        (
          let succ = read_word g s in
          if Usize.v succ >= Usize.v mword && Usize.v succ < heap_size && is_hp_addr succ then
           is_fields_contents_within_limit2 h_index wz' g
          else
           false
        )
        else
        (
          is_fields_contents_within_limit2 h_index wz' g
        )
       )





let color_lemma (h_index)
                (g:heap)
          : Lemma
            (ensures ((color_of_object1 h_index g == white) \/
                      (color_of_object1 h_index g == black) \/
                      (color_of_object1 h_index g == gray) \/
                      (color_of_object1 h_index g == blue))) = ()

#push-options "--split_queries always "

#restart-solver

#restart-solver

let rec objects2 h_index g =
let wz =  getWosize (read_word g h_index) in
let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
if Usize.v wz = 0 then
(
  let f' = Seq.empty  in// There are no zero length objects.
  assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
  assert (forall x. Seq.mem x f' ==> is_hp_addr x);
  f'
)
else
(
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
       assert (forall x. Seq.mem x f ==> is_hp_addr x);
       f
    )
    else
    (
      assert (Usize.v h_index_new < heap_size);
      let f_index_new =  Usize.add h_index_new mword in
      let f' =  objects2 h_index_new g in
      if length f' = 0 ||  (Usize.v f_index_new = heap_size) then
      (
        assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
        assert (forall x. Seq.mem x f' ==> is_hp_addr x);
        f'
      )
       else
       (
         assert (Usize.v h_index_new < heap_size);
         lemma_tl h_index f';
         let f'' = cons h_index f' in
         assert (Seq.length f'' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f'');
         G.is_vertex_set_cons h_index f';
         assert (G.is_vertex_set f'');
         assert (forall x. Seq.mem x f'' ==> is_hp_addr x);
         f''
       )
    )
  )
  else
  (
    assert (Usize.v h_index_new > heap_size); //h_index_new is greater than heap_size means the last object size exceeds the heap.
    let f' = Seq.empty in
    assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
    assert (forall x. Seq.mem x f' ==> is_hp_addr x);
    f'
  )
)

#restart-solver

let objects2_wosize_lemma h_index g = ()


let objects2_empty_lemma h_index g = 
 let wz =  getWosize (read_word g h_index) in
  objects2_wosize_lemma h_index g;
  ()

let objects2_non_empty_lemma h_index g = 
 let wz =  getWosize (read_word g h_index) in
  objects2_wosize_lemma h_index g;
 ()

let objects2_singleton_lemma h_index g =
   admit()
   
let wosize_plus_times_mword_multiple_of_mword (wz:wosize)
                     :Lemma
                      (ensures (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0)) = ()

let objects2_mem_lemma (h_index: hp_addr)
                           (g:heap)


          : Lemma
            (ensures (let wz =  getWosize (read_word g h_index) in
                      let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                      (Seq.length (objects2 h_index g) > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new (objects2 h_index g))))
            (decreases (heap_size - Usize.v h_index)) =
let wz =  getWosize (read_word g h_index) in
let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
if Usize.v wz = 0 then
(
  let f' = Seq.empty  in// There are no zero length objects.
  assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
  ()
)
else
(
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
      if length f' = 0 then
      (
        assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
        ()
      )
       else
       (

         lemma_tl h_index f';
         let f'' = cons h_index f' in

         G.is_vertex_set_cons h_index f';
         assert (Seq.length f'' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f'');
         ()
       )
    )
  )
  else
  (
    assert (Usize.v h_index_new > heap_size); //h_index_new is greater than heap_size means the last object size exceeds the heap.
    let f' = Seq.empty in
    assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
    ()
  )
)

#restart-solver

#restart-solver

let rec objects2_mem_lemma1 (h_index: hp_addr)
                            (g:heap)


          : Lemma
            (ensures ((Seq.length (objects2 h_index g) > 0  ==> (forall x. Seq.mem x (objects2 h_index g) /\
                                                                  Usize.v (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) < heap_size ==>
                                                                       Seq.mem (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword))
                                                                           (objects2 h_index g))))) =
let wz =  getWosize (read_word g h_index) in
let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
if Usize.v wz = 0 then
(
  let f' = Seq.empty  in// There are no zero length objects.
  assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
  assert (Seq.length (objects2 h_index g) > 0  ==> (forall x. Seq.mem x (objects2 h_index g) /\
                                                                  Usize.v (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) < heap_size ==>
                                                                       Seq.mem (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword))
                                                                           (objects2 h_index g)));
  ()
)
else
(
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
       assert (Seq.length (objects2 h_index g) > 0  ==> (forall x. Seq.mem x (objects2 h_index g) /\
                                                                  Usize.v (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) < heap_size ==>
                                                                       Seq.mem (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword))
                                                                           (objects2 h_index g)));
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
        assert (Seq.length (objects2 h_index g) > 0  ==> (forall x. Seq.mem x (objects2 h_index g) /\
                                                                  Usize.v (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) < heap_size ==>
                                                                       Seq.mem (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword))
                                                                           (objects2 h_index g)));
        ()
      )
       else
       (
         lemma_tl h_index f';
         let f'' = cons h_index f' in
         assert (Seq.length f'' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f'');
         G.is_vertex_set_cons h_index f';
         assert (Seq.length f'' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f'');
         assert (Seq.length (objects2 h_index g) > 0  ==> (forall x. Seq.mem x (objects2 h_index g) /\
                                                                  Usize.v (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) < heap_size ==>
                                                                       Seq.mem (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword))
                                                                           (objects2 h_index g)));
         ()
       )
    )
  )
  else
  (
    assert (Usize.v h_index_new > heap_size); //h_index_new is greater than heap_size means the last object size exceeds the heap.
    let f' = Seq.empty in
    assert (Seq.length f' > 0 /\ (Usize.v h_index_new < heap_size) ==> Seq.mem h_index_new f');
    assert (Seq.length (objects2 h_index g) > 0  ==> (forall x. Seq.mem x (objects2 h_index g) /\
                                                                  Usize.v (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) < heap_size ==>
                                                                       Seq.mem (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword))
                                                                           (objects2 h_index g)));
    ()
  )
)

(*assume (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g)))*)

let rec objects2_equal_lemma h_index g g' =
let wz =  getWosize (read_word g h_index) in

if Usize.v wz = 0 then () // There are no zero length objects.
else
(
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
       ()
    )
    else
    (
      assert (Usize.v h_index_new < heap_size); // h_index_new < heap_size, still more blocks to explore, hence recurse.
      let f' =  objects2 h_index_new g in
      objects2_equal_lemma h_index_new g g';
      if length f' = 0 then ()
       else
       (
         (*lemma_tail_snoc f' h_index;
         lemma_mem_snoc f' h_index;
         let f'' = snoc f' h_index in

         G.snoc_unique_lemma h_index f';*)
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
)

let wosize_times_mword_multiple_of_mword5 (wz:wosize)
                     :Lemma
                      (ensures (Usize.v (Usize.mul (Usize.add wz 1UL)  mword) % Usize.v mword == 0)) = ()






let objects2_mem_lemma1_app3 (h_index: hp_addr)
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

#restart-solver

let rec objects2_equal_lemma3 (h_index:hp_addr)
                          (g:heap)
                          (g':heap)
                   : Lemma
                       (requires (objects2 0UL g == objects2 0UL g') /\
                                 (Seq.mem h_index (objects2 0UL g)) /\
                                 (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word g' x)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index)) =
let wz =  getWosize (read_word g h_index) in
let wz1 =  getWosize (read_word g' h_index) in
assert (wz == wz1);
if Usize.v wz = 0 then () // There are no zero length objects.
else
(
  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in // possible next header = h_index + (wz + 1) * mword. Eg. h_index = 0; wz = 1; mword = 8;
  wosize_times_mword_multiple_of_mword wz;
  assert (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0);

  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);                                                                             // h_index_new = 0 +
                                                                      // first field range in g = 8......15. Only one field. So next header starts at 16
  assert ((Usize.v h_index + Usize.v (Usize.mul (Usize.add wz 1UL) mword)) % Usize.v mword == 0);
  assert (Usize.v h_index_new % Usize.v mword == 0);
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
      assert (is_hp_addr h_index_new);
      let f' =  objects2 h_index_new g in
      objects2_mem_lemma1_app3 h_index g;
      assert (Seq.mem h_index_new (objects2 0UL g));
      objects2_equal_lemma3 h_index_new g g';
      if length f' = 0 then ()
       else
       (
         (*lemma_tail_snoc f' h_index;
         lemma_mem_snoc f' h_index;
         let f'' = snoc f' h_index in

         G.snoc_unique_lemma h_index f';*)
         assert (Seq.mem h_index (objects2 0UL g));
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
)

#restart-solver

let rec objects2_length_lemma h_index g =
 let wz =  getWosize (read_word g h_index) in

if Usize.v wz = 0 then () // There are no zero length objects.
else
(
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
       ()
    )
    else
    (
      assert (Usize.v h_index_new < heap_size); // h_index_new < heap_size, still more blocks to explore, hence recurse.
      let f' =  objects2 h_index_new g in
      objects2_length_lemma h_index_new g;
      if length f' = 0 then ()
       else
       (
         (*lemma_tail_snoc f' h_index;
         lemma_mem_snoc f' h_index;
         let f'' = snoc f' h_index in

         G.snoc_unique_lemma h_index f';*)
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
)

#restart-solver

let rec objects2_color_lemma h_index g =
  let wz =  getWosize (read_word g h_index) in
  color_lemma h_index g;
if Usize.v wz = 0 then () // There are no zero length objects.
else
(
  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in // possible next header = h_index + (wz + 1) * mword. Eg. h_index = 0; wz = 1; mword = 8;
                                                                               // h_index_new = 0 + (1 + 1) * 8 = 0 + 16 = 16. h_index range in g = 0......7
   wosize_times_mword_multiple_of_mword wz;
  assert (Usize.v (Usize.mul wz mword) % Usize.v mword == 0);

  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul wz mword);
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
      let f' =  objects2 h_index_new g in
      objects2_color_lemma h_index_new g;
      assert ((forall x. Seq.mem x (objects2 h_index_new g) ==> color_of_object1 x g == white \/
                                                           color_of_object1 x g == gray \/
                                                           color_of_object1 x g == black \/
                                                           color_of_object1 x g == blue));
      assert ((forall x. Seq.mem x f' ==> color_of_object1 x g == white \/
                                     color_of_object1 x g == gray \/
                                     color_of_object1 x g == black \/
                                     color_of_object1 x g == blue));
      assert (color_of_object1 h_index g == white \/
              color_of_object1 h_index g == gray \/
              color_of_object1 h_index g == black \/
              color_of_object1 h_index g == blue);
      if length f' = 0 then ()
       else
       (
         (*lemma_tail_snoc f' h_index;
         lemma_mem_snoc f' h_index;
         let f'' = snoc f' h_index in

         G.snoc_unique_lemma h_index f';*)
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
)

let rec get_allocs_helper (g:heap{Seq.length (objects2 0UL g) > 0})
                          (f: seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                           (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                           (G.is_vertex_set f) /\
                                           (forall x. Seq.mem x f ==> Seq.mem x (objects2 0UL g))})
                    : Tot (allocs: seq Usize.t{(forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                               (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                               (G.is_vertex_set allocs) /\
                                               (forall x. Seq.mem x allocs ==> Seq.mem x f) /\
                                               (G.subset_vertices allocs f) /\
                                               (forall x. Seq.mem x allocs ==>
                                                  Seq.mem x (objects2 0UL g)) /\
                                               (forall x. Seq.mem x allocs ==> Seq.mem x (objects2 0UL g)) /\
                                               (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ (isGrayObject1 x g) \/
                                                                        (isBlackObject1 x g)) /\
                                               (forall x. Seq.mem x f /\
                                                            ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/
                                                                        (isBlackObject1 x g))==>
                                                         Seq.mem x allocs) /\
                                               (forall x. Seq.mem x f /\ (isWhiteObject1 x g) ==> Seq.mem x allocs) /\
                                               (forall x. Seq.mem x f /\ (isBlackObject1 x g) ==> Seq.mem x allocs) /\
                                               (forall x. Seq.mem x f /\ (isGrayObject1 x g) ==> Seq.mem x allocs)})
                      (decreases length f) =
if length f = 0 then
(
 G.is_vertex_set_lemma1 f;
 assert (G.is_vertex_set f);
 assert (G.subset_vertices f f);
 assert (forall x. Seq.mem x f /\ (isWhiteObject1 x g) ==> Seq.mem x f);
 f
)
else
 (
   let hd = Seq.head f in
   let tl = Seq.tail f in

   assert (forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
   assert (forall x. Seq.mem x tl ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
   assert (G.is_vertex_set f);

   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);

   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));

   let allocs' = get_allocs_helper g tl in
   assert (forall x. Seq.mem x tl /\ (isWhiteObject1 x g) ==> Seq.mem x allocs');
   assert (forall x. Seq.mem x allocs' ==> Seq.mem x tl);
   assert (~(Seq.mem hd allocs'));
   assert (Seq.mem hd f);
   objects2_color_lemma 0UL g;
   assert (forall x. Seq.mem x (objects2 0UL g) ==> color_of_object1 x g == white \/
                                               color_of_object1 x g == gray \/
                                               color_of_object1 x g == black \/
                                               color_of_object1 x g == blue);
   assert (forall x. Seq.mem x f ==> Seq.mem x (objects2 0UL g));
   assert (color_of_object1 hd g == white \/ color_of_object1 hd g == gray \/ color_of_object1 hd g == black \/ color_of_object1 hd g == blue);
   if (isWhiteObject1 hd g || isGrayObject1 hd g || isBlackObject1 hd g) then
     (
       if length allocs' > 0 then
       (
          Seq.lemma_tail_snoc allocs' hd;
          Seq.lemma_mem_snoc allocs' hd;
          let allocs'' = snoc allocs' hd in
          assert (G.is_vertex_set allocs');
          assert (~(Seq.mem hd allocs'));
          G.snoc_unique_lemma hd allocs';
          assert (G.is_vertex_set allocs'');
          assert (G.subset_vertices allocs'' f);
          allocs''

       )
       else
       (
         let allocs'' =  Seq.cons hd (Seq.empty) in//Seq.create 1 hd in
         lemma_tl hd (Seq.empty);
         G.is_vertex_set_lemma2 allocs'';
         assert (Seq.mem hd f);
         assert (Seq.length allocs'' == 1);
         assert (Seq.head allocs'' == hd);
         assert (Seq.tail allocs'' == Seq.empty);
         lemma_mem_inversion allocs'';
         assert (forall x. mem x allocs'' = (x = head allocs'' || mem x (tail allocs'')));
         assert (forall x. mem x allocs'' ==> (x = head allocs'' || mem x (tail allocs'')));
         assert (forall x. mem x allocs'' ==> (x = hd || mem x (Seq.empty)));
         assert (forall x. mem x allocs'' ==> (x = hd));
         assert (forall x. mem x allocs'' ==> Seq.mem x f);
         assert (forall x. Seq.mem x allocs'' ==> Seq.mem x f);
         assert (G.subset_vertices allocs'' f);
         allocs''
       )

     )
   else
     (
      assert (forall x. Seq.mem x allocs' ==> Seq.mem x tl);
      assert (forall x. Seq.mem x allocs' ==> Seq.mem x f);
      assert (G.subset_vertices allocs' f);
      allocs'
     )
  )


let snoc_equality_lemma (f: seq Usize.t{Seq.length f > 0})
                        (f': seq Usize.t{Seq.length f' > 0})
                        (hd: Usize.t)
                        (hd': Usize.t)
                : Lemma
                  (requires f == f' /\ hd == hd')
                  (ensures (snoc f hd == snoc f' hd')) = ()

#restart-solver

#restart-solver

#restart-solver

let seq_mem_lemma (f: seq Usize.t{Seq.length f > 0})
            : Lemma
              (ensures(Seq.mem (Seq.head f) f) /\
                      (forall x. Seq.mem x (Seq.tail f) ==> Seq.mem x f)) = ()

let seq_length_tl_lemma (f: seq Usize.t{Seq.length f > 0})
            : Lemma
              (ensures (Seq.length (Seq.tail f) < Seq.length f)) = ()


let seq_empty_length_lemma ()
            : Lemma
              (ensures (Seq.length (Seq.empty) == 0)) = ()

let seq_cons_length_mem_lemma (hd:Usize.t)
                   : Lemma
                     (ensures (Seq.length (Seq.cons hd (Seq.empty)) == 1) /\
                              (Seq.head (Seq.cons hd (Seq.empty)) == hd) /\
                              (Seq.tail (Seq.cons hd (Seq.empty)) == Seq.empty)) = ()

let seq_empty_mem_lemma (#a:eqtype)
            : Lemma
              (ensures ~(exists x.Seq.mem x (Seq.empty #a))) = ()


#reset-options "--z3rlimit 50  --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let rec get_allocs_helper_lemma (g:heap{Seq.length (objects2 0UL g) > 0})
                                (g':heap{Seq.length (objects2 0UL g') > 0})
                                (f: seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                 (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                 (G.is_vertex_set f) /\
                                                 (forall x. Seq.mem x f ==> is_hp_addr x) /\
                                                 (forall x. Seq.mem x f ==> Seq.mem x (objects2 0UL g))})
                                (f': seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                  (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                  (G.is_vertex_set f') /\
                                                  (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                  (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g'))})
                                (v_id:hp_addr)
                                (c:color)
                      : Lemma
                        (requires (objects2 0UL g ==
                                   objects2 0UL g') /\
                                  (f == f') /\
                                  (Seq.length g == Seq.length g') /\
                                  (heap_remains_same_except_index_v_id v_id g g') /\
                                  (color_of_object1 v_id g' == c) /\
                                  (color_of_object1 v_id g == white \/ color_of_object1 v_id g == gray \/
                                    color_of_object1 v_id g == black) /\
                                  (wosize_of_object1 v_id g' == wosize_of_object1 v_id g) /\
                                  (tag_of_object1 v_id g' == tag_of_object1 v_id g) /\
                                  (Seq.mem v_id (objects2 0UL g)) /\
                                  (Seq.mem v_id (objects2 0UL g')) /\
                                  (c == 1UL \/ c == 2UL \/ c == 3UL))
                         (ensures (get_allocs_helper g f == get_allocs_helper g' f'))
                         (decreases (Seq.length f))=
if length f = 0 then
  (
     G.is_vertex_set_lemma1 f;
     assert (G.is_vertex_set f);
     assert (G.subset_vertices f f);
     assert (get_allocs_helper g f == get_allocs_helper g' f');
     ()
)
else
 (
   let hd = Seq.head f in
   let tl = Seq.tail f in

   let hd' = Seq.head f' in
   let tl' = Seq.tail f' in

   assert (hd == hd');
   assert (tl == tl');

   G.is_vertex_set_lemma f;
   G.is_vertex_set_lemma f';

   assert (G.is_vertex_set f /\ length f > 0 ==> G.is_vertex_set (tail f));
   assert (G.is_vertex_set (tail f));
   assert (tl == tail f);
   assert (G.is_vertex_set tl);
   assert (G.is_vertex_set tl');

   G.is_vertex_set_lemma4 f;
   G.is_vertex_set_lemma4 f';
   seq_mem_lemma f;
   let allocs' = get_allocs_helper g tl in
   let allocs'' = get_allocs_helper g' tl' in

   seq_length_tl_lemma f;
   get_allocs_helper_lemma g g' tl tl' v_id c;

   //assert (G.is_vertex_set tl);
   assert (get_allocs_helper g tl == get_allocs_helper g' tl');

   if (isWhiteObject1 hd g || isGrayObject1 hd g || isBlackObject1 hd g) then
     (
       assert (isWhiteObject1 hd g || isGrayObject1 hd g || isBlackObject1 hd g);
       assert (isWhiteObject1 hd g' || isGrayObject1 hd g' || isBlackObject1 hd g');
       if length allocs' > 0 then
       (
          Seq.lemma_tail_snoc allocs' hd;
          Seq.lemma_mem_snoc allocs' hd;
          Seq.lemma_tail_snoc allocs'' hd';
          Seq.lemma_mem_snoc allocs'' hd';
          let allocs1 = snoc allocs' hd in
          let allocs2 = snoc allocs'' hd' in

          G.snoc_unique_lemma hd allocs';
          G.snoc_unique_lemma hd' allocs'';
          assert (allocs'' == allocs');
          assert (hd == hd');
          snoc_equality_lemma allocs' allocs'' hd hd';
          assert (allocs1 == allocs2);
          ()
       )
       else
       (
         let allocs1 =  Seq.cons hd (Seq.empty) in//Seq.create 1 hd in
         seq_empty_length_lemma #UInt64.t ();
         lemma_tl hd (Seq.empty);
         G.is_vertex_set_lemma2 allocs1;
         assert (Seq.mem hd f);
         seq_cons_length_mem_lemma hd;
         assert (Seq.length allocs1 == 1);
         assert (Seq.head allocs1 == hd);
         assert (Seq.tail allocs1 == Seq.empty);
         lemma_mem_inversion allocs1;
         assert (forall x. mem x allocs1 = (x = head allocs1 || mem x (tail allocs1)));
         assert (forall x. mem x allocs1 ==> (x = head allocs1 || mem x (tail allocs1)));
         assert (forall x. mem x allocs1 ==> (x = hd || mem x (Seq.empty)));
         seq_empty_mem_lemma #UInt64.t;
         assert (forall x. mem x allocs1 ==> (x = hd));
         assert (forall x. mem x allocs1 ==> Seq.mem x f);
         assert (forall x. Seq.mem x allocs1 ==> Seq.mem x f);
         assert (G.subset_vertices allocs1 f);
         ()

       )
     )
   else
     (
        ()
     )
 )

#reset-options "--z3rlimit 500"

#push-options "--split_queries always"


let get_allocated_block_addresses   (g:heap {Seq.length (objects2 0UL g) > 0})
                          : Tot (allocs: seq Usize.t {(forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x allocs ==> is_hp_addr x) /\
                                                      (forall x. Seq.mem x allocs ==> Seq.mem x (objects2 0UL g)) /\
                                                      (G.is_vertex_set allocs) /\
                                                      (G.subset_vertices allocs (objects2 0UL g)) /\
                                                      (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/
                                                                                 (isGrayObject1 x g) \/
                                                                                (isBlackObject1 x g)) /\
                                                      (forall x. Seq.mem x (objects2 0UL g) /\
                                                           ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                               Seq.mem x allocs)}) =
let f =  objects2 0UL g in
   assert (length f > 0);
   assert (forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
   assert (G.is_vertex_set f);
   assert (forall x. Seq.mem x f ==> Usize.v x >= 0);

   let allocs = get_allocs_helper g f in
   assert (G.is_vertex_set allocs);
   assert (G.subset_vertices allocs f);
   assert (G.subset_vertices allocs (objects2 0UL g));
   assert (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g));
   assert (forall x. Seq.mem x f /\ ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                     Seq.mem x allocs);
   assert (forall x. Seq.mem x (objects2 0UL g) /\
                          ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                     Seq.mem x allocs);
   assert (forall x. Seq.mem x f /\ (isWhiteObject1 x g) ==> Seq.mem x allocs);
   assert (forall x. Seq.mem x f /\ (isBlackObject1 x g) ==> Seq.mem x allocs);
   assert (forall x. Seq.mem x f /\ (isGrayObject1 x g) ==> Seq.mem x allocs);
   allocs

let cons_lemma_mem (hd:Usize.t)
                       (l: seq Usize.t)
                       (f: seq Usize.t)
               : Lemma
                 (requires (G.is_vertex_set l) /\ (G.is_vertex_set f) /\ ~(Seq.mem hd l) /\ (Seq.mem hd f) /\ (G.subset_vertices l f))
                 (ensures (forall x. Seq.mem x (Seq.cons hd l) ==> Seq.mem x f)) =
 let l1 = Seq.cons hd l in
 Seq.lemma_tl hd l;
 Seq.mem_cons hd l;
 ()

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver



let rec is_fields_contents_within_limit2_lemma_for_sweep   (h_index: hp_addr)
                                                           (wz: wosize{is_fields_within_limit1 h_index wz})
                                                           (wz': wosize{is_fields_within_limit1 h_index wz'})
                                                           (g:heap{Seq.length (objects2 0UL g) > 0})
                                                           (g':heap{Seq.length (objects2 0UL g') > 0})

                          : Lemma
                            (requires (wz == wz') /\
                                      (Seq.mem h_index (get_allocated_block_addresses g) /\
                                       Seq.mem h_index (get_allocated_block_addresses g')) /\
                                      (forall y.   Usize.v y >= Usize.v h_index + Usize.v mword /\
                                                   Usize.v y <=
                                                     Usize.v h_index + (Usize.v wz * Usize.v mword) ==>
                                                                     read_word g y == read_word g' y) /\
                                      is_fields_contents_within_limit2 h_index wz g == true

                            )

                            (ensures (*(is_fields_contents_within_limit2 h_index wz g == true <==>*)
                                      is_fields_contents_within_limit2 h_index wz' g' == true)
                            (decreases (Usize.v wz)) =
 if (Usize.v wz = 0) then ()
 else
 (
  assert (Usize.v wz > 0);
   let s = Usize.add h_index (Usize.mul wz mword) in
   let wz1 = Usize.sub wz 1UL in
   let wz2 = Usize.sub wz' 1UL in
    wosize_times_mword_multiple_of_mword wz;
    assert (Usize.v (Usize.mul wz mword) % Usize.v mword == 0);

    sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul wz mword);
    assert (is_hp_addr s);
    let succ = read_word g s in
    let succ' = read_word g' s in
    assert (succ == succ');
    if (isPointer s g) then
   (

     if Usize.v succ >= Usize.v mword && Usize.v succ < heap_size && is_hp_addr succ then
         is_fields_contents_within_limit2_lemma_for_sweep h_index wz1 wz2 g g'

     else
         ()
   )
   else
   (
     assert (~(isPointer s g));
      is_fields_contents_within_limit2_lemma_for_sweep h_index wz1 wz2 g g';
     ()
   )
 )

let rec get_color_based_block_picker (g:heap{Seq.length (objects2 0UL g) > 0})
                                     (f: seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                      (G.is_vertex_set f) /\
                                                      (G.subset_vertices f (objects2 0UL g)) /\
                                                      (forall x. Seq.mem x f ==> Seq.mem x (objects2 0UL g)) /\
                                                      (forall x. Seq.mem x f ==> (isWhiteObject1 x g) \/
                                                                            (isGrayObject1 x g) \/
                                                                            (isBlackObject1 x g))})

                                     (c:color{c == white \/ c == gray \/ c == black})

                    : Tot (color_block: seq Usize.t{(forall x. Seq.mem x color_block ==> Usize.v x >= 0 /\ Usize.v x < heap_size)  /\
                                                    (forall x. Seq.mem x color_block ==> Usize.v x % Usize.v mword == 0) /\
                                                    (G.is_vertex_set color_block) /\
                                                    (forall x. Seq.mem x color_block ==> Seq.mem x f) /\
                                                    (G.subset_vertices color_block f) /\
                                                    (G.subset_vertices color_block (objects2 0UL g)) /\
                                                    (forall x. Seq.mem x color_block ==>  Seq.mem x (objects2 0UL g)) /\
                                                    (forall x. Seq.mem x color_block ==> Seq.mem x f /\ color_of_object1 x g == c) /\
                                                    (forall x. Seq.mem x f /\ color_of_object1 x g == c ==> Seq.mem x color_block) /\
                                                    (forall x. Seq.mem x color_block <==> Seq.mem x f /\ color_of_object1 x g == c)})

                      (decreases length f) =
assert (forall x. Seq.mem x f ==>  color_of_object1 x g == black \/
                             color_of_object1 x g == white \/
                             color_of_object1 x g == gray);
if length f = 0 then
(
 G.is_vertex_set_lemma1 f;
 assert (G.is_vertex_set f);
 assert (G.subset_vertices f f);
 assert (G.subset_vertices f (objects2 0UL g));
 assert (forall x. Seq.mem x f ==> Seq.mem x f /\ color_of_object1 x g == c);
 assert (forall x. Seq.mem x f <==> Seq.mem x f /\ color_of_object1 x g == c);
 f
)
else
 (
    let hd = Seq.head f in
    let tl = Seq.tail f in

    G.is_vertex_set_lemma f;

    G.is_vertex_set_lemma4 f;

    let color_block' = get_color_based_block_picker g tl c in
    assert (forall x. Seq.mem x color_block' ==> Seq.mem x tl);
    assert (~(Seq.mem hd color_block'));
    if (color_of_object1 hd g = c) then
     (
        if length color_block' > 0 then
          (
             Seq.lemma_tail_snoc color_block' hd;
             Seq.lemma_mem_snoc color_block' hd;
             let color_block'' = snoc color_block' hd in
             assert (G.is_vertex_set color_block');
             assert (~(Seq.mem hd color_block'));
             G.snoc_unique_lemma hd color_block';
             assert (G.is_vertex_set color_block'');
             assert (G.subset_vertices color_block'' f);
             assert (forall x. Seq.mem x color_block'' ==> Seq.mem x f /\ color_of_object1 x g == c);
             assert (forall x. Seq.mem x color_block'' <==> Seq.mem x f /\ color_of_object1 x g == c);
             color_block''
          )
        else
          (
             Seq.lemma_tl hd color_block';
             let color_block'' = Seq.cons hd color_block' in
             assert (~(Seq.mem hd color_block'));
             G.is_vertex_set_cons hd color_block';
             assert (G.is_vertex_set color_block'');
             assert (forall x. Seq.mem x color_block' ==> Seq.mem x f);
             assert (Seq.mem hd f);
             Seq.mem_cons hd color_block';
             assert (forall x. Seq.mem x color_block'' ==> Seq.mem x f);
             assert (G.subset_vertices color_block'' f);
             assert (G.subset_vertices color_block'' (objects2 0UL g));
             assert (forall x. Seq.mem x color_block'' ==> Seq.mem x f /\ color_of_object1 x g == c);
             assert (forall x. Seq.mem x color_block'' <==> Seq.mem x f /\ color_of_object1 x g == c);
             color_block''
          )
     )

    else
     (
        assert (G.is_vertex_set color_block');
        assert (G.subset_vertices color_block' f);
        assert (G.subset_vertices color_block' (objects2 0UL g));
        assert (forall x. Seq.mem x color_block' ==> Seq.mem x f /\ color_of_object1 x g == c);
        assert (forall x. Seq.mem x color_block' <==> Seq.mem x f /\ color_of_object1 x g == c);
        color_block'
     )
 )

#restart-solver

#reset-options "--z3rlimit 50"

let get_allocated_block_addresses_lemma g g' v_id c =
  assert (length (objects2 0uL g) > 0);
  let f =  objects2 0UL g in
  let f' = objects2 0UL g' in
  assert (length f > 0);
  assert (f == f');
  assert (length f > 0 ==> G.is_vertex_set f);
  let allocs1 = get_allocs_helper g f in
  let allocs2 = get_allocs_helper g' f' in
  get_allocs_helper_lemma g g' f f' v_id c;
  assert (allocs1 == allocs2);
  assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
  ()

#reset-options "--z3rlimit 500"

let get_black_block_addresses g f =
 let blacks =  get_color_based_block_picker g f black in
 assert (Seq.equal f (get_allocated_block_addresses g));
 assert ((forall x. Seq.mem x f ==> (isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g)) /\
         (forall x. Seq.mem x (objects2 0UL g) /\
                               ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                      Seq.mem x f));
 assert (forall x. Seq.mem x f /\ color_of_object1 x g == black ==> Seq.mem x blacks);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g ==>
                                                      Seq.mem x blacks);
 assert (forall x. Seq.mem x blacks ==> Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g);
 assert (forall x. Seq.mem x blacks <==> Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g);
 assert (forall x. Seq.mem x blacks ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (G.is_vertex_set blacks);
 assert (forall x. Seq.mem x blacks ==> Seq.mem x f);
 assert (G.subset_vertices blacks f /\
        (G.subset_vertices blacks (objects2 0UL g)));
 assert (forall x. Seq.mem x blacks ==> color_of_object1 x g == black);
 assert (forall x. Seq.mem x blacks <==> Seq.mem x f /\ color_of_object1 x g == black);
 assert (Seq.equal f (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x blacks <==> Seq.mem x (get_allocated_block_addresses g) /\ color_of_object1 x g == black);
 blacks

#restart-solver


let get_gray_block_addresses g f =
 let grays =  get_color_based_block_picker g f 2UL in
 assert (Seq.equal f (get_allocated_block_addresses g));
 assert ((forall x. Seq.mem x f ==> (isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g)) /\
         (forall x. Seq.mem x (objects2 0UL g) /\
                               ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                      Seq.mem x f));
 assert (forall x. Seq.mem x f /\ color_of_object1 x g == gray ==> Seq.mem x grays);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g ==>
                                                      Seq.mem x grays);
 assert (forall x. Seq.mem x grays ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);
 assert (forall x. Seq.mem x grays <==>
   Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);
 assert (forall x. Seq.mem x grays ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (G.is_vertex_set grays);
 assert (forall x. Seq.mem x grays ==> Seq.mem x f);
 assert (G.subset_vertices grays f /\
          (G.subset_vertices  grays (objects2 0UL g)));
 assert (forall x. Seq.mem x grays ==> color_of_object1 x g == gray);
 assert (forall x. Seq.mem x grays <==> Seq.mem x f /\ color_of_object1 x g == gray);
 assert (Seq.equal f (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x grays <==> Seq.mem x (get_allocated_block_addresses g) /\ color_of_object1 x g == gray);
 grays

#restart-solver

#reset-options "--split_queries always"

let get_white_block_addresses g f =
 let whites =  get_color_based_block_picker g f white in
 assert (Seq.equal f (get_allocated_block_addresses g));
 assert ((forall x. Seq.mem x f ==> (isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g)) /\
         (forall x. Seq.mem x (objects2 0UL g) /\
                               ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                      Seq.mem x f));
 assert (forall x. Seq.mem x f /\ color_of_object1 x g == white ==> Seq.mem x whites);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isWhiteObject1 x g ==>
                                                      Seq.mem x whites);
 assert (forall x. Seq.mem x whites ==> Seq.mem x (objects2 0UL g) /\ isWhiteObject1 x g);
 assert (forall x. Seq.mem x whites <==>
   Seq.mem x (objects2 0UL g) /\ isWhiteObject1 x g);
 assert (forall x. Seq.mem x whites ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (G.is_vertex_set whites);
 assert (forall x. Seq.mem x whites ==> Seq.mem x f);
 assert (G.subset_vertices whites f /\
          (G.subset_vertices whites (objects2 0UL g)));
 assert (forall x. Seq.mem x whites ==> color_of_object1 x g == white);
 assert (forall x. Seq.mem x whites <==> Seq.mem x f /\ color_of_object1 x g == white);
 assert (Seq.equal f (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x whites <==> Seq.mem x (get_allocated_block_addresses g) /\ color_of_object1 x g == white);
 whites

#reset-options ""

let rec is_fields_contents_within_limit2_lemma  h_index wz wz' g g' =
  if (Usize.v wz = 0) then ()
 else
 (
   assert (Usize.v wz > 0);
   let s = Usize.add h_index (Usize.mul wz mword) in
   let wz1 = Usize.sub wz 1UL in
   let wz2 = Usize.sub wz' 1UL in
   assert (is_hp_addr s);
   let succ = read_word g s in
   let succ' = read_word g' s in
   if (isPointer s g) then
   (
     assert (succ == succ');
     if Usize.v succ >= Usize.v mword && Usize.v succ < heap_size && is_hp_addr succ then
          is_fields_contents_within_limit2_lemma h_index wz1 wz2 g g'
     else
         ()
   )
   else
   (
      assert (~(isPointer s g));
      is_fields_contents_within_limit2_lemma h_index wz1 wz2 g g';
      assert (is_fields_contents_within_limit2 h_index wz1 g == true <==>
              is_fields_contents_within_limit2 h_index wz2 g' == true);
      assert (is_fields_contents_within_limit2 h_index wz g == true <==>
              is_fields_contents_within_limit2 h_index wz' g' == true);
      ()
   )
 )

let rec check_all_block_fields_within_limit2 g f' =
  match length f' with
   | 0 -> true
   | _ -> assert (length f' > 0);
         let hd = Seq.head f' in
         let tl = Seq.tail f' in
         assert (Usize.v hd % Usize.v mword == 0);
         let wz = getWosize (read_word g hd) in
         if (is_fields_contents_within_limit2 hd wz g) then
            (
               assert (is_fields_contents_within_limit2 hd wz g);
               check_all_block_fields_within_limit2 g tl
            )
            else
             false

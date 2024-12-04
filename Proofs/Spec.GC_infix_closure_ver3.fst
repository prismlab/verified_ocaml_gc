module Spec.GC_infix_closure_ver3

open FStar.Seq
open FStar.Seq.Base

open FStar.Mul (*Always use & operator to create pairs or tuples. Because opening this module interpret * as multiplication*)

open FStar.Classical
open FStar.FunctionalExtensionality

//Machine integer
module Usize = FStar.UInt64

let heap_size = admit ()

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

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

let get_allocated_block_addresses_lemma g g' v_id c =
  let f =  objects2 0UL g in
  let f' = objects2 0UL g' in
  assert (f == f');
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

#restart-solver

#reset-options "--split_queries always"

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



#restart-solver

#restart-solver

#push-options "--split_queries always"

#restart-solver

let rec check_all_block_fields_within_limit2_lemma g g' f' f'' =
 match length f' with
   | 0 -> ()
   | _ -> assert (length f' > 0);
         let hd = Seq.head f' in
         let hd' = Seq.head f'' in


         let tl = Seq.tail f' in
         let tl' = Seq.tail f'' in



         let wz = getWosize (read_word g hd) in
         let wz' = getWosize (read_word g' hd') in

         assert (Usize.v hd % Usize.v mword == 0);
         assert (Usize.v hd' % Usize.v mword == 0);

         assert (wz == wz');

         assert (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}). Usize.v (Usize.add hd (Usize.mul i mword)) < heap_size);

         h_index_field_index_all_mword_multiple_lemma1 g hd;
         assert (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}). Usize.v (Usize.add hd (Usize.mul i mword)) % Usize.v mword == 0);
         assert (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}).
                                                    (*(is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\ (*Mandatory condition, since z3 is not detecting modular
                                                                                                               arithmetic conditions*)
                                                    isPointer (Usize.add h_index (Usize.mul i mword)) g ==>*)
                                                    Usize.v (read_word g (Usize.add hd (Usize.mul i mword))) ==
                                                    Usize.v (read_word g' (Usize.add hd (Usize.mul i mword))));

         is_fields_contents_within_limit2_lemma hd wz wz' g g';

         if (is_fields_contents_within_limit2 hd wz g) then
            (

               check_all_block_fields_within_limit2_lemma g g' tl tl';
               ()
            )
         else
           ()




#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

let rec is_fields_points_to_blocks2_test      (h_index: hp_addr)
                                          (g:heap{Seq.length (objects2 0UL g) > 0})
                                          (wz: wosize{(is_fields_within_limit1 h_index wz /\
                                               is_fields_contents_within_limit2 h_index wz g)})
                                          (f':seq Usize.t { (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                    (forall x. Seq.mem x f' ==>
                                                     Seq.mem x (get_allocated_block_addresses g))})

                   : Tot (b:bool{b == true <==> is_fields_points_to_blocks2_post_condition h_index g wz f'})
                    (decreases (Usize.v wz)) =
 assert (is_hp_addr h_index);
 if (Usize.v wz = 0) then true
  else
  (
    assert (Usize.v wz > 0);
    //get the successor_index = h_index + wz * mword
    let s = Usize.add h_index (Usize.mul wz mword) in
    // For recursing, find wz' = wz - 1
    let wz' = Usize.sub wz 1UL in
    wosize_times_mword_multiple_of_mword wz;
    assert (Usize.v (Usize.mul wz mword) % Usize.v mword == 0);
    assert ((Usize.v h_index + (Usize.v wz * Usize.v mword)) % Usize.v mword == 0);
    assert (Usize.v s % Usize.v mword == 0);
    assert (Usize.v s < heap_size);
    assert (is_hp_addr s);
    if (isPointer s g) then
    (

      lemma_len_slice g (Usize.v s) ((Usize.v s) + (Usize.v mword));
      let succ = read_word g s in
      assert (Usize.v succ >= Usize.v mword);
      assert (Usize.v succ < heap_size);
      assert (Usize.v succ % Usize.v mword == 0);
      assert (is_hp_addr succ);
    //Get the header of succ. succ_hdr = succ - mword
      let hdr_succ = hd_address succ in
      let tg = tag_of_object1 hdr_succ g in
      if (Usize.v tg <> infix_tag) then
      (
        assert (Usize.v tg <> infix_tag);
        if (Seq.mem hdr_succ (get_allocated_block_addresses g)) then
        (
          is_fields_points_to_blocks2_test h_index g wz' f'
        )
        else
        (
          false
        )
      )
      else
      (
        assert (Usize.v tg == infix_tag);
        let wz_succ = wosize_of_object1 hdr_succ g in
        let wz_succ_offset = Usize.mul wz_succ mword in
        if (UInt.fits (Usize.v succ - Usize.v wz_succ_offset) Usize.n) then
        (
          let actual_succ = Usize.sub succ wz_succ_offset in
          if (Usize.v actual_succ >= Usize.v mword && is_hp_addr actual_succ) then
          (
            let hdr_actual_succ = hd_address actual_succ in
            let tg_actual = tag_of_object1 hdr_actual_succ g in
            if (Usize.v tg_actual = closure_tag && Seq.mem hdr_actual_succ (get_allocated_block_addresses g)) then
            (
              is_fields_points_to_blocks2_test h_index g wz' f'
            )
            else
            (
              false
            )
          )
          else
          (
            false
          )
        )
        else
        (
          false
        )
      )

    )
    else
    (
      assert (~(isPointer s g));
      let b = is_fields_points_to_blocks2_test h_index g wz' f' in
      b
    )

  )


let rec is_fields_points_to_blocks2 h_index g wz f' =
assert (is_hp_addr h_index);
 if (Usize.v wz = 0) then true
  else
  (
    assert (Usize.v wz > 0);
    //get the successor_index = h_index + wz * mword
    let s = Usize.add h_index (Usize.mul wz mword) in
    // For recursing, find wz' = wz - 1
    let wz' = Usize.sub wz 1UL in
    wosize_times_mword_multiple_of_mword wz;
    assert (Usize.v (Usize.mul wz mword) % Usize.v mword == 0);
    assert ((Usize.v h_index + (Usize.v wz * Usize.v mword)) % Usize.v mword == 0);
    assert (Usize.v s % Usize.v mword == 0);
    assert (Usize.v s < heap_size);
    assert (is_hp_addr s);
    if (isPointer s g) then
    (

      lemma_len_slice g (Usize.v s) ((Usize.v s) + (Usize.v mword));
      let succ = read_word g s in
      assert (Usize.v succ >= Usize.v mword);
      assert (Usize.v succ < heap_size);
      assert (Usize.v succ % Usize.v mword == 0);
      assert (is_hp_addr succ);
    //Get the header of succ. succ_hdr = succ - mword
      let hdr_succ = hd_address succ in
      let tg = tag_of_object1 hdr_succ g in
      if (Usize.v tg <> infix_tag) then
      (
        assert (Usize.v tg <> infix_tag);
        if (Seq.mem hdr_succ (get_allocated_block_addresses g)) then
        (
          is_fields_points_to_blocks2 h_index g wz' f'
        )
        else
        (
          false
        )
      )
      else
      (
        assert (Usize.v tg == infix_tag);
        let wz_succ = wosize_of_object1 hdr_succ g in
        let wz_succ_offset = Usize.mul wz_succ mword in
        if (UInt.fits (Usize.v succ - Usize.v wz_succ_offset) Usize.n) then
        (
          let actual_succ = Usize.sub succ wz_succ_offset in
          if (Usize.v actual_succ >= Usize.v mword && is_hp_addr actual_succ) then
          (
            let hdr_actual_succ = hd_address actual_succ in
            let tg_actual = tag_of_object1 hdr_actual_succ g in
            if (Usize.v tg_actual = closure_tag && Seq.mem hdr_actual_succ (get_allocated_block_addresses g)) then
            (
              is_fields_points_to_blocks2 h_index g wz' f'
            )
            else
            (
              false
            )
          )
          else
          (
            false
          )
        )
        else
        (
          false
        )
      )

    )
    else
    (
      assert (~(isPointer s g));
      let b = is_fields_points_to_blocks2_test h_index g wz' f' in
      b
    )

  )


#restart-solver

#restart-solver

#reset-options "--z3rlimit 500"

#push-options "--split_queries always"

#restart-solver

let rec is_fields_points_to_blocks2_lemma1  (h_index: hp_addr)
                                        (g:heap{Seq.length (objects2 0UL g) > 0})
                                        (wz: wosize{(is_fields_within_limit1 h_index wz /\
                                                     is_fields_contents_within_limit2 h_index wz g)})
                                        (f':seq Usize.t { (forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                          (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g))})
                                        (g':heap{Seq.length (objects2 0UL g') > 0})
                                        (wz1: wosize{(is_fields_within_limit1 h_index wz1 /\
                                                      is_fields_contents_within_limit2 h_index wz1 g')})
                                        (f'':seq Usize.t { (forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f'' ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x f'' ==> Seq.mem x (get_allocated_block_addresses g'))})
                               : Lemma
                                  (requires (wz == wz1) /\
                                            (f' == f'')  /\
                                            (objects2 0UL g == objects2 0UL g') /\
                                            (get_allocated_block_addresses g == get_allocated_block_addresses g') (*/\
                                      (forall x. Usize.v x  >= Usize.v h_index + Usize.v mword /\
                                            Usize.v x <= Usize.v h_index + (Usize.v wz * Usize.v mword) ==>
                                            (length (slice g' (Usize.v x) ((Usize.v x) + (Usize.v mword))) = 8)) /\

                                      (forall x. Usize.v x  >= Usize.v h_index + Usize.v mword /\
                                            Usize.v x <= Usize.v h_index + (Usize.v wz * Usize.v mword) ==>
                                            (length (slice g (Usize.v x) ((Usize.v x) + (Usize.v mword))) = 8))*) /\

                                      (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). wosize_of_object1 x g ==
                                               wosize_of_object1 x g') /\
                                      (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g ==
                                               tag_of_object1 x g') /\

                                      (forall x. Usize.v x  >= Usize.v h_index + Usize.v mword /\
                                            Usize.v x <= Usize.v h_index + (Usize.v wz * Usize.v mword) ==> read_word g x == read_word g' x))
                                  (ensures is_fields_points_to_blocks2 h_index g wz f' == true <==>
                                            is_fields_points_to_blocks2 h_index g' wz1 f'' == true)
                                  (decreases (Usize.v wz)) =
 if (Usize.v wz = 0) then ()
  else
  (
    assert (Usize.v wz > 0);
        //get the successor_index = h_index + wz * mword
    let s = Usize.add h_index (Usize.mul wz mword) in

    // For recursing, find wz' = wz - 1
    let wz' = Usize.sub wz 1UL in
    let wz2 = Usize.sub wz1 1UL in

    wosize_times_mword_multiple_of_mword wz;
    assert (Usize.v (Usize.mul wz mword) % Usize.v mword == 0);

    sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul wz mword);
    assert ((Usize.v h_index + (Usize.v wz * Usize.v mword)) % Usize.v mword == 0);
    assert (Usize.v s % Usize.v mword == 0);
    assert (Usize.v s < heap_size);
    assert (is_hp_addr s);
    if (isPointer s g) then
    (
      let succ = read_word g s in
      let succ' = read_word g' s in
      assert (succ == succ');

      assert (Usize.v succ >= Usize.v mword);
      assert (Usize.v succ < heap_size);
      assert (Usize.v succ % Usize.v mword == 0);
      assert (is_hp_addr succ);

      let hdr_succ = hd_address succ in
      let hdr_succ1 = hd_address succ' in
      assert (hdr_succ = hdr_succ1);
      let tg = tag_of_object1 hdr_succ g in
      let tg1 = tag_of_object1 hdr_succ1 g' in
      assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g ==
                                               tag_of_object1 x g');
      assert (Usize.v hdr_succ < heap_size /\ Usize.v hdr_succ % 8 == 0);
      assert (tg == tg1);
      if (Usize.v tg <> infix_tag) then
      (
        assert (Usize.v tg <> infix_tag);
        assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
        if (Seq.mem hdr_succ (get_allocated_block_addresses g)) then
        (
          is_fields_points_to_blocks2_lemma1 h_index g wz' f' g' wz2 f'';
          assert (is_fields_points_to_blocks2 h_index g wz' f' == true <==>
                                            is_fields_points_to_blocks2 h_index g' wz2 f'' == true);
          ()

        )
        else
        (
          ()
        )
      )

      else
      (
        assert (Usize.v tg == infix_tag);
        let wz_succ = wosize_of_object1 hdr_succ g in
        let wz_succ1 = wosize_of_object1 hdr_succ1 g' in
        let wz_succ_offset = Usize.mul wz_succ mword in
        let wz_succ_offset1 = Usize.mul wz_succ1 mword in
        assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). wosize_of_object1 x g ==
                                               wosize_of_object1 x g');
        assert (wz_succ == wz_succ1);
        if (UInt.fits (Usize.v succ - Usize.v wz_succ_offset) Usize.n) then
        (
          let actual_succ = Usize.sub succ wz_succ_offset in
          let actual_succ1 = Usize.sub succ' wz_succ_offset1 in
          if (Usize.v actual_succ >= Usize.v mword && is_hp_addr actual_succ) then
          (
             let hdr_actual_succ = hd_address actual_succ in
             let hdr_actual_succ1 = hd_address actual_succ1 in
             let tg_actual = tag_of_object1 hdr_actual_succ g in
             let tg_actual1 = tag_of_object1 hdr_actual_succ1 g' in
             assert (Usize.v hdr_actual_succ < heap_size /\ Usize.v hdr_actual_succ % 8 == 0);
             assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g ==
                                               tag_of_object1 x g');
             assert (tg_actual == tg_actual1);
            if (Usize.v tg_actual = closure_tag && Seq.mem hdr_actual_succ (get_allocated_block_addresses g)) then
            (
               is_fields_points_to_blocks2_lemma1 h_index g wz' f' g' wz2 f'';
               ()
            )
            else
            (
              ()
            )
          )
          else
          (
            ()
          )
        )
        else
        (
          ()
        )
      )
    )
    else
    (
       assert (~(isPointer s g));

       is_fields_points_to_blocks2_lemma1 h_index g wz' f' g' wz2 f'';
       ()
    )
  )

#restart-solver

#restart-solver


let rec is_fields_points_to_blocks2_lemma h_index g wz f' g' wz1 f'' =
  if (Usize.v wz = 0) then ()
  else
  (
    assert (Usize.v wz > 0);
        //get the successor_index = h_index + wz * mword
    let s = Usize.add h_index (Usize.mul wz mword) in

    // For recursing, find wz' = wz - 1
    let wz' = Usize.sub wz 1UL in
    let wz2 = Usize.sub wz1 1UL in

    wosize_times_mword_multiple_of_mword wz;
    assert (Usize.v (Usize.mul wz mword) % Usize.v mword == 0);

    sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul wz mword);
    assert ((Usize.v h_index + (Usize.v wz * Usize.v mword)) % Usize.v mword == 0);
    assert (Usize.v s % Usize.v mword == 0);
    assert (Usize.v s < heap_size);
    assert (is_hp_addr s);
    if (isPointer s g) then
    (
      let succ = read_word g s in
      let succ' = read_word g' s in
      assert (succ == succ');

      assert (Usize.v succ >= Usize.v mword);
      assert (Usize.v succ < heap_size);
      assert (Usize.v succ % Usize.v mword == 0);
      assert (is_hp_addr succ);

      let hdr_succ = hd_address succ in
      let hdr_succ1 = hd_address succ' in
      assert (hdr_succ = hdr_succ1);
      let tg = tag_of_object1 hdr_succ g in
      let tg1 = tag_of_object1 hdr_succ1 g' in
      assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g ==
                                               tag_of_object1 x g');
      assert (Usize.v hdr_succ < heap_size /\ Usize.v hdr_succ % 8 == 0);
      assert (tg == tg1);
      if (Usize.v tg <> infix_tag) then
      (
        assert (Usize.v tg <> infix_tag);
        assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
        if (Seq.mem hdr_succ (get_allocated_block_addresses g)) then
        (
          is_fields_points_to_blocks2_lemma h_index g wz' f' g' wz2 f'';
          assert (is_fields_points_to_blocks2 h_index g wz' f' == true <==>
                                            is_fields_points_to_blocks2 h_index g' wz2 f'' == true);
          ()

        )
        else
        (
          ()
        )
      )

      else
      (
        assert (Usize.v tg == infix_tag);
        let wz_succ = wosize_of_object1 hdr_succ g in
        let wz_succ1 = wosize_of_object1 hdr_succ1 g' in
        let wz_succ_offset = Usize.mul wz_succ mword in
        let wz_succ_offset1 = Usize.mul wz_succ1 mword in
        assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). wosize_of_object1 x g ==
                                               wosize_of_object1 x g');
        assert (wz_succ == wz_succ1);
        if (UInt.fits (Usize.v succ - Usize.v wz_succ_offset) Usize.n) then
        (
          let actual_succ = Usize.sub succ wz_succ_offset in
          let actual_succ1 = Usize.sub succ' wz_succ_offset1 in
          if (Usize.v actual_succ >= Usize.v mword && is_hp_addr actual_succ) then
          (
             let hdr_actual_succ = hd_address actual_succ in
             let hdr_actual_succ1 = hd_address actual_succ1 in
             let tg_actual = tag_of_object1 hdr_actual_succ g in
             let tg_actual1 = tag_of_object1 hdr_actual_succ1 g' in
             assert (Usize.v hdr_actual_succ < heap_size /\ Usize.v hdr_actual_succ % 8 == 0);
             assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g ==
                                               tag_of_object1 x g');
             assert (tg_actual == tg_actual1);
            if (Usize.v tg_actual = closure_tag && Seq.mem hdr_actual_succ (get_allocated_block_addresses g)) then
            (
               is_fields_points_to_blocks2_lemma h_index g wz' f' g' wz2 f'';
               ()
            )
            else
            (
              ()
            )
          )
          else
          (
            ()
          )
        )
        else
        (
          ()
        )
      )
    )
    else
    (
       assert (~(isPointer s g));

       is_fields_points_to_blocks2_lemma h_index g wz' f' g' wz2 f'';
       ()
    )
  )


#restart-solver

let get_allocated_block_addresses_color_lemma (g:heap {Seq.length (objects2 0UL g) > 0})
                                              (x:hp_addr{Seq.mem x (objects2 0UL g)})
                : Lemma
                  (requires color_of_object1 x g == white)
                  (ensures (Seq.mem x (get_allocated_block_addresses g))) =
  assert (forall x. Seq.mem x (objects2 0UL g) /\
                    ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                     Seq.mem x (get_allocated_block_addresses g));

  assert (Seq.mem x (get_allocated_block_addresses g));
  ()

#restart-solver

(*assume (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g)));*)



(*let rec is_fields_points_to_blocks2_lemma_for_sweep  (h_index: hp_addr)
                                                     (g:heap{Seq.length (objects2 0UL g) > 0})
                                                     (wz: wosize{(is_fields_within_limit1 h_index wz /\
                                                                  is_fields_contents_within_limit2 h_index wz g)})
                                                     (f':seq Usize.t { (forall x. Seq.mem x f' ==>
                                                                        Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                        (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                                        (forall x. Seq.mem x f' ==>
                                                                               Seq.mem x (get_allocated_block_addresses g)) /\
                                                                        (forall x. Seq.mem x f' ==>
                                                                                is_fields_within_limit1 x (getWosize (read_word g x)))})

                                                     (g':heap{Seq.length (objects2 0UL g') > 0})
                                                     (wz1: wosize{(is_fields_within_limit1 h_index wz1 /\
                                                                   is_fields_contents_within_limit2 h_index wz1 g')})
                                                     (f'':seq Usize.t { (forall x. Seq.mem x f'' ==>
                                                                          Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                        (forall x. Seq.mem x f'' ==> is_hp_addr x) /\
                                                                        (forall x. Seq.mem x f'' ==>
                                                                                   Seq.mem x (get_allocated_block_addresses g')) /\
                                                                       (forall x. Seq.mem x f'' ==>
                                                                            is_fields_within_limit1 x (getWosize (read_word g' x)))})
                               : Lemma
                                  (requires (wz == wz1) /\
                                            (wz == getWosize (read_word g h_index)) /\
                                            (wz1 == getWosize (read_word g' h_index)) /\
                                            (Seq.mem h_index f'') /\
                                            (forall x. Seq.mem x f'' ==> Seq.mem x f')  /\
                                            (*(objects2 0UL g == objects2 0UL g') /\*)
                                            (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                                       Seq.mem x (get_allocated_block_addresses g))  /\
                                            (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                               getWosize (read_word g x) ==
                                               getWosize (read_word g' x)) /\
                                            (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                               getTag (read_word g x) ==
                                               getTag (read_word g' x)) /\
                                        check_well_formed_closure_objs_lemma1_pre g g' f'' /\
                                        is_fields_points_to_blocks2 h_index g wz f'
                                      )
                                  (ensures is_fields_points_to_blocks2 h_index g' wz1 f'' == true
                                            )
                                  (decreases (Usize.v wz)) =
  (*if (Usize.v wz = 0) then ()
  else
  (
    assert (Usize.v wz > 0);
    //get the successor_index = h_index + wz * mword
    let s = Usize.add h_index (Usize.mul wz mword) in

    // For recursing, find wz' = wz - 1
    let wz' = Usize.sub wz 1UL in
    let wz2 = Usize.sub wz1 1UL in

    wosize_times_mword_multiple_of_mword wz;
    assert (Usize.v (Usize.mul wz mword) % Usize.v mword == 0);

    sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul wz mword);
    assert ((Usize.v h_index + (Usize.v wz * Usize.v mword)) % Usize.v mword == 0);
    assert (Usize.v s % Usize.v mword == 0);
    assert (Usize.v s < heap_size);
    assert (is_hp_addr s);
    assert (check_well_formed_closure_objs_lemma1_pre g g' f'' );
     if (isPointer s g) then
    (
      let succ = read_word g s in
      let succ' = read_word g' s in
      assert (succ == succ');

      assert (Usize.v succ >= Usize.v mword);
      assert (Usize.v succ < heap_size);
      assert (Usize.v succ % Usize.v mword == 0);
      assert (is_hp_addr succ);

      let hdr_succ = hd_address succ in
      let hdr_succ1 = hd_address succ' in
      assert (hdr_succ = hdr_succ1);
      let tg = tag_of_object1 hdr_succ g in
      let tg1 = tag_of_object1 hdr_succ1 g' in
      assume (color_of_object1 hdr_succ1 g' == white);
      assert (Seq.mem hdr_succ1 (objects2 0UL g));
      //assert (Seq.mem hdr_succ1 (get_allocated_block_addresses g'));
      //assert (tg == tg1);
      (*if (Usize.v tg <> infix_tag) then
      (
        assert (Usize.v tg <> infix_tag);
        assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
        if (Seq.mem hdr_succ (get_allocated_block_addresses g)) then
        (
          is_fields_points_to_blocks2_lemma h_index g wz' f' g' wz2 f'';
          assert (is_fields_points_to_blocks2 h_index g wz' f' == true <==>
                                            is_fields_points_to_blocks2 h_index g' wz2 f'' == true);
          ()

        )
        else
        (
          ()
        )
      )

      else
      (
        assert (Usize.v tg == infix_tag);
        let wz_succ = wosize_of_object1 hdr_succ g in
        let wz_succ1 = wosize_of_object1 hdr_succ1 g' in
        let wz_succ_offset = Usize.mul wz_succ mword in
        let wz_succ_offset1 = Usize.mul wz_succ1 mword in
        assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). wosize_of_object1 x g ==
                                               wosize_of_object1 x g');
        assert (wz_succ == wz_succ1);
        if (UInt.fits (Usize.v succ - Usize.v wz_succ_offset) Usize.n) then
        (
          let actual_succ = Usize.sub succ wz_succ_offset in
          let actual_succ1 = Usize.sub succ' wz_succ_offset1 in
          if (Usize.v actual_succ >= Usize.v mword && is_hp_addr actual_succ) then
          (
             let hdr_actual_succ = hd_address actual_succ in
             let hdr_actual_succ1 = hd_address actual_succ1 in
             let tg_actual = tag_of_object1 hdr_actual_succ g in
             let tg_actual1 = tag_of_object1 hdr_actual_succ1 g' in
             assert (Usize.v hdr_actual_succ < heap_size /\ Usize.v hdr_actual_succ % 8 == 0);
             assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g ==
                                               tag_of_object1 x g');
             assert (tg_actual == tg_actual1);
            if (Usize.v tg_actual = closure_tag && Seq.mem hdr_actual_succ (get_allocated_block_addresses g)) then
            (
               is_fields_points_to_blocks2_lemma h_index g wz' f' g' wz2 f'';
               ()
            )
            else
            (
              (*()*)
              admit()
            )
          )
          else
          (
            (*()*)
            admit()
          )
        )
        else
        (
          (*()*)
          admit()
        )
      )*)
      admit()
    )
    else
    (
       (*assert (~(isPointer s g));

       is_fields_points_to_blocks2_lemma h_index g wz' f' g' wz2 f'';
       ()*)
       admit()
    )
  )
*)
admit()
*)




#restart-solver


#reset-options "--z3rlimit 500" // --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

#restart-solver

let rec check_fields_points_to_blocks2_test (g:heap{Seq.length (objects2 0UL g) > 0})
                                            (f':seq Usize.t { (forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                     (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                     check_all_block_fields_within_limit2  g f'})


                               : Tot (b:bool{b == true <==> (forall x. Seq.mem x f' ==>
                                          is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g))})
                               (decreases length' f')  =
  match length f' with
   | 0 -> empty_lemma f';true
   | _ -> //assert (length f' > 0);
         non_empty_mem_lemma f';
         let hd = Seq.head f' in
         let tl = Seq.tail f' in
         let wz = getWosize (read_word g hd) in

         if Usize.v wz = 0 then
             check_fields_points_to_blocks2_test g tl

         else
           (
             assert (Usize.v wz > 0);
             assert (is_fields_contents_within_limit2 hd (getWosize (read_word g hd)) g);
             if (is_fields_points_to_blocks2 hd g (getWosize (read_word g hd)) (get_allocated_block_addresses g)) then
             (
                 assert (Seq.tail f' == tl);
                 assert (Seq.length tl < Seq.length f');
                 length'_lemma f';
                 check_fields_points_to_blocks2_test g tl

             )
             else
                  false

           )


let rec check_fields_points_to_blocks2 g f' =
  match length f' with
   | 0 -> empty_lemma f';true
   | _ -> assert (length f' > 0);
         non_empty_mem_lemma f';
         let hd = Seq.head f' in
         let tl = Seq.tail f' in
         let wz = getWosize (read_word g hd) in
         assert (Usize.v wz > 0);

         assert (is_fields_contents_within_limit2 hd (getWosize (read_word g hd)) g);
             if (is_fields_points_to_blocks2 hd g (getWosize (read_word g hd)) (get_allocated_block_addresses g)) then
             (
                 assert (Seq.tail f' == tl);
                 assert (Seq.length tl < Seq.length f');
                 length'_lemma f';
                 check_fields_points_to_blocks2 g tl

             )
             else
                  false



#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

let seq_length_lemma  (#a:Type)
                      (f:seq a)
        : Lemma
          (requires Seq.length f <> 0)
          (ensures Seq.length f > 0) =
()

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


let rec check_fields_points_to_blocks2_lemma  g g' f' f'' =
 match length f' with
   | 0 -> empty_lemma f';()
   | _ -> seq_length_lemma f';
         assert (length f' > 0);
         non_empty_mem_lemma f';
         let hd = Seq.head f' in
         let hd' = Seq.head f'' in
         let tl = Seq.tail f' in
         let tl' = Seq.tail f'' in
         assert (hd == hd');
         assert (tl == tl');
         let wz = getWosize (read_word g hd) in
         let wz1 = getWosize (read_word g' hd) in
         assert (wz == wz1);
         assert (Seq.mem hd f');

         assert (Usize.v wz > 0);
            assert (is_fields_contents_within_limit2 hd (getWosize (read_word g hd)) g);
            is_fields_points_to_blocks2_lemma hd g wz (get_allocated_block_addresses g) g' wz1 (get_allocated_block_addresses g');
            assert (is_fields_points_to_blocks2 hd g wz (get_allocated_block_addresses g) == true <==>
                                            is_fields_points_to_blocks2 hd g' wz1 (get_allocated_block_addresses g') == true);
            if (is_fields_points_to_blocks2 hd g wz (get_allocated_block_addresses g)) then
             (
              assert (is_fields_points_to_blocks2 hd g wz (get_allocated_block_addresses g));
              assert (is_fields_points_to_blocks2 hd g' wz1 (get_allocated_block_addresses g'));
              length'_lemma f';
              let _ = check_fields_points_to_blocks2_lemma g g' tl tl' in
              assert(check_fields_points_to_blocks2 g tl == true <==> check_fields_points_to_blocks2 g' tl' == true);

              assert (check_fields_points_to_blocks2 g f' == true <==> check_fields_points_to_blocks2 g' f'' == true);
              ()
             )
            else
             (
               (*assert (~(is_fields_points_to_blocks2 hd g (getWosize (read_word g hd)) (objects2 0UL g)));
               assert (check_fields_points_to_blocks2 g f' == true <==> check_fields_points_to_blocks2 g' f'' == true);
               ()*)
               ()

             )

#reset-options "--z3rlimit 500"

let rec check_well_formed_closure_objs g f =
  if Seq.length f = 0 then
    true
  else
  (
    let obj = Seq.head f in
    let rest_f = Seq.tail f in
    let tg = tag_of_object1 obj g in
    let wz = wosize_of_object1 obj g in
    if (Usize.v tg = closure_tag) then
    (
      if (Usize.v wz >= 2) then
      (
         let f_addr = f_address obj in
         assert (Usize.v f_addr >= Usize.v mword /\
                (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2) /\
                         is_fields_within_limit1 (hd_address f_addr) (wosize_of_object1 (hd_address f_addr) g));
         let clos_info = closinfo_val_from_closure_object g f_addr in
         let start_env = extract_start_env_bits clos_info in
         assert (Usize.v start_env >= Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g f_addr)));
         if is_hp_addr start_env && Usize.v start_env + 1 <= Usize.v wz && Usize.v start_env >= 1 then
         (
           let b = check_well_formed_closure_objs g rest_f in
           assert (b == true <==> closure_obj_props g rest_f);
           assert (Usize.v (tag_of_object1 obj g) == closure_tag);
           assert (Usize.v (wosize_of_object1 obj g) >= 2 /\
                  is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g (f_address obj))) /\
                  Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address obj))) <= Usize.v (wosize_of_object1 obj g) /\
                  Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address obj))) >= 1);
           assert (f == Seq.cons obj rest_f);
           (*assert (forall x. Seq.mem x rest_f ==> Usize.v (tag_of_object1 x g) = closure_tag ==>
                                       Usize.v (wosize_of_object1 x g) >= 2 /\
                                       is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) /\
                                       Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) + 1 <= Usize.v (wosize_of_object1 x g) /\
                                       Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) >= 1);*)
           assert (b == true <==> closure_obj_props g f);
           b
         )
         else
         (
           let b = false in
           assert (b == true <==> closure_obj_props g f);
           b
         )
      )
      else
      (
        let b = false in
        assert (b == true <==> closure_obj_props g f);
        b
      )
    )
    else
    (
      let b = check_well_formed_closure_objs g rest_f in
      assert (b == true <==> closure_obj_props g rest_f);
      assert (b == true <==> closure_obj_props g f);
      b
    )
  )

let get_succ_address g h_index wz i =
 let succ_address = Usize.add h_index (Usize.mul i mword) in
 assert (is_hp_addr succ_address);
 assert (Usize.v succ_address >= Usize.v mword);
 succ_address

#restart-solver

let get_succ_value g h_index wz i  =
 let succ_val = read_word g (get_succ_address g h_index wz i) in
 succ_val

let isPointer_succ g h_index wz i =
 isPointer (get_succ_address g h_index wz i) g


let hdr_address_succ_ptr g h_index wz i =
 hd_address (get_succ_value g h_index wz i)

(*wosize_succ is the wosize of the header of the succ pointer*)

let wosize_succ g h_index wz i =
wosize_of_object1 (hdr_address_succ_ptr g h_index wz i) g

let tag_succ g h_index wz i =
tag_of_object1 (hdr_address_succ_ptr g h_index wz i) g

(*predicate that ensures substraction is possible from the current succ pointer (infix) to reach its actual closure parent*)

let infix_sub_wosize_fits g h_index wz i =
 (*get the wosize of the header of the succ value*)
 let wz_succ = wosize_succ g h_index wz i in
 (*read the succ value*)
 let succ_val = get_succ_value g h_index wz i in
 (* prdct = wosize stored in the header of the succ * mword*)
 let prdct = Usize.v wz_succ * Usize.v mword in
 (*succ - prdct*)
 let diff = Usize.v succ_val - prdct in
 UInt.fits diff Usize.n


(*closure parent of infix object*)
(*arguments - h_index wz i g ---> Given an h_index infix parent() finds the closure parent by sustracting the succ value stored at the ith succ from the wosize
 of that succ header multiplied with mword*)
let infix_parent g h_index wz i =
 Usize.sub (get_succ_value g h_index wz i) (Usize.mul (wosize_succ g h_index wz i) mword)

(*header address of the parent of the infix object*)
let hdr_infix_parent g h_index wz i =
 hd_address (infix_parent g h_index wz i)


let closinfo_val_from_closure_object_lemma g f_addr g' =
 let hdr_f_addr = hd_address f_addr in
 let offst1 = mword in
 let wz = wosize_of_object1 hdr_f_addr g in
 assert (is_fields_within_limit1 hdr_f_addr wz);
 let s1 = Usize.add f_addr offst1 in
 assert (Usize.v s1 < heap_size);
 assert (Usize.v s1 % Usize.v mword == 0);
 assert (is_hp_addr s1);
 let clos_info = read_word g s1 in
 let clos_info1 = read_word g' s1 in
 assert (clos_info == clos_info1);
 ()

let rec check_well_formed_closure_objs_lemma g g' f f'' =
  if Seq.length f = 0 then
    ()
  else
  (
    let obj = Seq.head f in
    let rest_f = Seq.tail f in

    let obj1 = Seq.head f'' in
    let rest_f1 = Seq.tail f'' in

    assert (obj == obj1);
    assert (rest_f == rest_f1);

    assert (Seq.length rest_f < Seq.length f);

    let tg = tag_of_object1 obj g in
    let wz = wosize_of_object1 obj g in

    let tg1 = tag_of_object1 obj g' in
    let wz1 = wosize_of_object1 obj g' in

    assert (wz == wz1);
    assert (tg == tg1);

    if (Usize.v tg = closure_tag) then
    (
      if (Usize.v wz >= 2) then
      (
         let f_addr = f_address obj in
         assert (Usize.v f_addr >= Usize.v mword /\
                (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2) /\
                         is_fields_within_limit1 (hd_address f_addr) (wosize_of_object1 (hd_address f_addr) g));
         let clos_info = closinfo_val_from_closure_object g f_addr in
         let start_env = extract_start_env_bits clos_info in

         let clos_info1 = closinfo_val_from_closure_object g' f_addr in
         let start_env1 = extract_start_env_bits clos_info1 in

         assert (clos_info ==  clos_info1);
         assert (start_env ==  start_env1);
         assert (Usize.v start_env >= Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g f_addr)));
         if is_hp_addr start_env && Usize.v start_env <= Usize.v wz && Usize.v start_env >= 1 then
         (
           let b = check_well_formed_closure_objs g rest_f in

           check_well_formed_closure_objs_lemma g g' rest_f rest_f1;
           ()
         )
         else
         (
           let b = false in

           ()
         )
      )
      else
      (
        let b = false in

        ()
      )
    )
    else
    (
      let b = check_well_formed_closure_objs g rest_f in

      check_well_formed_closure_objs_lemma g g' rest_f rest_f1;
      ()
    )
  )

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver

let check_well_formed_closure_objs_lemma2_prop  (g:heap{Seq.length (objects2 0UL g) > 0})
                                                 (f:seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f ==> Seq.mem x (get_allocated_block_addresses g)) /\

                                                                  (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)))})=
  forall x. (Seq.mem x f /\ (Usize.v (tag_of_object1 x g) = closure_tag)) ==>
                      (Usize.v (wosize_of_object1 x g) >= 2 /\
                      is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) /\
                      Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) + 1 <= Usize.v (wosize_of_object1 x g) /\
                      Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) >= 1)


#reset-options "--z3rlimit 500"

#restart-solver


let well_formed_heap2 g =
   let f = objects2 0UL g in

  if length f > 0 then
  (
     let f' = get_allocated_block_addresses g in
     if check_all_block_fields_within_limit2 g f' &&
        check_fields_points_to_blocks2 g f' &&
         check_well_formed_closure_objs g f' then
       true
     else
      false
  )

  else
   false


#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver

#restart-solver

#restart-solver

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
         //assert (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)));
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







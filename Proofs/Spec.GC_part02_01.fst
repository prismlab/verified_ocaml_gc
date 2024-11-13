module Spec.GC_part02_01

open FStar.Seq
open FStar.Seq.Base

open FStar.Mul (*Always use & operator to create pairs or tuples. Because opening this module interpret * as multiplication*)

open FStar.Classical
open FStar.FunctionalExtensionality

//Machine integer
module Usize = FStar.UInt64

open Spec.GC_part01

#restart-solver

#restart-solver

#restart-solver

#reset-options "--z3rlimit 100"

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

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

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

#reset-options "--z3rlimit 100 --split_queries always"

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

#reset-options "--z3rlimit 500"

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
 let offst1 = Usize.mul 1UL mword in
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


#restart-solver

#reset-options "--z3rlimit 1000"

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

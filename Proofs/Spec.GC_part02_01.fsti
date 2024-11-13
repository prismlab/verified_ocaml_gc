module Spec.GC_part02_01

include Spec.GC_part01

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


val check_all_block_fields_within_limit2_lemma :(g:heap{Seq.length (objects2 0UL g) > 0})->
                                                (g':heap{Seq.length (objects2 0UL g') > 0})->
                                                (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                 (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                 (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g)) /\

                                                                 (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g x)))})->
                                                (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f'' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f'' ==> Seq.mem x (get_allocated_block_addresses g')) /\

                                                                  (forall x. Seq.mem x f'' ==> is_fields_within_limit1 x (getWosize (read_word g x)))})->
                                  Lemma

                                  (requires (f' == f'')  /\
                                            (objects2 0UL g ==
                                             objects2 0UL g') /\
                                             (get_allocated_block_addresses g ==
                                              get_allocated_block_addresses g') /\
                                            (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x)) /\
                                (forall x y. Seq.mem x f' /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                                      Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y))
                                  (ensures check_all_block_fields_within_limit2 g f' == true <==>
                                           check_all_block_fields_within_limit2 g' f'' == true)
                                   (decreases length f')


#restart-solver

#push-options "--z3rlimit 100" //--fuel 2 --ifuel 4"

#restart-solver


let test21  (h_index: hp_addr)
            (g:heap)
            (wz: wosize{(is_fields_within_limit1 h_index wz /\
                         is_fields_contents_within_limit2 h_index wz g)})
            (f':seq Usize.t { (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                    (forall x. Seq.mem x f' ==>
                                                     Seq.mem x (objects2 0UL g))})
            (j:Usize.t {(Usize.v j > 0 /\ Usize.v j <= Usize.v wz) /\ isPointer (Usize.add h_index (Usize.mul j mword)) g}) =

 assert (is_fields_contents_within_limit2 h_index wz g);
 assert ((forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}).isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                          Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) >= Usize.v mword /\
                                                          Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) < heap_size));


 assert (Usize.v (read_word g (Usize.add h_index (Usize.mul j mword))) >= Usize.v mword /\
         Usize.v (read_word g (Usize.add h_index (Usize.mul j mword))) < heap_size);

 let f_val = read_word g (Usize.add h_index (Usize.mul j mword)) in
 assert (UInt.fits (Usize.v f_val - Usize.v mword) Usize.n);
 assert (is_hp_addr f_val);
 let h_index' = hd_address (f_val) in
 admit()

let is_fields_points_to_blocks2_post_condition    (h_index: hp_addr)
                                                  (g:heap{Seq.length (objects2 0UL g) > 0})
                                                  (wz: wosize{(is_fields_within_limit1 h_index wz /\
                                                               is_fields_contents_within_limit2 h_index wz g)})
                                                  (f':seq Usize.t {(forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                                     (forall x. Seq.mem x f' ==>
                                                                         Seq.mem x (get_allocated_block_addresses g))}) =
(forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
  (is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\
   isPointer (Usize.add h_index (Usize.mul i mword)) g  ==>
    (
      (
       (Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) <> infix_tag) /\

          Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g)
      ) \/

      (
        (Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) == infix_tag) /\
        (UInt.fits (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) -
                                                   (Usize.v (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) * Usize.v mword)) Usize.n) /\
          (
                                                       (let actual_succ = (Usize.sub (read_word g (Usize.add h_index (Usize.mul i mword)))
                                                       (Usize.mul (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) mword)) in
                                                        (Usize.v actual_succ >= Usize.v mword) /\
                                                        (is_hp_addr actual_succ) /\
                                                        (Usize.v (tag_of_object1 (hd_address actual_succ) g) == closure_tag) /\
                                                        (Seq.mem (hd_address actual_succ) (get_allocated_block_addresses g)))
      )

   )
 ))


val is_fields_points_to_blocks2 :    (h_index: hp_addr) ->
                                     (g:heap{Seq.length (objects2 0UL g) > 0})->
                                     (wz: wosize{(is_fields_within_limit1 h_index wz /\
                                               is_fields_contents_within_limit2 h_index wz g)}) ->
                                     (f':seq Usize.t { (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                    (forall x. Seq.mem x f' ==>
                                                     Seq.mem x (get_allocated_block_addresses g))})->

                   Tot (b:bool{b == true <==> is_fields_points_to_blocks2_post_condition h_index g wz f'})
                   (decreases (Usize.v wz))

#restart-solver

val is_fields_points_to_blocks2_lemma : (h_index: hp_addr) ->
                                        (g:heap{Seq.length (objects2 0UL g) > 0})->
                                        (wz: wosize{(is_fields_within_limit1 h_index wz /\
                                                     is_fields_contents_within_limit2 h_index wz g)}) ->
                                        (f':seq Usize.t { (forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                          (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g))})->
                                        (g':heap{Seq.length (objects2 0UL g') > 0})->
                                        (wz': wosize{(is_fields_within_limit1 h_index wz' /\
                                                      is_fields_contents_within_limit2 h_index wz' g')}) ->
                                        (f'':seq Usize.t { (forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f'' ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x f'' ==> Seq.mem x (get_allocated_block_addresses g'))})->
                                  Lemma
                                  (requires (wz == wz') /\
                                            (f' == f'')  /\
                                            (objects2 0UL g == objects2 0UL g') /\
                                            (get_allocated_block_addresses g == get_allocated_block_addresses g') /\

                                      (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). wosize_of_object1 x g ==
                                               wosize_of_object1 x g') /\
                                      (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g ==
                                               tag_of_object1 x g') /\
                                      (forall x. Usize.v x  >= Usize.v h_index + Usize.v mword /\
                                            Usize.v x <= Usize.v h_index + (Usize.v wz * Usize.v mword) ==> read_word g x == read_word g' x))
                                  (ensures is_fields_points_to_blocks2 h_index g wz f' == true <==>
                                            is_fields_points_to_blocks2 h_index g' wz' f'' == true)
                                  (decreases (Usize.v wz))

let empty_lemma (f:seq Usize.t)
       : Lemma
         (requires Seq.length f ==  0)
         (ensures (~(exists x. Seq.mem x f))) =
()

let non_empty_mem_lemma (f:seq Usize.t)
         : Lemma
         (requires Seq.length f > 0)
         (ensures (Seq.mem (Seq.head f) f) /\
                  (forall x. Seq.mem x (Seq.tail f) ==> Seq.mem x f) /\
                  (forall x. Seq.mem x f ==> x == (Seq.head f) \/ Seq.mem x (Seq.tail f)) /\
                  (Seq.length (Seq.tail f) < Seq.length f) /\
                  (Seq.length (Seq.tail f) >= 0)) =
()

let length' (f:seq Usize.t)
          :Tot (l:nat{l = Seq.length f})=
  Seq.length f

let length'_lemma (f:seq Usize.t)
       : Lemma
         (requires length' f > 0)
         (ensures length' (Seq.tail f) < length' f) =
 ()


val check_fields_points_to_blocks2:(g:heap{Seq.length (objects2 0UL g) > 0})->
                                   (f':seq Usize.t { (forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                     (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                     check_all_block_fields_within_limit2  g f'}) ->


                               Tot (b:bool{b == true <==> (forall x. Seq.mem x f' ==>
                                          is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g))})
                               (decreases length' f')

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

let check_fields_points_to_blocks2_lemma_pre (g:heap{Seq.length (objects2 0UL g) > 0})
                                             (g':heap{Seq.length (objects2 0UL g') > 0})
                                             (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g))  /\
                                                           (forall x. Seq.mem x f' ==>
                                                                   is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)(*/\
                                                           check_all_block_fields_within_limit2 g f'*)}) =

 (forall i x.  Seq.mem x f' /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==>
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                                     (forall x y. Seq.mem x f' /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                                                            Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                              read_word g y == read_word g' y)

//#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries always"


#restart-solver

val check_fields_points_to_blocks2_lemma : (g:heap{Seq.length (objects2 0UL g) > 0})->
                                           (g':heap{Seq.length (objects2 0UL g') > 0}) ->
                                           (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g))  /\
                                                           (forall x. Seq.mem x f' ==>
                                                                   is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)(*/\
                                                           check_all_block_fields_within_limit2 g f'*)})->


                                           (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x f'' ==> is_hp_addr x) /\
                                                            (forall x. Seq.mem x f'' ==> Seq.mem x (get_allocated_block_addresses g'))  /\
                                                           (forall x. Seq.mem x f'' ==>
                                                                   is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g')(*/\
                                                            check_all_block_fields_within_limit2 g' f''*)})->

                                          Lemma
                                           (requires (f' == f'')  /\ (objects2 0UL g == objects2 0UL g') /\
                                                     (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                                     (forall (x:Usize.t{Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}).
                                                               getWosize (read_word g x) == getWosize (read_word g' x)) /\
                                                     (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). wosize_of_object1 x g ==
                                                                                                                      wosize_of_object1 x g') /\
                                                     (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g ==
                                                                                                                      tag_of_object1 x g') /\
                                                     check_fields_points_to_blocks2_lemma_pre g g' f')

                                           (ensures check_fields_points_to_blocks2 g f' == true <==> check_fields_points_to_blocks2 g' f'' == true)
                                           (decreases length' f')

let closure_obj_props1 (g:heap{Seq.length (objects2 0UL g) > 0})
                      (f:seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                              (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x f ==>
                                                                 Seq.mem x (get_allocated_block_addresses g)) /\
                                                               (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)))})=
(forall x. Seq.mem x f ==> Usize.v (tag_of_object1 x g) = closure_tag ==>
Usize.v (wosize_of_object1 x g) >= 2 /\

         is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) /\
         Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) + 1 <= Usize.v (wosize_of_object1 x g) /\
         Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) >= 1)

val check_well_formed_closure_objs  :(g:heap{Seq.length (objects2 0UL g) > 0})->
                                     (f:seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                              (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x f ==>
                                                                 Seq.mem x (get_allocated_block_addresses g)) /\
                                                               (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)))})->
                               Tot (b: bool{b == true <==> closure_obj_props1 g f})
                                (decreases length f)

val get_succ_address : (g:heap) ->
                       (h_index: hp_addr)->
                       (wz: wosize{is_fields_within_limit1 h_index wz /\
                         is_fields_contents_within_limit2 h_index wz g})->
             (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz})->
         Tot (s:hp_addr{s == Usize.add h_index (Usize.mul i mword) /\
                          (Usize.v s >= Usize.v mword)})

#restart-solver

val get_succ_value : (g:heap)->
                     (h_index: hp_addr)->
                     (wz: wosize{is_fields_within_limit1 h_index wz /\
                               is_fields_contents_within_limit2 h_index wz g})->
                     (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz})->
             Tot (s_val:Usize.t{s_val == read_word g (get_succ_address g h_index wz i)})


val isPointer_succ : (g:heap)->
                     (h_index: hp_addr)->
                     (wz: wosize{is_fields_within_limit1 h_index wz /\
                               is_fields_contents_within_limit2 h_index wz g})->
                     (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz})->
            Tot (b:bool{b == true <==> isPointer (get_succ_address g h_index wz i) g})


val hdr_address_succ_ptr :  (g:heap)->
                            (h_index: hp_addr)->
                            (wz: wosize{is_fields_within_limit1 h_index wz /\
                               is_fields_contents_within_limit2 h_index wz g})->
                            (i:Usize.t {(Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
                                      isPointer_succ g h_index wz i})->
              Tot (hdr_addr:hp_addr{hdr_addr == hd_address (get_succ_value g h_index wz i)})

val  wosize_succ : (g:heap)->
                   (h_index: hp_addr)->
                   (wz: wosize{is_fields_within_limit1 h_index wz /\
                               is_fields_contents_within_limit2 h_index wz g})->
                   (i:Usize.t {(Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
                                      isPointer_succ g h_index wz i})->
         Tot (wz_succ:wosize{wz_succ == wosize_of_object1 (hdr_address_succ_ptr g h_index wz i) g})

val tag_succ : (g:heap)->
               (h_index: hp_addr)->
               (wz: wosize{is_fields_within_limit1 h_index wz /\
                               is_fields_contents_within_limit2 h_index wz g})->
               (i:Usize.t {(Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
                                      isPointer_succ g h_index wz i})->
         Tot (tg_succ:wosize{tg_succ == tag_of_object1 (hdr_address_succ_ptr g h_index wz i) g})

val infix_sub_wosize_fits : (g:heap)->
                            (h_index: hp_addr)->
                            (wz: wosize{is_fields_within_limit1 h_index wz /\
                                      is_fields_contents_within_limit2 h_index wz g}) ->
                            (i:Usize.t {(Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
                                      isPointer_succ g h_index wz i})->
             Tot (b:bool{b== true <==> UInt.fits (Usize.v (get_succ_value g h_index wz i) - (Usize.v (wosize_succ g h_index wz i) * Usize.v mword)) Usize.n})

val infix_parent : (g:heap)->
                   (h_index: hp_addr)->
                   (wz: wosize{is_fields_within_limit1 h_index wz /\
                            is_fields_contents_within_limit2 h_index wz g})->
                   (i:Usize.t {(Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
                                      (isPointer_succ g h_index wz i) /\
                                      (infix_sub_wosize_fits g h_index wz i)})->
             Tot (pr_succ: hp_addr{pr_succ == Usize.sub (get_succ_value g h_index wz i) (Usize.mul (wosize_succ g h_index wz i) mword)})

val hdr_infix_parent : (g:heap)->
                       (h_index: hp_addr)->
                       (wz: wosize{is_fields_within_limit1 h_index wz /\
                            is_fields_contents_within_limit2 h_index wz g})->
                       (i:Usize.t {(Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
                                      (isPointer_succ g h_index wz i) /\
                                      (infix_sub_wosize_fits g h_index wz i) /\
                                      (Usize.v (infix_parent g h_index wz i) >= Usize.v mword)})->
             Tot (hdr_pr_succ: hp_addr{hdr_pr_succ == hd_address (infix_parent g h_index wz i)})

let diff_of_multiple_of_mword_is_multiple_of_mword (x:Usize.t{Usize.v x % Usize.v mword == 0})
                                                   (y:Usize.t{Usize.v y % Usize.v mword == 0})
                                :Lemma
                                 (ensures ((Usize.v x - Usize.v y) % Usize.v mword == 0)) = ()

#restart-solver

#restart-solver

#reset-options "--z3rlimit 500"

val closinfo_val_from_closure_object_lemma : (g:heap)->
                                             (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                                    (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                                                    (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2) /\
                                                    is_fields_within_limit1 (hd_address f_addr) (wosize_of_object1 (hd_address f_addr) g) /\
                                                    is_fields_contents_within_limit2 (hd_address f_addr) (wosize_of_object1 (hd_address f_addr) g) g})->
                                             (g':heap)->
                         Lemma
                         (requires (Usize.v f_addr >= Usize.v mword /\
                                   (Usize.v (tag_of_object1 (hd_address f_addr) g') == Usize.v (tag_of_object1 (hd_address f_addr) g)) /\
                                   (Usize.v (wosize_of_object1 (hd_address f_addr) g) == Usize.v (wosize_of_object1 (hd_address f_addr) g')) /\
                                   is_fields_within_limit1 (hd_address f_addr) (wosize_of_object1 (hd_address f_addr) g') /\
                                   read_word g (Usize.add f_addr (Usize.mul 1UL mword)) == read_word g' (Usize.add f_addr (Usize.mul 1UL mword))))
                         (ensures closinfo_val_from_closure_object g f_addr == closinfo_val_from_closure_object g' f_addr)

val check_well_formed_closure_objs_lemma : (g:heap{Seq.length (objects2 0UL g) > 0})->
                                           (g':heap{Seq.length (objects2 0UL g') > 0})->
                                           (f:seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                              (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x f ==>
                                                                 Seq.mem x (get_allocated_block_addresses g)) /\
                                                               (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)))})->
                                           (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f'' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f'' ==> Seq.mem x (get_allocated_block_addresses g')) /\

                                                                  (forall x. Seq.mem x f'' ==> is_fields_within_limit1 x (getWosize (read_word g' x)))})->
                              Lemma
                              (requires (f == f'')  /\
                                        (objects2 0UL g == objects2 0UL g') /\
                                        (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                        (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}).
                                               getWosize (read_word g x) ==
                                               getWosize (read_word g' x)) /\
                                        (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}).
                                               getTag (read_word g x) ==
                                               getTag (read_word g' x)) /\
                                (forall x y. Seq.mem x f /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                                      Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y))
                                  (ensures check_well_formed_closure_objs g f == true <==>
                                           check_well_formed_closure_objs g' f'' == true)
                              (decreases length f)


val well_formed_heap2 : (g:heap) ->
                 Tot (b:bool{b == true <==> Seq.length (objects2 0UL g) > 0  /\
                                          (check_all_block_fields_within_limit2 g (get_allocated_block_addresses g)) /\
                                          (check_fields_points_to_blocks2 g (get_allocated_block_addresses g)) /\
                                          (check_well_formed_closure_objs g (get_allocated_block_addresses g))
                                          })

let is_valid_header1  (h:hp_addr)  // index should be passed to check for header validity
                      (g:heap {well_formed_heap2 g})
               : Tot (b:bool{b == true <==> (Seq.mem h (get_allocated_block_addresses g))}) =
 let f = get_allocated_block_addresses g in
 if Seq.mem h f then true
 else
 false

#restart-solver

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


let succ_index_fn (g:heap{well_formed_heap2 g})
                  (h_index:hp_addr{is_valid_header1 h_index g})
                  (i:Usize.t{Usize.v i < Usize.v (getWosize (read_word g h_index)) + 1 /\ Usize.v i >= 1})
        : Tot (succ_index:hp_addr{Usize.v succ_index == Usize.v h_index + (Usize.v i * Usize.v mword)}) =
 let succ_index = Usize.add h_index (Usize.mul i mword) in
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
 assert (is_hp_addr succ_index);
 assert (succ_index == Usize.add h_index (Usize.mul i mword) );
 assert (Usize.v succ_index == Usize.v h_index + (Usize.v i * Usize.v mword));
 succ_index

#reset-options "--z3rlimit 50"

let read_succ (g:heap{well_formed_heap2 g})
              (h_index:hp_addr{is_valid_header1 h_index g})
              (i:Usize.t{Usize.v i < Usize.v (getWosize (read_word g h_index)) + 1 /\ Usize.v i >= 1})
          :Tot (succ:Usize.t{succ == read_word g (succ_index_fn g h_index i)})=
 let succ_index = succ_index_fn g h_index i in

 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
 let succ = read_word g succ_index in
 assert (succ == read_word g succ_index);
 succ

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#push-options "--z3rlimit 500"

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#reset-options "--z3rlimit 500"


let get_block_address_length_lemma (g:heap {well_formed_heap2 g})
                               : Lemma
                                 (Seq.length (objects2 0UL g) <= heap_size) =
  objects2_length_lemma 0UL g;
  assert (Seq.length (objects2 0UL g) <= heap_size);
  ()

#restart-solver

let wosize_plus_times_mword_multiple_of_mword3 (wz:wosize)
                     :Lemma
                      (ensures (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0)) = ()

let is_valid_header  (h:hp_addr)  // index should be passed to check for header validity
                     (g:heap {well_formed_heap2 g})
               : Tot (b:bool{b == true <==> (Seq.mem h (objects2 0UL g))}) =
 let f = objects2 0UL g in
 if Seq.mem h f then true
 else
 false

let objects2_mem_lemma1_app1 (h_index: hp_addr)
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

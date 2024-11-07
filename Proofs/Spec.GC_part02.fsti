module Spec.GC_part02

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

#restart-solver

let test_well_formedness_of_closure_objects (g:heap{well_formed_heap2 g})
                                            (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                                           (is_valid_header1 (hd_address f_addr) g) /\
                                                           (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag)}) =
 assert (Seq.length (objects2 0UL g) > 0  /\
        (check_all_block_fields_within_limit2 g (get_allocated_block_addresses g)) /\
        (check_fields_points_to_blocks2 g (get_allocated_block_addresses g)) /\
        (check_well_formed_closure_objs g (get_allocated_block_addresses g)));
let wz = wosize_of_object1 (hd_address f_addr) g in
assert (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2);
let clos_info = closinfo_val_from_closure_object g f_addr in
let start_env = extract_start_env_bits clos_info in
(*assert ((is_hp_addr (Usize.add f_addr (Usize.mul 1UL mword))) /\
           (clos_info == read_word g (Usize.add f_addr (Usize.mul 1UL mword))));*)
assert (start_env == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul);
assert (start_env == Usize.shift_right (Usize.shift_left (read_word g (Usize.add f_addr (Usize.mul 1UL mword))) 8ul) 9ul);
assert (Seq.length (objects2 0UL g) > 0);
assert (check_well_formed_closure_objs g (get_allocated_block_addresses g));
assert (closure_obj_props1 g (get_allocated_block_addresses g));
assert (is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g f_addr))); 
assert (is_hp_addr start_env);
let hdr_f_addr = hd_address f_addr in
assert (is_valid_header1 hdr_f_addr g);

assert (Usize.v start_env <= Usize.v wz);
assert (Usize.v start_env + 1 <= Usize.v wz);
assert (Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g f_addr)) >= 1);
assert (Usize.v start_env >= 1);
admit()

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
  
#restart-solver

#restart-solver

(*val objects2_equal_lemma1 :  (g:heap{well_formed_heap2 g})-> 
                             (g':heap)->
                             (h_index:hp_addr{is_valid_header h_index g})->
                      Lemma
                       (requires (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word g' p) ==  getWosize (read_word g p)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index))*)

val objects2_cons_lemma1 : (h_index: hp_addr)->
                           (g:heap)->
                           (h_index_new:hp_addr{h_index_new == (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword))})->
                           
            Lemma 
            (ensures (Seq.length (objects2 h_index g) > 0 /\ 
                        Usize.v h_index_new < heap_size ==> 
                         ((objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g)) /\
                         (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)))))
                         
(*val objects2_length_lemma1 :(g:heap{well_formed_heap2 g}) ->
                            (h_index:hp_addr{is_valid_header h_index g}) ->
                            (h_index_new:hp_addr{h_index_new == (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword))})->
                  Lemma
                  (requires (Seq.length (objects2 h_index g) > 0) /\ (Usize.v h_index_new < heap_size))
                  (ensures ((Seq.length (objects2 h_index_new g) > 0))) *)



(*Define the various types of heap operations possible. And prove that during each case, the well-formedness remains intact
  Case 1 : Header change - Color of an allocated object changes to white, grey or black
  Case 2 : Header change - Color of an allocated object changes to blue
  Case 3 : Header Change - wosize of a blue object changes to sum of the wosizes of that object and the next object.
  Case 4 : Field Change - The first field of a blue object is changed to point to another blue value*)

val objects2_equal_lemma5 :  (g:heap(*{well_formed_heap2 g}*){Seq.length (objects2 0UL g) > 0})-> 
                             (g':heap)->
                             (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})->
                      Lemma
                       (requires (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word g' p) ==  getWosize (read_word g p)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index))



val objects2_cons_lemma2 : (h_index: hp_addr)->
                           (g:heap)->
                         
            Lemma 
            (ensures (Seq.length (objects2 h_index g) > 0 /\ 
                        Usize.v (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) >= heap_size ==> 
                          Seq.length (objects2 h_index g) == 1))

val objects2_length_lemma3 :(g:heap{Seq.length (objects2 0UL g) > 0}) ->
                            (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)}) ->
                            (h_index_new:hp_addr{Usize.v h_index_new == (Usize.v h_index +  (Usize.v (getWosize (read_word g h_index)) + 1) * Usize.v mword)})->
                  Lemma
                  (requires (Seq.length (objects2 h_index g) > 0) /\ (Usize.v h_index_new < heap_size))
                  (ensures ((Seq.length (objects2 h_index_new g) > 0))) 


let check_well_formed_closure_objs_lemma1_pre  (g:heap{Seq.length (objects2 0UL g) > 0})
                                               (g':heap{Seq.length (objects2 0UL g') > 0})
                                          
                                               (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g')) /\
                                                                   
                                                                  (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g' x)))})=
      (forall x y. Seq.mem x f' /\ 
                   Usize.v y >= Usize.v x + Usize.v mword /\
                   Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                                     read_word g y == read_word g' y)


(*val check_well_formed_closure_objs_lemma2  : (g:heap{Seq.length (objects2 0UL g) > 0}) ->
                                             (g':heap{Seq.length (objects2 0UL g') > 0}) ->
                                             (f:seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                              (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x f ==> 
                                                                 Seq.mem x (get_allocated_block_addresses g)) /\
                                                               (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)))}) ->
                                            (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g')) /\
                                                                   
                                                                  (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g' x)))}) ->
                              Lemma 
                              (requires (forall x. Seq.mem x f' ==> Seq.mem x f)  /\
                                        (objects2 0UL g == objects2 0UL g') /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==> 
                                               getWosize (read_word g x) ==
                                               getWosize (read_word g' x)) /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==> 
                                               getTag (read_word g x) ==
                                               getTag (read_word g' x)) /\
                                        check_well_formed_closure_objs_lemma1_pre g g' f' /\
                                        check_well_formed_closure_objs g f == true
                                        )
                                  (ensures check_well_formed_closure_objs g' f' == true)*)
  
  #restart-solver
  
  #reset-options "--z3rlimit 2000"

  #restart-solver

  #restart-solver


  let check_well_formed_closure_objs_lemma2_cond  (g:heap{Seq.length (objects2 0UL g) > 0}) 
                                             (g':heap{Seq.length (objects2 0UL g') > 0}) 
                                             (f:seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                              (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x f ==> 
                                                                 Seq.mem x (get_allocated_block_addresses g)) /\
                                                               (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)))})
                                            (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g')) /\
                                                                   
                                                                  (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g' x)))}) =
    (forall x. Seq.mem x f' ==> Seq.mem x f)  /\
                                        (objects2 0UL g == objects2 0UL g') /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==> 
                                               getWosize (read_word g x) ==
                                               getWosize (read_word g' x)) /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==> 
                                               getTag (read_word g x) ==
                                               getTag (read_word g' x)) /\
                                        check_well_formed_closure_objs_lemma1_pre g g' f' /\
                                        check_well_formed_closure_objs g f == true
      
#restart-solver

#restart-solver

#restart-solver

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver

#restart-solver

//#push-options "--z3rlimit 2000"

#restart-solver

  let rec check_well_formed_closure_objs_lemma2  (g:heap{Seq.length (objects2 0UL g) > 0}) 
                                             (g':heap{Seq.length (objects2 0UL g') > 0}) 
                                             (f:seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                              (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x f ==> 
                                                                 Seq.mem x (get_allocated_block_addresses g)) /\
                                                               (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)))})
                                            (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g')) /\
                                                                   
                                                                  (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g' x)))})
                              : Lemma 
                                (requires (*(forall x. Seq.mem x f' ==> Seq.mem x f)  /\
                                        (objects2 0UL g == objects2 0UL g') /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==> 
                                               getWosize (read_word g x) ==
                                               getWosize (read_word g' x)) /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==> 
                                               getTag (read_word g x) ==
                                               getTag (read_word g' x)) /\
                                        check_well_formed_closure_objs_lemma1_pre g g' f' /\
                                        check_well_formed_closure_objs g f == true*)
                                        check_well_formed_closure_objs_lemma2_cond g g' f f'
                                        )
                                  (ensures check_well_formed_closure_objs g' f' == true)
                                   (decreases length f') 
                                  =
  if Seq.length f' = 0 then 
    ()
  else
  (
    let obj = Seq.head f' in
    let rest_f = Seq.tail f' in

    
    let tg = tag_of_object1 obj g in
    let wz = wosize_of_object1 obj g in

    let tg1 = tag_of_object1 obj g' in
    let wz1 = wosize_of_object1 obj g' in
    
    
    assert (Seq.mem obj (get_allocated_block_addresses g'));
    assert (wz == wz1);
    assert (tg == tg1);
    assert (check_well_formed_closure_objs g f);
    assert (closure_obj_props1 g f);
    assert (check_well_formed_closure_objs_lemma2_cond g g' f rest_f);
    check_well_formed_closure_objs_lemma2 g g' f rest_f;
    ()
    
  )

let rec check_all_block_fields_within_limit2_lemma_for_sweep
                                                (g:heap{Seq.length (objects2 0UL g) > 0}) 
                                                (g':heap{Seq.length (objects2 0UL g') > 0}) 
                                                (f':seq Usize.t 
                                                 {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                  (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                  (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                  (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g x)))})
                                                (f'':seq Usize.t 
                                                  {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                   (forall x. Seq.mem x f'' ==> Usize.v x % Usize.v mword == 0) /\
                                                   (forall x. Seq.mem x f'' ==> Seq.mem x (get_allocated_block_addresses g')) /\
                                                   (forall x. Seq.mem x f'' ==> is_fields_within_limit1 x (getWosize (read_word g' x)))})
                                :Lemma
                              
                                  (requires   
                                              (forall x. Seq.mem x f'' ==>
                                                        Seq.mem x f') /\
                                              (forall x. Seq.mem x f'' ==>
                                                         getWosize (read_word g x) == getWosize (read_word g' x)) /\
                                              
                                              (forall x y. Seq.mem x f'' /\ 
                                                           Usize.v y >= Usize.v x + Usize.v mword /\
                                                           Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * 
                                                                                           Usize.v mword) ==>
                                                                     read_word g y == read_word g' y) /\
                                              (forall x. Seq.mem x f' ==> 
                                                  is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)      
                                                        
                                   )
                                  (ensures 
                                            (forall x. Seq.mem x f'' ==> 
                                                  is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g'))
                                   (decreases length f'') =
match length f'' with
   | 0 -> ()
   | _ -> assert (length f'' > 0);
          let hd = Seq.head f'' in
          //let tl = Seq.tail f'' in
          assert (Seq.mem hd f');
          let tl = Seq.tail f' in
          let tl' = Seq.tail f'' in
          assert (forall x. Seq.mem x tl ==> Seq.mem x f');
          let wz = getWosize (read_word g hd) in
          let wz' = getWosize (read_word g' hd) in
          assert (Usize.v hd % Usize.v mword == 0);
          assert (wz == wz');
          h_index_field_index_all_mword_multiple_lemma1 g hd;
          assert (Seq.mem hd (get_allocated_block_addresses g) /\
                  Seq.mem hd (get_allocated_block_addresses g'));
          assert (forall y.   Usize.v y >= Usize.v hd + Usize.v mword /\
                              Usize.v y <= Usize.v hd + (Usize.v wz * Usize.v mword) ==>
                                          read_word g y == read_word g' y);
          assert (is_fields_contents_within_limit2 hd wz g == true);
          is_fields_contents_within_limit2_lemma_for_sweep hd wz wz' g g';
           if (is_fields_contents_within_limit2 hd wz g) then
            (  
              assert ((forall x. Seq.mem x tl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                      (forall x. Seq.mem x tl ==> Usize.v x % Usize.v mword == 0) /\
                      (forall x. Seq.mem x tl ==> Seq.mem x (get_allocated_block_addresses g)) /\
                      (forall x. Seq.mem x tl ==> is_fields_within_limit1 x (getWosize (read_word g x))));
              assert ((forall x. Seq.mem x tl' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                      (forall x. Seq.mem x tl' ==> Usize.v x % Usize.v mword == 0) /\
                      (forall x. Seq.mem x tl' ==> Seq.mem x (get_allocated_block_addresses g')) /\
                      (forall x. Seq.mem x tl' ==> is_fields_within_limit1 x (getWosize (read_word g' x))));
              
              assert (forall x. Seq.mem x tl' ==>
                                          Seq.mem x f');
              check_all_block_fields_within_limit2_lemma_for_sweep g g' f' tl';
              assert (forall x. Seq.mem x tl' ==> 
                                        is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
              assert (is_fields_contents_within_limit2 hd wz' g');
              assert (forall x. Seq.mem x f'' ==> x == hd \/ Seq.mem x tl');
              assert (forall x. Seq.mem x f'' ==> 
                                        is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
              ()
              
            )
         else
           ()


#push-options "--split_queries always"



let test_objects (g:heap{well_formed_heap2 g})
                 (h_index:hp_addr{is_valid_header1 h_index g}) =
  assert  (Seq.length (objects2 0UL g) > 0  /\
                                          (check_all_block_fields_within_limit2 g (get_allocated_block_addresses g)) /\
                                          (check_fields_points_to_blocks2 g (get_allocated_block_addresses g)) /\
                                          (check_well_formed_closure_objs g (get_allocated_block_addresses g)));
  assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g));
  assert (Seq.mem h_index (get_allocated_block_addresses g));
  assert (is_fields_points_to_blocks2 h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
  assert (is_fields_points_to_blocks2_post_condition h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
  assert (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g h_index))) /\ 
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
            ));
  admit()

let field_reads_equal_lemma (g:heap{well_formed_heap2 g})
                            (g':heap)
                            (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                            (x:hp_addr{Seq.mem x (objects2 0UL g) /\ x <> h_index})
                            (y:hp_addr{Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword)})
                  : Lemma
                    (requires (objects2 0UL g == objects2 0UL g') /\
                              
                              (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                    (ensures (read_word g y == read_word g' y)) = 
 assert (~(Seq.mem y (objects2 0UL g)));
 assert (y <> h_index);
 assert (read_word g y == read_word g' y);
 assert (Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y);
()

#restart-solver

#restart-solver


let field_reads_equal_h_index_lemma (g:heap{well_formed_heap2 g})
                                    (g':heap)
                                    (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                    (y:hp_addr{Usize.v y >= Usize.v h_index + Usize.v mword /\
                                       Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword)})
                  : Lemma
                    (requires (objects2 0UL g == objects2 0UL g') /\
                              (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                    (ensures (read_word g y == read_word g' y)) = 
assert (~(Seq.mem y (objects2 0UL g)));
assert (y <> h_index);
assert (read_word g y == read_word g' y);
()


let field_reads_all_equal_lemma (g:heap{well_formed_heap2 g})
                                (g':heap)
                                (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                (x:hp_addr{Seq.mem x (objects2 0UL g) /\ x <> h_index})
                      : Lemma
                        (requires (objects2 0UL g == objects2 0UL g') /\
                              (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                        (ensures (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                        read_word g y == read_word g' y)) = 
 Classical.forall_intro (Classical.move_requires (field_reads_equal_lemma g g' h_index x))

#restart-solver 

let field_reads_all_equal_h_index_lemma (g:heap{well_formed_heap2 g})
                                        (g':heap)
                                        (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                            : Lemma
                              (requires (objects2 0UL g == objects2 0UL g') /\
                                        (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                              (ensures (forall y. Usize.v y >= Usize.v h_index + Usize.v mword /\
                                             Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword) ==>
                                                   read_word g y == read_word g' y)) = 
 
 Classical.forall_intro (Classical.move_requires (field_reads_equal_h_index_lemma g g' h_index))

#restart-solver 

let field_reads_all_equal_for_all_objects_lemma (g:heap{well_formed_heap2 g})
                                                (g':heap)
                                                (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                 :Lemma
                                 (requires (objects2 0UL g == objects2 0UL g') /\
                                          (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t)) 
                                 (*(ensures (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) /\
                                       x <> h_index ==>  read_word g y == read_word g' y))*)
                                 (ensures (forall x. Seq.mem x (objects2 0UL g) /\  x <> h_index ==> 
                                            (forall y. (Usize.v y >= Usize.v x + Usize.v mword) /\
                                                  (Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword)) ==>
                                                    read_word g y == read_word g' y)))  =
Classical.forall_intro (Classical.move_requires (field_reads_all_equal_lemma g g' h_index))

#restart-solver 

#restart-solver 

#push-options "--z3rlimit 500"

#restart-solver

#restart-solver

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

let colorHeader1  (v_id:hp_addr)  
                  (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                  (c:color)
             : Tot (g': heap{Seq.length g == Seq.length g' /\
                             (length (slice g' (Usize.v v_id) ((Usize.v v_id) + (Usize.v mword))) = 8) /\
                             read_word g' v_id == makeHeader (wosize_of_object1 v_id g) (c) (tag_of_object1 v_id g) /\
                            heap_remains_same_except_index_v_id v_id g g' /\
                            color_of_object1 v_id g' == c /\
                            wosize_of_object1 v_id g' == wosize_of_object1 v_id g /\
                            tag_of_object1 v_id g' == tag_of_object1 v_id g /\
                            objects2 0UL g == objects2 0UL g' (*/\
                            well_formed_heap2 g' /\ is_valid_header v_id g'*)}) =
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
 assert (Seq.mem h_index (get_allocated_block_addresses g));
 assert (Seq.length (objects2 0UL g) > 0);

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 

 assert (heap_remains_same_except_index_v_id h_index g g');

 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.mem v_id (objects2 0UL g'));
 assert (is_fields_contents_within_limit2 v_id wz g);
 assert (Seq.length g == Seq.length g');
 lemma_len_slice g' (Usize.v  v_id) ((Usize.v  v_id) + (Usize.v mword));
 assert (read_word g' v_id == makeHeader (wosize_of_object1 v_id g) (c) (tag_of_object1 v_id g));
 assert (heap_remains_same_except_index_v_id v_id g g');
 assert (color_of_object1 v_id g' == c /\
                            wosize_of_object1 v_id g' == wosize_of_object1 v_id g /\
                            tag_of_object1 v_id g' == tag_of_object1 v_id g /\
                            objects2 0UL g == objects2 0UL g');
 g'

#restart-solver 
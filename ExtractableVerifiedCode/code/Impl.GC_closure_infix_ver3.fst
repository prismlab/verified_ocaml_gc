(*Title: Mechanized Verification of OCaml style Garbage Collectors (Version that handles closure and infix objects)
Author: Sheera Shamsu
Date of Creation: 23/11/2023

Copyright © [2023] [Sheera Shamsu]. All rights reserved.

This document serves as a declaration of copyright ownership for the work titled Mechanized Verification of OCaml style Garbage Collectors, created by 
Sheera Shamsu on 23/11/2023. The copyright owner retains all exclusive rights to reproduce, distribute, display, and perform the work.

Any unauthorized use, reproduction, or distribution of this work, in whole or in part, is strictly prohibited without the written permission of the copyright owner.

For inquiries regarding the use or licensing of this work, please contact:

Sheera Shamsu
email: sheera.shms@gmail.com
This copyright document is governed by the laws of India/Chennai and any disputes arising from its use shall be subject to the jurisdiction of the courts in 
India/Chennai.*)


/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
/// Low* Specification and Implementation of a Mark and Sweep Garbage Collector (GC) that acts on OCaml style objects and a heap memory compatible with OCaml heap memory.
/// Each of the sub-functions that make up a Mark and sweep GC like, root_greying, mark and sweep is implemented in Low* and their output is proven to be equivalent
/// to their respective functional counter parts. The same startegy can be applied for adding more features and verifying them on the go.

module Impl.GC_closure_infix_ver3

module Sq =  FStar.Seq
module Sq_base = FStar.Seq.Base

module H = FStar.HyperStack

module HA = FStar.HyperStack.All

module Usize = FStar.UInt64

module B = LowStar.Buffer

/// S represents the functional layer where functional GC is implemented---------------------------------------------------------------------------------------
module S = Spec.GC_infix_closure_ver3
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------
/// G represents the graph layer where graph and reachability definitions are there
module G = Spec.Graph3
/// ----------------------------------------------------------------------------------------------------------------------------------------------------------
module MB = LowStar.Monotonic.Buffer

module ST = FStar.HyperStack.ST

module L = FStar.List.Tot

open LowStar.BufferOps

open FStar.Mul 
open FStar.Endianness

open LowStar.Endianness

module C = C.Loops

/// ----------------------------------------------------------------------------------------------------------------------------------------------------------
#set-options "--max_fuel 3 --max_ifuel 0 --z3rlimit 50"

let getColor h = 
 let _ = S.max_color_size_lemma () in
 let _ = assert (Usize.v S.max_color = pow2 2 - 1) in
 
 let c' = Usize.shift_right h 8ul in
 let c = Usize.logand c' 3UL in
 
 assert (Usize.v c' == Usize.v h/ pow2 8);
 assert (Usize.v c' <= pow2 64/pow2 8);
 Math.Lemmas.pow2_minus 64 8;
 assert (Usize.v c' <= pow2 56);
 UInt.logand_le #64 (Usize.v c') 3;
 assert (Usize.v c <= Usize.v c');

 assert (Usize.v c <= Usize.v S.max_color);
 assert (Usize.v  h <= UInt.max_int 64);
 assert (Usize.v h <= pow2 64 - 1);
 assert (Usize.v c <=  pow2 64 - 1);
 assert (Usize.v S.max_color <= pow2 64 - 1);
 c

let makeHeader wz c tg = 
S.makeHeader wz c tg

inline_for_extraction
let read_word_from_byte_buffer g byte_index = 
  load64_le_i g (UInt32.uint_to_t (UInt64.v byte_index))

inline_for_extraction
let write_word_to_byte_buffer g byte_index v = 
 let h0 = ST.get () in
 store64_le_i g FStar.UInt32.(UInt32.uint_to_t (UInt64.v byte_index)) v;
 let h1 = ST.get () in
//le_to_n produces a value
 assert (le_to_n (Seq.slice (B.as_seq h1 g) (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)))) 
                                                     (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)) + 8))) == UInt64.v v);
 assert (Seq.equal (Seq.slice (B.as_seq h0 g) 0 (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)))))
                      (Seq.slice (B.as_seq h1 g) 0 FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)))));
 assert (Seq.equal (Seq.slice (B.as_seq h0 g) (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)) + 8)) (B.length g))
                      (Seq.slice (B.as_seq h1 g) (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)) + 8)) (B.length g)));


 assert (S.read_word (B.as_seq h1 g) (byte_index) == v);
 assert (Seq.length (B.as_seq h1 g) == Seq.length (B.as_seq h0 g));
 Seq.lemma_eq_elim (S.write_word (B.as_seq h0 g) byte_index v) (B.as_seq h1 g);
 assert (S.write_word (B.as_seq h0 g) byte_index v == B.as_seq h1 g);
 ()



let wosize_of_block v_id g = 
let index = read_word_from_byte_buffer g v_id in
let wz = S.getWosize index in
wz


let color_of_block v_id g = 
let index = read_word_from_byte_buffer g v_id in
let cl = S.getColor index in (*Since wosize is a Usize.t, this is fine*)
cl


let tag_of_block v_id g = 
let index = read_word_from_byte_buffer g v_id in
let tg = S.getTag index in 
tg

let colorHeader1 g v_id c = 
 let h0 = ST.get() in
 let wz = wosize_of_block v_id g in

 let h1 = ST.get() in
 assert (h0 == h1);
 let tg = tag_of_block v_id g in

 let h2 = ST.get() in
 assert (h1 == h2);
 let h_val = S.makeHeader wz c tg in 

 let h3 = ST.get() in
 
 assert (wz == S.getWosize h_val);
 assert (c == S.getColor h_val);
 assert (tg == S.getTag h_val);
 //assert  (UInt32.v (UInt32.uint_to_t (UInt64.v v_id)) < B.length g / 8);
 assert  (store_pre g (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v v_id)))) 8 (fun s -> le_to_n s == UInt64.v h_val) h3);
 write_word_to_byte_buffer g v_id h_val;
 
 let h = ST.get() in
 assert (B.modifies (B.loc_buffer g) h3 h);
 assert (B.modifies (B.loc_buffer g) h2 h);
 assert (B.modifies (B.loc_buffer g) h0 h);
 assert ((B.as_seq h g) == S.colorHeader1 (v_id_f v_id) (B.as_seq h0 g) c);
 ()

#push-options "--split_queries always"

#restart-solver

let push_to_stack g st st_len elem =
                              
 let open Usize in
 let h0 = ST.get() in
 let i = !*st_len in

 let f_elem = S.f_address elem in
 B.upd st (UInt32.uint_to_t (Usize.v i)) f_elem;
 let h0' = ST.get() in
 st_len.(0ul) <- !*st_len +^ 1UL;
 let h1 = ST.get() in
 let i1 = !*st_len in
 assert (B.modifies (B.loc_union (B.loc_buffer st) (B.loc_buffer st_len)) h0 h1);
 colorHeader1 g elem S.gray;
 let h2 = ST.get() in
 assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st) (B.loc_buffer st_len))) h0 h2);
 //assert (G.is_vertex_set (Seq.slice (B.as_seq h0 st) 0 (Usize.v i)));
 assert (G.is_vertex_set (stack_slice h0 st !i));
 assert (forall x. Seq.mem x (stack_slice h0 st !i) ==> Usize.v x >= !S.mword /\ Usize.v x < S.heap_size);

 assert (Seq.length (Seq.slice (B.as_seq h2 st) 0 (Usize.v i + 1)) == 
           Seq.length ((fst (S.push_to_stack2 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (Usize.v i)) elem))));
           
 (*The below three asserts are mandatory for proving the functional equivalence********************************************************************)
 assert (forall (j:nat{j < Seq.length (Seq.slice (B.as_seq h2 st) 0 (!(Seq.index (B.as_seq h0' st_len) 0)))}). 
                Seq.index (Seq.slice (B.as_seq h2 st) 0 (!(Seq.index (B.as_seq h0' st_len) 0))) j == 
                Seq.index ((fst (S.push_to_stack2 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (!(Seq.index (B.as_seq h0' st_len) 0))) elem))) j);
 
 
 assert (Seq.index (Seq.slice (B.as_seq h2 st) 0 (!(Seq.index (B.as_seq h2 st_len) 0))) !(Seq.index (B.as_seq h0' st_len) 0) == (v_id_f f_elem));

 assert ((Seq.slice (B.as_seq h2 st) 0 !(Seq.index (B.as_seq h2 st_len) 0)) ==
           Seq.snoc (Seq.slice (B.as_seq h2 st) 0 !(Seq.index (B.as_seq h0' st_len) 0)) (v_id_f f_elem));
 
 (*************************************************************************************************************************************************)
 assert (forall (j:nat{j < Seq.length (Seq.slice (B.as_seq h2 st) 0 (!(Seq.index (B.as_seq h2 st_len) 0)))}). 
                Seq.index (Seq.slice (B.as_seq h2 st) 0 (!(Seq.index (B.as_seq h2 st_len) 0))) j == 
                Seq.index ((fst (S.push_to_stack2 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (!(Seq.index (B.as_seq h0 st_len) 0))) elem))) j);


 Seq.lemma_eq_intro (stack_slice h2 st (!i + 1))
                                         (fst (S.push_to_stack2 (B.as_seq h0 g) (stack_slice h0 st !i) elem));
                                         
 Seq.lemma_eq_intro (B.as_seq h2 g) (snd (S.push_to_stack2 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (Usize.v i)) elem));
 assert (S.well_formed_heap2 (B.as_seq h2 g));
 assert (S.is_valid_header (v_id_f elem) (B.as_seq h2 g));
 ()

let read_succ_impl g h_index i =
let m0 = ST.get() in
let succ_index = Usize.add h_index (Usize.mul i S.mword) in
assert (succ_index == S.succ_index_fn (B.as_seq m0 g) h_index i);
assert (Usize.v succ_index % Usize.v S.mword == 0);
assert (S.is_hp_addr succ_index);
let succ = read_word_from_byte_buffer g succ_index in
assert (succ == S.read_word (B.as_seq m0 g) succ_index);
assert (succ == S.read_succ (B.as_seq m0 g) h_index i);
succ

#restart-solver 

#restart-solver 

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let parent_closure_of_infix_object_impl g h_index i = 
 let m0 = ST.get() in
 let succ = read_succ_impl g h_index i in
 let h_addr_succ = S.hd_address succ in
 let h_addr_succ_val = read_word_from_byte_buffer g h_addr_succ in
 let wosize = S.getWosize h_addr_succ_val in
 assert (S.is_hp_addr succ);
 assert (UInt.fits (Usize.v succ - (Usize.v wosize * Usize.v S.mword)) Usize.n);
 let parent_succ = Usize.sub succ (Usize.mul wosize S.mword) in
 assert (Usize.v parent_succ >= Usize.v S.mword);
 let h_addr_parent = S.hd_address parent_succ in
 assert (S.is_hp_addr h_addr_parent);
 assert (S.is_valid_header h_addr_parent (B.as_seq m0 g));
 assert (Usize.v (S.tag_of_object1 h_addr_parent (B.as_seq m0 g)) == S.closure_tag);
 assert (Usize.v h_addr_parent + Usize.v S.mword < S.heap_size);
 assert (UInt.fits (Usize.v h_addr_parent + Usize.v S.mword) Usize.n);
 assert (h_addr_parent == S.parent_closure_of_infix_object (B.as_seq m0 g) h_index i);
 h_addr_parent

#reset-options "--max_fuel 3 --max_ifuel 0 --z3rlimit 50"

#push-options "--split_queries always"

//#push-options "--z3rlimit 1000"

#restart-solver

let darken_helper_impl g st st_len hdr_id =
 let h1 = ST.get() in
 if color_of_block hdr_id g = S.white then
 (
   S.valid_succ_color_lemma (B.as_seq h1 g) (v_id_f hdr_id);
   assert (Seq.mem (v_id_f hdr_id) (S.objects2 0UL (B.as_seq h1 g)) /\
           (S.color_of_object1 (v_id_f hdr_id) (B.as_seq h1 g) <> S.gray));
   S.stack_less_than_heap_size_when_one_non_gray_exists (B.as_seq h1 g) 
                                                        (stack_slice h1 st (stack_end h1 st_len))
                                                        (v_id_f hdr_id);
   assert (Seq.length (stack_slice h1 st (stack_end h1 st_len)) < S.heap_size);
   assert ((!(Seq.index (B.as_seq h1 st_len) 0)) < S.heap_size);
   assert (~(S.isGrayObject1 (v_id_f hdr_id) (B.as_seq h1 g)) /\ ~(S.isBlackObject1 (v_id_f hdr_id) (B.as_seq h1 g)));
   assert (~(Seq.mem (v_id_f (S.f_address hdr_id)) (stack_slice h1 st (!(Seq.index (B.as_seq h1 st_len) 0)))));
   assert (~(Seq.mem (S.f_address hdr_id) (stack_slice h1 st (stack_end h1 st_len))));
   S.stack_mem_lemma (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) (v_id_f hdr_id);
   push_to_stack g st st_len hdr_id;
   let h3 = ST.get() in
   S.push_to_stack2_heap_state_lemma (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) (v_id_f hdr_id);
   S.push_to_stack2_field_size_lemma (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) (v_id_f hdr_id);

   S.objects2_equal_lemma 0UL (B.as_seq h1 g) (B.as_seq h3 g);

   S.push_to_stack2_lemma (B.as_seq h1 g)  (stack_slice h1 st (stack_end h1 st_len)) (v_id_f hdr_id);
   
   assert (stack_slice h3 st (stack_end h3 st_len) ==
                              fst (S.push_to_stack2 (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) hdr_id));
                                                     
   assert (B.as_seq h3 g == snd (S.push_to_stack2 (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) hdr_id));
   Seq.lemma_eq_intro (B.as_seq h3 g) 
                          (snd (S.darken_helper (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) hdr_id));
   Seq.lemma_eq_intro (stack_slice h3 st (stack_end h3 st_len))
                           (fst (S.darken_helper (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) hdr_id));
   assert ((B.as_seq h3 g) == (snd (S.darken_helper (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) hdr_id)));
   assert (stack_slice h3 st (stack_end h3 st_len) == (fst (S.darken_helper (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) hdr_id)));
                
   assert (modified3 h1 h3 g st st_len);
   assert (!(Seq.index (B.as_seq h3 st_len) 0) <= S.heap_size);
   ()
 )
 else
 (
   ()
 )

#restart-solver

let darken_body g st st_len h_index wz i  = 
  let h1 = ST.get() in

  S.field_limits_allocated_blocks_lemma (B.as_seq h1 g);
  S.field_contents_within_limits_allocated_blocks_lemma (B.as_seq h1 g);

  assert (S.is_fields_within_limit1 h_index (S.getWosize (S.read_word (B.as_seq h1 g) h_index)));
  assert (S.is_fields_contents_within_limit2 h_index (S.getWosize (S.read_word (B.as_seq h1 g) h_index)) (B.as_seq h1 g));
  
  let succ_index = Usize.add h_index (Usize.mul i S.mword) in

  assert (S.is_valid_header (v_id_f h_index) (B.as_seq h1 g));
  assert (!i <= !wz);
  assert (!succ_index < S.heap_size); 

  S.max_wosize_times_mword_multiple_of_mword i;

  assert ((!(Usize.mul i S.mword) % !S.mword == 0));
  
  S.sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i S.mword);

  assert ((!h_index + !(Usize.mul i S.mword)) % (!S.mword) == 0);

  assert (!succ_index % !S.mword == 0);
  assert (S.is_hp_addr succ_index);
  let succ = read_word_from_byte_buffer g succ_index in
  let h2 = ST.get() in
  assert (h1 == h2); (*No heap change, hence this assert passes*)
  assert (succ == S.read_word (B.as_seq h1 g) succ_index);
  assert (Seq.mem h_index (S.objects2 0UL (B.as_seq h1 g)));
 if isPointer succ_index g then 
 (
   let h_addr_succ = S.hd_address succ in
   if tag_of_block h_addr_succ g = Usize.uint_to_t (S.infix_tag) then
   (
     assert (Usize.v (S.tag_of_object1 h_addr_succ (B.as_seq h1 g)) == S.infix_tag);
     let parent_hdr = parent_closure_of_infix_object_impl g h_index i in
     darken_helper_impl g st st_len parent_hdr;
     let h3 = ST.get() in
     assert (stack_slice h3 st (stack_end h3 st_len) == fst (S.darken_helper (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) parent_hdr));
     assert ((B.as_seq h3 g) == (snd (S.darken_helper (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) parent_hdr)));
     
     Seq.lemma_eq_intro (B.as_seq h3 g) 
                          (snd (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                                       (stack_slice h1 st (stack_end h1 st_len))
                                                       (h_index)
                                                       (wz)
                                                       (i)));
    Seq.lemma_eq_intro (stack_slice h3 st (stack_end h3 st_len))
                           (fst (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                                       (stack_slice h1 st (stack_end h1 st_len))
                                                       (h_index)
                                                       (wz)
                                                       (i)));
    ()
   )
   else
   (
     assert (Usize.v (S.tag_of_object1 h_addr_succ (B.as_seq h1 g)) <> S.infix_tag);
     darken_helper_impl g st st_len h_addr_succ;
     let h3 = ST.get() in
       
     assert (stack_slice h3 st (stack_end h3 st_len) ==
                              fst (S.darken_helper (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) h_addr_succ));
     assert ((B.as_seq h3 g) == (snd (S.darken_helper (B.as_seq h1 g) (stack_slice h1 st (stack_end h1 st_len)) h_addr_succ)));
     Seq.lemma_eq_intro (B.as_seq h3 g) 
                          (snd (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                                       (stack_slice h1 st (stack_end h1 st_len))
                                                       (h_index)
                                                       (wz)
                                                       (i)));
     Seq.lemma_eq_intro (stack_slice h3 st (stack_end h3 st_len))
                           (fst (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                                       (stack_slice h1 st (stack_end h1 st_len))
                                                       (h_index)
                                                       (wz)
                                                       (i)));
     ()
   )
 )
 else
 (
   ()
 )

#restart-solver 

let darken g st st_len h_index wz =  
 let h0 = ST.get() in
 let inv h (i: nat) = B.live h g /\ B.live h st /\ B.live h st_len /\
                    B.length st_len == 1  /\
                    stack_end h st_len <= S.heap_size /\
                     
                    disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\
                   
                    i <= Usize.v wz + 1 /\
                    i >= 1 /\
                    (Usize.v wz == Usize.v (S.getWosize (S.read_word (B.as_seq h g) h_index))) /\
                    
                    S.well_formed_heap2 (B.as_seq h g) /\

                    S.is_valid_header1 (v_id_f h_index) (B.as_seq h g) /\
                    
                    stack_props h g st st_len /\
                    
                    (modified3 h0 h g st st_len) /\
                    (S.objects2 0UL (B.as_seq h g) ==
                     S.objects2 0UL (B.as_seq h0 g)) /\
                    S.fieldPush_spec1 (B.as_seq h g) 
                                      (stack_slice h st (stack_end h st_len))
                                      (h_index) 
                                      (wz) 
                                      (Usize.uint_to_t i) ==
                    S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (stack_slice h0 st (stack_end h0 st_len))
                                      (h_index) 
                                      (wz) 
                                      1UL in
 
 let body (i: UInt32.t{ 1 <= UInt32.v i /\ UInt32.v i < Usize.v wz + 1})
    : HA.Stack unit
    (requires (fun m -> inv m (UInt32.v i)))
    (ensures (fun m0 () m1 -> inv m0 (UInt32.v i) /\ inv m1 (UInt32.v i + 1))) =
 let h1 = ST.get() in
 darken_body g st st_len h_index wz (Usize.uint_to_t (UInt32.v i));
 let h3 = ST.get() in
 let i' = Usize.((Usize.uint_to_t (UInt32.v i ) ) +^ 1UL) in
 assert ((B.as_seq h3 g) ==  (snd (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                                         (stack_slice h1 st (stack_end h1 st_len))
                                                         (h_index)
                                                         (wz)
                                                         ((Usize.uint_to_t (UInt32.v i))))));
                
 assert (stack_slice h3 st (stack_end h3 st_len) ==
                 (fst (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                             (stack_slice h1 st (stack_end h1 st_len))
                                             (h_index)
                                             (wz)
                                             ((Usize.uint_to_t (UInt32.v i ) )))));

 assert (S.fieldPush_spec1 (B.as_seq h3 g) 
                           (stack_slice h3 st (stack_end h3 st_len))
                           (h_index) 
                           (wz) 
                           (i') ==
         S.fieldPush_spec1 (snd (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                                       (stack_slice h1 st (stack_end h1 st_len))
                                                       (h_index)
                                                       (wz)
                                                       ((Usize.uint_to_t (UInt32.v i ) ))))
                           (fst (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                                       (stack_slice h1 st (stack_end h1 st_len))
                                                       (h_index)
                                                       (wz)
                                                       ((Usize.uint_to_t (UInt32.v i ) ))))
                           (h_index) 
                           (wz) 
                           (i'));

 S.fieldPush_fieldPush_spec_body_lemma (B.as_seq h1 g)
                                       (stack_slice h1 st (stack_end h1 st_len))
                                       (h_index)
                                       (wz)
                                       ((Usize.uint_to_t (UInt32.v i ) ))
                                       (i');

 assert (S.fieldPush_spec1 (B.as_seq h3 g) 
                           (stack_slice h3 st (stack_end h3 st_len))
                           (h_index) 
                           (wz) 
                           (i') ==
        S.fieldPush_spec1 (B.as_seq h1 g) 
                          (stack_slice h1 st (stack_end h1 st_len))
                          (h_index) 
                          (wz) 
                          ((Usize.uint_to_t (UInt32.v i ) )));

assert (S.fieldPush_spec1 (B.as_seq h1 g) 
                          (stack_slice h1 st (stack_end h1 st_len))
                          (h_index) 
                          (wz) 
                          ((Usize.uint_to_t (UInt32.v i ) )) ==
          S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (stack_slice h0 st (stack_end h0 st_len))
                                      (h_index) 
                                      (wz) 
                                      1UL);
 
assert (S.fieldPush_spec1 (B.as_seq h3 g) 
                          (stack_slice h3 st (stack_end h3 st_len))
                          (h_index) 
                          (wz) 
                          (i') ==
                    S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (stack_slice h0 st (stack_end h0 st_len))
                                      (h_index) 
                                      (wz) 
                                      1UL) in
 C.Loops.for 1ul (UInt32.uint_to_t (Usize.v Usize.(wz +^ 1UL))) inv body;
 let h4 = ST.get() in
 assert (S.fieldPush_spec1 (B.as_seq h4 g) 
                           (stack_slice h4 st (stack_end h4 st_len))
                           (h_index) 
                           (wz) 
                           (Usize.(wz +^ 1UL)) ==
                    S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (stack_slice h0 st (stack_end h0 st_len))
                                      (h_index) 
                                      (wz) 
                                      1UL);

S.fieldPush_fieldPush_spec_body_lemma1 (B.as_seq h4 g) 
                                       (stack_slice h4 st (stack_end h4 st_len))
                                       (h_index) 
                                       (wz) 
                                       (Usize.(wz +^ 1UL));

assert (stack_slice h4 st (stack_end h4 st_len) ==
            fst (S.fieldPush_spec1 (B.as_seq h4 g) 
                                   (stack_slice h4 st (stack_end h4 st_len))
                                   (h_index) 
                                   (wz) 
                                   (Usize.(wz +^ 1UL))));

assert (stack_slice h4 st (stack_end h4 st_len) == 
               fst (S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (stack_slice h0 st (stack_end h0 st_len))
                                      (h_index) 
                                      (wz) 
                                      1UL));
assert ((B.as_seq h4 g)  ==
           snd (S.fieldPush_spec1 (B.as_seq h4 g) 
                                  (stack_slice h4 st (stack_end h4 st_len))
                                  (h_index) 
                                  (wz) 
                                  (Usize.(wz +^ 1UL))));
                                      
 assert (modified3 h0 h4 g st st_len);
 assert (stack_end h4 st_len <= S.heap_size);
 assert (stack_props h4 g st st_len);
 ()
 
#restart-solver 

let darken1 g st st_len h_index wz j =
  let h0 = ST.get() in
  let inv h (i: nat) = B.live h g /\ B.live h st /\ B.live h st_len /\
                    B.length st_len == 1  /\
                    stack_end h st_len <= S.heap_size /\
                     
                    disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\
                   
                    i <= Usize.v wz + 1 /\
                    i >= Usize.v j /\
                    Usize.v j <= Usize.v wz /\
                    Usize.v j >= 1 /\
                    (Usize.v wz == Usize.v (S.getWosize (S.read_word (B.as_seq h g) h_index))) /\
                    
                    S.well_formed_heap2 (B.as_seq h g) /\

                    S.is_valid_header1 (v_id_f h_index) (B.as_seq h g) /\
                    
                    stack_props h g st st_len /\
                    
                    (modified3 h0 h g st st_len) /\
                    (S.objects2 0UL (B.as_seq h g) ==
                     S.objects2 0UL (B.as_seq h0 g)) /\
                    S.fieldPush_spec1 (B.as_seq h g) 
                                      (stack_slice h st (stack_end h st_len))
                                      (h_index) 
                                      (wz) 
                                      (Usize.uint_to_t i) ==
                    S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (stack_slice h0 st (stack_end h0 st_len))
                                      (h_index) 
                                      (wz) 
                                      j in
  let body (i: UInt32.t{Usize.v j <= UInt32.v i /\ UInt32.v i < Usize.v wz + 1})
    : HA.Stack unit
    (requires (fun m -> inv m (UInt32.v i)))
    (ensures (fun m0 () m1 -> inv m0 (UInt32.v i) /\ inv m1 (UInt32.v i + 1))) =
 let h1 = ST.get() in
 darken_body g st st_len h_index wz (Usize.uint_to_t (UInt32.v i));
 let h3 = ST.get() in
 let i' = Usize.((Usize.uint_to_t (UInt32.v i ) ) +^ 1UL) in
 assert ((B.as_seq h3 g) ==  (snd (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                                         (stack_slice h1 st (stack_end h1 st_len))
                                                         (h_index)
                                                         (wz)
                                                         ((Usize.uint_to_t (UInt32.v i))))));
                
 assert (stack_slice h3 st (stack_end h3 st_len) ==
                 (fst (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                             (stack_slice h1 st (stack_end h1 st_len))
                                             (h_index)
                                             (wz)
                                             ((Usize.uint_to_t (UInt32.v i ) )))));

 assert (S.fieldPush_spec1 (B.as_seq h3 g) 
                           (stack_slice h3 st (stack_end h3 st_len))
                           (h_index) 
                           (wz) 
                           (i') ==
         S.fieldPush_spec1 (snd (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                                       (stack_slice h1 st (stack_end h1 st_len))
                                                       (h_index)
                                                       (wz)
                                                       ((Usize.uint_to_t (UInt32.v i ) ))))
                           (fst (S.fieldPush_spec_body1 (B.as_seq h1 g)
                                                       (stack_slice h1 st (stack_end h1 st_len))
                                                       (h_index)
                                                       (wz)
                                                       ((Usize.uint_to_t (UInt32.v i ) ))))
                           (h_index) 
                           (wz) 
                           (i'));

 S.fieldPush_fieldPush_spec_body_lemma (B.as_seq h1 g)
                                       (stack_slice h1 st (stack_end h1 st_len))
                                       (h_index)
                                       (wz)
                                       ((Usize.uint_to_t (UInt32.v i ) ))
                                       (i');

 assert (S.fieldPush_spec1 (B.as_seq h3 g) 
                           (stack_slice h3 st (stack_end h3 st_len))
                           (h_index) 
                           (wz) 
                           (i') ==
        S.fieldPush_spec1 (B.as_seq h1 g) 
                          (stack_slice h1 st (stack_end h1 st_len))
                          (h_index) 
                          (wz) 
                          ((Usize.uint_to_t (UInt32.v i))));

assert (S.fieldPush_spec1 (B.as_seq h1 g) 
                          (stack_slice h1 st (stack_end h1 st_len))
                          (h_index) 
                          (wz) 
                          ((Usize.uint_to_t (UInt32.v i))) ==
          S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (stack_slice h0 st (stack_end h0 st_len))
                                      (h_index) 
                                      (wz) 
                                      j);
 
assert (S.fieldPush_spec1 (B.as_seq h3 g) 
                          (stack_slice h3 st (stack_end h3 st_len))
                          (h_index) 
                          (wz) 
                          (i') ==
                    S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (stack_slice h0 st (stack_end h0 st_len))
                                      (h_index) 
                                      (wz) 
                                      j) in
 C.Loops.for ((UInt32.uint_to_t (Usize.v j))) (UInt32.uint_to_t (Usize.v Usize.(wz +^ 1UL))) inv body;
 let h4 = ST.get() in
 assert (S.fieldPush_spec1 (B.as_seq h4 g) 
                           (stack_slice h4 st (stack_end h4 st_len))
                           (h_index) 
                           (wz) 
                           (Usize.(wz +^ 1UL)) ==
                    S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (stack_slice h0 st (stack_end h0 st_len))
                                      (h_index) 
                                      (wz) 
                                      j);

S.fieldPush_fieldPush_spec_body_lemma1 (B.as_seq h4 g) 
                                       (stack_slice h4 st (stack_end h4 st_len))
                                       (h_index) 
                                       (wz) 
                                       (Usize.(wz +^ 1UL));

assert (stack_slice h4 st (stack_end h4 st_len) ==
            fst (S.fieldPush_spec1 (B.as_seq h4 g) 
                                   (stack_slice h4 st (stack_end h4 st_len))
                                   (h_index) 
                                   (wz) 
                                   (Usize.(wz +^ 1UL))));

assert (stack_slice h4 st (stack_end h4 st_len) == 
               fst (S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (stack_slice h0 st (stack_end h0 st_len))
                                      (h_index) 
                                      (wz) 
                                      j));
assert ((B.as_seq h4 g)  ==
           snd (S.fieldPush_spec1 (B.as_seq h4 g) 
                                  (stack_slice h4 st (stack_end h4 st_len))
                                  (h_index) 
                                  (wz) 
                                  (Usize.(wz +^ 1UL))));
                                      
 assert (modified3 h0 h4 g st st_len);
 assert (stack_end h4 st_len <= S.heap_size);
 assert (stack_props h4 g st st_len);
 ()

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver 

let closinfo_val_impl g f_addr =
  let h0 = ST.get() in
  let hdr_f_addr = S.hd_address f_addr in
  assert (S.is_valid_header hdr_f_addr (B.as_seq h0 g));
  let wz = wosize_of_block hdr_f_addr g in
  assert (Usize.v wz >= 2);
  let offst1 = Usize.mul 1UL S.mword in
  let s1 = Usize.add f_addr offst1 in
  //assert (S.is_hp_addr s);
  assert (Usize.v s1 < S.heap_size);
  S.max_wosize_times_mword_multiple_of_mword 1UL;
  S.sum_of_multiple_of_mword_is_multiple_of_mword f_addr (Usize.mul 1UL S.mword);
  assert (Usize.v (Usize.add f_addr (Usize.mul 1UL S.mword)) % Usize.v S.mword == 0);
  assert (Usize.v s1 % Usize.v S.mword == 0);
  assert (S.is_hp_addr s1);
  let clos_info = read_word_from_byte_buffer g s1 in
  assert (clos_info == S.read_word (B.as_seq h0 g) s1);
  assert (clos_info == S.closinfo_val_from_closure_object (B.as_seq h0 g) f_addr);
  clos_info

#reset-options "--max_fuel 3 --max_ifuel 0 --z3rlimit 50"

#push-options "--split_queries always"

#restart-solver 

let start_env_clos_info g f_addr =
  let h0 = ST.get() in
  let clos_info = closinfo_val_impl g f_addr in
  let start_env = S.extract_start_env_bits' clos_info in
  start_env
 
#restart-solver 

#restart-solver 

#set-options "--max_fuel 3 --max_ifuel 0 --z3rlimit 50"

#push-options "--z3rlimit 2000"

#restart-solver

let darken_wrapper_impl g st st_len h_x wz =
 if tag_of_block h_x g = Usize.uint_to_t (S.closure_tag) then
  (
    let h1' = ST.get() in
    assert (Usize.v wz >= 2);
    let x = S.f_address h_x in
    let start_env = start_env_clos_info g x in
    let start_env_plus_one = Usize.add start_env 1UL in
    darken1 g st st_len h_x wz start_env_plus_one;
    let h2 = ST.get() in
    assert (B.live h2 g /\ B.live h2 st /\ B.live h2 st_len);
    assert (stack_end h2 st_len <= S.heap_size);                 
    assert (disjoint st st_len /\ disjoint g st /\ disjoint g st_len);
    assert (S.well_formed_heap2 (B.as_seq h2 g));               
    assert (S.is_valid_header (v_id_f h_x) (B.as_seq h2 g));             
    assert (stack_props h2 g st st_len);                 
    assert (modified3 h1' h2 g st st_len);               
    assert ((B.as_seq h2 g)  ==
                   snd (S.fieldPush_spec1 (B.as_seq h1' g) 
                                          (stack_slice h1' st (stack_end h1' st_len))
                                          (h_x) 
                                          (wz) 
                                          start_env_plus_one));              
                 
                  
    assert (stack_slice h2 st (stack_end h2 st_len) == 
                   fst (S.fieldPush_spec1 (B.as_seq h1' g) 
                                      (stack_slice h1' st (stack_end h1' st_len))
                                      (h_x) 
                                      (wz) 
                                      start_env_plus_one)); 
    
     ()
  )
  else
  (
     let h1' = ST.get() in
     darken1 g st st_len h_x wz 1UL;

     let h2 = ST.get() in
     assert (B.live h2 g /\ B.live h2 st /\ B.live h2 st_len);
     assert (stack_end h2 st_len <= S.heap_size);                 
     assert (disjoint st st_len /\ disjoint g st /\ disjoint g st_len);
     assert (S.well_formed_heap2 (B.as_seq h2 g));               
     assert (S.is_valid_header (v_id_f h_x) (B.as_seq h2 g));             
     assert (stack_props h2 g st st_len);                 
     assert (modified3 h1' h2 g st st_len);               
     assert ((B.as_seq h2 g)  ==
                   snd (S.fieldPush_spec1 (B.as_seq h1' g) 
                                          (stack_slice h1' st (stack_end h1' st_len))
                                          (h_x) 
                                          (wz) 
                                          1UL));              
                 
                  
     assert (stack_slice h2 st (stack_end h2 st_len) == 
                   fst (S.fieldPush_spec1 (B.as_seq h1' g) 
                                      (stack_slice h1' st (stack_end h1' st_len))
                                      (h_x) 
                                      (wz) 
                                      1UL));                
     ()
   )

#restart-solver 

#restart-solver

#restart-solver

let mark_heap_body1_impl g st st_len =
  let open Usize in
  let h0 = ST.get() in
  assert (stack_props h0 g st st_len);
  assert (let stack_top = !(Seq.index (B.as_seq h0 st_len) 0) in
         let stack_slice = Seq.slice (B.as_seq h0 st) 0 stack_top in
         (forall x. Seq.mem x stack_slice ==> !x >= !S.mword /\ Usize.v x < S.heap_size) /\
         (forall x. Seq.mem x stack_slice ==>  !x % !S.mword == 0) /\
         (forall x. Seq.mem x stack_slice ==> S.is_valid_header1 (S.hd_address x) (B.as_seq h0 g)) /\
         (forall x. Seq.mem (S.hd_address x) (S.objects2 0UL (B.as_seq h0 g)) /\ S.isGrayObject1 (S.hd_address x) (B.as_seq h0 g) <==>
                                           Seq.mem x stack_slice));
                                           
 
 Seq.lemma_slice_snoc  (Seq.slice (B.as_seq h0 st) 0 !(Seq.index (B.as_seq h0 st_len) 0)) 0 (!(Seq.index (B.as_seq h0 st_len) 0));
 assert (let s = Seq.slice (B.as_seq h0 st) 0 !(Seq.index (B.as_seq h0 st_len) 0) in
         let j = !(Seq.index (B.as_seq h0 st_len) 0) in
         let sl = Seq.slice s 0 j in
         let sl' = Seq.slice s 0 (j - 1) in
         (forall x. Seq.mem x sl <==> (x = Seq.index s (j - 1) || Seq.mem x sl')));
 
 st_len.(0ul) <- !*st_len -^ 1UL;   
 
 let h0' = ST.get() in // After stack top is decremented
 assert (stack_end h0' st_len == (stack_end h0 st_len) - 1);
 assert (B.as_seq h0' st == B.as_seq h0 st);
 assert (B.modifies (B.loc_buffer st_len) h0 h0');

 //                                                                            (B.as_seq h0 g)   ---> Intial GC heap memory (g)
 //            (Seq.slice (B.as_seq h0 st) 0 (stack_end h0 st_len))                              ---> Initial stack (st)
 // (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (stack_end h0 st_len)) 0 (stack_end h0' st_len));   ---> stack with stack top decremented (s)
 
 assert (let stack_top = !(Seq.index (B.as_seq h0' st_len) 0) in
         let stack_slice = Seq.slice (B.as_seq h0' st) 0 stack_top in
         (forall x. Seq.mem x stack_slice ==> !x >= !S.mword /\ Usize.v x < S.heap_size) /\
         (forall x. Seq.mem x stack_slice ==>  !x % !S.mword == 0) /\
         (forall x. Seq.mem x stack_slice ==> S.is_valid_header1 (S.hd_address x) (B.as_seq h0' g)));

 let x =  st.(UInt32.uint_to_t (Usize.v !*st_len )) in // last element of the stack is popped
 let h1 = ST.get() in
 assert (h0' == h1);
 let h_x = S.hd_address x in
 assert (S.is_valid_header1 h_x (B.as_seq h1 g));
 assert (x == Seq.index (stack_slice h0 st (stack_end h0 st_len)) ((stack_end h0 st_len) - 1));
 (*The length of the stack is equal to the value stored at the st_top at h0 memory state*)
 assert (Seq.length (stack_slice h0 st (stack_end h0 st_len)) == (stack_end h0 st_len));
 assert (x == Seq.index (stack_slice h0 st (stack_end h0 st_len)) (stack_end h1 st_len)); 
 assert (B.modifies (B.loc_buffer st_len) h0 h1);                                        
 assert ((B.as_seq h1 st) == (B.as_seq h0 st));
 assert ((B.as_seq h1 g) == (B.as_seq h0 g));                                                                               
 G.is_vertex_set_lemma3 (stack_slice h0 st (stack_end h0 st_len));
 assert (G.is_vertex_set (Seq.slice (stack_slice h0 st (stack_end h0 st_len)) 0 (stack_end h1 st_len)));
 colorHeader1 g h_x S.black;
 let h1' = ST.get() in

 S.colorHeader5_lemma (v_id_f h_x) (B.as_seq h1 g) S.black;
 
 S.colorHeader1_alloc_colors_lemma (v_id_f h_x) (B.as_seq h1 g) S.black;
 
 (*assert (S.get_allocated_block_addresses (B.as_seq h1 g) == 
                S.get_allocated_block_addresses (B.as_seq h1' g));*)
 G.is_vertex_set_lemma5 (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0)));
 assert (~(Seq.mem x (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_len) 0)))));
 assert (~(Seq.mem x (Seq.slice (stack_slice h0 st (stack_end h0 st_len)) 0 (stack_end h1 st_len))));
 Seq.lemma_mem_snoc (Seq.slice (stack_slice h0 st (stack_end h0 st_len)) 0 (stack_end h1 st_len)) x;
 assert (forall y. Seq.mem y (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0))) 0 
                 (Usize.v (Seq.index (B.as_seq h0' st_len) 0))) \/  (y == x) <==> Seq.mem (S.hd_address y) (S.objects2 0UL (B.as_seq h1 g)) /\  
                 S.isGrayObject1 (S.hd_address y) (B.as_seq h1 g));
 
 assert (forall y. Seq.mem y (Seq.slice (stack_slice h0 st (stack_end h0 st_len)) 0 (stack_end h1 st_len)) \/  (y == x) <==> 
                  Seq.mem (S.hd_address y) (S.objects2 0UL (B.as_seq h1 g)) /\  S.isGrayObject1 (S.hd_address y) (B.as_seq h1 g));
 assert (S.all_mem_st_mem_st__except_v_id_in_stack x 
                                                  (stack_slice h0 st (stack_end h0 st_len))
                                                  (Seq.slice (stack_slice h0 st (stack_end h0 st_len)) 0 (stack_end h1 st_len)));
 
 let wz = wosize_of_block h_x g in
  
 assert (S.color_of_object1 h_x (B.as_seq h1' g) == S.black);
 assert (S.color_of_object1 h_x (B.as_seq h1 g) == S.gray);
 assert (h_x == S.hd_address x);
 assert (x == S.f_address h_x);
 assert (forall y. Seq.mem y (Seq.slice (stack_slice h0 st (stack_end h0 st_len)) 0 (stack_end h1 st_len)) \/  (y == S.f_address h_x) <==> 
                  Seq.mem (S.hd_address y) (S.objects2 0UL (B.as_seq h1 g)) /\  S.isGrayObject1 (S.hd_address y) (B.as_seq h1 g));
 
 
 S.slice_coloring_lemma1 (B.as_seq h1 g) 
                         (B.as_seq h1' g) 
                         h_x 
                        (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0)))
                        (Seq.index (B.as_seq h1 st_len) 0);
 assert (~(S.color_of_object1 h_x (B.as_seq h1' g) == S.gray));
 assert (forall y. Seq.mem y (Seq.slice (stack_slice h0 st (stack_end h0 st_len)) 0 (stack_end h1 st_len)) <==>
                             Seq.mem (S.hd_address y) (S.objects2 0UL (B.as_seq h1' g)) /\ S.isGrayObject1 (S.hd_address y) (B.as_seq h1' g));
 
                                                        
 assert (forall y. Seq.mem y (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_len) 0))) <==>
         Seq.mem (S.hd_address y) (S.objects2 0UL (B.as_seq h1' g)) /\ S.isGrayObject1 (S.hd_address y) (B.as_seq h1' g));     
 
 assert (0 <= (Usize.v (Seq.index (B.as_seq h0 st_len) 0))); 
 assert ((Usize.v (Seq.index (B.as_seq h0 st_len) 0)) <= Seq.length (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0))));
 assert (0 <= (Usize.v (Seq.index (B.as_seq h0' st_len) 0))); 
 assert ((Usize.v (Seq.index (B.as_seq h0' st_len) 0)) == (Usize.v (Seq.index (B.as_seq h0 st_len) 0)) - 1);
 //assert ((Usize.v (Seq.index (B.as_seq h0' st_len) 0)) <= (Usize.v (Seq.index (B.as_seq h0 st_len) 0)));
 Seq.slice_slice (B.as_seq h0 st) 
                 0 
                 (Usize.v (Seq.index (B.as_seq h0 st_len) 0))
                 0
                 (Usize.v (Seq.index (B.as_seq h0' st_len) 0));
 

 assert (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_len) 0)) ==
            Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0' st_len) 0)));
 
 assert (forall y. Seq.mem y (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0' st_len) 0))) <==>
         Seq.mem (S.hd_address y) (S.objects2 0UL (B.as_seq h1' g)) /\ S.isGrayObject1 (S.hd_address y) (B.as_seq h1' g)); 
 
 assert (forall y. Seq.mem y (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_len) 0))) <==>
         Seq.mem (S.hd_address y) (S.objects2 0UL (B.as_seq h1' g)) /\ S.isGrayObject1 (S.hd_address y) (B.as_seq h1' g)); 
 assert (Usize.v (Seq.index (B.as_seq h1 st_len) 0) == (Usize.v (Seq.index (B.as_seq h1' st_len) 0)));
 
 assert (forall y. Seq.mem y (Seq.slice (B.as_seq h1' st) 0 (Usize.v (Seq.index (B.as_seq h1' st_len) 0))) <==>
         Seq.mem (S.hd_address y) (S.objects2 0UL (B.as_seq h1' g)) /\ S.isGrayObject1 (S.hd_address y) (B.as_seq h1' g));
 
 assert (B.live h1' g /\ B.live h1' st /\ B.live h1' st_len);
 assert (stack_end h1' st_len <= S.heap_size );               
 assert (disjoint st st_len /\ disjoint g st /\ disjoint g st_len);
 assert (S.well_formed_heap2 (B.as_seq h1' g));                
 assert (S.is_valid_header (v_id_f h_x) (B.as_seq h1' g));                
 assert (!wz == !(S.getWosize (S.read_word (B.as_seq h1' g) h_x)));                 
 assert (stack_props h1' g st st_len);
 let tg = tag_of_block h_x g in
 
 if (tg <^ UInt64.uint_to_t (S.no_scan_tag)) then
 (
    assert  (Usize.v (S.tag_of_object1 h_x (B.as_seq h1' g)) < S.no_scan_tag);
    assert (B.live h1' g /\ B.live h1' st /\ B.live h1' st_len);
    assert (stack_end h1' st_len <= S.heap_size);             
    assert (disjoint st st_len /\ disjoint g st /\ disjoint g st_len);
    assert (S.well_formed_heap2 (B.as_seq h1' g));             
    assert (S.is_valid_header (v_id_f h_x) (B.as_seq h1' g));              
    assert (!wz == !(S.getWosize (S.read_word (B.as_seq h1' g) h_x)));             
    assert (stack_props h1' g st st_len);           
    darken_wrapper_impl g st st_len h_x wz;
    let h2 = ST.get() in
    assert  ((B.as_seq h2 g)  ==
                   snd (S.darken_wrapper (B.as_seq h1' g) 
                                          (stack_slice h1' st (stack_end h1' st_len))
                                          (h_x) 
                                          (wz) 
                                          )); 

   assert (stack_slice h2 st (stack_end h2 st_len) == 
                   fst (S.darken_wrapper (B.as_seq h1' g) 
                                      (stack_slice h1' st (stack_end h1' st_len))
                                      (h_x) 
                                      (wz) 
                                       ));
   S.mark5_body1_darken_wrapper_lemma (B.as_seq h0 g) 
                                      (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0)))
                                       x
                                      (B.as_seq h1' g)
                                      (stack_slice h1' st (stack_end h1' st_len))
                                      (wz);
   
    assert (fst (S.mark5_body1 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0)))) == 
                        fst (S.darken_wrapper (B.as_seq h1' g) 
                                               (stack_slice h1' st (stack_end h1' st_len)) 
                                                h_x
                                                wz 
                                               )); 
 
    
    assert (snd (S.mark5_body1 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0)))) == 
                        snd (S.darken_wrapper (B.as_seq h1' g) 
                                               (stack_slice h1' st (stack_end h1' st_len)) 
                                                h_x
                                                wz 
                                                )); 
   
   assert ((B.as_seq h2 g)  == snd (S.mark5_body1 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0)))));
   assert (stack_slice h2 st (stack_end h2 st_len) == fst (S.mark5_body1 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0)))));
   assert (B.live h2 g /\ B.live h2 st /\ B.live h2 st_len);
   assert (disjoint st st_len /\ disjoint g st /\ disjoint g st_len);
   assert (modified3 h1' h2 g st st_len);
   assert (modified3 h0 h2 g st st_len);
   assert (stack_end h2 st_len <= S.heap_size);
   assert (S.well_formed_heap2 (B.as_seq h2 g));
   assert (stack_props h2 g st st_len);
   ()
 )
 else
 (
    let h2 = ST.get() in
    assert (Usize.v (S.tag_of_object1 h_x (B.as_seq h1' g)) >= S.no_scan_tag);
    S.mark5_body1_darken_wrapper_lemma1 (B.as_seq h0 g) 
                                 (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0)))
                                  x
                                 (B.as_seq h1' g)
                                 (stack_slice h1' st (stack_end h1' st_len))
                                 (wz);
  
    assert ((B.as_seq h2 g)  ==
                 snd (S.mark5_body1 (B.as_seq h0 g) (stack_slice h0 st (stack_end h0 st_len))));
    assert (stack_slice h2 st (stack_end h2 st_len) == 
                 fst (S.mark5_body1 (B.as_seq h0 g) (stack_slice h0 st (stack_end h0 st_len))));
    ()
 )

#restart-solver 

let mark_heap7 g st st_len = 
  let open Usize in
 let h_init = ST.get() in

 (* Loop invariant should hold;
 (1) Before every iteration
 (2) During every iteration and 
 (3) At the end of every iteration
 Before the first iteration, g in the invariant is g itself.*) 

 let inv h =  (B.live h g /\ B.live h st /\ B.live h st_len) /\  

              (stack_end h st_len  <= S.heap_size)  /\

              (disjoint st st_len /\ disjoint g st /\ disjoint g st_len) /\
             
              (S.well_formed_heap2 (B.as_seq h g)) /\
              
              (S.objects2 0UL (B.as_seq h g) == S.objects2 0UL (B.as_seq h_init g)) /\
              
              (stack_props h g st st_len) /\

              (modified3 h_init h g st st_len) /\
             
              (S.mark7 (B.as_seq h g) (stack_slice h st (stack_end h st_len)) ==
              S.mark7 (B.as_seq h_init g) (stack_slice h_init st (stack_end h_init st_len))) in
              
 
 let guard (test: bool) h = inv h /\ 
   (test = true  ==> Usize.v (B.get h st_len 0) > 0) /\
   (test = false ==> Usize.v (B.get h st_len 0) = 0)  in
 
 let test ()
     : HA.Stack bool 
       (requires (fun h -> inv h)) 
       (ensures (fun _ ret h1 -> guard ret h1)) = (!*st_len) >^ 0UL in
 
 let body ()
     : HA.Stack unit 
       (requires (fun h -> guard true h)) 
       (ensures (fun _ _ h1 -> inv h1)) = 
   let h0 = ST.get() in   
   mark_heap_body1_impl g st st_len;
   let h1 = ST.get() in
   assert  (B.live h1 g /\ B.live h1 st /\ B.live h1 st_len /\
            disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\
            modified3 h0 h1 g st st_len /\
            stack_end h1 st_len <= S.heap_size /\
            S.well_formed_heap2 (B.as_seq h1 g) /\
            stack_props h1 g st st_len /\
                        
            ((B.as_seq h1 g)  == snd (S.mark5_body1 (B.as_seq h0 g) (stack_slice h0 st (stack_end h0 st_len)))) /\
                              
            (stack_slice h1 st (stack_end h1 st_len) == fst (S.mark5_body1 (B.as_seq h0 g) (stack_slice h0 st (stack_end h0 st_len)))));
                             
  S.mark7_mark_body_lemma (B.as_seq h0 g) (stack_slice h0 st (stack_end h0 st_len)); 
  ()
  in
  C.Loops.while #(inv) #(guard) test body;
  let h2 = ST.get() in
  S.mark7_mark_body_lemma1 (B.as_seq h2 g) (Seq.slice (B.as_seq h2 st) 0 (Usize.v (Seq.index (B.as_seq h2 st_len) 0)));
 ()
  
#restart-solver 

#restart-solver


let colorHeader3 g v_id c = 
 let h0 = ST.get() in
 let wz = wosize_of_block v_id g in

 let h1 = ST.get() in
 assert (h0 == h1);
 let tg = tag_of_block v_id g in

 let h2 = ST.get() in
 assert (h1 == h2);
 let h_val = S.makeHeader wz c tg in 

 let h3 = ST.get() in
 
 assert (wz == S.getWosize h_val);
 assert (c == S.getColor h_val);
 assert (tg == S.getTag h_val);
 //assert  (UInt32.v (UInt32.uint_to_t (UInt64.v v_id)) < B.length g / 8);
 assert  (store_pre g (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v v_id)))) 8 (fun s -> le_to_n s == UInt64.v h_val) h3);
 write_word_to_byte_buffer g v_id h_val;
 
 let h = ST.get() in
 assert (B.modifies (B.loc_buffer g) h3 h);
 assert (B.modifies (B.loc_buffer g) h2 h);
 assert (B.modifies (B.loc_buffer g) h0 h);
 assert ((B.as_seq h g) == S.colorHeader3 (v_id_f v_id) (B.as_seq h0 g) c);
 ()

#push-options "--z3rlimit 2000"


let sweep_body_helper_with_free_list1 g f_index free_list_ptr =
  let open Usize in
 let h0 = ST.get() in
 let f_index_val = !*f_index in
 let h_index = S.hd_address f_index_val in
 
 
 let c = color_of_block h_index g in
 assert (~(c == S.gray));
 
 assert (Seq.length (S.objects2 0UL (B.as_seq h0 g)) > 0);
 let wz = wosize_of_block h_index g in
 assert (Usize.v wz <> 0);
 if (c = S.white || c = S.blue) then 
 (
    let h1 = ST.get() in
    assert (h0 == h1);
    colorHeader3 g h_index S.blue;
    let h2 = ST.get() in
    assert (B.as_seq h2 g == S.colorHeader3 h_index (B.as_seq h1 g) S.blue);

    assert (B.modifies (B.loc_buffer g) h1 h2);
    
    
    assert (S.objects2 0UL (B.as_seq h1 g) == S.objects2 0UL (B.as_seq h2 g));
    
    let free_list_ptr_val = !*free_list_ptr in
    
    S.sum_of_multiple_of_mword_is_multiple_of_mword free_list_ptr_val S.mword;
    

    (*updating the first field of the free_list --> heap change*)
    write_word_to_byte_buffer g free_list_ptr_val f_index_val;
    
    let h3 = ST.get() in
    assert (B.modifies (B.loc_buffer g) h2 h3);
    (*Updating the free list pointer to point to h_index ---> no heap change*)
    free_list_ptr.(0ul) <- f_index_val;
    let h4 = ST.get() in
    assert (B.modifies (B.loc_buffer free_list_ptr) h3 h4);
    assert (B.as_seq h4 g == B.as_seq h3 g);
    assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_buffer free_list_ptr)) h1 h4);
    Seq.lemma_eq_intro (B.as_seq h4 g) (fst (S.sweep_body_with_free_list (B.as_seq h0 g) f_index_val (Seq.index (B.as_seq h0 free_list_ptr) 0)));
    Seq.lemma_eq_intro (B.as_seq h4 g) (fst (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 f_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0)));
   
    assert (Seq.index (B.as_seq h4 free_list_ptr) 0 == (snd (S.sweep_body_with_free_list (B.as_seq h0 g) f_index_val (Seq.index (B.as_seq h0 free_list_ptr) 0))));
    assert (Seq.index (B.as_seq h4 free_list_ptr) 0 == (snd (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 f_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0))));
    assert (B.as_seq h4 g == (fst (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 f_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0))));
    ()
   
 )
 else
 (
      assert (c == S.black);
      let h3 = ST.get() in
      assert (h0 == h3);
      colorHeader3 g h_index S.white;
      let h4 = ST.get() in
      assert (B.as_seq h4 g == S.colorHeader3 h_index (B.as_seq h3 g) S.white);

      assert (B.modifies (B.loc_buffer g) h3 h4);
      
      
      Seq.lemma_eq_intro (B.as_seq h4 g) (fst (S.sweep_body_with_free_list (B.as_seq h0 g) f_index_val (Seq.index (B.as_seq h0 free_list_ptr) 0)));
      Seq.lemma_eq_intro (B.as_seq h4 g) (fst (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 f_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0)));
      assert (Seq.index (B.as_seq h4 free_list_ptr) 0 == (snd (S.sweep_body_with_free_list (B.as_seq h0 g) f_index_val (Seq.index (B.as_seq h0 free_list_ptr) 0))));
      assert (Seq.index (B.as_seq h4 free_list_ptr) 0 == (snd (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 f_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0))));
      assert (B.as_seq h4 g == (fst (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 f_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0))));
      ()
 )

let sweep1_with_free_list1  g f_index free_list_ptr =
  let open Usize in
let h_init = ST.get() in
let inv h =  B.live h g /\ B.live h f_index /\ B.live h free_list_ptr /\

              disjoint g f_index /\
              disjoint g free_list_ptr /\
              disjoint f_index free_list_ptr /\
             
             
             B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer free_list_ptr) (B.loc_buffer f_index))) h_init h /\
             (Usize.v (Seq.index (B.as_seq h f_index) 0) % Usize.v S.mword == 0)  /\
             (Seq.length (S.objects2 0UL (B.as_seq h g)) > 0) /\
             B.length f_index == 1 /\
             B.length free_list_ptr == 1 /\ 
             
             S.noGreyObjects (B.as_seq h g) /\
             (Usize.v (index_zero_of_single_length_seq h f_index) >=  Usize.v S.mword) /\
             (S.objects2 0UL ((B.as_seq h_init g)) == S.objects2 0UL (B.as_seq h g)) /\
             
             Usize.v (index_zero_of_single_length_seq h free_list_ptr) >= Usize.v S.mword /\ 
             Usize.v (index_zero_of_single_length_seq h free_list_ptr) < S.heap_size /\
             Usize.v (index_zero_of_single_length_seq h free_list_ptr) % Usize.v S.mword == 0  /\
             (S.color_of_object1 (v_id_f (S.hd_address (index_zero_of_single_length_seq h free_list_ptr))) (B.as_seq h g) == S.blue) /\
             (Usize.v  (Seq.index (B.as_seq h f_index) 0) < S.heap_size ==>
                   (Seq.mem (v_id_f (S.hd_address (Seq.index (B.as_seq h f_index) 0))) (S.objects2 0UL (B.as_seq h g)))) /\
             
             (Usize.v  (Seq.index (B.as_seq h f_index) 0) >= S.heap_size ==> 
                       (B.as_seq h g == 
                          (fst (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)))) /\
                        (Seq.index (B.as_seq h free_list_ptr) 0 == 
                          (snd (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)))))
              
              
              /\ 
              (forall x y. Seq.mem x (S.objects2 0UL (B.as_seq h g)) /\ Seq.mem y (S.objects2 0UL (B.as_seq h g)) ==>
                                   Usize.v (S.getWosize (S.read_word (B.as_seq h g) x)) + 
                                   Usize.v (S.getWosize (S.read_word (B.as_seq h g) y)) < S.heap_size) /\
             
             (Seq.mem (v_id_f (S.hd_address (index_zero_of_single_length_seq h free_list_ptr))) (S.objects2 0UL (B.as_seq h g))) /\
             (Usize.v  (Seq.index (B.as_seq h f_index) 0) < S.heap_size ==>
                  (Seq.length (S.objects2 (S.hd_address  (index_zero_of_single_length_seq h f_index)) (B.as_seq h g)) > 0) /\
                   
                   (fst (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) == 
                      fst (S.sweep_with_free_list3 (B.as_seq h g) (Seq.index (B.as_seq h f_index) 0) (Seq.index (B.as_seq h free_list_ptr) 0))) /\
                    (snd (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) == 
                      snd (S.sweep_with_free_list3 (B.as_seq h g) (Seq.index (B.as_seq h f_index) 0) (Seq.index (B.as_seq h free_list_ptr) 0))) )            
                           in
let guard (test: bool) h = inv h /\ 
   (test = true  ==> Usize.v (B.get h f_index 0) < S.heap_size) /\
   (test = false ==> Usize.v (B.get h f_index 0) >= S.heap_size)  in             
let test ()
     : HA.Stack bool 
       (requires (fun h -> inv h)) 
       (ensures (fun _ ret h1 -> guard ret h1)) = (!*f_index) <^ UInt64.uint_to_t (S.heap_size) in
let body ()
     : HA.Stack unit 
       (requires (fun h -> guard true h)) 
       (ensures (fun _ _ h1 -> inv h1)) = 
 let h0 = ST.get() in
 let f_index_val = !*f_index in
 assert (Usize.v f_index_val < S.heap_size);
 let h1 = ST.get() in
 assert (h1 == h0);
 let h_index_val = S.hd_address f_index_val in
 let wz = wosize_of_block h_index_val g in
 let h_index_new =  Usize.add h_index_val (Usize.mul (Usize.add wz 1UL) S.mword) in
 let f_index_new = Usize.add h_index_new S.mword in
 let h2 = ST.get() in
 assert (h1 == h2);
 assert (guard true h0);
 assert (Usize.v (B.get h0 f_index 0) < S.heap_size);
 assert (Usize.v (B.get h2 f_index 0) < S.heap_size);
 
 assert (Usize.v (index_zero_of_single_length_seq h0 f_index) < S.heap_size);
 
 let h3 = ST.get() in
 assert (h3 == h2);
 sweep_body_helper_with_free_list1 g f_index free_list_ptr; 
 let h4 = ST.get() in
 assert (B.as_seq h4 g == (fst (S.sweep_body_with_free_list (B.as_seq h3 g) 
                                 (Seq.index (B.as_seq h3 f_index) 0) (Seq.index (B.as_seq h3 free_list_ptr) 0))));
 assert(Seq.index (B.as_seq h4 free_list_ptr) 0 == 
                                 (snd (S.sweep_body_with_free_list (B.as_seq h3 g) (Seq.index (B.as_seq h3 f_index) 0) (Seq.index (B.as_seq h3 free_list_ptr) 0))));
 S.sweep_body_with_free_list_lemma5 (B.as_seq h3 g) (Seq.index (B.as_seq h3 f_index) 0) (Seq.index (B.as_seq h3 free_list_ptr) 0);

 assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_buffer free_list_ptr)) h3 h4);
 f_index.(0ul) <- f_index_new;
 
 let h5 = ST.get() in
 assert (B.modifies (B.loc_buffer f_index) h4 h5);
 assert (B.as_seq h4 g == B.as_seq h5 g);
 assert(Seq.index (B.as_seq h4 free_list_ptr) 0 == Seq.index (B.as_seq h5 free_list_ptr) 0);
 
 assert (Usize.v (Seq.index (B.as_seq h5 f_index) 0) == Usize.v f_index_new);
 
 
 S.wosize_plus_times_mword_multiple_of_mword1 wz;
 S.sum_of_multiple_of_mword_is_multiple_of_mword h_index_val (Usize.mul (Usize.add wz 1UL) S.mword);
 assert (Usize.v h_index_new % Usize.v S.mword == 0); 
 S.sum_of_multiple_of_mword_is_multiple_of_mword h_index_new S.mword;
 assert (Usize.v f_index_new % Usize.v S.mword == 0);
 
 if (Usize.v f_index_new >= S.heap_size) then
  (
             assert (B.live h5 g /\ B.live h5 f_index /\ B.live h5 free_list_ptr /\

             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer f_index) /\
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer free_list_ptr) /\
             B.loc_disjoint (B.loc_buffer f_index) (B.loc_buffer free_list_ptr));
             S.objects2_cons_lemma2 h_index_val (B.as_seq h5 g);
             S.objects2_sweep_lemma3 h_index_val (B.as_seq h0 g);
             assert (Usize.v f_index_new >= S.heap_size ==> 
                      ~(Seq.mem h_index_new (S.objects2 h_index_val (B.as_seq h5 g))));

             S.objects2_sweep_lemma4 h_index_val (B.as_seq h0 g);
             assert (~(Seq.mem h_index_new (S.objects2 h_index_val (B.as_seq h5 g))) /\ 
                      (Seq.length (S.objects2 (S.hd_address f_index_val) (B.as_seq h5 g)) > 0) ==> 
                              Seq.length (S.objects2 h_index_val (B.as_seq h5 g)) == 1);
             S.objects2_property_lemma (B.as_seq h5 g) h_index_val;
             
             assert (inv h5);
             ()
   )
    else
    (
      assert (S.is_hp_addr h_index_new);
      S.objects2_mem_lemma1_app h_index_val (B.as_seq h3 g);
     
      S.objects2_length_lemma3 (B.as_seq h5 g) h_index_val h_index_new; 
      
      assert ((Seq.index (B.as_seq h5 f_index) 0) == f_index_new);
      assert (Usize.v f_index_new < S.heap_size);
      assert (Usize.v (Seq.index (B.as_seq h5 f_index) 0) < S.heap_size);
      assert (Usize.add h_index_val (Usize.mul (Usize.add wz 1UL) S.mword) == h_index_new);
      
      (*This is a true statement. A lemma can assert it. For time being, putting an assume*)
      assert ((Usize.v f_index_val >= Usize.v S.mword /\ 
              Usize.v f_index_val < S.heap_size /\
              Usize.v f_index_val % Usize.v S.mword == 0 /\
              (Seq.mem (v_id_f (S.hd_address f_index_val)) (S.objects2 0UL (B.as_seq h0 g))) /\
              (let h_index_val = S.hd_address f_index_val in
              let wz = S.wosize_of_object1 h_index_val (B.as_seq h0 g) in
              let h_index_new =  Usize.add h_index_val (Usize.mul (Usize.add wz 1UL) S.mword) in
              let f_index_new = Usize.add h_index_new S.mword in
              Usize.v f_index_new < S.heap_size)));
      assert (Usize.v f_index_new % Usize.v S.mword == 0);
      assert (Usize.v f_index_new < S.heap_size);
      assert (S.is_hp_addr f_index_new);
      //assert (Usize.v f_index_val < S.heap_size);
      //assume (S.is_hp_addr f_index_val);
      f_index_lemma (B.as_seq h0 g) f_index_val;
      //assume (UInt.fits (Usize.v f_index_new - Usize.v S.mword) Usize.n);
      assert (S.hd_address f_index_new == h_index_new);
      assert (S.hd_address (Seq.index (B.as_seq h5 f_index) 0) == h_index_new);
      assert ((Usize.v  
                  (Seq.index (B.as_seq h5 f_index) 0) < S.heap_size ==>
                     (Seq.mem (v_id_f (S.hd_address (Seq.index (B.as_seq h5 f_index) 0))) 
                              (S.objects2 0UL (B.as_seq h5 g)))));
      assert ((Usize.v  (Seq.index (B.as_seq h5 f_index) 0) < S.heap_size ==>
                  (Seq.length 
                     (S.objects2 (S.hd_address  (index_zero_of_single_length_seq h5 f_index)) 
                                 (B.as_seq h5 g)) > 0) /\
              
               (fst (S.sweep_with_free_list3 (B.as_seq h_init g) 
                     (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) == 
               fst (S.sweep_with_free_list3 (B.as_seq h5 g) 
                     (Seq.index (B.as_seq h5 f_index) 0) (Seq.index (B.as_seq h5 free_list_ptr) 0))) /\
                    
              (snd (S.sweep_with_free_list3 (B.as_seq h_init g) 
                     (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) == 
              snd (S.sweep_with_free_list3 (B.as_seq h5 g) 
                     (Seq.index (B.as_seq h5 f_index) 0) (Seq.index (B.as_seq h5 free_list_ptr) 0)))));
      assert (Usize.v  (Seq.index (B.as_seq h5 f_index) 0) < S.heap_size);
      assert (B.live h5 g /\ B.live h5 f_index /\ B.live h5 free_list_ptr /\

              disjoint g f_index /\
              disjoint g free_list_ptr /\
              disjoint f_index free_list_ptr /\
             
             
             B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer free_list_ptr) (B.loc_buffer f_index))) h_init h5 /\
             (Usize.v (Seq.index (B.as_seq h5 f_index) 0) % Usize.v S.mword == 0)  /\
             (Seq.length (S.objects2 0UL (B.as_seq h5 g)) > 0) /\
             B.length f_index == 1 /\
             B.length free_list_ptr == 1 /\ 
             
             S.noGreyObjects (B.as_seq h5 g) /\
             (Usize.v (index_zero_of_single_length_seq h5 f_index) >=  Usize.v S.mword) /\
             (S.objects2 0UL ((B.as_seq h_init g)) == S.objects2 0UL (B.as_seq h5 g)) /\
             
             Usize.v (index_zero_of_single_length_seq h5 free_list_ptr) >= Usize.v S.mword /\ 
             Usize.v (index_zero_of_single_length_seq h5 free_list_ptr) < S.heap_size /\
             Usize.v (index_zero_of_single_length_seq h5 free_list_ptr) % Usize.v S.mword == 0  /\
             (S.color_of_object1 (v_id_f (S.hd_address (index_zero_of_single_length_seq h5 free_list_ptr))) (B.as_seq h5 g) == S.blue));
      assert ((Usize.v  (Seq.index (B.as_seq h5 f_index) 0) < S.heap_size ==>
                   (Seq.mem (v_id_f (S.hd_address (Seq.index (B.as_seq h5 f_index) 0))) (S.objects2 0UL (B.as_seq h5 g)))) /\
             
             (Usize.v  (Seq.index (B.as_seq h5 f_index) 0) >= S.heap_size ==> 
                       (B.as_seq h5 g == 
                          (fst (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) 
                            (Seq.index (B.as_seq h_init free_list_ptr) 0)))) /\
                        (Seq.index (B.as_seq h5 free_list_ptr) 0 == 
                          (snd (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) 
                          (Seq.index (B.as_seq h_init free_list_ptr) 0)))))
              
              
              /\ 
              (forall x y. Seq.mem x (S.objects2 0UL (B.as_seq h5 g)) /\ Seq.mem y (S.objects2 0UL (B.as_seq h5 g)) ==>
                                   Usize.v (S.getWosize (S.read_word (B.as_seq h5 g) x)) + 
                                   Usize.v (S.getWosize (S.read_word (B.as_seq h5 g) y)) < S.heap_size) );
      
      assert (B.live h5 g /\ B.live h5 f_index /\ B.live h5 free_list_ptr /\

              disjoint g f_index /\
              disjoint g free_list_ptr /\
              disjoint f_index free_list_ptr /\
             
             
             B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer free_list_ptr) (B.loc_buffer f_index))) h_init h5 /\
             (Usize.v (Seq.index (B.as_seq h5 f_index) 0) % Usize.v S.mword == 0)  /\
             (Seq.length (S.objects2 0UL (B.as_seq h5 g)) > 0) /\
             B.length f_index == 1 /\
             B.length free_list_ptr == 1 /\ 
             
             S.noGreyObjects (B.as_seq h5 g) /\
             (Usize.v (index_zero_of_single_length_seq h5 f_index) >=  Usize.v S.mword) /\
             (S.objects2 0UL ((B.as_seq h_init g)) == S.objects2 0UL (B.as_seq h5 g)) /\
             
             Usize.v (index_zero_of_single_length_seq h5 free_list_ptr) >= Usize.v S.mword /\ 
             Usize.v (index_zero_of_single_length_seq h5 free_list_ptr) < S.heap_size /\
             Usize.v (index_zero_of_single_length_seq h5 free_list_ptr) % Usize.v S.mword == 0  /\
             (S.color_of_object1 (v_id_f (S.hd_address (index_zero_of_single_length_seq h5 free_list_ptr))) (B.as_seq h5 g) == S.blue) /\
             (Usize.v  (Seq.index (B.as_seq h5 f_index) 0) < S.heap_size ==>
                   (Seq.mem (v_id_f (S.hd_address (Seq.index (B.as_seq h5 f_index) 0))) (S.objects2 0UL (B.as_seq h5 g)))) /\
             
             (Usize.v  (Seq.index (B.as_seq h5 f_index) 0) >= S.heap_size ==> 
                       (B.as_seq h5 g == 
                          (fst (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)))) /\
                        (Seq.index (B.as_seq h5 free_list_ptr) 0 == 
                          (snd (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)))))
              
              
              /\ 
              (forall x y. Seq.mem x (S.objects2 0UL (B.as_seq h5 g)) /\ Seq.mem y (S.objects2 0UL (B.as_seq h5 g)) ==>
                                   Usize.v (S.getWosize (S.read_word (B.as_seq h5 g) x)) + 
                                   Usize.v (S.getWosize (S.read_word (B.as_seq h5 g) y)) < S.heap_size) /\
             
            
              (Seq.mem (v_id_f (S.hd_address (index_zero_of_single_length_seq h5 free_list_ptr))) (S.objects2 0UL (B.as_seq h5 g))) /\
             (Usize.v  (Seq.index (B.as_seq h5 f_index) 0) < S.heap_size ==>
                  (Seq.length (S.objects2 (S.hd_address  (index_zero_of_single_length_seq h5 f_index)) (B.as_seq h5 g)) > 0) /\
                   
                   (fst (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) == 
                      fst (S.sweep_with_free_list3 (B.as_seq h5 g) (Seq.index (B.as_seq h5 f_index) 0) (Seq.index (B.as_seq h5 free_list_ptr) 0))) /\
                    (snd (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) == 
                      snd (S.sweep_with_free_list3 (B.as_seq h5 g) (Seq.index (B.as_seq h5 f_index) 0) (Seq.index (B.as_seq h5 free_list_ptr) 0))) ) );
      assert (inv h5);
      ()
    )
  in
  C.Loops.while #(inv) #(guard) test body;    
  let h_after = ST.get() in
  
  assert (fst (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) ==
           B.as_seq h_after g);
  assert (snd (S.sweep_with_free_list3 (B.as_seq h_init g) (Seq.index (B.as_seq h_init f_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) ==
           Seq.index (B.as_seq h_after free_list_ptr) 0);
  assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer free_list_ptr) (B.loc_buffer f_index))) h_init h_after);
  ()


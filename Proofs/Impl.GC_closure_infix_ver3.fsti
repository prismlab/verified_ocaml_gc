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
/// ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
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

(*heap memory is modelled as a byte addressable array*)

let (!) (x: Usize.t) : int = Usize.v x

type heap = g: B.buffer UInt8.t{B.length g == S.heap_size}

type addr = elem:Usize.t{!elem >= 0 /\ !elem < S.heap_size /\
                         ! elem % !S.mword == 0}
let v_id_f (v_id: addr)
           : GTot S.hp_addr = v_id

type stack = st:B.buffer Usize.t{B.length st == S.heap_size}

type usize_buffer = B.buffer Usize.t

let disjoint (#a:eqtype)
             (#b:eqtype)
             (x:B.buffer a)
             (y:B.buffer b) =

 B.loc_disjoint (B.loc_buffer x) (B.loc_buffer y)

let portion (#a:eqtype)
            (s:Seq.seq a)
            (i:nat)
            (j:nat{i <= j /\ j <= Seq.length s}) =
 Seq.slice s i j


let buf_to_seq (#a:eqtype)
               (h:H.mem)
               (s:B.buffer a) =
 B.as_seq h s

let modified2 (#a:eqtype)
             (#b:eqtype)
             (m0:H.mem)
             (m1:H.mem)
             (x:B.buffer a)
             (y: B.buffer b) =
  B.modifies (B.loc_union (B.loc_buffer x) (B.loc_buffer y)) m0 m1

let modified3 (#a:eqtype)
             (#b:eqtype)
             (m0:H.mem)
             (m1:H.mem)
             (x:B.buffer a)
             (y: B.buffer b)
             (z: B.buffer b) =
  B.modifies (B.loc_union (B.loc_buffer x) (B.loc_union (B.loc_buffer y) (B.loc_buffer z))) m0 m1


let stack_props (m:H.mem)
                (g:heap{S.well_formed_heap2 (B.as_seq m g)})
                (st: stack)
                (st_len: usize_buffer{B.length st_len == 1 /\ !(Seq.index (B.as_seq m st_len) 0) <= S.heap_size})
                =
 let stack_top =  !(Seq.index (B.as_seq m st_len) 0) in
 let stack_slice = Seq.slice (B.as_seq m st) 0 stack_top in
 (G.is_vertex_set stack_slice) /\
 (forall x. Seq.mem x stack_slice ==> !x >= !S.mword /\ !x < S.heap_size) /\
 (forall x. Seq.mem x stack_slice ==>  !x % !S.mword == 0 ) /\
 (forall x. Seq.mem x stack_slice ==> Usize.v (S.tag_of_object1 (S.hd_address x) (B.as_seq m g)) <> S.infix_tag) /\
 (forall x. Seq.mem x stack_slice ==> S.is_valid_header1 (S.hd_address x) (B.as_seq m g)) /\
 (forall x. Seq.mem (S.hd_address x) (S.objects2 0UL (B.as_seq m g)) /\ S.isGrayObject1 (S.hd_address x) (B.as_seq m g) <==> Seq.mem x stack_slice)

type st_top = st_len:usize_buffer{B.length st_len == 1}

let stack_slice (m:H.mem)
                (st: stack)
                (st_len: nat{st_len <= B.length st}) =
   Seq.slice (B.as_seq m st) 0 st_len


(*For reading the color of an object. S.getcolor is the functional equivalent*)
val getColor : (h:Usize.t{Usize.v h < S.heap_size /\
                          Usize.v h % Usize.v S.mword == 0}) ->
          HA.Stack (S.color)
          (fun m -> True)
          (fun h0 x h1 -> x == S.getColor (v_id_f h) /\ h0 == h1 /\ B.modifies (B.loc_none) h0 h1)

val makeHeader  :(wz:S.wosize) ->
                 (c:S.color)->
                 (tg:S.tag)->
       HA.Stack Usize.t
       (fun m -> True)
       (fun h0 x h1 -> x == S.makeHeader wz c tg /\
                            (B.modifies (B.loc_none) h0 h1))


inline_for_extraction
val read_word_from_byte_buffer : (g: heap) ->
                                  (byte_index: S.hp_addr)->
            HA.Stack (UInt64.t)
            (fun m -> B.live m g)
            (fun m0 x m1 ->  m0 == m1  /\ (B.live m1 g) /\
                          (x == S.read_word (B.as_seq m1 g) byte_index) /\
                          (B.modifies (B.loc_none) m0 m1))
#restart-solver

inline_for_extraction
val write_word_to_byte_buffer : (g: heap) ->
                                (byte_index: S.hp_addr)->
                                (v:UInt64.t)->
   HA.Stack unit
     (requires fun h -> B.live h g  /\
                     store_pre g (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)))) 8 (fun s -> le_to_n s == UInt64.v v) h)

     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer g) h0 h1 /\
                          S.write_word (B.as_seq h0 g) byte_index v == B.as_seq h1 g)

let isPointer (v_id: Usize.t)
              (g:heap)
           : HA.Stack (bool)
             (fun m -> B.live m g /\
              Usize.v v_id >= 0 /\ Usize.v v_id < S.heap_size /\
              (Usize.v v_id % Usize.v S.mword == 0))

             (fun h0 b h1 -> h0 == h1 /\ b == S.isPointer (v_id_f v_id) (B.as_seq h1 g) /\
                          (B.modifies (B.loc_none) h0 h1) /\ h0 == h1) =
 Usize.logand (read_word_from_byte_buffer g v_id) 1UL = 0UL

let stack_end (m:H.mem)
              (st_len:st_top) =

 !(Seq.index (B.as_seq m st_len) 0)

#push-options "--split_queries always"

#restart-solver

#restart-solver

val wosize_of_block : (v_id: addr)->
                      (g:heap)->
           HA.Stack (S.wosize)
           (fun m -> B.live m g (*/\ S.well_formed_heap2 (B.as_seq m g) /\
                    S.is_valid_header1 (v_id_f v_id) (B.as_seq m g)*))

           (fun h0 x h1 -> h0 == h1 /\
                          x == S.wosize_of_object1 (v_id_f v_id) (B.as_seq h1 g) /\
                          h0 == h1 /\
                          (B.modifies (B.loc_none) h0 h1))



val color_of_block  : (v_id: addr)->
                      (g:heap)->
           HA.Stack (S.color)
           (fun m -> B.live m g (*/\ S.well_formed_heap2 (B.as_seq m g) /\
                    S.is_valid_header1 (v_id_f v_id) (B.as_seq m g)*))

           (fun h0 x h1 -> h0 == h1 /\ x == S.color_of_object1 (v_id_f v_id) (B.as_seq h1 g) /\
             h0 == h1 /\
            (B.modifies (B.loc_none) h0 h1))


val tag_of_block : (v_id: addr)->
                   (g:heap)->
           HA.Stack (S.tag)
           (fun m -> B.live m g (*/\ S.well_formed_heap2 (B.as_seq m g) /\
                    S.is_valid_header1 (v_id_f v_id) (B.as_seq m g)*))

           (fun h0 x h1 -> h0 == h1 /\ x == S.tag_of_object1 (v_id_f v_id) (B.as_seq h1 g) /\
                          (B.modifies (B.loc_none) h0 h1) /\ h0 == h1)

#restart-solver

val colorHeader1 : (g:heap) ->
                   (v_id:addr)->
                   (c:S.color) ->
            HA.Stack (unit)
            (fun m -> B.live m g /\
                   S.well_formed_heap2 (B.as_seq m g) /\
                   S.is_valid_header1 (v_id_f v_id) (B.as_seq m g))

            (fun m0 () m1 -> B.live m1 g /\ B.modifies (B.loc_buffer g) m0 m1 /\
                          ((B.as_seq m1 g) == S.colorHeader1 (v_id_f v_id) (B.as_seq m0 g) c))

#restart-solver

#restart-solver


#push-options " --z3rlimit 100"

#restart-solver


val push_to_stack : (g:heap)->
                    (st: stack)->
                    (st_len: st_top)->
                    (elem: S.hp_addr)->
               HA.Stack unit
               (fun m -> B.live m g /\ B.live m st /\ B.live m st_len /\

                      disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\

                      !(Seq.index (B.as_seq m st_len) 0) < S.heap_size /\

                      (
                         let stack_top =  !(Seq.index (B.as_seq m st_len) 0) in
                         let stack_slice' = Seq.slice (B.as_seq m st) 0 stack_top in

                         S.well_formed_heap2 (B.as_seq m g) /\
                         stack_props m g st st_len /\
                         (S.is_valid_header1 (v_id_f elem) (B.as_seq m g)) /\
                         (~(Seq.mem (v_id_f (S.f_address elem)) stack_slice')) /\
                         (Usize.v (S.tag_of_object1 elem (B.as_seq m g)) <> S.infix_tag)
                      )
                )
               (fun m0 _ m1 ->
                            B.live m1 st /\ B.live m1 g /\ B.live m1 st_len /\ B.length st_len == 1 /\
                            !(Seq.index (B.as_seq m1 st_len) 0) <= S.heap_size /\
                            disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\
                            modified3 m0 m1 g st st_len /\

                            S.well_formed_heap2 (B.as_seq m1 g) /\
                            S.is_valid_header1 (v_id_f elem) (B.as_seq m1 g) /\

                            (
                              let st_top_m0 =  !(Seq.index (B.as_seq m0 st_len) 0) in
                              let st_top_m1 =  !(Seq.index (B.as_seq m1 st_len) 0) in
                              let func_stack, func_heap = S.push_to_stack2 (B.as_seq m0 g) (stack_slice m0 st st_top_m0) elem in
                              B.as_seq m1 g == func_heap /\
                              stack_slice m1 st st_top_m1 == func_stack

                           )
                )


val read_succ_impl : (g:heap)->
                     (h_index: S.hp_addr)->
                     (i:Usize.t)->
           HA.Stack Usize.t
            (fun m -> B.live m g /\
                   S.well_formed_heap2 (B.as_seq m g) /\
                   (S.is_valid_header1 (v_id_f h_index) (B.as_seq m g)) /\
                   (Usize.v i < Usize.v (S.getWosize (S.read_word (B.as_seq m g) h_index)) + 1 /\ Usize.v i >= 1)
            )
            (fun m0 r m1 -> B.live m1 g /\
                         B.modifies (B.loc_none) m0 m1 /\
                         (r == S.read_succ (B.as_seq m0 g) h_index i)
            )

(*let parent_closure_of_infix_object (g:heap{well_formed_heap2 g})
                                   (h_index:hp_addr{is_valid_header1 h_index g})
                                   (i:Usize.t{(Usize.v i < Usize.v (getWosize (read_word g h_index)) + 1 /\ Usize.v i >= 1) /\
                                               isPointer (succ_index_fn g h_index i) g /\
                                               (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag)
                                             })
                  : Tot (parent_hdr:hp_addr{is_valid_header1 parent_hdr g /\
                                            (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n) /\
                                            (Usize.v parent_hdr + Usize.v mword < heap_size) /\
                                            (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                                            (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag)})*)


val parent_closure_of_infix_object_impl : (g:heap)->
                                          (h_index: S.hp_addr)->
                                          (i:Usize.t)->
            HA.Stack Usize.t
            (fun m -> B.live m g /\
                   S.well_formed_heap2 (B.as_seq m g) /\
                   (S.is_valid_header1 (v_id_f h_index) (B.as_seq m g)) /\
                   (Usize.v i < Usize.v (S.getWosize (S.read_word (B.as_seq m g) h_index)) + 1 /\ Usize.v i >= 1) /\
                   (S.isPointer (S.succ_index_fn (B.as_seq m g) h_index i) (B.as_seq m g)) /\
                   (Usize.v (S.tag_of_object1 (S.hd_address (S.read_succ (B.as_seq m g) h_index i)) (B.as_seq m g)) == S.infix_tag)
            )
            (fun m0 r m1 -> B.live m1 g /\
                         B.modifies (B.loc_none) m0 m1 /\
                         (S.is_hp_addr r) /\
                         (r == S.parent_closure_of_infix_object (B.as_seq m0 g) h_index i)
            )

(*let darken_helper(g:heap{well_formed_heap2 g})
                 (st: seq Usize.t{stack_props_func g st})
                 (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                  (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)})
           : Tot (st_hp:stack_heap_pair{well_formed_heap2 (snd st_hp) /\

                                         stack_props_func (snd st_hp) (fst st_hp) /\

                                         (forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) == getWosize (read_word (snd st_hp) x)) /\

                                         (objects2 0UL g ==  objects2 0UL (snd st_hp)) /\

                                         (Seq.length g == Seq.length (snd st_hp)) /\

                                         (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\

                                         (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))})*)

val darken_helper_impl: (g:heap)->
                        (st: stack)->
                        (st_len: st_top)->
                        (hdr_id: S.hp_addr)->
               HA.Stack unit
               (fun m -> B.live m g /\ B.live m st /\ B.live m st_len /\

                      disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\

                      !(Seq.index (B.as_seq m st_len) 0) <= S.heap_size /\

                      (
                         let stack_top =  !(Seq.index (B.as_seq m st_len) 0) in
                         let stack_slice' = Seq.slice (B.as_seq m st) 0 stack_top in

                         S.well_formed_heap2 (B.as_seq m g) /\
                         stack_props m g st st_len /\
                         (S.is_valid_header1 (v_id_f hdr_id) (B.as_seq m g)) /\
                         (Usize.v (S.tag_of_object1 hdr_id (B.as_seq m g)) <> S.infix_tag)
                      )
                )
               (fun m0 _ m1 ->  B.live m1 st /\ B.live m1 g /\ B.live m1 st_len /\ B.length st_len == 1 /\
                            !(Seq.index (B.as_seq m1 st_len) 0) <= S.heap_size /\
                            disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\
                            modified3 m0 m1 g st st_len /\

                            S.well_formed_heap2 (B.as_seq m1 g) /\
                            (
                              let st_top_m0 =  !(Seq.index (B.as_seq m0 st_len) 0) in
                              let st_top_m1 =  !(Seq.index (B.as_seq m1 st_len) 0) in
                              let func_stack, func_heap = S.darken_helper (B.as_seq m0 g) (stack_slice m0 st st_top_m0) hdr_id in
                              B.as_seq m1 g == func_heap /\
                              stack_slice m1 st st_top_m1 == func_stack)
                )

val darken_body : (g:heap)->
                  (st: stack)->
                  (st_len: st_top)->
                  (h_index:S.hp_addr)->
                  (wz:S.wosize)->
                  (i:Usize.t)->
             HA.Stack unit
             (fun m ->  B.live m g /\ B.live m st /\ B.live m st_len /\
                       disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\

                       stack_end m st_len <= S.heap_size /\
                       !i >= 1 /\
                       !i < !wz + 1 /\
                       S.well_formed_heap2 (B.as_seq m g) /\
                       S.is_valid_header1 (v_id_f h_index) (B.as_seq m g) /\

                       (!wz == !(S.getWosize (S.read_word (B.as_seq m g) h_index))) /\

                       stack_props m g st st_len)

             (fun m0 _ m1 -> B.live m1 g /\ B.live m1 st /\ B.live m1 st_len /\
                             disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\
                             (modified3 m0 m1 g st st_len) /\

                             stack_end m1 st_len <= S.heap_size /\
                             ((B.as_seq m1 g) ==  (snd (S.fieldPush_spec_body1 (B.as_seq m0 g)
                                                      (stack_slice m0 st (stack_end m0 st_len))
                                                      (h_index)
                                                      (wz)
                                                      (i)))) /\
                             (stack_slice m1 st (stack_end m1 st_len) ==
                                    (fst (S.fieldPush_spec_body1 (B.as_seq m0 g)
                                             (stack_slice m0 st (stack_end m0 st_len))
                                             (h_index)
                                             (wz)
                                             (i)))))

#restart-solver

val darken : (g:heap)->
             (st: stack)->
             (st_len: st_top)->
             (h_index:S.hp_addr)->
             (wz:S.wosize)->
         HA.Stack unit
          (fun m -> (*concrete memory properties*)
                 B.live m g /\ B.live m st /\ B.live m st_len /\


                 (*Since st_top is used for slice calculation of st, st_top contents should be less than or equal to st length*)
                  stack_end m st_len <= S.heap_size /\
                  disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\




                 (*algebraic properties to connect with Spec*)
                 S.well_formed_heap2 (B.as_seq m g) /\
                 S.is_valid_header1 (v_id_f h_index) (B.as_seq m g) /\

                 (!wz == !(S.getWosize (S.read_word (B.as_seq m g) h_index))) /\

                 stack_props m g st st_len


            )
          (fun m0 () m1 -> B.live m1 g /\ B.live m1 st /\ B.live m1 st_len /\


                 (*Since st_top is used for slice calculation of st, st_top contents should be less than or equal to st length*)
                  stack_end m1 st_len <= S.heap_size /\
                  disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\

                 (*algebraic properties to connect with Spec*)
                 S.well_formed_heap2 (B.as_seq m1 g) /\
                 S.is_valid_header1 (v_id_f h_index) (B.as_seq m1 g) /\
                 stack_props m1 g st st_len /\

                 (modified3 m0 m1 g st st_len) /\
                 ((B.as_seq m1 g)  ==
                   snd (S.fieldPush_spec1 (B.as_seq m0 g)
                                          (stack_slice m0 st (stack_end m0 st_len))
                                          (h_index)
                                          (wz)
                                          1UL)) /\
                 (stack_slice m1 st (stack_end m1 st_len) ==
                   fst (S.fieldPush_spec1 (B.as_seq m0 g)
                                      (stack_slice m0 st (stack_end m0 st_len))
                                      (h_index)
                                      (wz)
                                      1UL)))







#restart-solver

#restart-solver

#restart-solver

val darken1 : (g:heap)->
              (st: stack)->
              (st_len: st_top)->
              (h_index:S.hp_addr)->
              (wz:S.wosize)->
              (j:Usize.t) ->
         HA.Stack unit
          (fun m -> (*concrete memory properties*)
                 B.live m g /\ B.live m st /\ B.live m st_len /\


                 (*Since st_top is used for slice calculation of st, st_top contents should be less than or equal to st length*)
                  stack_end m st_len <= S.heap_size /\
                  disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\



                 (Usize.v j >= 1 /\ Usize.v j <= Usize.v wz) /\
                 (*algebraic properties to connect with Spec*)
                 S.well_formed_heap2 (B.as_seq m g) /\
                 S.is_valid_header1 (v_id_f h_index) (B.as_seq m g) /\

                 (!wz == !(S.getWosize (S.read_word (B.as_seq m g) h_index))) /\

                 stack_props m g st st_len


            )
          (fun m0 () m1 -> B.live m1 g /\ B.live m1 st /\ B.live m1 st_len /\


                 (*Since st_top is used for slice calculation of st, st_top contents should be less than or equal to st length*)
                  stack_end m1 st_len <= S.heap_size /\
                  disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\

                 (*algebraic properties to connect with Spec*)
                 S.well_formed_heap2 (B.as_seq m1 g) /\
                 S.is_valid_header1 (v_id_f h_index) (B.as_seq m1 g) /\
                 stack_props m1 g st st_len /\

                 (modified3 m0 m1 g st st_len) /\
                 ((B.as_seq m1 g)  ==
                   snd (S.fieldPush_spec1 (B.as_seq m0 g)
                                          (stack_slice m0 st (stack_end m0 st_len))
                                          (h_index)
                                          (wz)
                                          j)) /\
                 (stack_slice m1 st (stack_end m1 st_len) ==
                   fst (S.fieldPush_spec1 (B.as_seq m0 g)
                                      (stack_slice m0 st (stack_end m0 st_len))
                                      (h_index)
                                      (wz)
                                      j)))

val closinfo_val_impl: (g:heap)->
                       (f_addr:S.hp_addr)->
            HA.Stack Usize.t
            (fun m -> B.live m g /\
                   S.well_formed_heap2 (B.as_seq m g) /\
                   Usize.v f_addr >= Usize.v S.mword /\
                   (S.is_valid_header1 (S.hd_address f_addr) (B.as_seq m g)) /\
                   (Usize.v (S.tag_of_object1 (S.hd_address f_addr) (B.as_seq m g)) == S.closure_tag) /\
                   (Usize.v (S.wosize_of_object1 (S.hd_address f_addr) (B.as_seq m g)) >= 2)
            )
            (fun m0 r m1 -> B.live m1 g /\
                         B.modifies (B.loc_none) m0 m1 (*/\
                         (S.is_hp_addr (Usize.add f_addr (Usize.mul 1UL S.mword)))*) /\
                         (r == S.closinfo_val_from_closure_object (*closinfo_val1*) (B.as_seq m0 g) f_addr)
            )

val start_env_clos_info: (g:heap)->
                         (f_addr:S.hp_addr)->
            HA.Stack Usize.t
            (fun m -> B.live m g /\
                   S.well_formed_heap2 (B.as_seq m g) /\
                   Usize.v f_addr >= Usize.v S.mword /\
                   (S.is_valid_header1 (S.hd_address f_addr) (B.as_seq m g)) /\
                   (Usize.v (S.tag_of_object1 (S.hd_address f_addr) (B.as_seq m g)) == S.closure_tag) /\
                   (Usize.v (S.wosize_of_object1 (S.hd_address f_addr) (B.as_seq m g)) >= 2)
            )
            (fun m0 r m1 -> B.live m1 g /\
                         B.modifies (B.loc_none) m0 m1 (*/\
                         (S.is_hp_addr (Usize.add f_addr (Usize.mul 1UL S.mword)))*) /\
                         (r == S.start_env_clos_info (B.as_seq m0 g) f_addr)
            )

val darken_wrapper_impl : (g:heap)->
                          (st: stack)->
                          (st_len: st_top)->
                          (h_index:S.hp_addr)->
                          (wz:S.wosize)->
          HA.Stack unit
          (fun m -> (*concrete memory properties*)
                 B.live m g /\ B.live m st /\ B.live m st_len /\


                 (*Since st_top is used for slice calculation of st, st_top contents should be less than or equal to st length*)
                  stack_end m st_len <= S.heap_size /\
                  disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\
                  (*algebraic properties to connect with Spec*)
                  S.well_formed_heap2 (B.as_seq m g) /\
                  S.is_valid_header1 (v_id_f h_index) (B.as_seq m g) /\
                  (Usize.v (S.tag_of_object1 h_index (B.as_seq m g)) < S.no_scan_tag) /\

                  (!wz == !(S.getWosize (S.read_word (B.as_seq m g) h_index))) /\

                  stack_props m g st st_len
           )

          (fun m0 () m1 -> B.live m1 g /\ B.live m1 st /\ B.live m1 st_len /\


                 (*Since st_top is used for slice calculation of st, st_top contents should be less than or equal to st length*)
                  stack_end m1 st_len <= S.heap_size /\
                  disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\

                 (*algebraic properties to connect with Spec*)
                 S.well_formed_heap2 (B.as_seq m1 g) /\
                 S.is_valid_header1 (v_id_f h_index) (B.as_seq m1 g) /\
                 stack_props m1 g st st_len /\

                 (modified3 m0 m1 g st st_len) /\
                 ((B.as_seq m1 g)  ==
                   snd (S.darken_wrapper (B.as_seq m0 g)
                                          (stack_slice m0 st (stack_end m0 st_len))
                                          (h_index)
                                          (wz)
                                          )) /\
                 (stack_slice m1 st (stack_end m1 st_len) ==
                   fst (S.darken_wrapper (B.as_seq m0 g)
                                      (stack_slice m0 st (stack_end m0 st_len))
                                      (h_index)
                                      (wz)
                                       )))


val mark_heap_body1_impl  :(g:heap)->
                           (st: stack)->
                           (st_len: st_top)->
           HA.Stack (unit)
           (*----------------------------------------Pre-conditions---------------------------------------------*)

           (fun m ->  (*Liveness of buffers------------------------------------------------------------------------*)
                   B.live m g /\ B.live m st /\ B.live m st_len /\

                   (*Disjointness of buffers--------------------------------------------------------------------*)
                   disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\

                   (*Range of st_top----------------------------------------------------------------------------*)
                   (stack_end m st_len  <= S.heap_size) /\
                   (stack_end m st_len > 0) /\


                   (*Algebraic properties of the contents of the buffers. This should match with spec-----------*)
                   S.well_formed_heap2 (B.as_seq m g) /\
                   (*We need to reason about only the used parts of st; that is upto st_top---------------------*)
                   stack_props m g st st_len)
            (fun m0 _ m1 -> B.live m1 g /\ B.live m1 st /\ B.live m1 st_len /\
                         disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\
                         modified3 m0 m1 g st st_len /\
                         stack_end m1 st_len <= S.heap_size /\
                         S.well_formed_heap2 (B.as_seq m1 g) /\
                         stack_props m1 g st st_len /\

                         ((B.as_seq m1 g)  ==
                              snd (S.mark5_body1 (B.as_seq m0 g) (stack_slice m0 st (stack_end m0 st_len)))) /\
                         (stack_slice m1 st (stack_end m1 st_len) ==
                              fst (S.mark5_body1 (B.as_seq m0 g) (stack_slice m0 st (stack_end m0 st_len)))))

val mark_heap7 : (g:heap)->
                (st: stack)->
                (st_len: st_top)->
           HA.Stack (unit)
           (*----------------------------------------Pre-conditions---------------------------------------------*)

           (fun m ->  (*Liveness of buffers------------------------------------------------------------------------*)
                   B.live m g /\ B.live m st /\ B.live m st_len /\


                   (*Disjointness of buffers--------------------------------------------------------------------*)
                   disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\

                   (*Range of st_top----------------------------------------------------------------------------*)
                   (stack_end m st_len  <= S.heap_size)  /\

                   (*Algebraic properties of the contents of the buffers. This should match with spec-----------*)
                    S.well_formed_heap2 (B.as_seq m g) /\

                   (*We need to reason about only the used parts of st; that is upto st_top---------------------*)
                   stack_props m g st st_len)

                    (*-----------------------------------------Post-conditions---------------------------------------------*)
           (*S.mark (B.as_seq m1 g) (B.as_seq m1 st upto stack_top)  == S.mark (B.as_seq m0 g) (B.as_seq m0 st upto stack_top)*)
           (fun m0 () m1 -> B.live m1 g /\ B.live m1 st /\ B.live m1 st_len /\
                         disjoint st st_len /\ disjoint g st /\ disjoint g st_len /\

                         S.well_formed_heap2 (B.as_seq m1 g) /\

                         Usize.v (B.get m1 st_len 0) == 0 /\
                         B.length st == S.heap_size /\
                         B.length st_len == 1 /\

                         (modified3 m0 m1 g st st_len) /\
                         (stack_props m1 g st st_len) /\
                         (B.as_seq m1 g) == S.mark7 (B.as_seq m0 g) (Seq.slice (B.as_seq m0 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_len) 0)))
           )

let index_zero_of_single_length_seq (m:H.mem)
                                    (buf: B.buffer Usize.t{B.length buf == 1})
                          : GTot (v:UInt64.t {v == (Seq.index (B.as_seq m buf) 0)})=
 let v = (Seq.index (B.as_seq m buf) 0) in
 v

val colorHeader3 : (g:heap) ->
                   (v_id:addr)->
                   (c:S.color) ->
            HA.Stack (unit)
            (fun m -> B.live m g  /\
                      (Seq.length (S.objects2 0UL (B.as_seq m g)) > 0) /\
                      (Seq.mem v_id (S.objects2 0UL (B.as_seq m g))))

            (fun m0 () m1 -> B.live m1 g /\ B.modifies (B.loc_buffer g) m0 m1 /\
                          ((B.as_seq m1 g) == S.colorHeader3 (v_id_f v_id) (B.as_seq m0 g) c))


#restart-solver

#restart-solver

val sweep_body_helper_with_free_list1 : (g:heap) ->
                                        (f_index: B.buffer Usize.t) ->
                                        (free_list_ptr: B.buffer Usize.t) ->
               HA.Stack unit
               (fun m ->  B.live m g /\ B.live m f_index /\ B.live m free_list_ptr /\

                       disjoint g f_index /\
                       disjoint g free_list_ptr /\
                       disjoint f_index free_list_ptr /\

                       (*S.well_formed_heap2 (B.as_seq m g) /\*)
                       (Seq.length (S.objects2 0UL (B.as_seq m g)) > 0) /\
                       S.noGreyObjects (B.as_seq m g) /\
                       B.length f_index == 1 /\
                       B.length free_list_ptr == 1  /\
                       (S.write_word_to_blue_object_field_lemma_props1 (B.as_seq m g)) /\

                       Usize.v (index_zero_of_single_length_seq m f_index) >= Usize.v S.mword /\
                       Usize.v (index_zero_of_single_length_seq m f_index) < S.heap_size /\
                       Usize.v (index_zero_of_single_length_seq m f_index) % Usize.v S.mword == 0 /\
                       (Seq.mem (v_id_f (S.hd_address (index_zero_of_single_length_seq m f_index))) (S.objects2 0UL (B.as_seq m g))) /\

                       Usize.v (index_zero_of_single_length_seq m free_list_ptr) >= Usize.v S.mword /\
                       Usize.v (index_zero_of_single_length_seq m free_list_ptr) < S.heap_size /\
                       Usize.v (index_zero_of_single_length_seq m free_list_ptr) % Usize.v S.mword == 0  /\
                      (Seq.mem (v_id_f (S.hd_address (index_zero_of_single_length_seq m free_list_ptr))) (S.objects2 0UL (B.as_seq m g)))  /\
                       S.color_of_object1 (v_id_f (S.hd_address (index_zero_of_single_length_seq m free_list_ptr))) (B.as_seq m g) == S.blue /\
                      (forall x y. Seq.mem x (S.objects2 0UL (B.as_seq m g)) /\ Seq.mem y (S.objects2 0UL (B.as_seq m g)) ==>
                                   Usize.v (S.getWosize (S.read_word (B.as_seq m g) x)) +
                                   Usize.v (S.getWosize (S.read_word (B.as_seq m g) y)) < S.heap_size)
           )

               (fun m0 _ m1 -> B.live m1 g /\  B.live m1 f_index /\ B.live m1 free_list_ptr  /\
                            (modified2 m0 m1 g free_list_ptr) /\


                            (B.as_seq m1 g == (fst (S.sweep_body_with_free_list (B.as_seq m0 g)
                                 (Seq.index (B.as_seq m0 f_index) 0) (Seq.index (B.as_seq m0 free_list_ptr) 0)))) /\
                            (Seq.index (B.as_seq m1 free_list_ptr) 0 ==
                                 (snd (S.sweep_body_with_free_list (B.as_seq m0 g) (Seq.index (B.as_seq m0 f_index) 0) (Seq.index (B.as_seq m0 free_list_ptr) 0))))
                                 )


let f_index_lemma (g:S.heap)
                  (f_index: S.hp_addr)

       : Lemma
         (requires  (Usize.v f_index >= Usize.v S.mword /\
                     Usize.v f_index < S.heap_size /\
                      Usize.v f_index % Usize.v S.mword == 0 /\
                      (Seq.mem (v_id_f (S.hd_address f_index)) (S.objects2 0UL g)) /\
                      (let h_index_val = S.hd_address f_index in
                       let wz = S.wosize_of_object1 h_index_val g in
                       let h_index_new =  Usize.add h_index_val (Usize.mul (Usize.add wz 1UL) S.mword) in
                       let f_index_new = Usize.add h_index_new S.mword in
                       Usize.v f_index_new < S.heap_size)))

         (ensures (let h_index_val = S.hd_address f_index in
                   let wz = S.wosize_of_object1 h_index_val g in
                   let h_index_new =  Usize.add h_index_val (Usize.mul (Usize.add wz 1UL) S.mword) in
                   let f_index_new = Usize.add h_index_new S.mword in
                   (S.hd_address f_index_new == h_index_new)
         )) =
 let h_index_val = S.hd_address f_index in
 let wz = S.wosize_of_object1 h_index_val g in
 let h_index_new =  Usize.add h_index_val (Usize.mul (Usize.add wz 1UL) S.mword) in
 let f_index_new = Usize.add h_index_new S.mword in
 assert (UInt.fits (Usize.v f_index_new - Usize.v S.mword) Usize.n);

 S.wosize_plus_times_mword_multiple_of_mword1 wz;
 S.sum_of_multiple_of_mword_is_multiple_of_mword h_index_val (Usize.mul (Usize.add wz 1UL) S.mword);
 assert (Usize.v h_index_new % Usize.v S.mword == 0);
 S.sum_of_multiple_of_mword_is_multiple_of_mword h_index_new S.mword;
 assert (Usize.v f_index_new % Usize.v S.mword == 0);
 assert (Usize.v f_index_new < S.heap_size);
 assert (S.is_hp_addr f_index_new);
 assert (S.hd_address f_index_new == h_index_new);
 ()


val sweep1_with_free_list1 : (g:heap) ->
                             (f_index: B.buffer Usize.t) ->
                             (free_list_ptr: B.buffer Usize.t) ->
           HA.Stack unit
               (fun m ->  B.live m g /\ B.live m f_index /\ B.live m free_list_ptr /\

                       disjoint g f_index /\
                       disjoint g free_list_ptr /\
                       disjoint f_index free_list_ptr /\
                       (Seq.length (S.objects2 0UL (B.as_seq m g)) > 0) /\
                       S.noGreyObjects (B.as_seq m g) /\

                       B.length f_index == 1 /\
                       B.length free_list_ptr == 1 /\
                       Usize.v (index_zero_of_single_length_seq m f_index) >= Usize.v S.mword /\
                       Usize.v (index_zero_of_single_length_seq m f_index) < S.heap_size /\
                       Usize.v (index_zero_of_single_length_seq m f_index) % Usize.v S.mword == 0 /\
                      (Seq.mem (v_id_f (S.hd_address (index_zero_of_single_length_seq m f_index))) (S.objects2 0UL (B.as_seq m g))) /\

                      (Seq.length (S.objects2 (S.hd_address  (index_zero_of_single_length_seq m f_index)) (B.as_seq m g)) > 0) /\
                      (S.write_word_to_blue_object_field_lemma_props1 (B.as_seq m g)) /\

                       Usize.v (index_zero_of_single_length_seq m free_list_ptr) >= Usize.v S.mword /\
                       Usize.v (index_zero_of_single_length_seq m free_list_ptr) < S.heap_size /\
                       Usize.v (index_zero_of_single_length_seq m free_list_ptr) % Usize.v S.mword == 0  /\
                       (Seq.mem (v_id_f (S.hd_address (index_zero_of_single_length_seq m free_list_ptr))) (S.objects2 0UL (B.as_seq m g))) /\

                       S.color_of_object1 (v_id_f (S.hd_address (index_zero_of_single_length_seq m free_list_ptr))) (B.as_seq m g) == S.blue /\
                       (forall x y. Seq.mem x (S.objects2 0UL (B.as_seq m g)) /\ Seq.mem y (S.objects2 0UL (B.as_seq m g)) ==>
                                   Usize.v (S.getWosize (S.read_word (B.as_seq m g) x)) +
                                   Usize.v (S.getWosize (S.read_word (B.as_seq m g) y)) < S.heap_size))

               (fun m0 _ m1 -> B.live m1 g /\ B.live m1 f_index  /\ B.live m1 free_list_ptr /\
                            (fst (S.sweep_with_free_list3 (B.as_seq m0 g) (Seq.index (B.as_seq m0 f_index) 0)
                                        (Seq.index (B.as_seq m0 free_list_ptr) 0)) == B.as_seq m1 g) /\
                            (snd (S.sweep_with_free_list3 (B.as_seq m0 g)
                                        (Seq.index (B.as_seq m0 f_index) 0) (Seq.index (B.as_seq m0 free_list_ptr) 0)) ==
                                               Seq.index (B.as_seq m1 free_list_ptr) 0) /\
                            (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer free_list_ptr) (B.loc_buffer f_index))) m0 m1)
                            )





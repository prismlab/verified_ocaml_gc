module Spec.GC_part1

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

(*Karamel is not going to extract the definition*)
///Machine words corresponding to a 64 bit machine
//If using a 32 bit machine, mword = 8ul
noextract inline_for_extraction
unfold let mword = 8UL

(*Karamel is not going to extract the definition*)
///Machine words corresponding to a 64 bit machine

/// heap_size indicates the heap memory size. A valid object address should lie between heap_low to heap_high.
noextract inline_for_extraction
unfold let heap_size = 1024

/// GC should operate on blocks with tags < no_scan_tag
noextract inline_for_extraction
unfold let no_scan_tag = 251

/// To represent mutually recursive objects
noextract inline_for_extraction
unfold let closure_tag = 247

/// To separate mutually recursive objects, that are store under closure tag, from each other.
noextract inline_for_extraction
unfold let infix_tag = 249

(*
  Code
  -------------------------------------
  let test () =
  let n = Random.int 10 in

  let rec f x y = n + n + y + g x
  and g y = f y (y + 1) in

  f
  -----------------------------------------------------------------------------------------------------------------------------------------------------------
  Object representation
  
  |----------------------------|
  | header (closure_tag,size=6)|
  |----------------------------|
  | "caml_curry2"              | 0       <- start of closure `f` (offset=0)
  |----------------------------|
  | {arity=2,startenv=6}       | 1
  |----------------------------|
  | function pointer of `f`    | 2
  |----------------------------|
  | header (infix_tag,size=32) | 3  2     :: size = 32 = 8 * 4 (offset of the start of the closure for `g`)
  |----------------------------|
  | function pointer of `g`    | 4, 3  g(0) f(3)      <- start of closure `g` (offset=4)
  |----------------------------|
  | {arity=1,startenv=2}       | 5, 4       :: startenv = 2 = 6 (absolute startenv) - 4 (offset of `g`)
  |----------------------------|
  | value of <n>               | 6       <- start of env (offset=6)


  |----------------------------|
  | header (closure_tag,size=6)|
  |----------------------------|
  | function pointer of `f`    | 0       
  |----------------------------|
  | {arity=2,startenv=6}       | 1
  |----------------------------|
  | header (infix_tag,size=32) | 2
  |----------------------------|
  | function pointer of `g`    | 3    
  |----------------------------|
  | {arity=1,startenv=2}       | 4 
  |----------------------------|
  | value of <n>               | 5      
  |----------------------------|
      


start_of_env = 5 

utop # Obj.reachable_words (Obj.repr g);;
- : int = 6
─( 09:41:23 )─< command 73 >───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # Obj.reachable_words (Obj.repr f);;
- : int = 6
─( 09:42:48 )─< command 74 >───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # Obj.size (Obj.repr f);;
- : int = 5
─( 09:43:02 )─< command 75 >───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────{ counter: 0 }─
utop # Obj.size (Obj.repr g);;
- : int = 3

*)

let is_heap_size_multiple_of_mwords ()
          : Tot (b:bool{b == true <==> heap_size % (Usize.v mword) == 0})= 
  if (heap_size % (Usize.v mword) = 0) then true
 else
   false

let test  =
  assert (is_heap_size_multiple_of_mwords ())

(*Use hp_ as the prefix for all variables which are pointers to headers. 
      val_ as prefix for all variables which point to the object (i.e, the first field of the object).*)


(*Colors used in OCaml for 64 bit machine. For 32 bit machine, ul has to be used instead of UL*)
let blue = 0UL
let white = 1UL
let gray = 2UL
let black = 3UL

/// ------------OCaml object header for a 64 bit machine--------------------
///        wosize          color       tag
/// |--------------------|---------|------------|--------------------------
///       54 bits          2 bits       8 bits      variable length fields

(*max word size for data fields for 64 bit machines*)
(*----------------------------------------------------------------------------------------------------------------------*)
let max_wosize =
  Usize.sub (Usize.shift_left 1UL 54ul) 1UL

(*max color value*)
let max_color =
  Usize.sub (Usize.shift_left 1UL 2ul) 1UL

(*max tag value*)
let max_tag = Usize.sub (Usize.shift_left 1UL 8ul) 1UL

(*---------------------------------------------------------------------------------------------------------------------*)
(*max_wosize, max_color, max_tag properties*)
val max_wosize_lemma : unit -> Lemma (Usize.v max_wosize = pow2 54 - 1)

val max_color_size_lemma : unit -> Lemma (Usize.v max_color = pow2 2 - 1)

val max_tag_size_lemma : unit -> Lemma (Usize.v max_tag = pow2 8 - 1)
(*---------------------------------------------------------------------------------------------------------------------*)

(*Definitions*)
type heap = g:seq U8.t{Seq.length g == heap_size /\ is_heap_size_multiple_of_mwords ()}

type wosize = sz:Usize.t{0 <= Usize.v sz /\ Usize.v sz <= Usize.v max_wosize}

type color = cl:Usize.t{0 <= Usize.v cl /\ Usize.v cl <= Usize.v max_color}

type tag = tg:Usize.t{0 <= Usize.v tg /\ Usize.v tg <= Usize.v max_tag}

val is_size_fits_after_subtraction :(x:Usize.t) ->
                                    (y:Usize.t) ->
                       Tot (b:bool{b == true <==> UInt.fits (Usize.v x - Usize.v y) Usize.n})

type hp_addr = h:Usize.t {Usize.v h >= 0 /\ Usize.v h < heap_size /\ (Usize.v h % 8 == 0)}

type hp_addr_32 = h:UInt32.t {UInt32.v h >= 0 /\ UInt32.v h < heap_size /\ (UInt32.v h % 8 == 0)}


let is_hp_addr (h:Usize.t) 
             : Tot (b:bool{b == true <==> (Usize.v h < heap_size) /\ (Usize.v h % Usize.v mword = 0)})=
   if ((Usize.v h < heap_size) && (Usize.v h % Usize.v mword = 0)) then true
   else
     false 

type val_addr = o:hp_addr {Usize.v o >= Usize.v mword}
 
let read_word (byte_array: heap) 
              (byte_index:hp_addr)
        : Tot (v:UInt64.t{v ==  uint64_of_le (slice byte_array (Usize.v byte_index) ((Usize.v byte_index) + Usize.v mword))})    =  
 let word_array = slice byte_array (Usize.v byte_index) ((Usize.v byte_index) + Usize.v mword) in // Extract the word from byte array
 uint64_of_le word_array

let read_word1 (byte_array: heap) 
               (byte_index:hp_addr_32)  
        : Tot (v:UInt64.t{v ==  uint64_of_le (slice byte_array (UInt32.v byte_index) ((UInt32.v byte_index) + Usize.v mword))})    =  
 let word_array = slice byte_array (UInt32.v byte_index) ((UInt32.v byte_index) + Usize.v mword) in // Extract the word from byte array
 uint64_of_le word_array

let replace_range (source: heap) 
                  (start_index:hp_addr {Usize.v start_index < length source}) 
                  (replacement: seq UInt8.t{length replacement == Usize.v mword}) 
  : Pure (seq UInt8.t) (requires length replacement <= length source - (Usize.v start_index)) 
               
                (ensures fun result -> (*1*)   (length result == length source) /\
                                    (*2*)   (forall (i:nat{i < length source}). 
                                                 index result i == (
                                                       if i >= (Usize.v start_index) && i < (Usize.v start_index) + (length replacement) then
                                                         (index replacement (i - (Usize.v start_index))) 
                                                       else 
                                                          index source i))) =
  let before_start = slice source 0 (Usize.v start_index) in
  let after_end = slice source ((Usize.v start_index) + (length replacement)) (length source) in
  append before_start (append replacement after_end)

let replace_range1 (source: heap) 
                   (start_index:hp_addr) 
                   (replacement: seq UInt8.t{length replacement == Usize.v mword}) 
  : Pure (seq UInt8.t) (requires True) 
                       (ensures fun result -> (*1*)   (length result == length source) /\
                                    (*2*)   (forall (i:nat{i < length source}). 
                                                 index result i == (
                                                       if i >= (Usize.v start_index) && i < (Usize.v start_index) + (length replacement) then
                                                         (index replacement (i - (Usize.v start_index))) 
                                                       else 
                                                          index source i))) =
  let before_start = slice source 0 (Usize.v start_index) in
  let after_end = slice source ((Usize.v start_index) + (length replacement)) (length source) in
  let result = append before_start (append replacement after_end) in
  assert (forall i. i > (Usize.v start_index) && i < (Usize.v start_index) + (length replacement) ==> i % Usize.v mword <> 0);
  assert (forall i. Usize.v i >= 0 /\ Usize.v i < Usize.v start_index /\ Usize.v i % Usize.v mword == 0 ==> index result (Usize.v i) == index source (Usize.v i));
  assert (forall i. Usize.v i >= 0 /\ Usize.v i < Usize.v start_index ==> index result (Usize.v i) == index source (Usize.v i));
  assert (Seq.length before_start == Usize.v start_index);
  assert ((Seq.length before_start) % Usize.v mword == 0);
  assert (Seq.length after_end == length source - (Usize.v start_index + length replacement));
  assert (Seq.length after_end % Usize.v mword == 0);
  lemma_eq_elim (slice result (Usize.v start_index) ((Usize.v start_index) + UInt64.v mword)) replacement;
  lemma_eq_elim (slice result 0 (Usize.v start_index)) before_start;
  assert (read_word result start_index == uint64_of_le replacement);
  result


let replace_range_structure_lemma (source: heap) 
                                  (start_index:hp_addr) 
                                  (replacement: seq UInt8.t{length replacement == Usize.v mword}) 
                    : Lemma
                      (ensures replace_range source start_index replacement == 
                        append (slice source 0 (Usize.v start_index)) (append replacement (slice source ((Usize.v start_index) + (length replacement)) (length source)))) =
  ()

(*This was not an easy proof. Requires proof by contradiction.*)
let replace_range_before_start_lemma (source: heap) 
                                     (start_index:hp_addr) 
                                     (replacement: seq UInt8.t{length replacement == Usize.v mword})
                                     (i:hp_addr{(Usize.v i >= 0) /\ (Usize.v i < Usize.v start_index) /\ (Usize.v i % Usize.v mword == 0)})
                    : Lemma
                      (ensures (read_word (replace_range source start_index replacement) i == read_word source i))=
  let s = replace_range source start_index replacement in
  let value1 = read_word s i in
  let value2 = read_word source i in
  lemma_eq_elim (slice s (Usize.v start_index) ((Usize.v start_index) + UInt64.v mword)) replacement;
  assert (read_word s start_index == uint64_of_le replacement);
  if (value1 = value2) then ()
  else
   (
     assert (value1 <> value2);
     assert (forall i. Usize.v i >= 0 /\ Usize.v i < Usize.v start_index ==> index s (Usize.v i) == index source (Usize.v i));
     assert (forall i. Usize.v i >= 0 /\ Usize.v i < Usize.v start_index /\ (Usize.v i % Usize.v mword == 0) ==> index s (Usize.v i) == index source (Usize.v i));
     assert (forall j. Usize.v j > Usize.v i /\ Usize.v j < (Usize.v i + Usize.v mword) ==> Usize.v j < Usize.v start_index);
     assert (forall j. Usize.v j > Usize.v i /\ Usize.v j < (Usize.v i + Usize.v mword) ==> (index source (Usize.v j) == index s (Usize.v j)));
     lemma_eq_elim (slice s (Usize.v i) (Usize.v i + Usize.v mword)) (slice source (Usize.v i) (Usize.v i + Usize.v mword));
     assert (Seq.slice s (Usize.v i) (Usize.v i + Usize.v mword) == Seq.slice source (Usize.v i) (Usize.v i + Usize.v mword));
     assert (uint64_of_le (Seq.slice s (Usize.v i) (Usize.v i + Usize.v mword)) == uint64_of_le (Seq.slice source (Usize.v i) (Usize.v i + Usize.v mword)));
     assert (value1 == value2);
     ()
   )

let replace_range_before_start_all_lemma (source: heap) 
                                         (start_index:hp_addr) 
                                         (replacement: seq UInt8.t{length replacement == Usize.v mword})
                           : Lemma
                             (ensures (forall (i:hp_addr). (Usize.v i >= 0) /\ (Usize.v i < Usize.v start_index) /\ (Usize.v i % Usize.v mword == 0) ==>
                                             read_word (replace_range source start_index replacement) i == read_word source i))=
 Classical.forall_intro (Classical.move_requires (replace_range_before_start_lemma source start_index replacement))

let replace_range_after_start_end_lemma (source: heap) 
                                        (start_index:hp_addr) 
                                        (replacement: seq UInt8.t{length replacement == Usize.v mword})
                                        (i:hp_addr{(Usize.v i >= (Usize.v start_index) + (length replacement)) /\ (Usize.v i < length source) /\ (Usize.v i % Usize.v mword == 0)})
                    : Lemma
                      (ensures (read_word (replace_range source start_index replacement) i == read_word source i))=
  let s = replace_range source start_index replacement in
  let value1 = read_word s i in
  let value2 = read_word source i in
  lemma_eq_elim (slice s (Usize.v start_index) ((Usize.v start_index) + UInt64.v mword)) replacement;
  assert (read_word s start_index == uint64_of_le replacement);
  if (value1 = value2) then ()
  else
   (
     assert (forall i. Usize.v i >= ((Usize.v start_index) + (length replacement)) /\ Usize.v i < length source ==> index s (Usize.v i) == index source (Usize.v i));
     assert (forall i. Usize.v i >= ((Usize.v start_index) + (length replacement)) /\ Usize.v i < length source /\ (Usize.v i % Usize.v mword == 0) ==> index s (Usize.v i) == index source (Usize.v i));
     assert (forall j. Usize.v j > Usize.v i /\ Usize.v j < (Usize.v i + Usize.v mword) ==> Usize.v j < length source);
     assert (forall j. Usize.v j > Usize.v i /\ Usize.v j < (Usize.v i + Usize.v mword) ==> (index source (Usize.v j) == index s (Usize.v j)));
     lemma_eq_elim (slice s (Usize.v i) (Usize.v i + Usize.v mword)) (slice source (Usize.v i) (Usize.v i + Usize.v mword));
     assert (Seq.slice s (Usize.v i) (Usize.v i + Usize.v mword) == Seq.slice source (Usize.v i) (Usize.v i + Usize.v mword));
     assert (uint64_of_le (Seq.slice s (Usize.v i) (Usize.v i + Usize.v mword)) == uint64_of_le (Seq.slice source (Usize.v i) (Usize.v i + Usize.v mword)));
     assert (value1 == value2);
     ()
   )

let replace_range_after_start_end_all_lemma (source: heap) 
                                            (start_index:hp_addr) 
                                            (replacement: seq UInt8.t{length replacement == Usize.v mword})
                           : Lemma
                             (ensures (forall (i:hp_addr). (Usize.v i >= ((Usize.v start_index) + (length replacement))) /\ (Usize.v i < length source) /\ (Usize.v i % Usize.v mword == 0) ==>
                                             read_word (replace_range source start_index replacement) i == read_word source i))=
 Classical.forall_intro (Classical.move_requires (replace_range_after_start_end_lemma source start_index replacement))

let write_word (byte_array: heap)
               (byte_index: hp_addr)
               (value: UInt64.t)
  : Pure (heap) 
    (requires True)
    (ensures fun result -> length result == length byte_array /\
                        (forall (i:nat{i < length byte_array}). 
                                                 index result i == (
                                                       if i >= (Usize.v byte_index) && 
                                                          i < ((Usize.v byte_index) + (length (FStar.Endianness.le_of_uint64 value))) then
                                                         (index (FStar.Endianness.le_of_uint64 value) (i - (Usize.v byte_index))) 
                                                       else 
                                                          index byte_array i)) /\
                        read_word result byte_index == value) =  
 let bytes = FStar.Endianness.le_of_uint64 value in
 assert (uint64_of_le bytes == value);
 assert (length bytes == Usize.v mword);
 let result = replace_range byte_array byte_index bytes in
 lemma_eq_elim (slice result (Usize.v byte_index) ((Usize.v byte_index) + UInt64.v mword)) bytes; 
 result

let read_and_write_are_valid (byte_array: heap)
                             (byte_index:hp_addr)
                             (value: UInt64.t)
  : Lemma (read_word (write_word byte_array byte_index value) byte_index == value) = ()

let write_word_replacement_lemma (byte_array: heap)
                                 (byte_index: hp_addr)
                                 (value: UInt64.t)
            : Lemma
              (ensures (forall (i:hp_addr). Usize.v i >= (Usize.v byte_index) /\  Usize.v i < ((Usize.v byte_index) + Usize.v mword) /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) byte_index == value)) = ()
    
let write_word_before_start_lemma (byte_array: heap)
                                  (byte_index: hp_addr)
                                  (value: UInt64.t)
                      : Lemma
                        (ensures (forall (i:hp_addr). Usize.v i >= 0 /\  Usize.v i < Usize.v byte_index /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) i == read_word byte_array i)) = 
 replace_range_before_start_all_lemma byte_array byte_index (FStar.Endianness.le_of_uint64 value)


let write_word_after_start_end_lemma (byte_array: heap)
                                     (byte_index: hp_addr)
                                     (value: UInt64.t)
                      : Lemma
                        (ensures (forall (i:hp_addr). (Usize.v i >= ((Usize.v byte_index) + Usize.v mword)) /\ (Usize.v i < length byte_array) /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) i == read_word byte_array i)) =
 replace_range_after_start_end_all_lemma byte_array byte_index (FStar.Endianness.le_of_uint64 value)


let write_word_lemma (byte_array: heap)
                     (byte_index: hp_addr)
                     (value: UInt64.t)
                : Lemma 
                  ((forall (i:hp_addr). read_word (write_word byte_array byte_index value) i == (
                                                           if Usize.v i >= (Usize.v byte_index) && 
                                                              Usize.v i < ((Usize.v byte_index) + (Usize.v mword)) && 
                                                              (Usize.v i % Usize.v mword = 0) then
                                                                  value 
                                                             else 
                                                                read_word byte_array i))) = 
write_word_replacement_lemma byte_array byte_index value;  
write_word_before_start_lemma byte_array byte_index value;
write_word_after_start_end_lemma byte_array byte_index value;
()


/// Extract wosize from header value
val getWosize : (h:Usize.t) ->
          Tot (wz:wosize{wz == Usize.shift_right h 10ul})

/// Extract color from header value
val getColor : (h:Usize.t) ->
          Tot (c:color{c = Usize.logand (Usize.shift_right h 8ul) 3UL})

/// Extract tag from header value
val getTag : (h:Usize.t) ->
          Tot (tg:tag{tg == Usize.logand h 255UL})

val color_of_object1 : (v_id: hp_addr) ->
                       (g:heap)->
             Tot (c:color{c == getColor(read_word g v_id)}) 

val wosize_of_object1 : (v_id: hp_addr) ->
                        (g:heap)->
             Tot (w:wosize{w == getWosize(read_word g v_id)}) 


val tag_of_object1 : (v_id: hp_addr) ->
                     (g:heap)->
             Tot (t:tag{t == getTag(read_word g v_id)}) 


val isBlueObject1 :(v_id: hp_addr)->
                   (g:heap) ->
         Tot (b: bool {b == true <==> (color_of_object1 v_id g) == blue}) 

val isWhiteObject1 : (v_id: hp_addr)->
                     (g:heap) ->
         Tot (b: bool {b == true <==> (color_of_object1 v_id g) == white}) 

val isGrayObject1 : (v_id: hp_addr)->
                    (g:heap) ->
         Tot (b: bool {b == true <==> (color_of_object1 v_id g) == gray}) 

val isBlackObject1 : (v_id: hp_addr)->
                     (g:heap) ->
         Tot (b: bool {b == true <==> (color_of_object1 v_id g) == black}) 

val makeHeader : (wz:wosize) ->
                 (c:color) ->
                 (tg:tag) ->
             Tot (h:Usize.t{wz == getWosize h /\
                            c == getColor h /\
                            tg == getTag h})
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// h_index = start byte address of the object
/// wz = wosize type
/// is_fields_within_limit1 is true iff start address + ((wz + 1) * mword - 1) < heap_size
/// Let heap_size = 24
/// start_address = 8
/// wz = 1
/// (wz + 1) * mword = 2 * mword = 2 * 8 = 16
/// That is the object starting at address 8 can have a single field to fit within the heap size limit.
/// ----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24
/// |..................|  |.....................| |
///      header                    field 1        heap_size
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------


val isPointer : (v_id: hp_addr) ->
                (g:heap) ->
            Tot (b:bool{b == true <==> Usize.logand (read_word g v_id) 1UL == 0UL})

(*No object size exceeds the heap limit*)
(*h_index + (wz + 1) * mword takes to the next header. Therefore, (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) will take us to the last index of the
   byte array which marks the end of the last field of the object. That should be less than heap size.*)

/// Calculation of start of environment offset in closure objects
/// #define Closinfo_val(val) Field((val), 1)          /* Arity and start env */
/// arity (8 bits) . start-of-environment ((wordsize - 9) bits) . 1
/// For a closure object size including header should be wosize stored in closure object header + 1
/// wosize stored in closure object header should be minimum = 1 (caml_curry2) + 1 (start_env info) + 1 (first code pointer) + 1 (header infix tag) + 1 (second code pointer) +
///                                                            1 (start_enc info associated with second pointer) = 6 words.

let closinfo_val  (g:heap) 
                  (f_addr: hp_addr{is_hp_addr (Usize.add f_addr mword)})
          : Tot (Usize.t) =
  let offset_field = Usize.add f_addr mword in
  assert (is_hp_addr offset_field);
  let offset_field_val = read_word g offset_field in
  offset_field_val

(*The sum of an address and its ((wosize value + 1) * mword - 1) should be less than the heap_size*)
(*(wosize value + 1) * mword ---> Takes to the heap address next of wosize value in the byte array.*)

val is_fields_within_limit1  : (h_index: hp_addr) ->
                               (wz: wosize)->
              Tot (b:bool{b == true <==> (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size)})

#push-options "--split_queries always"


val is_fields_contents_within_limit2 : (h_index: hp_addr) ->
                                       (wz: wosize{is_fields_within_limit1 h_index wz}) ->
                                       (g:heap(*{Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
                                               Usize.v (tag_of_object1 h_index g) <> closure_tag}*)) ->
                            Tot (b:bool{b == true <==>  (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}).isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                          (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) >= Usize.v mword /\
                                                          Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) < heap_size) /\
                                                          is_hp_addr (read_word g (Usize.add h_index (Usize.mul i mword))))})
                            (decreases (Usize.v wz))

let wosize_times_mword_multiple_of_mword (wz:wosize)
                     :Lemma 
                      (ensures (Usize.v (Usize.mul wz mword) % Usize.v mword == 0)) = ()


let sum_of_multiple_of_mword_is_multiple_of_mword (x:Usize.t{Usize.v x % Usize.v mword == 0})
                                                  (y:Usize.t{Usize.v y % Usize.v mword == 0})
                                :Lemma 
                                 (ensures ((Usize.v x + Usize.v y) % Usize.v mword == 0)) = ()

val objects2 : (h_index: hp_addr)->
               (g:heap) ->
        Tot (s:seq Usize.t {Seq.length s > 0 ==> (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                 (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0) /\
                                                 (Seq.mem h_index s) (*/\
                                                 (let h_index_new =  
                                                     Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword) in
                                                   let f_index_new =  Usize.add h_index_new mword in
                                                   Usize.v f_index_new <> heap_size) *)/\
                                                 (forall x. Seq.mem x s ==> is_hp_addr x) /\
                                                 (forall x. Seq.mem x s ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                 (forall x. Seq.mem x s ==> Usize.v x >= Usize.v h_index) /\
                                                 (forall x. Seq.mem x s ==> Usize.v (getWosize (read_word g x)) > 0) /\
                                                 (G.is_vertex_set s) /\
                                                 (forall x. Seq.mem x s ==> Usize.v x + Usize.v mword < heap_size) /\
                                                 ((forall x y. Seq.mem x s /\ 
                                                   (Usize.v y >= Usize.v x + Usize.v mword) /\ 
                                                   (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1)) ==>
                                                   ~(Seq.mem y s)))})
                                                                     
                       (decreases (heap_size - Usize.v h_index))

/// Given the start address of an object, which is the address of the first field of the object, hd_address gets the header address of that object
let hd_address (st_index: hp_addr{UInt.fits (Usize.v st_index - Usize.v mword) Usize.n})
          : Tot (h:hp_addr{Usize.v h == Usize.v st_index - Usize.v mword}) = 
  let h_index = Usize.sub st_index mword in
  assert (Usize.v h_index % Usize.v mword == 0);
  assert (Usize.v h_index >= 0);
  assert (is_hp_addr h_index);
  h_index

#restart-solver 

/// Given the header address of an object, the f_address finds the address of the first field of the object
let f_address (h_index: hp_addr{UInt.fits (Usize.v h_index + Usize.v mword) Usize.n /\ (Usize.v h_index + Usize.v mword < heap_size)}) 
         : Tot (f:hp_addr{Usize.v f == Usize.v h_index + Usize.v mword})=
  let f_index = Usize.add h_index mword in
  assert (Usize.v f_index % Usize.v mword == 0);
  assert (Usize.v f_index >= 0);
  assert (is_hp_addr f_index);
  f_index

#restart-solver 

let closinfo_val_from_closure_object (g:heap) 
                                     (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                                    (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                                                    (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2) /\
                                                    is_fields_within_limit1 (hd_address f_addr) (wosize_of_object1 (hd_address f_addr) g)}) 
            :Tot (clos_info:Usize.t{ (is_hp_addr (Usize.add f_addr (Usize.mul 1UL mword))) /\
                                     (clos_info == read_word g (Usize.add f_addr (Usize.mul 1UL mword)))})=
 
 let hdr_f_addr = hd_address f_addr in
 let offst1 = Usize.mul 1UL mword in
 let wz = wosize_of_object1 hdr_f_addr g in
 assert (is_fields_within_limit1 hdr_f_addr wz);
 let s1 = Usize.add f_addr offst1 in
 assert (Usize.v s1 < heap_size);
 assert (Usize.v s1 % Usize.v mword == 0);
 assert (is_hp_addr s1);
 let clos_info = read_word g s1 in
 assert (clos_info == read_word g s1);
 assert (clos_info == read_word g (Usize.add f_addr (Usize.mul 1UL mword)));
 clos_info



#restart-solver

#restart-solver

(*#define Make_closinfo(arity,delta) \
  (((uintnat)(arity) << 56) + ((uintnat)(delta) << 1) + 1)*)

let extract_start_env_bits (clos_info:Usize.t) 
               : Tot (strt_env: Usize.t{strt_env == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul})=
 let l1 = Usize.shift_left clos_info 8ul in
 let r1 = Usize.shift_right l1 9ul in
 assert (r1 == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul);
 r1

#restart-solver 

val objects2_mem_lemma1 :   (h_index: hp_addr) ->
                            (g:heap) ->
                           
                      
            Lemma 
            (ensures ((Seq.length (objects2 h_index g) > 0  ==> (forall x. Seq.mem x (objects2 h_index g) /\ 
                                                                  Usize.v (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) < heap_size ==> 
                                                                       Seq.mem (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) 
                                                                           (objects2 h_index g)))))
            (decreases (heap_size - Usize.v h_index))

val objects2_equal_lemma :(h_index:hp_addr) ->
                          (g:heap) ->
                          (g':heap) ->
                     Lemma
                       (requires (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index))


val objects2_equal_lemma3 :(h_index:hp_addr) ->
                           (g:heap) ->
                           (g':heap) ->
                       Lemma
                       (requires (objects2 0UL g == objects2 0UL g') /\
                                 (Seq.mem h_index (objects2 0UL g)) /\
                                 (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word g' x)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index))
                       
val objects2_length_lemma :(h_index:hp_addr) ->
                           (g:heap) ->
                     Lemma
                     (ensures (Seq.length (objects2 h_index g) <= (heap_size - Usize.v h_index)))
                     (decreases (heap_size - Usize.v h_index))

val objects2_color_lemma : (h_index:hp_addr) ->
                           (g:heap) ->
                     Lemma
                     (ensures (forall x. Seq.mem x (objects2 h_index g) ==> color_of_object1 x g == white \/
                                                                       color_of_object1 x g == gray \/
                                                                       color_of_object1 x g == black \/
                                                                       color_of_object1 x g == blue))
                     (decreases (heap_size - Usize.v h_index))



#restart-solver

let heap_remains_same_except_index_v_id  (v_id:hp_addr)
                                         (g:heap)
                                         (g':heap{Seq.length g == Seq.length g'}) =
  forall (x:Usize.t {Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). x <> v_id ==>
           read_word g x == read_word g' x 
           

val get_allocated_block_addresses  : (g:heap {Seq.length (objects2 0UL g) > 0}) ->
                           Tot (allocs: seq Usize.t {(forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x allocs ==> is_hp_addr x) /\
                                                      (forall x. Seq.mem x allocs ==> Seq.mem x (objects2 0UL g)) /\
                                                      (G.is_vertex_set allocs) /\
                                                      (G.subset_vertices allocs (objects2 0UL g)) /\
                                                      (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                                 (isGrayObject1 x g) \/
                                                                                (isBlackObject1 x g)) /\
                                                      (forall x. Seq.mem x (objects2 0UL g) /\
                                                           ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                               Seq.mem x allocs)})


val is_fields_contents_within_limit2_lemma_for_sweep :  (h_index: hp_addr) ->
                                                           (wz: wosize{is_fields_within_limit1 h_index wz}) ->
                                                           (wz': wosize{is_fields_within_limit1 h_index wz'})->
                                                           (g:heap{Seq.length (objects2 0UL g) > 0}) ->
                                                           (g':heap{Seq.length (objects2 0UL g') > 0})->
                                          
                          Lemma
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
                            (decreases (Usize.v wz))

#restart-solver

//#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

val get_allocated_block_addresses_lemma :   (g:heap {Seq.length (objects2 0UL g) > 0}) ->
                                            (g':heap{Seq.length (objects2 0UL g') > 0})->
                                            (v_id:hp_addr) ->
                                            (c:color)->
                           Lemma
                           (requires (objects2 0UL g ==
                                      objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id v_id g g' /\
                                      color_of_object1 v_id g' == c /\
                                      (color_of_object1 v_id g == white \/ color_of_object1 v_id g == gray \/ 
                                      color_of_object1 v_id g == black) /\
                                      wosize_of_object1 v_id g' == wosize_of_object1 v_id g /\
                                      tag_of_object1 v_id g' == tag_of_object1 v_id g /\
                                      Seq.mem v_id (objects2 0UL g) /\ Seq.mem v_id (objects2 0UL g') /\
                                      (c == 1UL \/ c == 2UL \/ c == 3UL))
                           (ensures (get_allocated_block_addresses g == get_allocated_block_addresses g'))

#reset-options "--z3rlimit 500"



val get_black_block_addresses : (g:heap {Seq.length (objects2 0UL g) > 0}) ->
                                (allocs: seq Usize.t {Seq.equal allocs (get_allocated_block_addresses g) /\
                                                     (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x allocs ==> Seq.mem x (objects2 0UL g)) /\
                                                     (G.is_vertex_set allocs) /\
                                                     (G.subset_vertices allocs 
                                                       (objects2 0UL g)) /\
                                                     (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                               (isGrayObject1 x g) \/
                                                                               (isBlackObject1 x g))}) ->
                            Tot (blacks: G.vertex_list (*seq Usize.t*)
                                          {(forall x. Seq.mem x blacks ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x blacks ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x blacks ==> Seq.mem x (objects2 0UL g)) /\
                                                     (G.is_vertex_set blacks) /\
                                                     (G.subset_vertices blacks allocs) /\
                                                     (G.subset_vertices blacks 
                                                         (objects2 0UL g)) /\
                                                     (G.subset_vertices blacks (get_allocated_block_addresses g)) /\
                                                     (forall x. Seq.mem x blacks ==> color_of_object1 x g == black) /\
                                                     (forall x. Seq.mem x (objects2 0UL g) /\
                                                                          isBlackObject1 x g ==> Seq.mem x blacks) /\
                                                     (forall x. Seq.mem x blacks <==> 
                                                         Seq.mem x (objects2 0UL g) /\
                                                         isBlackObject1 x g) /\
                                                     (forall x. Seq.mem x blacks <==> Seq.mem x (get_allocated_block_addresses g) /\ 
                                                        color_of_object1 x g == black)})

val get_gray_block_addresses : (g:heap {Seq.length (objects2 0UL g) > 0}) ->
                                (allocs: seq Usize.t {Seq.equal allocs (get_allocated_block_addresses g) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                   (forall x. Seq.mem x allocs ==> Seq.mem x (objects2 0UL g)) /\
                                                    (G.is_vertex_set allocs) /\
                                                    (G.subset_vertices allocs 
                                                       (objects2 0UL g)) /\
                                                    (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                               (isGrayObject1 x g) \/
                                                                               (isBlackObject1 x g))}) ->
                            Tot (grays: G.vertex_list (*seq Usize.t*)
                                          {(forall x. Seq.mem x grays ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x grays ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x grays ==> Seq.mem x (objects2 0UL g)) /\
                                                     (G.is_vertex_set grays) /\
                                                     (G.subset_vertices grays allocs) /\
                                                     (G.subset_vertices grays 
                                                         (objects2 0UL g)) /\
                                                     (G.subset_vertices grays (get_allocated_block_addresses g)) /\
                                                     (forall x. Seq.mem x grays ==> color_of_object1 x g == gray) /\
                                                     (forall x. Seq.mem x (objects2 0UL g) /\
                                                                          isGrayObject1 x g ==> Seq.mem x grays) /\
                                                     (forall x. Seq.mem x grays <==> 
                                                         Seq.mem x (objects2 0UL g) /\
                                                         isGrayObject1 x g) /\
                                                     (forall x. Seq.mem x grays <==> Seq.mem x (get_allocated_block_addresses g) /\ 
                                                        color_of_object1 x g == gray)})

val get_white_block_addresses : (g:heap {Seq.length (objects2 0UL g) > 0}) ->
                                (allocs: seq Usize.t {Seq.equal allocs (get_allocated_block_addresses g) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                   (forall x. Seq.mem x allocs ==> Seq.mem x (objects2 0UL g)) /\
                                                    (G.is_vertex_set allocs) /\
                                                    (G.subset_vertices allocs 
                                                       (objects2 0UL g)) /\
                                                    (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                               (isGrayObject1 x g) \/
                                                                               (isBlackObject1 x g))}) ->
                            Tot (whites: G.vertex_list (*seq Usize.t*)
                                          {(forall x. Seq.mem x whites ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x whites ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x whites ==> Seq.mem x (objects2 0UL g)) /\
                                                     (G.is_vertex_set whites) /\
                                                     (G.subset_vertices whites allocs) /\
                                                     (G.subset_vertices whites 
                                                         (objects2 0UL g)) /\
                                                     (G.subset_vertices whites (get_allocated_block_addresses g)) /\
                                                     (forall x. Seq.mem x whites ==> color_of_object1 x g == white) /\
                                                     (forall x. Seq.mem x (objects2 0UL g) /\
                                                                          isWhiteObject1 x g ==> Seq.mem x whites) /\
                                                     (forall x. Seq.mem x whites <==> 
                                                         Seq.mem x (objects2 0UL g) /\
                                                         isWhiteObject1 x g) /\
                                                     (forall x. Seq.mem x whites <==> Seq.mem x (get_allocated_block_addresses g) /\ 
                                                        color_of_object1 x g == white)})

#restart-solver 

#restart-solver 

let max_wosize_times_mword_multiple_of_mword (i: Usize.t{(Usize.v i <= Usize.v max_wosize)})
                     :Lemma 
                      (ensures ((Usize.v (Usize.mul i mword) % Usize.v mword == 0))) = ()
                      
let h_index_field_index_mword_multiple_lemma1 (g:heap)
                                             (h_index: hp_addr{Seq.mem h_index (objects2 0UL g)})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()
                                    
let h_index_field_index_all_mword_multiple_lemma1(g:heap)
                                                 (h_index: hp_addr{Seq.mem h_index (objects2 0UL g)})
                                                   
                                : Lemma
                                 
                                  (ensures (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g h_index)) ==> 
                                          (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
 Classical.forall_intro (Classical.move_requires (h_index_field_index_mword_multiple_lemma1 g h_index (getWosize (read_word g h_index))))

let objects_mem_h_index_field_index_all_mword_multiple (g:heap)
                                                       (f':seq hp_addr{(forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g))})
                                        : Lemma
                                          (ensures (forall x. Seq.mem x f' ==>
                                                       ((forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)))) =
Classical.forall_intro (Classical.move_requires (h_index_field_index_all_mword_multiple_lemma1 g))

#push-options "--split_queries always"


#restart-solver 

let hd_address_f_address_lemma7 (x:hp_addr{Usize.v x + Usize.v mword < heap_size})
               : Lemma 
                 (ensures hd_address (f_address x) = x) = ()


let closure_obj_props_object (x: hp_addr{Usize.v x + Usize.v mword < heap_size})
                             (g:heap)
                             (wz: wosize{Usize.v wz <= Usize.v (wosize_of_object1 x g) /\
                                         is_fields_within_limit1 x (wosize_of_object1 x g)}) =
  Usize.v (tag_of_object1 x g) = closure_tag ==> 
          
         (*1*) Usize.v (wosize_of_object1 x g) >= 2 /\
          (let f_addr = f_address x in
          
           assert (Usize.v f_addr >= Usize.v mword);
           assert (Usize.v (tag_of_object1 x g) == closure_tag);
           assert (hd_address (f_address x) == x);
           assert (hd_address f_addr == x);
           assert (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag);
           assert (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag);
           
           assert (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2);
           
           assert (is_fields_within_limit1 (hd_address f_addr) (wosize_of_object1 (hd_address f_addr) g));
           
         let clos_info = closinfo_val_from_closure_object g f_addr in
         (*2*) is_hp_addr (extract_start_env_bits (clos_info))  /\
         (*3*) Usize.v (extract_start_env_bits (clos_info)) + 1 <= Usize.v (wosize_of_object1 x g) /\
         (*4*) Usize.v (extract_start_env_bits (clos_info)) >= 1)

let closure_obj_props (g:heap{Seq.length (objects2 0UL g) > 0})
                      (f:seq Usize.t {(forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                              (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x f ==> 
                                                                 Seq.mem x (get_allocated_block_addresses g)) /\
                                                               (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)))})=
(forall x. Seq.mem x f ==> closure_obj_props_object x g (wosize_of_object1 x g))


let conditions_on_pointer_fields (h_index: hp_addr{Usize.v h_index + Usize.v mword < heap_size}) 
                                       
                                 (g:heap{Seq.length (objects2 0UL g) > 0 (*/\
                                                   (Seq.mem h_index (get_allocated_block_addresses g))*)}) 
                                       
                                 (wz: wosize{Usize.v wz <= Usize.v (wosize_of_object1 h_index g) /\
                                                         is_fields_within_limit1 h_index (wosize_of_object1 h_index g) /\
                                                         closure_obj_props_object h_index g (wosize_of_object1 h_index g)})
                                 (field_start: Usize.t{Usize.v field_start > 0}) =
 
 (forall (i:Usize.t {Usize.v i > Usize.v field_start /\ Usize.v i <= Usize.v wz}).isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                           
                                                          is_hp_addr (read_word g (Usize.add h_index (Usize.mul i mword))) /\
                                                          (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) >= Usize.v mword /\
                                                          Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) < heap_size)
                                                          
                                                          )

#restart-solver 

#restart-solver

#restart-solver

let fields_points_to_blocks_condition (h_index: hp_addr{Usize.v h_index + Usize.v mword < heap_size}) 
                                       
                                 (g:heap{Seq.length (objects2 0UL g) > 0 (*/\
                                                   (Seq.mem h_index (get_allocated_block_addresses g))*)}) 
                                       
                                 (wz: wosize{Usize.v wz <= Usize.v (wosize_of_object1 h_index g) /\
                                                         is_fields_within_limit1 h_index (wosize_of_object1 h_index g) /\
                                                         closure_obj_props_object h_index g (wosize_of_object1 h_index g)})
                                 (field_start: Usize.t{Usize.v field_start > 0 /\
                                                       conditions_on_pointer_fields h_index g wz field_start}) =
  
  (forall (i:Usize.t {Usize.v i > Usize.v field_start /\ Usize.v i <= Usize.v wz}).isPointer (Usize.add h_index (Usize.mul i mword)) g ==> 
                                    Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) == infix_tag ==> 
                                    (UInt.fits (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) - 
                                       (Usize.v (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) * Usize.v mword)) Usize.n) /\
                                   (
                                    let actual_succ = (Usize.sub (read_word g (Usize.add h_index (Usize.mul i mword))) 
                                                  (Usize.mul (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) mword)) in
                                    (Usize.v actual_succ >= Usize.v mword) /\
                                    (is_hp_addr actual_succ) /\
                                    (Usize.v (tag_of_object1 (hd_address actual_succ) g) == closure_tag) /\
                                    (Seq.mem (hd_address actual_succ) (get_allocated_block_addresses g)))) /\
 
 (forall (i:Usize.t {Usize.v i > Usize.v field_start /\ Usize.v i <= Usize.v wz}).isPointer (Usize.add h_index (Usize.mul i mword)) g ==> 
                                    Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) <> infix_tag ==>
  (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g)))
                                                     


let  condition_check_for_different_objects  (h_index: hp_addr{Usize.v h_index + Usize.v mword < heap_size}) 
                                       
                                            (g:heap{Seq.length (objects2 0UL g) > 0 (*/\
                                                   (Seq.mem h_index (get_allocated_block_addresses g))*)}) 
                                       
                                             (wz: wosize{Usize.v wz <= Usize.v (wosize_of_object1 h_index g) /\
                                                         is_fields_within_limit1 h_index (wosize_of_object1 h_index g) /\
                                                         closure_obj_props_object h_index g (wosize_of_object1 h_index g)}) =
  (if  Usize.v (tag_of_object1 h_index g) <> closure_tag then
                                                       (
                                                         conditions_on_pointer_fields h_index g wz 1UL /\
                                                         fields_points_to_blocks_condition h_index g wz 1UL
                                                       )
                                                       else
                                                       (
                                                          
                                                          (let f_addr = f_address h_index in
          
                                                           assert (Usize.v f_addr >= Usize.v mword);
                                                           assert (Usize.v (tag_of_object1 h_index g) == closure_tag);
                                                           assert (hd_address (f_address h_index) == h_index);
                                                           assert (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag);
                                                           assert (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2);
                                                           assert (is_fields_within_limit1 (hd_address f_addr) (wosize_of_object1 (hd_address f_addr) g));
                                                           let clos_info = closinfo_val_from_closure_object g f_addr in
                                                           let start_env = extract_start_env_bits clos_info in
                                                           let start_env_plus_one = Usize.add start_env 1UL in
                                                       
                                                           
                                                           conditions_on_pointer_fields h_index g wz start_env_plus_one /\
                                                           fields_points_to_blocks_condition h_index g wz start_env_plus_one)
                                                         
                                                       ))
val is_fields_contents_within_limit2_lemma : (h_index: hp_addr) ->
                                             (wz: wosize{is_fields_within_limit1 h_index wz}) ->
                                             (wz': wosize{is_fields_within_limit1 h_index wz'})->
                                             (g:heap) ->
                                             (g':heap) ->
                                          
                            Lemma
                            (requires (wz == wz') /\
                                      (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}). 
                                                    
                                                    Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) == 
                                                    Usize.v (read_word g' (Usize.add h_index (Usize.mul i mword)))))
                                                                 
                            (ensures (is_fields_contents_within_limit2 h_index wz g == true <==>
                                      is_fields_contents_within_limit2 h_index wz' g' == true))
                            (decreases (Usize.v wz))

val check_all_block_fields_within_limit2 :(g:heap{Seq.length (objects2 0UL g) > 0})->
                                          (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                              (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x f' ==> 
                                                                 Seq.mem x (get_allocated_block_addresses g)) /\
                                                               (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g x)))})->
                               Tot (b: bool{b == true <==> (forall x. Seq.mem x f' ==> 
                                            is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)})
                                (decreases length f')



#restart-solver

#restart-solver

#push-options "--split_queries always"


#restart-solver 


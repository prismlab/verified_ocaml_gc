/// ---------------------------------------------------------------------------------------------------------------------------------------------------------------
/// GC with closure and infix tag checks
/// ---------------------------------------------------------------------------------------------------------------------------------------------------------------

module Spec.GC_infix_closure_ver3

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
                                                     
(**)

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

//#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries"

#restart-solver 

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

let valid_header_lemma (g: heap {well_formed_heap2 g})
                       (g':heap {well_formed_heap2 g'})
                       (v_id: hp_addr {is_valid_header1 v_id g})
                       (c:color)
               : Lemma
                 (requires (getWosize  (read_word g v_id) == getWosize (read_word g' v_id)) /\
                           (getTag     (read_word g v_id) == getTag    (read_word g' v_id)) /\
                           (c == white \/ c == gray \/ c == black) /\
                           (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                          
                           (heap_remains_same_except_index_v_id v_id g g'))
                 (ensures (is_valid_header1 v_id g')) = 
assert (Seq.mem v_id (get_allocated_block_addresses g));
assert (Seq.mem v_id (get_allocated_block_addresses g'));
assert (is_valid_header1 v_id g');
()


#restart-solver

#restart-solver 

#restart-solver 

let h_index_field_index_mword_multiple_lemma (g:heap{well_formed_heap2 g})
                                             (h_index: hp_addr{is_valid_header1 h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()

let h_index_field_index_mword_multiple_lemma5 (g:heap{Seq.length (objects2 0UL g) > 0})
                                             (h_index: hp_addr{Seq.mem h_index (get_allocated_block_addresses g)})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ 
                                                           is_fields_within_limit1 h_index wz /\
                                                          is_fields_contents_within_limit2 h_index wz g)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) =
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()

let fieldaddress_within_limits_lemma (g:heap{well_formed_heap2 g})
                                     (x:hp_addr{is_valid_header1 x g /\ Seq.mem x (get_allocated_block_addresses g)})
                                     (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))})
                          : Lemma
                            (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                            (ensures (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 h_index_field_index_mword_multiple_lemma g x (getWosize (read_word g x)) i
 

#restart-solver

#restart-solver


 let fieldaddress_within_limits_lemma5 (g:heap{Seq.length (objects2 0UL g) > 0})
                                     (x:hp_addr{Seq.mem x (get_allocated_block_addresses g)})
                                     (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))})
                          : Lemma
                            (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                            (ensures (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 h_index_field_index_mword_multiple_lemma5 g x (getWosize (read_word g x)) i


 
let fieldaddress_within_limits_lemma_x_i_all(g:heap{well_formed_heap2 g})
                                             (x:hp_addr{is_valid_header1 x g /\ Seq.mem x (get_allocated_block_addresses g)})
                           : Lemma
                             (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                             (ensures (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma g x))


let fieldaddress_within_limits_lemma_x_i_all5(g:heap{Seq.length (objects2 0UL g) > 0})
                                             (x:hp_addr{Seq.mem x (get_allocated_block_addresses g)})
                           : Lemma
                             (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                             (ensures (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma5 g x))


let fieldaddress_within_limits_lemma_x_all (g:heap{well_formed_heap2 g})
                                    : Lemma
                                      (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                                      (ensures (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
 Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma_x_i_all g))
 

let fieldaddress_within_limits_lemma_x_all5 (g:heap{Seq.length (objects2 0UL g) > 0})
                                    : Lemma
                                      (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                                      (ensures (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
 Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma_x_i_all5 g))


#restart-solver 

let colorHeader1_alloc_colors_lemma  (v_id:hp_addr)  
                                     (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                                     (c:color)
                         : Lemma
                           (requires (c == white \/ c == gray \/ c == black))
                           (ensures well_formed_heap2 (colorHeader1 v_id g c) /\ is_valid_header1 v_id (colorHeader1 v_id g c) /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses (colorHeader1 v_id g c))) =
 let wz = getWosize (read_word g v_id) in
 let tg = getTag (read_word g v_id) in  
 let h = makeHeader wz c tg in
 let h_index = v_id in

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 assert (g' == colorHeader1 v_id g c);
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.length (objects2 0UL g') > 0);
 get_allocated_block_addresses_lemma g g' v_id c;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 check_all_block_fields_within_limit2_lemma g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
 assert (check_all_block_fields_within_limit2 g' (get_allocated_block_addresses g'));
 fieldaddress_within_limits_lemma_x_all g;
 assert  (forall i x.  Seq.mem x (get_allocated_block_addresses g)  /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
 check_fields_points_to_blocks2_lemma  g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g'); 
 assert  (check_fields_points_to_blocks2 g' (get_allocated_block_addresses g'));
 check_well_formed_closure_objs_lemma g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g'); 
 assert (check_well_formed_closure_objs g' (get_allocated_block_addresses g'));
 assert (well_formed_heap2 g'); 
 valid_header_lemma g g' v_id c;
 assert (is_valid_header1 v_id g');
 ()

type stack = s:seq Usize.t {forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size}

type stack_heap_pair = stack & heap


#reset-options "--z3rlimit 500"

#push-options "--z3rlimit 50"

#restart-solver

#push-options "--split_queries always"

let stack_props_func (g:heap{well_formed_heap2 g})
                     (st: seq Usize.t ) =
     G.is_vertex_set st /\
     (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
     (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
     (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag) /\
     (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g) /\
     (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>  Seq.mem x st)

#restart-solver

#restart-solver 

#reset-options "--z3rlimit 1000"

#restart-solver

let seq_lemmas_empty (g:heap{well_formed_heap2 g})
                     (st: seq Usize.t {stack_props_func g st})
                                    
                     (x: hp_addr{is_valid_header1 x g /\
                                ~(Seq.mem (f_address x) st) /\
                                 (Usize.v (tag_of_object1 x g) <> infix_tag)})
             :Lemma
              (requires (Seq.length st == 0))
              (ensures (let stk' = Seq.create 1 (f_address x) in
                       (Seq.mem (f_address x) (Seq.create 1 (f_address x))) /\
                       (G.is_vertex_set stk') /\
                       (Seq.length stk' == 1) /\
                       (~(exists y. Seq.mem y stk' /\ y <> (f_address x))) /\
                       (forall y. Seq.mem y st \/ y == (f_address x) ==> Seq.mem y stk'))) =
let stk' = Seq.create 1 (f_address x) in
G.is_vertex_set_lemma2 stk';
assert (G.is_vertex_set stk');
assert (Seq.length stk' == 1);
assert (~(exists y. Seq.mem y stk' /\ y <> (f_address x)));
assert (forall y. Seq.mem y st \/ y == (f_address x) ==> Seq.mem y stk');
()

let seq_lemmas_non_empty (g:heap{well_formed_heap2 g})
                     (st: seq Usize.t {stack_props_func g st})
                                    
                     (x: hp_addr{is_valid_header1 x g /\
                                ~(Seq.mem (f_address x) st) /\
                                 (Usize.v (tag_of_object1 x g) <> infix_tag)})
             :Lemma
              (requires ~(Seq.length st == 0))
              (ensures Seq.length st > 0) =
()

let seq_lemmas_non_empty_snoc (g:heap{well_formed_heap2 g})
                     (st: seq Usize.t {stack_props_func g st})
                                    
                     (x: hp_addr{is_valid_header1 x g /\
                                ~(Seq.mem (f_address x) st) /\
                                 (Usize.v (tag_of_object1 x g) <> infix_tag)})
              :Lemma
              (requires (Seq.length st > 0))
              (ensures (let st' = snoc st (f_address x) in
                        (forall y. Seq.mem y st \/ y == (f_address x) ==> Seq.mem y st') /\
                        (Seq.length st' == Seq.length st + 1))) =
lemma_tail_snoc st (f_address x);
lemma_mem_snoc st (f_address x);
()
              
#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver
#restart-solver

let push_to_stack2  (g:heap{well_formed_heap2 g})
                    (st: seq Usize.t {stack_props_func g st})
                                    
                    (x: hp_addr{is_valid_header1 x g /\
                                ~(Seq.mem (f_address x) st) /\
                                 (Usize.v (tag_of_object1 x g) <> infix_tag)
                                })  
                   : Tot (st': stack_heap_pair{well_formed_heap2 (snd st') /\
                                       (forall x. Seq.mem x st ==> Seq.mem x (fst st')) /\
                                  
                                       Seq.mem (f_address x) (fst st') /\

                                       Seq.length (fst st') == Seq.length st + 1 /\
                                  
                                       stack_props_func (snd st') (fst st')}) =
if Seq.length st = 0 then
(
   assert (Usize.v (tag_of_object1 x g) <> infix_tag);
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   colorHeader1_alloc_colors_lemma x g gray;
   assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
   assert (Usize.v (tag_of_object1 x g') <> infix_tag);
   assert (Usize.v (tag_of_object1 (hd_address f_x) g') <> infix_tag);
   assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
   seq_lemmas_empty g st x;
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>  Seq.mem x st);
   assert (Seq.length stk' == 1);
   assert (~(exists y. Seq.mem y stk' /\ y <> f_x));
   assert (forall y. Seq.mem y stk' ==> color_of_object1 (hd_address y) g' == gray);
   assert (forall y. Seq.mem y stk' ==> Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g');
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==>  Seq.mem x st);
   assert (forall y. Seq.mem y stk' ==> Seq.mem y st \/ y == f_x);
   assert (forall y. Seq.mem y st \/ y == f_x ==> Seq.mem y stk');
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g ==> Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g');
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> (Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g) \/
                                                                                                    (hd_address y) == x);
   assert (hd_address f_x == x);
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> Seq.mem y st \/
                                                                                                    (hd_address y) == x);
                                                                                                  
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> Seq.mem y stk');
                                            
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x stk');

   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x stk');
   assert (heap_remains_same_except_index_v_id x g g');
   assert (forall x. Seq.mem x stk' ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
   
   assert (well_formed_heap2 g' /\
                                       (forall x. Seq.mem x st ==> Seq.mem x stk') /\
                                  
                                       Seq.mem (f_address x) stk' /\

                                       Seq.length stk' == Seq.length st + 1 /\
                                  
                                       stack_props_func g' stk');
   (stk', g')
)
    
else
(
  assert (Usize.v (tag_of_object1 x g) <> infix_tag);
  let f_x = f_address x in
  seq_lemmas_non_empty g st x;
  assert (Seq.length st > 0);
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  colorHeader1_alloc_colors_lemma x g gray;
  assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
  assert (Usize.v (tag_of_object1 x g') <> infix_tag);
  assert (Usize.v (tag_of_object1 (hd_address f_x) g') <> infix_tag);
  assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st');
  seq_lemmas_non_empty_snoc g st x;
  assert (forall y. Seq.mem y st \/ y == f_x ==> Seq.mem y st');
  assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g ==> Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g');
  assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> (Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g) \/
                                                                                                    (hd_address y) == x);
  assert (hd_address f_x == x);
  assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> Seq.mem y st \/
                                                                                                    (hd_address y) == x);
  assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g' ==> Seq.mem y st');
  
  assert (forall y. Seq.mem y st' ==> Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g');
  assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x st');
  

  assert (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g);
  assert (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g');
  
  assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x st');
  assert (heap_remains_same_except_index_v_id x g g');
  assert (forall x. Seq.mem x st' ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
  assert (well_formed_heap2 g' /\
                                       (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                  
                                       Seq.mem (f_address x) st' /\

                                       Seq.length st' == Seq.length st + 1 /\
                                  
                                       stack_props_func g' st');
  (st',g')
)            

#reset-options "--z3rlimit 500"


let field_limits_allocated_blocks_lemma (g:heap{well_formed_heap2 g})
                    : Lemma
                      (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)))) = 
 assert (well_formed_heap2 g);
 let objs = objects2 0UL g in
 assert (forall x. Seq.mem x objs ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 assert (G.subset_vertices (get_allocated_block_addresses g) objs);
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 ()

#restart-solver 

let field_contents_within_limits_allocated_blocks_lemma (g:heap{well_formed_heap2 g})
                                            : Lemma
                                              (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) = 
 assert (well_formed_heap2 g);
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g
                                                             );
 ()

let valid_succ_color_lemma (g:heap{well_formed_heap2 g})
                           (succ:hp_addr{is_valid_header1 succ g})
                                         
                  : Lemma
                    (requires True)
                    (ensures (color_of_object1 succ g == white ==> ~(isGrayObject1 succ g) /\
                                                                 ~(isBlackObject1 succ g))) = ()

#restart-solver

let vl_props_func (g:heap{well_formed_heap2 g})
                  (vl: seq Usize.t ) =
  (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
  (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) (*/\
  (forall x. Seq.mem x vl ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag)*) /\
  (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
  (G.is_vertex_set vl) /\
  (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==>  Seq.mem x vl)

let is_alloc_color (g:heap{well_formed_heap2 g})
                   (succ:hp_addr{is_valid_header1 succ g}) =
  (color_of_object1 succ g == white \/
   color_of_object1 succ g == gray \/
   color_of_object1 succ g == black)

let valid_succ_color_lemma1 (g:heap{well_formed_heap2 g})
                            (st: seq Usize.t{stack_props_func g st})
                            
                            (vl: seq Usize.t {vl_props_func g st})
                                                                       
                            (succ:hp_addr{is_valid_header1 succ g}) 
                                    
                   : Lemma
                    (requires (is_alloc_color g succ))  
                    (ensures ~(color_of_object1 succ g == white) ==> Seq.mem (f_address succ) st \/ Seq.mem (f_address succ) vl) = ()

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver

let push_to_stack2_heap_state_lemma  (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{stack_props_func g st})
                                    
                                    (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st)  /\
                                                (Usize.v (tag_of_object1 x g) <> infix_tag)
                                               })  
                                               
                  : Lemma  
                    (ensures (heap_remains_same_except_index_v_id x g (snd (push_to_stack2 g st x)))) = ()

let push_to_stack2_field_size_lemma (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{stack_props_func g st})
                                    
                                    (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st)  /\
                                                (Usize.v (tag_of_object1 x g) <> infix_tag)
                                               })
                                                
                  : Lemma  
                    (ensures (forall (y:Usize.t{Usize.v y < heap_size /\  Usize.v y % Usize.v mword == 0}). (getWosize (read_word g y)) ==
                                               (getWosize (read_word (snd (push_to_stack2 g st x)) y)))) = ()

#restart-solver 

let push_to_stack2_lemma (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{stack_props_func g st})
                                    
                                     (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st) /\ (color_of_object1 x g == white) /\
                                                 (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                })
                     : Lemma
                     (ensures (get_allocated_block_addresses g == get_allocated_block_addresses (snd (push_to_stack2 g st x)))) =
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   get_allocated_block_addresses_lemma g g' x 2UL;
   ()
)
    
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  colorHeader1_alloc_colors_lemma x g gray;
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  get_allocated_block_addresses_lemma g g' x 2UL;
  ()
)

#restart-solver 

#restart-solver

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

let parent_closure_of_infix_object (g:heap{well_formed_heap2 g})
                                   (h_index:hp_addr{is_valid_header1 h_index g})
                                   (i:Usize.t{(Usize.v i < Usize.v (getWosize (read_word g h_index)) + 1 /\ Usize.v i >= 1) /\
                                               isPointer (succ_index_fn g h_index i) g /\
                                               (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag)
                                             }) 
                  : Tot (parent_hdr:hp_addr{is_valid_header1 parent_hdr g /\
                                            (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n) /\
                                            (Usize.v parent_hdr + Usize.v mword < heap_size) /\
                                            (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                                            (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag)}) = 
 assert (well_formed_heap2 g);
 assert (Seq.length (objects2 0UL g) > 0  /\
                                          (check_all_block_fields_within_limit2 g (get_allocated_block_addresses g)) /\
                                          (check_fields_points_to_blocks2 g (get_allocated_block_addresses g)) /\
                                          (check_well_formed_closure_objs g (get_allocated_block_addresses g)));
 assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
 assert  (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g));
 assert (is_fields_points_to_blocks2 h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
 assert (is_fields_points_to_blocks2_post_condition h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
                                          
 assert ((Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) == infix_tag) /\
        (UInt.fits (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) - 
                                                   (Usize.v (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) * Usize.v mword)) Usize.n) /\
          (
                                                       (let actual_succ = (Usize.sub (read_word g (Usize.add h_index (Usize.mul i mword))) 
                                                       (Usize.mul (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) mword)) in
                                                        (Usize.v actual_succ >= Usize.v mword) /\
                                                        (is_hp_addr actual_succ) /\
                                                        (Usize.v (tag_of_object1 (hd_address actual_succ) g) == closure_tag) /\
                                                        (Seq.mem (hd_address actual_succ) (get_allocated_block_addresses g)))));
      
 
 let actual_succ = Usize.sub (read_word g (Usize.add h_index (Usize.mul i mword))) 
                                                       (Usize.mul (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) mword) in
 let hdr_actual_succ = hd_address actual_succ in
 assert (is_valid_header1 hdr_actual_succ g);
 assert (UInt.fits (Usize.v hdr_actual_succ + Usize.v mword) Usize.n);
 assert (Usize.v hdr_actual_succ + Usize.v mword < heap_size);
 assert (Usize.v (tag_of_object1 hdr_actual_succ g) == closure_tag);
 assert (Usize.v (tag_of_object1 hdr_actual_succ g) <> infix_tag);
 hdr_actual_succ

let stack_mem_lemma (g:heap{well_formed_heap2 g})
                    (st: seq Usize.t{stack_props_func g st})
                    (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                     ~(isGrayObject1 hdr_id g)})
          : Lemma
            (ensures (~(Seq.mem (f_address hdr_id) st))) =
 assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
 assert (~(Seq.mem (f_address hdr_id) st));
 ()

#restart-solver

#restart-solver

let darken_helper(g:heap{well_formed_heap2 g})
                 (st: seq Usize.t{stack_props_func g st})
                 (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                  (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
           : Tot (st_hp:stack_heap_pair{well_formed_heap2 (snd st_hp) /\
                                         
                                         stack_props_func (snd st_hp) (fst st_hp) /\
                                               
                                         (forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) == getWosize (read_word (snd st_hp) x)) /\
                                               
                                         (objects2 0UL g ==  objects2 0UL (snd st_hp)) /\ 
                                          
                                         (Seq.length g == Seq.length (snd st_hp)) /\
                                         
                                         (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\
                                         
                                         (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))}) =
 if (color_of_object1 hdr_id g = white) then
(
   assert (is_valid_header hdr_id g);
   valid_succ_color_lemma g hdr_id;
      
   assert (~(isGrayObject1 hdr_id g) /\ ~(isBlackObject1 hdr_id g));
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
   assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
   stack_mem_lemma g st hdr_id;
   assert (Usize.v hdr_id + Usize.v mword < heap_size);
   assert (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n);
   assert (~(Seq.mem (f_address hdr_id) st));
   let st', g' = push_to_stack2 g st hdr_id  in
   push_to_stack2_heap_state_lemma g st hdr_id;
   push_to_stack2_field_size_lemma g st hdr_id;
   assert (G.is_vertex_set st');
          
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');

   assert (color_of_object1 hdr_id g == white);
   push_to_stack2_lemma g st hdr_id;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   (st', g')
)
else
(
  (st,g)
)

#reset-options "--z3rlimit 500"

#restart-solver

let fieldPush_spec_body   (g:heap{well_formed_heap2 g})
                          (st: seq Usize.t{stack_props_func g st})
                          (h_index:hp_addr{is_valid_header1 h_index g})
                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                          (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})                
                     : Pure (stack_heap_pair)
                      (requires True)
                      (ensures fun st_hp -> well_formed_heap2 (snd st_hp) /\
                                         
                                         stack_props_func (snd st_hp) (fst st_hp) /\
                                               
                                         (forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) == getWosize (read_word (snd st_hp) x)) /\
                                               
                                         (objects2 0UL g ==  objects2 0UL (snd st_hp)) /\ 
                                         (is_hp_addr (Usize.(h_index +^ (i *^ mword)))) /\   
                                         
                                         (Seq.length g == Seq.length (snd st_hp)) /\
                                         
                                         (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\
                                         
                                         (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))) =
 assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
       
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);
       
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));
  
  
   if isPointer succ_index g  then
    (
      let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        if color_of_object1 parent_hdr g = white  then
        (
          assert (is_valid_header parent_hdr g);
          valid_succ_color_lemma g parent_hdr;
      
          assert (~(isGrayObject1 parent_hdr g) /\ ~(isBlackObject1 parent_hdr g));
          assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
          assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
          stack_mem_lemma g st parent_hdr;
          assert (Usize.v parent_hdr + Usize.v mword < heap_size);
          assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
          assert (~(Seq.mem (f_address parent_hdr) st));
          let st', g' = push_to_stack2 g st parent_hdr  in
          push_to_stack2_heap_state_lemma g st parent_hdr;
          push_to_stack2_field_size_lemma g st parent_hdr;
          assert (G.is_vertex_set st');
          
          objects2_equal_lemma 0UL g g';
          assert (objects2 0UL g == objects2 0UL g');

          assert (color_of_object1 parent_hdr g == white);
          push_to_stack2_lemma g st parent_hdr;

          assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
          assert ((Seq.length g == Seq.length g'));
     
         (st', g')
      )
      else
      (
          (st,g)
      )
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        if color_of_object1 h_addr_succ g = white  then
        (
          assert (is_valid_header h_addr_succ g);
          valid_succ_color_lemma g h_addr_succ;
      
          assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
          assert (~(Seq.mem (f_address h_addr_succ) st));
          assert (~(Seq.mem succ st));
       
          assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
       
          let st', g' = push_to_stack2 g st  h_addr_succ in
          push_to_stack2_heap_state_lemma g st h_addr_succ;
          push_to_stack2_field_size_lemma g st h_addr_succ;
          assert (G.is_vertex_set st');
          assert (well_formed_heap2 g' /\
              (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                  
              (Seq.mem succ st') /\
                                  
              Seq.length st' == Seq.length st + 1 /\
                                  
              (forall y. Seq.mem y st' ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

              (forall y. Seq.mem y st' ==> Usize.v y % Usize.v mword == 0) /\
                                  
              (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g') /\
                                  
              (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st') /\
                                               
              (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st'));

         assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
         objects2_equal_lemma 0UL g g';
         assert (objects2 0UL g == objects2 0UL g');

         assert (color_of_object1 h_addr_succ g == white);
         push_to_stack2_lemma g st h_addr_succ;

         assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
         assert ((Seq.length g == Seq.length g'));
     
         (st', g')
      )
      else
      (
          (st,g)
      )
    )
   )
  else
   ( 
       (st,g)
   )
 
let fieldPush_spec_body1  (g:heap{well_formed_heap2 g})
                          (st: seq Usize.t{stack_props_func g st})
                          (h_index:hp_addr{is_valid_header1 h_index g})
                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                          (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})                
                     : Pure (stack_heap_pair)
                      (requires True)
                      (ensures fun st_hp -> well_formed_heap2 (snd st_hp) /\
                                         
                                         stack_props_func (snd st_hp) (fst st_hp) /\
                                               
                                         (forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) == getWosize (read_word (snd st_hp) x)) /\
                                               
                                         (objects2 0UL g ==  objects2 0UL (snd st_hp)) (*/\ 
                                         (is_hp_addr (Usize.(h_index +^ (i *^ mword))))*) /\   
                                         
                                         (Seq.length g == Seq.length (snd st_hp)) /\
                                         
                                         (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\
                                         
                                         (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))) = 
                                            
 assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
       
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);
       
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));
  
  
   if isPointer succ_index g  then
    (
      let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        assert (Usize.v parent_hdr + Usize.v mword < heap_size);
        assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
        let st', g' = darken_helper g st parent_hdr in
        (st',g')
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        (st',g')
      )
   )
  else
   ( 
       (st,g)
   )

#restart-solver

let rec fieldPush_spec1   (g:heap{well_formed_heap2 g})
                          (st: seq Usize.t{stack_props_func g st})
                          (h_index:hp_addr{is_valid_header1 h_index g})
                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                          (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
         : Pure (stack_heap_pair)
         (requires True)
         (ensures fun st_hp -> (well_formed_heap2 (snd st_hp)) /\
                            (Seq.length g == Seq.length (snd st_hp)) /\
         
                            (stack_props_func (snd st_hp) (fst st_hp)) /\
                            
                            (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\ 
                            (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                            
                            get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))
                              
         (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       st_hp
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body1 g st h_index wz i in
       fieldPush_spec1 g' st' h_index wz i'
    )                

let slice_mem_helper_lemma (s: seq Usize.t{(Seq.length s) > 0})
                           (s': seq Usize.t{Seq.equal s' (Seq.slice s 0 (Seq.length s - 1))})
                           (x:Usize.t)
                  : Lemma
                    (requires (Seq.mem x s'))
                    (ensures (Seq.mem x s)) =
 Seq.lemma_mem_snoc s' (Seq.index s (Seq.length s - 1))

let slice_mem_lemma (s: seq Usize.t{(Seq.length s) > 0})
                    (s': seq Usize.t{Seq.equal s' (Seq.slice s 0 (Seq.length s - 1))})
                : Lemma 
                  (ensures (forall x. Seq.mem x s' ==> Seq.mem x s))=
Classical.forall_intro (Classical.move_requires (slice_mem_helper_lemma s s'))

let all_mem_st_mem_st__except_v_id_in_stack (v_id:hp_addr)
                                            (st:stack)
                                            (st':stack) = (forall x. Seq.mem x st' /\ x <> v_id ==> Seq.mem x st)

#restart-solver 

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

let extract_start_env_bits' (clos_info:Usize.t) 
               : Tot (strt_env: Usize.t{strt_env == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul})=
 let l1 = Usize.shift_left clos_info 8ul in
 let r1 = Usize.shift_right l1 9ul in
 assert (r1 == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul);
 r1

#restart-solver 

#restart-solver 

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


(*closinfo_val1 gives assertion failure if (is_hp_addr (Usize.add f_addr (Usize.mul 1UL mword))) condition is not added before the result of post condition. Either we can
  add it as a post condition before the result or as a pre-condition. Post condition is preferable, otherwise we need to ensure the precondition before calling the function.*)
let start_env_clos_info (g:heap{well_formed_heap2 g}) 
                        (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                  (is_valid_header1 (hd_address f_addr) g) /\
                                  (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                                  (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2)}) 
                 : Tot (start_env:hp_addr{(Usize.v start_env >= Usize.v (extract_start_env_bits ((*closinfo_val1*) closinfo_val_from_closure_object g f_addr))) /\
                                          (Usize.v start_env + 1 <= Usize.v (wosize_of_object1 (hd_address f_addr) g)) /\
                                           Usize.v start_env >= 1}) =
  let clos_info = (*closinfo_val1*) closinfo_val_from_closure_object g f_addr in
  let start_env = extract_start_env_bits clos_info in
  (*assert ((is_hp_addr (Usize.add f_addr (Usize.mul 1UL mword))) /\
           (clos_info == read_word g (Usize.add f_addr (Usize.mul 1UL mword))));
  assert (start_env == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul);
  assert (start_env == Usize.shift_right (Usize.shift_left (read_word g (Usize.add f_addr (Usize.mul 1UL mword))) 8ul) 9ul);
  assert (is_hp_addr start_env);
  let hdr_f_addr = hd_address f_addr in
  assert (is_valid_header1 hdr_f_addr g);
  let wz = wosize_of_object1 hdr_f_addr g in
  assert (Usize.v start_env <= Usize.v wz);
  assert (Usize.v start_env >= Usize.v (extract_start_env_bits ((*closinfo_val1*) closinfo_val_from_closure_object g f_addr)));
  assert (Usize.v start_env >= 1);*)
  start_env

#restart-solver

#restart-solver 

#restart-solver

let colorHeader5  (v_id:hp_addr)  
                  (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                  (c:color)
             : Tot (g': heap{g' == colorHeader1 v_id g c}) = 
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
 assert (Seq.length (objects2 0UL g) > 0);

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 assert (g' == colorHeader1 v_id g c);
 
 g'

#reset-options "--z3rlimit 1000"

#restart-solver

let colorHeader5_lemma (v_id:hp_addr)  
                  (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                  (c:color)
          : Lemma
            (ensures (Seq.equal (colorHeader5 v_id g c) (colorHeader1 v_id g c))) = ()

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

let start_env_clos_info_helper_lemma (g:heap{well_formed_heap2 g}) 
                              (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                  (is_valid_header1 (hd_address f_addr) g) /\
                                  (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                                  (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2)}) 
                   : Lemma
                     (ensures ~(Seq.mem (Usize.add f_addr (Usize.mul 1UL mword)) (objects2 0UL g))) =
 
  let s = objects2 0UL g in
  assert (forall x y. Seq.mem x s /\ (Usize.v y >= Usize.v x + Usize.v mword) /\ 
                                                   (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1)) ==>
                                                   ~(Seq.mem y s));
                                                   
  
  let next_f_addr = Usize.add f_addr (Usize.mul 1UL mword) in
  let hdr_f_addr = hd_address f_addr in
  assert (Usize.v (wosize_of_object1 hdr_f_addr g) >= 2);
  let next_next_hdr_f_addr = Usize.add hdr_f_addr(Usize.mul 2UL mword) in
  assert (next_f_addr == next_next_hdr_f_addr);
  assert (Seq.mem hdr_f_addr s);
  let wz = getWosize (read_word g hdr_f_addr) in
  assert (Usize.v wz >= 2);
  let sum =  Usize.v hdr_f_addr + (((Usize.v wz  + 1) * Usize.v mword) - 1) in
  assert (Usize.v next_next_hdr_f_addr <= sum);
  (*assert (Usize.v next_next_hdr_f_addr >= Usize.v hdr_f_addr + Usize.v mword);
  assert (~(Seq.mem next_next_hdr_f_addr s));
  assert (~(Seq.mem next_f_addr s));*)
  ()

#restart-solver 

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver


let start_env_clos_info_helper_lemma1 (g:heap{well_formed_heap2 g}) 
                              (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                  (is_valid_header1 (hd_address f_addr) g) /\
                                  (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                                  (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2)}) 
                              (v_id:hp_addr{is_valid_header1 v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})

                              (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                    : Lemma
                      (requires is_hp_addr (Usize.add f_addr (Usize.mul 1UL mword)))
                      (ensures read_word g (Usize.add f_addr (Usize.mul 1UL mword)) == read_word (colorHeader1 v_id g c) (Usize.add f_addr (Usize.mul 1UL mword))) = 
 let next_f_addr = Usize.add f_addr (Usize.mul 1UL mword) in
 let hdr_f_addr = hd_address f_addr in
 assert (Usize.v (wosize_of_object1 hdr_f_addr g) >= 2);
 let next_next_hdr_f_addr = Usize.add hdr_f_addr(Usize.mul 2UL mword) in
 assert (next_f_addr == next_next_hdr_f_addr);
 assert (is_hp_addr next_f_addr);
 assert (is_hp_addr next_next_hdr_f_addr);

 //lemma_len_slice g (Usize.v (Usize.add next_f_addr (Usize.mul 1UL mword))) ((Usize.v (Usize.add next_f_addr (Usize.mul 1UL mword))) + (Usize.v mword));
 let r = read_word g next_f_addr in
 let g' = colorHeader1 v_id g c in
 let r' = read_word g' next_f_addr in
 start_env_clos_info_helper_lemma g f_addr;
 assert (~(Seq.mem next_f_addr (objects2 0UL g)));
 assert (heap_remains_same_except_index_v_id v_id g g');
 assert (v_id <> next_f_addr);
 assert (r == r');
 ()

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

#restart-solver

let start_env_clos_info_lemma (g:heap{well_formed_heap2 g}) 
                              (f_addr:hp_addr{Usize.v f_addr >= Usize.v mword /\
                                  (is_valid_header1 (hd_address f_addr) g) /\
                                  (Usize.v (tag_of_object1 (hd_address f_addr) g) == closure_tag) /\
                                  (Usize.v (wosize_of_object1 (hd_address f_addr) g) >= 2)}) 
                              (v_id:hp_addr{is_valid_header1 v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})

                              (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                      : Lemma
                        (requires well_formed_heap2 (colorHeader1 v_id g c))
                        (ensures (start_env_clos_info g f_addr == start_env_clos_info (colorHeader1 v_id g c) f_addr)) =
  let clos_info = closinfo_val_from_closure_object g f_addr in
  let start_env = extract_start_env_bits clos_info in
  (*assert ((is_hp_addr (Usize.add f_addr (Usize.mul 1UL mword))) /\
           (clos_info == read_word g (Usize.add f_addr (Usize.mul 1UL mword))));*)
  assert (start_env == Usize.shift_right (Usize.shift_left clos_info 8ul) 9ul);
  assert (start_env == Usize.shift_right (Usize.shift_left (read_word g (Usize.add f_addr (Usize.mul 1UL mword))) 8ul) 9ul);
  assert (is_hp_addr start_env);
  let hdr_f_addr = hd_address f_addr in
  assert (is_valid_header hdr_f_addr g);
  let wz = wosize_of_object1 hdr_f_addr g in
  assert (Usize.v start_env <= Usize.v wz);
  assert (Usize.v start_env >= Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g f_addr)));
  assert (Usize.v start_env >= 1);
  let g' = colorHeader5 v_id g c in
  colorHeader5_lemma v_id g c;
  let clos_info' = closinfo_val_from_closure_object g' f_addr in
  assert (Usize.v (tag_of_object1 (hd_address f_addr) g') == Usize.v (tag_of_object1 (hd_address f_addr) g));
  assert (Usize.v (wosize_of_object1 (hd_address f_addr) g) == Usize.v (wosize_of_object1 (hd_address f_addr) g'));
  lemma_len_slice g (Usize.v (Usize.add f_addr (Usize.mul 1UL mword))) ((Usize.v (Usize.add f_addr (Usize.mul 1UL mword))) + (Usize.v mword));
  lemma_len_slice g' (Usize.v (Usize.add f_addr (Usize.mul 1UL mword))) ((Usize.v (Usize.add f_addr (Usize.mul 1UL mword))) + (Usize.v mword));
  start_env_clos_info_helper_lemma1  g f_addr v_id c;
  assert (read_word g (Usize.add f_addr (Usize.mul 1UL mword)) == read_word g' (Usize.add f_addr (Usize.mul 1UL mword)));
  //closinfo_val1_lemma g f_addr v_id c;
  closinfo_val_from_closure_object_lemma g f_addr g';
  assert (clos_info == clos_info');
  let start_env' = extract_start_env_bits clos_info' in
  assert (start_env == start_env');
  ()

#restart-solver

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

let non_empty_set_lemma (g:heap{well_formed_heap2 g})
                        (st: seq Usize.t {stack_props_func g st})
     : Lemma
       (requires (~(G.is_emptySet st)))
       (ensures (Seq.length st > 0) /\
                (Seq.mem (Seq.index st (Seq.length st - 1)) st) /\
                Seq.equal (Seq.slice st 0 (Seq.length st - 1)) (Seq.slice st 0 (Seq.length st - 1)) /\
                Seq.equal st (Seq.slice st 0 (Seq.length st)) /\
                (forall x. mem x st <==> x == Seq.index st (Seq.length st - 1) \/ Seq.mem x (slice st 0 (Seq.length st - 1)))) =
assert (Seq.length st > 0);
assert (0 < Seq.length st);
assert (Seq.length st <= Seq.length st);
Seq.lemma_slice_snoc st 0 (Seq.length st);
assert (forall x. mem x (slice st 0 (Seq.length st)) <==> (x = index st ((Seq.length st) - 1) || mem x (slice st 0 ((Seq.length st) - 1))));
assert (forall x. mem x st <==> x == Seq.index st (Seq.length st - 1) \/ Seq.mem x (slice st 0 (Seq.length st - 1)));
()
       
#restart-solver


#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver


let mark5_body (g:heap{well_formed_heap2 g}) 
               (st: seq Usize.t {stack_props_func g st})
                                    
           : Pure (stack_heap_pair)
             (requires (~(G.is_emptySet st)))
             (ensures (fun st_hp -> (Seq.length g == Seq.length (snd st_hp)) /\
                                 well_formed_heap2 (snd st_hp) /\
                                 stack_props_func (snd st_hp) (fst st_hp) /\
                                 (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                                 (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp)))) = 

 assert (~(G.is_emptySet st));
 non_empty_set_lemma g st;
 let v_id = Seq.index st (Seq.length st - 1) in
 let s = Seq.slice st 0 (Seq.length st - 1) in
 assert (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (Usize.v v_id  >= Usize.v mword);
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
   
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Seq.mem x st);
 G.is_vertex_set_lemma3 st;
 assert (forall x. Seq.mem x s ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 let g' = colorHeader5 h_v_id g black in
 colorHeader5_lemma h_v_id g black;
 assert (g' == colorHeader1 h_v_id g black);
 assert (color_of_object1 h_v_id g' == black);
 colorHeader1_alloc_colors_lemma h_v_id g black;
   
 let f = objects2 0UL g in
 let f' = objects2 0UL g' in
 assert (f == f');
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 Seq.lemma_mem_snoc s v_id;
 assert (forall x. Seq.mem x st <==> (x == v_id) \/ Seq.mem x s);
 assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem (hd_address x) (objects2 0UL g) /\
                                                        isGrayObject1 (hd_address x) g);
 
 assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
 assert (color_of_object1 h_v_id g' == 3UL);
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (forall x. Seq.mem x s <==> Seq.mem (hd_address x) (objects2 0UL g') /\
                                                        isGrayObject1 (hd_address x) g');
 
 let wz = wosize_of_object1 h_v_id g' in
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));
 assert (Usize.v wz == Usize.v (getWosize (read_word g' h_v_id)));
 assert (well_formed_heap2 g');
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                             Seq.mem x s);
 assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size);
 assert (Usize.v h_v_id % Usize.v mword == 0);
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));

 assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
 
 let tg = tag_of_object1 h_v_id g' in
 assert (Usize.v tg <> infix_tag);
 assert (check_well_formed_closure_objs g (get_allocated_block_addresses g));
 assert (stack_props_func g st);
 assert (Seq.mem v_id st);
 assert (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g);
 assert (h_v_id == hd_address v_id);

 if (Usize.v tg < no_scan_tag) then 
 (
   if (Usize.v tg = closure_tag) then
   (
     assert (Usize.v wz >= 2);
     assert (Usize.v v_id >= Usize.v mword);
     assert (is_valid_header1 h_v_id g);
     assert (is_valid_header (hd_address v_id) g);
    
     let start_env = start_env_clos_info g' v_id in

     assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address v_id) g')) /\
             Usize.v start_env >= 1);

     let start_env_plus_one = Usize.add start_env 1UL in
     let st1, g1 = fieldPush_spec1 g' s h_v_id wz (start_env_plus_one) in
     
     (st1,g1)
   )
   else
   (
     let st1, g1 = fieldPush_spec1 g' s h_v_id wz 1UL in
     assert (G.is_vertex_set st1);
     assert (Seq.length g == Seq.length g1);
     
     (st1,g1)
   )
   
 )
  else
  (
    (s,g')
  )

let darken_wrapper (g:heap{well_formed_heap2 g})
                       (st: seq Usize.t{stack_props_func g st})
                       (h_index:hp_addr{is_valid_header1 h_index g})
                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                          
         : Pure (stack_heap_pair)
         (requires Usize.v (tag_of_object1 h_index g) < no_scan_tag)
         (ensures fun st_hp -> (well_formed_heap2 (snd st_hp)) /\
                            (Seq.length g == Seq.length (snd st_hp)) /\
         
                            (stack_props_func (snd st_hp) (fst st_hp)) /\
                            
                            (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\ 
                            (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                            
                            get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp)) =
 if (Usize.v (tag_of_object1 h_index g) = closure_tag) then
   (
     assert (Usize.v wz >= 2);

     let v_id = f_address h_index in
     
     let start_env = start_env_clos_info g v_id in

     assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address v_id) g)) /\
             Usize.v start_env >= 1);
     let start_env_plus_one = Usize.add start_env 1UL in
     let st1, g1 = fieldPush_spec1 g st h_index wz start_env_plus_one in
     
     (st1,g1)
   )
   else
   (
     let st1, g1 = fieldPush_spec1 g st h_index wz 1UL in
     assert (G.is_vertex_set st1);
     assert (Seq.length g == Seq.length g1);
     assert (well_formed_heap2 g1);
     assert (forall x. Seq.mem x st1 ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
     assert (forall x. Seq.mem x st1 ==> is_valid_header (hd_address x) g1);
     assert (forall x. Seq.mem x st1 ==> Usize.v x % Usize.v mword == 0);
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isGrayObject1 (hd_address x) g1 <==>
                                                Seq.mem x st1);
     assert (forall x. Seq.mem x st ==> Seq.mem x st1);
  
     assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
     assert (objects2 0UL g == objects2 0UL g1);
     assert (objects2 0UL g == objects2 0UL g1);
     assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
     (st1,g1)
   )

let mark5_body1 (g:heap{well_formed_heap2 g}) 
               (st: seq Usize.t {stack_props_func g st})
                                    
           : Pure (stack_heap_pair)
             (requires (~(G.is_emptySet st)))
             (ensures (fun st_hp -> (Seq.length g == Seq.length (snd st_hp)) /\
                                 well_formed_heap2 (snd st_hp) /\
                                 stack_props_func (snd st_hp) (fst st_hp) /\
                                 (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                                 (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))))=
 assert (~(G.is_emptySet st));
 non_empty_set_lemma g st;
 let v_id = Seq.index st (Seq.length st - 1) in
 let s = Seq.slice st 0 (Seq.length st - 1) in
 assert (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (Usize.v v_id  >= Usize.v mword);
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
   
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Seq.mem x st);
 G.is_vertex_set_lemma3 st;
 assert (forall x. Seq.mem x s ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 let g' = colorHeader5 h_v_id g black in
 colorHeader5_lemma h_v_id g black;
 assert (g' == colorHeader1 h_v_id g black);
 assert (color_of_object1 h_v_id g' == black);
 colorHeader1_alloc_colors_lemma h_v_id g black;
   
 let f = objects2 0UL g in
 let f' = objects2 0UL g' in
 assert (f == f');
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 Seq.lemma_mem_snoc s v_id;
 assert (forall x. Seq.mem x st <==> (x == v_id) \/ Seq.mem x s);
 assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem (hd_address x) (objects2 0UL g) /\
                                                        isGrayObject1 (hd_address x) g);
 
 assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
 assert (color_of_object1 h_v_id g' == 3UL);
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (forall x. Seq.mem x s <==> Seq.mem (hd_address x) (objects2 0UL g') /\
                                                        isGrayObject1 (hd_address x) g');
 
 let wz = wosize_of_object1 h_v_id g' in
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));
 assert (Usize.v wz == Usize.v (getWosize (read_word g' h_v_id)));
 assert (well_formed_heap2 g');
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                             Seq.mem x s);
 assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size);
 assert (Usize.v h_v_id % Usize.v mword == 0);
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));

 assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
 
 let tg = tag_of_object1 h_v_id g' in
 assert (Usize.v tg <> infix_tag);
 assert (check_well_formed_closure_objs g (get_allocated_block_addresses g));
 assert (stack_props_func g st);
 assert (Seq.mem v_id st);
 assert (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g);
 assert (h_v_id == hd_address v_id);

 if (Usize.v tg < no_scan_tag) then 
 (
    let st1, g1 = darken_wrapper g' s h_v_id wz in
     
     (st1,g1)
 )
 else
 (
   (s,g')
 )

#reset-options "--z3rlimit 500"

#restart-solver 

let mark5_body1_darken_wrapper_lemma (g:heap{well_formed_heap2 g}) 
                                     (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0})
                                     (v_id:hp_addr{(v_id == Seq.index st (Seq.length st - 1)) /\ (is_valid_header1 (hd_address v_id) g)})
                               
                                     (g': heap{g' == colorHeader1 (hd_address v_id) g black /\
                                               well_formed_heap2 g'})
                                     (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                                     (wz:wosize{wz == wosize_of_object1 (hd_address v_id) g})   
                   : Lemma
                   (requires (stack_props_func g' s) /\
                             (Usize.v v_id >= Usize.v mword /\ Usize.v v_id < heap_size) /\
                              (is_valid_header1 (hd_address v_id) g') /\
                              (Usize.v (tag_of_object1 (hd_address v_id) g') < no_scan_tag))
                                                  
                   (ensures (fst (mark5_body1 g st) == fst (darken_wrapper g' s (hd_address v_id) wz)) /\
                            (snd (mark5_body1 g st) == snd (darken_wrapper g' s (hd_address v_id) wz))) = ()

let mark5_body1_darken_wrapper_lemma1 (g:heap{well_formed_heap2 g}) 
                                     (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0})
                                     (v_id:hp_addr{(v_id == Seq.index st (Seq.length st - 1)) /\ (is_valid_header (hd_address v_id) g)})
                               
                                     (g': heap{g' == colorHeader1 (hd_address v_id) g black /\
                                               well_formed_heap2 g'})
                                     (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                                     (wz:wosize{wz == wosize_of_object1 (hd_address v_id) g})   
                   : Lemma
                   (requires (stack_props_func g' s) /\
                             (Usize.v v_id >= Usize.v mword /\ Usize.v v_id < heap_size) /\
                              (is_valid_header (hd_address v_id) g') /\
                              (Usize.v (tag_of_object1 (hd_address v_id) g') >=  no_scan_tag))
                                                  
                   (ensures (fst (mark5_body1 g st) == s) /\
                            (snd (mark5_body1 g st) == g')) = ()

#restart-solver 

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


let stack_slice_only_has_gray_color_lemma (g:heap{well_formed_heap2 g}) 
                                          (st: seq Usize.t {stack_props_func g st /\
                                                             Seq.length st > 0
                                                            })
                                          (v_id:hp_addr{v_id == Seq.index st (Seq.length st - 1) /\
                                                        Usize.v v_id >= Usize.v mword /\
                                                        is_valid_header1 (hd_address v_id) g})
                                          (c:color{c == 3UL})
                               : Lemma
                                 (requires True)
                                 
                                 (ensures (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g c)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g c)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)))) = 
 non_empty_set_lemma g st;
 
 let s = Seq.slice st 0 (Seq.length st - 1) in
 assert (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (Usize.v v_id  >= Usize.v mword);
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
   
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 G.is_vertex_set_lemma3 st;
 assert (forall x. Seq.mem x s ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 let g' = colorHeader5 h_v_id g black in
 colorHeader5_lemma h_v_id g black;
 assert (g' == colorHeader1 h_v_id g black);
 assert (color_of_object1 h_v_id g' == black);
 colorHeader1_alloc_colors_lemma h_v_id g black;
   
 let f = objects2 0UL g in
 let f' = objects2 0UL g' in
 assert (f == f');
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 Seq.lemma_mem_snoc s v_id;
 assert (forall x. Seq.mem x st <==> (x == v_id) \/ Seq.mem x s);
 assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem (hd_address x) (objects2 0UL g) /\
                                                        isGrayObject1 (hd_address x) g);
 
 assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
 assert (color_of_object1 h_v_id g' == 3UL);
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (forall x. Seq.mem x s <==> Seq.mem (hd_address x) (objects2 0UL g') /\
                                                        isGrayObject1 (hd_address x) g');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g c)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g c)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)));
 ()


#reset-options "--z3rlimit 500"

let colorHeader1_subset_lemma  (v_id:hp_addr)  
                               (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                        
              : Lemma
                (ensures (forall x. Seq.mem x (get_black_block_addresses g (get_allocated_block_addresses g)) ==>
                                    Seq.mem x (get_black_block_addresses (colorHeader1 v_id g black) 
                                                 (get_allocated_block_addresses (colorHeader1 v_id g black)))) /\
                          G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                            (get_black_block_addresses (colorHeader1 v_id g black) 
                                                 (get_allocated_block_addresses (colorHeader1 v_id g black)))) = 
let g' = colorHeader1 v_id g black in
let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
assert (heap_remains_same_except_index_v_id v_id g g');
assert (color_of_object1 v_id g' == black);
assert (forall x. Seq.mem x blacks /\ x <> v_id ==> Seq.mem x blacks');
assert (forall x. Seq.mem x blacks ==> Seq.mem x blacks');
assert (G.subset_vertices blacks blacks');
()

#restart-solver

let colorHeader1_black_nodes_lemma (g:heap{well_formed_heap2 g}) 
                                   (y:hp_addr{Usize.v y >= 0 /\ Usize.v y < heap_size /\
                                             is_valid_header1 y g /\
                                             color_of_object1 y g <> black
                                          })
           : Lemma
             (ensures Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (colorHeader1 y g black) (get_allocated_block_addresses (colorHeader1 y g black)))) = 
let g' = colorHeader1 y g black in
let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
colorHeader1_alloc_colors_lemma y g black;
colorHeader1_subset_lemma y g;
assert (G.subset_vertices blacks blacks');
 assert (is_valid_header1 y g');
 assert (Seq.mem y blacks');
 assert (~(Seq.mem y blacks));
 assert (Seq.length blacks <= Seq.length blacks');
 if Seq.length blacks < Seq.length blacks' then ()
 else
 (
   assert (Seq.length blacks == Seq.length blacks');
   G.subset_of_each_other blacks blacks';
   assert (G.subset_vertices blacks' blacks);
   assert (forall x. Seq.mem x blacks' ==> Seq.mem x blacks);
   ()
 )

let colorHeader1_color_Lemma (v_id:hp_addr)  
                             (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g /\ color_of_object1 v_id g == white}) 
                             (c:color{c == 2UL})
              : Lemma
                (color_of_object1 v_id (colorHeader1 v_id g c) == 2UL /\
                 color_of_object1 v_id (colorHeader1 v_id g c) <> black /\
                 color_of_object1 v_id g <> black) = ()

#restart-solver 

let push_to_stack2_lemma_black_nodes1 (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{stack_props_func g st})
                                    
                                    (x: hp_addr{is_valid_header1 x g /\
                                                                ~(Seq.mem (f_address x) st) /\ 
                                                                (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                                color_of_object1 x g == white /\
                                                                (*Introduction of the below condition was needed to typecheck*)
                                                                is_fields_within_limit1 x (getWosize (read_word g x))}) 
                                                               
                                                              
                   : Lemma 
                     (ensures G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x))))) = 
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   colorHeader1_alloc_colors_lemma x g gray;
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   colorHeader1_color_Lemma x g 2UL;

   get_allocated_block_addresses_lemma g g' x 2UL;

   assert ((get_allocated_block_addresses g) == (get_allocated_block_addresses g'));
    
   let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
   let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
   G.is_vertex_set_lemma2 stk';
    
   assert (color_of_object1 x g == white);
   assert (color_of_object1 x g <> black);
   assert (color_of_object1 x g' <> black);
   assert (heap_remains_same_except_index_v_id x g g');
   assert (forall y. Seq.mem y blacks ==> Seq.mem y blacks');
   assert (G.subset_vertices blacks blacks');
   assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x)))));
   ()
)
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  colorHeader1_alloc_colors_lemma x g gray;
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  colorHeader1_color_Lemma x g 2UL;

  get_allocated_block_addresses_lemma g g' x 2UL;

  assert ((get_allocated_block_addresses g) == (get_allocated_block_addresses g'));
    
  let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
  let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
  assert (color_of_object1 x g == white);
  assert (color_of_object1 x g <> black);
  assert (color_of_object1 x g' <> black);
  assert (heap_remains_same_except_index_v_id x g g');
  assert (forall y. Seq.mem y blacks ==> Seq.mem y blacks');
  assert (G.subset_vertices blacks blacks');
  assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x)))));
  ()
)

let darken_helper_black_nodes_lemma(g:heap{well_formed_heap2 g})
                                   (st: seq Usize.t{stack_props_func g st})
                                   (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                                   (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
           : Lemma
             (ensures (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                   (get_black_block_addresses (snd (darken_helper g st hdr_id)) 
                                                              (get_allocated_block_addresses (snd (darken_helper g st hdr_id)))))) =
if (color_of_object1 hdr_id g = white) then
(
   assert (is_valid_header hdr_id g);
   valid_succ_color_lemma g hdr_id;
      
   assert (~(isGrayObject1 hdr_id g) /\ ~(isBlackObject1 hdr_id g));
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
   assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
   stack_mem_lemma g st hdr_id;
   assert (Usize.v hdr_id + Usize.v mword < heap_size);
   assert (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n);
   assert (~(Seq.mem (f_address hdr_id) st));
   let st', g' = push_to_stack2 g st hdr_id  in
   push_to_stack2_heap_state_lemma g st hdr_id;
   push_to_stack2_field_size_lemma g st hdr_id;
   push_to_stack2_lemma_black_nodes1 g st hdr_id;
   assert (G.is_vertex_set st');
          
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');

   assert (color_of_object1 hdr_id g == white);
   push_to_stack2_lemma g st hdr_id;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   ()
)
else
(
   ()
)

#restart-solver 

#restart-solver

//#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#reset-options "--z3rlimit 1000"
#restart-solver

let fieldPush_spec_body1_black_nodes_lemma (g:heap{well_formed_heap2 g})
                                          (st: seq Usize.t{stack_props_func g st})
                                          (h_index:hp_addr{is_valid_header1 h_index g})
                                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                          (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                          
                                          
                                          
                        : Lemma
                          (requires G.is_vertex_set (get_black_block_addresses g (get_allocated_block_addresses g)) /\
                                    G.is_vertex_set (get_black_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)))))
                          (ensures G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                   (get_black_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i))))) =
  
assert (well_formed_heap2 g);
       
field_limits_allocated_blocks_lemma g;
field_contents_within_limits_allocated_blocks_lemma g;
assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
let succ_index = Usize.add h_index (Usize.mul i mword) in
       
assert (Usize.v succ_index < heap_size);
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert (Usize.v succ_index % Usize.v mword == 0);
assert (is_hp_addr succ_index);
let succ = read_word g succ_index in
assert (succ == read_word g succ_index);
assert (Seq.mem h_index (objects2 0UL g));
 if isPointer succ_index g  then
 (
   let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        assert (Usize.v parent_hdr + Usize.v mword < heap_size);
        assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
        let st', g' = darken_helper g st parent_hdr in
        darken_helper_black_nodes_lemma g st parent_hdr;
        ()
      )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        darken_helper_black_nodes_lemma g st h_addr_succ;
        ()
      )
 )
 else
 (
   ()
 )

#restart-solver 

let rec fieldPush_spec1_black_nodes_lemma (g:heap{well_formed_heap2 g})
                                          (st: seq Usize.t{stack_props_func g st})
                         
                                          (h_index:hp_addr{is_valid_header1 h_index g})
                                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                          (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                              
                                           
                                           
                        : Lemma
                          (ensures (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (fieldPush_spec1 g st h_index wz i)) 
                                                                               (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i))))))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i >= 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st', g' = fieldPush_spec_body1 g st h_index wz i in
       let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
       assert (G.is_vertex_set blacks);
       let blacks' = get_black_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i))) in
       assert (G.is_vertex_set blacks');
       assert (G.is_vertex_set (get_black_block_addresses g (get_allocated_block_addresses g)) /\
                                    G.is_vertex_set (get_black_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)))));
       fieldPush_spec_body1_black_nodes_lemma g st h_index wz i;
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
                                         Seq.mem x st'));
       
       let st'', g'' = fieldPush_spec1 g' st' h_index wz i' in
       fieldPush_spec1_black_nodes_lemma g' st' h_index wz i';
       assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                 (get_black_block_addresses g'' (get_allocated_block_addresses g'')));
       ()
    )

#restart-solver

#restart-solver

let color_pre_condition (g:heap{well_formed_heap2 g}) 
                        (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0}) = 
 (forall x. Seq.mem (hd_address x) (objects2 0UL (colorHeader5 (hd_address (Seq.index st (Seq.length st - 1))) g black)) /\ 
           isGrayObject1 (hd_address x) (colorHeader5 (hd_address (Seq.index st (Seq.length st - 1))) g black) <==>
           Seq.mem x (Seq.slice st 0 (Seq.length st - 1)))

let mark5_body_black_nodes_lemma_post_condition (g:heap{well_formed_heap2 g}) 
                                                (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0}) =
 Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st))))


let is_black_subset (g:heap{well_formed_heap2 g})
                    (g':heap{well_formed_heap2 g'}) =
 G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                   (get_black_block_addresses g' (get_allocated_block_addresses g'))

let is_black_subset_lemma (g:heap{well_formed_heap2 g})
                          (g':heap{well_formed_heap2 g'}) 
              : Lemma 
                (requires is_black_subset g g')
                (ensures Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <=
                            Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g'))) =
 ()

let black_objects_length (g:heap{well_formed_heap2 g})
                         (g':heap{well_formed_heap2 g'}) =
  Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
           Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g'))

let black_objects_length1 (g:heap{well_formed_heap2 g})
                         (g':heap{well_formed_heap2 g'}) =
  Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <=
           Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g'))

let is_black_subset_lemma_trans (g:heap{well_formed_heap2 g})
                                (g':heap{well_formed_heap2 g'}) 
                                (g1:heap{well_formed_heap2 g1}) 
               : Lemma
                 (requires (black_objects_length g g') /\ (black_objects_length1 g' g1))
                 (ensures (black_objects_length g g1)) = 
 ()

let seq_slice_lemma (#a:eqtype)
                    (st: seq a{Seq.length st > 0})
              : Lemma
                (ensures  (let s = Seq.slice st 0 (Seq.length st - 1) in
                           Seq.equal s (Seq.slice st 0 (Seq.length st - 1)))) = ()
 
let seq_index_lemma (#a:eqtype)
                    (st: seq a{Seq.length st > 0})
              : Lemma
                (ensures  (let s = Seq.index st (Seq.length st - 1) in
                           s == (Seq.index st (Seq.length st - 1)))) = ()


let seq_slice_transitive_lemma (#a:eqtype)
                               (st: seq a{Seq.length st > 0})
                               (s: seq a)
                               (xs: seq a)
                     : Lemma   
                       (requires (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)) /\
                                  Seq.equal xs (Seq.slice st 0 (Seq.length st - 1))))
                       (ensures (Seq.equal s xs) /\
                                (s == xs)) = () 

let seq_index_lemma1 (#a:eqtype)
                    (st: seq a{Seq.length st > 0})
              : Lemma
                (ensures  (let s = Seq.index st (Seq.length st - 1) in
                          (Seq.mem s st))) = ()
#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver



let test19  (v_id:hp_addr)  
            (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
            (c:color) = 
 let g1 = colorHeader5 v_id g c in
 admit()

#push-options "--split_queries always"

#restart-solver

let mark5_body_black_nodes_lemma (g:heap{well_formed_heap2 g}) 
                                 (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0})
                                    
    : Lemma
      (requires color_pre_condition g st)
                                    
      (ensures mark5_body_black_nodes_lemma_post_condition g st) = 
assert (~(G.is_emptySet st));
 non_empty_set_lemma g st;
 let v_id = Seq.index st (Seq.length st - 1) in
 let s = Seq.slice st 0 (Seq.length st - 1) in
 assert (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (Usize.v v_id  >= Usize.v mword);
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
   
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Seq.mem x st);
 G.is_vertex_set_lemma3 st;
 assert (forall x. Seq.mem x s ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 let g' = colorHeader5 h_v_id g black in
 colorHeader5_lemma h_v_id g black;
 assert (g' == colorHeader1 h_v_id g black);
 assert (color_of_object1 h_v_id g' == black);
 colorHeader1_alloc_colors_lemma h_v_id g black;
   
 let f = objects2 0UL g in
 let f' = objects2 0UL g' in
 assert (f == f');
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 Seq.lemma_mem_snoc s v_id;
 assert (forall x. Seq.mem x st <==> (x == v_id) \/ Seq.mem x s);
 assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem (hd_address x) (objects2 0UL g) /\
                                                        isGrayObject1 (hd_address x) g);
 
 assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
 assert (color_of_object1 h_v_id g' == 3UL);
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (forall x. Seq.mem x s <==> Seq.mem (hd_address x) (objects2 0UL g') /\
                                                        isGrayObject1 (hd_address x) g');
 
 let wz = wosize_of_object1 h_v_id g' in
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));
 assert (Usize.v wz == Usize.v (getWosize (read_word g' h_v_id)));
 assert (well_formed_heap2 g');
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                             Seq.mem x s);
 assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size);
 assert (Usize.v h_v_id % Usize.v mword == 0);
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));

 assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
 
 let tg = tag_of_object1 h_v_id g' in
 assert (Usize.v tg <> infix_tag);
 assert (check_well_formed_closure_objs g (get_allocated_block_addresses g));
 assert (stack_props_func g st);
 assert (Seq.mem v_id st);
 assert (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g);
 assert (h_v_id == hd_address v_id);

 colorHeader1_subset_lemma h_v_id g;

 (*always use abstrcations whenever seq lemmas are disabled. is_black_subset is defined before seq leamms disabling*)
 assert (is_black_subset g g');

 colorHeader1_black_nodes_lemma  g h_v_id;

 assert (black_objects_length g g');

 if (Usize.v tg < no_scan_tag) then 
 (
   if (Usize.v tg = closure_tag) then
   (
     assert (Usize.v wz >= 2);
     assert (Usize.v v_id >= Usize.v mword);
     assert (is_valid_header1 h_v_id g);
     assert (is_valid_header (hd_address v_id) g);
    
     let start_env = start_env_clos_info g' v_id in

     assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address v_id) g')) /\
             Usize.v start_env >= 1);

     let start_env_plus_one = Usize.add start_env 1UL in
     let st1, g1 = fieldPush_spec1 g' s h_v_id wz (start_env_plus_one) in
     
     fieldPush_spec1_black_nodes_lemma g' s h_v_id wz start_env_plus_one;
     assert (is_black_subset g' g1);
     assert (black_objects_length g g');
     is_black_subset_lemma g' g1;
     assert (black_objects_length1 g' g1);
     is_black_subset_lemma_trans g g' g1;
     assert (black_objects_length g g1);
     assert (mark5_body_black_nodes_lemma_post_condition g st);
     ()
   )
   else
   (
     let st1, g1 = fieldPush_spec1 g' s h_v_id wz 1UL in
     assert (G.is_vertex_set st1);
     assert (Seq.length g == Seq.length g1);
     fieldPush_spec1_black_nodes_lemma g' s h_v_id wz 1UL;
     assert (is_black_subset g' g1);
     assert (black_objects_length g g');
     is_black_subset_lemma g' g1;
     assert (black_objects_length1 g' g1);
     is_black_subset_lemma_trans g g' g1;
     assert (black_objects_length g g1);
     assert (mark5_body_black_nodes_lemma_post_condition g st);
     ()
   )
   
 )
  else
  (
    assert (is_black_subset g g');
    assert (mark5_body_black_nodes_lemma_post_condition g st);
    ()
  )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

let rec mark5 (g:heap{well_formed_heap2 g}) 
              (st: seq Usize.t {stack_props_func g st })
           : Pure (heap)
            (requires True)
            (ensures (fun g' -> well_formed_heap2 g'))
            (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
if (G.is_emptySet st) then
   (
      g
   )
 else
   (
     let st', g' = mark5_body g st in
     let v_id = Seq.index st (Seq.length st - 1) in
     assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
     assert (is_valid_header (hd_address v_id) g);
     stack_slice_only_has_gray_color_lemma g st v_id 3UL;
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g 3UL)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g 3UL)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)));
      
     mark5_body_black_nodes_lemma g st;
     assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
     
     assert (well_formed_heap2 g');
     assert ((forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g') /\
                                                            (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0) /\
                                                            (G.is_vertex_set st') /\
                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                                   Seq.mem x st'));
     
     mark5 g' st'
   )

let mark_body_mark_body1_lemma (g:heap{well_formed_heap2 g}) 
                               (st: seq Usize.t {stack_props_func g st})
                                    
           : Lemma
             (requires (~(G.is_emptySet st)))
             (ensures mark5_body g st == mark5_body1 g st) =
 ()

let rec mark7 (g:heap{well_formed_heap2 g}) 
              (st: seq Usize.t {stack_props_func g st })
           : Pure (heap)
            (requires True)
            (ensures (fun g' -> well_formed_heap2 g'))
            (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
if (G.is_emptySet st) then
   (
      g
   )
 else
   (
     let st', g' = mark5_body1 g st in
     mark_body_mark_body1_lemma g st;
     let v_id = Seq.index st (Seq.length st - 1) in
     assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
     assert (is_valid_header (hd_address v_id) g);
     stack_slice_only_has_gray_color_lemma g st v_id 3UL;
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g 3UL)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g 3UL)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)));
      
     mark5_body_black_nodes_lemma g st;
     assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
     
     assert (well_formed_heap2 g');
     assert ((forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g') /\
                                                            (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0) /\
                                                            (G.is_vertex_set st') /\
                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                                   Seq.mem x st'));
     
     mark7 g' st'
   )

let mark7_mark_body_lemma (g:heap{well_formed_heap2 g}) 
                         (st: seq Usize.t {stack_props_func g st})
                   : Lemma
                     (requires (~(G.is_emptySet st)))
                     (ensures (mark7 g st == mark7 (snd (mark5_body1 g st)) (fst (mark5_body1 g st)))) = ()                                          
                  
let mark7_mark_body_lemma1 (g:heap{well_formed_heap2 g}) 
                          (st: seq Usize.t {stack_props_func g st})
                    : Lemma
                     (requires ((G.is_emptySet st)))
                     (ensures (mark7 g st == g)) = ()   

#restart-solver 

let rec mark7_mark5_lemma (g:heap{well_formed_heap2 g}) 
                      (st: seq Usize.t {stack_props_func g st})
              : Lemma
                (ensures mark7 g st == mark5 g st)
                (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st])= 
 if (G.is_emptySet st) then
   (
     ()
   )
 else
   (
     let st', g' = mark5_body1 g st in
     mark_body_mark_body1_lemma g st;
     let v_id = Seq.index st (Seq.length st - 1) in
     assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
     assert (is_valid_header (hd_address v_id) g);
     stack_slice_only_has_gray_color_lemma g st v_id 3UL;
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g 3UL)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g 3UL)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)));
      
     mark5_body_black_nodes_lemma g st;
     assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
     
     assert (well_formed_heap2 g');
     assert ((forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g') /\
                                                            (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0) /\
                                                            (G.is_vertex_set st') /\
                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                                   Seq.mem x st'));

     mark7_mark5_lemma g' st';
     ()
   )

let stack_less_than_heap_size_when_one_non_gray_exists (g:heap{well_formed_heap2 g})
                                                        (st:seq Usize.t)
                                                        (x:Usize.t)
                                  : Lemma
                                    (requires  stack_props_func g st /\ (Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g <> gray)))
                                    (ensures (Seq.length st < heap_size)) = 

 assert (Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g <> gray));
 assert (~(Seq.mem (f_address x) st));
 let blocks = objects2 0UL g in
 get_block_address_length_lemma g;
 assert (Seq.length blocks <= heap_size);
 assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) blocks);
 assert (G.is_vertex_set st);
 assert (G.is_vertex_set blocks);
 assert (forall x. Seq.mem x st ==> UInt.fits (Usize.v x - Usize.v mword) Usize.n);
 assert (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g); 
 assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) blocks); 
 assert (G.subset_vertices_variant st blocks);
 G.subset_variant_lemma st blocks;
 assert (Seq.length st <= Seq.length blocks);
 assert (Seq.length st <= heap_size);
 if Seq.length st < heap_size then ()
 else
   (
     assert (Seq.length st == heap_size);
     assert (Seq.length st == Seq.length blocks);
     assert  (forall x. Seq.mem x st ==> Seq.mem (hd_address x) blocks);
     assert (forall x. Seq.mem x st ==> is_hp_addr x);
     G.subset_of_each_other1 st blocks;
     assert (forall x. Seq.mem x blocks ==> Seq.mem (f_address x) st);
     assert (Seq.mem (f_address x) st);
     ()
   )     

#restart-solver

let fieldPush_fieldPush_spec_body_lemma (g:heap{well_formed_heap2 g})
                                        (st: seq Usize.t{stack_props_func g st})
                                        (h_index:hp_addr{is_valid_header1 h_index g})
                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                        (i':Usize.t{Usize.v i' == Usize.v i + 1})
                          : Lemma
                         (requires True)
                         (ensures (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                                                        (fst (fieldPush_spec_body1 g st h_index wz i))
                                                                                        h_index 
                                                                                        wz
                                                                                        i')) = ()             
                                       
let fieldPush_fieldPush_spec_body_lemma1 (g:heap{well_formed_heap2 g})
                                          (st: seq Usize.t{stack_props_func g st})
                                          (h_index:hp_addr{is_valid_header1 h_index g})
                                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                                          (i:Usize.t)
                         : Lemma
                         (requires (Usize.v i == Usize.v wz + 1))
                         (ensures g == snd (fieldPush_spec1 g st h_index wz i) /\
                                  st == fst (fieldPush_spec1 g st h_index wz i)) = ()  

let slice_coloring_lemma1 (g:heap{well_formed_heap2 g}) 
                          (g':heap{well_formed_heap2 g'}) 
                          (v_id: hp_addr{is_valid_header1 v_id g /\
                                      is_valid_header1 v_id g'})
                          (s: seq Usize.t)
                          (s_top:Usize.t{Usize.v s_top <= Seq.length s}) 
         : Lemma
              (requires ((G.is_vertex_set (Seq.slice s 0 (Usize.v s_top))) /\
                        (~(Seq.mem (f_address v_id) (Seq.slice s 0 (Usize.v s_top)))) /\
                         (color_of_object1 v_id g' == black) /\
                         (heap_remains_same_except_index_v_id v_id g g') /\
                        ((objects2 0UL g ==
                             objects2 0UL g')) /\
                         (get_allocated_block_addresses g == 
                              get_allocated_block_addresses g') /\
                         
                         (color_of_object1 v_id g == gray) /\
                         (forall y. Seq.mem y (Seq.slice s 0 (Usize.v s_top)) \/
                          (y == (f_address v_id)) <==> Seq.mem (hd_address y) (objects2 0UL g) /\ isGrayObject1 (hd_address y) g)))
              (ensures ((forall y. Seq.mem y (Seq.slice s 0 (Usize.v s_top)) <==>
                             Seq.mem (hd_address y) (objects2 0UL g') /\ isGrayObject1 (hd_address y) g'))) = () 

#restart-solver

#restart-solver

let mark5_body_fieldPush_lemma (g:heap{well_formed_heap2 g}) 
                               (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0  })
                               (v_id:hp_addr{v_id == Seq.index st (Seq.length st - 1) /\ is_valid_header1 (hd_address v_id) g})
                               
                               (g': heap{g' == colorHeader1 (hd_address v_id) g black})
                               (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                               (wz:wosize{wz == wosize_of_object1 (hd_address v_id) g})   
                   : Lemma
                   (requires well_formed_heap2 g' /\
                             (stack_props_func g' s) /\
                             (Usize.v v_id >= Usize.v mword /\ Usize.v v_id < heap_size) /\
                              is_valid_header1 (hd_address v_id) g' /\
                              (Usize.v (tag_of_object1 (hd_address v_id) g') < no_scan_tag) /\
                              (Usize.v  (tag_of_object1 (hd_address v_id) g') <> closure_tag))
                                                  
                   (ensures fst (mark5_body g st) == fst (fieldPush_spec1 g' s (hd_address v_id) wz 1UL) /\
                            snd (mark5_body g st) == snd (fieldPush_spec1 g' s (hd_address v_id) wz 1UL)) = ()    

let mark5_body_fieldPush_lemma1 (g:heap{well_formed_heap2 g}) 
                               (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0  })
                               (v_id:hp_addr{v_id == Seq.index st (Seq.length st - 1) /\ is_valid_header1 (hd_address v_id) g})
                               
                               (g': heap{g' == colorHeader1 (hd_address v_id) g black})
                               (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                               (wz:wosize{wz == wosize_of_object1 (hd_address v_id) g})   
                   : Lemma
                   (requires well_formed_heap2 g' /\
                             (stack_props_func g' s) /\
                             (Usize.v v_id >= Usize.v mword /\ Usize.v v_id < heap_size) /\
                              is_valid_header1 (hd_address v_id) g' /\
                              Usize.v (tag_of_object1 (hd_address v_id) g') >= no_scan_tag)
                                                  
                   (ensures fst (mark5_body g st) == s /\
                            snd (mark5_body g st) == g') = ()                               

#restart-solver 

#restart-solver

let mark5_body_fieldPush_lemma2 (g:heap{well_formed_heap2 g}) 
                               (st: seq Usize.t {stack_props_func g st /\ Seq.length st > 0})
                               (v_id:hp_addr{(v_id == Seq.index st (Seq.length st - 1)) /\ (is_valid_header1 (hd_address v_id) g)})
                               
                               (g': heap{g' == colorHeader1 (hd_address v_id) g black})
                               (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                               (wz:wosize{wz == wosize_of_object1 (hd_address v_id) g})   
                   : Lemma
                   (requires well_formed_heap2 g' /\
                             (stack_props_func g' s) /\
                             (Usize.v v_id >= Usize.v mword /\ Usize.v v_id < heap_size) /\
                              (is_valid_header1 (hd_address v_id) g') /\
                              (Usize.v (tag_of_object1 (hd_address v_id) g') < no_scan_tag) /\
                              (Usize.v  (tag_of_object1 (hd_address v_id) g') == closure_tag) /\
                              (Usize.v wz >= 2))
                                                  
                   (ensures (fst (mark5_body g st) == fst (fieldPush_spec1 g' s (hd_address v_id) wz (Usize.add (start_env_clos_info g' v_id) 1UL))) /\
                            (snd (mark5_body g st) == snd (fieldPush_spec1 g' s (hd_address v_id) wz (Usize.add (start_env_clos_info g' v_id) 1UL)))) = ()

let mark_mark_body_lemma (g:heap{well_formed_heap2 g}) 
                         (st: seq Usize.t {stack_props_func g st})
                   : Lemma
                     (requires (~(G.is_emptySet st)))
                     (ensures (mark5 g st == mark5 (snd (mark5_body g st)) (fst (mark5_body g st)))) = () 

let mark_mark_body_lemma1 (g:heap{well_formed_heap2 g}) 
                          (st: seq Usize.t {stack_props_func g st})
                    : Lemma
                     (requires ((G.is_emptySet st)))
                     (ensures (mark5 g st == g)) = ()    


#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

/// ---------------------------------------------------------------------------------------------------------------------------------------------------
/// Graph Construction. The successors for an object with no_scan_tag should be empty. Also incorporate how to deal with closure plus infix objects 
/// ---------------------------------------------------------------------------------------------------------------------------------------------------

let valid_wosize (g:heap{well_formed_heap2 g}) 

                 (h_index:hp_addr{is_valid_header1 h_index g})
                 (wz: wosize) =
  (wz == getWosize (read_word g h_index)) /\ 
  is_fields_within_limit1 h_index wz /\
  is_fields_contents_within_limit2 h_index wz g /\
  (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)

#restart-solver 

let rec create_successors_list_for_h_index (g:heap{well_formed_heap2 g}) 

                                           (h_index:hp_addr{is_valid_header1  h_index g})
                                         
                                           (wz: wosize{valid_wosize g h_index wz})
                         
                                           (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})                 
                                           
                               : Tot (seq Usize.t) 
                         
                                 (decreases ((Usize.v wz + 1) - Usize.v i)) = 
if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
       
       s_list
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 
           ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
        
      let s_list' = create_successors_list_for_h_index g h_index wz i' in
      if isPointer succ_index g  then
      (
        
         let h_addr_succ = hd_address succ in
         
        
         if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
         (
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
           assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
           let parent_succ = f_address parent_hdr in
           lemma_tl parent_succ s_list'; 
        
           let s_list = Seq.cons parent_succ s_list' in 
        
           assert (Seq.head s_list == parent_succ);

           s_list
         )
         else
         (
           
           lemma_tl succ s_list'; 
        
           let s_list = Seq.cons succ s_list' in 
        
           assert (Seq.head s_list == succ);

           s_list
         )
      )
      else
      (
       
        s_list'
      )
    )

let create_successors_list_for_h_index_base_lemma (g:heap{well_formed_heap2 g}) 

                                                      (h_index:hp_addr{is_valid_header1 h_index g})
                                         
                                                      (wz: wosize{valid_wosize g h_index wz})
                         
                                                      (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})                 
                                      : Lemma
                                        (ensures (Usize.v i == Usize.v wz + 1 ==> create_successors_list_for_h_index g h_index wz i == Seq.empty)) = ()

#restart-solver

#restart-solver

#restart-solver              

let f_address_hp_address_lemma (h_index: hp_addr{UInt.fits (Usize.v h_index + Usize.v mword) Usize.n /\ (Usize.v h_index + Usize.v mword < heap_size)})
                         : Lemma (hd_address (f_address h_index) == h_index) = ()

#restart-solver 

#restart-solver

#restart-solver

let cons_property_lemma3 (g:heap{well_formed_heap2 g}) 

                         (h_index:hp_addr{is_valid_header1 h_index g})
                          (s:seq G.edge{(forall p q. Seq.mem (p,q) s ==> is_hp_addr p /\ (UInt.fits (Usize.v p - Usize.v mword) Usize.n) /\
                                                            is_hp_addr q /\ (UInt.fits (Usize.v q - Usize.v mword) Usize.n) /\
                                                            Seq.mem (hd_address p) (get_allocated_block_addresses g) /\
                                                            Seq.mem (hd_address q) (get_allocated_block_addresses g)) /\
                                        (forall p q. Seq.mem (p,q) s ==> hd_address p == h_index)})
                         
                          (s_cons:G.edge{is_hp_addr (fst s_cons) /\ (UInt.fits (Usize.v (fst s_cons) - Usize.v mword) Usize.n) /\
                                        is_hp_addr (snd s_cons) /\ (UInt.fits (Usize.v (snd s_cons) - Usize.v mword) Usize.n) /\
                                       Seq.mem (hd_address (fst s_cons)) (get_allocated_block_addresses g) /\
                                       Seq.mem (hd_address (snd s_cons)) (get_allocated_block_addresses g) /\
                                       hd_address (fst s_cons) == h_index})
                 : Lemma
                   (ensures (forall x y. Seq.mem (x,y) (Seq.cons s_cons s) ==>  is_hp_addr x /\ (UInt.fits (Usize.v x - Usize.v mword) Usize.n) /\
                                                                           is_hp_addr y /\ (UInt.fits (Usize.v y - Usize.v mword) Usize.n) /\
                                                                           Seq.mem (hd_address x) (get_allocated_block_addresses g) /\
                                                                           Seq.mem (hd_address y) (get_allocated_block_addresses g)) /\
                            (forall x y. Seq.mem (x,y) (Seq.cons s_cons s) ==> hd_address x == h_index)) = 
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 ()

let cons_property_lemma5 (g:heap{well_formed_heap2 g}) 

                         (h_index:hp_addr{is_valid_header1 h_index g})
                         (s:seq G.edge{(forall (p:G.edge). Seq.mem p s ==> is_hp_addr (fst p) /\ (UInt.fits (Usize.v (fst p) - Usize.v mword) Usize.n) /\
                                                            is_hp_addr (snd p) /\ (UInt.fits (Usize.v (snd p) - Usize.v mword) Usize.n) /\
                                                            Seq.mem (hd_address (fst p)) (get_allocated_block_addresses g) /\
                                                            Seq.mem (hd_address (snd p)) (get_allocated_block_addresses g)) /\
                                        (forall (p:G.edge). Seq.mem p s ==> hd_address (fst p) == h_index) /\
                                        (forall (p:G.edge). Seq.mem p s ==> (fst p) == f_address h_index)})
                         
                         (s_cons:G.edge{is_hp_addr (fst s_cons) /\ (UInt.fits (Usize.v (fst s_cons) - Usize.v mword) Usize.n) /\
                                        is_hp_addr (snd s_cons) /\ (UInt.fits (Usize.v (snd s_cons) - Usize.v mword) Usize.n) /\
                                       Seq.mem (hd_address (fst s_cons)) (get_allocated_block_addresses g) /\
                                       Seq.mem (hd_address (snd s_cons)) (get_allocated_block_addresses g) /\
                                       hd_address (fst s_cons) == h_index /\
                                       fst s_cons == f_address h_index})
                 : Lemma
                   (ensures (forall (x:G.edge). Seq.mem x (Seq.cons s_cons s) ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                           is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                           Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                           Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                            (forall (x:G.edge). Seq.mem x (Seq.cons s_cons s) ==> hd_address (fst x) == h_index) /\
                            (forall (x:G.edge). Seq.mem x (Seq.cons s_cons s) ==> (fst x) == f_address h_index)) = 
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 ()

#restart-solver

#restart-solver

#restart-solver

let rec create_edge_pairs_for_h_index (g:heap{well_formed_heap2 g}) 

                                      (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                      (wz: wosize{valid_wosize g h_index wz})
                         
                                      (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                       : Tot (f':seq (G.edge) {
                       
                                               (forall (x:G.edge). Seq.mem x f' ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                                is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                                Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                                Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                                               (forall (x:G.edge). Seq.mem x f' ==> hd_address (fst x) == h_index) /\
                                               (forall (x:G.edge). Seq.mem x f' ==> (fst x) == f_address h_index)}) 
                        (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let e = Seq.empty #G.edge in
       assert (Seq.length e == 0);
       assert ((Seq.length e == (Usize.v wz + 1) - Usize.v i));
       e
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 
           ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
        
      let e' = create_edge_pairs_for_h_index g h_index wz i' in
      if isPointer succ_index g  then
      (
        
         let h_addr_succ = hd_address succ in
        
         let f_index = f_address h_index in
         f_address_hp_address_lemma h_index;
         assert (hd_address f_index == h_index);
         if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
         (
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
           assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
           let parent_succ = f_address parent_hdr in
           let edge_pair = (f_index,parent_succ) in
           assert (hd_address (fst edge_pair) == h_index);
           assert (fst edge_pair == f_index);
           assert (snd edge_pair == parent_succ);
           assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
           assert (well_formed_heap2 g);
           assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
           assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                        is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g));
           assert (Seq.mem h_index (get_allocated_block_addresses g));
           assert (is_fields_points_to_blocks2 h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));  
           assert (is_fields_points_to_blocks2_post_condition h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
           assert ((Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) == infix_tag) /\
                              (UInt.fits (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) - 
                                                   (Usize.v (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) * Usize.v mword)) Usize.n) /\
          (
                                                       (let actual_succ = (Usize.sub (read_word g (Usize.add h_index (Usize.mul i mword))) 
                                                       (Usize.mul (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) mword)) in
                                                        (Usize.v actual_succ >= Usize.v mword) /\
                                                        (is_hp_addr actual_succ) /\
                                                        (Usize.v (tag_of_object1 (hd_address actual_succ) g) == closure_tag) /\
                                                        (Seq.mem (hd_address actual_succ) (get_allocated_block_addresses g)))
           ));
           assert (hd_address parent_succ == parent_hdr);
           assert (parent_hdr ==  parent_closure_of_infix_object g h_index i);
           assert (is_valid_header1 parent_hdr g);
           assert (parent_hdr == (hd_address (snd edge_pair)));
           assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
           lemma_tl edge_pair e'; 
        
           let e = Seq.cons edge_pair e' in 
           cons_property_lemma5 g h_index e' edge_pair;
        
           e
         )
         else
         (

           let edge_pair = (f_index,succ) in
           assert (hd_address (fst edge_pair) == h_index);
           assert (fst edge_pair == f_index);
           assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
           assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
           lemma_tl edge_pair e'; 
        
           let e = Seq.cons edge_pair e' in 
           cons_property_lemma5 g h_index e' edge_pair;
           e
         )
      )
      else
      (
        e'
      )
    )

#restart-solver

#restart-solver                      

let rec create_edge_pairs_for_h_index_length_lemma (g:heap{well_formed_heap2 g}) 

                                                   (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                   (wz: wosize{valid_wosize g h_index wz})
                         
                                                   (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                               : Lemma
                                 (ensures (Seq.length (create_edge_pairs_for_h_index g h_index wz i) <= (Usize.v wz + 1) - Usize.v i))
                                 (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 if Usize.v i = Usize.v wz + 1 then
    (
       let e = Seq.empty #G.edge in
       assert (Seq.length e == 0);
       assert ((Seq.length e == (Usize.v wz + 1) - Usize.v i));
       ()
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 
           ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
        
      let e' = create_edge_pairs_for_h_index g h_index wz i' in
      create_edge_pairs_for_h_index_length_lemma g h_index wz i';
      if isPointer succ_index g  then
      (
        
         let h_addr_succ = hd_address succ in
        
         let f_index = f_address h_index in
         f_address_hp_address_lemma h_index;
         assert (hd_address f_index == h_index);
         if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
         (
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
           assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
           let parent_succ = f_address parent_hdr in
           let edge_pair = (f_index,parent_succ) in
           assert (hd_address (fst edge_pair) == h_index);
           assert (fst edge_pair == f_index);
           assert (snd edge_pair == parent_succ);
           assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
           assert (well_formed_heap2 g);
           assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
           assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                        is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g));
           assert (Seq.mem h_index (get_allocated_block_addresses g));
           assert (is_fields_points_to_blocks2 h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));  
           assert (is_fields_points_to_blocks2_post_condition h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
           assert ((Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) == infix_tag) /\
                              (UInt.fits (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) - 
                                                   (Usize.v (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) * Usize.v mword)) Usize.n) /\
          (
                                                       (let actual_succ = (Usize.sub (read_word g (Usize.add h_index (Usize.mul i mword))) 
                                                       (Usize.mul (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) mword)) in
                                                        (Usize.v actual_succ >= Usize.v mword) /\
                                                        (is_hp_addr actual_succ) /\
                                                        (Usize.v (tag_of_object1 (hd_address actual_succ) g) == closure_tag) /\
                                                        (Seq.mem (hd_address actual_succ) (get_allocated_block_addresses g)))
           ));
           assert (hd_address parent_succ == parent_hdr);
           assert (parent_hdr ==  parent_closure_of_infix_object g h_index i);
           assert (is_valid_header1 parent_hdr g);
           assert (parent_hdr == (hd_address (snd edge_pair)));
           assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
           lemma_tl edge_pair e'; 
        
           let e = Seq.cons edge_pair e' in 
           cons_property_lemma5 g h_index e' edge_pair;
        
           ()
         )
         else
         (

           let edge_pair = (f_index,succ) in
           assert (hd_address (fst edge_pair) == h_index);
           assert (fst edge_pair == f_index);
           assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
           assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
           lemma_tl edge_pair e'; 
        
           let e = Seq.cons edge_pair e' in 
           cons_property_lemma5 g h_index e' edge_pair;
           ()
         )
      )
      else
      (
        ()
      )
    )

let create_edge_pairs_for_h_index_length_mem_lemma (g:heap{well_formed_heap2 g}) 

                                                   (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                   (wz: wosize{valid_wosize g h_index wz})
                         
                               : Lemma
                               (ensures (
                                         (forall (x:G.edge). Seq.mem x (create_edge_pairs_for_h_index g h_index wz 1UL) ==> 
                                                                                is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                                is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                                Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                                Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                                         (forall (x:G.edge). Seq.mem x (create_edge_pairs_for_h_index g h_index wz 1UL) ==> 
                                                        (hd_address (fst x) == h_index) /\
                                                        (fst x == f_address h_index)) /\
                                                        Seq.length (create_edge_pairs_for_h_index g h_index wz 1UL) <= Usize.v wz)) = 
let e = create_edge_pairs_for_h_index g h_index wz 1UL in
create_edge_pairs_for_h_index_length_lemma g h_index wz 1UL;
assert (Seq.length (create_edge_pairs_for_h_index g h_index wz 1UL) <= Usize.v wz);
()

#restart-solver 

#restart-solver 


let success_fn_test (i:Usize.t)
                    (e:seq (G.edge){(forall x. Seq.mem x e ==> fst x == i)}) =
  let s = G.successors_fn2 i e in
  assert (forall x. Seq.mem x s <==> Seq.mem (i,x) e);
  G.successors_fn2_pick_second_lemma i e;
  assert (G.pick_second e == s);
  ()

#restart-solver 

let within_heap_all (f: seq Usize.t)
 = (forall x. Seq.mem x f ==> Usize.v x < heap_size)

let multiple_of_mword_all (f: seq Usize.t)
=  (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0)

let all_valid_headers (f: seq Usize.t)
                      (g:heap{well_formed_heap2 g})=
 (forall x. Seq.mem x f ==> is_valid_header1 x g)

let all_objects_and_their_field_pointers_are_within_heap_size (f: seq Usize.t)
                                                              (g:heap{well_formed_heap2 g})=
 (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                      is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)

let all_field_address_are_word_aligned (f: seq Usize.t)
                                       (g:heap{well_formed_heap2 g})=
  (forall x. Seq.mem x f ==> (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))

let all_mem_of_allocated_blocks (f: seq Usize.t)
                                (g:heap{well_formed_heap2 g}) =
 (forall x. Seq.mem x f ==> Seq.mem x (get_allocated_block_addresses g))

#restart-solver 


#restart-solver

let can_be_shifted_forward (f: seq Usize.t)
  = forall x. mem x f ==> Usize.v x + Usize.v mword < heap_size

let can_be_shifted_backward (f: seq Usize.t)
  = forall x. mem x f ==> Usize.v x > 0

#restart-solver

#restart-solver

let edge_fst_snd_hdr_mem_allocs (g:heap{well_formed_heap2 g})
                                (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                                (f': seq (G.edge)) =
 (forall (x:G.edge). Seq.mem x f' ==> is_hp_addr (fst x) /\  Usize.v (fst x) >= Usize.v mword /\
                                 is_hp_addr (snd x) /\  Usize.v (snd x) >= Usize.v mword /\
                                 Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                 Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
 (forall (x:G.edge). Seq.mem x f' ==> Seq.mem (hd_address (fst x)) f)

let edge_graph_succ_connect (g:heap{well_formed_heap2 g})
                            (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                            (f': seq (G.edge)) =
  (forall x. Seq.mem x f  /\ (Usize.v (tag_of_object1 x g) < no_scan_tag) ==> G.successors_fn2 (f_address x) f' == 
                                                                       G.successors_fn2 (f_address x) 
                                                                                  (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL)) /\
  
                                                                                                                 
  (forall x. Seq.mem x f  /\ (Usize.v (tag_of_object1 x g) >= no_scan_tag) ==> G.successors_fn2 (f_address x) f' ==  Seq.empty #UInt64.t)

let edge_graph_succ_connect1 (g:heap{well_formed_heap2 g})
                            (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                            (f': seq (G.edge)) =
  (forall (x:Usize.t{Seq.mem x f}). G.successors_fn2 (f_address x) f' == (
                                                                      if (Usize.v (tag_of_object1 x g) < no_scan_tag) then
                                                                        G.successors_fn2 (f_address x) 
                                                                                  (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL)
                                                                      else
                                                                        Seq.empty #UInt64.t
                                                                    ) )   

#restart-solver 

#restart-solver 

let hp_addr_all (f: seq Usize.t)
=  (forall x. Seq.mem x f ==> is_hp_addr x)

#restart-solver 

let edge_graph_succ_connect_closure_objs (g:heap{well_formed_heap2 g})
                            (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                            (f': seq (G.edge)) =
   (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) < no_scan_tag) ==>  (Usize.v (tag_of_object1 x g) == closure_tag) ==> 
    ( let f_id = f_address x in
      let start_of_env = start_env_clos_info g f_id in
      let start_env_plus_one = Usize.add start_of_env 1UL in
      let e' = create_edge_pairs_for_h_index g x (getWosize (read_word g x)) start_env_plus_one in
      (G.successors_fn2 (f_address x) f' ==  G.successors_fn2 (f_address x) e')))
      

let edge_graph_succ_connect3 (g:heap{well_formed_heap2 g})
                            (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                            (f': seq (G.edge)) =
  
 
 edge_graph_succ_connect_closure_objs g f f' /\
 (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) < no_scan_tag) ==>  (Usize.v (tag_of_object1 x g) <> closure_tag) ==> 
    G.successors_fn2 (f_address x) f' ==  G.successors_fn2 (f_address x) (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL)) /\
  (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) >= no_scan_tag) ==>
    G.successors_fn2 (f_address x) f' ==  Seq.empty #UInt64.t)      
                                                                                                                                 
#restart-solver

#restart-solver 

let f_address_lemma (tl:seq Usize.t)
                    (hd:hp_addr{Usize.v hd + Usize.v mword < heap_size})
           : Lemma
             (requires (forall y. Seq.mem y tl ==> hd <> y))
             (ensures (forall y. Seq.mem y tl ==> f_address hd <> f_address y)) = ()

#restart-solver 

let can_shift_forward_lemma (f: seq Usize.t)
                            (g:heap{well_formed_heap2 g})
                            (hd: hp_addr{Seq.mem hd f})
              : Lemma
                (requires all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g)
                (ensures (Usize.v hd + Usize.v mword < heap_size)) = ()

#restart-solver

#restart-solver

#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver

let seq_empty_lemma ()
            : Lemma
              (ensures (Seq.length (Seq.empty #G.edge) == 0) /\ 
                       (~(exists x. Seq.mem x (Seq.empty #G.edge)))) = ()

let seq_empty_lemma1  (f: seq Usize.t)
            : Lemma
              (requires Seq.length f == 0)
              (ensures (~(exists x. Seq.mem x f))) = ()


let seq_non_empty_lemma (f: seq Usize.t)
            : Lemma
              (requires ~(Seq.length f == 0))
              (ensures (Seq.length f > 0) /\
                       (Seq.mem (Seq.head f) f) /\
                       (forall x. Seq.mem x (Seq.tail f) ==> Seq.mem x f) /\
                        (Seq.length (Seq.tail f) < Seq.length f) /\
                        Seq.cons (Seq.head f) (Seq.tail f) == f /\
                        (forall x.Seq.mem x f ==> (x == Seq.head f) \/
                                            Seq.mem x (Seq.tail f))) = ()

let length_fn (f: seq Usize.t) =
   Seq.length f

let length_fn_lemma (f: seq Usize.t{length_fn f > 0}) 
     : Lemma
       (length_fn f > length_fn (Seq.tail f)) = ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"
#push-options "--split_queries always"

#restart-solver

#restart-solver

#restart-solver

let rec create_edge_list_from_heap1   (g:heap{well_formed_heap2 g})
                                      (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                        within_heap_all f /\
                                                        multiple_of_mword_all f /\
                                                        all_valid_headers f g /\
                                                        (G.is_vertex_set f) /\
                                                        all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                        all_field_address_are_word_aligned  f g})
                       : Tot
                         (f': seq (G.edge){edge_fst_snd_hdr_mem_allocs g f f' /\ edge_graph_succ_connect3 g f f'})
                         (decreases (*(Seq.length f)*) length_fn f) = 
if length f = 0 then 
 (
   let e = Seq.empty #G.edge in
   seq_empty_lemma ();
   assert (forall (x:G.edge). Seq.mem x e ==> is_hp_addr (fst x) /\  Usize.v (fst x) >= Usize.v mword /\
                                 is_hp_addr (snd x) /\  Usize.v (snd x) >= Usize.v mword /\
                                 Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                 Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
   
   assert (edge_fst_snd_hdr_mem_allocs g f e);
   
   seq_empty_lemma1 f;
   assert (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) >= no_scan_tag) ==>
           G.successors_fn2 (f_address x) e ==  Seq.empty #UInt64.t);
   
   assert (edge_graph_succ_connect3 g f e);
   e
 )
 else
 (
   
   seq_non_empty_lemma f;
   let hd = Seq.head f in
   assert (is_hp_addr hd);
   can_shift_forward_lemma f g hd;
   assert (Usize.v hd + Usize.v mword < heap_size);
   let tl = Seq.tail f in
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));
   
   assert (Seq.length f > Seq.length tl);
   assert (Seq.length f > Seq.length (Seq.tail f));
   length_fn_lemma f;
   assert (length_fn f > length_fn (Seq.tail f));
   assert (length_fn f > length_fn tl);
   
   let rest_of_f = create_edge_list_from_heap1 g tl in
   assert (forall (x:G.edge). Seq.mem x rest_of_f ==> Seq.mem (hd_address (fst x)) tl);
  

   assert (~(exists (x:G.edge). Seq.mem x rest_of_f /\ (hd_address (fst x)) == hd));
   assert (edge_graph_succ_connect3 g tl rest_of_f);

   let tg = tag_of_object1 hd g in
   if (Usize.v tg < no_scan_tag) then 
   (
     let wz = getWosize (read_word g hd) in
     let f_id = f_address hd in
     f_address_lemma tl hd;
     assert (forall y. Seq.mem y tl ==> f_address hd <> f_address y);
     assert (hd_address f_id == hd);
     if (Usize.v tg = closure_tag) then
     (
       assert (Usize.v wz >= 2);
       assert (Usize.v f_id >= Usize.v mword);
       assert (is_valid_header hd g);
       assert (is_valid_header (hd_address f_id) g);
       assert (Usize.v (tag_of_object1 (hd_address f_id) g) == closure_tag);
       let start_env = start_env_clos_info g f_id in
       let start_env_plus_one = Usize.add start_env 1UL in

       assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address f_id) g)) /\
             Usize.v start_env >= 1);
       let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz start_env_plus_one in
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> 
                                                        is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                        is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                        Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                        Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
                                                        
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (hd_address (fst x)) == hd);
       
   
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (fst x == f_id));
       assert (~(Seq.mem hd tl));
       assert (forall y. Seq.mem y tl ==> hd <> y);
       
       assert (forall (x:G.edge) y. Seq.mem y tl /\ Seq.mem x edge_pairs_for_hd ==> (fst x <> f_address y));
       //assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
       G.successors_fn2_pick_second_lemma f_id edge_pairs_for_hd;
   
       assert (G.successors_fn2 f_id edge_pairs_for_hd == G.pick_second edge_pairs_for_hd);
       let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
       Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
   
       assert (~(exists (x:G.edge). Seq.mem x rest_of_f /\ (fst x) == f_id));
       G.successors_fn2_e2_is_successors_fn2_e_if_no_fst_i_in_e1 f_id (edge_pairs_for_hd) (rest_of_f) f';
       assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (edge_pairs_for_hd));
       assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (create_edge_pairs_for_h_index g hd 
                                                                                          (getWosize (read_word g hd))
                                                                                          start_env_plus_one));
       assert (cons hd tl == f);
       assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
       G.successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e'' tl (edge_pairs_for_hd) (rest_of_f) f';
       assert (forall x. Seq.mem x tl ==> (G.successors_fn2 (f_address x) f' == G.successors_fn2 (f_address x) (rest_of_f)));
       assert (forall x. Seq.mem x f ==> x == hd \/ Seq.mem x tl);
       assert (edge_fst_snd_hdr_mem_allocs g f f');
       assert (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) >= no_scan_tag) ==>
               G.successors_fn2 (f_address x) f' ==  Seq.empty #UInt64.t);
       assert (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) < no_scan_tag) ==>  (Usize.v (tag_of_object1 x g) <> closure_tag) ==> 
               G.successors_fn2 (f_address x) f' ==  G.successors_fn2 (f_address x) (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL));
       assert (edge_graph_succ_connect_closure_objs g f f');
       assert (edge_graph_succ_connect3 g f f');
       f'
     )
     else
     (
       let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz 1UL in
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> 
                                                        is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                        is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                        Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                        Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
                                                        
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (hd_address (fst x)) == hd);
       
   
       assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (fst x == f_id));
       assert (~(Seq.mem hd tl));
       assert (forall y. Seq.mem y tl ==> hd <> y);
       
       assert (forall (x:G.edge) y. Seq.mem y tl /\ Seq.mem x edge_pairs_for_hd ==> (fst x <> f_address y));
       //assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
       G.successors_fn2_pick_second_lemma f_id edge_pairs_for_hd;
   
       assert (G.successors_fn2 f_id edge_pairs_for_hd == G.pick_second edge_pairs_for_hd);
       let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
       Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
   
       assert (~(exists (x:G.edge). Seq.mem x rest_of_f /\ (fst x) == f_id));
       G.successors_fn2_e2_is_successors_fn2_e_if_no_fst_i_in_e1 f_id (edge_pairs_for_hd) (rest_of_f) f';
       assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (edge_pairs_for_hd));
       assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (create_edge_pairs_for_h_index g hd 
                                                                                          (getWosize (read_word g hd))
                                                                                          1UL));
       assert (cons hd tl == f);
       assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
       G.successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e'' tl (edge_pairs_for_hd) (rest_of_f) f';
       assert (forall x. Seq.mem x tl ==> (G.successors_fn2 (f_address x) f' == G.successors_fn2 (f_address x) (rest_of_f)));
       assert (edge_fst_snd_hdr_mem_allocs g f f');
       assert (forall x. Seq.mem x tl  ==> (Usize.v (tag_of_object1 x g) < no_scan_tag) ==>  (Usize.v (tag_of_object1 x g) <> closure_tag) ==> 
               G.successors_fn2 (f_address x) f' ==  G.successors_fn2 (f_address x) (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL));
       assert (forall x. Seq.mem x f ==> x == hd \/ Seq.mem x tl);
       assert (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) < no_scan_tag) ==>  (Usize.v (tag_of_object1 x g) <> closure_tag) ==> 
               G.successors_fn2 (f_address x) f' ==  G.successors_fn2 (f_address x) (create_edge_pairs_for_h_index g x (getWosize (read_word g x)) 1UL));
       assert (forall x. Seq.mem x f  ==> (Usize.v (tag_of_object1 x g) >= no_scan_tag) ==>
               G.successors_fn2 (f_address x) f' ==  Seq.empty #UInt64.t);
       assert (edge_graph_succ_connect_closure_objs g f f');
       assert (edge_graph_succ_connect3 g f f');
       f'
     )
   )
   else
   (
     (*branch type checked when other branches are commented out*)
     let edge_pairs_for_hd = Seq.empty #G.edge in
     seq_empty_lemma ();
     assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (hd_address (fst x)) == hd);
     assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> 
                                                        is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                        is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                        Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                        Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
     
     assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> is_hp_addr (fst x) /\  Usize.v (fst x) >= Usize.v mword /\
                                                           is_hp_addr (snd x) /\  Usize.v (snd x) >= Usize.v mword /\
                                                           Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                           Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
     let f_id = f_address hd in
     assert (hd_address f_id == hd);
   
     assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (fst x == f_id));
     assert (~(Seq.mem hd tl));
     assert (forall y. Seq.mem y tl ==> hd <> y);
     f_address_lemma tl hd;
     assert (forall y. Seq.mem y tl ==> f_address hd <> f_address y);
    
     //assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
    
     G.successors_fn2_pick_second_lemma f_id edge_pairs_for_hd;
   
     assert (G.successors_fn2 f_id edge_pairs_for_hd == G.pick_second edge_pairs_for_hd);
     let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
     Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
   
     assert (~(exists (x:G.edge). Seq.mem x rest_of_f /\ (fst x) == f_id));
     G.successors_fn2_e2_is_successors_fn2_e_if_no_fst_i_in_e1 f_id (edge_pairs_for_hd) (rest_of_f) f';
     assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (edge_pairs_for_hd));
     assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (Seq.empty #G.edge));
     assert (cons hd tl == f);
     assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
     G.successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e'' tl (edge_pairs_for_hd) (rest_of_f) f';
     assert (forall x. Seq.mem x tl ==> (G.successors_fn2 (f_address x) f' == G.successors_fn2 (f_address x) (rest_of_f)));
     assert (append (edge_pairs_for_hd) (rest_of_f) == f');
     assert (edge_fst_snd_hdr_mem_allocs g tl rest_of_f);
     Seq.append_empty_l rest_of_f;
     assert (f' == rest_of_f);
     assert (edge_fst_snd_hdr_mem_allocs g tl rest_of_f);
     assert (edge_fst_snd_hdr_mem_allocs g f f');
     assert (forall x. Seq.mem x f ==> x == hd \/ Seq.mem x tl);
     assert (edge_graph_succ_connect_closure_objs g f f');
     assert (edge_graph_succ_connect3 g f f');
     f'
   )
)

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver 

let rec first_field_addresses_of_allocated_blocks   (g:heap{well_formed_heap2 g})
                                                    (f: seq Usize.t 
                                                      { 
                                                       (all_mem_of_allocated_blocks f g) /\
                                                       (within_heap_all f) /\
                                                       (multiple_of_mword_all f) /\
                                                       (all_valid_headers f g) /\
                                                       (G.is_vertex_set f) /\
                                                       (all_objects_and_their_field_pointers_are_within_heap_size f g) /\
                                                       (all_field_address_are_word_aligned f g) /\
                                                       (can_be_shifted_forward f)
                                                       }
                                                     ) 
                       : Tot (f':seq Usize.t{(within_heap_all f') /\
                                             (multiple_of_mword_all f') /\
                                             (can_be_shifted_backward f')  /\
                                             (forall x. Seq.mem x f' <==> Seq.mem (hd_address x) f) /\
                                             (forall x. Seq.mem x f <==> Seq.mem (f_address x) f') /\
                                             (Seq.length f == Seq.length f') /\
                                             (G.is_vertex_set f') /\
                                             (forall x. Seq.mem x f' ==> Seq.mem (hd_address x) (get_allocated_block_addresses g))}) 
                         (decreases Seq.length f) = 

if length f = 0 then 
 (
   let f' = Seq.empty #Usize.t in
   G.is_vertex_set_lemma1 f';
   f'
 )
 else
 (
   let hd = Seq.head f in
   let tl = Seq.tail f in
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));
   
   let rest_of_f = first_field_addresses_of_allocated_blocks g tl in
  
   let f_id = f_address hd in
   assert (hd_address f_id == hd);

   lemma_tl f_id rest_of_f;
   let f' = Seq.cons f_id rest_of_f in
   assert (within_heap_all f);
   assert (within_heap_all rest_of_f);
   assert (within_heap_all f');
   let hd' = Seq.head f' in
   let tl' = Seq.tail f' in
   assert (hd' == f_id);
   assert (tl' == rest_of_f);
   assert (~(mem (head f') (tail f')));
   G.is_vertex_set_cons f_id rest_of_f;
   assert (G.is_vertex_set f');
   assert (forall x. Seq.mem x f' <==> Seq.mem (hd_address x) f);
   assert (forall x. Seq.mem x f <==> Seq.mem (f_address x) f');
   assert (can_be_shifted_backward f');
   assert (forall x. Seq.mem x f' ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));
   f'
  )

#restart-solver 

#restart-solver                                             
                         
let rec first_field_addresses_of_allocated_blocks_lemma   (g:heap{well_formed_heap2 g})
                                                          (f: seq Usize.t 
                                                             { 
                                                               (all_mem_of_allocated_blocks f g) /\
                                                               (within_heap_all f) /\
                                                               (multiple_of_mword_all f) /\
                                                               (all_valid_headers f g) /\
                                                               (G.is_vertex_set f) /\
                                                               (all_objects_and_their_field_pointers_are_within_heap_size f g) /\
                                                               (all_field_address_are_word_aligned f g) /\
                                                               (can_be_shifted_forward f)
                                                             }
                                                           )
                                                           (g':heap{well_formed_heap2 g'})
                                                           (f': seq Usize.t 
                                                             { 
                                                               (all_mem_of_allocated_blocks f' g') /\
                                                               (within_heap_all f') /\
                                                               (multiple_of_mword_all f') /\
                                                               (all_valid_headers f' g') /\
                                                               (G.is_vertex_set f') /\
                                                               (all_objects_and_their_field_pointers_are_within_heap_size f' g') /\
                                                               (all_field_address_are_word_aligned f' g') /\
                                                               (can_be_shifted_forward f')
                                                             }
                                                           )
                            : Lemma
                              (requires f == f')
                              (ensures first_field_addresses_of_allocated_blocks g f == first_field_addresses_of_allocated_blocks g' f') 
                              (decreases Seq.length f) =
if length f = 0 then 
 (
   let f' = Seq.empty #Usize.t in
   G.is_vertex_set_lemma1 f';
   ()
 )
 else
 (
   let hd = Seq.head f in
   let tl = Seq.tail f in
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));

   let hd' = Seq.head f' in
   let tl' = Seq.tail f' in
   G.is_vertex_set_lemma f';
   assert (G.is_vertex_set tl');
   
   G.is_vertex_set_lemma4 f';
   assert (~(Seq.mem hd tl'));
   let rest_of_f = first_field_addresses_of_allocated_blocks g tl in
   
   assert (tl == tl');
   assert (hd == hd');
   assert ((all_mem_of_allocated_blocks tl' g') /\
                                                               (within_heap_all tl') /\
                                                               (multiple_of_mword_all tl') /\
                                                               (all_valid_headers tl' g') /\
                                                               (G.is_vertex_set tl') /\
                                                               (all_objects_and_their_field_pointers_are_within_heap_size tl' g') /\
                                                               (all_field_address_are_word_aligned tl' g'));
   
   assert (can_be_shifted_forward tl');
   let rest_of_f' = first_field_addresses_of_allocated_blocks g' tl' in
   
   first_field_addresses_of_allocated_blocks_lemma g tl g' tl';
   
   assert (rest_of_f == rest_of_f');
  
   let f_id = f_address hd in
   let f_id' = f_address hd' in
   assert (hd_address f_id == hd);
   assert (f_id == f_id');

   lemma_tl f_id rest_of_f;
   let f1 = Seq.cons f_id rest_of_f in
   
   lemma_tl f_id' rest_of_f';
   let f2 = Seq.cons f_id' rest_of_f' in

   assert (f1 == f2);
   ()
 )

#reset-options "--z3rlimit 1000"

#restart-solver

#restart-solver

let create_edge_list_for_graph (g:heap{well_formed_heap2 g}) 
               : Tot
                 (f': seq (G.edge){(forall (x:G.edge). Seq.mem x f' ==> is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                   is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                   Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                   Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g))}) =
let allocs = get_allocated_block_addresses g in
  assert ((forall x. Seq.mem x allocs ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                       (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                       (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                       (forall x. Seq.mem x allocs ==> is_valid_header x g) /\
                                                       (G.is_vertex_set allocs));
  assert (forall x. Seq.mem x allocs ==> is_fields_within_limit1 x (getWosize (read_word g x)));
  assert (forall x. Seq.mem x allocs ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
  fieldaddress_within_limits_lemma_x_all g;
  assert (forall x. Seq.mem x allocs ==> (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0));
  let f' = create_edge_list_from_heap1 g allocs in
  assert (forall (x:G.edge). Seq.mem x f' ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                           is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                           Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                           Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));                                               
                                                                   
                                                                    
                                           
  f'

let create_graph_from_heap (g:heap {well_formed_heap2 g}) 
                   : Pure (G.graph_state #unit #unit)
                    (requires all_field_address_are_word_aligned (get_allocated_block_addresses g) g)
                    (ensures fun f -> (G.is_vertex_set f.vertices) /\
                                   (Seq.equal (f.vertices) (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)))) = 
let f = get_allocated_block_addresses g in 
  assert ((all_mem_of_allocated_blocks f g) /\
          (within_heap_all f) /\
          (multiple_of_mword_all f) /\
          (all_valid_headers f g) /\
          (G.is_vertex_set f));
  assert (can_be_shifted_forward f);
  fieldaddress_within_limits_lemma_x_all g;
  assert (all_objects_and_their_field_pointers_are_within_heap_size f g);
  assert (all_field_address_are_word_aligned f g);                                               
  let ff_allocs = first_field_addresses_of_allocated_blocks g f in  
  assert (forall x. Seq.mem x ff_allocs ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));
  let e = create_edge_list_for_graph g in
  
  assert (forall x. Seq.mem x f <==> Seq.mem (f_address x) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (hd_address (fst x)) f);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (f_address (hd_address (fst x))) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (fst x) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (hd_address (snd x)) f);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (f_address (hd_address (snd x))) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (snd x) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (fst x) ff_allocs /\
                                       Seq.mem (snd x) ff_allocs);
  {
    vertices  = ff_allocs;
    edge_set  = e;
  }

#restart-solver 

#restart-solver 

#push-options "--z3rlimit 500"

#restart-solver

let create_edge_pairs_for_h_index_length_mem_lemma1 (g:heap{well_formed_heap2 g}) 

                                                    (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                    (wz: wosize{valid_wosize g h_index wz})
                                                    (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                         
                               : Lemma
                               (ensures (
                                         (forall (x:G.edge). Seq.mem x (create_edge_pairs_for_h_index g h_index wz i) ==> 
                                                                                is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                                is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                                Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                                Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                                         (forall (x:G.edge). Seq.mem x (create_edge_pairs_for_h_index g h_index wz i) ==> 
                                                        (hd_address (fst x) == h_index) /\
                                                        (fst x == f_address h_index)) /\
                                                        Seq.length (create_edge_pairs_for_h_index g h_index wz i) <= (Usize.v wz + 1) - Usize.v i)) = 
let e = create_edge_pairs_for_h_index g h_index wz i in
create_edge_pairs_for_h_index_length_lemma g h_index wz i;
()

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver


#restart-solver

#push-options "--split_queries always"

#restart-solver

let graph_successors_mem_lemma (g: heap {well_formed_heap2 g })
                               (h_index:hp_addr{is_valid_header1 h_index g})
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g))
                                  (ensures (forall x. Seq.mem x  (G.successors (create_graph_from_heap g) (f_address h_index)) ==> 
                                                         Seq.mem (hd_address x) (get_allocated_block_addresses g))) = 
let allocs = get_allocated_block_addresses g in
 assert (G.is_vertex_set allocs);
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 let grph = create_graph_from_heap g in
 let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in 
 assert (Seq.equal (grph.vertices) ff_allocs);
 assert (forall x. Seq.mem x allocs <==> Seq.mem (f_address x) ff_allocs);
 assert (Seq.mem (f_address h_index) (ff_allocs));
 let f_h_index = f_address h_index in 
 G.successors_successors_fn2_connect_lemma grph f_h_index;  
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index grph.edge_set);
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_for_graph g));
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs));
 assert (Seq.mem h_index allocs);                                                         
 let tg = tag_of_object1 h_index g in
 assert (edge_graph_succ_connect3 g allocs (create_edge_list_from_heap1 g allocs));
 
 assert (forall x. Seq.mem x allocs  ==>(Usize.v (tag_of_object1 x g) >= no_scan_tag) ==> 
              G.successors_fn2 (f_address x) (create_edge_list_from_heap1 g allocs) ==  Seq.empty #UInt64.t);

 if (Usize.v tg < no_scan_tag) then 
 (
    if (Usize.v tg = closure_tag) then
    (
      let start_env = start_env_clos_info g f_h_index in
      let start_env_plus_one = Usize.add start_env 1UL in
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) start_env_plus_one in 
      create_edge_pairs_for_h_index_length_mem_lemma1 g h_index (getWosize (read_word g h_index)) start_env_plus_one;
      G.pick_second_mem_lemma grph h_index_edge_list;
      ()
    )
    else
    (
      
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL in 
      G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;
      create_edge_pairs_for_h_index_length_mem_lemma g h_index (getWosize (read_word g h_index));
      G.pick_second_mem_lemma grph h_index_edge_list;
      ()
    )
      
 )
 else
 (
  ()
 )

#restart-solver 

#restart-solver

#restart-solver 

#reset-options "--z3rlimit 100"


let length_empty_lemma (s:seq UInt64.t)
                : Lemma
                  (requires s == Seq.empty)
                  (ensures (Seq.length s == 0)) = ()
                  
let mem_empty_lemma (s:seq UInt64.t)
              : Lemma
                (requires s == Seq.empty)
                (ensures (~(exists x. Seq.mem x s))) = ()

let cons_mem_property_lemma (s:seq UInt64.t)
                            (elem: UInt64.t)
               : Lemma
                 (requires (forall x. Seq.mem x s ==> Usize.v x > 0 /\ Usize.v x < heap_size) /\
                           (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0) /\
                           (forall x. Seq.mem x s ==> is_hp_addr x) /\
                           
                           (Usize.v elem > 0 /\ Usize.v elem < heap_size) /\
                           (Usize.v elem % Usize.v mword == 0) /\
                           (is_hp_addr elem))
                (ensures ( (forall x. Seq.mem x (cons elem s) ==> Usize.v x > 0 /\ Usize.v x < heap_size) /\
                           (forall x. Seq.mem x (cons elem s) ==> Usize.v x % Usize.v mword == 0) /\
                           (forall x. Seq.mem x (cons elem s) ==> is_hp_addr x))) =
                           
 mem_cons elem s;
 ()

#push-options "--z3rlimit 1000"

#restart-solver

let cons_length_lemma (s:seq Usize.t)
                      (s_cons:Usize.t)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s)) == Seq.length s + 1)=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ; 
 ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let graph_successors_length_lemma (g: heap {well_formed_heap2 g})
                                  (h_index:hp_addr{is_valid_header1 h_index g})
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g))
                                  (ensures (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= 
                                                Usize.v (getWosize (read_word g h_index)))) =
let allocs = get_allocated_block_addresses g in
 assert (G.is_vertex_set allocs);
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 let grph = create_graph_from_heap g in
 let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in 
 assert (Seq.equal (grph.vertices) ff_allocs);
 assert (forall x. Seq.mem x allocs <==> Seq.mem (f_address x) ff_allocs);
 assert (Seq.mem (f_address h_index) (ff_allocs));
 let f_h_index = f_address h_index in 
 G.successors_successors_fn2_connect_lemma grph f_h_index;  
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index grph.edge_set);
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_for_graph g));
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs));
 assert (Seq.mem h_index allocs);                                                         
 let tg = tag_of_object1 h_index g in
 assert (edge_graph_succ_connect3 g allocs (create_edge_list_from_heap1 g allocs));
 
 assert (forall x. Seq.mem x allocs  ==>(Usize.v (tag_of_object1 x g) >= no_scan_tag) ==> 
              G.successors_fn2 (f_address x) (create_edge_list_from_heap1 g allocs) ==  Seq.empty #UInt64.t);

 if (Usize.v tg < no_scan_tag) then 
 (
    if (Usize.v tg = closure_tag) then
    (
      let start_env = start_env_clos_info g f_h_index in
      let start_env_plus_one = Usize.add start_env 1UL in
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) start_env_plus_one in 
      G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;
      create_edge_pairs_for_h_index_length_mem_lemma1 g h_index (getWosize (read_word g h_index)) start_env_plus_one;
      G.pick_second_length_lemma h_index_edge_list;
      
      assert (Usize.v start_env >= 1);
      assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address f_h_index) g)));  
      assert (wosize_of_object1 (hd_address f_h_index) g == getWosize (read_word g (hd_address f_h_index)));
      assert (hd_address f_h_index == h_index);
      assert (wosize_of_object1 (hd_address f_h_index) g == getWosize (read_word g h_index));
      
      assert (Seq.length h_index_edge_list <=  Usize.v (getWosize (read_word g h_index)));
      assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs));
      assert (edge_graph_succ_connect3 g allocs (create_edge_list_from_heap1 g allocs));
      assert (G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs) == G.successors_fn2 f_h_index h_index_edge_list);
      assert (Seq.length (G.successors_fn2 f_h_index h_index_edge_list) == Seq.length h_index_edge_list);
      assert (Seq.length (G.successors_fn2 f_h_index h_index_edge_list) <= Usize.v (getWosize (read_word g h_index)));
      assert (Seq.length (G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs)) <= Usize.v (getWosize (read_word g h_index)));
      assert (Seq.length (G.successors grph f_h_index) <= Usize.v (getWosize (read_word g h_index)));
      ()
    )
    else
    (
      
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL in 
      G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;
      create_edge_pairs_for_h_index_length_mem_lemma g h_index (getWosize (read_word g h_index));
      G.pick_second_length_lemma h_index_edge_list;
      assert (Seq.length (G.successors_fn2 f_h_index h_index_edge_list) <= 
                            Usize.v (getWosize (read_word g h_index)));
      assert (Seq.length (G.successors grph f_h_index) <= Usize.v (getWosize (read_word g h_index)));
      ()
    )
      
 )
 else
 (
  length_empty_lemma (Seq.empty #UInt64.t);
  ()
 )

#reset-options "--z3rlimit 500"
#push-options "--split_queries always"


let size_less_heap_size_lemma (g:heap{well_formed_heap2 g})

                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header1 h_index g 
                                                            })
                                           
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                             (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                  : Lemma
                    (requires (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size))
                    (ensures (Usize.v (Usize.add h_index (Usize.mul i mword))< heap_size)) =  ()

#restart-solver 

#restart-solver 

let i_value_lemma (wz:Usize.t)
                  (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1}) 
           : Lemma
             (requires (Usize.v i <> Usize.v wz + 1)) 
             (ensures (Usize.v i < Usize.v wz + 1)) =
 ()

let length_empty_generic_lemma (#a:Type)
                                (s:seq a)
                : Lemma
                  (requires s == Seq.empty)
                  (ensures (Seq.length s == 0)) = ()

#restart-solver

let succ_index_lemma (g:heap{well_formed_heap2 g}) 
                     (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                     (wz: wosize{valid_wosize g h_index wz})
                         
                     (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
          : Lemma
            (ensures ~(Seq.mem (Usize.add h_index (Usize.mul i mword)) (objects2 0UL g))) =
let succ_index = Usize.add h_index (Usize.mul i mword) in
assert (Usize.v succ_index >= Usize.v h_index + Usize.v mword);
assert (Usize.v succ_index <= Usize.v h_index + (((Usize.v (getWosize (read_word g h_index)) + 1) * Usize.v mword) - 1));
assert ((forall x y. Seq.mem x (objects2 0UL g) /\  (Usize.v y >= Usize.v x + Usize.v mword) /\ 
                                                   (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1)) ==>
                                                   ~(Seq.mem y (objects2 0UL g))));
assert (Seq.mem h_index (objects2 0UL g));
assert (~(Seq.mem succ_index (objects2 0UL g)));
()

let create_edge_pairs_for_h_index_lemma_rec_lemma_infix (g:heap{well_formed_heap2 g}) 
                                                            (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                            (wz: wosize{valid_wosize g h_index wz})
                         
                                                            (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                            (i':Usize.t{Usize.v i' == Usize.v i + 1})
                          :Lemma
                           (ensures (isPointer (Usize.add h_index (Usize.mul i mword)) g /\ 
                     Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) == infix_tag ==> 
                              create_edge_pairs_for_h_index g h_index wz i == Seq.cons ((f_address h_index),(f_address (parent_closure_of_infix_object g h_index i))) 
                                                              (create_edge_pairs_for_h_index g h_index wz i'))) =
()

let create_edge_pairs_for_h_index_lemma_rec_lemma_non_infix (g:heap{well_formed_heap2 g}) 
                                                            (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                            (wz: wosize{valid_wosize g h_index wz})
                         
                                                            (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                            (i':Usize.t{Usize.v i' == Usize.v i + 1})
                          :Lemma
                           (ensures (isPointer (Usize.add h_index (Usize.mul i mword)) g /\ 
                                       Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) <> infix_tag ==> 
                                       create_edge_pairs_for_h_index g h_index wz i == Seq.cons ((f_address h_index),(read_word g (Usize.add h_index (Usize.mul i mword)))) (create_edge_pairs_for_h_index g h_index wz i'))) =
()

let colorHeader1_tags_lemma  (v_id:hp_addr)  
                             (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                             (c:color)
                             (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })
            : Lemma
              (ensures ((forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g == tag_of_object1 x g'))) =
()

let colorHeader1_wosize_lemma  (v_id:hp_addr)  
                             (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                             (c:color)
                             (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })
            : Lemma
              (ensures ((forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). wosize_of_object1 x g == wosize_of_object1 x g'))) =
()

let allocs_props_g (g:heap{well_formed_heap2 g})
                   (h_index:hp_addr{is_valid_header1 h_index g}) =
  (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g /\
                                                       is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g))

let parent_closure_index_props (g:heap{well_formed_heap2 g})
                               (h_index:hp_addr{is_valid_header1 h_index g})
                               (i:Usize.t) =
 (Usize.v i < Usize.v (getWosize (read_word g h_index)) + 1 /\ Usize.v i >= 1) /\
                                               isPointer (succ_index_fn g h_index i) g /\
                                               (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag)

let field_points_to_blocks_allocs_lemma (g:heap{well_formed_heap2 g})
                                            : Lemma
                                              (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) 
                                              (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                                          is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g))) = 
 assert (well_formed_heap2 g);
 assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
 ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#push-options "--split_queries always"

#restart-solver


let parent_closure_of_infix_object_lemma (g:heap{well_formed_heap2 g})
                                         (h_index:hp_addr{is_valid_header1 h_index g})
                                         (i:Usize.t{parent_closure_index_props g h_index i}) 
                                         (v_id:hp_addr{is_valid_header1 v_id g}) 
                                         (c:color)
                                         (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) /\ is_valid_header1 h_index g' })
                                         
                   : Lemma
                     (requires (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                allocs_props_g g h_index /\
                                allocs_props_g g' h_index /\
                                parent_closure_index_props g' h_index i /\
                                (let succ_index = Usize.add h_index (Usize.mul i mword) in
                                  (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8) /\
                                  (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8) /\
                                  (read_word g succ_index = read_word g' succ_index) /\
                                  wosize_of_object1 (hd_address (read_word g succ_index)) g = wosize_of_object1 (hd_address (read_word g succ_index)) g'))
                       
                     (ensures (parent_closure_of_infix_object g h_index i == parent_closure_of_infix_object g' h_index i)) =
 assert (well_formed_heap2 g);
 assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
 
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 assert  (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                               is_fields_contents_within_limit2 x (getWosize (read_word g x)) g /\
                      is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g));
 assert (is_fields_points_to_blocks2 h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
 assert (is_fields_points_to_blocks2_post_condition h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
 let succ_index = Usize.add h_index (Usize.mul i mword) in
 lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
 lemma_len_slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
 let succ = read_word g succ_index in
 let succ1 = read_word g' succ_index in
 assert (succ == succ1);
 assert ((Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) == infix_tag) /\
        (UInt.fits (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) - 
                                                   (Usize.v (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) * Usize.v mword)) Usize.n) /\
          (
                                                       (let actual_succ = (Usize.sub (read_word g (Usize.add h_index (Usize.mul i mword))) 
                                                       (Usize.mul (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) mword)) in
                                                        (Usize.v actual_succ >= Usize.v mword) /\
                                                        (is_hp_addr actual_succ) /\
                                                        (Usize.v (tag_of_object1 (hd_address actual_succ) g) == closure_tag) /\
                                                        (Seq.mem (hd_address actual_succ) (get_allocated_block_addresses g)))));
 let hdr_succ = hd_address succ in
 let wsize_succ = wosize_of_object1 hdr_succ g in
 let wsize_succ_offset = Usize.mul wsize_succ mword in
 let actual_succ = Usize.sub succ wsize_succ_offset in

 let hdr_actual_succ = hd_address actual_succ in
 assert (hdr_actual_succ == parent_closure_of_infix_object g h_index i);
 let wsize_succ1 = wosize_of_object1 hdr_succ g' in
 assert (wsize_succ == wsize_succ1);
 assert (is_valid_header1 h_index g');
 assert ((Usize.v i < Usize.v (getWosize (read_word g' h_index)) + 1 /\ Usize.v i >= 1) /\
                                               isPointer (succ_index_fn g' h_index i) g' /\
                                               (UInt.fits (Usize.v (read_succ g' h_index i) - Usize.v mword) Usize.n) /\
                                               (Usize.v (tag_of_object1 (hd_address (read_succ g' h_index i)) g') == infix_tag));
 assert (parent_closure_of_infix_object g' h_index i == parent_closure_of_infix_object g h_index i);
 ()
  


#restart-solver


#restart-solver

#push-options "--split_queries always"

#restart-solver

let get_allocs_props (g:heap{well_formed_heap2 g}) =
    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
    (forall j x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)

#restart-solver 

#restart-solver

//#reset-options "--z3rlimit 1000"

#restart-solver

let rec create_edge_pairs_for_h_index_lemma1 (g:heap{well_formed_heap2 g}) 
                                             (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                             (wz: wosize{valid_wosize g h_index wz})
                         
                                             (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                                             (v_id:hp_addr{is_valid_header1 v_id g})

                                             (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})

                                             (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })

                                             (wz1: wosize{(wz1 == getWosize (read_word g' h_index))})
                                             
                        : Lemma
                          (requires (objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    (wz == wz1) /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                    (get_allocs_props g) /\ (get_allocs_props g')
                                    
                                    )
                          (ensures (create_edge_pairs_for_h_index g h_index wz i == create_edge_pairs_for_h_index g' h_index wz1 i))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 
if Usize.v i = Usize.v wz + 1 then
    (
       let e = Seq.empty #G.edge in
       length_empty_generic_lemma e;
       assert (Seq.length e == 0);
       (*assert ((Seq.length e == (Usize.v wz + 1) - Usize.v i));*)
       ()
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      lemma_len_slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 
           ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      let succ1 = read_word g' succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
      succ_index_lemma g h_index wz i;
      assert (~(Seq.mem succ_index (objects2 0UL g)));
      assert (Seq.mem v_id (objects2 0UL g));
      assert (succ_index <> v_id);
      assert (succ == succ1);
       
      assert (Usize.v succ_index < heap_size);
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
        
      let e' = create_edge_pairs_for_h_index g h_index wz i' in
      let e1 = create_edge_pairs_for_h_index g' h_index wz1 i' in
      
      create_edge_pairs_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;
      assert (e' == e1);
      if isPointer succ_index g  then
      (
        
         assert (isPointer succ_index g');
         let h_addr_succ = hd_address succ in
        
         let f_index = f_address h_index in
         f_address_hp_address_lemma h_index;
         assert (hd_address f_index == h_index);
         assert (read_word g (Usize.add h_index (Usize.mul i mword)) == read_word g' (Usize.add h_index (Usize.mul i mword)));
         colorHeader1_tags_lemma v_id g c g';
         assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g == tag_of_object1 x g');
         assert (Usize.v (tag_of_object1 h_addr_succ g) == Usize.v (tag_of_object1 h_addr_succ g'));
         if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
         (
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           let parent_hdr1 = parent_closure_of_infix_object g' h_index i in
           field_limits_allocated_blocks_lemma g;
           field_contents_within_limits_allocated_blocks_lemma g;
           field_limits_allocated_blocks_lemma g';
           field_contents_within_limits_allocated_blocks_lemma g';
           field_points_to_blocks_allocs_lemma g;
           field_points_to_blocks_allocs_lemma g';
           assert (allocs_props_g g h_index);
           assert (allocs_props_g g' h_index);
           assert (parent_closure_index_props g' h_index i);
           colorHeader1_wosize_lemma v_id g c g';
           parent_closure_of_infix_object_lemma  g h_index i v_id c g';
           assert (parent_hdr == parent_hdr1);
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
           assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
           let parent_succ = f_address parent_hdr in
           let edge_pair = (f_index,parent_succ) in
           assert (hd_address (fst edge_pair) == h_index);
           assert (fst edge_pair == f_index);
           assert (snd edge_pair == parent_succ);
           assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
           assert (well_formed_heap2 g);
           assert (check_fields_points_to_blocks2 g (get_allocated_block_addresses g));
           assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                        is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g));
           assert (Seq.mem h_index (get_allocated_block_addresses g));
           assert (is_fields_points_to_blocks2 h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));  
           assert (is_fields_points_to_blocks2_post_condition h_index g (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
           assert ((Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) == infix_tag) /\
                              (UInt.fits (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) - 
                                                   (Usize.v (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) * Usize.v mword)) Usize.n) /\
          (
                                                       (let actual_succ = (Usize.sub (read_word g (Usize.add h_index (Usize.mul i mword))) 
                                                       (Usize.mul (wosize_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) mword)) in
                                                        (Usize.v actual_succ >= Usize.v mword) /\
                                                        (is_hp_addr actual_succ) /\
                                                        (Usize.v (tag_of_object1 (hd_address actual_succ) g) == closure_tag) /\
                                                        (Seq.mem (hd_address actual_succ) (get_allocated_block_addresses g)))
           ));
           assert (hd_address parent_succ == parent_hdr);
           assert (parent_hdr ==  parent_closure_of_infix_object g h_index i);
           assert (is_valid_header1 parent_hdr g);
           assert (parent_hdr == (hd_address (snd edge_pair)));
           assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
           lemma_tl edge_pair e'; 
        
           let e = Seq.cons edge_pair e' in 
           cons_property_lemma5 g h_index e' edge_pair;
           create_edge_pairs_for_h_index_lemma_rec_lemma_infix g' h_index wz1 i i';
           assert (isPointer (Usize.add h_index (Usize.mul i mword)) g' /\ 
                     Usize.v (tag_of_object1 (hd_address (read_word g' (Usize.add h_index (Usize.mul i mword)))) g') == infix_tag ==> 
             create_edge_pairs_for_h_index g' h_index wz1 i == Seq.cons (f_index,(f_address (parent_closure_of_infix_object g' h_index i))) 
                                                              (create_edge_pairs_for_h_index g' h_index wz1 i'));
           ()
         )
         else
         (

           let edge_pair = (f_index,succ) in
           let edge_pair1 = (f_index,succ1) in
           assert (hd_address (fst edge_pair) == h_index);
           assert (fst edge_pair == f_index);
           assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
           assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
           lemma_tl edge_pair e'; 
        
           let e = Seq.cons edge_pair e' in 
           let e2 = Seq.cons edge_pair1 e1 in 
           cons_property_lemma5 g h_index e' edge_pair;
           assert (edge_pair == edge_pair1);
           assert (e == e2);
           assert (create_edge_pairs_for_h_index g h_index wz i == e);
           create_edge_pairs_for_h_index_lemma_rec_lemma_non_infix g' h_index wz1 i i';
           assert (isPointer (Usize.add h_index (Usize.mul i mword)) g' /\ 
                     Usize.v (tag_of_object1 (hd_address (read_word g' (Usize.add h_index (Usize.mul i mword)))) g') <> infix_tag ==> 
                         create_edge_pairs_for_h_index g' h_index wz1 i == Seq.cons (f_index,succ1) (create_edge_pairs_for_h_index g' h_index wz1 i'));
           assert (create_edge_pairs_for_h_index g' h_index wz1 i == e2);
           ()
         )
      )
      else
      (
        ()
      )
    )

//#reset-options "--z3rlimit 1000"

#restart-solver

let well_formed_closure_objs_lemma (g:heap{well_formed_heap2 g})
                                   (hd:hp_addr{is_valid_header1 hd g}) 
                    : Lemma
                      (requires Usize.v (tag_of_object1 hd g) < no_scan_tag /\
                                Usize.v (tag_of_object1 hd g) = closure_tag) 
                      (ensures (Usize.v (wosize_of_object1 hd g) >= 2 /\
                                is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) /\
                                Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) + 1 <= Usize.v (wosize_of_object1 hd g) /\
                                Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) >= 1)) =
 assert (check_well_formed_closure_objs g (get_allocated_block_addresses g));
 assert (closure_obj_props1 g (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> Usize.v (tag_of_object1 x g) = closure_tag ==> 
                              Usize.v (wosize_of_object1 x g) >= 2 /\
                              is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) /\
                              Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) + 1 <= Usize.v (wosize_of_object1 x g) /\
                              Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address x))) >= 1);
 assert (Seq.mem hd (get_allocated_block_addresses g));
 assert (Usize.v (wosize_of_object1 hd g) >= 2 /\
         is_hp_addr (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) /\
         Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) + 1 <= Usize.v (wosize_of_object1 hd g) /\
         Usize.v (extract_start_env_bits (closinfo_val_from_closure_object g (f_address hd))) >= 1);
 ()

#reset-options "--z3rlimit 100"


let colorHeader_props_lemma (g:heap{well_formed_heap2 g}) 
                            (v_id:hp_addr{is_valid_header1 v_id g})
                            (c:color{c == 3UL \/ c == 2UL \/ c == 1UL}) 
                            (g':heap{well_formed_heap2 g'})
                 : Lemma 
                   (requires (Seq.equal g' (colorHeader1 v_id g c)))
                   (ensures  (g' == colorHeader1 v_id g c)) =
 ()

(*let create_edge_list_from_heap_rec_lemma  (g:heap{well_formed_heap2 g}) 
                                          (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                            within_heap_all f /\
                                                            multiple_of_mword_all f /\
                                                            all_valid_headers f g /\
                                                            (G.is_vertex_set f) /\
                                                            all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                            all_field_address_are_word_aligned  f g})
                                           
                                          
                        : Lemma
                          (requires (Seq.length f > 0) /\
                                    Usize.v (tag_of_object1 (Seq.head f) g) < no_scan_tag /\
                                    Usize.v (tag_of_object1 (Seq.head f) g) = closure_tag)
                          (ensures create_edge_list_from_heap1 g f == 
                                     Seq.append (create_edge_pairs_for_h_index g (Seq.head f) (getWosize (read_word g (Seq.head f))) 
                                     (Usize.add (start_env_clos_info g (f_address (Seq.head f))) 1UL)) (create_edge_list_from_heap1 g (Seq.tail f))) =
 admit()
*)

let seq_head_tail_equality_lemma (f: seq Usize.t)
                                 (f1: seq Usize.t)
                 : Lemma
                   (requires (Seq.length f > 0) /\
                             (f == f1))
                   (ensures (Seq.head f == Seq.head f1) /\
                            (Seq.tail f == Seq.tail f1)) =
()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#push-options "--split_queries always"

#restart-solver

let rec create_edge_list_from_heap_lemma  (g:heap{well_formed_heap2 g}) 
                                          (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                            within_heap_all f /\
                                                            multiple_of_mword_all f /\
                                                            all_valid_headers f g /\
                                                            (G.is_vertex_set f) /\
                                                            all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                            all_field_address_are_word_aligned  f g})
                                           
                                           (v_id:hp_addr{is_valid_header1 v_id g})
                                           
                                           (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                                           
                                           (g':heap{well_formed_heap2 g' /\ Seq.equal g' (colorHeader1 v_id g c)})
                                           (f1: seq Usize.t {all_mem_of_allocated_blocks f1 g' /\
                                                             within_heap_all f1 /\
                                                             multiple_of_mword_all f1 /\
                                                             all_valid_headers f1 g' /\
                                                             (G.is_vertex_set f1) /\
                                                             all_objects_and_their_field_pointers_are_within_heap_size f1 g' /\
                                                             all_field_address_are_word_aligned f1 g'})
                          : Lemma
                           (requires (f == f1))
                           (ensures (create_edge_list_from_heap1 g f == create_edge_list_from_heap1 g' f1))
                           (decreases (Seq.length f)) = 
if length f = 0 then 
 (
   let e = Seq.empty #G.edge in
   seq_empty_lemma ();
   
   
   seq_empty_lemma1 f;
   
   ()
 )
 else
 (
   
   seq_non_empty_lemma f;
   let hd = Seq.head f in
   let hd1 = Seq.head f1 in
   assert (is_hp_addr hd);
   can_shift_forward_lemma f g hd;
   assert (Usize.v hd + Usize.v mword < heap_size);
   let tl = Seq.tail f in
   let tl1 = Seq.tail f1 in
   
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));
   
   assert (Seq.length f > Seq.length tl);
   assert (Seq.length f > Seq.length (Seq.tail f));
   length_fn_lemma f;
   assert (length_fn f > length_fn (Seq.tail f));
   assert (length_fn f > length_fn tl);

   seq_head_tail_equality_lemma f f1;
   
   let rest_of_f = create_edge_list_from_heap1 g tl in
   let rest_of_f1 = create_edge_list_from_heap1 g' tl in
   create_edge_list_from_heap_lemma g tl v_id c g' tl;
   assert (create_edge_list_from_heap1 g tl == create_edge_list_from_heap1 g' tl);
   
   let tg = tag_of_object1 hd g in
   colorHeader1_tags_lemma v_id g c g';
   
   if (Usize.v tg < no_scan_tag) then 
   (
     let wz = getWosize (read_word g hd) in
     let wz1 = getWosize (read_word g' hd) in
     let f_id = f_address hd in
     f_address_lemma tl hd;
     assert (forall y. Seq.mem y tl ==> f_address hd <> f_address y);
     assert (hd_address f_id == hd);
     
     colorHeader1_wosize_lemma v_id g c g';
     colorHeader1_alloc_colors_lemma v_id g c;
     colorHeader_props_lemma g v_id c g';
     
     
     field_limits_allocated_blocks_lemma g;
     field_contents_within_limits_allocated_blocks_lemma g;
     fieldaddress_within_limits_lemma_x_all g;
     
     if (Usize.v tg = closure_tag) then
     (
       assert (is_valid_header1 hd g /\
               Usize.v (tag_of_object1 hd g) < no_scan_tag /\
               Usize.v (tag_of_object1 hd g) = closure_tag);
       well_formed_closure_objs_lemma g hd;
       assert (Usize.v wz >= 2);
       assert (Usize.v f_id >= Usize.v mword);
       assert (is_valid_header1 hd g);
       assert (is_valid_header1 (hd_address f_id) g);
       assert (Usize.v (tag_of_object1 (hd_address f_id) g) == closure_tag);
       let start_env = start_env_clos_info g f_id in
       let start_env_plus_one = Usize.add start_env 1UL in

       assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address f_id) g)) /\
             Usize.v start_env >= 1);
       let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz start_env_plus_one in
       //colorHeader1_wosize_lemma v_id g c g';
       assert (wz == wz1);
       assert (Usize.v start_env_plus_one <= Usize.v wz1 + 1 /\ Usize.v start_env_plus_one >= 1);
       let edge_pairs_for_hd1 = create_edge_pairs_for_h_index g' hd wz1 start_env_plus_one in
       //colorHeader1_alloc_colors_lemma v_id g c;
       //colorHeader_props_lemma g v_id c g';
       assert (g' == colorHeader1 v_id g c);
       assert ((objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    (wz == wz1) /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses g'));
       assert ((get_allocs_props g) /\ (get_allocs_props g'));
       create_edge_pairs_for_h_index_lemma1 g hd wz start_env_plus_one v_id c g' wz1;
       
       
       let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
       Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
       assert (edge_pairs_for_hd == edge_pairs_for_hd1);
       assert (rest_of_f == rest_of_f1);

       let f2 = Seq.append (edge_pairs_for_hd1) (rest_of_f1) in
  
   
       Seq.lemma_mem_append (edge_pairs_for_hd1) (rest_of_f1);
       assert (f' == f2);
       assert (f' == create_edge_list_from_heap1 g f);
       assert (hd == hd1);
       assert (tl == tl1);
       let start_env1 = start_env_clos_info g' f_id in
       start_env_clos_info_lemma g f_id v_id c;
       assert (start_env == start_env1);
       assert (f2 == create_edge_list_from_heap1 g' f1);
       assert (create_edge_list_from_heap1 g f == create_edge_list_from_heap1 g' f1);
       ()
     )
     else
     (
       let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz 1UL in
       let edge_pairs_for_hd1 = create_edge_pairs_for_h_index g' hd1 wz1 1UL in
       
       let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
       let f2 = Seq.append (edge_pairs_for_hd1) (rest_of_f1) in 
   
       Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
       Seq.lemma_mem_append (edge_pairs_for_hd1) (rest_of_f1);
       assert (hd == hd1);
       assert (tl == tl1);


       assert (wz == wz1);
       create_edge_pairs_for_h_index_lemma1 g hd wz 1UL v_id c g' wz1;
       assert (edge_pairs_for_hd ==  edge_pairs_for_hd1);
       assert (rest_of_f == rest_of_f1);
       assert (f' == f2);
       assert (f' == create_edge_list_from_heap1 g f);
       assert (f2 == create_edge_list_from_heap1 g' f1);
       assert (create_edge_list_from_heap1 g f == create_edge_list_from_heap1 g' f1);
       ()
     )
   )
   else
   (
     (*branch type checked when other branches are commented out*)
     let edge_pairs_for_hd = Seq.empty #G.edge in
     let edge_pairs_for_hd1 = Seq.empty #G.edge in
     seq_empty_lemma ();
     
     let f_id = f_address hd in
     assert (hd_address f_id == hd);
   
    
     let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
     let f2 = Seq.append (edge_pairs_for_hd1) (rest_of_f1) in
  
   
     Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
     Seq.lemma_mem_append (edge_pairs_for_hd1) (rest_of_f1);
   
   
     
     Seq.append_empty_l rest_of_f;
     Seq.append_empty_l rest_of_f1;
     
     assert (f' == rest_of_f);
     assert (f2 == rest_of_f1);
     assert (f' == f2);
     assert (f' == create_edge_list_from_heap1 g f);
     assert (f2 == create_edge_list_from_heap1 g' f1);
     assert (create_edge_list_from_heap1 g f == create_edge_list_from_heap1 g' f1);
     ()
   )
)

#reset-options "--z3rlimit 500"


let create_edge_list_for_graph_lemma (g:heap{well_formed_heap2 g}) 
                                     (v_id:hp_addr{is_valid_header1 v_id g})
                                     (c:color{c == 3UL \/ c== 2UL \/ c == 1UL})
                    : Lemma 
                      (requires (well_formed_heap2(colorHeader1 v_id g c)))
                      (ensures (create_edge_list_for_graph g == create_edge_list_for_graph (colorHeader1 v_id g c))) = 
  let allocs = get_allocated_block_addresses g in

  field_limits_allocated_blocks_lemma g;
  field_contents_within_limits_allocated_blocks_lemma g;
  fieldaddress_within_limits_lemma_x_all g;
  
  let f  = create_edge_list_from_heap1 g allocs in
  
  let g' = colorHeader1 v_id g c in
  let allocs' = get_allocated_block_addresses g' in
  colorHeader1_alloc_colors_lemma v_id g c;
  
  assert (allocs == allocs');

  field_limits_allocated_blocks_lemma g';
  field_contents_within_limits_allocated_blocks_lemma g';
  fieldaddress_within_limits_lemma_x_all g';
  
  let f' = create_edge_list_from_heap1 g' allocs' in
  
  create_edge_list_from_heap_lemma g allocs v_id c g' allocs';
  assert (f == f');
  ()

let can_be_shift_forward_lemma (wz:Usize.t{Usize.v wz > 0})
               (x:Usize.t{Usize.v x + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size})
          : Lemma
            (ensures (Usize.v x + Usize.v mword < heap_size)) = 
assert (Usize.v wz > 0);
assert (Usize.v x + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size);
assert (Usize.v x + Usize.v mword < heap_size);
()

let can_be_shift_forward_lemma1  (g:heap{well_formed_heap2 g})
                                 (f: seq Usize.t { all_mem_of_allocated_blocks f g /\
                                                            within_heap_all f /\
                                                            multiple_of_mword_all f /\
                                                            all_valid_headers f g /\
                                                            (G.is_vertex_set f) /\
                                                            all_objects_and_their_field_pointers_are_within_heap_size f g /\
                                                            all_field_address_are_word_aligned  f g})
                           : Lemma
                             (ensures  (forall x. Seq.mem x f ==> Usize.v x + Usize.v mword < heap_size)) = 
 assert (forall x. Seq.mem x f ==> Usize.v (getWosize (read_word g x)) > 0);
 assert (forall x. Seq.mem x f ==> Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1) < heap_size);
 assert (forall x. Seq.mem x f ==> Usize.v x + Usize.v mword < heap_size);
 ()

#restart-solver 

let create_graph_from_heap_lemma (g:heap {well_formed_heap2 g})
                                 (v_id:hp_addr{is_valid_header1 v_id g})
                                 (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                         : Lemma 
                           (requires (well_formed_heap2 (colorHeader1 v_id g c) /\
                                      (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)))
                           (ensures (create_graph_from_heap g == create_graph_from_heap (colorHeader1 v_id g c))) = 
 let f = get_allocated_block_addresses g in 
 assert ((all_mem_of_allocated_blocks f g) /\
          (within_heap_all f) /\
          (multiple_of_mword_all f) /\
          (all_valid_headers f g) /\
          (G.is_vertex_set f));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 can_be_shift_forward_lemma1 g f;
 assert (can_be_shifted_forward f);
 assert (all_objects_and_their_field_pointers_are_within_heap_size f g);
 assert (all_field_address_are_word_aligned f g); 
 let ff_allocs = first_field_addresses_of_allocated_blocks g f in 

 let g' = colorHeader1 v_id g c in
 let f' = get_allocated_block_addresses g' in
 get_allocated_block_addresses_lemma g g' v_id c;
 assert (f == f');

 field_limits_allocated_blocks_lemma g';
 field_contents_within_limits_allocated_blocks_lemma g';
 fieldaddress_within_limits_lemma_x_all g';
 can_be_shift_forward_lemma1 g' f';
 assert (can_be_shifted_forward f');
 let ff_allocs' = first_field_addresses_of_allocated_blocks g' f' in 
 first_field_addresses_of_allocated_blocks_lemma g f g' f';
 assert (ff_allocs == ff_allocs');
 
 create_edge_list_for_graph_lemma g v_id c;
 assert (create_edge_list_for_graph g == create_edge_list_for_graph g');
 
 let grph1 = create_graph_from_heap g in
 let grph2 = create_graph_from_heap g' in
 assert (grph1 == grph2);
 ()


#restart-solver 

//#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let create_graph_from_heap_lemma_gray (g:heap {well_formed_heap2 g})
                                 (v_id:hp_addr{is_valid_header1 v_id g})
                           : Lemma 
                           (requires (well_formed_heap2 (colorHeader1 v_id g 2UL) /\
                                      (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)))
                           (ensures (create_graph_from_heap g == create_graph_from_heap (colorHeader1 v_id g 2UL))) =
 create_graph_from_heap_lemma g v_id 2UL

#reset-options "--z3rlimit 500"

let tail_cons (#a:eqtype)
              (s: seq a)
              (x: a)
        : Lemma
          (ensures (Seq.tail (Seq.cons x s) == s)) = 
 lemma_tl x s;
 ()
          
let cons_length_lemma2 (#a:Type)
                       (s:seq a)
                       (s_cons:a)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s)) > 0)=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ; 
 ()

let cons_length_lemma1 (#a:Type)
                       (s:seq a)
                       (s_cons:a)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s)) == Seq.length s + 1)=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ; 
 ()



#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let rec create_successors_pick_second_lemma (g:heap{well_formed_heap2 g}) 
                                            (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                            (wz: wosize{valid_wosize g h_index wz})
                         
                                            (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                           : Lemma
                             (ensures (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == 
                                          create_successors_list_for_h_index g h_index wz i))
                             (decreases ((Usize.v wz + 1) - Usize.v i)) = 
if Usize.v i = Usize.v wz + 1 then
(
  seq_empty_lemma ();
  assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);
  ()
)
else
(
  let i' = Usize.(i +^ 1UL) in
  assert (is_valid_header h_index g);  
  assert (Usize.v i < Usize.v wz + 1);
  assert (Usize.v i' <= Usize.v wz + 1);
  assert (Seq.mem h_index (objects2 0UL g));
  assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
  assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

  field_limits_allocated_blocks_lemma g;
  field_contents_within_limits_allocated_blocks_lemma g;
  fieldaddress_within_limits_lemma_x_all g;
        
  assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
  assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
  assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);

  lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
  assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 
           ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
  assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
  assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));
       
  assert (Usize.v succ_index < heap_size);
  assert (Usize.v i' > 1);
  assert (Usize.v i < Usize.v wz + 1);
  assert (Usize.v i' <= Usize.v wz + 1);
        
  let s_list' = create_successors_list_for_h_index g h_index wz i' in
  let e' = create_edge_pairs_for_h_index g h_index wz i' in
  create_successors_pick_second_lemma g h_index wz i';
  assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i') == create_successors_list_for_h_index g h_index wz i');
  if isPointer succ_index g  then
      (
        
         let h_addr_succ = hd_address succ in
        
         let f_index = f_address h_index in
         f_address_hp_address_lemma h_index;
         assert (hd_address f_index == h_index);
         if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
         (
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
           assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
           let parent_succ = f_address parent_hdr in
           lemma_tl parent_succ s_list'; 
        
           let s_list = Seq.cons parent_succ s_list' in 
           cons_length_lemma2 s_list' parent_succ;
           Seq.head_cons parent_succ s_list';
        
           assert (Seq.head s_list == parent_succ);

           let edge_pair = (f_index,parent_succ) in
           lemma_tl edge_pair e'; 
           let e = Seq.cons edge_pair e' in 
        
           cons_length_lemma2 e' edge_pair;
           Seq.head_cons  edge_pair e'; 
           assert (Seq.head e == edge_pair);
           assert (s_list == Seq.cons parent_succ (G.pick_second e'));
           assert (Seq.cons parent_succ (G.pick_second e') == s_list);

           assert (parent_succ == snd (edge_pair));

           assert (Seq.cons (snd edge_pair) (G.pick_second e') == s_list);

           cons_length_lemma1 e' edge_pair; 
           assert (Seq.length e > 0);

           tail_cons e' edge_pair;
           assert (Seq.tail e == e');

           G.pick_second_lemma e;
      
           assert (G.pick_second e == Seq.cons (snd edge_pair) (G.pick_second e'));

           assert (G.pick_second e == s_list);
           assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);

           ()
         )
         else
         (
           
           lemma_tl succ s_list'; 
        
           let s_list = Seq.cons succ s_list' in 
           cons_length_lemma2 s_list' succ;
           Seq.head_cons succ s_list';
        
           assert (Seq.head s_list == succ);

           let edge_pair = (f_index,succ) in
           lemma_tl edge_pair e'; 
           let e = Seq.cons edge_pair e' in 
        
           cons_length_lemma2 e' edge_pair;
           Seq.head_cons  edge_pair e'; 
           assert (Seq.head e == edge_pair);
           assert (s_list == Seq.cons succ (G.pick_second e'));
           assert (Seq.cons succ (G.pick_second e') == s_list);

           assert (succ == snd (edge_pair));

           assert (Seq.cons (snd edge_pair) (G.pick_second e') == s_list);

           cons_length_lemma1 e' edge_pair; 
           assert (Seq.length e > 0);

           tail_cons e' edge_pair;
           assert (Seq.tail e == e');

           G.pick_second_lemma e;
      
           assert (G.pick_second e == Seq.cons (snd edge_pair) (G.pick_second e'));

           assert (G.pick_second e == s_list);
           assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);

        
           assert (Seq.head s_list == succ);

           ()
         )
      )
      else
      (
       
        assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i') == create_successors_list_for_h_index g h_index wz i');
        assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);
        ()
      )
)

let succ_props_pre (g: heap {well_formed_heap2 g})
                   (h_index:hp_addr{is_valid_header1 h_index g}) =
 (is_fields_within_limit1 h_index (getWosize (read_word g h_index)) /\
  is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g /\                                                                    
 (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
            (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\                                                       
 (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
 (Seq.mem (f_address h_index) ((create_graph_from_heap g).vertices)))

#restart-solver 

#reset-options "--z3rlimit 500"

#restart-solver

let succ_props (g: heap {well_formed_heap2 g})
               (h_index:hp_addr{is_valid_header1 h_index g /\
                                succ_props_pre g h_index}) =                                        
   (*1*) (Usize.v (tag_of_object1 h_index g) < no_scan_tag ==> 
            (Usize.v (tag_of_object1 h_index g) == closure_tag) ==>
                                                
               (let f_id = f_address h_index in
                let start_of_env = start_env_clos_info g f_id in
                let start_of_env_plus_one = Usize.add start_of_env 1UL in
                   (G.successors (create_graph_from_heap g) (f_address h_index) == 
                      create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one))) /\
                                  
   (*2*)  (Usize.v (tag_of_object1 h_index g) < no_scan_tag ==>
            (Usize.v (tag_of_object1 h_index g) <> closure_tag) ==>
                   (G.successors (create_graph_from_heap g) (f_address h_index) == 
                      create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL)) /\
                                           
   (*3*)  (Usize.v (tag_of_object1 h_index g) >= no_scan_tag ==> 
                   (G.successors (create_graph_from_heap g) (f_address h_index) == Seq.empty #UInt64.t))    

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver 

let graph_successors_heap_create_successor_list_equivalence_lemma (g: heap {well_formed_heap2 g})
                                                                  (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g})
                                : Lemma
                                  (requires succ_props_pre g h_index)
                                  
                                  (ensures  succ_props g h_index) = 
 let allocs = get_allocated_block_addresses g in
 assert (G.is_vertex_set allocs);
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 let grph = create_graph_from_heap g in
 let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in 
 assert (Seq.equal (grph.vertices) ff_allocs);
 assert (forall x. Seq.mem x allocs <==> Seq.mem (f_address x) ff_allocs);
 assert (Seq.mem (f_address h_index) (ff_allocs));
 let f_h_index = f_address h_index in 
 G.successors_successors_fn2_connect_lemma grph f_h_index; 
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index grph.edge_set);
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_for_graph g));
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs));
 assert (Seq.mem h_index allocs); 
 let tg = tag_of_object1 h_index g in
 assert (edge_graph_succ_connect3 g allocs (create_edge_list_from_heap1 g allocs));
 if (Usize.v tg < no_scan_tag) then 
 (
   f_address_hp_address_lemma h_index;
   assert (hd_address f_h_index == h_index);
   if (Usize.v tg = closure_tag) then
    (
      let start_env = start_env_clos_info g f_h_index in
      let start_of_env_plus_one = Usize.add start_env 1UL in
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one in 
      
      assert (G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs) ==  G.successors_fn2 f_h_index h_index_edge_list);
                                          
      assert (G.successors grph f_h_index == G.successors_fn2 f_h_index h_index_edge_list);
      G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;

      assert (G.successors_fn2 f_h_index h_index_edge_list ==
              G.pick_second h_index_edge_list);
      create_successors_pick_second_lemma g h_index (getWosize (read_word g h_index)) start_of_env_plus_one;
      
      assert (G.pick_second h_index_edge_list == 
           create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one);
      
      assert (G.successors_fn2 f_h_index h_index_edge_list ==
             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one);
      
      assert (G.successors grph f_h_index ==  
             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one);
      
      assert (G.successors (create_graph_from_heap g) f_h_index == 
              create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) start_of_env_plus_one);
      assert (succ_props g h_index);
      ()
    )
    else
    (
      
      let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL in 
      
      assert (G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs) ==  G.successors_fn2 f_h_index h_index_edge_list);
                                          
      assert (G.successors grph f_h_index == G.successors_fn2 f_h_index h_index_edge_list);
      G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;

      assert (G.successors_fn2 f_h_index h_index_edge_list ==
              G.pick_second h_index_edge_list);
      create_successors_pick_second_lemma g h_index (getWosize (read_word g h_index)) 1UL;
      
      assert (G.pick_second h_index_edge_list == 
           create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
      
      assert (G.successors_fn2 f_h_index h_index_edge_list ==
             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
      
      assert (G.successors grph f_h_index ==  
             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
      
      assert (G.successors (create_graph_from_heap g) f_h_index == 
              create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
      assert (succ_props g h_index);
      ()
    )
      
 )
 else
 (
   assert ( G.successors_fn2 f_h_index (create_edge_list_from_heap1 g allocs) ==  Seq.empty #UInt64.t);
   assert (G.successors grph f_h_index == Seq.empty #UInt64.t);
   assert (Usize.v (tag_of_object1 h_index g) >= no_scan_tag ==> 
                                                   G.successors (create_graph_from_heap g) (f_address h_index) == Seq.empty #UInt64.t);
   ()
 )

#reset-options "--z3rlimit 500"
#push-options "--split_queries always"


let is_visited   (v_id:hp_addr)
                 (g:heap)
          : Tot (b:bool{b == true <==>  (color_of_object1 v_id g) == black}) =
    if  (color_of_object1 v_id g) = black then true else false

let unvisited  (v_id:hp_addr)
               (g:heap{color_of_object1 v_id g == white \/
                       color_of_object1 v_id g == gray \/
                       color_of_object1 v_id g == black})
         : Tot (b:bool{(b == true <==> (~(is_visited v_id g) /\ ~(isGrayObject1 v_id g))) /\
                        (b == true <==> color_of_object1 v_id g == white)}) =
 if not(is_visited v_id g) && not(isGrayObject1 v_id g) then true
 else
  false 

let unvisited_lemma  (v_id:hp_addr)
                     (g:heap{color_of_object1 v_id g == white \/
                             color_of_object1 v_id g == gray \/
                             color_of_object1 v_id g == black})
            : Lemma
              (requires (color_of_object1 v_id g == gray \/
                         color_of_object1 v_id g == black))
              (ensures (color_of_object1 v_id g <> white)) = () 

let push_to_stack2_lemma_block_address (g:heap{well_formed_heap2 g})
                                       (st: seq Usize.t {stack_props_func g st})
                                       (x: hp_addr{is_valid_header1 x g /\
                                                   ~(Seq.mem (f_address x) st) /\
                                                  (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                  })  
                    : Lemma
                     (ensures (objects2 0UL g == objects2 0UL (snd (push_to_stack2 g st x)))) =
if Seq.length st = 0 then
(
   assert (Usize.v (tag_of_object1 x g) <> infix_tag);
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
   assert (Usize.v (tag_of_object1 x g') <> infix_tag);
   assert (Usize.v (tag_of_object1 (hd_address f_x) g') <> infix_tag);
   assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
   
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   ()
)
    
else
(
  assert (Usize.v (tag_of_object1 x g) <> infix_tag);
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
  assert (Usize.v (tag_of_object1 x g') <> infix_tag);
  assert (Usize.v (tag_of_object1 (hd_address f_x) g') <> infix_tag);
  assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g') <> infix_tag);
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  ()
)         

let push_to_stack2_lemma_valid_header (g:heap{well_formed_heap2 g})
                                      (st: seq Usize.t {stack_props_func g st})
                                      (x: hp_addr{is_valid_header1 x g /\
                                                   ~(Seq.mem (f_address x) st) /\
                                                  (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                  })
                   : Lemma
                     (ensures (forall y. is_valid_header1 y g ==> is_valid_header1 y (snd (push_to_stack2 g st x)))) =
  push_to_stack2_lemma_block_address g st x;
  ()

#restart-solver 

#restart-solver

let text_vl_props (g:heap{well_formed_heap2 g})
                  (vl: seq Usize.t {vl_props_func g vl}) =
 assert (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g);
 assert (forall x. Seq.mem x vl ==> is_valid_header1 (hd_address x) g);
 ()

#restart-solver

#restart-solver

let push_to_stack2_visited_list_valid_header_lemma  (g:heap{well_formed_heap2 g})
                                                    (st: seq Usize.t {stack_props_func g st})
                                                    (x: hp_addr{is_valid_header1 x g /\
                                                                ~(Seq.mem (f_address x) st) /\
                                                                (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                               })
                                                    (vl: seq Usize.t {vl_props_func g vl }) 
                        : Lemma
                          (ensures (forall y. Seq.mem y vl ==> is_valid_header1 (hd_address y) (snd (push_to_stack2 g st x)))) = 
 push_to_stack2_lemma_valid_header g st x; 
 ()

#restart-solver

#restart-solver
let push_to_stack2_lemma_gray_nodes_helper (g:heap{well_formed_heap2 g})
                                           (st: seq Usize.t {stack_props_func g st})
                                           (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st) /\
                                                (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                               })
                                           (y:hp_addr {is_valid_header1 y g /\ isGrayObject1 y g /\ x <> y})
                                      
                     : Lemma
                       (ensures is_valid_header1 y (snd (push_to_stack2 g st x)) /\ isGrayObject1 y (snd (push_to_stack2 g st x))) =
 if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
   assert (is_valid_header1 y g /\ isGrayObject1 y g /\ x <> y);
   assert (is_valid_header1 y g');
   assert (isGrayObject1 y g');
   assert (g' == snd (push_to_stack2 g st x));
   assert (isGrayObject1 y (snd (push_to_stack2 g st x)));
   assert (is_valid_header1 y (snd (push_to_stack2 g st x)));
   ()
)
    
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  assert (is_valid_header1 y g /\ isGrayObject1 y g /\ x <> y);
  assert (is_valid_header1 y g');
  assert (isGrayObject1 y g');
  assert (g' == snd (push_to_stack2 g st x));
  assert (isGrayObject1 y (snd (push_to_stack2 g st x)));
  assert (is_valid_header1 y (snd (push_to_stack2 g st x)));
  ()
)

let push_to_stack2_lemma_gray_nodes (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t {stack_props_func g st})
                                    (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st) /\
                                                (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                               })
                     : Lemma
                     (ensures (forall y. is_valid_header1 y g /\ isGrayObject1 y g /\ x <> y ==> is_valid_header1 y (snd (push_to_stack2 g st x)) /\
                                                                                      isGrayObject1 y (snd (push_to_stack2 g st x)))) = 
Classical.forall_intro (Classical.move_requires (push_to_stack2_lemma_gray_nodes_helper  g st x))

#restart-solver 

#reset-options "--z3rlimit 500" 

#push-options "--split_queries always"

#restart-solver

let colorHeader1_fields_lemma  (v_id:hp_addr)  
                              
                               (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g}) 
                               (c:color)
             : Lemma 
               (ensures    (*header coloring does not change wosize*)
                           (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word (colorHeader1 v_id g c) x)) /\

                           (*header coloring does not change field values*)
                           (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word (colorHeader1 v_id g c) y)) = 
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
 assert (Seq.length (objects2 0UL g) > 0);

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 assert (forall (x:hp_addr). x <> h_index ==> read_word g x == read_word g' x);
 assert (heap_remains_same_except_index_v_id h_index g g');
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). x <> h_index ==> getWosize (read_word g x) == getWosize (read_word g' x));
 assert (getWosize (read_word g h_index) == getWosize (read_word g' h_index));
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x));
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.mem v_id (objects2 0UL g'));
 
 assert (is_fields_contents_within_limit2 v_id wz g);
 
 
 assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> v_id ==>
                             read_word g x == read_word g' x);


 field_reads_all_equal_for_all_objects_lemma g g' h_index;
 field_reads_all_equal_h_index_lemma g g' h_index;
 assert ((forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y));
 ()

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000"

#restart-solver

let push_to_stack2_fields_allocated_blocks_lemma (g:heap{well_formed_heap2 g})
                                                 (st: seq Usize.t {stack_props_func g st})
                                                 (x: hp_addr{is_valid_header1 x g /\
                                                              ~(Seq.mem (f_address x) st) /\
                                                             (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                             ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                                             })
            : Lemma
              (ensures (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g t) == 
                                                                                   getWosize (read_word (snd (push_to_stack2 g st x)) t)) /\

                           (*header coloring does not change field values*)
                           (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (push_to_stack2 g st x)) y)) =
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   colorHeader1_fields_lemma x g gray;
   ()
)
    
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  colorHeader1_fields_lemma x g gray;
  ()
)

#restart-solver

#restart-solver

let seq_not_empty_lemma (#a:eqtype)
                        (s:seq a) 
           : Lemma
             (requires ~(Seq.length s = 0))
             (ensures Seq.length s > 0) =
()

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver 

let is_valid_header_color_lemma (g:heap{well_formed_heap2 g})
                                (y:hp_addr{(is_valid_header y g)})
                 : Lemma
                   (requires (color_of_object1 y g == black \/ color_of_object1 y g == gray \/ color_of_object1 y g == white))
                   (ensures (is_valid_header1 y g)) =
()
                                                                               
#push-options "--split_queries always"

#restart-solver 

let push_to_stack2_lemma_black_nodes_helper (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t {stack_props_func g st})
                                     (x: hp_addr{is_valid_header1 x g /\
                                                              ~(Seq.mem (f_address x) st) /\
                                                             (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                             ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                                             })
                                     (y:hp_addr {is_valid_header1 y g /\ isBlackObject1 y g /\ x <> y})
                     : Lemma
                       (ensures (is_valid_header1 y (snd (push_to_stack2 g st x)) /\ isBlackObject1 y (snd (push_to_stack2 g st x)))) =
 if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   get_allocated_block_addresses_lemma g g' x 2UL;
   assert (is_valid_header1 y g /\ isBlackObject1 y g /\ x <> y);
   colorHeader1_alloc_colors_lemma x g gray;
   assert (heap_remains_same_except_index_v_id x g g');
   assert (color_of_object1 y g' == black);
   assert (isBlackObject1 y g');
   assert (is_valid_header y g);
   assert (is_valid_header y g');
   is_valid_header_color_lemma g' y;
   assert (is_valid_header1 y g');
   assert (g' == snd (push_to_stack2 g st x));
   assert (is_valid_header1 y g' /\ isBlackObject1 y g');
   ()
)
    
else
(
  seq_not_empty_lemma st;
  assert (Seq.length st > 0);
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  get_allocated_block_addresses_lemma g g' x 2UL;
  assert (heap_remains_same_except_index_v_id x g g');
  assert (color_of_object1 y g' == black);
  assert (isBlackObject1 y g');
  assert (is_valid_header y g);
  assert (is_valid_header y g');
  is_valid_header_color_lemma g' y;
  assert (is_valid_header1 y g');
  assert (g' == snd (push_to_stack2 g st x));
  assert (is_valid_header1 y g' /\ isBlackObject1 y g');
  ()
)


let push_to_stack2_lemma_black_nodes (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t {stack_props_func g st})
                                     (x: hp_addr{is_valid_header1 x g /\
                                                              ~(Seq.mem (f_address x) st) /\
                                                             (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                             ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                                             })
                   : Lemma
                     (ensures (forall y. is_valid_header1 y g /\ isBlackObject1 y g /\ x <> y ==> 
                                    is_valid_header1 y (snd (push_to_stack2 g st x)) /\ isBlackObject1 y (snd (push_to_stack2 g st x)))) =
Classical.forall_intro (Classical.move_requires (push_to_stack2_lemma_black_nodes_helper g st x))

#restart-solver 

#restart-solver

#push-options "--z3rlimit 500"

#push-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 4" 


#restart-solver

let colorHeader1_mem_lemma (v_id:hp_addr)  
                           (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g})
                 : Lemma 
                   (ensures (~(exists y. (Seq.mem y (objects2 0UL (colorHeader1 v_id g black)) /\
                                     isBlackObject1 y (colorHeader1 v_id g black)) /\
                                   ~(Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g) /\
                                    (v_id <> y)))) = 
 let g' = colorHeader1 v_id g black in
 colorHeader1_subset_lemma v_id g;
 assert (~(exists y. (Seq.mem y (objects2 0UL (colorHeader1 v_id g black)) /\
                                     isBlackObject1 y (colorHeader1 v_id g black)) /\
                                   ~(Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g) /\
                                    (v_id <> y)));
 ()

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver


let colorHeader1_mem_lemma_gray (v_id:hp_addr{ (Usize.v v_id >= 0 /\ Usize.v v_id < heap_size) /\
                                               (Usize.v v_id % Usize.v mword == 0)})  
                                (g:heap{well_formed_heap2 g /\ is_valid_header1 v_id g /\ (color_of_object1 v_id g == white) /\
                                        (is_fields_within_limit1 v_id (getWosize (read_word g v_id)))})
                 : Lemma 
                   (ensures (~(exists y. (Seq.mem y (get_black_block_addresses (colorHeader1 v_id g gray) 
                                                  (get_allocated_block_addresses (colorHeader1 v_id g gray)))) /\
                                    ~(Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)))))) = 
let g' = colorHeader1 v_id g gray in
//assert (well_formed_heap2 g');
    
 objects2_equal_lemma 0UL g g';
    
 colorHeader1_color_Lemma v_id g 2UL;

 (*assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id v_id g g' /\
                                      color_of_object1 v_id g' == 2UL /\
                                      (color_of_object1 v_id g == white \/ color_of_object1 v_id g == gray \/ 
                                      color_of_object1 v_id g == black) /\
                                      wosize_of_object1 v_id g' == wosize_of_object1 v_id g /\
                                      tag_of_object1 v_id g' == tag_of_object1 v_id g /\
                                      is_valid_header v_id g /\ is_valid_header v_id g');*)
    
 get_allocated_block_addresses_lemma g g' v_id 2UL;

 assert ((get_allocated_block_addresses g) == (get_allocated_block_addresses g'));
 let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
 let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
 
 assert (color_of_object1 v_id g <> black);
 assert (color_of_object1 v_id g' <> black);
 
 assert (G.subset_vertices blacks blacks');
 assert (~(exists y. (Seq.mem y blacks') /\ ~(Seq.mem y blacks)));
 ()
 
#restart-solver 

#restart-solver

#restart-solver

let push_to_stack2_mem_lemma_black_nodes (g:heap{well_formed_heap2 g})
                                         (st: seq Usize.t {stack_props_func g st})
                                         (x: hp_addr{is_valid_header1 x g /\
                                                              ~(Seq.mem (f_address x) st) /\
                                                             (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                             ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                             (is_fields_within_limit1 x (getWosize (read_word g x)))}) 
                                    
                     : Lemma 
                     (ensures (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                               Seq.mem y (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x)))))) = 
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   colorHeader1_color_Lemma x g 2UL;

   (*assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id x g g' /\
                                      color_of_object1 x g' == 2UL /\
                                      (color_of_object1 x g == white \/ color_of_object1 x g == gray \/ 
                                      color_of_object1 x g == black) /\
                                      wosize_of_object1 x g' == wosize_of_object1 x g /\
                                      tag_of_object1 x g' == tag_of_object1 x g /\
                                      is_valid_header x g /\ is_valid_header x g');*)
    
    get_allocated_block_addresses_lemma g g' x 2UL;
    
    let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
    let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
   
    G.is_vertex_set_lemma2 stk';
    assert (color_of_object1 x g == white);
    assert (color_of_object1 x g <> black);
    assert (color_of_object1 x g' <> black);
    assert (heap_remains_same_except_index_v_id x g g');
    assert (forall y. Seq.mem y blacks ==> Seq.mem y blacks');
    assert (G.subset_vertices blacks blacks');
    
    
    colorHeader1_mem_lemma_gray x g;
    assert (~(exists y. (Seq.mem y blacks') /\ ~(Seq.mem y blacks)));
    assert (forall y. Seq.mem y blacks' <==> Seq.mem y blacks);
    assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g');
    ()
 )
 else
 (
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  
  colorHeader1_color_Lemma x g 2UL;
  get_allocated_block_addresses_lemma g g' x 2UL;
  
  
  let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
  let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
 
  assert (heap_remains_same_except_index_v_id x g g');
  
  colorHeader1_mem_lemma_gray x g;
  assert (~(exists y. (Seq.mem y blacks') /\ ~(Seq.mem y blacks)));
  assert (forall y. Seq.mem y blacks' <==> Seq.mem y blacks);
  assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g');
  ()
 )

#restart-solver

#restart-solver

#restart-solver

#restart-solver

let push_to_stack2_mem_lemma_black_nodes_for_visited_list (g:heap{well_formed_heap2 g})
                                                          (st: seq Usize.t {stack_props_func g st})
                                                          (x: hp_addr{is_valid_header1 x g /\
                                                                       ~(Seq.mem (f_address x) st) /\
                                                                       (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                                       ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (is_fields_within_limit1 x (getWosize (read_word g x)))}) 
                   : Lemma 
                     (ensures (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==> 
                                       Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y (snd (push_to_stack2 g st x)))) = 

push_to_stack2_mem_lemma_black_nodes g st x;
let st1,g1 = push_to_stack2 g st x in
assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                               Seq.mem y (get_black_block_addresses g1 (get_allocated_block_addresses g1)));
assert (forall x. Seq.mem x (get_black_block_addresses g (get_allocated_block_addresses g)) <==> Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g);
assert (forall x. Seq.mem x (get_black_block_addresses g1 (get_allocated_block_addresses g1)) <==> Seq.mem x (objects2 0UL g1) /\ isBlackObject1 x g1);
assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>  Seq.mem x (get_black_block_addresses g1 (get_allocated_block_addresses g1)));
assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>  Seq.mem x (objects2 0UL g1) /\ isBlackObject1 x g1);                                                  
assert (g1 == snd (push_to_stack2 g st x));                                                              
assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  
                                         Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y g1);

assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  
                                         Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y (snd (push_to_stack2 g st x)));                            
()

let push_to_stack_mem_lemma_black_nodes_visited_list_lemma (g:heap{well_formed_heap2 g})
                                                           (st: seq Usize.t {stack_props_func g st})
                                                           (x: hp_addr{is_valid_header1 x g /\
                                                                       ~(Seq.mem (f_address x) st) /\
                                                                       (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                                       ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))}) 
                                                           (vl: seq Usize.t {vl_props_func g vl})
                                    
                                    
                                : Lemma
                                  (ensures (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                            isBlackObject1 (hd_address y) (snd (push_to_stack2 g st x)) <==>  
                                                   Seq.mem y vl)) =
 assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl));
 push_to_stack2_mem_lemma_black_nodes_for_visited_list  g st x;
 assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                                       isBlackObject1 y (snd (push_to_stack2 g st x)));  
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                                       isBlackObject1 (hd_address y) (snd (push_to_stack2 g st x)) <==> Seq.mem y vl);
                                                                        
 ()

#restart-solver

#restart-solver

let push_to_stack_heap_and_push_to_graph_equality_lemma1 (g:heap{well_formed_heap2 g})
                                                         (st: seq Usize.t {stack_props_func g st})
                                                         (x: hp_addr{is_valid_header1 x g /\
                                                                       ~(Seq.mem (f_address x) st) /\
                                                                       (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                                                       ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                                         (vl: seq Usize.t {vl_props_func g vl})
                                        : Lemma
                                          (requires 
                                                    
                                                    (~(Seq.mem (f_address x) st) /\ ~(Seq.mem (f_address x) vl)) /\
                                                    (Seq.mem x (get_allocated_block_addresses g)) /\
                                                    (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                    (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                   (ensures (fst (push_to_stack2 g st x) == G.push_to_stack_graph1 vl st (f_address x))) = 
if Seq.length st = 0 then
 (
    let f_x = f_address x in
    let stk' = Seq.create 1 f_x in
    let g' = colorHeader1 x g gray in 
    
   
    G.is_vertex_set_lemma2 stk';
    
    objects2_equal_lemma 0UL g g';

    assert (color_of_object1 x g == white);
    get_allocated_block_addresses_lemma g g' x 2UL;
    assert (Seq.length st == 0);
    //G.push_to_stack_graph_lemma grph vl st x;
    assert (G.push_to_stack_graph1 vl st f_x  == Seq.create 1 f_x);
    assert (stk' == Seq.create 1 f_x);
    assert (G.push_to_stack_graph1 vl st f_x == stk');
    ()
 )
 else
 ( 
   let f_x = f_address x in
   lemma_tail_snoc st f_x;
   lemma_mem_snoc st f_x; 
   let st' = snoc st f_x in
   let g' = colorHeader1 x g gray in 
   objects2_equal_lemma 0UL g g';
  
   //assert (objects2 0UL g ==  objects2 0UL g');
   //assert (well_formed_heap2 g');
   //assert (G.is_vertex_set st);
   //assert (~(Seq.mem (f_address x) st));
   G.snoc_unique_lemma f_x st;
   assert (G.is_vertex_set st'); 
   
   assert (Seq.length st > 0);
   //G.push_to_stack_graph_lemma1 grph vl st x;
   assert (G.push_to_stack_graph1 vl st f_x == snoc st f_x);
   ()
 )

#restart-solver

#restart-solver 

#reset-options "--z3rlimit 500"

#push-options "--split_queries always"

#restart-solver

let push_to_stack2_graph_lemma  (g:heap{well_formed_heap2 g})
                                (st: seq Usize.t {stack_props_func g st})
                                (x: hp_addr{is_valid_header1 x g /\
                                            ~(Seq.mem (f_address x) st) /\
                                            (Usize.v (tag_of_object1 x g) <> infix_tag) /\
                                            ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                             (Seq.mem x (get_allocated_block_addresses g))})
                     : Lemma 
                     (requires  
                                (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (push_to_stack2 g st x))) (snd (push_to_stack2 g st x))))
                     (ensures (create_graph_from_heap g == create_graph_from_heap ((snd (push_to_stack2 g st x))))) = 

if Seq.length st = 0 then
(
    let f_x = f_address x in
    let stk' = Seq.create 1 f_x in
    let g' = colorHeader1 x g gray in
    
    field_limits_allocated_blocks_lemma g;
    field_contents_within_limits_allocated_blocks_lemma g;
    fieldaddress_within_limits_lemma_x_all g;

    field_limits_allocated_blocks_lemma g';
    field_contents_within_limits_allocated_blocks_lemma g';
    fieldaddress_within_limits_lemma_x_all g';
    
    create_graph_from_heap_lemma_gray g x;
    assert (create_graph_from_heap g == create_graph_from_heap g');
    ()
)
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 

  field_limits_allocated_blocks_lemma g;
  field_contents_within_limits_allocated_blocks_lemma g;
  fieldaddress_within_limits_lemma_x_all g;

  field_limits_allocated_blocks_lemma g';
  field_contents_within_limits_allocated_blocks_lemma g';
  fieldaddress_within_limits_lemma_x_all g';
    
  create_graph_from_heap_lemma_gray g x;
  assert (create_graph_from_heap g == create_graph_from_heap g');
  ()
)   

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let darken_helper_fields_lemma(g:heap{well_formed_heap2 g})
                              (st: seq Usize.t{stack_props_func g st})
                              (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                               (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
          :Lemma
          (requires (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                    length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8) /\
                                 
                    (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                    length (slice (snd (darken_helper g st hdr_id)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8))
          
          (ensures  (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). 
                             getWosize (read_word g t) == getWosize (read_word (snd (darken_helper g st hdr_id)) t)) /\
                             
                             (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (darken_helper g st hdr_id)) y)) =

 if (color_of_object1 hdr_id g = white) then
(
   assert (is_valid_header hdr_id g);
   valid_succ_color_lemma g hdr_id;
      
   assert (~(isGrayObject1 hdr_id g) /\ ~(isBlackObject1 hdr_id g));
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
   assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
   stack_mem_lemma g st hdr_id;
   assert (Usize.v hdr_id + Usize.v mword < heap_size);
   assert (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n);
   assert (~(Seq.mem (f_address hdr_id) st));
   let st', g' = push_to_stack2 g st hdr_id  in
   push_to_stack2_heap_state_lemma g st hdr_id;
   push_to_stack2_field_size_lemma g st hdr_id;
   push_to_stack2_fields_allocated_blocks_lemma g st hdr_id ;
   assert (G.is_vertex_set st');
          
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');

   assert (color_of_object1 hdr_id g == white);
   push_to_stack2_lemma g st hdr_id;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   ()
)
else
(
  ()
)

#restart-solver 

#restart-solver

let fieldPush_spec_body_fields_lemma   (g:heap{well_formed_heap2 g})
                                       (st: seq Usize.t{stack_props_func g st})
                                       (h_index:hp_addr{is_valid_header1 h_index g})
                                       (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                       (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                    :Lemma
                     (requires (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8) /\
                                 
                               (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice (snd (fieldPush_spec_body1 g st h_index wz i)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)
                                )
                     (ensures  (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). 
                             getWosize (read_word g t) == getWosize (read_word (snd (fieldPush_spec_body1 g st h_index wz i)) t)) /\
                             
                             (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (fieldPush_spec_body1 g st h_index wz i)) y)) = 

 assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
       
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);
       
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));
  
  
   if isPointer succ_index g  then
    (
      let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        assert (Usize.v parent_hdr + Usize.v mword < heap_size);
        assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
        let st', g' = darken_helper g st parent_hdr in
        darken_helper_fields_lemma g st parent_hdr;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        darken_helper_fields_lemma g st h_addr_succ;
        ()
      )
   )
  else
   ( 
       ()
   )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver


#restart-solver 

#restart-solver 

let darken_helper_black_nodes_mem_lemma(g:heap{well_formed_heap2 g})
                                       (st: seq Usize.t{stack_props_func g st})
                                       (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                               (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
          : Lemma
            (ensures (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                           Seq.mem y (get_black_block_addresses (snd (darken_helper g st hdr_id)) 
                                                                (get_allocated_block_addresses (snd (darken_helper g st hdr_id)))))) = 
if (color_of_object1 hdr_id g = white) then
(
   assert (is_valid_header hdr_id g);
   valid_succ_color_lemma g hdr_id;
      
   assert (~(isGrayObject1 hdr_id g) /\ ~(isBlackObject1 hdr_id g));
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
   assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
   stack_mem_lemma g st hdr_id;
   assert (Usize.v hdr_id + Usize.v mword < heap_size);
   assert (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n);
   assert (~(Seq.mem (f_address hdr_id) st));
   let st', g' = push_to_stack2 g st hdr_id  in
   push_to_stack2_heap_state_lemma g st hdr_id;
   push_to_stack2_field_size_lemma g st hdr_id;
   push_to_stack2_lemma_black_nodes1 g st hdr_id;
   assert (G.is_vertex_set st');
          
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');

   assert (color_of_object1 hdr_id g == white);
   push_to_stack2_lemma g st hdr_id;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   ()
)
else
(
   ()
)

#restart-solver 

let fieldPush_spec_body_lemma_black_nodes_mem_lemma_props (g:heap{well_formed_heap2 g})
                                                          (st: seq Usize.t{stack_props_func g st})
                                                          (h_index:hp_addr{is_valid_header1 h_index g})
                                                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                                          (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) =
  (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                          Seq.mem y (get_black_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i)))))
                                                              

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let fieldPush_spec_body_black_nodes_mem_lemma (g:heap{well_formed_heap2 g})
                                              (st: seq Usize.t{stack_props_func g st})
                                              (h_index:hp_addr{is_valid_header1 h_index g})
                                              (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                              (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                             
                        : Lemma
                          (ensures (fieldPush_spec_body_lemma_black_nodes_mem_lemma_props g st h_index wz i)) = 

  assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
       
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);

  lemma_len_slice g (Usize.v  succ_index) ((Usize.v succ_index) + (Usize.v mword));
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));
  
  
   if isPointer succ_index g  then
    (
      let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        assert (Usize.v parent_hdr + Usize.v mword < heap_size);
        assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
        let st', g' = darken_helper g st parent_hdr in
        darken_helper_black_nodes_mem_lemma g st parent_hdr;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        darken_helper_black_nodes_mem_lemma g st h_addr_succ;
        ()
      )
   )
  else
   ( 
       ()
   )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

#restart-solver 

#restart-solver

let darken_helper_valid_header_visited_set_lemma (g:heap{well_formed_heap2 g})
                                                      (st: seq Usize.t{stack_props_func g st})
                                                      (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                                                      (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
                                                      (vl: seq Usize.t{vl_props_func g vl})
         : Lemma
           (ensures ((forall y. Seq.mem y vl ==> is_valid_header1 (hd_address y) (snd (darken_helper g st hdr_id))))) = 

if (color_of_object1 hdr_id g = white) then
(
   assert (is_valid_header hdr_id g);
   valid_succ_color_lemma g hdr_id;
      
   assert (~(isGrayObject1 hdr_id g) /\ ~(isBlackObject1 hdr_id g));
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
   assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
   stack_mem_lemma g st hdr_id;
   assert (Usize.v hdr_id + Usize.v mword < heap_size);
   assert (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n);
   assert (~(Seq.mem (f_address hdr_id) st));
   let st', g' = push_to_stack2 g st hdr_id  in
   push_to_stack2_heap_state_lemma g st hdr_id;
   push_to_stack2_field_size_lemma g st hdr_id;
   
   
   assert (G.is_vertex_set st');
          
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');

   assert (color_of_object1 hdr_id g == white);
   push_to_stack2_lemma g st hdr_id;
   push_to_stack2_visited_list_valid_header_lemma g st hdr_id vl;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   ()
)
else
(
   ()
)

let fieldPush_spec_body_valid_header_visited_set_lemma  (g:heap{well_formed_heap2 g})
                                                        (st: seq Usize.t{stack_props_func g st})
                                                        (h_index:hp_addr{is_valid_header1 h_index g})
                                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                        (vl: seq Usize.t{vl_props_func g vl}) 
                            : Lemma
                              (ensures ((forall y. Seq.mem y vl ==> is_valid_header1 (hd_address y) (snd (fieldPush_spec_body1 g st h_index wz i))))) =

assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
       
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);
       
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));
  
  
   if isPointer succ_index g  then
    (
      let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        assert (Usize.v parent_hdr + Usize.v mword < heap_size);
        assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
        let st', g' = darken_helper g st parent_hdr in
        darken_helper_valid_header_visited_set_lemma g st parent_hdr vl;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        darken_helper_valid_header_visited_set_lemma g st h_addr_succ vl;
        ()
      )
   )
  else
   ( 
       ()
   )

#restart-solver 

#restart-solver

let darken_helper_black_nodes_visited_set_lemma (g:heap{well_formed_heap2 g})
                                                (st: seq Usize.t{stack_props_func g st})
                                                (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                                                      (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
                                                (vl: seq Usize.t{vl_props_func g vl})
         : Lemma
           (ensures (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (darken_helper g st hdr_id))) /\ 
                                                  isBlackObject1 (hd_address y) (snd (darken_helper g st hdr_id)) <==>  
                                                                                           Seq.mem y vl)) = 
if (color_of_object1 hdr_id g = white) then
(
   assert (is_valid_header hdr_id g);
   valid_succ_color_lemma g hdr_id;
      
   assert (~(isGrayObject1 hdr_id g) /\ ~(isBlackObject1 hdr_id g));
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
   assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
   stack_mem_lemma g st hdr_id;
   assert (Usize.v hdr_id + Usize.v mword < heap_size);
   assert (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n);
   assert (~(Seq.mem (f_address hdr_id) st));
   let st', g' = push_to_stack2 g st hdr_id  in
   push_to_stack2_heap_state_lemma g st hdr_id;
   push_to_stack2_field_size_lemma g st hdr_id;
   
   
   assert (G.is_vertex_set st');
          
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');

   assert (color_of_object1 hdr_id g == white);
   push_to_stack2_lemma g st hdr_id;
  push_to_stack_mem_lemma_black_nodes_visited_list_lemma  g st hdr_id vl;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   ()
)
else
(
   ()
)

let fieldPush_spec_body_black_nodes_visited_set_lemma (g:heap{well_formed_heap2 g})
                                                      (st: seq Usize.t{stack_props_func g st})
                                                      (h_index:hp_addr{is_valid_header1 h_index g})
                                                      (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                                      (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                      (vl: seq Usize.t{vl_props_func g vl}) 
                            : Lemma
                              (ensures (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (fieldPush_spec_body1 g st h_index wz i))) /\ 
                                                  isBlackObject1 (hd_address y) (snd (fieldPush_spec_body1 g st h_index wz i)) <==>  
                                                                                           Seq.mem y vl)) = 
 assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
       
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);
       
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));
  
  
   if isPointer succ_index g  then
    (
      let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        assert (Usize.v parent_hdr + Usize.v mword < heap_size);
        assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
        let st', g' = darken_helper g st parent_hdr in
        darken_helper_black_nodes_visited_set_lemma g st parent_hdr vl;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        darken_helper_black_nodes_visited_set_lemma g st h_addr_succ vl;
        ()
      )
   )
  else
   ( 
       ()
   )


#restart-solver 

#restart-solver

#restart-solver

let darken_helper_graph_lemma (g:heap{well_formed_heap2 g})
                              (st: seq Usize.t{stack_props_func g st})
                              (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                               (Usize.v (tag_of_object1 hdr_id g) <> infix_tag)}) 
         : Lemma
           (requires (
                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g))) 
                                     
           (ensures (create_graph_from_heap g == create_graph_from_heap (snd (darken_helper g st hdr_id)))) =  

if (color_of_object1 hdr_id g = white) then
(
   assert (is_valid_header hdr_id g);
   valid_succ_color_lemma g hdr_id;
      
   assert (~(isGrayObject1 hdr_id g) /\ ~(isBlackObject1 hdr_id g));
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
   assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
   stack_mem_lemma g st hdr_id;
   assert (Usize.v hdr_id + Usize.v mword < heap_size);
   assert (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n);
   assert (~(Seq.mem (f_address hdr_id) st));
   let st', g' = push_to_stack2 g st hdr_id  in
   push_to_stack2_heap_state_lemma g st hdr_id;
   push_to_stack2_field_size_lemma g st hdr_id;
   
   
   assert (G.is_vertex_set st');
          
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');

   assert (color_of_object1 hdr_id g == white);
   push_to_stack2_lemma g st hdr_id;

   
   push_to_stack2_graph_lemma g st hdr_id;

   assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
   assert ((Seq.length g == Seq.length g'));
     
   ()
)
else
(
   ()
)

#restart-solver 

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let fieldPush_spec_body_graph_lemma (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{stack_props_func g st})
                                    (h_index:hp_addr{is_valid_header1 h_index g})
                                    (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                    (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (requires (
                                     (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                     
                                     (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8) /\
                                 
                               (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice (snd (fieldPush_spec_body1 g st h_index wz i)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)))
                                     
                          (ensures (create_graph_from_heap g == create_graph_from_heap (snd (fieldPush_spec_body1 g st h_index wz i)))) = 

assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
       
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);
       
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));
  
  
  let allocs = get_allocated_block_addresses g in
  fieldaddress_within_limits_lemma_x_all g;
  assert (forall i x.  Seq.mem x allocs /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
 
  
                                          
  if isPointer succ_index g  then
    (
      let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        assert (Usize.v parent_hdr + Usize.v mword < heap_size);
        assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
        let st', g' = darken_helper g st parent_hdr in
        assert (Seq.mem parent_hdr (get_allocated_block_addresses g));
        
        darken_helper_graph_lemma g st parent_hdr;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        assert (Seq.mem h_addr_succ (get_allocated_block_addresses g));
        
        darken_helper_graph_lemma g st h_addr_succ;
        ()
      )
   )
  else
   ( 
       ()
   )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

let fieldPush_spec1_fields_lemma1_props (g:heap{well_formed_heap2 g})
                                            (st: seq Usize.t{stack_props_func g st})
                                            (h_index:hp_addr{is_valid_header1 h_index g})
                                            (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                            (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1}) =
 (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g t) == 
                                                                                   getWosize (read_word (snd (fieldPush_spec1 g st h_index wz i)) t)) /\
                   (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (fieldPush_spec1 g st h_index wz i)) y)



#restart-solver

//#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

let rec fieldPush_spec1_fields_lemma1 (g:heap{well_formed_heap2 g})
                                      (st: seq Usize.t{stack_props_func g st})
                                      (h_index:hp_addr{is_valid_header1 h_index g})
                                      (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                      (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
          :Lemma
          (ensures (fieldPush_spec1_fields_lemma1_props g st h_index wz i))
          (decreases ((Usize.v wz + 1) - Usize.v i)) =

if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       
       assert (fieldPush_spec1_fields_lemma1_props g st h_index wz i);
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body g st h_index wz i in
       (*assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
                                         Seq.mem x st'));*)
       fieldPush_spec_body_fields_lemma g st h_index wz i;
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st_hp = fieldPush_spec1 g' st' h_index wz i' in
       fieldPush_spec1_fields_lemma1 g' st' h_index wz i';
       ()
    )

#restart-solver

#restart-solver

let rec fieldPush_spec1_black_nodes_lemma1 (g:heap{well_formed_heap2 g})
                                           (st: seq Usize.t{stack_props_func g st})
                                           (h_index:hp_addr{is_valid_header1 h_index g})
                                           (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                           (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (ensures (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses  (snd (fieldPush_spec1 g st h_index wz i))
                                                                         (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i))))))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body1 g st h_index wz i in
       

       fieldPush_spec_body_black_nodes_mem_lemma g st h_index wz i;
       fieldPush_spec_body1_black_nodes_lemma g st h_index wz i;
       (*assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                          Seq.mem y (get_black_block_addresses g' 
                                                              (get_allocated_block_addresses g')));*)
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st_hp = fieldPush_spec1 g' st' h_index wz i' in
       fieldPush_spec1_black_nodes_lemma1 g' st' h_index wz i';
       (*assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses (snd st_hp) (get_allocated_block_addresses (snd st_hp))));
                                                                         
       
       
       assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses (snd (fieldPush_spec1 g' st' h_index wz i')) 
                                                      (get_allocated_block_addresses (snd (fieldPush_spec1 g' st' h_index wz i')))));
       
       assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses (snd (fieldPush_spec1 g st h_index wz i)) 
                                                      (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i)))));*)
       ()
    )

#restart-solver 

#restart-solver

let lemma_len_slice_invoke (g:heap{well_formed_heap2 g})
                           (t:hp_addr)
                : Lemma
                  (ensures (length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)) =
lemma_len_slice g (Usize.v t) ((Usize.v t) + (Usize.v mword));
()

let lemma_len_slice_invoke_all (g:heap{well_formed_heap2 g})
                : Lemma
                  (ensures (forall (t:hp_addr(*{Usize.v t < heap_size /\ Usize.v t % 8 == 0}*)).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)) =
Classical.forall_intro (Classical.move_requires (lemma_len_slice_invoke g))

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let rec fieldPush_spec1_graph_lemma (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{stack_props_func g st})
                                    (h_index:hp_addr{is_valid_header1 h_index g})
                                    (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                    (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (requires (
                                     (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                     (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i))) 
                                                    (snd (fieldPush_spec1 g st h_index wz i)))))
                          
                          (ensures (create_graph_from_heap g == create_graph_from_heap (snd (fieldPush_spec1 g st h_index wz i)))) 
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       fieldPush_fieldPush_spec_body_lemma1 g st h_index wz i;
       assert (g == snd (fieldPush_spec1 g st h_index wz i));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i >= 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st', g' = fieldPush_spec_body1 g st h_index wz i in
       
       
       (*assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
                                         Seq.mem x st'));*)
       
       let st'', g'' = fieldPush_spec1 g' st' h_index wz i' in
       field_limits_allocated_blocks_lemma g'';
       field_contents_within_limits_allocated_blocks_lemma g'';
       lemma_len_slice_invoke_all g;
       lemma_len_slice_invoke_all g';
       (*assert (forall (t:hp_addr). length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8);
                                 
       assert (forall (t:hp_addr). length (slice (snd (fieldPush_spec_body1 g st h_index wz i)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8);*)
                                 
       fieldPush_spec_body_graph_lemma g st h_index wz i;
       fieldaddress_within_limits_lemma_x_all g'';
       assert (all_field_address_are_word_aligned (get_allocated_block_addresses g'') g'');
       fieldPush_spec1_graph_lemma g' st' h_index wz i';
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       ()
  )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

#restart-solver

let arithmetic_lemma (i:Usize.t)
                     (wz:wosize)
            : Lemma
              (requires (Usize.v i < Usize.v wz + 1))
              (ensures (Usize.v i <= Usize.v wz)) = 
 assert (Usize.v i < Usize.v wz + 1);
 assert (Usize.v i <= Usize.v wz);
 ()

#restart-solver 

let arithmetic_lemma1 (i:Usize.t)
                     (wz:wosize)
            : Lemma
              (requires (Usize.v i <= Usize.v wz))
              (ensures (Usize.v i - 1 < Usize.v wz)) = 
 assert (Usize.v i <= Usize.v wz);
 assert (Usize.v i - 1 < Usize.v wz);
 ()


#restart-solver

#restart-solver 

let h_index_within_limits (g: heap {well_formed_heap2 g})
                          (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g}) = 
 (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
 (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
   (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                          (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) 

#restart-solver 

#restart-solver

//#push-options "--z3rlimit 500"

#restart-solver

let seq_empty_slice_lemma (f:seq Usize.t)
                          (i:Usize.t {Usize.v i == Seq.length f})
            : Lemma
              (ensures Seq.empty #Usize.t == Seq.slice f (Usize.v i) (Seq.length f)) =
()

let seq_cons_slice_lemma (succ: Usize.t)
                         (f: seq Usize.t)
                         (rest_of_list: seq Usize.t)
                         (i:Usize.t {Usize.v i < Seq.length f})
                         (i':Usize.t {Usize.v i' == Usize.v i  + 1})
            : Lemma
              (requires (rest_of_list == Seq.slice f (Usize.v i') (Seq.length f)) /\
                        (succ == Seq.index f (Usize.v i)))
              (ensures  (Seq.cons succ rest_of_list == Seq.slice f (Usize.v i) (Seq.length f)) /\
                        (Seq.head (Seq.cons succ rest_of_list) == succ) /\
                        (Seq.tail (Seq.cons succ rest_of_list) == rest_of_list)) =
()

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let rec graph_successors_create_from_an_index (g: heap {well_formed_heap2 g})
                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     
                                                                                     h_index_within_limits g h_index})
                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                              (i:Usize.t {Usize.v i <= Seq.length f}) 
                                  : Tot (s_list': seq Usize.t{s_list' == Seq.slice f (Usize.v i) (Seq.length f)})
                              (decreases (Seq.length f - Usize.v i))= 
if Usize.v i = Seq.length f then
 (
   
    seq_empty_slice_lemma f i;
    Seq.empty #Usize.t
 )
 else
 (
   let succ = Seq.index f (Usize.v i) in
   let i' = Usize.add i 1UL in
   let rest_of_list = graph_successors_create_from_an_index g h_index f i' in
   assert (rest_of_list == Seq.slice f (Usize.v i') (Seq.length f));
   lemma_tl  succ rest_of_list;
   let s_list' = Seq.cons succ rest_of_list in
   seq_cons_slice_lemma succ f rest_of_list i i';
   assert (s_list' == Seq.slice f (Usize.v i) (Seq.length f));
   s_list'
 )

let graph_successors_create_from_an_index_lemma (g: heap {well_formed_heap2 g})
                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     
                                                                                     h_index_within_limits g h_index})
                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                    (i:Usize.t {Usize.v i < Seq.length f}) 
                                  : Lemma
                                    (requires (Seq.length (graph_successors_create_from_an_index g h_index f i) > 0))
                                    (ensures (Seq.head (graph_successors_create_from_an_index g h_index f i) == Seq.index f (Usize.v i))) = 

if Usize.v i = Seq.length f then
 (
   
    seq_empty_slice_lemma f i;
    ()
 )
 else
 (
   let succ = Seq.index f (Usize.v i) in
   let i' = Usize.add i 1UL in
   let rest_of_list = graph_successors_create_from_an_index g h_index f i' in
   assert (rest_of_list == Seq.slice f (Usize.v i') (Seq.length f));
   lemma_tl  succ rest_of_list;
   let s_list' = Seq.cons succ rest_of_list in
   seq_cons_slice_lemma succ f rest_of_list i i';
   assert (s_list' == Seq.slice f (Usize.v i) (Seq.length f));
   ()
 )

let graph_successors_create_from_an_index_lemma1 (g: heap {well_formed_heap2 g})
                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g  /\
                                                                                     h_index_within_limits g h_index})
                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                    (i:Usize.t {Usize.v i < Seq.length f}) 
                                                    (i': Usize.t {Usize.v i' == Usize.v i + 1})
                                  : Lemma
                                    (requires (Seq.length (graph_successors_create_from_an_index g h_index f i) > 0))
                                    (ensures (Seq.tail (graph_successors_create_from_an_index g h_index f i) == (graph_successors_create_from_an_index g h_index f i'))) =

if Usize.v i = Seq.length f then
 (
   
    seq_empty_slice_lemma f i;
    ()
 )
 else
 (
   let succ = Seq.index f (Usize.v i) in
   let i' = Usize.add i 1UL in
   let rest_of_list = graph_successors_create_from_an_index g h_index f i' in
   assert (rest_of_list == Seq.slice f (Usize.v i') (Seq.length f));
   lemma_tl  succ rest_of_list;
   let s_list' = Seq.cons succ rest_of_list in
   seq_cons_slice_lemma succ f rest_of_list i i';
   assert (s_list' == Seq.slice f (Usize.v i) (Seq.length f));
   ()
 )

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

let head_content_successor_list_in_heap_props (g:heap{well_formed_heap2 g}) 

                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g  /\
                                                                                     h_index_within_limits g h_index})
                                         
                                              (wz: wosize{valid_wosize g h_index wz})
                         
                                              (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1 /\
                                                         (is_hp_addr (Usize.add h_index (Usize.mul i mword)))}) =
 ((*if succ of h_index at index i is a pointer*)
   isPointer_succ g h_index wz i ==>
   (*if the succ points to an infix object*)
          Usize.v (tag_succ g h_index wz i) == infix_tag  ==> 
     (*then head of succ_list starting at index i is the object address of the parent closure of the infix object*)
     Seq.head (create_successors_list_for_h_index g h_index wz i) ==
       f_address (parent_closure_of_infix_object g h_index i)) /\
 
 ((*if succ of h_index at index i is a pointer*)
   isPointer_succ g h_index wz i ==>
   (*if the succ points to an object whose tag is not infix tag*)
          Usize.v (tag_succ g h_index wz i) <> infix_tag  ==> 
     (*then head of succ_list starting at index i is the object address of succ*)
     Seq.head (create_successors_list_for_h_index g h_index wz i) ==
       get_succ_value g h_index wz i)     

let create_successors_list_for_h_index_from_i_index_lemma (g:heap{well_formed_heap2 g}) 

                                                          (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g  /\
                                                                                     h_index_within_limits g h_index})
                                         
                                                          (wz: wosize{valid_wosize g h_index wz})
                         
                                                          (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                   : Lemma
                                     (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                     (ensures head_content_successor_list_in_heap_props g h_index wz i) = 
()

#restart-solver 

let create_successors_list_for_h_index_from_i_index_lemma_tail_helper (g:heap{well_formed_heap2 g}) 

                                                                      (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g  /\
                                                                                     h_index_within_limits g h_index})
                                         
                                                                      (wz: wosize{valid_wosize g h_index wz})
                         
                                                                      (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                                   
                                    : Lemma
                                      (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\ (isPointer(Usize.add h_index (Usize.mul i mword)) g))
                                      (ensures (create_successors_list_for_h_index g h_index wz i <> Seq.empty) /\ 
                                                 Seq.length (create_successors_list_for_h_index g h_index wz i) > 0) = ()

#restart-solver 

#restart-solver

let create_successors_list_for_h_index_from_i_index_lemma_tail (g:heap{well_formed_heap2 g}) 

                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g  /\
                                                                                     h_index_within_limits g h_index})
                                         
                                                               (wz: wosize{valid_wosize g h_index wz})
                         
                                                               (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                               (i':Usize.t{Usize.v i' == Usize.v i + 1}) 
                                    : Lemma
                                      (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\ (isPointer(Usize.add h_index (Usize.mul i mword)) g) /\
                                                 Seq.length (create_successors_list_for_h_index g h_index wz i) > 0)
                                      (ensures Seq.tail (create_successors_list_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i') =

if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
       
       ()
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 
           ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
        
      let s_list' = create_successors_list_for_h_index g h_index wz i' in
      if isPointer succ_index g  then
      (
        
         let h_addr_succ = hd_address succ in
         
         if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
         (
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
           assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
           let parent_succ = f_address parent_hdr in
           lemma_tl parent_succ s_list'; 
        
           let s_list = Seq.cons parent_succ s_list' in 
        
           assert (Seq.head s_list == parent_succ);

           ()
         )
         else
         (
           
           lemma_tl succ s_list'; 
        
           let s_list = Seq.cons succ s_list' in 
        
           assert (Seq.head s_list == succ);

           ()
         )
      )
      else
      (
       
        ()
      )
    )

#restart-solver 

#restart-solver 

#restart-solver

let slice_lemma (#a:Type)
                (s:seq a)
       : Lemma 
         (ensures s == Seq.slice s 0 (Seq.length s)) = ()


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

let graph_successors_create_from_index_0_equals_graph_successors (g: heap {well_formed_heap2 g})
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                                                 
                                        : Lemma
                                          (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                    (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                    (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index))) /\
                                                    0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)))
                                          (ensures G.successors (create_graph_from_heap g) (f_address h_index) == 
                                                    graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL) = 
let s_list' =  graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL in
assert (s_list' == Seq.slice (G.successors (create_graph_from_heap g) (f_address h_index)) 0 (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))));
slice_lemma (G.successors (create_graph_from_heap g) (f_address h_index));
assert (G.successors (create_graph_from_heap g) (f_address h_index) == 
         Seq.slice (G.successors (create_graph_from_heap g) (f_address h_index)) 0 (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))));
assert (G.successors (create_graph_from_heap g) (f_address h_index) == 
         graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL);
()

#restart-solver 

#restart-solver 

#reset-options "--z3rlimit 500"


let graph_successors_from_0_and_heap_field_pointers_from_1_are_equal (g: heap {well_formed_heap2 g})
                                                                     (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                               
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                    (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                    (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index))) /\
                                                    0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                    Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
                                                    Usize.v (tag_of_object1 h_index g) <> closure_tag)
                                  (ensures graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) = 

graph_successors_create_from_index_0_equals_graph_successors g h_index;
assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
assert (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
              (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0);
assert (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);

graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
assert (Usize.v (tag_of_object1 h_index g) < no_scan_tag);
assert (Usize.v (tag_of_object1 h_index g) <> closure_tag);
assert (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
()

#push-options "--split_queries always"

#restart-solver

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


let graph_successors_from_0_and_heap_field_pointers_from_1_are_equal1 (g: heap {well_formed_heap2 g})
                                                                      (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                               
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                    (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                    (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index))) /\
                                                    0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                    Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
                                                    Usize.v (tag_of_object1 h_index g) == closure_tag)
                                  (ensures (let start_env = start_env_clos_info g (f_address h_index) in
                                            let start_env_plus_one = Usize.add start_env 1UL in
                                               graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 
                                                                                             (start_env_plus_one))) = 
graph_successors_create_from_index_0_equals_graph_successors g h_index;
assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
assert (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
              (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0);
assert (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);

graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
assert (Usize.v (tag_of_object1 h_index g) < no_scan_tag);
assert (Usize.v (tag_of_object1 h_index g) == closure_tag);
(*assert (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 
                                                (start_env_clos_info g (f_address h_index)));*)
()

#reset-options "--z3rlimit 500"
#push-options "--split_queries always"

let create_successors_list_for_h_index_recursing_property_lemma (g: heap {well_formed_heap2 g})
                                                                (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                         
                                                                (wz: wosize{valid_wosize g h_index wz})
                         
                                                                (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                                (i':Usize.t{Usize.v i' == Usize.v i + 1}) 
                                       : Lemma
                                         (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                         (ensures ~(isPointer(Usize.add h_index (Usize.mul i mword)) g) ==> create_successors_list_for_h_index g h_index wz i == 
                                                                                create_successors_list_for_h_index g h_index wz i') = ()

let successors_list_recursing_props (g: heap {well_formed_heap2 g})
                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                         
                                    (wz: wosize{valid_wosize g h_index wz})
                         
                                    (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                    (i':Usize.t{Usize.v i' == Usize.v i + 1 /\ (is_hp_addr (get_succ_address g h_index wz i))}) =
 (isPointer_succ g h_index wz i ==> 
       Usize.v (tag_succ g h_index wz i) == infix_tag  ==> 
           create_successors_list_for_h_index g h_index wz i == 
           Seq.cons  (f_address (parent_closure_of_infix_object g h_index i)) (create_successors_list_for_h_index g h_index wz i')) /\
 
 (isPointer_succ g h_index wz i ==> 
      Usize.v (tag_succ g h_index wz i) <> infix_tag  ==> 
           create_successors_list_for_h_index g h_index wz i == 
           Seq.cons  (get_succ_value g h_index wz i) (create_successors_list_for_h_index g h_index wz i'))

let create_successors_list_for_h_index_recursing_property_lemma1 (g:heap{well_formed_heap2 g}) 

                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                         
                                                                 (wz: wosize{valid_wosize g h_index wz})
                         
                                                                 (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                                 (i':Usize.t{Usize.v i' == Usize.v i + 1})
                                       : Lemma
                                         (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                         (ensures (successors_list_recursing_props g h_index wz i i')) =
()

let create_successors_list_for_h_index_recursing_property_lemma2 (g:heap{well_formed_heap2 g}) 
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                           
                                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                 (i:Usize.t{Usize.v i == Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                        : Lemma
                                          (ensures create_successors_list_for_h_index g h_index wz i == Seq.empty) = ()

#restart-solver

let create_successors_list_for_h_index_recursing_property_lemma3 (g:heap{well_formed_heap2 g}) 
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                           
                                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                 (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                 (i':Usize.t{Usize.v i' == Usize.v i + 1})
                                        : Lemma
                                          (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                          (ensures (create_successors_list_for_h_index g h_index wz i == Seq.empty) ==> 
                                                      create_successors_list_for_h_index g h_index wz i' == Seq.empty) = ()

let create_successors_list_for_h_index_recursing_property_lemma4 (g:heap{well_formed_heap2 g}) 
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                           
                                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                 (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                
                                        : Lemma
                                          (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                          (ensures (create_successors_list_for_h_index g h_index wz i == Seq.empty) ==> 
                                                       ~(isPointer(Usize.add h_index (Usize.mul i mword)) g)) = ()

#restart-solver

let seq_cons_non_empty_lemma (s:seq Usize.t)
                             (x:Usize.t)
                             (s':seq Usize.t{s' == Seq.cons x s})
         : Lemma
           (ensures ~(s' == Seq.empty)) =
 ()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

let graph_successors_create_from_an_index_empty_lemma (g: heap {well_formed_heap2 g})
                                                      (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     h_index_within_limits g h_index})
                                                      (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                      (i:Usize.t {Usize.v i <= Seq.length f})
                            : Lemma
                              (ensures (graph_successors_create_from_an_index g h_index f i) == Seq.empty ==>
                                             Usize.v i == Seq.length f) = 
if Usize.v i = Seq.length f then
 (
   
    seq_empty_slice_lemma f i;
    let s = Seq.empty #Usize.t in
    assert (s == graph_successors_create_from_an_index g h_index f i);
    assert (s == Seq.empty);
    assert (Usize.v i == Seq.length f);
    ()
 )
 else
 (
   let succ = Seq.index f (Usize.v i) in
   let i' = Usize.add i 1UL in
   let rest_of_list = graph_successors_create_from_an_index g h_index f i' in
   assert (rest_of_list == Seq.slice f (Usize.v i') (Seq.length f));
   lemma_tl  succ rest_of_list;
   let s_list' = Seq.cons succ rest_of_list in
   seq_cons_slice_lemma succ f rest_of_list i i';
   assert (s_list' == Seq.slice f (Usize.v i) (Seq.length f));
   seq_cons_non_empty_lemma rest_of_list succ s_list';
   assert (~(s_list' == Seq.empty));
   ()
 )

let create_successors_list_for_h_index_i_equals_wz_plus_one_implies_succ_list_from_j_is_empty (g:heap{well_formed_heap2 g})
                                                                                              (st: seq Usize.t{stack_props_func g st})
                         
                                                                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                              is_valid_header1 h_index g /\
                                                                                                              h_index_within_limits g h_index})
                                           
                                                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                               (i:Usize.t{Usize.v i == Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                               (j:Usize.t)
                                          : Lemma
                                            (requires 
                                                      
                                            
                                                       h_index_within_limits g h_index /\
                                                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                       (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                       (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                       (Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                       (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                       (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i))
                                            (ensures Usize.v j == Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) = 
 create_successors_list_for_h_index_recursing_property_lemma2 g h_index wz i;
 assert (create_successors_list_for_h_index g h_index wz i == Seq.empty);
 assert ((graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) == Seq.empty);
 graph_successors_create_from_an_index_empty_lemma g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j;
 assert (Usize.v j == Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)));
 ()

#restart-solver

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j (g:heap{well_formed_heap2 g})
                                                                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                              is_valid_header1 h_index g /\
                                                                                                              h_index_within_limits g h_index})
                                           
                                                                                              (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                              (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                              (j:Usize.t) 
                                               : Lemma
                                                 (requires  (h_index_within_limits g h_index /\
                                                           (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                           (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                           (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                           (Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                           (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                           (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                           Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0))
                                            (ensures (let s_heap_i = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) in
                                                      let s_graph_j = (graph_successors_create_from_an_index g h_index 
                                                                          (G.successors (create_graph_from_heap g) (f_address h_index)) j) in
                                                       let hd = Seq.head s_heap_i in
                                                       let hd1 = Seq.head s_graph_j in
                                                      
                                                       let tl = Seq.tail s_heap_i in
                                                       let tl1 = Seq.tail s_graph_j in
                                                       (hd == hd1) /\ (tl == tl1))) = ()
                                                      
#reset-options "--z3rlimit 1000"

#restart-solver

let i_times_mword_multiple_of_mword (i:Usize.t{Usize.v i <= Usize.v max_wosize})
                     :Lemma 
                      (ensures (Usize.v (Usize.mul i mword) % Usize.v mword == 0)) = ()

#restart-solver

#restart-solver 

#restart-solver

#restart-solver

let field_ptr_construct (g:heap{well_formed_heap2 g}) 

                        (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                        (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                        is_valid_header1 h_index g /\
                                        h_index_within_limits g h_index})
                                           
                        (wz: wosize{wz == getWosize (read_word g h_index) /\ h_index_within_limits g h_index})
                         
                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
              : Tot (s:hp_addr{Usize.v s == Usize.v h_index + (Usize.v i * Usize.v mword)})=
  let s = (Usize.add h_index (Usize.mul i mword)) in
  i_times_mword_multiple_of_mword i;
  assert (Usize.v (Usize.mul i mword) % Usize.v mword == 0);
  assert (Usize.v h_index % Usize.v mword == 0);
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword); 
  assert (Usize.v s % Usize.v mword == 0);
  assert (Usize.v s < heap_size);
  assert (is_hp_addr s);
  s

let cons_length_lemma3 (#a:Type)
                       (s:seq a)
                       (s_cons:a)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s) > 0))=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ;
 assert (Seq.length s' > 0);
 ()

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver


#restart-solver

#push-options "--split_queries always"

#restart-solver

#restart-solver

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j1 (g:heap{well_formed_heap2 g})
                                                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                              is_valid_header1 h_index g /\
                                                                                                              h_index_within_limits g h_index})
                                           
                                                                                                (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                                (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                                (j:Usize.t) 
                                                    : Lemma
                                            (requires 
                                            
                                                       h_index_within_limits g h_index /\
                                                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                       (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                       (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                       (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                       (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                       (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                        (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                        (isPointer(Usize.add h_index (Usize.mul i mword)) g) /\
                                                        (Usize.v (tag_succ g h_index wz i) <> infix_tag) /\ 
                                                        Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0
                                                     )
                                              (ensures (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                        read_word g (Usize.add h_index (Usize.mul i mword)))) = 
 graph_successors_create_from_an_index_lemma g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j;
 create_successors_list_for_h_index_from_i_index_lemma g h_index wz i; 
 create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j g h_index wz i j;
 assert (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         read_word g (Usize.add h_index (Usize.mul i mword)));
 ()

(*Create a lemma similar to the above to handle the case when the field pointer points to an infix object*)

#restart-solver 

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j3 (g:heap{well_formed_heap2 g})
                                                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                              is_valid_header1 h_index g /\
                                                                                                              h_index_within_limits g h_index})
                                           
                                                                                                (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                                (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                                (j:Usize.t) 
                                                    : Lemma
                                            (requires  h_index_within_limits g h_index /\
                                                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                       (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                       (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                       (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                       (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                       (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                        (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                        (isPointer(Usize.add h_index (Usize.mul i mword)) g) /\
                                                        (Usize.v (tag_succ g h_index wz i) == infix_tag) /\ 
                                                        Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0
                                                     )
                                              (ensures (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         f_address (parent_closure_of_infix_object g h_index i))) =
graph_successors_create_from_an_index_lemma g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j;
create_successors_list_for_h_index_from_i_index_lemma g h_index wz i; 
create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j g h_index wz i j;
assert (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         f_address (parent_closure_of_infix_object g h_index i));
                                            
()

#reset-options "--z3rlimit 1000"
#restart-solver


#restart-solver

#push-options "--split_queries always"

#push-options "--z3rlimit 1000"

#restart-solver

let create_successors_list_for_h_index_pointer_lemma (g:heap{well_formed_heap2 g}) 

                                           (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header1 h_index g})
                                           
                                           (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                           (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})

                       : Lemma
                         (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x)))) /\
                                   (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) /\
                                   (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                            (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                            (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                   (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                   (isPointer (field_ptr_construct g h_index wz i) g))
                         (ensures (Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0))
                         
                         (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
       
       ()
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 
           ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
        
      let s_list' = create_successors_list_for_h_index g h_index wz i' in
      if isPointer succ_index g  then
      (
        
         let h_addr_succ = hd_address succ in
         (*test_allocs g h_index wz;
         assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
         assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
         assert (Seq.mem (hd_address succ) (objects2 0UL g));
         assert (is_valid_header (hd_address succ) g);

         assert (well_formed_allocated_blocks g);
         assert (Seq.mem h_index (get_allocated_block_addresses g));*)
         if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
         (
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
           assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
           let parent_succ = f_address parent_hdr in
           lemma_tl parent_succ s_list'; 
        
           let s_list = Seq.cons parent_succ s_list' in 
        
           assert (Seq.head s_list == parent_succ);

           ()
         )
         else
         (
           
           lemma_tl succ s_list'; 
        
           let s_list = Seq.cons succ s_list' in 
        
           assert (Seq.head s_list == succ);

           ()
         )
      )
      else
      (
       
        ()
      )
    )

#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver  

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j2 (g:heap{well_formed_heap2 g})
                                                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                               is_valid_header1 h_index g})
                                           
                                                                                                (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                                (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                                (j:Usize.t) 
                                               : 
                                          Lemma
                                            (requires (h_index_within_limits g h_index) /\
                                                      (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                      (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                      
                                                      (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                      (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                      (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                      (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                      (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                      (isPointer(Usize.add h_index (Usize.mul i mword)) g)
                                                     )
                                             (ensures (let i' = Usize.add i 1UL in
                                                       let j' = Usize.add j 1UL in
                                                       (graph_successors_create_from_an_index g h_index ((G.successors (create_graph_from_heap g) (f_address h_index))) j' == 
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i')))  = 
 let i' = Usize.add i 1UL in
 let j' = Usize.add j 1UL in

 let s_heap_i = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) in
 let s_graph_j =  (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) in
 
 let sl = (G.successors (create_graph_from_heap g) (f_address h_index)) in
 assert (s_heap_i == s_graph_j);
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;

 create_successors_list_for_h_index_pointer_lemma g h_index wz i;
 assert (Seq.length s_heap_i > 0);
 assert (Seq.length s_graph_j > 0);
  
 let tl = Seq.tail s_heap_i in
 let tl1 = Seq.tail s_graph_j in
 create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j g h_index wz i j;
 assert (tl == tl1);
 let s_graph_j1 =  (graph_successors_create_from_an_index g h_index sl j') in
 graph_successors_create_from_an_index_lemma1 g h_index sl j j';
 assert (tl1 == s_graph_j1);
 let s_heap_i1 = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i') in
 create_successors_list_for_h_index_from_i_index_lemma_tail g h_index wz i i';
 assert (tl ==  s_heap_i1);
 assert (s_graph_j1 == s_heap_i1);
 assert (graph_successors_create_from_an_index g h_index sl j' == create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');
 ()

#restart-solver 

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"


#restart-solver

#restart-solver


#restart-solver

let fieldPush_spec_body_successor_push_body_equivalence_lemma3 (g:heap{well_formed_heap2 g})
                                                               (st: seq Usize.t{stack_props_func g st})
                                                               (h_index:hp_addr{is_valid_header1 h_index g})
                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                         
                                                               (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                               
                                                               (vl: seq Usize.t{vl_props_func g vl}) 
                                : Lemma
                                  (requires ((h_index_within_limits g h_index) /\
                                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                             (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                      
                                                     
                                             (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                 
                                             (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                             ( ~(isPointer(Usize.add h_index (Usize.mul i mword)) g)) /\
                                                  
                                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                                        (ensures (fst (fieldPush_spec_body g st h_index wz i) == st)) = ()
                                                  
#restart-solver

#restart-solver 

#push-options "--split_queries always"

#restart-solver

let gray_black_stack_vl_mem_lemma (g:heap{well_formed_heap2 g})
                                  (st: seq Usize.t{stack_props_func g st})
                                  (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                                   (Usize.v (tag_of_object1 hdr_id g) <> infix_tag) /\
                                                   (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n)})
                                  (succ:hp_addr{succ == f_address hdr_id})
                                  (vl: seq Usize.t{vl_props_func g vl})
                   : Lemma
                     (requires (isGrayObject1 hdr_id g) \/ (isBlackObject1 hdr_id g))
                     (ensures (Seq.mem succ st) \/ (Seq.mem succ vl)) =

 assert (stack_props_func g st);
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==> Seq.mem x st);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g ==> Seq.mem (f_address x) st);

 assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g ==> Seq.mem (f_address x) vl);
 assert ((isGrayObject1 hdr_id g) \/ (isBlackObject1 hdr_id g));
 assert (Seq.mem hdr_id (objects2 0UL g));
 assert (Seq.mem (f_address hdr_id) st \/ Seq.mem (f_address hdr_id) vl);
 assert (Seq.mem succ st \/ Seq.mem succ vl);
 ()

#restart-solver 


let darken_helper_lemma (g:heap{well_formed_heap2 g})
                        (st: seq Usize.t{stack_props_func g st})
                        (h_index:hp_addr{is_valid_header1 h_index g})
                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                         
                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                        (j:Usize.t)
                        (vl: seq Usize.t{vl_props_func g vl})
                        (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                  (Usize.v (tag_of_object1 hdr_id g) <> infix_tag) /\
                                  (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n)})
                        (succ:hp_addr{succ == f_address hdr_id})
                  : Lemma
                    (requires  (h_index_within_limits g h_index) /\
                               (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                  
                               (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\

                                
                                                      
                               (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                               (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                  (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                         
                                                  (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) ==
                                                    succ) /\
                                                  (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                  (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                    (ensures fst (darken_helper g st hdr_id) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j)) = 
let succ1 = f_address hdr_id in
let succ2 = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
assert (succ1 == succ2);
if (color_of_object1 hdr_id g = white) then
(
   let succ_index = Usize.add h_index (Usize.mul i mword) in
   assert (is_valid_header hdr_id g);
   valid_succ_color_lemma g hdr_id;
      
   assert (~(isGrayObject1 hdr_id g) /\ ~(isBlackObject1 hdr_id g));
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
   assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
   stack_mem_lemma g st hdr_id;
   assert (Usize.v hdr_id + Usize.v mword < heap_size);
   assert (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n);
   assert (~(Seq.mem (f_address hdr_id) st));
   let st', g' = push_to_stack2 g st hdr_id  in
   push_to_stack2_heap_state_lemma g st hdr_id;
   push_to_stack2_field_size_lemma g st hdr_id;
   assert (~(Seq.mem (f_address hdr_id) vl));
   //assert (f_address hdr_id == read_word g succ_index);
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
   fieldaddress_within_limits_lemma_x_all g;
   //test_allocs g h_index wz;
   assert (Seq.mem hdr_id (get_allocated_block_addresses g));
   let succ' = f_address hdr_id in
   let succ'' = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
   assert (succ' == succ'');
   push_to_stack_heap_and_push_to_graph_equality_lemma1 g st hdr_id vl;
   let st1 = G.push_to_stack_graph1 vl st succ in
   assert (st' == G.push_to_stack_graph1 vl st succ);
   let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j) in
   assert (st'' == G.push_to_stack_graph1 vl st succ);
   assert (st'' == st1);
   assert (st' == st1);
   assert (st' == st'');
   assert (fst (push_to_stack2 g st hdr_id) == st'');
   assert (fst (darken_helper g st hdr_id) == st'');
   assert (fst (darken_helper g st hdr_id) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
   ()
)
else
(
  let st' = st in
  let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st  (Usize.v j) in
  assert (~(color_of_object1 hdr_id g = white));
  assert ((isGrayObject1 hdr_id g) \/ (isBlackObject1 hdr_id g));
  gray_black_stack_vl_mem_lemma g st hdr_id succ vl;
  assert ((Seq.mem (f_address hdr_id) st) \/ (Seq.mem (f_address hdr_id) vl));
  assert (st'' == st);
  //assert (st'' == st');
  assert (fst (darken_helper g st hdr_id) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
  ()
)

#restart-solver

#restart-solver 

#restart-solver

#restart-solver 

#restart-solver

#restart-solver

let fieldPush_spec_body_successor_push_body_equivalence_lemma2 (g:heap{well_formed_heap2 g})
                                                               (st: seq Usize.t{stack_props_func g st})
                                                               (h_index:hp_addr{is_valid_header1 h_index g})
                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                         
                                                               (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                               (j:Usize.t)
                                                               (vl: seq Usize.t{vl_props_func g vl}) 
                                        : Lemma
                                        (requires (h_index_within_limits g h_index) /\
                                                  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                  
                                                  (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                      
                                                  (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                  (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                  (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                  (let succ_index = Usize.add h_index (Usize.mul i mword) in
                                                   (isPointer succ_index g  /\
                                                   (Usize.v (read_word g succ_index) >= Usize.v mword) /\
                                                   (Usize.v (tag_of_object1 (hd_address (read_word g succ_index)) g) <> infix_tag) ==> 
                                                         (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         read_word g succ_index)) /\

                                                   (isPointer succ_index g  /\
                                                   (Usize.v (read_word g succ_index) >= Usize.v mword) /\
                                                   (Usize.v (tag_of_object1 (hd_address (read_word g succ_index)) g) == infix_tag) ==> 
                                                         (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         f_address (parent_closure_of_infix_object g h_index i)))) /\
                                                         
                                                    
                                                  (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                  (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                                          
                                          (ensures (fst (fieldPush_spec_body1 g st h_index wz i) == 
                                                       ( if (isPointer(Usize.add h_index (Usize.mul i mword)) g) then
                                                                (
                                                                      G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) 
                                                                                              (vl) 
                                                                                              (st) 
                                                                                              (Usize.v j)
                                                                )
                                                               else
                                                                (
                                                                      st
                                                                )))) =

assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   fieldaddress_within_limits_lemma_x_all g;
       
   let succ_index = Usize.add h_index (Usize.mul i mword) in
       
   max_wosize_times_mword_multiple_of_mword i;
   sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);

   assert (Usize.v succ_index % Usize.v mword == 0);
   assert (is_hp_addr succ_index);

   lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8); 
   let succ_h = read_word g succ_index in
   let succ_g = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
   assert (succ_h == read_word g succ_index);
   if isPointer succ_index g  then
    (
       //assume (succ_h == succ_g);
       let h_addr_succ = hd_address succ_h in
       if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
       (
          assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
          assert (isPointer (succ_index_fn g h_index i) g);
          assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
          let parent_hdr = parent_closure_of_infix_object g h_index i in
          assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
          assert (Usize.v parent_hdr + Usize.v mword < heap_size);
          assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
          let st', g' = darken_helper g st parent_hdr in
          let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j) in
          assert (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         f_address (parent_closure_of_infix_object g h_index i));
          let succ = f_address parent_hdr in
          let succ1 = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
          darken_helper_lemma g st h_index wz i j vl parent_hdr succ;
          assert (st' == st'');
          assert (fst (fieldPush_spec_body1 g st h_index wz i) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
          ()
          (*assert (succ == succ1);
          darken_helper_lemma g st h_index wz i j vl parent_hdr succ;
          assert (st' == st'');
          assert (fst (fieldPush_spec_body1 g st h_index wz i) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
          ()*)
          
       )
       else
       (
         assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
         let st', g' = darken_helper g st h_addr_succ in
         let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j) in
         let succ1 = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
         let succ = f_address h_addr_succ in
         assert (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                          read_word g succ_index);
         assert ((Usize.v (tag_of_object1 (hd_address (read_word g succ_index)) g) <> infix_tag) ==> 
                                                         (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         read_word g succ_index));
         darken_helper_lemma g st h_index wz i j vl h_addr_succ succ;
         assert (fst (darken_helper g st h_addr_succ) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
         assert (st' == st'');
         assert (fst (fieldPush_spec_body1 g st h_index wz i) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
         ()
         //assert (succ == succ1);
         (*assert (st' == st'');
         assert (fst (fieldPush_spec_body1 g st h_index wz i) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
         ()*)
         
         
       )
    )
   else
   (
     ()
   )

#restart-solver 

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000"


let create_succcessors_for_h_index_lemma_rec_lemma_non_infix (g:heap{well_formed_heap2 g}) 
                                                            (h_index:hp_addr{is_valid_header1 h_index g})
                                           
                                                            (wz: wosize{valid_wosize g h_index wz})
                         
                                                            (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                            (i':Usize.t{Usize.v i' == Usize.v i + 1})
                          :Lemma
                           (ensures (isPointer (Usize.add h_index (Usize.mul i mword)) g /\ 
                                       Usize.v (tag_of_object1 (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) g) <> infix_tag ==> 
                                       create_successors_list_for_h_index g h_index wz i == Seq.cons (read_word g (Usize.add h_index (Usize.mul i mword)))
                                       (create_successors_list_for_h_index g h_index wz i'))) =
()

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries always"

#restart-solver

let rec create_succcessors_for_h_index_lemma1 (g:heap{well_formed_heap2 g}) 

                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header1 h_index g})
                                           
                                             (wz: wosize{(wz == getWosize (read_word g h_index))})

                                            
                         
                                             (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                                             (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})

                                             (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})

                                             (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })

                                             (wz1: wosize{(wz1 == getWosize (read_word g' h_index))})
                          : Lemma
                          (requires 
                                    (objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    (wz == wz1) /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g') /\
                                    (forall j x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                    (forall j x.  Seq.mem x (get_allocated_block_addresses g') /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g' x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)
                                    )
                          (ensures (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       seq_empty_lemma ();
       assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
       ()
    )
  else
   (
     field_reads_all_equal_for_all_objects_lemma g g' v_id;
     field_reads_all_equal_h_index_lemma g g' v_id;
     let succ_index = Usize.add h_index (Usize.mul i mword) in

     assert (Usize.v i < Usize.v wz + 1);
    

     assert (is_fields_within_limit1 h_index wz);

     assert (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size);

     assert (Usize.v i < Usize.v wz + 1);

     assert (Usize.v h_index + (Usize.v i * Usize.v mword) < heap_size);
     
     assert (Usize.v succ_index < heap_size);
     
     field_limits_allocated_blocks_lemma g;
     field_contents_within_limits_allocated_blocks_lemma g;
     fieldaddress_within_limits_lemma_x_all g;
     
     max_wosize_times_mword_multiple_of_mword i;
     sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);

     //assert (Usize.v succ_index < heap_size);
     
      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);

      lemma_len_slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8); 
      
      let succ1 = read_word g' succ_index in
      assert (succ1 == read_word g' succ_index);
      assert (Usize.v succ_index >= Usize.v h_index + Usize.v mword /\
             Usize.v succ_index <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword));
      assert (succ == succ1);
      let i' = Usize.(i +^ 1UL) in
      if isPointer succ_index g  then
      (
          let h_addr_succ = hd_address succ in
          let f_index = f_address h_index in
          f_address_hp_address_lemma h_index;
          assert (hd_address f_index == h_index);
          assert (read_word g (Usize.add h_index (Usize.mul i mword)) == read_word g' (Usize.add h_index (Usize.mul i mword)));
          colorHeader1_tags_lemma v_id g c g';
          assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). tag_of_object1 x g == tag_of_object1 x g');
          assert (Usize.v (tag_of_object1 h_addr_succ g) == Usize.v (tag_of_object1 h_addr_succ g'));
          //test_allocs g h_index wz;
          (*assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
          assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
          assert (Seq.mem (hd_address succ) (objects2 0UL g));
          assert (is_valid_header (hd_address succ) g);

          
          assert (Seq.mem h_index (get_allocated_block_addresses g));*)
         if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
         (
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           let parent_hdr1 = parent_closure_of_infix_object g' h_index i in
           field_limits_allocated_blocks_lemma g;
           field_contents_within_limits_allocated_blocks_lemma g;
           field_limits_allocated_blocks_lemma g';
           field_contents_within_limits_allocated_blocks_lemma g';
           field_points_to_blocks_allocs_lemma g;
           field_points_to_blocks_allocs_lemma g';
           assert (allocs_props_g g h_index);
           assert (allocs_props_g g' h_index);
           assert (parent_closure_index_props g' h_index i);
           colorHeader1_wosize_lemma v_id g c g';
           parent_closure_of_infix_object_lemma  g h_index i v_id c g';
           assert (parent_hdr == parent_hdr1);
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
          
           assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
           assert (isPointer (succ_index_fn g h_index i) g);
           assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
           let parent_hdr = parent_closure_of_infix_object g h_index i in
           assert (is_valid_header parent_hdr g /\
           (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
           (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
           assert (Usize.v parent_hdr + Usize.v mword < heap_size);
           assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
           
           let s_list' = create_successors_list_for_h_index g h_index wz i' in
           let s_list'' = create_successors_list_for_h_index g' h_index wz1 i' in
           create_succcessors_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;
           assert (create_successors_list_for_h_index g h_index wz i' == create_successors_list_for_h_index g' h_index wz1 i');
           let parent_succ = f_address parent_hdr in
           lemma_tl parent_succ s_list'; 
        
           let s_list = Seq.cons parent_succ s_list' in 
           let s_list1 = Seq.cons parent_succ s_list'' in
           assert (s_list == s_list1);
           assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
           ()
         )
         else 
         (
          let s_list' = create_successors_list_for_h_index g h_index wz i' in
          let s_list'' = create_successors_list_for_h_index g' h_index wz1 i' in
          create_succcessors_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;
          assert (create_successors_list_for_h_index g h_index wz i' == create_successors_list_for_h_index g' h_index wz1 i');

          lemma_tl succ s_list'; 
          lemma_tl succ s_list''; 
        
          let s_list = Seq.cons succ s_list' in 
          let s_list1 = Seq.cons succ s_list'' in 
          assert (s_list == s_list1);
          create_succcessors_for_h_index_lemma_rec_lemma_non_infix g h_index wz i i';
          create_succcessors_for_h_index_lemma_rec_lemma_non_infix g' h_index wz1 i i';
          assert (s_list == create_successors_list_for_h_index g h_index wz i);
          assert (isPointer succ_index g');
          assert ((Usize.v (tag_of_object1 h_addr_succ g') <> infix_tag));
          assert (create_successors_list_for_h_index g' h_index wz1 i == Seq.cons (read_word g' (Usize.add h_index (Usize.mul i mword)))
                                       (create_successors_list_for_h_index g' h_index wz1 i'));
                                       
          //assert ( s_list1 == create_successors_list_for_h_index g' h_index wz1 i);
          assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
          ()
         )
          
      )
      else
      (
        let s_list' = create_successors_list_for_h_index g h_index wz i' in

        create_succcessors_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;

        assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
       
        ()
      )
  )

#restart-solver 


#restart-solver 

#reset-options "--z3rlimit 500"

#restart-solver 

let push_to_stack2_create_successors_for_h_index_lemma  (g:heap{well_formed_heap2 g})
                                                        (st: seq Usize.t {stack_props_func g st})
                                    
                    
                                                        (x: hp_addr{is_valid_header1 x g /\
                                                                   ~(Seq.mem (f_address x) st) /\
                                                                   (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                                   })  
                                                       (c:color{c == 2UL})

                                                       (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header1 h_index g})

                                                       (wz: wosize{wz == getWosize (read_word g h_index)})
                                                       (wz1: wosize{(wz1 == getWosize (read_word (snd (push_to_stack2 g st x)) h_index))})

                                                
                                                       (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                     : Lemma
                                        (requires (wz == wz1) /\ 
                                                  (is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                  (color_of_object1 x g == white) /\
                                                  (Seq.mem x (get_allocated_block_addresses g)) /\
                                                  
                                                  (h_index_within_limits g h_index) (*/\
                                                  (h_index_within_limits (snd (push_to_stack2 g st x)) h_index)*))
                                        (ensures create_successors_list_for_h_index g h_index wz i == 
                                                   create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i) = 

if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in

   
   let g' = colorHeader1 x g gray in 

   assert (well_formed_heap2 g');
    
    objects2_equal_lemma 0UL g g';
    
    get_allocated_block_addresses_lemma g g' x c;
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))));
    assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
    //colorHeader1_Lemma x g c; 

    assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
    fieldaddress_within_limits_lemma_x_all g;

    assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
    //well_formed_allocated_blocks_lemma g x c g';
    

    //assert (well_formed_allocated_blocks g');
    
    //assert (Seq.mem f_x stk');
    G.is_vertex_set_lemma2 stk';
    assert (G.is_vertex_set stk');
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))));
    assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
    fieldaddress_within_limits_lemma_x_all g';
    
    create_succcessors_for_h_index_lemma1 g h_index wz i x c g' wz1;
    assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
    assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i);
    ()
)
    
else
(
   let f_x = f_address x in
   lemma_tail_snoc st f_x;
   lemma_mem_snoc st f_x; 
   let st' = snoc st f_x in
   let g' = colorHeader1 x g gray in 
   objects2_equal_lemma 0UL g g';
   get_allocated_block_addresses_lemma g g' x c;
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))));
    assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
    //colorHeader1_Lemma x g c; 

    assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
    fieldaddress_within_limits_lemma_x_all g;

    assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
    
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))));
    assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
    fieldaddress_within_limits_lemma_x_all g';
    
    //well_formed_allocated_blocks_lemma g x c g';
    

    //assert (well_formed_allocated_blocks g');
    
    G.snoc_unique_lemma f_x st;
    assert (G.is_vertex_set st');
   
   
    create_succcessors_for_h_index_lemma1 g h_index wz i x c g' wz1;
    assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
    assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i);
    ()
 )

#restart-solver 

#restart-solver

let darken_helper_create_successors_for_h_index_lemma (g:heap{well_formed_heap2 g})
                                                      (st: seq Usize.t{stack_props_func g st})
                                                      (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header1 h_index g})
                                                      (c:color{c == 2UL})
                                                      (hdr_id: hp_addr{is_valid_header1 hdr_id g /\
                                                                        (Usize.v (tag_of_object1 hdr_id g) <> infix_tag) /\
                                                                        (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n)})
                                                      (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                                      (wz1: wosize{(wz1 == getWosize (read_word (snd (darken_helper g st hdr_id)) h_index))})
                                                      (j:Usize.t{Usize.v j <= Usize.v wz + 1 /\ Usize.v j >= 1})
                                                      
         
                                                      
          : Lemma
            (requires (wz == wz1) /\
                      (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                      (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (darken_helper g st hdr_id))) 
                                                                                             (snd (darken_helper g st hdr_id))) /\
                      (h_index_within_limits g h_index))
                      
            (ensures (create_successors_list_for_h_index g h_index wz j == 
                                    create_successors_list_for_h_index (snd (darken_helper g st hdr_id)) h_index wz1 j)) = 
if (color_of_object1 hdr_id g = white) then
(
   assert (is_valid_header hdr_id g);
   valid_succ_color_lemma g hdr_id;
      
   assert (~(isGrayObject1 hdr_id g) /\ ~(isBlackObject1 hdr_id g));
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
   assert (forall x. Seq.mem x st ==> isGrayObject1 (hd_address x) g);
   stack_mem_lemma g st hdr_id;
   assert (Usize.v hdr_id + Usize.v mword < heap_size);
   assert (UInt.fits (Usize.v hdr_id + Usize.v mword) Usize.n);
   assert (~(Seq.mem (f_address hdr_id) st));
   let st', g' = push_to_stack2 g st hdr_id  in
   push_to_stack2_heap_state_lemma g st hdr_id;
   push_to_stack2_field_size_lemma g st hdr_id;
   push_to_stack2_create_successors_for_h_index_lemma g st hdr_id c h_index wz wz1 j;
   ()
)
else
(
   ()
)

#restart-solver 

#restart-solver

let fieldPush_spec_body_create_successors_for_h_index_lemma  (g:heap{well_formed_heap2 g})
                                                             (st: seq Usize.t{stack_props_func g st})
                                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header1 h_index g })
                                                             (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                                             (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})  
                                                             (wz1: wosize{wz1 == getWosize (read_word (snd (fieldPush_spec_body1 g st h_index wz i)) h_index) 
                                                                                   })
                                                            (c:color{c == 2UL})
                                                            (j:Usize.t{Usize.v j <= Usize.v wz + 1 /\ Usize.v j >= 1})
                                                                    
                                      : Lemma
                                        (requires (wz == wz1) /\ 
                                                  
                                                  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                    (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (fieldPush_spec_body1 g st h_index wz i))) 
                                                                                                          (snd (fieldPush_spec_body1 g st h_index wz i))) /\
                                                  (h_index_within_limits g h_index))
                                        (ensures (create_successors_list_for_h_index g h_index wz j == 
                                                     create_successors_list_for_h_index (snd (fieldPush_spec_body1 g st h_index wz i)) h_index wz1 j)) =

   assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
       
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);
       
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));
  
  
  if isPointer succ_index g  then
    (
      let h_addr_succ = hd_address succ in

      if (Usize.v (tag_of_object1 h_addr_succ g) = infix_tag) then 
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) == infix_tag);
        assert (isPointer (succ_index_fn g h_index i) g);
        assert (Usize.v (tag_of_object1 (hd_address (read_succ g h_index i)) g) == infix_tag);
        let parent_hdr = parent_closure_of_infix_object g h_index i in
        assert (is_valid_header parent_hdr g /\
                (Usize.v (tag_of_object1 parent_hdr g) == closure_tag) /\
                (Usize.v (tag_of_object1 parent_hdr g) <> infix_tag));
        assert (Usize.v parent_hdr + Usize.v mword < heap_size);
        assert (UInt.fits (Usize.v parent_hdr + Usize.v mword) Usize.n);
        let st', g' = darken_helper g st parent_hdr in
        assert (well_formed_heap2 g');
        field_limits_allocated_blocks_lemma g';
        assert (Seq.mem parent_hdr (get_allocated_block_addresses g));
        
        darken_helper_create_successors_for_h_index_lemma g st h_index c parent_hdr wz wz1 j;
        ()
     )
      else
      (
        assert (Usize.v (tag_of_object1 h_addr_succ g) <> infix_tag);
        let st', g' = darken_helper g st h_addr_succ in
        field_limits_allocated_blocks_lemma g';
        assert (Seq.mem h_addr_succ (get_allocated_block_addresses g));
        
        darken_helper_create_successors_for_h_index_lemma g st h_index c h_addr_succ wz wz1 j;
        ()
        
      )
   )
  else
   ( 
       ()
   )

#restart-solver

#restart-solver 

#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#restart-solver 

let graph_successors_create_from_an_index_equivalence_lemma  (g:heap{well_formed_heap2 g})
                                                             (st: seq Usize.t{stack_props_func g st})
                                                           
                                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})

                                                             (wz: wosize{wz == getWosize (read_word g h_index)})

                                                             (j:Usize.t{Usize.v j < Usize.v wz + 1 /\ Usize.v j >= 1})

                                                                
                                                                                     
                                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                                                 (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                                                 (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                                                 (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                                
                                                              (i:Usize.t {Usize.v i <= Seq.length f})
                                                              
                                                              (g': heap {well_formed_heap2 g' /\
                                                                            g' == (snd (fieldPush_spec_body1 g st h_index wz j))})
                                                              (wz1: wosize{wz1 == getWosize (read_word g' h_index)})
                                                              (f1: seq Usize.t)

                                             : Lemma
                                               (requires (wz == wz1) /\ (f == f1) /\
                                                         (h_index_within_limits g h_index)  /\
                                                         (h_index_within_limits g' h_index) /\
                                                         (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                                         (all_field_address_are_word_aligned (get_allocated_block_addresses g') g') /\
                                                          (let grph = create_graph_from_heap g' in
                                                              let l = G.successors grph (f_address h_index) in
                                                              (f1 == l) /\ (Seq.length f1 <= Usize.v wz1)))
                                               (ensures graph_successors_create_from_an_index g h_index f i == graph_successors_create_from_an_index g' h_index f1 i) = ()

#restart-solver 

#reset-options "--z3rlimit 500"

#restart-solver

#restart-solver

let stack_properties   (g:heap{well_formed_heap2 g})
                       (st: seq Usize.t) =
  G.is_vertex_set st /\  (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                                  Seq.mem x st)

let vl_properties(g:heap{well_formed_heap2 g})
                 (vl: seq Usize.t) =
  (G.is_vertex_set vl) /\  (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl)
                                                                     
let h_index_properties (g:heap{well_formed_heap2 g})
                        (h_index:hp_addr) =
   Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\ (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                 is_valid_header h_index g

#restart-solver 

#restart-solver


let slice_length_props (g:heap{well_formed_heap2 g}) =
     (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)

let slice_length_props_lemma (g:heap{well_formed_heap2 g})
                       (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}) 
                : Lemma 
                  (ensures length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)=
 
lemma_len_slice g (Usize.v t) ((Usize.v t) + (Usize.v mword));
()

let slice_length_props_all_lemma (g:heap{well_formed_heap2 g}) 
                : Lemma
                  (ensures (slice_length_props g)) =
 Classical.forall_intro (Classical.move_requires (slice_length_props_lemma  g))   


let lemma_len_slice_invoke1 (g:heap{well_formed_heap2 g})
                           (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0})
                : Lemma
                  (ensures (length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)) =
lemma_len_slice g (Usize.v t) ((Usize.v t) + (Usize.v mword));
()

let lemma_len_slice_invoke_all1 (g:heap{well_formed_heap2 g})
                : Lemma
                  (ensures (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)) =
Classical.forall_intro (Classical.move_requires (lemma_len_slice_invoke g))

let create_succcessors_for_h_index_lemma5_helper (g:heap{well_formed_heap2 g})
                                                  (g':heap{well_formed_heap2 g'}) 
                                                  (h_index:hp_addr {Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                    is_valid_header1 h_index g /\
                                                                     is_valid_header1 h_index g'})
                                                 (wz:wosize{(Usize.v wz == Usize.v (getWosize (read_word g h_index)))})=
                                                     
 (forall i. Usize.v i >= 1 /\ Usize.v i <= Usize.v wz + 1 ==> is_hp_addr (Usize.add h_index (Usize.mul i mword)) /\
                                                      read_word g (Usize.add h_index (Usize.mul i mword)) ==
                                                      read_word g' (Usize.add h_index (Usize.mul i mword)))

#restart-solver

let fieldPush_spec_successor_push_itr_equivalence_lemma2_pre_props  (g:heap{well_formed_heap2 g})
                                                                        (st: seq Usize.t{stack_props_func g st})
                                                                        (h_index:hp_addr{ Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                               (Usize.v h_index % Usize.v mword == 0) /\
                                                                               is_valid_header1 h_index g})
                                                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                                                        (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                        (j:Usize.t)
                                                                        (vl: seq Usize.t{vl_props_func g vl}) 
                                                                         =
(h_index_within_limits g h_index) /\
(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
(Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
(Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
(Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
(graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                          (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
(forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
(forall x. Seq.mem x vl ==> ~(Seq.mem x st))

#restart-solver 

let fieldPush_spec_successor_push_itr_equivalence_lemma2_post_props  (g:heap{well_formed_heap2 g /\
                                                                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)})
                                                                        (st: seq Usize.t{stack_props_func g st})
                                                                        (h_index:hp_addr{ Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                               (Usize.v h_index % Usize.v mword == 0) /\
                                                                               is_valid_header1 h_index g /\
                                                                               (h_index_within_limits g h_index) /\
                                                                               (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices)})
                                                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index)) /\
                                                                                   Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz}) 
                                                                        (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                        (j:Usize.t{(Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)))})
                                                                        (vl: seq Usize.t{vl_props_func g vl /\
                                                                                         (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                                                         (forall x. Seq.mem x vl ==> ~(Seq.mem x st))}) 
                                                                         =
((fst (fieldPush_spec1 g st h_index wz i)) ==  G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index))
                                                                                  (vl)
                                                                                  (st)
                                                                                  (Usize.v j))

let length_less_than_or_equal_lemma (s:seq Usize.t)
                                    (j:Usize.t)
            : Lemma
              (requires Usize.v j <= Seq.length s /\ ~(Usize.v j == Seq.length s))
              (ensures Usize.v j < Seq.length s) = ()
              
#restart-solver

let push_to_stack2_vl_props_lemma (g:heap{well_formed_heap2 g})
                                  (st: seq Usize.t{stack_props_func g st})
                                    
                                  (x: hp_addr{is_valid_header1 x g /\
                                                ~(Seq.mem (f_address x) st) /\ (color_of_object1 x g == white) /\
                                                 (Usize.v (tag_of_object1 x g) <> infix_tag)
                                                })
                                  (vl: seq Usize.t{vl_props_func g vl}) 
                     : Lemma
                     (ensures (vl_props_func (snd (push_to_stack2 g st x)) vl)) =
assert (vl_props_func g vl);
assert ((forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
        (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==>  Seq.mem x vl));
push_to_stack2_visited_list_valid_header_lemma g st x vl;
push_to_stack_mem_lemma_black_nodes_visited_list_lemma g st x vl;
assert (vl_props_func (snd (push_to_stack2 g st x)) vl);
()

let fieldPush_spec_body_vl_props_lemma  (g:heap{well_formed_heap2 g})
                                        (st: seq Usize.t{stack_props_func g st})
                                        (h_index:hp_addr{is_valid_header1 h_index g})
                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})              
                                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                        (vl: seq Usize.t{vl_props_func g vl}) 
                            : Lemma
                              (ensures (vl_props_func (snd (fieldPush_spec_body1 g st h_index wz i)) vl)) =
fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;
assert (vl_props_func (snd (fieldPush_spec_body1 g st h_index wz i)) vl);
()

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver

let h_index_field_within_heap_size (g:heap{well_formed_heap2 g})
                                       
                                   (h_index:hp_addr{ Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                         (Usize.v h_index % Usize.v mword == 0) /\
                                                         is_valid_header1 h_index g})
                                   (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                   (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                        : Lemma
                          (ensures (Usize.v h_index + (Usize.v i * Usize.v mword) < heap_size)) =
assert (well_formed_heap2 g);
assert (is_valid_header1 h_index g);
assert (Seq.mem h_index (get_allocated_block_addresses g));
field_limits_allocated_blocks_lemma g;
assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
assert (Usize.v wz == Usize.v (getWosize (read_word g h_index)));
assert (is_fields_within_limit1 h_index wz);
()

#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries always" (BE CAREFUL IN USING SPLIT QUERIES --- SOMETIMES IT CAUSES UNDEFINED BEHAVIOUR)

#restart-solver

//#reset-options "--z3rlimit 1000"

#restart-solver

#push-options "--split_queries always"

#restart-solver

let rec fieldPush_spec_successor_push_itr_equivalence_lemma2 (g:heap{well_formed_heap2 g})
                                                             (st: seq Usize.t{stack_props_func g st})
                                                             (h_index:hp_addr{ Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                               (Usize.v h_index % Usize.v mword == 0) /\
                                                                               is_valid_header1 h_index g})
                                                             (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                                             (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                             (j:Usize.t)
                                                             (vl: seq Usize.t{vl_props_func g vl}) 
                                                             (c:color{Usize.v c == 2})
                                           : Lemma
                                             (requires fieldPush_spec_successor_push_itr_equivalence_lemma2_pre_props g st h_index wz i j vl)
                                            
                                            (ensures   fieldPush_spec_successor_push_itr_equivalence_lemma2_post_props g st h_index wz i j vl)
                                            (decreases ((Usize.v wz + 1) - Usize.v i))  = 
  let grph = create_graph_from_heap g in
  let l = G.successors grph (f_address h_index) in
  graph_successors_length_lemma g h_index;
  graph_successors_mem_lemma g h_index;
  assert (Seq.length l <= Usize.v (getWosize (read_word g h_index)));
  assert (forall x. Seq.mem x  l ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));
 if Usize.v i = Usize.v wz + 1 then
  (
    create_successors_list_for_h_index_i_equals_wz_plus_one_implies_succ_list_from_j_is_empty g st h_index wz i j;
    assert (Usize.v j == Seq.length l);
    let st' = G.successor_push_itr1 l vl st (Usize.v j) in
    G.successor_push_itr1_lemma1 l vl st (Usize.v j);
    assert (st' == st);
    assert (fst (fieldPush_spec1 g st h_index wz i) == st);
    assert (G.successor_push_itr1 l vl st (Usize.v j) == st);
    ()
  )
  else
  (
    let i' = Usize.add i 1UL in
    assert (Usize.v i < Usize.v wz + 1);
    assert (Seq.length (objects2 0UL g) > 0);
    h_index_field_within_heap_size g h_index wz i;
    //assume (UInt.fits (Usize.v h_index + (Usize.v i * Usize.v mword)) Usize.n);
    assert (Usize.v h_index + (Usize.v i * Usize.v mword) < heap_size);
    let succ_index = Usize.add h_index (Usize.mul i mword) in
       
    assert (Usize.v succ_index < heap_size);
    max_wosize_times_mword_multiple_of_mword i;
    sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
    assert (Usize.v succ_index % Usize.v mword == 0);
    assert (is_hp_addr succ_index);
    //let succ = read_word g succ_index in
    let st', g' = fieldPush_spec_body1 g st h_index wz i in
    arithmetic_lemma i wz;
    assert (Usize.v i <= Usize.v wz);
    arithmetic_lemma1 i wz;
    assert (Usize.v i - 1 < Usize.v wz);
    //assert (Seq.length l <= Usize.v wz);
   // assert (Usize.v j <= Seq.length l);
    if (Usize.v j = Seq.length l) then
    (
       let l' = (graph_successors_create_from_an_index g h_index l j) in
       assert (l' == Seq.empty);
       length_empty_lemma l';
       assert (Seq.length l' == 0);
       (*This means starting from index i if we scan the fields of h_index, we will not get any field pointers. 
         So even if we call fieldPush_spec_body, it will return the
        stack as unaffected. There is no point in recursively continuing the fieldPush at this point.*)
        
        assert (Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) == 0);
        create_successors_list_for_h_index_recursing_property_lemma3 g h_index wz i i';
        assert ((create_successors_list_for_h_index g h_index wz i == Seq.empty) ==> 
             (create_successors_list_for_h_index g h_index wz i' == Seq.empty));
        
        assert ((graph_successors_create_from_an_index g h_index l j) ==
             (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i));
       (*Essential pre-condition to continue the recursive call*)
       (*---------------------------------------------------------------------------------------------------------------------------------------*)
       assert ((graph_successors_create_from_an_index g h_index l j) ==
               (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i'));
       let st_gr = G.successor_push_itr1 l vl st (Usize.v j) in
       G.successor_push_itr1_lemma1 l vl st (Usize.v j);
       assert (st_gr == st);

       create_successors_list_for_h_index_recursing_property_lemma4  g h_index wz i;
        //This is required to establish that fieldPush_spec_body returns the stack as unchanged as the field value is not a pointer
        //---------------------------------------------------------------------------------------------------------------------------------------
       assert (~(isPointer(Usize.add h_index (Usize.mul i mword)) g));
       fieldPush_spec_body_successor_push_body_equivalence_lemma3 g st h_index wz i vl;
       
       assert (st' == st); 
       slice_length_props_all_lemma g;
       slice_length_props_all_lemma g';
       assert (slice_length_props g);
       assert (slice_length_props g');
       //fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
       fieldPush_spec_body_graph_lemma g st h_index wz i;
       //assert (well_formed_allocated_blocks g');
       //fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
       let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
       let st2 = G.successor_push_itr1 l vl st (Usize.v j) in
        let wz' = getWosize (read_word g' h_index) in
       assert (wz == wz');
       assert (objects2 0UL g == objects2 0UL g');
       fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
       fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;
       (*Essential pre-condition to continue the recursive call*)
       (*---------------------------------------------------------------------------------------------------------------------------------------*)
       assert ((graph_successors_create_from_an_index g h_index l j) ==
             (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i')); 
       
       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j vl c;
       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st (Usize.v j));
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body g st h_index wz i)) 
                                                                                        (fst (fieldPush_spec_body g st h_index wz i))
                                                                                        h_index 
                                                                                        wz
                                                                                        i');
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');
       G.successor_push_itr1_lemma1 l vl st (Usize.v j);
       assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 l (vl) (st) (Usize.v j));
       ()
    )
    else
    (
      (*In this branch only, we can invoke (G.successor_push_body1). This is because j should be < Seq.length l *)
       assert (~(Usize.v j == Seq.length l));
       length_less_than_or_equal_lemma l j;
       assert (Usize.v j < Seq.length l);
       assert (Usize.v i < Usize.v wz + 1);
        
       field_limits_allocated_blocks_lemma g;
       field_contents_within_limits_allocated_blocks_lemma g;
       fieldaddress_within_limits_lemma_x_all g;

       field_limits_allocated_blocks_lemma g';
       field_contents_within_limits_allocated_blocks_lemma g';
       fieldaddress_within_limits_lemma_x_all g';
        
       assert (is_hp_addr succ_index);
       lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
       assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
       assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
       assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);
       //let succ = read_word g succ_index in
       let succ = get_succ_value g h_index wz i in
       //let b = isPointer succ_index g in
       // 2 cases
       //Case 1: (isPointer(Usize.add h_index (Usize.mul i mword)) g)
        if ((*b*)isPointer succ_index g) then
        (
         let h_addr_succ = hd_address succ in
         //test_allocs g h_index wz;
         //assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
         //assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
         //assert (Seq.mem (hd_address succ) (objects2 0UL g));
         //assert (is_valid_header (hd_address succ) g);

         //assert (well_formed_allocated_blocks g);
         assert (Seq.mem h_index (get_allocated_block_addresses g));
         
         let tg = tag_of_object1 h_addr_succ g in
         let j' = Usize.add j 1UL in
         (*assert ((forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x)))) /\
                                   (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) /\
                                   (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                            (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                            (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)); *)
                                            
           assert (is_hp_addr (Usize.add h_index (Usize.mul i mword)));
           assert (Usize.v (field_ptr_construct g h_index wz i) == Usize.v (Usize.add h_index (Usize.mul i mword)));
           assert (isPointer succ_index g);
           assert (field_ptr_construct g h_index wz i == succ_index);
           assert (isPointer (field_ptr_construct g h_index wz i) g);
           create_successors_list_for_h_index_pointer_lemma g h_index wz i;
           assert (Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0);

           
           if Usize.v tg = infix_tag then
           (
             (*assert (Usize.v tg == infix_tag);
             create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j3 g h_index wz i j;
             assert (Seq.index l (Usize.v j) == f_address (parent_closure_of_infix_object g h_index i));
             create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j2 g h_index wz i j;  
             let st'' = G.successor_push_body1 l vl st (Usize.v j) in
             //fieldPush_spec_body_lemma should ensure that the stack returned by fieldPush_spec_body and successor_push_body are the same
             (*Call fieldPush_spec_body_lemma*)
             fieldPush_spec_body_successor_push_body_equivalence_lemma2 g st h_index wz i j vl;                                            
             assert (st' == st'');
             field_limits_allocated_blocks_lemma g;
             //field_limits_allocated_blocks_lemma g';
             field_contents_within_limits_allocated_blocks_lemma g';
             lemma_len_slice_invoke_all1 g;
             lemma_len_slice_invoke_all1 g';
             assert (Seq.mem h_index (get_allocated_block_addresses g));
             assert (Seq.mem h_index (get_allocated_block_addresses g'));
             assert  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);
             assert (stack_props_func g st);
             assert (Usize.v wz == Usize.v (getWosize (read_word g h_index)));
             
             //fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
             //assert (well_formed_allocated_blocks g');
             
             fieldPush_spec_body_graph_lemma g st h_index wz i;
             assert  (create_graph_from_heap g == create_graph_from_heap g');
             //assert (well_formed_allocated_blocks g');
             //fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
             let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
             let st2 = G.successor_push_itr1 l vl st' (Usize.v j') in
             let wz' = getWosize (read_word g' h_index) in
             assert (wz == wz');
             assert (objects2 0UL g == objects2 0UL g');
             assert (vl_props_func g vl);
             assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
             fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
             fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;

         (*Essential pre-condition to continue the recursive call*)
        (*---------------------------------------------------------------------------------------------------------------------------------------*)
        assert (graph_successors_create_from_an_index g h_index l j' == 
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');

        assert ((forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
              (forall x. Seq.mem x vl ==> ~(Seq.mem x st')));
        assert (Usize.v j' <= Seq.length l);

        assert (is_fields_within_limit1 h_index (getWosize (read_word g' h_index)));

        assert (well_formed_heap2 g');
        assert (get_allocated_block_addresses g ==  get_allocated_block_addresses g');
        assert (Seq.mem h_index (get_allocated_block_addresses g));
        assert (Seq.mem h_index (get_allocated_block_addresses g'));
        field_contents_within_limits_allocated_blocks_lemma g';
        
                                           
       
       assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g' h_index)) g');
             
       //fieldaddress_within_limits_lemma_x_all g';
       (*assert (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g' h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0);*)

       
       assert (all_field_address_are_word_aligned (get_allocated_block_addresses g') g');
       graph_successors_create_from_an_index_equivalence_lemma g st h_index wz i l j' g' wz' l;
       assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');
       //assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');
       
       //assert (h_index_within_limits g h_index);

       //assert (well_formed_allocated_blocks g');
       assert (h_index_within_limits g h_index);
       assert (Usize.v i' <= Usize.v wz + 1 /\ Usize.v i' >= 1);
       assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
       assert (wz' == getWosize (read_word (snd (fieldPush_spec_body1 g st h_index wz i)) h_index));
       assert (Usize.v i' <= Usize.v wz + 1 /\ Usize.v i' >= 1);
       fieldPush_spec_body_create_successors_for_h_index_lemma g st h_index wz i wz' c i';

       //create_succcessors_for_h_index_lemma3 g h_index wz i' g' wz';
       
       assert (graph_successors_create_from_an_index g h_index l j' == 
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');
       assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');

       
       //create_succcessors_for_h_index_lemma5 g h_index wz st i' i g' wz';
       //fieldPush_spec_body_create_successors_for_h_index_lemma g st h_index wz i wz' 2UL i';
       assert ((create_successors_list_for_h_index g h_index wz i' == 
                create_successors_list_for_h_index g' h_index wz' i'));
       
       assert (graph_successors_create_from_an_index g' h_index l j' == 
                          create_successors_list_for_h_index g' h_index (getWosize (read_word g' h_index)) i');
                          
       
       assert ((h_index_within_limits g' h_index) /\
               (all_field_address_are_word_aligned (get_allocated_block_addresses g') g') /\
               (Seq.mem (f_address h_index) (create_graph_from_heap g').vertices) /\
               (Seq.length (G.successors (create_graph_from_heap g') (f_address h_index)) <= Usize.v wz) /\
               (Usize.v j' <= Seq.length (G.successors (create_graph_from_heap g') (f_address h_index))) /\
               (graph_successors_create_from_an_index g' h_index (G.successors (create_graph_from_heap g') (f_address h_index)) j') ==
                                                          (create_successors_list_for_h_index g' h_index (getWosize (read_word g' h_index)) i'));
       assert ((forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
               (forall x. Seq.mem x vl ==> ~(Seq.mem x st')));
       fieldPush_spec_body_vl_props_lemma g st h_index wz i vl;
       assert (vl_props_func g' vl);
       assert (fieldPush_spec_successor_push_itr_equivalence_lemma2_pre_props g' st' h_index wz i' j' vl);
       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j' vl c;

       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st' (Usize.v j'));
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                                                        (fst (fieldPush_spec_body1 g st h_index wz i))
                                                                                        h_index 
                                                                                        wz
                                                                                        i');
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');
       G.successor_push_itr1_lemma l vl st (Usize.v j);
       assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 l (vl) (st)  (Usize.v j));
       assert (fst (fieldPush_spec1 g st h_index wz i) == 
                                                            G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index))
                                                                                  (vl)
                                                                                  (st)
                                                                                  (Usize.v j));                                                                                               
       ()*)
       admit()
       
           )
           else
           (
             assert (Usize.v tg <> infix_tag);
             create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j1 g h_index wz i j;
             //This is the essential precondition for fieldPush_spec body lemma to get the fact that the fieldPush_body and successor_push_body pushes the same field pointer
             //to the stack
             assert (Seq.index l (Usize.v j) ==  read_word g (Usize.add h_index (Usize.mul i mword)));
             create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j2 g h_index wz i j;  
             let st'' = G.successor_push_body1 l vl st (Usize.v j) in
             //fieldPush_spec_body_lemma should ensure that the stack returned by fieldPush_spec_body and successor_push_body are the same
             (*Call fieldPush_spec_body_lemma*)
             fieldPush_spec_body_successor_push_body_equivalence_lemma2 g st h_index wz i j vl;
             assert (st' == st'');
             field_limits_allocated_blocks_lemma g;
             //field_limits_allocated_blocks_lemma g';
             field_contents_within_limits_allocated_blocks_lemma g';
             lemma_len_slice_invoke_all1 g;
             lemma_len_slice_invoke_all1 g';
             assert (Seq.mem h_index (get_allocated_block_addresses g));
             assert (Seq.mem h_index (get_allocated_block_addresses g'));
             assert  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);
             assert (stack_props_func g st);
             assert (Usize.v wz == Usize.v (getWosize (read_word g h_index)));
             
             //fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
             //assert (well_formed_allocated_blocks g');
             
             fieldPush_spec_body_graph_lemma g st h_index wz i;
             assert  (create_graph_from_heap g == create_graph_from_heap g');
             //assert (well_formed_allocated_blocks g');
             //fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
             let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
             let st2 = G.successor_push_itr1 l vl st' (Usize.v j') in
             let wz' = getWosize (read_word g' h_index) in
             assert (wz == wz');
             assert (objects2 0UL g == objects2 0UL g');
             assert (vl_props_func g vl);
             assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
             fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
             fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;

         (*Essential pre-condition to continue the recursive call*)
        (*---------------------------------------------------------------------------------------------------------------------------------------*)
        assert (graph_successors_create_from_an_index g h_index l j' == 
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');

        assert ((forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
              (forall x. Seq.mem x vl ==> ~(Seq.mem x st')));
        assert (Usize.v j' <= Seq.length l);

        assert (is_fields_within_limit1 h_index (getWosize (read_word g' h_index)));

        assert (well_formed_heap2 g');
        assert (get_allocated_block_addresses g ==  get_allocated_block_addresses g');
        assert (Seq.mem h_index (get_allocated_block_addresses g));
        assert (Seq.mem h_index (get_allocated_block_addresses g'));
        field_contents_within_limits_allocated_blocks_lemma g';
        
                                           
       
       assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g' h_index)) g');
             
       //fieldaddress_within_limits_lemma_x_all g';
       (*assert (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g' h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0);*)

       
       assert (all_field_address_are_word_aligned (get_allocated_block_addresses g') g');
       graph_successors_create_from_an_index_equivalence_lemma g st h_index wz i l j' g' wz' l;
       assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');
       //assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');
       
       //assert (h_index_within_limits g h_index);

       //assert (well_formed_allocated_blocks g');
       assert (h_index_within_limits g h_index);
       assert (Usize.v i' <= Usize.v wz + 1 /\ Usize.v i' >= 1);
       assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
       assert (wz' == getWosize (read_word (snd (fieldPush_spec_body1 g st h_index wz i)) h_index));
       assert (Usize.v i' <= Usize.v wz + 1 /\ Usize.v i' >= 1);
       fieldPush_spec_body_create_successors_for_h_index_lemma g st h_index wz i wz' c i';

       //create_succcessors_for_h_index_lemma3 g h_index wz i' g' wz';
       
       assert (graph_successors_create_from_an_index g h_index l j' == 
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');
       assert (graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j');

       
       //create_succcessors_for_h_index_lemma5 g h_index wz st i' i g' wz';
       //fieldPush_spec_body_create_successors_for_h_index_lemma g st h_index wz i wz' 2UL i';
       assert ((create_successors_list_for_h_index g h_index wz i' == 
                create_successors_list_for_h_index g' h_index wz' i'));
       
       assert (graph_successors_create_from_an_index g' h_index l j' == 
                          create_successors_list_for_h_index g' h_index (getWosize (read_word g' h_index)) i');
                          
       
       fieldPush_spec_body_vl_props_lemma g st h_index wz i vl;
       assert (vl_props_func g' vl);
       assert (fieldPush_spec_successor_push_itr_equivalence_lemma2_pre_props g' st' h_index wz i' j' vl);
       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j' vl c;

       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st' (Usize.v j'));
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body1 g st h_index wz i)) 
                                                                                        (fst (fieldPush_spec_body1 g st h_index wz i))
                                                                                        h_index 
                                                                                        wz
                                                                                        i');
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');
       G.successor_push_itr1_lemma l vl st (Usize.v j);
       assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 l (vl) (st)  (Usize.v j));
       assert (fst (fieldPush_spec1 g st h_index wz i) == 
                                                            G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index))
                                                                                  (vl)
                                                                                  (st)
                                                                                  (Usize.v j));                                                                                               
       ()
       )
        )
        else
        (
              //fieldPush_spec_body returns the stack as unchanged as the field value is not a pointer
       //---------------------------------------------------------------------------------------------------------------------------------------
       //assert (~(b));
       create_successors_list_for_h_index_recursing_property_lemma g h_index wz i i';
       assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g h_index wz i');

       //fieldPush_spec_body_lemma should ensure that the stack is returned as unchanged
       (*Call fieldPush_spec_body_lemma*)
       fieldPush_spec_body_successor_push_body_equivalence_lemma2 g st h_index wz i j vl;
       assert (st == st');

       field_limits_allocated_blocks_lemma g;
       field_contents_within_limits_allocated_blocks_lemma g';
       lemma_len_slice_invoke_all g;
       lemma_len_slice_invoke_all g';
       //assert (forall (t:hp_addr). length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8);
                                 
       (*assert (forall (t:hp_addr). length (slice (snd (fieldPush_spec_body1 g st h_index wz i)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8);*)
       //fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
       fieldPush_spec_body_graph_lemma g st h_index wz i;

       //assert (well_formed_allocated_blocks g');
       assert (Seq.mem h_index (get_allocated_block_addresses g));
       assert (Seq.mem h_index (get_allocated_block_addresses g'));
       assert (stack_props_func g' st');
       //fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
       let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
       let st2 = G.successor_push_itr1 l vl st (Usize.v j) in
       let wz' = getWosize (read_word g' h_index) in
       assert (wz == wz');
       assert (objects2 0UL g == objects2 0UL g');
       
       fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
       fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;
       
       

       (*Essential pre-condition to continue the recursive call*)
       (*---------------------------------------------------------------------------------------------------------------------------------------*)
       assert ((graph_successors_create_from_an_index g h_index l j) ==
             (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i')); 

       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j vl c;
       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st (Usize.v j));
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body g st h_index wz i)) 
                                                                                        (fst (fieldPush_spec_body g st h_index wz i))
                                                                                        h_index 
                                                                                        wz
                                                                                        i');
       (*assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');*)
       G.successor_push_itr1_lemma l vl st (Usize.v j);
       (*assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 l (vl) (st) (Usize.v j));*)
       
       ()
           
        )
       
    )
  )

#reset-options "--z3rlimit 1000"

#restart-solver 

#restart-solver 

#restart-solver

let all_mem_implies_subset (s1:seq Usize.t)
                           (s2:seq Usize.t)
                   : Lemma
                     (requires (G.is_vertex_set s1 /\
                                G.is_vertex_set s2 /\
                                (forall x. Seq.mem x s1 ==> Seq.mem x s2)))
                     (ensures (G.subset_vertices s1 s2)) = ()

#restart-solver

#restart-solver 


let all_mem_st_mem_st'_in_stack (st:stack)
                                (st':stack) = (forall x. Seq.mem x st ==> Seq.mem x st')



#restart-solver

#restart-solver

let valid_header_lemma1 (g:heap{well_formed_heap2 g})
                        (i:nat)
                        (succ:seq Usize.t { i <= Seq.length succ  ==>
                                     ((forall x. Seq.mem x (Seq.slice succ i (Seq.length succ)) ==> 
                                              Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                      (forall x. Seq.mem x (Seq.slice succ i (Seq.length succ)) ==> 
                                              is_valid_header1 x g))})
             : Lemma
               (ensures ((i + 1) <= Seq.length succ ==> 
                              ((forall x. Seq.mem x (Seq.slice succ (i + 1) (Seq.length succ)) ==> 
                                              Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                      (forall x. Seq.mem x (Seq.slice succ (i + 1) (Seq.length succ)) ==> 
                                              is_valid_header1 x g)))) = ()

let color_stack_mem_lemma  (g:heap{well_formed_heap2 g})
                               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                 (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                 (forall x. Seq.mem x st ==> is_valid_header1 x g) /\
                                                 (G.is_vertex_set st) /\
                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                                })
                               (succ:hp_addr{is_valid_header1 succ g /\
                                                (color_of_object1 succ g == white \/
                                                 color_of_object1 succ g == gray \/
                                                 color_of_object1 succ g == black
                                                )})
                   : Lemma
                     (requires (color_of_object1 succ g == white))
                     (ensures (~(isGrayObject1 succ g) /\
                               ~(isBlackObject1 succ g) /\
                               ~(Seq.mem succ st))) = ()

#restart-solver 

let slice_property_lemma (g:heap{well_formed_heap2 g}) 
                         (st: seq Usize.t)
                         (st_top: Usize.t)
                 : Lemma
                   (requires Usize.v st_top <= Seq.length st /\
                             Usize.v st_top > 0 /\
                             (forall x. Seq.mem x (Seq.slice st 0 (Usize.v st_top)) ==>
                                        Usize.v x >= 0 /\ Usize.v x < heap_size))
                   (ensures (forall x. Seq.mem x (Seq.slice st 0 (Usize.v st_top - 1)) ==>
                                         Usize.v x >= 0 /\ Usize.v x < heap_size)) =
 Seq.lemma_slice_snoc st 0 (Usize.v st_top);
 ()

let slice_coloring_lemma (g:heap{well_formed_heap2 g}) 
                         (g':heap{well_formed_heap2 g'}) 
                         (v_id: hp_addr{is_valid_header1 v_id g /\
                                      is_valid_header1 v_id g'})
                         (s: seq Usize.t)
                         (s_top:Usize.t{Usize.v s_top <= Seq.length s}) 
         : Lemma
              (requires (G.is_vertex_set (Seq.slice s 0 (Usize.v s_top)) /\
                        ~(Seq.mem v_id (Seq.slice s 0 (Usize.v s_top))) /\
                         color_of_object1 v_id g' == black /\
                         heap_remains_same_except_index_v_id v_id g g' /\
                         (objects2 0UL g ==
                             objects2 0UL g') /\
                         (get_allocated_block_addresses g == 
                              get_allocated_block_addresses g') /\
                         
                         color_of_object1 v_id g == gray /\
                         (forall y. Seq.mem y (Seq.slice s 0 (Usize.v s_top)) \/
                          (y == v_id) <==> Seq.mem y (objects2 0UL g) /\ isGrayObject1 y g)))
              (ensures ((forall y. Seq.mem y (Seq.slice s 0 (Usize.v s_top)) <==>
                             Seq.mem y (objects2 0UL g') /\ isGrayObject1 y g'))) = ()

#restart-solver 

#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver

let h_index_field_index_mword_multiple_lemma2 (g:heap{well_formed_heap2 g})
                                             (h_index: hp_addr{is_valid_header1 h_index g})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()

let fieldaddress_within_limits_lemma1 (g:heap{well_formed_heap2 g})
                                     (x:hp_addr{is_valid_header1 x g})
                                     (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))})
                          : Lemma
                            (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                            (ensures (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 h_index_field_index_mword_multiple_lemma2 g x (getWosize (read_word g x)) i

#restart-solver 

let fieldaddress_within_limits_lemma_x_i_all1(g:heap{well_formed_heap2 g})
                                             (x:hp_addr{is_valid_header1 x g})
                           : Lemma
                             (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                             (ensures (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma1 g x))

#restart-solver 

let fieldaddress_within_limits_lemma_x_all1 (g:heap{well_formed_heap2 g})
                                    : Lemma
                                      (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                                      (ensures (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
 Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma_x_i_all1 g))

#restart-solver

#restart-solver

#restart-solver


let seq_length_minus_one_is_less_than_seq_length (s:seq Usize.t)
                                 : Lemma
                                   (ensures ((Seq.length s - 1) < Seq.length s)) = ()


#restart-solver

let is_vertex_set_slice (g:heap{well_formed_heap2 g}) 
                        (st: seq Usize.t{G.is_vertex_set st /\  (~(G.is_emptySet st)) /\
                                         (forall x. Seq.mem x st ==> Seq.mem (hd_address x) (get_allocated_block_addresses g)) 
                                         }) 
                         
            : Lemma
              (ensures (G.is_vertex_set (Seq.slice st 0 (Seq.length st - 1)) /\
                       (forall x. Seq.mem x (Seq.slice st 0 (Seq.length st - 1)) ==> Seq.mem (hd_address x) (get_allocated_block_addresses g)))) = 
 G.is_vertex_set_lemma3 st;
 slice_mem_lemma st (Seq.slice st 0 (Seq.length st - 1));
 assert (G.is_vertex_set (Seq.slice st 0 (Seq.length st - 1)));
 ()

#restart-solver 

#restart-solver

let test_helper (y:hp_addr{(Usize.v y + Usize.v mword < heap_size)}) 
    : Lemma 
      (ensures (hd_address (f_address y) == y)) = 
let f_y = f_address y in
let y' = hd_address f_y in
assert (y' == y);
()

let test_helper1 (s1:seq Usize.t)
                 (s2:seq Usize.t)
                 (y:Usize.t)
         : Lemma
           (requires (forall x. Seq.mem x s1 ==> Seq.mem x s2 \/ x == y) /\ Seq.mem y s2)
           (ensures (forall x. Seq.mem x s1 ==> Seq.mem x s2)) = ()
  
#restart-solver 

let test_helper3 (s1:seq Usize.t{(forall x. Seq.mem x s1 ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                 (forall x. Seq.mem x s1 ==> Usize.v x % Usize.v mword == 0)})
                 (s2:seq Usize.t)
                 (y:hp_addr{(Usize.v y + Usize.v mword < heap_size)}) 
         : Lemma
           (requires (forall x. Seq.mem x s1 ==> Seq.mem (hd_address x) s2 \/ x == (f_address y)) /\ Seq.mem (hd_address (f_address y)) s2)
           (ensures (forall x. Seq.mem x s1 ==> Seq.mem (hd_address x) s2)) =
()

#restart-solver

let test_helper5 (y:hp_addr{(Usize.v y + Usize.v mword < heap_size)}) 
       : Lemma 
         (ensures (forall x. hd_address x == y ==> x == f_address y)) = ()

#restart-solver

#restart-solver

let test29 (g:heap{well_formed_heap2 g})
           (y:hp_addr{Seq.mem y (get_allocated_block_addresses g)})
           (vl: seq Usize.t{vl_props_func g vl}) 
       : Lemma 
         (requires  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                    ~(Seq.mem (f_address y) vl))
         (ensures True) = 
 let allocs = get_allocated_block_addresses g in
 fieldaddress_within_limits_lemma_x_all g;
 let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in 
 assert (forall x. Seq.mem x allocs <==> Seq.mem (f_address x) ff_allocs);
 assert (forall x. Seq.mem x ff_allocs <==> Seq.mem (hd_address x) allocs);
 assert (forall x. Seq.mem (hd_address x) allocs ==> Seq.mem x ff_allocs);
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) (objects2 0UL g));
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) allocs);
 assert (forall x. Seq.mem x vl ==> Seq.mem (f_address (hd_address x)) ff_allocs);
 assert (forall x. Seq.mem x vl ==> Seq.mem x ff_allocs);
 let grph = create_graph_from_heap g in
 assert (Seq.mem y allocs);
 assert (Seq.mem (f_address y) ff_allocs);
 assert (Seq.mem (f_address y) grph.vertices);
 assert (G.subset_vertices vl (grph.vertices));
 let f_y = f_address y in
 let vl' = G.insert_to_vertex_set grph f_y vl in
 let g' = colorHeader1 y g black in
 assert (forall x. Seq.mem x vl ==> Seq.mem x vl');
 assert (Seq.mem f_y vl');
 assert (isBlackObject1 y g');
 colorHeader1_subset_lemma y g;

 let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
 let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in

 assert (forall x. Seq.mem x blacks ==>  Seq.mem x blacks');
             
 assert (forall x. Seq.mem x blacks <==> Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g);
 assert (forall x. Seq.mem x blacks' <==> Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g');
                                                         
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g ==> Seq.mem x blacks'); 
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g ==> Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g'); 

 G.insert_to_vertex_set_lemma grph f_y vl; 
 assert (~(exists x. (Seq.mem x vl') /\ ~(Seq.mem x vl) /\ x <> f_y));
 colorHeader1_mem_lemma y g;
 
 assert (~(exists x. (Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g') /\
                ~(Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g) /\
                                    (x <> y)));  
 objects2_equal_lemma 0UL g g';
 assert (G.is_vertex_set vl');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl);
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g);
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) (objects2 0UL g') /\ isBlackObject1 (hd_address x) g');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g ==> Seq.mem x vl); 
 assert (Seq.mem f_y vl' /\ isBlackObject1 y g');
 assert (~(exists x. (Seq.mem x vl') /\ ~(Seq.mem x vl) /\ x <> f_y)); 
 assert (~(exists x. (Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g') /\
                ~(Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g) /\
                                    (x <> y))); 
 assert (forall x. Seq.mem x vl' <==> Seq.mem x vl \/ x == f_y);
 assert (forall x. Seq.mem x vl' ==> Seq.mem x vl \/ x == f_y);
 assert (forall x. Seq.mem x vl' ==> (Seq.mem (hd_address x) (objects2 0UL g') /\ isBlackObject1 (hd_address x) g') \/ x == f_y);
 assert (Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g');
 test_helper y;
 assert (hd_address (f_address y) == y);
 assert (forall x. Seq.mem x vl' ==> Seq.mem (hd_address x) blacks' \/ x == f_y);
 assert (Seq.mem y blacks');
 assert (Seq.mem (hd_address (f_address y)) blacks');
 assert (f_y == f_address y);
 assert (Seq.mem (hd_address f_y) blacks');
 test_helper3 vl' blacks' y;
 assert (forall x. Seq.mem x vl' ==> Seq.mem (hd_address x) blacks');
 assert (forall x. Seq.mem x vl \/ x == f_y ==> Seq.mem x vl');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g ==> Seq.mem x vl);
 assert (forall x. Seq.mem (hd_address x) blacks ==> Seq.mem x vl);
 assert (forall x. Seq.mem x blacks' ==>  Seq.mem x blacks \/ x == y);
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) blacks);
 assert (forall x. Seq.mem x vl ==> Seq.mem (hd_address x) blacks');
 assert (forall x. Seq.mem (hd_address x) blacks \/ x == f_y ==> Seq.mem x vl');
 assert (forall x. Seq.mem x blacks \/ x == y ==> Seq.mem x blacks');
 assert (Seq.mem (hd_address f_y) blacks');
 assert (forall x. Seq.mem x blacks \/ x == y <==> Seq.mem x blacks');
 assert (forall x. Seq.mem (hd_address x) blacks \/ (hd_address x) == y <==> Seq.mem (hd_address x) blacks');
 test_helper5 y;
 assert (forall x. hd_address x == y ==> (x == f_address y));
 assert (forall x. Seq.mem (hd_address x) blacks \/ x == (f_address y) <==> Seq.mem (hd_address x) blacks');
 assert (forall x. Seq.mem (hd_address x) blacks' ==> Seq.mem x vl');
 assert (forall x. Seq.mem (hd_address x) blacks' <==> Seq.mem x vl');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isBlackObject1 (hd_address x) g' <==> Seq.mem x vl');
 ()

#restart-solver

let visited_list_lemma (g:heap{well_formed_heap2 g}) 
                       (vl: seq Usize.t{vl_props_func g vl}) 
                       (x: Usize.t{Usize.v x >= 0 /\ Usize.v x < heap_size /\
                                   (Usize.v x % Usize.v mword == 0) /\
                                 is_valid_header1 x g /\
                                 isGrayObject1 x g /\
                                 ~(Seq.mem (f_address x) vl)})
                       
             : Lemma
               (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                          (Seq.mem (f_address x) (create_graph_from_heap g).vertices) /\
                          (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
               
               (ensures (let grph = create_graph_from_heap g in
                         let f_x = f_address x in
                         let vl' = G.insert_to_vertex_set grph f_x vl in
                         let g' = colorHeader1 x g black in
                         let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
                         (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> Seq.mem y vl') /\
                         (forall y. Seq.mem (hd_address y) blacks' <==> Seq.mem y vl')
                         
                        )) = 
let allocs = get_allocated_block_addresses g in
assert (G.is_vertex_set allocs); // This assert is required
assert (all_field_address_are_word_aligned allocs g);
fieldaddress_within_limits_lemma_x_all g;
let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in 
assert (forall y. Seq.mem y allocs <==> Seq.mem (f_address y) ff_allocs);
assert (forall y. Seq.mem y ff_allocs <==> Seq.mem (hd_address y) allocs);
assert (forall y. Seq.mem (hd_address y) allocs ==> Seq.mem y ff_allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) (objects2 0UL g));
assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem (f_address (hd_address y)) ff_allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem y ff_allocs);
let grph = create_graph_from_heap g in
assert (Seq.mem x allocs);
assert (Seq.mem (f_address x) ff_allocs);
assert (Seq.mem (f_address x) grph.vertices);
assert (G.subset_vertices vl (grph.vertices));
let f_x = f_address x in
let vl' = G.insert_to_vertex_set grph f_x vl in
let g' = colorHeader1 x g black in
assert (forall x. Seq.mem x vl ==> Seq.mem x vl');
assert (Seq.mem f_x vl');
assert (isBlackObject1 x g');
colorHeader1_subset_lemma x g;
let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
assert (forall y. Seq.mem y blacks ==>  Seq.mem y blacks');
             
 assert (forall y. Seq.mem y blacks <==> Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g);
 assert (forall y. Seq.mem y blacks' <==> Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g');
                                                         
 assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g ==> Seq.mem y blacks'); 
 assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g ==> Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g'); 

 G.insert_to_vertex_set_lemma grph f_x vl; 
 assert (~(exists y. (Seq.mem y vl') /\ ~(Seq.mem y vl) /\ y <> f_x));
 colorHeader1_mem_lemma x g;
 assert (~(exists y. (Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g') /\
                ~(Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g) /\
                                    (x <> y))); 
 
 objects2_equal_lemma 0UL g g';
 assert (G.is_vertex_set vl');
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isBlackObject1 (hd_address y) g <==> Seq.mem y vl);
 assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) (objects2 0UL g) /\ isBlackObject1 (hd_address y) g);
 assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g');
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isBlackObject1 (hd_address y) g ==> Seq.mem y vl); 
 assert (Seq.mem f_x vl' /\ isBlackObject1 x g');
 test_helper x;
 assert (hd_address (f_address x) == x);
 assert (forall y. Seq.mem y vl' ==> Seq.mem (hd_address y) blacks' \/ y == f_x);
 assert (Seq.mem x blacks');
 assert (Seq.mem (hd_address (f_address x)) blacks');
 assert (f_x == f_address x);
 assert (Seq.mem (hd_address f_x) blacks');
 test_helper3 vl' blacks' x;
 assert (forall y. Seq.mem y vl' ==> Seq.mem (hd_address y) blacks');
 assert (forall y. Seq.mem y vl \/ y == f_x ==> Seq.mem y vl');
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL g) /\ isBlackObject1 (hd_address y) g ==> Seq.mem y vl);
 assert (forall y. Seq.mem (hd_address y) blacks ==> Seq.mem y vl);
 assert (forall y. Seq.mem y blacks' ==>  Seq.mem y blacks \/ y == x);
 assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) blacks);
 assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) blacks');
 assert (forall y. Seq.mem (hd_address y) blacks \/ y == f_x ==> Seq.mem y vl');
 assert (forall y. Seq.mem x blacks \/ y == x ==> Seq.mem y blacks');
 assert (Seq.mem (hd_address f_x) blacks');
 assert (forall y. Seq.mem y blacks \/ y == x <==> Seq.mem y blacks');
 assert (forall y. Seq.mem (hd_address y) blacks \/ (hd_address y) == x <==> Seq.mem (hd_address y) blacks');
 test_helper5 x;
 assert (forall y. (hd_address y) == x ==> (y == (f_address x)));
 assert (forall y. Seq.mem (hd_address y) blacks \/ y == (f_address x) <==> Seq.mem (hd_address y) blacks');
 assert (forall y. Seq.mem (hd_address y) blacks' ==> Seq.mem y vl');
 assert (forall y. Seq.mem (hd_address y) blacks' <==> Seq.mem y vl');
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> Seq.mem y vl');
 ()                                                                      

#restart-solver 

let is_vertex_set_vl_after_insert (g:heap{well_formed_heap2 g})
                                  (vl: seq Usize.t{vl_props_func g vl})                  
                                  (x: Usize.t{Usize.v x >= 0 /\ Usize.v x < heap_size /\
                                             (Usize.v x % Usize.v mword == 0) /\
                                              is_valid_header1 x g /\
                                              isGrayObject1 x g /\
                                              ~(Seq.mem (f_address x) vl)})                                    
                                                                      
                                 
                : Lemma
                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                            (Seq.mem (f_address x) (create_graph_from_heap g).vertices) /\
                            (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
                  (ensures (let grph = create_graph_from_heap g in
                            let f_x = f_address x in
                            let vl' = G.insert_to_vertex_set grph f_x vl in
                            (G.is_vertex_set vl') /\
                            (Seq.mem f_x vl') /\
                            (G.subset_vertices vl' (grph.vertices)))) = 
let allocs = get_allocated_block_addresses g in
assert (G.is_vertex_set allocs); // This assert is required
assert (all_field_address_are_word_aligned allocs g);
fieldaddress_within_limits_lemma_x_all g;
let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in 
assert (forall y. Seq.mem y allocs <==> Seq.mem (f_address y) ff_allocs);
assert (forall y. Seq.mem y ff_allocs <==> Seq.mem (hd_address y) allocs);
assert (forall y. Seq.mem (hd_address y) allocs ==> Seq.mem y ff_allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) (objects2 0UL g));
assert (forall y. Seq.mem y vl ==> Seq.mem (hd_address y) allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem (f_address (hd_address y)) ff_allocs);
assert (forall y. Seq.mem y vl ==> Seq.mem y ff_allocs);
let grph = create_graph_from_heap g in
assert (Seq.mem x allocs);
assert (Seq.mem (f_address x) ff_allocs);
assert (Seq.mem (f_address x) grph.vertices);
assert (G.subset_vertices vl (grph.vertices));
let f_x = f_address x in
let vl' = G.insert_to_vertex_set grph f_x vl in
assert (G.is_vertex_set vl');
assert (G.subset_vertices vl' (grph.vertices));
assert (Seq.mem f_x vl');
()

#restart-solver

#restart-solver

let mutual_exclusion_lemma (st: seq Usize.t{G.is_vertex_set st /\  (~(G.is_emptySet st))}) 
                           (vl: seq Usize.t{G.is_vertex_set vl})
                           
                : Lemma
                  (requires  (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                  (ensures ((forall x. Seq.mem x (Seq.slice st 0 (Seq.length st - 1)) ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x (Seq.slice st 0 (Seq.length st - 1))))))) = 
 let s = Seq.slice st 0 (Seq.length st - 1) in
 assert ((forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
         (forall x. Seq.mem x vl ==> ~(Seq.mem x st))));
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Seq.mem x st);
 assert (forall x. Seq.mem x s ==> ~(Seq.mem x vl));
 assert (forall x. Seq.mem x vl ==> ~(Seq.mem x s));
 ()

let mutual_exclusion_lemma1 (g:heap{well_formed_heap2 g
                                   })
                            
                            (x:Usize.t{Seq.mem x (get_allocated_block_addresses g)})
                           
                            (s: seq Usize.t) 
                            (vl: seq Usize.t)
                : Lemma
                  (requires  
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                             (Seq.mem (f_address x) ((create_graph_from_heap g)).vertices) /\
                             (G.is_vertex_set s /\
                                           G.subset_vertices s (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)) /\
                                            ~(Seq.mem (f_address x) s)) /\
                             (G.is_vertex_set vl /\
                                            G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)) /\
                                             ~(Seq.mem (f_address x) vl)) /\
                             (forall y. Seq.mem y s ==> ~(Seq.mem y vl) /\
                             (forall y. Seq.mem y vl ==> ~(Seq.mem y s))) /\
                             (forall i y.  Seq.mem y (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g y))) ==> 
                                                    (Usize.v y  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
                  
                  (ensures (let grph = create_graph_from_heap g in
                            let f_x = f_address x in
                            let vl' = G.insert_to_vertex_set grph f_x vl in
                            (forall y. Seq.mem y vl' ==> ~(Seq.mem y s)) /\
                            (forall y. Seq.mem y s ==> ~(Seq.mem y vl')))) = 
let grph = create_graph_from_heap g in
let f_x = f_address x in
let vl' = G.insert_to_vertex_set grph f_x vl in
G.insert_to_vertex_set_mem_negation_lemma grph f_x vl s;
assert (forall y. Seq.mem y vl' ==> ~(Seq.mem y s));
assert (forall y. Seq.mem y s ==> ~(Seq.mem y vl'));
()

#restart-solver 

#restart-solver

#restart-solver

#push-options "--split_queries always"

#restart-solver

let is_vertex_set_vl_after_insert1 (g:heap{well_formed_heap2 g})
                                   (vl: seq Usize.t {(G.is_vertex_set vl) /\
                                          (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                          (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                          (forall x. Seq.mem x vl ==> is_valid_header1 (hd_address x) g) /\
                                          (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl)
                                                    })                  
                                    (x: Usize.t{Usize.v x >= Usize.v mword /\ Usize.v x < heap_size /\
                                             (Usize.v x % Usize.v mword == 0) /\
                                              is_valid_header1 (hd_address x) g /\
                                              isGrayObject1 (hd_address x) g /\
                                             
                                             ~(Seq.mem x vl)})                                    
                  : Lemma
                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                            (Seq.mem x (create_graph_from_heap g).vertices) /\
                            (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
                  (ensures (let grph = create_graph_from_heap g in
                            let vl' = G.insert_to_vertex_set grph x vl in
                            (G.is_vertex_set vl') /\
                            (Seq.mem x vl') /\
                            (G.subset_vertices vl' (grph.vertices)))) =                                                 
 let grph = create_graph_from_heap g in
 //let vl' = G.insert_to_vertex_set grph x vl in
 (*assert ((G.is_vertex_set vl') /\
         (Seq.mem x vl') /\
         (G.subset_vertices vl' (grph.vertices)));*)
 ()

#restart-solver 

#restart-solver

#push-options "--split_queries always"

#restart-solver

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

//#push-options "--split_queries always"

let mutual_exclusion_lemma3 (g:heap{well_formed_heap2 g
                                   })
                            
                            (x:Usize.t{ Usize.v x >= Usize.v mword /\ Usize.v x < heap_size /\
                                        (Usize.v x % Usize.v mword == 0) /\
                                        Seq.mem (hd_address x) (get_allocated_block_addresses g)})
                           
                            (s: seq Usize.t) 
                            (vl: seq Usize.t)
                : Lemma
                  (requires  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                             (Seq.mem x ((create_graph_from_heap g)).vertices) /\
                             
                             (G.is_vertex_set s /\
                                           G.subset_vertices s (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)) /\
                                            ~(Seq.mem x s)) /\
                             (G.is_vertex_set vl /\
                                            G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)) /\
                                             ~(Seq.mem x vl)) /\
                             (forall y. Seq.mem y s ==> ~(Seq.mem y vl) /\
                             (forall y. Seq.mem y vl ==> ~(Seq.mem y s))) /\
                             (forall i y.  Seq.mem y (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g y))) ==> 
                                                    (Usize.v y  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
                  
                  (ensures (let grph = create_graph_from_heap g in
                            let vl' = G.insert_to_vertex_set grph x vl in
                            (forall y. Seq.mem y vl' ==> ~(Seq.mem y s)) /\
                            (forall y. Seq.mem y s ==> ~(Seq.mem y vl')))) = 
let grph = create_graph_from_heap g in
let vl' = G.insert_to_vertex_set grph x vl in
G.insert_to_vertex_set_mem_negation_lemma grph x vl s;
assert (forall y. Seq.mem y vl' ==> ~(Seq.mem y s));
assert (forall y. Seq.mem y s ==> ~(Seq.mem y vl'));
()

#reset-options " --z3rlimit 1000"

#restart-solver

#push-options "--split_queries always"

let graph_succs_length_lemma (g:heap{well_formed_heap2 g
                                    })
                            
                             (x:Usize.t{ Usize.v x >= Usize.v mword /\ Usize.v x < heap_size /\
                                        (Usize.v x % Usize.v mword == 0) /\
                                        Seq.mem (hd_address x) (get_allocated_block_addresses g)}) 
                     : Lemma
                       (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                 (Seq.mem x ((create_graph_from_heap g)).vertices))
                       (ensures (let grph = create_graph_from_heap g in
                                 let sl = G.successors grph x in
                                 (Seq.length sl >= 0)))= ()



#restart-solver

#push-options " --z3rlimit 1000"

#restart-solver

let fieldPush_spec1_black_nodes_lemma3  (g:heap{well_formed_heap2 g})
                                        (st: seq Usize.t{stack_props_func g st})
                                        (h_index:hp_addr{ Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                               (Usize.v h_index % Usize.v mword == 0) /\
                                                                               is_valid_header1 h_index g})
                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
                                        (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (ensures (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>
                                         Seq.mem y (objects2 0UL  (snd (fieldPush_spec1 g st h_index wz i))) /\
                                                                         (isBlackObject1 y  (snd (fieldPush_spec1 g st h_index wz i))))) = 
fieldPush_spec1_black_nodes_lemma1 g st h_index wz i;
()

#restart-solver

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#push-options "--split_queries always"

#restart-solver

let darken_wrapper_lemma (g:heap{well_formed_heap2 g})
                         (st: seq Usize.t{stack_props_func g st})
                         (h_index:hp_addr{is_valid_header1 h_index g})
                         (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))}) 
            : Lemma 
              (requires Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
                        
                        (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                        (let g1 = snd (darken_wrapper g st h_index wz) in
                           well_formed_heap2 g1 /\
                           
                           (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)))
               (ensures (let g1 = snd (darken_wrapper g st h_index wz) in
                           (create_graph_from_heap g == create_graph_from_heap g1) /\
                           (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  Seq.mem y (objects2 0UL g1) /\ (isBlackObject1 y g1)))) =
 if (Usize.v (tag_of_object1 h_index g) = closure_tag) then
   (
     assert (Usize.v wz >= 2);

     let v_id = f_address h_index in
     
     let start_env = start_env_clos_info g v_id in

     assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address v_id) g)) /\
             Usize.v start_env >= 1);
     let start_env_plus_one = Usize.add start_env 1UL in
     let st1, g1 = fieldPush_spec1 g st h_index wz start_env_plus_one in
     
     let grph1 = create_graph_from_heap g in
     let grph3 = create_graph_from_heap g1 in
     fieldPush_spec1_graph_lemma g st h_index wz start_env_plus_one;
     
     assert (grph1 == grph3);
     fieldPush_spec1_black_nodes_lemma3 g st h_index wz start_env_plus_one;
     assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  Seq.mem y (objects2 0UL g1) /\ (isBlackObject1 y g1));
     ()
   )
   else
   (
     let st1, g1 = fieldPush_spec1 g st h_index wz 1UL in
     assert (G.is_vertex_set st1);
     assert (Seq.length g == Seq.length g1);
     assert (well_formed_heap2 g1);
     assert (forall x. Seq.mem x st1 ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
     assert (forall x. Seq.mem x st1 ==> is_valid_header (hd_address x) g1);
     assert (forall x. Seq.mem x st1 ==> Usize.v x % Usize.v mword == 0);
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isGrayObject1 (hd_address x) g1 <==>
                                                Seq.mem x st1);
     assert (forall x. Seq.mem x st ==> Seq.mem x st1);
  
     assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
     assert (objects2 0UL g == objects2 0UL g1);
     assert (objects2 0UL g == objects2 0UL g1);
     assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
     (*field_limits_allocated_blocks_lemma g1;
     field_contents_within_limits_allocated_blocks_lemma g1;
     fieldaddress_within_limits_lemma_x_all1 g1;
     fieldPush_spec1_well_formed_allocated_blocks_lemma g st h_index wz 1UL;*)
    
     assert (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1);
     let grph1 = create_graph_from_heap g in
     let grph3 = create_graph_from_heap g1 in
     fieldPush_spec1_graph_lemma g st h_index wz 1UL;
     
     assert (grph1 == grph3);
     fieldPush_spec1_black_nodes_lemma3 g st h_index wz 1UL;
     assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  Seq.mem y (objects2 0UL g1) /\ (isBlackObject1 y g1));
     ()
   )          
 
#restart-solver       

#restart-solver

#restart-solver

#restart-solver

let dfs_mark_equivalence_body_lemma1 (g:heap{well_formed_heap2 g}) 
                                     (st: seq Usize.t {stack_props_func g st})
                                     (vl: seq Usize.t {vl_props_func g vl}) 
                                    (c:color{c == 3UL})
                          : Lemma
                   (requires (~(G.is_emptySet st)) /\
                             
                             
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                             (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses (snd ( mark5_body g st))) (snd ( mark5_body g st))) /\
                             (G.subset_vertices st (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             (G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             
                             (Seq.length st > 0) /\
                            
                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                                           
                             
                   (ensures (*graph equivalence*)(create_graph_from_heap g == create_graph_from_heap (snd ( mark5_body g st))) /\
                            (*visited set equivalence*) (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (mark5_body g st))) /\ 
                                                           isBlackObject1 (hd_address y) (snd (mark5_body g st)) <==> 
                                                               Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)))) = 

assert (~(G.is_emptySet st));
let v_id = Seq.index st (Seq.length st - 1) in
 seq_index_lemma st;
 assert (v_id == Seq.index st (Seq.length st - 1));
 let s = Seq.slice st 0 (Seq.length st - 1) in
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
 seq_slice_lemma st;
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g);
 G.is_vertex_set_lemma3 st;
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 assert (Seq.mem h_v_id (get_allocated_block_addresses g));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 let g' = colorHeader5 h_v_id g black in
 colorHeader5_lemma h_v_id g black;
 assert (color_of_object1 h_v_id g' == black);
 colorHeader1_alloc_colors_lemma h_v_id g black;
 assert (well_formed_heap2 g');
 objects2_equal_lemma 0UL g g';
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 stack_slice_only_has_gray_color_lemma g st v_id c;
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g'  <==>  Seq.mem x s);
 let wz = wosize_of_object1 h_v_id g' in
 assert (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);
 let grph1 = create_graph_from_heap g in
 field_limits_allocated_blocks_lemma g';
 field_contents_within_limits_allocated_blocks_lemma g';
 fieldaddress_within_limits_lemma_x_all1 g';
 
 
 assert (all_field_address_are_word_aligned (get_allocated_block_addresses g') g');
 
 let grph2 = create_graph_from_heap g' in
 create_graph_from_heap_lemma g h_v_id c;
 assert (grph1 == grph2);
 (*compare with dfs_body---------------------------------------------------------------------------------------------------------------*)
   let x = G.get_last_elem grph1 st in
   assert (x == Seq.index st (Seq.length st - 1));
   assert (x == v_id);

   let xs = G.get_first grph1 st in
   assert (Seq.equal xs (Seq.slice st 0 (Seq.length st - 1)));
   seq_slice_transitive_lemma st s xs;
   assert (s == xs);
   let vl' = G.insert_to_vertex_set grph1 x vl in
   assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size /\
          (Usize.v h_v_id % Usize.v mword == 0));
   assert (is_valid_header h_v_id g);
   assert (isGrayObject1  h_v_id g);
   assert (Seq.mem h_v_id (get_allocated_block_addresses g));
   assert (h_v_id == hd_address v_id);
   f_address_hp_address_lemma h_v_id;
   assert (f_address h_v_id == v_id);
   assert (~(Seq.mem v_id vl));
   assert (~(Seq.mem (f_address h_v_id) vl));
   visited_list_lemma g vl h_v_id;
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> Seq.mem y vl');
   assert (vl' == (snd (D.dfs_body (create_graph_from_heap g) st vl)));
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> 
                   Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)));
   
  let tg = tag_of_object1 h_v_id g' in
  if (Usize.v tg < no_scan_tag) then
  (
    let st1, g1 = darken_wrapper g' s h_v_id wz in
    assert (well_formed_heap2 g1);
    field_limits_allocated_blocks_lemma g1;
    field_contents_within_limits_allocated_blocks_lemma g1;
    fieldaddress_within_limits_lemma_x_all1 g1;
    
    darken_wrapper_lemma g' s h_v_id wz;
    assert ((create_graph_from_heap g' == create_graph_from_heap g1) /\
           (forall y. Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g' <==>  Seq.mem y (objects2 0UL g1) /\ (isBlackObject1 y g1)));
    
    assert (forall y. Seq.mem (hd_address y) (objects2 0UL g1) /\ isBlackObject1 (hd_address y) g1 <==> 
                   Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)));

    assert (g1 == snd (mark5_body g st));
    assert (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (mark5_body g st))) /\ isBlackObject1 (hd_address y) (snd (mark5_body g st)) <==> 
                   Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)));
    ()
  )
  else
  (
    ()
  )

#restart-solver 

let dfs_mark_equivalence_body_lemma1_v1 (g:heap{well_formed_heap2 g}) 
                                        (st: seq Usize.t {stack_props_func g st})
                                        (vl: seq Usize.t {vl_props_func g vl}) 
                                        (c:color{c == 3UL})
                          : Lemma
                   (requires (~(G.is_emptySet st)) /\
                             
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                             (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses (snd ( mark5_body1 g st))) (snd ( mark5_body1 g st))) /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses (snd ( mark5_body g st))) (snd ( mark5_body g st))) /\
                             (G.subset_vertices st (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             (G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             
                             (Seq.length st > 0) /\
                            
                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                                           
                             
                   (ensures (*graph equivalence*)(create_graph_from_heap g == create_graph_from_heap (snd ( mark5_body1 g st))) /\
                            (*visited set equivalence*) (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (mark5_body1 g st))) /\ 
                                                           isBlackObject1 (hd_address y) (snd (mark5_body1 g st)) <==> 
                                                               Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)))) = 
 dfs_mark_equivalence_body_lemma1 g st vl c;
 mark_body_mark_body1_lemma g st;
 ()

#restart-solver

#restart-solver

let darken_wrapper_helper_lemma (g:heap{well_formed_heap2 g})
                                (st: seq Usize.t{stack_props_func g st})
                                (h_index:hp_addr{is_valid_header1 h_index g})
                                (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                                (vl: seq Usize.t{vl_props_func g vl /\  (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                                       (forall x. Seq.mem x vl ==> ~(Seq.mem x st))})
                                                                                        
                                (c:color{Usize.v c == 2})
         : Lemma
         (requires Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
                   (h_index_within_limits g h_index) /\
                   (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                   (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                   (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                   (0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))))
         (ensures (fst (darken_wrapper g st h_index wz) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index)) 
                                                                                  vl
                                                                                  st 
                                                                                  0)) =
 if (Usize.v (tag_of_object1 h_index g) = closure_tag) then
   (
     assert (Usize.v wz >= 2);

     let v_id = f_address h_index in
     
     let start_env = start_env_clos_info g v_id in

     assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address v_id) g)) /\
             Usize.v start_env >= 1);
     let start_env_plus_one = Usize.add start_env 1UL in
     let st1, g1 = fieldPush_spec1 g st h_index wz start_env_plus_one in
     assert ((all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
             (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
             (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index))) /\
             0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) /\
             Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
             Usize.v (tag_of_object1 h_index g) == closure_tag);
     graph_successors_from_0_and_heap_field_pointers_from_1_are_equal1 g h_index;
     assert (fieldPush_spec_successor_push_itr_equivalence_lemma2_pre_props g st h_index wz start_env_plus_one 0UL vl);
     fieldPush_spec_successor_push_itr_equivalence_lemma2 g st h_index wz start_env_plus_one 0UL vl c;
     assert ((fst (fieldPush_spec1 g st h_index wz start_env_plus_one)) ==  G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index))
                                                                                  (vl)
                                                                                  (st)
                                                                                   0);
     assert (fst (darken_wrapper g st h_index wz) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index)) 
                                                                                  vl
                                                                                  st 
                                                                                  0);
     ()
     
   )
   else
   (
     let st1, g1 = fieldPush_spec1 g st h_index wz 1UL in
     graph_successors_from_0_and_heap_field_pointers_from_1_are_equal g h_index;
     assert (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
     
     fieldPush_spec_successor_push_itr_equivalence_lemma2 g st h_index wz 1UL 0UL vl c;
     assert ((fst (fieldPush_spec1 g st h_index wz 1UL)) ==  G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index))
                                                                                  (vl)
                                                                                  (st)
                                                                                   0);
     assert (fst (darken_wrapper g st h_index wz) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_index)) 
                                                                                  vl
                                                                                  st 
                                                                                  0);
     ()
   )

#restart-solver

#restart-solver

#restart-solver

let dfs_mark_equivalence_body_lemma (g:heap{well_formed_heap2 g}) 
                                    (st: seq Usize.t {stack_props_func g st})
                                    (vl: seq Usize.t {vl_props_func g vl}) 
                                    (c:color{c == 3UL})
                                    (c1:color{Usize.v c1 == 2})
                          : Lemma
                   (requires (~(G.is_emptySet st)) /\
                             
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                             (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses (snd ( mark5_body g st))) (snd ( mark5_body g st))) /\
                             (G.subset_vertices st (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             (G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                             
                             (Seq.length st > 0) /\
                            
                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                                           
                             
                   (ensures (*stack equivalence*) fst ( mark5_body g st) == fst (D.dfs_body (create_graph_from_heap g) st vl)) = 
assert (~(G.is_emptySet st));
 let v_id = Seq.index st (Seq.length st - 1) in
 seq_index_lemma st;
 assert (v_id == Seq.index st (Seq.length st - 1));
 let s = Seq.slice st 0 (Seq.length st - 1) in
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
 seq_slice_lemma st;
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g);
 G.is_vertex_set_lemma3 st;
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 assert (Seq.mem h_v_id (get_allocated_block_addresses g));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 let g' = colorHeader5 h_v_id g black in
 colorHeader5_lemma h_v_id g black;
 assert (color_of_object1 h_v_id g' == black);
 colorHeader1_alloc_colors_lemma h_v_id g black;
 assert (well_formed_heap2 g');
 objects2_equal_lemma 0UL g g';
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 stack_slice_only_has_gray_color_lemma g st v_id c;
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g'  <==>  Seq.mem x s);
 let wz = wosize_of_object1 h_v_id g' in
 assert (all_field_address_are_word_aligned (get_allocated_block_addresses g) g);
 let grph1 = create_graph_from_heap g in
 field_limits_allocated_blocks_lemma g';
 field_contents_within_limits_allocated_blocks_lemma g';
 fieldaddress_within_limits_lemma_x_all1 g';
 
 
 assert (all_field_address_are_word_aligned (get_allocated_block_addresses g') g');
 
 let grph2 = create_graph_from_heap g' in
 create_graph_from_heap_lemma g h_v_id c;
 assert (grph1 == grph2);
 (*compare with dfs_body---------------------------------------------------------------------------------------------------------------*)
   let x = G.get_last_elem grph1 st in
   assert (x == Seq.index st (Seq.length st - 1));
   assert (x == v_id);

   let xs = G.get_first grph1 st in
   assert (Seq.equal xs (Seq.slice st 0 (Seq.length st - 1)));
   seq_slice_transitive_lemma st s xs;
   assert (s == xs);
   let vl' = G.insert_to_vertex_set grph1 x vl in
   assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size /\
          (Usize.v h_v_id % Usize.v mword == 0));
   assert (is_valid_header h_v_id g);
   assert (isGrayObject1  h_v_id g);
   assert (Seq.mem h_v_id (get_allocated_block_addresses g));
   assert (h_v_id == hd_address v_id);
   f_address_hp_address_lemma h_v_id;
   assert (f_address h_v_id == v_id);
   assert (~(Seq.mem v_id vl));
   assert (~(Seq.mem (f_address h_v_id) vl));
   visited_list_lemma g vl h_v_id;
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> Seq.mem y vl');
   assert (vl' == (snd (D.dfs_body (create_graph_from_heap g) st vl)));
   assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> 
                   Seq.mem y (snd (D.dfs_body (create_graph_from_heap g) st vl)));

  let _ = G.get_last_mem_lemma grph1 st in
  assert (~(Seq.mem x xs));
  let sl = G.successors grph1 x in
  let _ = G.insert_to_vertex_set_mem_negation_lemma grph1 x vl xs in
  is_vertex_set_slice g st;
  is_vertex_set_vl_after_insert1 g vl x;
  mutual_exclusion_lemma st vl;
  mutual_exclusion_lemma3 g x s vl;
  let tg = tag_of_object1 h_v_id g' in
  if (Usize.v tg < no_scan_tag) then
  (
    let st1, g1 = darken_wrapper g' s h_v_id wz in
    assert (well_formed_heap2 g1);
    field_limits_allocated_blocks_lemma g1;
    field_contents_within_limits_allocated_blocks_lemma g1;
    fieldaddress_within_limits_lemma_x_all1 g1;

    let r' = G.successor_push_itr1 sl vl' xs 0 in
    G.successor_push_itr1_subset_lemma grph1 sl vl' xs 0;
    graph_successors_length_lemma g' h_v_id;
    assert (h_v_id == hd_address v_id);
    test_helper5 h_v_id;
    assert (v_id == f_address h_v_id);
    assert (f_address h_v_id == x);
    assert (Seq.mem x grph2.vertices);
    assert (Seq.length sl <= Usize.v (getWosize (read_word g' h_v_id)));
    graph_succs_length_lemma g' x;
    assert (0 <= Seq.length sl); 
    assert ((all_field_address_are_word_aligned (get_allocated_block_addresses g') g') /\
            (Seq.mem (f_address h_v_id) (create_graph_from_heap g').vertices) /\
            (Seq.length (G.successors (create_graph_from_heap g') (f_address h_v_id)) <= Usize.v (getWosize (read_word g' h_v_id))) /\
            0 <= Seq.length (G.successors (create_graph_from_heap g') (f_address h_v_id)) /\
            Usize.v (tag_of_object1 h_v_id g') < no_scan_tag
           );
   
    let st1, g1 = darken_wrapper g' s h_v_id wz in
    assert  (Usize.v (tag_of_object1 h_v_id g') < no_scan_tag /\
                   (h_index_within_limits g' h_v_id) /\
                   (all_field_address_are_word_aligned (get_allocated_block_addresses g') g') /\
                   (Seq.mem (f_address h_v_id) (create_graph_from_heap g').vertices) /\
                   (Seq.length (G.successors (create_graph_from_heap g') (f_address h_v_id)) <= Usize.v wz) /\
                   (0 <= Seq.length (G.successors (create_graph_from_heap g') (f_address h_v_id))));
    
    visited_list_lemma g vl h_v_id;
    assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> Seq.mem y vl');
    assert ((forall x. Seq.mem x vl' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
           (forall x. Seq.mem x vl' ==> Usize.v x % Usize.v mword == 0));
    assert (G.is_vertex_set vl');
    assert (forall x. Seq.mem x vl' ==> is_valid_header (hd_address x) g');
    assert (vl_props_func g' vl');
    assert  ((forall x. Seq.mem x s ==> ~(Seq.mem x vl')) /\
            (forall x. Seq.mem x vl' ==> ~(Seq.mem x s)));
    assert (stack_props_func g' s);
    
    darken_wrapper_helper_lemma g' s h_v_id wz vl' c1;
    assert (fst (darken_wrapper g' s h_v_id wz) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) (f_address h_v_id)) 
                                                                                  vl'
                                                                                  s 
                                                                                  0);
    assert (fst (mark5_body1 g st) == fst (darken_wrapper g' s h_v_id wz));
    assert (st1 == r'); 
    assert (fst (D.dfs_body grph1 st vl) == r');
    assert (fst ( mark5_body1 g st) == st1);
    assert (fst ( mark5_body1 g st) == fst (D.dfs_body (create_graph_from_heap g) st vl));
    
    ()
    
  )
  else
  (
    graph_successors_heap_create_successor_list_equivalence_lemma g h_v_id;
    assert (Usize.v (tag_of_object1 h_v_id g) == Usize.v (tag_of_object1 h_v_id g'));
    assert (Usize.v (tag_of_object1 h_v_id g) >= no_scan_tag);
    assert (G.successors (create_graph_from_heap g) (f_address h_v_id) == Seq.empty #UInt64.t);
    let r' = G.successor_push_itr1 sl vl' xs 0 in
    test_helper5 h_v_id;
    assert (v_id == f_address h_v_id);
    assert (f_address h_v_id == x);
    assert (sl == Seq.empty #UInt64.t);
    length_empty_lemma sl;
    assert (Seq.length sl == 0);
    G.successor_push_itr1_lemma1 sl vl' xs 0; 
    assert (G.successor_push_itr1 sl vl' xs 0 == xs);
    assert (r' == xs);
    assert (fst (D.dfs_body grph1 st vl) == r');
    assert (fst ( mark5_body g st) == xs);
    assert (fst ( mark5_body g st) == fst (D.dfs_body (create_graph_from_heap g) st vl));
    ()
  )

#reset-options "--z3rlimit 500"

#restart-solver

let cardinal_diff (g:heap{well_formed_heap2 g}) 
         : Tot (diff:int{(diff =  G.cardinal1(get_allocated_block_addresses g) - G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g))) /\
                        diff >= 0})=
 let card_allocs = G.cardinal1(get_allocated_block_addresses g) in
 let card_blacks = G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g)) in
 let diff = card_allocs - card_blacks in
 assert (diff >= 0);
 diff

let cardinal_diff_lemma (g:heap{well_formed_heap2 g})
                        (g':heap{well_formed_heap2 g'})
             : Lemma 
               (requires (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                         (Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g')) > 
                            Seq.length (get_black_block_addresses g (get_allocated_block_addresses g))))
               (ensures (cardinal_diff g > cardinal_diff g')) = ()


let neg_empty_lemma (s:seq Usize.t{G.is_vertex_set s})
                    
            : Lemma
              (requires (~(G.is_emptySet s)))
              (ensures Seq.length s > 0) = ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries always"

#restart-solver

let rec dfs_mark_equivalence_lemma  (g:heap{well_formed_heap2 g}) 
                                    (st: seq Usize.t {stack_props_func g st})
                                    (vl: seq Usize.t {vl_props_func g vl}) 

                                    (c:color{c == 3UL})
                                    (c1:color{c1 == 2UL})
                                
                 : Lemma
                   (requires  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                              (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                              
                              (G.subset_vertices st (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\
                              (G.subset_vertices vl (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g))) /\ 
                              (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                              (forall x. Seq.mem x vl ==> ~(Seq.mem x st))
                              
                   )
                          
                   (ensures (forall x. Seq.mem (hd_address x) (objects2 0UL (mark5 g st)) /\ isBlackObject1 (hd_address x) (mark5 g st) <==>
                                 Seq.mem x (D.dfs (create_graph_from_heap g)
                                            st
                                            vl))) 
                   (decreases %[cardinal_diff g;
                                Seq.length st])= 

if (G.is_emptySet st) then
   (
      ()
   )
 else
   (
     neg_empty_lemma st;
     assert (Seq.length st > 0);
     let st', g' = mark5_body g st in
     let v_id = Seq.index st (Seq.length st - 1) in
     seq_index_lemma st;
     assert (v_id == Seq.index st (Seq.length st - 1));
     let s = Seq.slice st 0 (Seq.length st - 1) in
     seq_index_lemma1 st;
     assert (Seq.mem v_id st);
     assert (Usize.v v_id >= Usize.v mword);
     stack_slice_only_has_gray_color_lemma g st v_id 3UL;
     mark5_body_black_nodes_lemma g st;
     let g1 = mark5 g' st' in
     mark_mark_body_lemma g st;
     assert (mark5 g st == mark5 g' st');
     let grph1 = create_graph_from_heap g in
     let _ = G.negation_nonEmpty_implies_empty st in
     assert (G.nonEmpty_set st);
     let st1,vl1 = D.dfs_body grph1 st vl in
     
     field_limits_allocated_blocks_lemma g';
     field_contents_within_limits_allocated_blocks_lemma g';
     fieldaddress_within_limits_lemma_x_all1 g';
     assert (all_field_address_are_word_aligned (get_allocated_block_addresses g') g');
     
     dfs_mark_equivalence_body_lemma1 g st vl c;
     dfs_mark_equivalence_body_lemma g st vl c c1;
     assert (st' == st1);

     let grph2 = create_graph_from_heap g' in
     assert (grph1 == grph2);
     assert (forall y. Seq.mem (hd_address y) (objects2 0UL g') /\ isBlackObject1 (hd_address y) g' <==> 
                                                     Seq.mem y vl1);
                                                              
     let vl2 = D.dfs grph1 st1 vl1 in
     D.dfs_lemma grph1 st vl ;
     assert (D.dfs grph1 st vl == D.dfs grph1 st1 vl1);
     assert (G.subset_vertices st' (first_field_addresses_of_allocated_blocks g' (get_allocated_block_addresses g')));
     assert (G.subset_vertices vl1 (first_field_addresses_of_allocated_blocks g' (get_allocated_block_addresses g')));
     assert ((forall x. Seq.mem x st' ==> ~(Seq.mem x vl1)) /\
             (forall x. Seq.mem x vl1 ==> ~(Seq.mem x st')));
     assert  ((forall x. Seq.mem x vl1 ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
              (forall x. Seq.mem x vl1 ==> Usize.v x % Usize.v mword == 0));
     assert  (forall x. Seq.mem x vl1 ==> is_valid_header (hd_address x) g');
     
     cardinal_diff_lemma g g';
     assert (cardinal_diff g > cardinal_diff g'); 

     dfs_mark_equivalence_lemma g' st' vl1 c c1;
     ()
   )

#restart-solver 

let noGreyObjects1 (g:heap{well_formed_heap2 g}) = 
   (forall (x:hp_addr{UInt.fits (Usize.v x - Usize.v mword) Usize.n }). Seq.mem (hd_address x) (objects2 0UL g) ==> ~(color_of_object1 (hd_address x) g == gray)) 

let noGreyObjects (g:heap) = (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray))

let heap_heap_addr_pair = heap & hp_addr

#restart-solver

#reset-options "--z3rlimit 500"

#push-options "--split_queries always"


#restart-solver

let colorHeader3  (v_id:hp_addr)  
                  (g:heap(*{well_formed_heap2 g /\ is_valid_header1 v_id g}*){(Seq.length (objects2 0UL g) > 0) /\ (Seq.mem v_id (objects2 0UL g))}) 
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
 //assert (well_formed_heap2 g);
 let h_index = v_id in
 assert (Seq.mem h_index (objects2 0UL g));
 
// assert (Seq.length (objects2 0UL g) > 0);

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 

 assert (heap_remains_same_except_index_v_id h_index g g');

 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.mem v_id (objects2 0UL g'));
 //assert (is_fields_contents_within_limit2 v_id wz g);
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

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver



let write_word_replacement_lemma1 (byte_array: heap)
                                 (byte_index: hp_addr)
                                 (value: UInt64.t)
            : Lemma
              (ensures (forall (i:hp_addr). read_word (write_word byte_array byte_index value) byte_index == value)) = ()

#reset-options "--z3rlimit 500"

let write_word_before_start_lemma1 (byte_array: heap)
                                   (byte_index: hp_addr)
                                   (value: UInt64.t)
                      : Lemma
                        (ensures (forall (i:hp_addr). Usize.v i >= 0 /\  Usize.v i < Usize.v byte_index /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) i == read_word byte_array i)) = 
 replace_range_before_start_all_lemma byte_array byte_index (FStar.Endianness.le_of_uint64 value)

let write_word_lemma1 (byte_array: heap)
                     (byte_index: hp_addr)
                     (value: UInt64.t)
                : Lemma 
                  ((forall (i:hp_addr). read_word (write_word byte_array byte_index value) i == (
                                                           if Usize.v i = Usize.v byte_index then
                                                                  value 
                                                             else 
                                                                read_word byte_array i))) = 
write_word_replacement_lemma1 byte_array byte_index value;  
write_word_before_start_lemma byte_array byte_index value;
write_word_after_start_end_lemma byte_array byte_index value;
()

let write_word_lemma3 (byte_array: heap)
                     (byte_index: hp_addr)
                     (value: UInt64.t)
                : Lemma 
                  (forall (i:hp_addr). Usize.v i <> Usize.v byte_index ==> read_word (write_word byte_array byte_index value) i == read_word byte_array i) =
 write_word_lemma1 byte_array byte_index value;
 ()
                                                                

let write_word_lemma5 (byte_array: heap)
                     (byte_index: hp_addr)
                     (value: UInt64.t)
                : Lemma 
                  (forall (i:hp_addr). Usize.v i == Usize.v byte_index ==> read_word (write_word byte_array byte_index value) i == value) =
 write_word_lemma1 byte_array byte_index value;
 ()

let write_word_after_start_end_lemma1 (byte_array: heap)
                                     (byte_index: hp_addr)
                                     (value: UInt64.t)
                      : Lemma
                        (ensures (forall (i:hp_addr). (Usize.v i >= ((Usize.v byte_index) + Usize.v mword)) /\ (Usize.v i < length byte_array) /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) i == read_word byte_array i)) =
 replace_range_after_start_end_all_lemma byte_array byte_index (FStar.Endianness.le_of_uint64 value)

let fields_not_mem_objs_lemma (g:heap(*{well_formed_heap2 g}*))
                              (g':heap)
                              (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                              (y:hp_addr{Usize.v y >= Usize.v h_index + Usize.v mword /\
                                       Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword)})
                  : Lemma
                    (ensures ~(Seq.mem y (objects2 0UL g))) = 
assert (~(Seq.mem y (objects2 0UL g)));
()

#restart-solver

(*val objects2_equal_lemma5 :  (g:heap(*{well_formed_heap2 g}*){Seq.length (objects2 0UL g) > 0})-> 
                             (g':heap)->
                             (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})->
                      Lemma
                       (requires (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word g' p) ==  getWosize (read_word g p)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index))*)

#restart-solver


  
let objects2_equal_lemma1_app (g:heap(*{well_formed_heap2 g}*){Seq.length (objects2 0UL g) > 0}) 
                              (g':heap)
                              
                   :   Lemma
                       (requires (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word g' p) ==  getWosize (read_word g p)))
                       (ensures (objects2 0UL g == objects2 0UL g'))= 
 objects2_equal_lemma5 g g' 0UL;
 assert (objects2 0UL g == objects2 0UL g');
 ()

#restart-solver 

#restart-solver 
            
let objects_color_equivalence_lemma (g:heap(*{well_formed_heap2 g}*))
                                    (x:hp_addr{(*is_valid_header x g /\ *)color_of_object1 x g == blue})
                                    (p:hp_addr{(*is_valid_header p g /\ *) color_of_object1 p g <> blue})
                     : Lemma
                       (ensures p <> x) = () 
                       
#restart-solver 

let objects_color_equivalence_lemma_all (g:heap(*{well_formed_heap2 g}*))
                                        (x:hp_addr{(*is_valid_header x g /\*) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                                       
                      : Lemma
                       (ensures (forall p. (*is_valid_header p g /\ *) color_of_object1 p g <> blue ==> p <> x)) = 
Classical.forall_intro (objects_color_equivalence_lemma g x) 

#restart-solver

let objects_fields_lemma (g:heap(*{well_formed_heap2 g}*))
                         (x:hp_addr{(*is_valid_header x g /\ *)Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                         (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                         (p:hp_addr{(*is_valid_header p g /\*)Seq.mem p (objects2 0UL g) /\  p <> x})
                         (j:hp_addr{Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword)})
                        
                  : Lemma
                    (ensures (Usize.v j <> Usize.v i)) = 
if (Usize.v p > Usize.v x) then
(
  assert (Usize.v p > Usize.v x);
  assert (Usize.v j > Usize.v x);
  assert (Usize.v j > Usize.v i);
  assert (Usize.v j <> Usize.v i);
  ()
)
else
(
  assert (Usize.v p < Usize.v x);
  assert (Usize.v j <> Usize.v x);
  assert (Usize.v j <> Usize.v i);
  ()
)

let objects_fields_lemma_all (g:heap(*{well_formed_heap2 g}*))
                             (x:hp_addr{(*is_valid_header x g /\ *) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                             (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                             (p:hp_addr{(*is_valid_header p g /\*) Seq.mem p (objects2 0UL g) /\  p <> x})
                   : Lemma
                     (ensures (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i)) = 
 Classical.forall_intro (objects_fields_lemma g x i p)

#restart-solver

let objects_fields_lemma_all1 (g:heap(*{well_formed_heap2 g}*))
                              (x:hp_addr{(*is_valid_header x g /\*)Seq.mem x (objects2 0UL g) /\  color_of_object1 x g == blue})
                              (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                            
                   : Lemma
                     (ensures (forall p. (*is_valid_header p g*) Seq.mem p (objects2 0UL g)  /\ p <> x ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i))) = 
Classical.forall_intro (objects_fields_lemma_all g x i)  


let objects_fields_lemma_all1_app (g:heap(*{well_formed_heap2 g}*))
                                  (x:hp_addr{(*is_valid_header x g /\*) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                                  (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                     : Lemma
                     (ensures (forall p. (*is_valid_header p g /\*) Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> 
                                    (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i))) = 
objects_color_equivalence_lemma_all g x;
objects_fields_lemma_all1 g x i ;
()   

let objects_fields_lemma_all1_app1 (g:heap(*{well_formed_heap2 g}*))
                                  (x:hp_addr{(*is_valid_header x g /\*) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                                  (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                     : Lemma
                     (ensures (forall p. (*is_valid_header p g /\*) Seq.mem p (objects2 0UL g) /\  p <> x ==> 
                                    (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i))) = 
objects_fields_lemma_all1 g x i ;
()   

#restart-solver 

#restart-solver 

#restart-solver 

#restart-solver 

let objects_fields_lemma1 (g:heap(*{well_formed_heap2 g}*))
                          (x:hp_addr{(*is_valid_header x g /\*) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                          (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                          (j:Usize.t{Usize.v j > 1 /\
                                     Usize.v j <= (Usize.v (getWosize (read_word g x)))}) 
                   : Lemma
                    (ensures (Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v i)) = ()
                    
let objects_fields_lemma1_all1 (g:heap(*{well_formed_heap2 g}*))
                               (x:hp_addr{(*is_valid_header x g /\*) Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                               (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                    : Lemma
                      (ensures (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g x))}).Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v i)) = 
 Classical.forall_intro (objects_fields_lemma1 g x i);
 ()

#restart-solver

let h_index_field_index_mword_multiple_lemma7 (g:heap(*{well_formed_heap2 g}*))
                                              (h_index: hp_addr{Seq.mem h_index (objects2 0UL g)})
                                              (wz: wosize{((wz == getWosize (read_word g h_index)) /\ 
                                                             is_fields_within_limit1 h_index wz) (*/\
                                                             is_fields_contents_within_limit2 h_index wz g*)})
                                              (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (is_hp_addr (Usize.add h_index (Usize.mul  i mword)))) = 
 
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) < heap_size);
assert (is_hp_addr (Usize.add h_index (Usize.mul  i mword)));
()

#restart-solver 

#restart-solver

let h_index_field_index_all_mword_multiple_lemma7(g:heap(*{well_formed_heap2 g}*))
                                                 (h_index: hp_addr{Seq.mem h_index (objects2 0UL g)})
                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ 
                                                             is_fields_within_limit1 h_index wz) (*/\
                                                             is_fields_contents_within_limit2 h_index wz g*)}) 
                                : Lemma
                                 (ensures (forall (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g h_index))}).
                                          is_hp_addr (Usize.add h_index (Usize.mul i mword)))) = 
Classical.forall_intro (Classical.move_requires (h_index_field_index_mword_multiple_lemma7 g h_index wz));
()

#restart-solver 

#restart-solver 

#restart-solver 

let first_field_of_blue (g:heap(*{well_formed_heap2 g}*))
                        (x:hp_addr) =
   Usize.v x >= Usize.v mword /\ (*is_valid_header (hd_address x) g*) Seq.mem (hd_address x) (objects2 0UL g)  /\ color_of_object1 (hd_address x) g == blue

let first_field_of_any (g:heap(*{well_formed_heap2 g}*))
                       (v:hp_addr) =
                
Usize.v v >= Usize.v mword /\ (*is_valid_header (hd_address v) g*)Seq.mem (hd_address v) (objects2 0UL g)

let header_value_does_not_change_with_a_field_write (g:heap(*{well_formed_heap2 g}*))
                                                    (x:hp_addr{first_field_of_blue g x})
                                                    (v:hp_addr{first_field_of_any g v}) =
    (forall p. Seq.mem p (objects2 0UL g) ==> read_word (write_word g x v) p ==  read_word g p)   
                                           
let objs_remain_the_same_with_a_write_to_first_field (g:heap(*{well_formed_heap2 g}*))
                                                     (x:hp_addr{first_field_of_blue g x})
                                                     (v:hp_addr{first_field_of_any g v}) =
   objects2 0UL g == objects2 0UL (write_word g x v) 

let write_to_the_firstfield_of_blue_object_preserves_the_field_reads_of_all_non_blue_objects (g:heap(*{well_formed_heap2 g}*))
                                                                                             (x:hp_addr{first_field_of_blue g x})
                                                                                             (v:hp_addr{first_field_of_any g v}) =
   (forall p. Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g x v) j == read_word g j))

let write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_objects_other_than_this_object (g:heap(*{well_formed_heap2 g}*))
                                                                                                              (x:hp_addr{first_field_of_blue g x})
                                                                                                              (v:hp_addr{first_field_of_any g v}) =
   (forall p. (*is_valid_header p g*) Seq.mem p (objects2 0UL g) /\ p <> (hd_address x) ==> 
                               (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g x v) j == read_word g j))

let write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_other_fields_of_that_object (g:heap(*{well_formed_heap2 g}*))
                                                                                                            (x:hp_addr{first_field_of_blue g x})
                                                                                                            (v:hp_addr{first_field_of_any g v}) =
  (forall (j:hp_addr). Usize.v j > Usize.v (hd_address x) + Usize.v mword /\
                                     Usize.v j <= Usize.v (hd_address x) + (Usize.v (getWosize (read_word g (hd_address x))) * Usize.v mword) ==>
                                      read_word (write_word g x v) j == read_word g j)

let write_to_first_field_of_a_blue_object_lies_within_heap_limits_of_fields (g:heap(*{well_formed_heap2 g}*))
                                                                            (x:hp_addr{first_field_of_blue g x})
                                                                            (v:hp_addr{first_field_of_any g v}) =

  Usize.v (read_word (write_word g x v) x) >= Usize.v mword /\ Usize.v (read_word (write_word g x v) x) < heap_size


#restart-solver

let field_addresses_are_heap_addresses (g:heap(*{well_formed_heap2 g}*))
                                       (x:hp_addr{Usize.v x >= Usize.v mword /\ (*is_valid_header (hd_address x) g*) Seq.mem (hd_address x) (objects2 0UL g) /\
                                                  color_of_object1 (hd_address x) g == blue})
                                           
                                           
                                       (v:hp_addr{Usize.v v >= Usize.v mword /\ (*is_valid_header (hd_address v) g*) Seq.mem (hd_address v) (objects2 0UL g)}) =
 (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g (hd_address x)))}). 
                                          is_hp_addr (Usize.add (hd_address x) (Usize.mul j mword))) 

let write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_other_fields_of_that_object1 (g:heap(*{well_formed_heap2 g}*))
                                                                                                            (x:hp_addr{first_field_of_blue g x})
                                                                                                            (v:hp_addr{first_field_of_any g v /\
                                                                                                                       field_addresses_are_heap_addresses g x v}) =
 forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g (hd_address x)))}).
                                                     Usize.v (read_word g (Usize.add (hd_address x) (Usize.mul j mword))) == 
                                                     Usize.v (read_word (write_word g x v) (Usize.add (hd_address x) (Usize.mul j mword)))

#restart-solver 

#restart-solver

#restart-solver 

#reset-options "--z3rlimit 500"

#restart-solver

let write_word_to_blue_object_field_lemma_props (g:heap(*{well_formed_heap2 g}*))
                                                (x:hp_addr{first_field_of_blue g x})
                                                (v:hp_addr{first_field_of_any g v}) =
 
 (forall (p:hp_addr). read_word (write_word g x v) p == ( if x = p then
                                                               v 
                                                             else 
                                                               read_word g p))
                                                          

let write_word_to_blue_object_field_lemma_props1 (g:heap(*{well_formed_heap2 g}*)) =
 ( forall p. Seq.mem p (objects2 0UL g) ==> Usize.v (getWosize (read_word g p)) > 0)

let write_word_to_blue_object_field_lemma_props2 (g:heap(*{well_formed_heap2 g}*))
                                                (x:hp_addr{first_field_of_blue g x}) =
  
   (Usize.v (getWosize (read_word g (hd_address x))) > 0) /\
   (Usize.v (getWosize (read_word g (hd_address x))) >= 1)

let write_word_to_blue_object_field_lemma_props3 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 (v:hp_addr{first_field_of_any g v})=
  (forall p. Seq.mem p (objects2 0UL g) ==> read_word (write_word g x v) p ==  read_word g p) /\
  (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word (write_word g x v) p) ==  getWosize (read_word g p))


let write_word_to_blue_object_field_lemma_props4 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 (v:hp_addr{first_field_of_any g v}) =

  (forall (p:hp_addr). p <> x ==> read_word (write_word g x v) p == read_word g p)
  

let write_word_to_blue_object_field_lemma_props5 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 (v:hp_addr{first_field_of_any g v}) =
 (forall p. Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v x)) /\
 (forall p.  Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g x v) j == read_word g j)) /\
 (forall p. Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g x v) j == read_word g j))

let write_word_to_blue_object_field_lemma_props6 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 (v:hp_addr{first_field_of_any g v}) =
                                                 
 (forall p.  Seq.mem p (objects2 0UL g) /\  p <> (hd_address x) ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v x)) /\
 (forall p.  Seq.mem p (objects2 0UL g) /\ p <> (hd_address x) ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g x v) j == read_word g j)) /\
 (forall (j:hp_addr). Usize.v j > Usize.v (hd_address x) + Usize.v mword /\
                                     Usize.v j <= Usize.v (hd_address x) + (Usize.v (getWosize (read_word g (hd_address x))) * Usize.v mword) ==>
                                      read_word (write_word g x v) j == read_word g j)

let write_word_to_blue_object_field_lemma_props7 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 (v:hp_addr{first_field_of_any g v}) =
  (Usize.v v >= Usize.v mword /\ Usize.v v < heap_size) /\
  
  (Usize.v v % Usize.v mword == 0) /\

  (read_word (write_word g x v) x == v) /\

  (Usize.v (read_word (write_word g x v) x) >= Usize.v mword /\ Usize.v (read_word (write_word g x v) x) < heap_size)


let write_word_to_blue_object_field_lemma_props8 (g:heap(*{well_formed_heap2 g}*))
                                                 (x:hp_addr{first_field_of_blue g x})
                                                 =
  (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g (hd_address x)))}).Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v x)

let objects_fields_lemma1_all1_props (g:heap(*{well_formed_heap2 g}*))
                                     (x:hp_addr{ Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})
                                     (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword})  =
                  
 (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g x))}).Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v i)

#restart-solver

let wosize_of_header_of_x (g:heap(*{well_formed_heap2 g}*))
                          (x:hp_addr{first_field_of_blue g x})
            : Tot (wz:wosize{wz == getWosize (read_word g (hd_address x)) /\ (is_fields_within_limit1 (hd_address x) wz)})=
 let wz = getWosize (read_word g (hd_address x)) in
 assert (is_fields_within_limit1 (hd_address x) wz);
 wz


let heap_remains_same_except_index_v_id2  (v_id1:hp_addr)
                                          (v_id2:hp_addr)
                                          (g:heap)
                                          (g':heap{Seq.length g == Seq.length g'}) =
  forall (x:Usize.t {Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). x <> v_id1  /\ x <> v_id2 ==>
           read_word g x == read_word g' x 

let heap_remains_same_except_index_lemma (v_id1:hp_addr)
                                         (v_id2:hp_addr)
                                         (g:heap)
                                         (g':heap{Seq.length g == Seq.length g'})
                                         (g'':heap{Seq.length g == Seq.length g''})
                        : Lemma
                          (requires (heap_remains_same_except_index_v_id v_id1 g g' /\
                                     heap_remains_same_except_index_v_id v_id2 g' g''))
                          (ensures heap_remains_same_except_index_v_id2 v_id1 v_id2 g g'') = ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries always"

#restart-solver


let write_word_to_blue_object_field_lemma (g:heap(*{well_formed_heap2 g}*){write_word_to_blue_object_field_lemma_props1 g /\ Seq.length (objects2 0UL g) > 0})
                                          (x:hp_addr{first_field_of_blue g x})
                                          (v:hp_addr{first_field_of_any g v})
                          :Lemma 
                          (ensures  (objs_remain_the_same_with_a_write_to_first_field g x v) /\ 
                          
                                    (header_value_does_not_change_with_a_field_write g x v) /\

                                    (*prove that write_to_the_firstfield_of_blue_object still preserves the property that
                                      all of the field pointers are pointing to the object set*)
                                    
                                    (write_to_the_firstfield_of_blue_object_preserves_the_field_reads_of_all_non_blue_objects g x v) /\
                                    
                                    (write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_objects_other_than_this_object g x v) /\
                                    
                                    (write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_other_fields_of_that_object g x v) /\
                                    
                                    (write_to_first_field_of_a_blue_object_lies_within_heap_limits_of_fields g x v) /\
                                    
                                    (field_addresses_are_heap_addresses g x v) /\
                                    (write_to_the_first_field_of_a_blue_object_preserves_the_field_reads_of_all_other_fields_of_that_object1 g x v) /\
                                    Seq.length (objects2 0UL (write_word g x v)) > 0
                                    ) = 

  let g' = write_word g x v in
  write_word_lemma1 g x v;
  assert (write_word_to_blue_object_field_lemma_props g x v);
  
  assert (Seq.mem (hd_address x) (objects2 0UL g));
  
  assert (write_word_to_blue_object_field_lemma_props1 g);
  
  assert (write_word_to_blue_object_field_lemma_props2 g x);
  fields_not_mem_objs_lemma g g' (hd_address x) x;
  assert (~(Seq.mem x (objects2 0UL g)));
  
  assert (write_word_to_blue_object_field_lemma_props3 g x v);
  
  objects2_equal_lemma1_app g g';
  assert (objects2 0UL g == objects2 0UL g');
  assert (Seq.length (objects2 0UL g) > 0);
  assert (Seq.length (objects2 0UL g') > 0);
  assert (write_word_to_blue_object_field_lemma_props4 g x v);
  objects_fields_lemma_all1_app g (hd_address x) x;
  assert (write_word_to_blue_object_field_lemma_props5 g x v);
  
 
  objects_fields_lemma_all1_app1 g (hd_address x) x;
  assert (write_word_to_blue_object_field_lemma_props6 g x v);
  
  assert (write_word_to_blue_object_field_lemma_props7 g x v);
  objects_fields_lemma1_all1 g (hd_address x) x;
  assert (objects_fields_lemma1_all1_props g (hd_address x) x);
  
  h_index_field_index_all_mword_multiple_lemma7 g (hd_address x) (wosize_of_header_of_x g x);
  ()



// one more heap untouched by sweep. Any object white in g less than f_index does not point to f_index. 
//g' --> heap after mark, g --> current heap (passing to sweep_body)
//Assume that well-formedness hold for the portion of g less than f_index. f-index = 0, intial; trivially holds
//PT. well_formedness hold for portion of g <= f_index.
//All the cases, B--> white ---> 

#restart-solver 

let sweep_body_with_free_list (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ write_word_to_blue_object_field_lemma_props1 g})
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ 
                                                              Seq.mem (hd_address f_index) (objects2 0UL g)})
                              (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                                         color_of_object1 (hd_address fp) g == blue /\
                                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
           
            : Tot (p:heap_heap_addr_pair{Seq.length (objects2 0UL (fst p)) > 0 /\ noGreyObjects (fst p) /\
                                         (objects2 0UL g == objects2 0UL (fst p)) /\
                                         Usize.v (snd p) >= Usize.v mword /\ 
                                         Seq.mem (hd_address (snd p)) (objects2 0UL (fst p)) /\ 
                                         color_of_object1 (hd_address (snd p)) (fst p) == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL (fst p)) /\ Seq.mem y (objects2 0UL (fst p)) ==>
                                             Usize.v (getWosize (read_word (fst p) x)) + Usize.v (getWosize (read_word (fst p) y)) < heap_size) /\
                                         (forall x. Seq.mem x (objects2 0UL g) /\ x <> (hd_address f_index) ==> Seq.mem x (objects2 0UL (fst p)))}) =
                            
 let h_index = hd_address f_index in
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white || c = blue) then 
 (
   let g' = colorHeader3 h_index g blue in
   assert (objects2 0UL g == objects2 0UL g');
   
   assert (Usize.v fp % Usize.v mword == 0);

   (*let hd_fp = hd_address fp in
   let fp_wz_sz = getWosize (read_word g' hd_fp) in
   let fp_wz_sz' = getWosize (read_word g hd_fp) in
   assert (fp_wz_sz == fp_wz_sz');
   let fp_color = getColor (read_word g' hd_fp) in
   assert (fp_color == blue);
   let fp_wz_sz_plus_one = Usize.add fp_wz_sz 1UL in
   let next_obj_offset = Usize.mul fp_wz_sz_plus_one mword in
   let next_obj = Usize.add fp next_obj_offset in*)
   
   let g1 = write_word g' fp f_index in
   //write_word_to_blue_object_field_lemma1 g' fp f_index;
   write_word_to_blue_object_field_lemma g' fp  f_index;
   //assert (well_formed_heap2 g1);
   assert (objects2 0UL g == objects2 0UL g');
   assert (Seq.length (objects2 0UL g') > 0);
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   assert (noGreyObjects g');
   assert (noGreyObjects g1);
   assert (Usize.v f_index >= Usize.v mword);
   assert (Seq.mem (hd_address f_index) (objects2 0UL g1));
   assert (color_of_object1 (hd_address f_index) g1 == blue);
   assert (forall x y. Seq.mem x (objects2 0UL g1) /\ Seq.mem y (objects2 0UL g1) ==>
                         Usize.v (getWosize (read_word g1 x)) + Usize.v (getWosize (read_word g1 y)) < heap_size);
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g1));
   (g1,f_index)

  
 )
 else
 (
   assert (c == black);
   let g' = colorHeader3 h_index g white in
   assert (objects2 0UL g == objects2 0UL g');
      
   
   assert (Usize.v fp >= Usize.v mword);
   //assert (is_valid_header (hd_address fp) g');
   assert (color_of_object1 (hd_address fp) g == blue);
   assert (color_of_object1 (hd_address fp) g' == blue);
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   assert (noGreyObjects g');
   (g',fp)
 )

#restart-solver

let colorHeader3_lemma  (v_id:hp_addr)  
                        (g:heap(*{well_formed_heap2 g /\ is_valid_header1 v_id g}*){(Seq.length (objects2 0UL g) > 0) /\ (Seq.mem v_id (objects2 0UL g))}) 
                        (c:color)
          : Lemma
            (requires well_formed_heap2 g /\ is_valid_header1 v_id g)
            (ensures colorHeader1 v_id g c == colorHeader3 v_id g c) =
()


let wosize_plus_one_times_mword_multiple_of_mword (wz:wosize)
                     :Lemma 
                      (ensures (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0)) = ()

let well_formedness_first_field_lemma (g:heap{Seq.length (objects2 0UL g) > 0
                                              })
                                      (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)})
                         : Lemma
                           (ensures (~(Seq.mem f_index (objects2 0UL g)))) =
 (*assert (well_formed_heap2 g);*)
 assert (forall x. Seq.mem x (objects2 0UL g) ==> Usize.v (getWosize (read_word g x)) > 0);
 let h_index = hd_address f_index in
 assert (Seq.mem h_index (objects2 0UL g));
 assert (forall x y. Seq.mem x (objects2 0UL g) /\ (Usize.v y >= Usize.v x + Usize.v mword) /\ 
                                                   (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1)) ==>
                                                   ~(Seq.mem y (objects2 0UL g)));
 assert (~(Seq.mem f_index (objects2 0UL g)));                                                
 ()


#reset-options "--z3rlimit 500"

#restart-solver

#push-options "--split_queries always"

#restart-solver

let write_word_length_lemma (byte_array: heap)
                            (byte_index: hp_addr)
                            (value: UInt64.t)
  : Lemma
    (ensures length (write_word byte_array byte_index value) == length byte_array) = ()
 
 
let write_word_heap_lemma (g:heap{ noGreyObjects g})
                          (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\  Seq.mem (hd_address f_index) (objects2 0UL g)})
                          (fp:hp_addr{Usize.v fp >= Usize.v mword /\  Seq.mem (hd_address fp) (objects2 0UL g) /\ color_of_object1 (hd_address fp) g == blue}) 
              : Lemma
                (ensures heap_remains_same_except_index_v_id fp g (write_word g fp f_index)) =
   let g1 = write_word g fp f_index in
   write_word_lemma g fp f_index;
   write_word_length_lemma g fp f_index;
   assert (length g == length g1);
   assert (heap_remains_same_except_index_v_id fp g g1);
   ()
                         
let wosize_plus_times_mword_multiple_of_mword1 (wz:wosize)
                     :Lemma 
                      (ensures (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0)) = ()

let objects2_mem_lemma1_app (h_index: hp_addr)
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

let rec objects_mem_h_index_lemma  (g:heap)
                                   (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                   (l: seq Usize.t {l == objects2 h_index g})
                                   (fp:hp_addr{Usize.v fp >= Usize.v mword /\ Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                               color_of_object1 (hd_address fp) g == blue /\
                                               (~(Seq.mem fp (objects2 0UL g)))
                                                }) 
                      : Lemma
                        (ensures ~(Seq.mem fp (objects2 h_index g)))
                        (decreases (Seq.length l))  =
 if Seq.length l = 0 then ()
else
(
  assert (Seq.length l > 0);
  assert (l == objects2 h_index g);
  let wz =  getWosize (read_word g h_index) in
  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
  if Usize.v h_index_new >= heap_size then
  (
    objects2_cons_lemma2 h_index g;
    assert ((Seq.length (objects2 h_index g) > 0 /\ 
                        Usize.v (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) >= heap_size ==> 
                          Seq.length (objects2 h_index g) == 1));
   
    assert (Seq.mem h_index (objects2 0UL g));
    assert (Seq.length (objects2 h_index g) == 1);
    assert (~(Seq.mem fp (objects2 0UL g)));
    ()
  )
  else
  (
    assert (Usize.v h_index_new < heap_size);
    wosize_plus_times_mword_multiple_of_mword1 wz;
    sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
    assert (Usize.v h_index_new % Usize.v mword == 0);
    assert (is_hp_addr h_index_new);
    objects2_cons_lemma1 h_index g h_index_new;
    assert (Seq.length (objects2 h_index g) > 0 /\  Usize.v h_index_new < heap_size ==> 
                      ((objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g)) /\
                      (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g))));
    let l1 = objects2 h_index_new g in
    assert (l == Seq.cons h_index l1);
    lemma_tl h_index l1;
    assert (l1 == Seq.tail l);
    objects2_mem_lemma1_app h_index g;
    
    assert (Seq.length l1 < Seq.length l);
    objects_mem_h_index_lemma g h_index_new l1 fp;
    assert (~(Seq.mem fp (objects2 h_index_new g)));
    
    assert (fp <> h_index);
    assert (~(Seq.mem fp l1));
    Seq.mem_cons h_index l1;
    assert (~(Seq.mem fp l));
    ()
  )
  
)


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let sweep_body_with_free_list_lemma5 (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ write_word_to_blue_object_field_lemma_props1 g})
                                     (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ 
                                                              Seq.mem (hd_address f_index) (objects2 0UL g)})
                                     (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                                         color_of_object1 (hd_address fp) g == blue /\
                                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
            
            
            :Lemma (ensures ((color_of_object1 (hd_address f_index) g == white \/  color_of_object1 (hd_address f_index) g == blue) <==>
                              color_of_object1 (hd_address f_index) (fst (sweep_body_with_free_list g f_index fp)) == blue) /\
                              
                              (color_of_object1 (hd_address f_index) g == black <==> 
                              color_of_object1 (hd_address f_index) (fst (sweep_body_with_free_list g f_index fp)) == white) /\
                              
                              (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ Usize.v x > Usize.v (hd_address f_index) ==> 
                                        getColor (read_word g x) == getColor (read_word (fst (sweep_body_with_free_list g f_index fp)) x)) /\
                               
                              (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v (hd_address f_index) ==> 
                                        getColor (read_word g x) == getColor (read_word (fst (sweep_body_with_free_list g f_index fp)) x)) /\
                              heap_remains_same_except_index_v_id2 (hd_address f_index) fp g (fst (sweep_body_with_free_list g f_index fp)) /\
                              (objects2 (hd_address f_index) g == objects2 (hd_address f_index) (fst (sweep_body_with_free_list g f_index fp))) /\
                              (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word (fst (sweep_body_with_free_list g f_index fp)) x))) =
 let h_index = hd_address f_index in

 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white || c = blue) then 
 (
   let g' = colorHeader3 h_index g blue in
   assert (objects2 0UL g == objects2 0UL g');
   
   assert (Usize.v fp % Usize.v mword == 0);

   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   
   let g1 = write_word g' fp f_index in
   write_word_heap_lemma g' f_index fp;
   assert (heap_remains_same_except_index_v_id fp g' (write_word g' fp f_index));
   write_word_to_blue_object_field_lemma g' fp  f_index;
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g1 x));
   assert (color_of_object1 h_index g1 == blue);
   assert ((color_of_object1 h_index g == white \/  color_of_object1 h_index g == blue) <==> color_of_object1 h_index g' == blue);
   assert (color_of_object1 h_index g' == blue <==> color_of_object1 h_index g1 == blue);
   assert ((color_of_object1 h_index g == white \/  color_of_object1 h_index g == blue) <==> color_of_object1 h_index g1 == blue);
   objects2_equal_lemma3 h_index g' g1;
   heap_remains_same_except_index_lemma h_index fp g g' g1;
   assert (heap_remains_same_except_index_v_id2 h_index fp g g1);
   assert (forall x. Seq.mem x (objects2 0UL g') /\ Usize.v x > Usize.v h_index ==> getColor (read_word g' x) == getColor (read_word g1 x));
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g1 x));
   assert (Usize.v h_index >= 0);
   objects2_equal_lemma3 h_index g g';
   assert (objects2 h_index g == objects2 h_index g');
   assert (objects2 h_index g' == objects2 h_index g1);
   objects_mem_h_index_lemma g h_index (objects2 h_index g) fp;
   well_formedness_first_field_lemma g f_index;
   well_formedness_first_field_lemma g fp;
   assert (forall x. Seq.mem x (objects2 h_index g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   assert (forall x. Seq.mem x (objects2 h_index g') /\ Usize.v x > Usize.v h_index ==> getColor (read_word g' x) == getColor (read_word g1 x));
   assert (forall x. Seq.mem x (objects2 h_index g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g1 x));
   assert (color_of_object1 (hd_address f_index) g == black <==> 
                              color_of_object1 (hd_address f_index) (fst (sweep_body_with_free_list g f_index fp)) == white);
   assert ((color_of_object1 (hd_address f_index) g == white \/  color_of_object1 (hd_address f_index) g == blue) <==>
                              color_of_object1 (hd_address f_index) (fst (sweep_body_with_free_list g f_index fp)) == blue);
   
   assert (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ Usize.v x > Usize.v (hd_address f_index) ==> 
                                        getColor (read_word g x) == getColor (read_word (fst (sweep_body_with_free_list g f_index fp)) x));
   
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v (hd_address f_index) ==> 
                                        getColor (read_word g x) == getColor (read_word (fst (sweep_body_with_free_list g f_index fp)) x));
   ()

  
 )
 else
 (
   assert (c == black);
   let g' = colorHeader3 h_index g white in
   assert (objects2 0UL g == objects2 0UL g');
   assert (objects2 0UL g == objects2 0UL g');
   assert (heap_remains_same_except_index_v_id h_index g g');
   
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   assert (color_of_object1 h_index g == black);
   assert (color_of_object1 h_index g' == white);
   assert (color_of_object1 h_index g == black <==> color_of_object1 h_index g' == white);
   assert (objects2 0UL g == objects2 0UL g');
   assert (Seq.mem h_index (objects2 0UL g));
   assert (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word g' x));
   objects2_equal_lemma3 h_index g g';
   assert (objects2 h_index g == objects2 h_index g');
   assert (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word (fst (sweep_body_with_free_list g f_index fp)) x));
   assert (heap_remains_same_except_index_v_id fp g' g');
   heap_remains_same_except_index_lemma h_index fp g g' g'; 
   assert (heap_remains_same_except_index_v_id2 h_index fp g g');
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   assert (objects2 h_index g == objects2 h_index g');
   assert (forall x. Seq.mem x (objects2 h_index g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   ()
 )

#restart-solver 

#restart-solver 

#restart-solver 

#push-options "--split_queries always"

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"


let objects2_property_lemma  (g:heap{(Seq.length (objects2 0UL g) > 0)})
                             (h_index:hp_addr{(Seq.length (objects2 h_index g) == 1)})
               : Lemma
                 (ensures ~(exists y. y <> h_index /\ Seq.mem y ((objects2 h_index g)))) = 
let s = objects2 h_index g in
assert (Seq.length (objects2 h_index g) > 0);
assert (Seq.length (objects2 h_index g) == 1);
assert (Seq.mem h_index (objects2 h_index g));
assert (~(exists y. y <> h_index /\ Seq.mem y ((objects2 h_index g))));
()

let objects2_property_lemma2  (g:heap{(Seq.length (objects2 0UL g) > 0)})
                              (h_index:hp_addr{(Seq.length (objects2 h_index g) > 0)})
               : Lemma
                 (ensures (forall x. Seq.mem x (objects2 h_index g) ==> Usize.v x >= Usize.v h_index)) = ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"
#push-options "--split_queries always"

#restart-solver

#restart-solver


val objects2_sweep_lemma3 : (h_index: hp_addr) ->
                            (g:heap{Seq.length (objects2 0UL g) > 0 /\
                                   Seq.mem h_index (objects2 0UL g)/\ 
                                  (Seq.length (objects2 h_index g) > 0)}) ->
                   Lemma
                   (ensures 
                   (let wz =  getWosize (read_word g h_index) in
                    let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                    let f_index_new =  Usize.add h_index_new mword in
                    Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g))))

val objects2_sweep_lemma4 : (h_index: hp_addr) ->
                           (g:heap{Seq.length (objects2 0UL g) > 0 /\
                                   Seq.mem h_index (objects2 0UL g)/\ 
                                  (Seq.length (objects2 h_index g) > 0)}) ->
                   Lemma
                   (requires 
                     (let wz =  getWosize (read_word g h_index) in
                     let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                     (~(Seq.mem h_index_new (objects2 h_index g)))))
                   
                   (ensures 
                     (let wz =  getWosize (read_word g h_index) in
                     let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                     let f_index_new =  Usize.add h_index_new mword in
                     Seq.length (objects2 h_index g) == 1))


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let rec sweep_with_free_list3 (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0)})
                             
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)/\ 
                                             (Seq.length (objects2 (hd_address f_index) g) > 0)
                              })
                             
                             (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                         color_of_object1 (hd_address fp) g == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
          
          : Tot (p:heap_heap_addr_pair{(Seq.length (objects2 0UL (fst p)) > 0) /\
                                       noGreyObjects (fst p) /\
                                       (Usize.v (snd p) >= Usize.v mword) /\
                                       (objects2 0UL g == objects2 0UL (fst p)) /\
                                       Seq.mem (hd_address (snd p)) (objects2 0UL (fst p)) /\
                                       color_of_object1 (hd_address (snd p)) (fst p) == blue /\
                                       (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word (fst p) x)) /\
                      
                                       (objects2 (hd_address f_index) g == objects2 (hd_address f_index) (fst p)) /\
                                       
                                       (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ color_of_object1 x g == black <==> 
                                             Seq.mem x (objects2 (hd_address f_index) (fst p)) /\ color_of_object1 x (fst p) == white) /\
                                           
                                       (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                                             Seq.mem x (objects2 (hd_address f_index) (fst p)) /\ color_of_object1 x (fst p) == blue) /\
                                       (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v (hd_address f_index) ==> 
                                             getColor (read_word g x) == getColor (read_word (fst p) x))}) 
           (decreases (heap_size - Usize.v f_index)) =

 let h_index = hd_address f_index in
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let f_index_new =  Usize.add h_index_new mword in
 wosize_plus_one_times_mword_multiple_of_mword wz;
 assert (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0);
 //assert (Usize.v h_index_new % Usize.v mword == 0);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index_new mword;

 assert (Usize.v (Usize.add h_index_new mword) % Usize.v mword == 0);
 assert (Usize.v f_index_new % Usize.v mword == 0);
 
 let g', fp' = sweep_body_with_free_list g f_index fp in
 sweep_body_with_free_list_lemma5 g f_index fp;
 assert (noGreyObjects g' /\ (Seq.length (objects2 0UL g') > 0));
 assert (Usize.v fp' >= Usize.v mword /\ 
        Seq.mem (hd_address fp') (objects2 0UL g') /\ 
        color_of_object1 (hd_address fp') g' == blue /\
       (forall x y. Seq.mem x (objects2 0UL g') /\ Seq.mem y (objects2 0UL g') ==>
                         Usize.v (getWosize (read_word g' x)) + Usize.v (getWosize (read_word g' y)) < heap_size));
 assert (Seq.mem (hd_address fp') (objects2 0UL g'));
 assert (color_of_object1 h_index g == white ==> color_of_object1 h_index g' == blue);
 assert (color_of_object1 h_index g == black ==> color_of_object1 h_index g' == white);
 assert (color_of_object1 h_index g == blue ==> color_of_object1 h_index g' == blue);
 assert (color_of_object1 h_index g' <> black);
 assert ((color_of_object1 h_index g == white \/  color_of_object1 h_index g == blue) <==>  color_of_object1 h_index g' == blue);
             
 assert (color_of_object1 h_index g == black <==> color_of_object1 h_index g' == white);
              
 assert (forall x. Seq.mem x (objects2 h_index g) /\ Usize.v x > Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
                                        
 assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x)); 
 if Usize.v f_index_new >= heap_size then
 (
   assert (objects2 (hd_address f_index) g == objects2 (hd_address f_index) g');
   objects2_cons_lemma2 h_index g;
   assert ((Seq.length (objects2 h_index g) > 0 /\ 
                        Usize.v (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) >= heap_size ==> 
                          Seq.length (objects2 h_index g) == 1));
   
   assert (Seq.mem h_index (objects2 0UL g));
   assert (Usize.v h_index + ((Usize.v (getWosize (read_word g h_index)) + 1) *  Usize.v mword) + Usize.v mword  == Usize.v f_index_new);
   assert (Usize.v h_index + ((Usize.v (getWosize (read_word g h_index)) + 1) *  Usize.v mword) == Usize.v h_index_new);
   assert (Usize.v f_index_new >= heap_size);
   assert (Seq.length (objects2 h_index g) > 0);
   objects2_sweep_lemma3 h_index g;
   assert (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g)));
   assert (~(Seq.mem h_index_new (objects2 h_index g)));
   objects2_sweep_lemma4 h_index g;
   assert (~(Seq.mem h_index_new (objects2 h_index g)) /\ (Seq.length (objects2 (hd_address f_index) g) > 0) ==> Seq.length (objects2 h_index g) == 1);
   assert (Seq.length (objects2 h_index g) == 1);
   assert (Seq.mem h_index (objects2 h_index g));
   objects2_property_lemma g h_index;
   assert (~(exists y.  y <> h_index /\ Seq.mem y ((objects2 h_index g))));
   assert (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ color_of_object1 x g == black <==> Seq.mem x (objects2 (hd_address f_index) g') /\ 
                                           color_of_object1 x g' == white);
   assert (forall x. Seq.mem x (objects2 h_index g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                               Seq.mem x (objects2 h_index g') /\ color_of_object1 x g' == blue);
   
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x));
   (g',fp')
 )
 else
 (
   assert (Usize.v f_index_new < heap_size);
   assert (Usize.v f_index_new >= Usize.v mword);
   assert (UInt.fits (Usize.v f_index_new - Usize.v mword) Usize.n);

   assert (Seq.length (objects2 0UL g) > 0 /\ Seq.mem h_index (objects2 0UL g));
   objects2_mem_lemma1_app1 h_index g;
   assert (Seq.mem h_index_new (objects2 0UL g));
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   assert (h_index_new <> h_index);
   assert (Seq.mem h_index_new (objects2 0UL g'));
   
  
   assert (Usize.v f_index_new >= Usize.v mword); 
   //assert (Seq.mem h_index_new (objects2 0UL g'));
   assert (Usize.v f_index_new % Usize.v mword == 0);
   assert (Usize.v f_index_new < heap_size);
   assert (is_hp_addr f_index_new);
   assert (Usize.v h_index_new < heap_size);
   assert (Seq.length (objects2 0UL g') > 0);
   assert (noGreyObjects g' /\ (Seq.length (objects2 0UL g') > 0));
   assert ((Seq.length (objects2 h_index g') > 0) /\ (Usize.v h_index_new < heap_size));
   assert (Seq.length (objects2 0UL g') > 0);
   assert (Seq.mem  h_index (objects2 0UL g'));
   assert (Usize.v h_index_new == (Usize.v h_index +  (Usize.v (getWosize (read_word g h_index)) + 1) * Usize.v mword));
   objects2_length_lemma3 g' h_index h_index_new; 
   let g'',fp'' = sweep_with_free_list3 g' f_index_new fp' in
   objects2_equal_lemma3 h_index g' g'';
   objects2_cons_lemma1 h_index g h_index_new;
   objects2_cons_lemma1 h_index g' h_index_new;
   objects2_cons_lemma1 h_index g'' h_index_new;
   assert (Seq.length (objects2 h_index g) > 0 /\  Usize.v h_index_new < heap_size ==> 
                      ((objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g)) /\
                      (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g))));
                        
   assert (Seq.length (objects2 h_index g) > 0 /\  Usize.v h_index_new < heap_size);
                       
   assert (((objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g)) /\
            (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g))));
   
   assert (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)));

   assert (((objects2 h_index g') == Seq.cons h_index (objects2 h_index_new g')) /\
            (forall x. Seq.mem x (objects2 h_index g') <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g'))));

   assert (((objects2 h_index g'') == Seq.cons h_index (objects2 h_index_new g'')) /\
           (forall x. Seq.mem x (objects2 h_index g'') <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g''))));
   assert  (objects2 (hd_address f_index) g' == objects2 (hd_address f_index) g'');
   assert  (objects2 (hd_address f_index) g == objects2 (hd_address f_index) g');
   
   
   objects2_equal_lemma3 h_index_new g' g'';
   assert (forall x. Seq.mem x (objects2 h_index_new g') /\ color_of_object1 x g' == black <==> Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white);
   objects2_length_lemma3 g h_index h_index_new; 
   objects2_property_lemma2 g h_index_new;
   assert (forall x. Seq.mem x (objects2 h_index_new g) ==> Usize.v x >= Usize.v h_index_new);
   
   
   assert (forall x. Seq.mem x (objects2 h_index_new g) /\ color_of_object1 x g == black <==> Seq.mem x (objects2 h_index_new g') /\ color_of_object1 x g' == black);
   assert (forall x. Seq.mem x (objects2 h_index_new g) /\ color_of_object1 x g == black <==> Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white);

   
   
   
   assert (color_of_object1 h_index g == black <==> color_of_object1 h_index g'' == white);
   assert (forall x. (x == h_index /\  color_of_object1 x g == black) \/ (Seq.mem x (objects2 h_index_new g) /\ color_of_object1 x g == black) <==> 
                   (x == h_index /\  color_of_object1 x g'' == white) \/ (Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white));
   assert (forall x. (x == h_index \/ Seq.mem x (objects2 h_index_new g)) /\ color_of_object1 x g == black <==> 
                   (x == h_index \/ Seq.mem x (objects2 h_index_new g'')) /\ color_of_object1 x g'' == white);
   assert (forall x. Seq.mem x (objects2 h_index g) /\ color_of_object1 x g == black <==> 
                   Seq.mem x (objects2 h_index g'') /\ color_of_object1 x g'' == white);
   
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index_new ==> getColor (read_word g' x) == getColor (read_word g'' x));
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g' x)); 
   assert (forall x. Seq.mem x (objects2 0UL g) /\ Usize.v x < Usize.v h_index ==> getColor (read_word g x) == getColor (read_word g'' x));
   (g'',fp'')
 )



#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

#restart-solver

#restart-solver 

#restart-solver

#restart-solver

#restart-solver


let sweep_with_free_list3_heap_lemma (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0)})
                                     (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                         color_of_object1 (hd_address fp) g == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)}) 
                         : Lemma
                           (requires (let f_index = mword in
                                      let h_index = hd_address f_index in
                                      let wz =  getWosize (read_word g h_index) in
                                      let h_index_new = Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword)  in
                                      let f_index_new =  Usize.add h_index_new mword in
                                       (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g))) /\
                                       (~(Seq.mem h_index_new (objects2 h_index g)) /\ (Seq.length (objects2 (hd_address f_index) g) > 0) ==> Seq.length (objects2 h_index g) == 1)))
                           
                           (ensures(let g1,_ = sweep_with_free_list3 g mword fp in
                           
                                   (forall x. Seq.mem x (objects2 0UL g1) ==>  
                                             color_of_object1 x g1 == white \/  color_of_object1 x g1 == blue) /\
                                   (forall x. Seq.mem x (get_allocated_block_addresses g1) <==> Seq.mem x (objects2 0UL g1) /\
                                   (color_of_object1 x g1 == white)))) =
  let f_index = mword in
  let s = objects2 0UL g in
  assert (Usize.v mword >= Usize.v mword);
  let h_index = hd_address f_index in
  assert (h_index == 0UL);
  assert (Seq.mem (hd_address f_index) (objects2 0UL g));
  assert (Seq.length (objects2 (hd_address f_index) g) > 0);
  let wz =  getWosize (read_word g h_index) in
  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
  let f_index_new =  Usize.add h_index_new mword in
  let g1, fp1 = sweep_with_free_list3 g f_index fp in
  assert (noGreyObjects g1);
  assert (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                                             Seq.mem x (objects2 (hd_address f_index) g1) /\ color_of_object1 x g1 == blue);
  
  assert (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ color_of_object1 x g == black <==> 
                                             Seq.mem x (objects2 (hd_address f_index) g1) /\ color_of_object1 x g1 == white);
  
  assert (forall x. Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                                             Seq.mem x (objects2 0UL g1) /\ color_of_object1 x g1 == blue);
  
  assert (forall x. Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == black <==> 
                                             Seq.mem x (objects2 0UL g1) /\ color_of_object1 x g1 == white);
  
  
  objects2_color_lemma 0UL g;
  assert (forall x. Seq.mem x (objects2 h_index g) ==> ~(color_of_object1 x g == gray));
  assert (forall x. Seq.mem x (objects2 h_index g) ==> color_of_object1 x g == white \/ color_of_object1 x g == black \/ color_of_object1 x g == blue);
  assert (forall x. Seq.mem x (objects2 h_index g1) ==> color_of_object1 x g1 == blue \/ color_of_object1 x g1 == white);
  assert (forall x. Seq.mem x (objects2 0UL g1) ==>  color_of_object1 x g1 == white \/  color_of_object1 x g1 == blue);
  let allocs = get_allocated_block_addresses g1 in
  assert (forall x. Seq.mem x allocs <==> Seq.mem x (objects2 0UL g1) /\
                                   (color_of_object1 x g1 == white \/
                                   color_of_object1 x g1 == black \/
                                   color_of_object1 x g1 == gray));
  assert (forall x. Seq.mem x (objects2 h_index g1) ==> ~(color_of_object1 x g1 == black));

  assert (forall x. Seq.mem x allocs <==> Seq.mem x (objects2 0UL g1) /\
                                   (color_of_object1 x g1 == white));
  ()

let root_props (g:heap{well_formed_heap2 g})
               (root_set: seq Usize.t ) =
     G.is_vertex_set root_set /\
     (forall x. Seq.mem x root_set ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
     (forall x. Seq.mem x root_set ==> Usize.v x % Usize.v mword == 0)

let f_id (f:Usize.t) =
     (Usize.v f >= Usize.v mword /\ Usize.v f < heap_size) /\
     (Usize.v f % Usize.v mword == 0)  

#restart-solver

#restart-solver


let props_reach (g:heap{well_formed_heap2 g /\ 
                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                (g1:heap{well_formed_heap2 g1 /\
                        (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})
                (root_set : seq Usize.t{root_props g root_set})
                (f_index: Usize.t {f_id f_index /\ 
                                    Seq.mem (hd_address f_index) (objects2 0UL g1) /\ 
                                    isBlackObject1 (hd_address f_index) g1 /\
                                    G.vertex_mem f_index (create_graph_from_heap g).vertices /\
                                    (create_graph_from_heap g == create_graph_from_heap g1)})
                =
   (exists o (z1: G.reach (create_graph_from_heap g) o f_index) . Seq.mem o root_set /\  
                  G.reachfunc (create_graph_from_heap g) o f_index z1)

                                                                        
#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries always"

#restart-solver 

let succ_reach_transitive_lemma1_from_graph (g:heap{well_formed_heap2 g})
                                            (x: Usize.t) 
                                            (o: Usize.t)
                            : Lemma
                                   (requires ((all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                             (let grph = create_graph_from_heap g in
                                             G.mem_graph_vertex grph o /\
                                             G.mem_graph_vertex grph x /\
                                             (exists (p: (G.reach grph o x)). G.reachfunc grph o x p))))
                                   (ensures 
                                              (let grph = create_graph_from_heap g in
                                              (forall y. G.vertex_mem y (G.successors grph x) ==> 
                                                  (exists (r1: G.reach grph o y).G.reachfunc grph o y r1)))) =
  
  let grph = create_graph_from_heap g in
  G.succ_reach_transitive_lemma1 grph o x;

  ()


#reset-options "--z3rlimit 500"

#restart-solver

#restart-solver

let stack_obj_rel (g:heap{well_formed_heap2 g}) 
                  (st: seq Usize.t {stack_props_func g st /\ G.is_emptySet st}) 
          : Lemma
            (ensures (noGreyObjects g)) =
 assert (stack_props_func g st);
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>  Seq.mem x st);
 assert (forall x. Seq.mem (f_address (hd_address x)) (objects2 0UL g) /\ isGrayObject1 (f_address (hd_address x)) g <==>  
                                                                      Seq.mem (f_address x) st);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>  
                                                                      Seq.mem (f_address x) st);
 assert (Seq.length st == 0);

 assert (~(exists x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (noGreyObjects g);
 ()


#restart-solver

(*No grey objects remain after mark is proved. This means after the mark, there are no Dangling pointers in the heap*)
let rec mark7_no_grey_nodes_lemma (g:heap{well_formed_heap2 g}) 
              (st: seq Usize.t {stack_props_func g st })
           : Lemma
            (requires True)
            (ensures (noGreyObjects (mark7 g st)))
            (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
if (G.is_emptySet st) then
   (
      assert (Seq.length st == 0);
      assert (stack_props_func g st);
      assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>  Seq.mem x st);
      assert (~(exists x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g));
      assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g) ==> ~(color_of_object1 (hd_address x) g == gray)));
      stack_obj_rel g st;
      assert (noGreyObjects g);
      assert (noGreyObjects (mark7 g st));
      ()
   )
 else
   (
     let st', g' = mark5_body1 g st in
     mark_body_mark_body1_lemma g st;
     let v_id = Seq.index st (Seq.length st - 1) in
     assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
     assert (is_valid_header (hd_address v_id) g);
     stack_slice_only_has_gray_color_lemma g st v_id 3UL;
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g 3UL)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g 3UL)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)));
      
     mark5_body_black_nodes_lemma g st;
     assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
     
     assert (well_formed_heap2 g');
     assert ((forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g') /\
                                                            (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0) /\
                                                            (G.is_vertex_set st') /\
                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                                   Seq.mem x st'));
     
     let g'' = mark7 g' st' in
     mark7_no_grey_nodes_lemma g' st';
     assert (noGreyObjects g'');
     ()
   ) 



#restart-solver

let graph_creation_necessary_condition (g:heap{well_formed_heap2 g})  =
(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                              (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)

let st_vl_root_set_subset_of_ff_allocs (g:heap{well_formed_heap2 g /\
                                              graph_creation_necessary_condition g}) 
                                           (st: seq Usize.t {stack_props_func g st})
                                           (vl: seq Usize.t {vl_props_func g vl}) 
                                          (root_set : seq Usize.t{root_props g root_set}) =

                              (
                                let allocs_g = get_allocated_block_addresses g in
                                let ff_address_g = first_field_addresses_of_allocated_blocks g allocs_g in
                                 (G.subset_vertices st ff_address_g) /\
                                 (G.subset_vertices vl ff_address_g) /\
                                 (G.subset_vertices root_set ff_address_g))

let mutual_exclusivity_of_st_vl (g:heap{well_formed_heap2 g}) 
                                (st: seq Usize.t {stack_props_func g st})
                                (vl: seq Usize.t {vl_props_func g vl}) =
   (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
   (forall x. Seq.mem x vl ==> ~(Seq.mem x st))

let pre_conditions_for_dfs_lemma_invoke (g:heap{well_formed_heap2 g}) 
                                        (st: seq Usize.t {stack_props_func g st})
                                        (vl: seq Usize.t {vl_props_func g vl}) 
                                        (root_set : seq Usize.t{root_props g root_set})= 

  (let grph = create_graph_from_heap g in
                              (forall o x (z2: G.reach grph o x). (G.reachfunc grph o x z2) /\ Seq.mem o root_set ==> 
                               (Seq.mem x vl \/ (exists y (z3: G.reach grph y x). G.reachfunc grph y x z3 /\ Seq.mem y st))) /\
                               
                               //Pre-condition to call dfs_backward lemma
                               (forall c b (r_cb: G.reach grph c b). (Seq.mem c vl /\ G.reachfunc grph c b r_cb /\ ~(c = b)) ==>
                                  (Seq.mem b vl \/ Seq.mem b st \/ (exists d. Seq.mem d st /\ 
                                   Seq.mem d (G.vertices_in_path grph c b r_cb)))) /\
                               
                               //Pre-condition to call dfs_forward lemma
                               (forall x. Seq.mem x st ==> (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1))/\ 
                               (forall x. Seq.mem x vl ==> (exists o (z1: G.reach grph o x). Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)))

#restart-solver

let black_objs_reachable_post_condition (g:heap{well_formed_heap2 g /\
                                                graph_creation_necessary_condition g}) 
                                        (st: seq Usize.t {stack_props_func g st}) 
                                        (root_set : seq Usize.t{root_props g root_set}) =
let grph = create_graph_from_heap g in 
let g1 = mark5 g st in
  (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1))

//#push-options "--split_queries always"

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

(*All black objects in the heap resulted after mark is reachable from a root set, where the root set satisfies the reachability
  pre-conditions with respect to visited set and stack*)
let all_black_objs_after_mark_is_reachable (g:heap{well_formed_heap2 g}) 
                                                  (st: seq Usize.t {stack_props_func g st})
                                                  (vl: seq Usize.t {vl_props_func g vl}) 
                                                  (root_set : seq Usize.t{root_props g root_set})

                                                  (c:color{c == 3UL})
                                                  (c1:color{c1 == 2UL})
                                
                 : Lemma
                   (requires  graph_creation_necessary_condition g /\
                              
                              st_vl_root_set_subset_of_ff_allocs g st vl root_set /\ 

                              mutual_exclusivity_of_st_vl g st vl /\
                              
                              pre_conditions_for_dfs_lemma_invoke g st vl root_set
                              
                   )
                  (ensures (let grph = create_graph_from_heap g in 
                            let g1 = mark5 g st in
                            (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)))) =
  
  let grph = create_graph_from_heap g in
  let g1 = mark5 g st in
  dfs_mark_equivalence_lemma g st vl c c1;
  assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                 Seq.mem x (D.dfs grph
                                            st
                                            vl)));
  D.dfs_equality_lemma grph st vl;
  
  assert (D.dfs grph st vl == D.dfs7 grph st vl);
  D.dfs7_lemma_backward grph st vl root_set;
  D.dfs_lemma_forward grph st vl root_set;

  (*assert ((forall x. Seq.mem x (D.dfs grph st vl) <==> (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)));
  
  assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 ==>
                (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)));   *)  
  
 
  ()

(*All successors of a black object in the heap after mark is reachable from some object in the root set if root set satisfies the 
  reachability preconditions with respect to visited set and stack*)

#restart-solver

let free_list_ptr_props (g:heap{well_formed_heap2 g})
                        (fp:hp_addr) =
   Usize.v fp >= Usize.v mword /\
    Seq.mem (hd_address fp) (objects2 0UL g) /\ 
    color_of_object1 (hd_address fp) g == blue (*/\
    (forall x y. Seq.mem x (objects2 0UL g) /\ 
    Seq.mem y (objects2 0UL g) ==>
                    Usize.v (getWosize (read_word g x)) + 
                    Usize.v (getWosize (read_word g y)) < heap_size)*)


#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

let all_whites_reach_pre (g:heap{well_formed_heap2 g}) 
                                             (st: seq Usize.t {stack_props_func g st})
                                             (vl: seq Usize.t {vl_props_func g vl}) 
                                             (root_set : seq Usize.t{root_props g root_set /\
                                                (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                 (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) }) =
   let allocs_g = get_allocated_block_addresses g in
                                let ff_address_g = first_field_addresses_of_allocated_blocks g allocs_g in
                                 (G.subset_vertices st ff_address_g) /\
                                 (G.subset_vertices vl ff_address_g) /\
                                 (G.subset_vertices root_set ff_address_g) /\ 

                              (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                              (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                              
                              (let grph = create_graph_from_heap g in
                              (forall o x (z2: G.reach grph o x). (G.reachfunc grph o x z2) /\ Seq.mem o root_set ==> 
                               (Seq.mem x vl \/ (exists y (z3: G.reach grph y x). G.reachfunc grph y x z3 /\ Seq.mem y st))) /\
                               
                               //Pre-condition to call dfs_backward lemma
                               (forall c b (r_cb: G.reach grph c b). (Seq.mem c vl /\ G.reachfunc grph c b r_cb /\ ~(c = b)) ==>
                                  (Seq.mem b vl \/ Seq.mem b st \/ (exists d. Seq.mem d st /\ 
                                   Seq.mem d (G.vertices_in_path grph c b r_cb)))) /\
                               
                               //Pre-condition to call dfs_forward lemma
                               (forall x. Seq.mem x st ==> (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1))/\ 
                               (forall x. Seq.mem x vl ==> (exists o (z1: G.reach grph o x). Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1)))


#restart-solver

#restart-solver

let all_whites_reach_pre1 (g:heap{well_formed_heap2 g}) 
                                             (st: seq Usize.t {stack_props_func g st})
                                             (vl: seq Usize.t {vl_props_func g vl}) 
                                             (root_set : seq Usize.t{root_props g root_set /\
                                                (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                 (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                                    all_whites_reach_pre g st vl root_set}) =

  let g1 = mark5 g st in
  let grph = create_graph_from_heap g in 
   (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1))


let all_whites_reach_pre2 (g:heap{well_formed_heap2 g}) 
                                             (st: seq Usize.t {stack_props_func g st})
                                             (vl: seq Usize.t {vl_props_func g vl}) 
                                             (root_set : seq Usize.t{root_props g root_set /\
                                                (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                 (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                                    all_whites_reach_pre g st vl root_set /\
                                                    all_whites_reach_pre1 g st vl root_set}) =

  let g1 = mark5 g st in
  let grph = create_graph_from_heap g in 
   (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 ==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1))


//#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

#restart-solver


let sweep_white_post_variant2  (g1:heap{well_formed_heap2 g1}) 
                               (g2:heap{Seq.length (objects2 0UL g2) > 0}) =
  (forall x.   Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                          isWhiteObject1 (hd_address x) g2 <==>
  
                  Seq.mem (hd_address x) (objects2 0UL g1) /\ 
                      isBlackObject1 (hd_address x) g1
                         )


  

#reset-options "--z3rlimit 500"

#restart-solver

#restart-solver

let all_whites_reach_pre7 (g:heap{well_formed_heap2 g}) 
                                             (st: seq Usize.t {stack_props_func g st})
                                             (vl: seq Usize.t {vl_props_func g vl}) 
                                             (root_set : seq Usize.t{root_props g root_set /\
                                                (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                 (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                                    all_whites_reach_pre g st vl root_set /\
                                                    all_whites_reach_pre1 g st vl root_set}) 
                                            (g2:heap{Seq.length (objects2 0UL g2) > 0 (*/\
                                                     (objects2 0UL g2) == (objects2 0UL (mark5 g st))*) (*/\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL (mark5 g st)) /\ 
                                                                 isBlackObject1 (hd_address x) (mark5 g st)) <==>
                                                        (forall x. Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                                                 isWhiteObject1 (hd_address x) g2)*)})=
  let g1 = mark5 g st in
  let grph = create_graph_from_heap g in 
  assert (all_whites_reach_pre1 g st vl root_set);
  //assert (all_whites_reach_pre2 g st vl root_set);
  (*assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1));
  
  assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 ==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1));
  
  (*assert (forall x. Seq.mem (hd_address x) (objects2 0UL g2) /\ isWhiteObject1 (hd_address x) g2 <==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1));*)
  
  (*assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 ==>
                                       (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o x z1));*)*)
  admit()

#reset-options "--z3rlimit 500"

let sweep_white_post  (g1:heap{well_formed_heap2 g1}) 
                      (g2:heap{Seq.length (objects2 0UL g2) > 0}) =
 (forall x. Seq.mem x (objects2 (hd_address mword) g1) /\ 
                    color_of_object1 x g1 == black <==> 
                    Seq.mem x (objects2 (hd_address mword) g2) /\ color_of_object1 x g2 == white)

let sweep_white_post_variant1  (g1:heap{well_formed_heap2 g1}) 
                               (g2:heap{Seq.length (objects2 0UL g2) > 0}) =
 (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ 
                      color_of_object1 (hd_address x) g1 == black <==> 
                      Seq.mem (hd_address x) (objects2 0UL g2) /\ color_of_object1 (hd_address x) g2 == white)



#restart-solver

let sweep_white_props  (g1:heap{well_formed_heap2 g1}) 
                       (g2:heap{Seq.length (objects2 0UL g2) > 0})
              : Lemma
                (requires 
                   sweep_white_post g1 g2)
                
                (ensures 
                   sweep_white_post_variant1 g1 g2 /\
                   sweep_white_post_variant2 g1 g2
                ) =
  assert (forall x. Seq.mem x (objects2 (hd_address mword) g1) /\ 
                    color_of_object1 x g1 == black <==> 
                    Seq.mem x (objects2 (hd_address mword) g2) /\ color_of_object1 x g2 == white);
  
  assert (forall x. Seq.mem x (objects2 0UL g1) /\ 
                    color_of_object1 x g1 == black <==> 
                    Seq.mem x (objects2 0UL g2) /\ color_of_object1 x g2 == white);
  
  assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ 
                    color_of_object1 (hd_address x) g1 == black <==> 
                    Seq.mem (hd_address x) (objects2 0UL g2) /\ color_of_object1 (hd_address x) g2 == white);
  
  assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ 
                      isBlackObject1 (hd_address x) g1 <==> 
                    Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                      isWhiteObject1 (hd_address x) g2);
  ()

 #restart-solver

 #reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


 let all_whites_reach_pre3 (g:heap{well_formed_heap2 g}) 
                                             (st: seq Usize.t {stack_props_func g st})
                                             (vl: seq Usize.t {vl_props_func g vl}) 
                                             (root_set : seq Usize.t{root_props g root_set /\
                                                (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                 (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                                    all_whites_reach_pre g st vl root_set /\
                                                    all_whites_reach_pre1 g st vl root_set})
                                             (g2:heap{Seq.length (objects2 0UL g2) > 0}) =

  let grph = create_graph_from_heap g in 
  let g1 = mark5 g st in
  sweep_white_post_variant2 (mark5 g st) g2 /\
          all_whites_reach_pre1 g st vl root_set


let sweep_white_post_variant3  (g1:heap{well_formed_heap2 g1}) 
                               (g2:heap{Seq.length (objects2 0UL g2) > 0}) =
  (forall x.   Seq.mem x (objects2 0UL g2) /\ 
                          isWhiteObject1 x g2 <==>
  
                  Seq.mem x (objects2 0UL g1) /\ 
                      isBlackObject1 x g1
                         )
#restart-solver


let all_black_obj_reach (g:heap{well_formed_heap2 g}) 
                                             (st: seq Usize.t {stack_props_func g st})
                                             (vl: seq Usize.t {vl_props_func g vl}) 
                                             (root_set : seq Usize.t{root_props g root_set /\
                                                (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                 (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                                    all_whites_reach_pre g st vl root_set}) =

  
  let g1 = mark5 g st in
  let grph = create_graph_from_heap g in 

  (forall x. Seq.mem x (objects2 0UL g1) /\ isBlackObject1 x g1 <==>
                                       (*without membership in graph vertices condition, this prop will not typecheck*)
                                       Seq.mem (f_address x) (grph.vertices) /\
                                       (exists o (z1: G.reach grph o (f_address x)) . Seq.mem o root_set /\
                                                                         G.reachfunc grph o (f_address x) z1))


#restart-solver

#restart-solver


let all_whites_reach_pre5 (g:heap{well_formed_heap2 g}) 
                                             (st: seq Usize.t {stack_props_func g st})
                                             (vl: seq Usize.t {vl_props_func g vl}) 
                                             (root_set : seq Usize.t{root_props g root_set /\
                                                (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                 (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                                    all_whites_reach_pre g st vl root_set /\
                                                    all_whites_reach_pre1 g st vl root_set})
                                             (g2:heap{Seq.length (objects2 0UL g2) > 0}) =

  let grph = create_graph_from_heap g in 
  let g1 = mark5 g st in
   (forall x.   Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                isWhiteObject1 (hd_address x) g2 <==>
                 (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                             G.reachfunc grph o x z1))




#reset-options "--z3rlimit 500"


let all_whites_objects_are_reachable_from_the_root_set (g:heap{well_formed_heap2 g}) 
                                                       (st: seq Usize.t {stack_props_func g st})
                                                       (vl: seq Usize.t {vl_props_func g vl}) 
                                                       (root_set : seq Usize.t{root_props g root_set /\
                                                                  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                                  (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                                                  all_whites_reach_pre g st vl root_set /\
                                                                  all_whites_reach_pre1 g st vl root_set})
                                              
                                              (g2:heap{Seq.length (objects2 0UL g2) > 0 /\
                                                       (objects2 0UL g2) = (objects2 0UL (mark5 g st)) /\
                                                       well_formed_heap2 g2})
                      : Lemma
                        (requires (sweep_white_post_variant2 (mark5 g st) g2)) 
                        (ensures all_whites_reach_pre3 g st vl root_set g2) =
  
  assert (all_whites_reach_pre1 g st vl root_set);
  assert (sweep_white_post_variant2 (mark5 g st) g2);
  assert (sweep_white_post_variant2 (mark5 g st) g2 /\
          all_whites_reach_pre1 g st vl root_set);
  assert (all_whites_reach_pre3 g st vl root_set g2);
  
  ()                            

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"






#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries always"

open FStar.Classical

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let black_field_props (g:heap{well_formed_heap2 g /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                      (g1:heap{well_formed_heap2 g1 /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                      (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})                             
                      (root_set : seq Usize.t{root_props g root_set})
                      (f_index: Usize.t {f_id f_index /\ 
                                         Seq.mem (hd_address f_index) (objects2 0UL g1) /\ 
                                         isBlackObject1 (hd_address f_index) g1 /\
                                        Seq.mem f_index (create_graph_from_heap g).vertices /\
                                        create_graph_from_heap g == create_graph_from_heap g1}) =

(forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==> 
                                       (exists o (z1: G.reach (create_graph_from_heap g) o x). Seq.mem o root_set /\ 
                                                      G.reachfunc (create_graph_from_heap g) o x z1) ==>
                                        Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1)


let black_field_props1 (g:heap{well_formed_heap2 g /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                      (g1:heap{well_formed_heap2 g1 /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                      (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})                             
                      (root_set : seq Usize.t{root_props g root_set})
                      (f_index: Usize.t {f_id f_index /\ 
                                         Seq.mem (hd_address f_index) (objects2 0UL g1) /\ 
                                         isBlackObject1 (hd_address f_index) g1 /\
                                        Seq.mem f_index (create_graph_from_heap g).vertices /\
                                        create_graph_from_heap g == create_graph_from_heap g1}) =

(forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==> 
                      Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1)

(*Instantiation
  g ---> initial heap
  g1 ---> heap after mark
  g2 ---> heap after sweep
  
  graph from g1 == graph from g2
  f_index ---> A black object address in g1
  The below lemma proves that a black object in g1 is part of the allocated object set in g2
  The below lemma proves that for a white object in g2, all its successors in the original graph are members of white
  object set in g2*)
let black_field_props1_lemma  (g:heap{well_formed_heap2 g /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                      (g1:heap{well_formed_heap2 g1 /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                      (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})                             
                      (root_set : seq Usize.t{root_props g root_set})
                      (g2:heap{Seq.length (objects2 0UL g2) > 0 /\
                               (objects2 0UL g1) == (objects2 0UL g2) /\
                               (forall x. Seq.mem x (get_allocated_block_addresses g2) ==>
                                          Seq.mem x (get_allocated_block_addresses g1) )})
                      (f_index: Usize.t {f_id f_index /\ 
                                         Seq.mem (hd_address f_index) (objects2 0UL g1) /\ 
                                         isBlackObject1 (hd_address f_index) g1 /\
                                        Seq.mem f_index (create_graph_from_heap g).vertices /\
                                        create_graph_from_heap g == create_graph_from_heap g1})
                      
            : Lemma
              (requires (black_field_props1  g g1 st root_set f_index) /\
                         sweep_white_post_variant2 g1 g2 /\
                         (forall x. Seq.mem x (get_allocated_block_addresses g2) <==>
                                      Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2))
              
              (ensures (forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==> 
                                  Seq.mem x (get_allocated_block_addresses g2)) /\
                                  (Seq.mem (hd_address f_index) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address f_index) g2)) =

  assert (black_field_props1  g g1 st root_set f_index);
  assert (sweep_white_post_variant2 g1 g2);
  assert (forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==> 
                      Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1);
  assert  (forall x.   Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                          isWhiteObject1 (hd_address x) g2 <==>
  
                       Seq.mem (hd_address x) (objects2 0UL g1) /\ 
                         isBlackObject1 (hd_address x) g1
                         );
  assert (forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==> 
                    Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                          isWhiteObject1 (hd_address x) g2);
  
  assert (forall x. Seq.mem x (get_allocated_block_addresses g2) <==>
                                      Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2);
  assert (forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==> 
                    Seq.mem x (get_allocated_block_addresses g2));
  assert (Seq.mem (hd_address f_index) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address f_index) g2);
  
  ()

#restart-solver


let black_field_props1_lemma_  (g:heap{well_formed_heap2 g /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                      (g1:heap{well_formed_heap2 g1 /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                      (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})                             
                      (root_set : seq Usize.t{root_props g root_set})
                      (g2:heap{Seq.length (objects2 0UL g2) > 0 /\
                               (objects2 0UL g1) == (objects2 0UL g2) /\
                               (forall x. Seq.mem x (get_allocated_block_addresses g2) ==>
                                          Seq.mem x (get_allocated_block_addresses g1) )})
                      (f_index: Usize.t {f_id f_index /\ 
                                         Seq.mem (hd_address f_index) (objects2 0UL g1) /\ 
                                         isBlackObject1 (hd_address f_index) g1 /\
                                        Seq.mem f_index (create_graph_from_heap g).vertices /\
                                        create_graph_from_heap g == create_graph_from_heap g1})
                      
            : Lemma
              (requires (black_field_props1  g g1 st root_set f_index) /\
                         sweep_white_post_variant2 g1 g2 /\
                         (forall x. Seq.mem (hd_address x) (get_allocated_block_addresses g2) <==>
                                      Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2))
              
              (ensures (forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==> 
                                  Seq.mem (hd_address x) (get_allocated_block_addresses g2)) /\
                                  (Seq.mem (hd_address f_index) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address f_index) g2)) =
  assert (black_field_props1  g g1 st root_set f_index);
  assert (sweep_white_post_variant2 g1 g2);
  assert (forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==> 
                      Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1);
  assert  (forall x. Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                          isWhiteObject1 (hd_address x) g2 <==>
  
                       Seq.mem (hd_address x) (objects2 0UL g1) /\ 
                         isBlackObject1 (hd_address x) g1
                         );
  assert (forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==> 
                    Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                          isWhiteObject1 (hd_address x) g2);
 
  assert (forall x. Seq.mem (hd_address x) (get_allocated_block_addresses g2) <==>
                                      Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2);
  assert (forall x. Seq.mem x (G.successors (create_graph_from_heap g) f_index) ==> 
                    Seq.mem (hd_address x) (get_allocated_block_addresses g2));
  assert (Seq.mem (hd_address f_index) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address f_index) g2);
  ()




let black_pointer (g:heap{well_formed_heap2 g /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                      (g1:heap{well_formed_heap2 g1 /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                      (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})                             
                     
                      (f_index: Usize.t) =
 
 f_id f_index /\ 
  Seq.mem (hd_address f_index) (objects2 0UL g1) /\ 
  isBlackObject1 (hd_address f_index) g1 /\
  Seq.mem f_index (create_graph_from_heap g).vertices /\
  create_graph_from_heap g == create_graph_from_heap g1


let black_field_props1_lemma_all  (g:heap{well_formed_heap2 g /\
                                         (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                                  (g1:heap{well_formed_heap2 g1 /\
                                         (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                                  (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})                             
                                  (root_set : seq Usize.t{root_props g root_set})
                                  (g2:heap{Seq.length (objects2 0UL g2) > 0 /\
                                           (objects2 0UL g1) == (objects2 0UL g2) /\
                                           (forall x. Seq.mem x (get_allocated_block_addresses g2) ==>
                                                 Seq.mem x (get_allocated_block_addresses g1) )})
              : Lemma
              (requires  (create_graph_from_heap g == create_graph_from_heap g1) /\
                         (forall (x:Usize.t). black_pointer g g1 st x ==> black_field_props1 g g1 st root_set x) /\
                         sweep_white_post_variant2 g1 g2 /\
                         (forall x. Seq.mem x (get_allocated_block_addresses g2) <==>
                                      Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2))
              
              (ensures (forall x y. black_pointer g g1 st y ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem x (get_allocated_block_addresses g2)) /\
                                       (Seq.mem (hd_address y) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address y) g2))) =
  Classical.forall_intro (Classical.move_requires (black_field_props1_lemma g g1 st root_set g2));
  
  (*All black objects in g1 implies their successors in graph from heap g are members of allocated objects in g2 and
      the black objects in g1 are white objects in g2*)
  assert (forall x y. black_pointer g g1 st y ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g) y) ==> 
                                       Seq.mem x (get_allocated_block_addresses g2)) /\
                                       (Seq.mem (hd_address y) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address y) g2));
  
  
  assert (forall y. black_pointer g g1 st y ==>  
                        (G.successors (create_graph_from_heap g) y ==
                         G.successors (create_graph_from_heap g1) y));
  assert (forall x y. black_pointer g g1 st y ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem x (get_allocated_block_addresses g2)) /\
                                       (Seq.mem (hd_address y) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address y) g2));
  ()


let black_field_props1_lemma_all_  (g:heap{well_formed_heap2 g /\
                                         (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                                  (g1:heap{well_formed_heap2 g1 /\
                                         (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                                  (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})                             
                                  (root_set : seq Usize.t{root_props g root_set})
                                  (g2:heap{Seq.length (objects2 0UL g2) > 0 /\
                                           (objects2 0UL g1) == (objects2 0UL g2) /\
                                           (forall x. Seq.mem x (get_allocated_block_addresses g2) ==>
                                                 Seq.mem x (get_allocated_block_addresses g1) )})
              : Lemma
              (requires  (create_graph_from_heap g == create_graph_from_heap g1) /\
                         (forall (x:Usize.t). black_pointer g g1 st x ==> black_field_props1 g g1 st root_set x) /\
                         sweep_white_post_variant2 g1 g2 /\
                         (forall x. Seq.mem (hd_address x) (get_allocated_block_addresses g2) <==>
                                      Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2))
              
              (ensures (forall x y. black_pointer g g1 st y ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem (hd_address x) (get_allocated_block_addresses g2)) /\
                                       (Seq.mem (hd_address y) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address y) g2))) =
  
  Classical.forall_intro (Classical.move_requires (black_field_props1_lemma_ g g1 st root_set g2));
  assert (forall x y. black_pointer g g1 st y ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g) y) ==> 
                                       Seq.mem (hd_address x) (get_allocated_block_addresses g2)) /\
                                       (Seq.mem (hd_address y) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address y) g2));
  
  assert (forall y. black_pointer g g1 st y ==>  
                        (G.successors (create_graph_from_heap g) y ==
                         G.successors (create_graph_from_heap g1) y));
  assert (forall x y. black_pointer g g1 st y ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem (hd_address x) (get_allocated_block_addresses g2)) /\
                                       (Seq.mem (hd_address y) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address y) g2));
  ()

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let field_ptrs_of_a_black_obj_after_mark_is_black  (g:heap{well_formed_heap2 g /\
                                                          (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                                                   (g1:heap{well_formed_heap2 g1 /\
                                                            (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                                                   (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})
                                                   (vl: seq Usize.t {vl_props_func g vl}) 
                                                   (root_set : seq Usize.t{root_props g root_set})

                                                   (c:color{c == 3UL})
                                                   (c1:color{c1 == 2UL})
                                                   (f_index: Usize.t {f_id f_index /\ 
                                                                      Seq.mem (hd_address f_index) (objects2 0UL g1) /\ 
                                                                      isBlackObject1 (hd_address f_index) g1 /\
                                                                      Seq.mem f_index (create_graph_from_heap g).vertices /\
                                                                      create_graph_from_heap g == create_graph_from_heap g1})
                 : Lemma
                   (requires (graph_creation_necessary_condition g /\
                              
                              st_vl_root_set_subset_of_ff_allocs g st vl root_set /\ 

                              mutual_exclusivity_of_st_vl g st vl /\
                              
                              pre_conditions_for_dfs_lemma_invoke g st vl root_set)
                              
                              
                   )
                  (ensures (black_field_props1 g g1 st root_set f_index)) =
  all_black_objs_after_mark_is_reachable g st vl root_set c c1;
  let grph = create_graph_from_heap g in
  
  //Bring the witness of an o, to assert the reachability of successors of f_index
   let _ = exists_elim 
           (forall y. Seq.mem y (G.successors (create_graph_from_heap g) f_index) ==> 
                                                  (exists o (r1: G.reach (create_graph_from_heap g) o y). 
                                                     Seq.mem o root_set /\ G.reachfunc (create_graph_from_heap g) o y r1))
           ()
           (fun (o:hp_addr{Seq.mem o root_set /\ 
                         (exists (z1: G.reach (create_graph_from_heap g) o f_index). 
                             Seq.mem o root_set /\ G.reachfunc (create_graph_from_heap g) o f_index z1)}) -> 

              assert (G.mem_graph_vertex grph o);
              assert (Seq.mem f_index grph.vertices);
              assert (G.mem_graph_vertex grph f_index);
              assert (exists (p: (G.reach grph o f_index)). G.reachfunc grph o f_index p);
              let _ = succ_reach_transitive_lemma1_from_graph g f_index o in
              ()) in 
  assert ((forall y. Seq.mem y (G.successors (create_graph_from_heap g) f_index) ==> 
                                                  (exists o (r1: G.reach (create_graph_from_heap g) o y). 
                                                     Seq.mem o root_set /\ G.reachfunc (create_graph_from_heap g) o y r1)));
  
()



#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver



#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let black_field_props1_all (g:heap{well_formed_heap2 g /\
                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                      (g1:heap{well_formed_heap2 g1 /\
                              (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                      (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})                             
                      (root_set : seq Usize.t{root_props g root_set}) =

forall (x:Usize.t). black_pointer g g1 st x ==> black_field_props1 g g1 st root_set x

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver


#restart-solver

 
let field_ptrs_black_all  (g:heap{well_formed_heap2 g /\
                                                          (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                                                   (g1:heap{well_formed_heap2 g1 /\
                                                            (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                                                   (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})
                                                   (vl: seq Usize.t {vl_props_func g vl}) 
                                                   (root_set : seq Usize.t{root_props g root_set})

                                                   (c:color{c == 3UL})
                                                   (c1:color{c1 == 2UL})
                                                   
                 : Lemma
                   (requires (graph_creation_necessary_condition g /\
                              
                              st_vl_root_set_subset_of_ff_allocs g st vl root_set /\ 

                              mutual_exclusivity_of_st_vl g st vl /\
                              
                              pre_conditions_for_dfs_lemma_invoke g st vl root_set)
                              
                   ) 
                   (ensures (black_field_props1_all g g1 st root_set))=
  
 Classical.forall_intro (Classical.move_requires (field_ptrs_of_a_black_obj_after_mark_is_black g g1 st vl root_set c c1));
 assert (forall (x:Usize.t). black_pointer g g1 st x ==> black_field_props1 g g1 st root_set x);
 assert (black_field_props1_all g g1 st root_set);
 ()

#reset-options "--z3rlimit 500"



let field_reads_equal_lemma1 (g:heap{Seq.length (objects2 0UL g) > 0})
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

let field_reads_equal_h_index_lemma1 (g:heap{Seq.length (objects2 0UL g) > 0})
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

#restart-solver

let field_reads_all_equal_lemma1 (g:heap{Seq.length (objects2 0UL g) > 0})
                                 (g':heap)
                                 (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                 (x:hp_addr{Seq.mem x (objects2 0UL g) /\ x <> h_index})
                      : Lemma
                        (requires (objects2 0UL g == objects2 0UL g') /\
                              (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                        (ensures (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                        read_word g y == read_word g' y)) = 
 Classical.forall_intro (Classical.move_requires (field_reads_equal_lemma1 g g' h_index x))
 

#restart-solver 

let field_reads_all_equal_h_index_lemma1 (g:heap{Seq.length (objects2 0UL g) > 0})
                                         (g':heap)
                                         (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                            : Lemma
                              (requires (objects2 0UL g == objects2 0UL g') /\
                                        (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                              (ensures (forall y. Usize.v y >= Usize.v h_index + Usize.v mword /\
                                             Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword) ==>
                                                   read_word g y == read_word g' y)) = 
 Classical.forall_intro (Classical.move_requires (field_reads_equal_h_index_lemma1 g g' h_index))

#restart-solver 

let field_reads_all_equal_for_all_objects_lemma1 (g:heap{Seq.length (objects2 0UL g) > 0})
                                                 (g':heap)
                                                 (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                 :Lemma
                                 (requires (objects2 0UL g == objects2 0UL g') /\
                                          (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t)) 
                              
                                 (ensures (forall x y. Seq.mem x (get_allocated_block_addresses g) ==>
                                               (Usize.v y >= Usize.v x + Usize.v mword /\
                                               Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y)))  =
Classical.forall_intro (Classical.move_requires (field_reads_all_equal_lemma1 g g' h_index));
(field_reads_all_equal_h_index_lemma1 g g' h_index);
assert (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y);

assert (forall x y. Seq.mem x (objects2 0UL g) ==>
                     (Usize.v y >= Usize.v x + Usize.v mword /\
                      Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y));
assert (forall x y. Seq.mem x (get_allocated_block_addresses g) ==>
                     (Usize.v y >= Usize.v x + Usize.v mword /\
                      Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y));

()

let field_reads_equal (g:heap{Seq.length (objects2 0UL g) > 0}) 
                      (g':heap{Seq.length (objects2 0UL g') > 0}) =
  
  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                                     read_word g y == read_word g' y)


let field_reads_equal_new_lemma (g:heap{Seq.length (objects2 0UL g) > 0})
                                (g':heap)
                                (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                        : Lemma
                          (requires (objects2 0UL g == objects2 0UL g') /\
                                    (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                               Seq.mem x (get_allocated_block_addresses g)))
                          (ensures field_reads_equal g g') =
 field_reads_all_equal_for_all_objects_lemma1 g g' h_index;
 assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g));
 assert (field_reads_equal g g');
 ()


#restart-solver 


#reset-options "--z3rlimit 500"

#restart-solver

#restart-solver

 let colorHeader3_black_object_colored_white_lemma (v_id:hp_addr)  
                                                   (g:heap{Seq.length (objects2 0UL g) > 0}) 
                                                   (c:color)
                         : Lemma
                           (requires (c == white) /\
                                     (mem v_id (objects2 0UL g)) /\
                                     (color_of_object1 v_id g == black))

                           (ensures  (let g' = colorHeader3 v_id g c in
                                      let allocs = (get_allocated_block_addresses g) in
                                      let allocs' = (get_allocated_block_addresses g') in
                                      (forall x. Seq.mem x allocs' ==>
                                                 Seq.mem x allocs) /\
                                      (forall x. Seq.mem x allocs' ==>
                                                 getWosize(read_word g x) == getWosize(read_word g' x)) /\
                                      (forall x. Seq.mem x allocs' ==>
                                                 getTag(read_word g x) == getTag(read_word g' x)) /\
                                      field_reads_equal g g')) =
  let allocs = get_allocated_block_addresses g in
  let g' = colorHeader3 v_id g c in
  assert (heap_remains_same_except_index_v_id v_id g g');

  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    getWosize(read_word g x) == getWosize(read_word g' x));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    getTag(read_word g x) == getTag(read_word g' x));
  
  field_reads_equal_new_lemma g g' v_id;
  assert (field_reads_equal g g');
  ()


let colorHeader3_white_object_colored_blue_lemma1  (v_id:hp_addr)  
                                                   (g:heap{Seq.length (objects2 0UL g) > 0}) 
                                                   (c:color)
                         : Lemma
                           (requires (c == blue) /\
                                     (mem v_id (objects2 0UL g)) /\
                                     (color_of_object1 v_id g == white)
                                     )
                           (ensures  (let g' = colorHeader3 v_id g c in
                                      (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                           getWosize(read_word g x) == getWosize(read_word g' x)) /\
                                      (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                           getTag(read_word g x) == getTag(read_word g' x)) /\
                                      (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                           Seq.mem x (get_allocated_block_addresses g)) /\
                                      field_reads_equal g g')) =
  let allocs = get_allocated_block_addresses g in
  let g' = colorHeader3 v_id g c in
  assert (heap_remains_same_except_index_v_id v_id g g');
  assert ((Seq.mem v_id (get_allocated_block_addresses g)));
  assert (~(Seq.mem v_id (get_allocated_block_addresses g')));
  assert  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ 
                         Usize.v y >= Usize.v x + Usize.v mword /\
                         Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                                     read_word g y == read_word g' y);
  
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    getWosize(read_word g x) == getWosize(read_word g' x));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    getTag(read_word g x) == getTag(read_word g' x));
  
  ()

let colorHeader3_blue_object_colored_blue_lemma1  (v_id:hp_addr)  
                                                  (g:heap{Seq.length (objects2 0UL g) > 0}) 
                                                  (c:color)
                         : Lemma
                           (requires (c == blue) /\
                                     (mem v_id (objects2 0UL g)) /\
                                     (color_of_object1 v_id g == blue)
                                     )
                           (ensures  (let g' = colorHeader3 v_id g c in
                                      let allocs = (get_allocated_block_addresses g) in
                                      let allocs' = (get_allocated_block_addresses g') in
                                      (forall x. Seq.mem x allocs' ==>
                                                 Seq.mem x allocs) /\
                                      (forall x. Seq.mem x allocs' ==>
                                                 getWosize(read_word g x) == getWosize(read_word g' x)) /\
                                      (forall x. Seq.mem x allocs' ==>
                                                 getTag(read_word g x) == getTag(read_word g' x)) /\
                                      field_reads_equal g g')) =
  
  let allocs = get_allocated_block_addresses g in
  
  let g' = colorHeader3 v_id g c in
  assert (heap_remains_same_except_index_v_id v_id g g');
  assert (~(Seq.mem v_id (get_allocated_block_addresses g)));
  assert (~(Seq.mem v_id (get_allocated_block_addresses g')));

  (*Field reads of all allocated blocks in g' remains the same between g and g'*)
  assert  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ 
                         Usize.v y >= Usize.v x + Usize.v mword /\
                         Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                                     read_word g y == read_word g' y);
  (*assert (forall (x:Usize.t {Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). x <> v_id ==>
                  read_word g x == read_word g' x);*)

  (*The the header reads of all allocated objects in g' renains the same between g and g'*)
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                  read_word g x == read_word g' x);

  (*All allocated objects in g' is present as allocated objects in g*)
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g));
  
  ()

#reset-options "--z3rlimit 500"

#restart-solver


let allocs_reads_equal (g:heap{write_word_to_blue_object_field_lemma_props1 g /\ 
                                                   Seq.length (objects2 0UL g) > 0})
                       (x:hp_addr{first_field_of_blue g x})
                       (v:hp_addr{first_field_of_any g v})  =
 let g' = write_word g x v in
 (objects2 0UL g == objects2 0UL g') /\
  (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\
                                        (forall p. Seq.mem p (get_allocated_block_addresses g') ==> 
                                                   read_word g' p ==  read_word g p)


#restart-solver

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let write_word_to_blue_object_field_lemma3 (g:heap{write_word_to_blue_object_field_lemma_props1 g /\ 
                                                   Seq.length (objects2 0UL g) > 0})
                                           (x:hp_addr{first_field_of_blue g x})
                                           (v:hp_addr{first_field_of_any g v}) 
                          : Lemma
                            (requires True)

                             (ensures  (let g' = write_word g x v in
                                        (*(objects2 0UL g == objects2 0UL g') /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\
                                        (forall p. Seq.mem p (get_allocated_block_addresses g') ==> 
                                                   read_word g' p ==  read_word g p) /\*)
                                        allocs_reads_equal g x v /\
                                        (Seq.length (objects2 0UL g') > 0) /\
                                         field_reads_equal g g')) =
  let g' = write_word g x v in
  write_word_lemma1 g x v;
  fields_not_mem_objs_lemma g g' (hd_address x) x;

  assert(~(Seq.mem x (objects2 0UL g)));
  assert(~(Seq.mem x (get_allocated_block_addresses g)));
  write_word_to_blue_object_field_lemma g x v;

  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                    Seq.mem x (get_allocated_block_addresses g'));
  
  (*This assert ensures that, the header value remains the same between the two heaps with a field write*)
  assert (header_value_does_not_change_with_a_field_write g x v);
  
  (*assert (forall p. Seq.mem p (objects2 0UL g) ==> read_word (write_word g x v) p ==  read_word g p);

  assert (forall p. Seq.mem p (get_allocated_block_addresses g) ==> read_word (write_word g x v) p ==  read_word g p);

  assert (forall p. Seq.mem p (get_allocated_block_addresses g') ==> read_word g' p ==  read_word g p);*)
  
  (*This assert ensures that, the field reads of all non-blue objects remains the same between the two heaps*)
  assert (write_to_the_firstfield_of_blue_object_preserves_the_field_reads_of_all_non_blue_objects g x v);
  assert (allocs_reads_equal g x v);
  assert (field_reads_equal g g');
  ()

#restart-solver

#reset-options "--z3rlimit 500"


let sweep_body_with_free_list_well_formedness_parts_lemma1 
                              (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ 
                                     write_word_to_blue_object_field_lemma_props1 g})
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ 
                                                Seq.mem (hd_address f_index) (objects2 0UL g)})
                              (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                           Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                           color_of_object1 (hd_address fp) g == blue /\
                                          (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                          Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
              : Lemma
                (requires True)
                
                (ensures (let g' =  fst (sweep_body_with_free_list g f_index fp) in
                                      let allocs' = (get_allocated_block_addresses g') in
                                       (forall x. Seq.mem x allocs' ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\
                                        
                                        (forall x. Seq.mem x allocs' ==>
                                                   getWosize(read_word g' x) == getWosize(read_word g x)) /\
                                        (forall x. Seq.mem x allocs' ==>
                                                   getTag(read_word g' x) == getTag(read_word g x)) /\
                                        (Seq.length (objects2 0UL g') > 0) /\
                                         field_reads_equal g g')) =
 let h_index = hd_address f_index in
 let c = getColor (read_word g h_index) in
 
 if (c = white || c = blue) then 
 (
   let g' = colorHeader3 h_index g blue in
  if c = white then
   (
      colorHeader3_white_object_colored_blue_lemma1 h_index g blue;
      let allocs' = get_allocated_block_addresses g' in
      assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                   getWosize(read_word g x) == getWosize(read_word g' x)) /\
              (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                           getTag(read_word g x) == getTag(read_word g' x)) /\
              (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                    Seq.mem x (get_allocated_block_addresses g)) /\
              field_reads_equal g g');
      assert (Seq.length (objects2 0UL g') > 0);

      let g1 = write_word g' fp f_index in
      write_word_to_blue_object_field_lemma g' fp f_index;
      write_word_to_blue_object_field_lemma3 g' fp f_index;

      assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                                                   Seq.mem x (get_allocated_block_addresses g')) /\
                                        (forall p. Seq.mem p (get_allocated_block_addresses g1) ==> 
                                                   read_word g1 p ==  read_word g' p) /\
                                        (Seq.length (objects2 0UL g1) > 0) /\
                                         field_reads_equal g' g1);
      assert (Seq.length (objects2 0UL g1) > 0);
      assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                                                   Seq.mem x (get_allocated_block_addresses g)));
      assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                       getWosize(read_word g1 x) == getWosize(read_word g x)));
      assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                       getTag(read_word g1 x) == getTag(read_word g x)));    
      assert (field_reads_equal g g1);
      ()
   )
   else
   (
    colorHeader3_blue_object_colored_blue_lemma1 h_index g blue;
    let allocs' = get_allocated_block_addresses g' in

    assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                   getWosize(read_word g x) == getWosize(read_word g' x)) /\
              (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                           getTag(read_word g x) == getTag(read_word g' x)) /\
              (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                    Seq.mem x (get_allocated_block_addresses g)) /\
              field_reads_equal g g');

    let g1 = write_word g' fp f_index in
    write_word_to_blue_object_field_lemma g' fp  f_index;
    write_word_to_blue_object_field_lemma3 g' fp f_index;

    assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                                                   Seq.mem x (get_allocated_block_addresses g')) /\
                                        (forall p. Seq.mem p (get_allocated_block_addresses g1) ==> 
                                                   read_word g1 p ==  read_word g' p) /\
                                        (forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                                                   getWosize(read_word g1 x) == getWosize(read_word g' x)) /\
                                        (Seq.length (objects2 0UL g1) > 0) /\
                                         field_reads_equal g' g1);
    assert (Seq.length (objects2 0UL g1) > 0);
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                                                   Seq.mem x (get_allocated_block_addresses g)));
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                       getWosize(read_word g1 x) == getWosize(read_word g x)));
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g1) ==>
                       getTag(read_word g1 x) == getTag(read_word g x)));    
    assert (field_reads_equal g g1);
    ()
   )
 )
 else
 (
   assert (c == black);
   let g' = colorHeader3 h_index g white in
   colorHeader3_black_object_colored_white_lemma h_index g white;
   let allocs = (get_allocated_block_addresses g) in
   let allocs' = (get_allocated_block_addresses g') in
   assert ((forall x. Seq.mem x allocs' ==>
                              Seq.mem x allocs) /\
           (forall x. Seq.mem x allocs' ==>
                               getWosize(read_word g x) == getWosize(read_word g' x)) /\
          (forall x. Seq.mem x allocs' ==>
                                getTag(read_word g x) == getTag(read_word g' x)) /\
                                      field_reads_equal g g');
  
   assert (Seq.length (objects2 0UL g') > 0);

   assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) (*/\
          (forall p. Seq.mem p (get_allocated_block_addresses g') ==> 
                                                   read_word g' p ==  read_word g p)*) /\
          (Seq.length (objects2 0UL g') > 0) /\
           field_reads_equal g g');
   () 
 )

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let rec sweep_with_free_list3_well_formedness_part_lemma1
                              (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0)})
                             
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)/\ 
                                             (Seq.length (objects2 (hd_address f_index) g) > 0)
                              })
                             
                             (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                         color_of_object1 (hd_address fp) g == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
                         : Lemma
                           (requires ( forall p. Seq.mem p (objects2 0UL g) ==> Usize.v (getWosize (read_word g p)) > 0))
                           (ensures (let g' =  fst (sweep_with_free_list3 g f_index fp) in
                                      let allocs' = (get_allocated_block_addresses g') in
                                       (forall x. Seq.mem x allocs' ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\
                                        
                                        (forall x. Seq.mem x allocs' ==>
                                                   getWosize(read_word g' x) == getWosize(read_word g x)) /\
                                        (forall x. Seq.mem x allocs' ==>
                                                   getTag(read_word g' x) == getTag(read_word g x)) /\
                                        (Seq.length (objects2 0UL g') > 0) /\
                                         field_reads_equal g g')) 
                             (decreases (heap_size - Usize.v f_index)) =

 let h_index = hd_address f_index in
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let f_index_new =  Usize.add h_index_new mword in
 wosize_plus_one_times_mword_multiple_of_mword wz;
 assert (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0);
 //assert (Usize.v h_index_new % Usize.v mword == 0);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index_new mword;

 let g', fp' = sweep_body_with_free_list g f_index fp in
 sweep_body_with_free_list_lemma5 g f_index fp;
 
 let allocs' = get_allocated_block_addresses g' in
 sweep_body_with_free_list_well_formedness_parts_lemma1 g f_index fp;

 assert((forall x. Seq.mem x allocs' ==>
                   Seq.mem x (get_allocated_block_addresses g)) /\
        (forall x. Seq.mem x allocs' ==>
                   getWosize(read_word g' x) == getWosize(read_word g x)) /\
        (forall x. Seq.mem x allocs' ==>
                   getTag(read_word g' x) == getTag(read_word g x)) /\
        (Seq.length (objects2 0UL g') > 0) /\
        field_reads_equal g g');
 
 if Usize.v f_index_new >= heap_size then
 (
   
   objects2_cons_lemma2 h_index g;
   
   objects2_sweep_lemma3 h_index g;
   assert (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g)));
   assert (~(Seq.mem h_index_new (objects2 h_index g)));
   objects2_sweep_lemma4 h_index g;
   assert (~(Seq.mem h_index_new (objects2 h_index g)) /\ (Seq.length (objects2 (hd_address f_index) g) > 0) ==> Seq.length (objects2 h_index g) == 1);
   assert (Seq.length (objects2 h_index g) == 1);
   objects2_property_lemma g h_index;
   
   ()
  
 )
 else
 (
   objects2_mem_lemma1_app1 h_index g;
   objects2_length_lemma3 g' h_index h_index_new; 
   let g'',fp'' = sweep_with_free_list3 g' f_index_new fp' in
   sweep_with_free_list3_well_formedness_part_lemma1 g' f_index_new fp';
   
   let allocs'' = get_allocated_block_addresses g'' in
   assert((forall x. Seq.mem x allocs'' ==>
                   Seq.mem x (get_allocated_block_addresses g')) /\
        (forall x. Seq.mem x allocs'' ==>
                   getWosize(read_word g'' x) == getWosize(read_word g' x)) /\
        (forall x. Seq.mem x allocs'' ==>
                   getTag(read_word g'' x) == getTag(read_word g' x)) /\
        (Seq.length (objects2 0UL g'') > 0) /\
        field_reads_equal g' g'');
  
  assert((forall x. Seq.mem x allocs'' ==>
                   Seq.mem x (get_allocated_block_addresses g)) /\
        (forall x. Seq.mem x allocs'' ==>
                   getWosize(read_word g'' x) == getWosize(read_word g x)) /\
        (forall x. Seq.mem x allocs'' ==>
                   getTag(read_word g'' x) == getTag(read_word g x)) /\
        (Seq.length (objects2 0UL g'') > 0) /\
        field_reads_equal g g'');
   ()
)

#restart-solver




#restart-solver

#restart-solver

#restart-solver



#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#reset-options "--z3rlimit 500"

let sweep_body_with_free_list_well_formedness_parts_lemma1_pre 
                              (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ 
                                     write_word_to_blue_object_field_lemma_props1 g})
                              
                              (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                           Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                           color_of_object1 (hd_address fp) g == blue /\
                                          (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                          Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
                              (g':heap{g' == fst (sweep_body_with_free_list g mword fp)}) =
 let allocs' = (get_allocated_block_addresses g') in
                                       (forall x. Seq.mem x allocs' ==>
                                                   Seq.mem x (get_allocated_block_addresses g)) /\
                                        
                                        (forall x. Seq.mem x allocs' ==>
                                                   getWosize(read_word g' x) == getWosize(read_word g x)) /\
                                        (forall x. Seq.mem x allocs' ==>
                                                   getTag(read_word g' x) == getTag(read_word g x)) /\
                                        (Seq.length (objects2 0UL g') > 0) /\
                                         field_reads_equal g g'


#restart-solver
#restart-solver

let pre_condition_sweep (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ 
                         write_word_to_blue_object_field_lemma_props1 g}) =
let f_index = mword in
                                      let h_index = hd_address f_index in
                                      let wz =  getWosize (read_word g h_index) in
                                      let h_index_new = Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword)  in
                                      let f_index_new =  Usize.add h_index_new mword in
                                       (Usize.v f_index_new >= heap_size ==> ~(Seq.mem h_index_new (objects2 h_index g))) /\
                                       (~(Seq.mem h_index_new (objects2 h_index g)) /\ (Seq.length (objects2 (hd_address f_index) g) > 0) ==> 
                                       Seq.length (objects2 h_index g) == 1)

#reset-options "--z3rlimit 500"

let field_reads_of_allocs_of_two_heaps_are_equal  (g:heap{Seq.length (objects2 0UL g) > 0})
                                                  (g':heap{Seq.length (objects2 0UL g') > 0})
                                          
                                                  (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g')) /\
                                                                   
                                                                  (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g' x)))})=
      (forall x y. Seq.mem x f' /\ 
                   Usize.v y >= Usize.v x + Usize.v mword /\
                   Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                                     read_word g y == read_word g' y)



let sweep_with_free_list3_heap_lemma2 (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0)})
                                     (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                         color_of_object1 (hd_address fp) g == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)}) 
                         : Lemma
                           (requires True)
                           
                           (ensures(let g1,_ = sweep_with_free_list3 g mword fp in
                           
                                   (forall x. Seq.mem x (objects2 0UL g1) ==>  
                                             color_of_object1 x g1 == white \/  color_of_object1 x g1 == blue) /\
                                   (forall x. Seq.mem x (get_allocated_block_addresses g1) <==> Seq.mem x (objects2 0UL g1) /\
                                   (color_of_object1 x g1 == white)))) =
  let f_index = mword in
  let s = objects2 0UL g in
  assert (Usize.v mword >= Usize.v mword);
  let h_index = hd_address f_index in
  assert (h_index == 0UL);
  assert (Seq.mem (hd_address f_index) (objects2 0UL g));
  assert (Seq.length (objects2 (hd_address f_index) g) > 0);
  let wz =  getWosize (read_word g h_index) in
  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
  let f_index_new =  Usize.add h_index_new mword in
  let g1, fp1 = sweep_with_free_list3 g f_index fp in
  assert (noGreyObjects g1);
  assert (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                                             Seq.mem x (objects2 (hd_address f_index) g1) /\ color_of_object1 x g1 == blue);
  
  assert (forall x. Seq.mem x (objects2 (hd_address f_index) g) /\ color_of_object1 x g == black <==> 
                                             Seq.mem x (objects2 (hd_address f_index) g1) /\ color_of_object1 x g1 == white);
  
  assert (forall x. Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                                             Seq.mem x (objects2 0UL g1) /\ color_of_object1 x g1 == blue);
  
  assert (forall x. Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == black <==> 
                                             Seq.mem x (objects2 0UL g1) /\ color_of_object1 x g1 == white);
  
  
  objects2_color_lemma 0UL g;
  assert (forall x. Seq.mem x (objects2 h_index g) ==> ~(color_of_object1 x g == gray));
  assert (forall x. Seq.mem x (objects2 h_index g) ==> color_of_object1 x g == white \/ color_of_object1 x g == black \/ color_of_object1 x g == blue);
  assert (forall x. Seq.mem x (objects2 h_index g1) ==> color_of_object1 x g1 == blue \/ color_of_object1 x g1 == white);
  assert (forall x. Seq.mem x (objects2 0UL g1) ==>  color_of_object1 x g1 == white \/  color_of_object1 x g1 == blue);
  let allocs = get_allocated_block_addresses g1 in
  assert (forall x. Seq.mem x allocs <==> Seq.mem x (objects2 0UL g1) /\
                                   (color_of_object1 x g1 == white \/
                                   color_of_object1 x g1 == black \/
                                   color_of_object1 x g1 == gray));
  assert (forall x. Seq.mem x (objects2 h_index g1) ==> ~(color_of_object1 x g1 == black));

  assert (forall x. Seq.mem x allocs <==> Seq.mem x (objects2 0UL g1) /\
                                   (color_of_object1 x g1 == white));
  ()



#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let sweep_with_free_list_well_formedness_lemma_2 
                              (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ 
                                     write_word_to_blue_object_field_lemma_props1 g})
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)/\ 
                                             (Seq.length (objects2 (hd_address f_index) g) > 0)
                              })
                              (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                           Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                           color_of_object1 (hd_address fp) g == blue /\
                                          (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                          Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
              : Lemma
                (requires  (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                      is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                          (check_well_formed_closure_objs g (get_allocated_block_addresses g) == true))
                
                
                (ensures  (let g' = (fst (sweep_with_free_list3 g mword fp)) in
                            check_all_block_fields_within_limit2 g' (get_allocated_block_addresses g') /\
                            check_well_formed_closure_objs g' (get_allocated_block_addresses g'))) =


  let g' = (fst (sweep_with_free_list3 g mword fp)) in
  assert (forall x. Seq.mem x (objects2 0UL g) ==> Usize.v (getWosize (read_word g x)) > 0);
  
  sweep_with_free_list3_well_formedness_part_lemma1 g mword fp;
  assert (let allocs' = (get_allocated_block_addresses g') in
          (forall x. Seq.mem x allocs' ==>
                            Seq.mem x (get_allocated_block_addresses g)) /\
                                        
          (forall x. Seq.mem x allocs' ==>
                            getWosize(read_word g' x) == getWosize(read_word g x)) /\
          (forall x. Seq.mem x allocs' ==>
                            getTag(read_word g' x) == getTag(read_word g x)) /\
          (Seq.length (objects2 0UL g') > 0) /\
          field_reads_equal g g');
  check_well_formed_closure_objs_lemma2 g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
  assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g)) /\
        (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                   getWosize (read_word g x) == getWosize (read_word g' x)));
  assert (field_reads_of_allocs_of_two_heaps_are_equal g g' (get_allocated_block_addresses g'));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> 
                    is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
  check_all_block_fields_within_limit2_lemma_for_sweep g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> 
                    is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
  assert (check_all_block_fields_within_limit2 g' (get_allocated_block_addresses g'));
  assert (check_well_formed_closure_objs g' (get_allocated_block_addresses g'));
  ()

#restart-solver

#restart-solver

#restart-solver

(*The below lemma proves that, for all allocated objects in g2, their successors in heap g1 are members 
      of the allocated objects in g2*)

let all_allocs_objs_in_g2_successors_in_g1_mem_allocs_in_g2 
                                  (g:heap{well_formed_heap2 g /\
                                         (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)}) 
                                  (g1:heap{well_formed_heap2 g1 /\
                                         (all_field_address_are_word_aligned (get_allocated_block_addresses g1) g1)}) 
                                  (st: seq Usize.t {stack_props_func g st /\ g1 == mark5 g st})                             
                                  (root_set : seq Usize.t{root_props g root_set})
                                  (g2:heap{Seq.length (objects2 0UL g2) > 0 /\
                                           (objects2 0UL g1) == (objects2 0UL g2) /\
                                           (forall x. Seq.mem x (get_allocated_block_addresses g2) ==>
                                                 Seq.mem x (get_allocated_block_addresses g1) )})
              : Lemma
              (requires  (create_graph_from_heap g == create_graph_from_heap g1) /\
                         (forall (x:Usize.t). black_pointer g g1 st x ==> black_field_props1 g g1 st root_set x) /\
                         sweep_white_post_variant2 g1 g2 /\
                         (forall x. Seq.mem (hd_address x) (get_allocated_block_addresses g2) <==>
                                      Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2))
              
              (ensures  (forall x y. Seq.mem (hd_address y) (get_allocated_block_addresses g2) ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem (hd_address x) (get_allocated_block_addresses g2))
                                         )) =

   black_field_props1_lemma_all_ g g1 st root_set g2;
   assert (forall x y. black_pointer g g1 st y ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem (hd_address x) (get_allocated_block_addresses g2)) /\
                                       (Seq.mem (hd_address y) (objects2 0UL g2) /\ 
                                         isWhiteObject1 (hd_address y) g2));
   
   assert (forall x y. (Seq.mem (hd_address y) (objects2 0UL g2) /\ 
                                isWhiteObject1 (hd_address y) g2) ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem (hd_address x) (get_allocated_block_addresses g2))
                                         );
   
   assert (forall x y. Seq.mem (hd_address y) (get_allocated_block_addresses g2) ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem (hd_address x) (get_allocated_block_addresses g2))
                                         );
   ()



#restart-solver

let well_formed_heap2_lemma (g:heap)
           : Lemma
             (requires Seq.length (objects2 0UL g) > 0  /\
                                          (check_all_block_fields_within_limit2 g (get_allocated_block_addresses g)) /\
                                          (check_fields_points_to_blocks2 g (get_allocated_block_addresses g)) /\
                                          (check_well_formed_closure_objs g (get_allocated_block_addresses g)))
             (ensures well_formed_heap2 g) = ()


#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

let sum_obj_sizes_should_be_less_than_heap_size (g:heap{well_formed_heap2 g}) =
  
  (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)
 
 let refinements_on_free_list (g:heap{well_formed_heap2 g})
                              (fp:hp_addr) =
    Usize.v fp >= Usize.v mword /\ 
    Seq.mem (hd_address fp) (objects2 0UL g) /\ 
    color_of_object1 (hd_address fp) g == blue /\
    sum_obj_sizes_should_be_less_than_heap_size g

 let pre_conditions_necessary_for_sweep (g:heap{well_formed_heap2 g}) 
                                        (st: seq Usize.t {stack_props_func g st })
                                        (fp:hp_addr{refinements_on_free_list g fp}) =
let g1 = mark5 g st in
    (objects2 0UL g == objects2 0UL g1 /\
    (Seq.length (objects2 0UL g1) > 0) /\
    (noGreyObjects g1) /\
    color_of_object1 (hd_address fp) g1 == blue /\
    sum_obj_sizes_should_be_less_than_heap_size g1)

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

let mark5_body_graph_lemma (g:heap{well_formed_heap2 g}) 
               (st: seq Usize.t {stack_props_func g st})
                                    
           : Lemma
             (requires (~(G.is_emptySet st) /\
                          graph_creation_necessary_condition g /\
                          (
                          graph_creation_necessary_condition (snd (mark5_body g st)))))
             (ensures (create_graph_from_heap g == create_graph_from_heap (snd (mark5_body g st)))) = 

 assert (~(G.is_emptySet st));
 non_empty_set_lemma g st;
 let v_id = Seq.index st (Seq.length st - 1) in
 let s = Seq.slice st 0 (Seq.length st - 1) in
 assert (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (Usize.v v_id  >= Usize.v mword);
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
   
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Seq.mem x st);
 G.is_vertex_set_lemma3 st;
 assert (forall x. Seq.mem x s ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 let g' = colorHeader5 h_v_id g black in
 colorHeader5_lemma h_v_id g black;
 assert (g' == colorHeader1 h_v_id g black);
 assert (color_of_object1 h_v_id g' == black);
 colorHeader1_alloc_colors_lemma h_v_id g black;
   
 let f = objects2 0UL g in
 let f' = objects2 0UL g' in
 assert (f == f');
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 Seq.lemma_mem_snoc s v_id;
 assert (forall x. Seq.mem x st <==> (x == v_id) \/ Seq.mem x s);
 assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem (hd_address x) (objects2 0UL g) /\
                                                        isGrayObject1 (hd_address x) g);
 
 assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
 assert (color_of_object1 h_v_id g' == 3UL);
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (forall x. Seq.mem x s <==> Seq.mem (hd_address x) (objects2 0UL g') /\
                                                        isGrayObject1 (hd_address x) g');
 
 let wz = wosize_of_object1 h_v_id g' in
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));
 assert (Usize.v wz == Usize.v (getWosize (read_word g' h_v_id)));
 assert (well_formed_heap2 g');
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                             Seq.mem x s);
 assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size);
 assert (Usize.v h_v_id % Usize.v mword == 0);
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));

 assert (forall x. Seq.mem x st ==> Usize.v (tag_of_object1 (hd_address x) g) <> infix_tag);
 
 let tg = tag_of_object1 h_v_id g' in
 assert (Usize.v tg <> infix_tag);
 assert (check_well_formed_closure_objs g (get_allocated_block_addresses g));
 assert (stack_props_func g st);
 assert (Seq.mem v_id st);
 assert (forall x. Seq.mem x st ==> is_valid_header1 (hd_address x) g);
 assert (h_v_id == hd_address v_id);

 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;

 field_limits_allocated_blocks_lemma g';
 field_contents_within_limits_allocated_blocks_lemma g';
 fieldaddress_within_limits_lemma_x_all1 g';

 create_graph_from_heap_lemma g h_v_id black;
 
 let grph1 = create_graph_from_heap g in
 let grph2 = create_graph_from_heap g' in
 assert (grph1 == grph2);

if (Usize.v tg < no_scan_tag) then
  (
    let st1, g1 = darken_wrapper g' s h_v_id wz in
    assert (well_formed_heap2 g1);
    field_limits_allocated_blocks_lemma g1;
    field_contents_within_limits_allocated_blocks_lemma g1;
    fieldaddress_within_limits_lemma_x_all1 g1;
    
    darken_wrapper_lemma g' s h_v_id wz;
    

    assert (g1 == snd (mark5_body g st));
    let grph3 = create_graph_from_heap g1 in
    assert (grph3 == grph2);
    assert (grph3 == grph1);
    assert (create_graph_from_heap g == create_graph_from_heap (snd (mark5_body g st)));
    ()
  )
  else
  (
    assert (grph2 == grph1);
    assert (create_graph_from_heap g == create_graph_from_heap (snd (mark5_body g st)));
    ()
  )



 

#reset-options "--z3rlimit 500"


let st_vl_subset_of_ff_allocs (g:heap{well_formed_heap2 g /\
                                      graph_creation_necessary_condition g}) 
                              (st: seq Usize.t {stack_props_func g st})
                              (vl: seq Usize.t {vl_props_func g vl})  =

                              (
                                let allocs_g = get_allocated_block_addresses g in
                                let ff_address_g = first_field_addresses_of_allocated_blocks g allocs_g in
                                 (G.subset_vertices st ff_address_g) /\
                                 (G.subset_vertices vl ff_address_g))



let rec mark5_graph_lemma (g:heap{well_formed_heap2 g}) 
                          (st: seq Usize.t {stack_props_func g st })
           : Lemma
            (requires (graph_creation_necessary_condition g /\
                       graph_creation_necessary_condition (mark5 g st)))
            (ensures (create_graph_from_heap g == create_graph_from_heap (mark5 g st)))
            (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
  if (G.is_emptySet st) then
   (
      ()
   )
 else
   (
     let st', g' = mark5_body g st in

     field_limits_allocated_blocks_lemma g';
     field_contents_within_limits_allocated_blocks_lemma g';
     fieldaddress_within_limits_lemma_x_all1 g';
     mark5_body_graph_lemma g st;

     let grph1 = create_graph_from_heap g in
     let grph2 = create_graph_from_heap g' in
     assert (grph1 == grph2);

     let v_id = Seq.index st (Seq.length st - 1) in
     assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
     assert (is_valid_header (hd_address v_id) g);
     stack_slice_only_has_gray_color_lemma g st v_id 3UL;
     assert (forall x. Seq.mem (hd_address x) (objects2 0UL  (colorHeader1 (hd_address v_id) g 3UL)) /\
                                                  isGrayObject1 (hd_address x) (colorHeader1 (hd_address v_id) g 3UL)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)));
      
     mark5_body_black_nodes_lemma g st;
     assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
     
     assert (well_formed_heap2 g');
     assert ((forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g') /\
                                                            (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0) /\
                                                            (G.is_vertex_set st') /\
                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                                   Seq.mem x st'));
     
     let g1 = mark5 g' st' in
     mark5_graph_lemma g' st';

     let grph3 = create_graph_from_heap g1 in
     assert (grph2 == grph3);
     assert (grph1 == grph3);
     ()
   )

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

(*The below lemma proves that, the white objects are the only vertices in the graph formed after sweep*)
(*An earlier lemma proves that, from the graph formed from the heap before GC, only the white objects in the heap
  after sweep is reachable from the root_set (all_whites_objects_are_reachable_from_the_root_set). *)
let graph_vertices_after_sweep_lemma (g:heap{well_formed_heap2 g}) 
                                     (st: seq Usize.t {stack_props_func g st })
                                     (vl: seq Usize.t {vl_props_func g vl}) 
                                     (root_set : seq Usize.t{root_props g root_set})

                                     (c:color{c == 3UL})
                                     (c1:color{c1 == 2UL})
                                     (fp:hp_addr{refinements_on_free_list g fp})
                              
              : Lemma
                (requires (graph_creation_necessary_condition g /\
                          st_vl_root_set_subset_of_ff_allocs g st vl root_set /\
                          mutual_exclusivity_of_st_vl g st vl /\
                          pre_conditions_for_dfs_lemma_invoke g st vl root_set /\
                          
                          pre_conditions_necessary_for_sweep g st fp /\
                          (well_formed_heap2 (fst (sweep_with_free_list3 (mark5 g st) mword fp))) /\
                           graph_creation_necessary_condition (fst (sweep_with_free_list3 (mark5 g st) mword fp))))
                
                (ensures (let g1 = mark5 g st in
                          let g2, _ =  sweep_with_free_list3 g1 mword fp in
                          let grph_sweep = create_graph_from_heap g2 in
                          let allocs_sweep = get_allocated_block_addresses g2 in
                          (forall x. Seq.mem x ((grph_sweep).vertices) <==>
                                     Seq.mem (hd_address x) allocs_sweep) /\
                          (forall x. Seq.mem x ((grph_sweep).vertices) <==>
                                     Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2))) =
  
  let g1 = mark5 g st in
  let g2, _ =  sweep_with_free_list3 g1 mword fp in
  let grph_sweep = create_graph_from_heap g2 in
  let allocs_sweep = get_allocated_block_addresses g2 in
  let ff_allocs_sweep = first_field_addresses_of_allocated_blocks g2 allocs_sweep in
  let graph_sweep_vertices = grph_sweep.vertices in
  assert (Seq.equal graph_sweep_vertices ff_allocs_sweep);
  assert (forall x. Seq.mem x ff_allocs_sweep ==> Seq.mem (hd_address x) allocs_sweep);
  assert (forall x. Seq.mem x ff_allocs_sweep <==> Seq.mem (hd_address x) allocs_sweep);
  assert (forall x. Seq.mem x graph_sweep_vertices <==> Seq.mem (hd_address x) allocs_sweep);
  
  sweep_with_free_list3_heap_lemma2 g1 fp; 
  
  assert (forall x. Seq.mem (hd_address x) allocs_sweep <==>
                                      Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2);
  
  assert (forall x. Seq.mem x graph_sweep_vertices <==>
                    Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2);
  ()

#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

#reset-options "--z3rlimit 1000"

#push-options "--split_queries always"

(*This post-condition should be proved from sweep*)
let field_reads_hd_equal_cond (g:heap{Seq.length (objects2 0UL g) > 0}) 
                              (g':heap{Seq.length (objects2 0UL g') > 0}) =
  
  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                 is_hp_addr (read_word g' y) /\ (isPointer y g') ==> 
                 is_hp_addr (read_word g y) /\
                 Usize.v (read_word g y) >= Usize.v mword /\
                 Usize.v (read_word g' y) >= Usize.v mword /\
                 is_hp_addr (hd_address (read_word g y)) /\
                 is_hp_addr (hd_address (read_word g' y))) /\
  
  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                is_hp_addr (read_word g' y) /\ (isPointer y g') ==> 
                                                                    tag_of_object1 (hd_address (read_word g y)) g ==  tag_of_object1 (hd_address (read_word g' y)) g' /\
      
      
                                                                    wosize_of_object1 (hd_address (read_word g y)) g == wosize_of_object1 (hd_address (read_word g' y)) g')

#restart-solver


#reset-options "--z3rlimit 2000 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver


(*The below lemma proves that, forall allocated objects of the heap after sweep, the graph successors in the heap before GC are members
  of the allocated objects of the heap after sweep
  
  We have already proved that the field pointers of all allocated objects before and after the sweep remains the same*)
let mark_and_sweep_lemma3 (g:heap{well_formed_heap2 g}) 
                          (st: seq Usize.t {stack_props_func g st })
                          (vl: seq Usize.t {vl_props_func g vl}) 
                          (root_set : seq Usize.t{root_props g root_set})

                          (c:color{c == 3UL})
                          (c1:color{c1 == 2UL})
                          (fp:hp_addr{refinements_on_free_list g fp})
                              
              : Lemma
                (requires (graph_creation_necessary_condition g /\
                          st_vl_root_set_subset_of_ff_allocs g st vl root_set /\
                          mutual_exclusivity_of_st_vl g st vl /\
                          pre_conditions_for_dfs_lemma_invoke g st vl root_set /\
                          
                          pre_conditions_necessary_for_sweep g st fp /\
                          graph_creation_necessary_condition (mark5 g st)))

                (ensures  (  let g1 = mark5 g st in
                             let g2, _ =  sweep_with_free_list3 g1 mword fp in
                             (forall x y. Seq.mem (hd_address y) (get_allocated_block_addresses g2) ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem (hd_address x) (get_allocated_block_addresses g2))
                                         ))) =
  let g1 = mark5 g st in
  assert (well_formed_heap2 g1);
  assert (Seq.length (objects2 0UL g1) > 0);
  field_limits_allocated_blocks_lemma g1;
  field_contents_within_limits_allocated_blocks_lemma g1;

  assert (forall x. Seq.mem x (get_allocated_block_addresses g1) ==> 
               is_fields_within_limit1 x (getWosize (read_word g1 x)));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g1) ==> 
               is_fields_contents_within_limit2 x (getWosize (read_word g1 x)) g1);
  fieldaddress_within_limits_lemma_x_all1 g1;
  mark7_no_grey_nodes_lemma g st;
  mark7_mark5_lemma g st;
  assert (noGreyObjects g1);
  assert (graph_creation_necessary_condition g /\
          graph_creation_necessary_condition (mark5 g st));
  mark5_graph_lemma g st;
  let grph = create_graph_from_heap g in
  let grph1 = create_graph_from_heap g1 in
  assert (grph == grph1);
  field_ptrs_black_all g g1 st vl root_set c c1;
  assert (forall (x:Usize.t). black_pointer g g1 st x ==> black_field_props1 g g1 st root_set x);
  assert (hd_address mword == 0UL);
  assert (Usize.v mword >= Usize.v mword /\ Seq.mem 0UL (objects2 0UL g1)/\ 
                                             (Seq.length (objects2 0UL g1) > 0));
  
  assert (Usize.v fp >= Usize.v mword /\ 
          Seq.mem (hd_address fp) (objects2 0UL g) /\ 
          color_of_object1 (hd_address fp) g == blue /\
          (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
          Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size));
  
  
  assert (objects2 0UL g == objects2 0UL g1);

  
  assert (color_of_object1 (hd_address fp) g1 == blue);
 
  assert (Usize.v fp >= Usize.v mword /\ 
          Seq.mem (hd_address fp) (objects2 0UL g1) /\ 
          color_of_object1 (hd_address fp) g1 == blue /\
          (forall x y. Seq.mem x (objects2 0UL g1) /\ Seq.mem y (objects2 0UL g1) ==>
          Usize.v (getWosize (read_word g1 x)) + Usize.v (getWosize (read_word g1 y)) < heap_size));
  
  let g2, _ = sweep_with_free_list3 g1 mword fp in

  assert (objects2 0UL g1 == objects2 0UL g2);

  assert (well_formed_heap2 g1);

  assert (Seq.length (objects2 0UL g1) > 0);

  sweep_with_free_list_well_formedness_lemma_2 g1 mword fp;
  
  assert (check_all_block_fields_within_limit2 g2 (get_allocated_block_addresses g2) /\
          check_well_formed_closure_objs g2 (get_allocated_block_addresses g2));
  
  sweep_with_free_list3_well_formedness_part_lemma1 g1 mword fp; 

  sweep_with_free_list3_heap_lemma2 g1 fp; 

  assert (forall x. Seq.mem x (get_allocated_block_addresses g2) <==> Seq.mem x (objects2 0UL g2) /\
                                   (color_of_object1 x g2 == white));

  assert (forall x. Seq.mem (hd_address x) (get_allocated_block_addresses g2) <==>
                                      Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2);

  assert (sweep_white_post_variant2 g1 g2);
  
  assert  (forall x. Seq.mem x (get_allocated_block_addresses g2) ==>
                                                 Seq.mem x (get_allocated_block_addresses g1));

  assert ((create_graph_from_heap g == create_graph_from_heap g1) /\
                         (forall (x:Usize.t). black_pointer g g1 st x ==> black_field_props1 g g1 st root_set x) /\
                         sweep_white_post_variant2 g1 g2 /\
                         (forall x. Seq.mem (hd_address x) (get_allocated_block_addresses g2) <==>
                                      Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2));

  all_allocs_objs_in_g2_successors_in_g1_mem_allocs_in_g2 g g1 st root_set g2;

  assert (forall x y. Seq.mem (hd_address y) (get_allocated_block_addresses g2) ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem (hd_address x) (get_allocated_block_addresses g2))
                                         );


()


#restart-solver

#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let  graph_successors_heap_create_successor_list_equivalence_post (g: heap {well_formed_heap2 g /\ graph_creation_necessary_condition g})
                                                                  (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g /\
                                                                                     (succ_props_pre g h_index)
                                                                                     }) =
    (  let tg = tag_of_object1 h_index g in
       let f_id = f_address h_index in
       let grph = create_graph_from_heap g in
       let grph_succ_h_index = G.successors grph f_id in
       let wz = wosize_of_object1 h_index g in
        (Usize.v tg < no_scan_tag /\ Usize.v tg = closure_tag ==>
        (let start_of_env = start_env_clos_info g f_id in
        let start_of_env_plus_one = Usize.add start_of_env 1UL in
          (grph_succ_h_index ==  
               create_successors_list_for_h_index g h_index wz start_of_env_plus_one))) \/
        (Usize.v tg < no_scan_tag /\ Usize.v tg <> closure_tag ==>
          (grph_succ_h_index == 
                create_successors_list_for_h_index g h_index wz 1UL)) \/
        (Usize.v tg > no_scan_tag ==>
          (grph_succ_h_index ==                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        
                Seq.empty #UInt64.t)))  


let graph_successors_heap_create_successor_list_equivalence_lemma_invoke (g: heap {well_formed_heap2 g})
                                                                         (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header1 h_index g}) 
                                                          : Lemma
                                                            (requires (succ_props_pre g h_index) /\
                                                                       graph_creation_necessary_condition g)
                                                            (ensures graph_successors_heap_create_successor_list_equivalence_post g h_index)=
  
  graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
  assert (succ_props g h_index);
  let tg = tag_of_object1 h_index g in
  let wz = wosize_of_object1 h_index g in
  let f_id = f_address h_index in
  let grph = create_graph_from_heap g in
  let grph_succ_h_index = G.successors grph f_id in
  if Usize.v tg < no_scan_tag then
  (
    if Usize.v tg = closure_tag then
    (
      assert (Usize.v f_id >= Usize.v mword);
      assert (is_hp_addr f_id);
      assert (Usize.v tg == closure_tag);
      assert (Usize.v wz >= 2);
      assert (is_fields_within_limit1 h_index wz);
     
      let start_of_env = start_env_clos_info g f_id in
      let start_of_env_plus_one = Usize.add start_of_env 1UL in
      assert (grph_succ_h_index ==  
                      create_successors_list_for_h_index g h_index wz start_of_env_plus_one);
      
      assert ( (Usize.v tg < no_scan_tag /\ Usize.v tg = closure_tag ==>
                    (grph_succ_h_index ==  
                      create_successors_list_for_h_index g h_index wz start_of_env_plus_one)) \/
                (Usize.v tg < no_scan_tag /\ Usize.v tg <> closure_tag ==>
                    (grph_succ_h_index == 
                      create_successors_list_for_h_index g h_index wz 1UL)) \/
                (Usize.v tg > no_scan_tag ==>
                    (grph_succ_h_index ==  
                       Seq.empty #UInt64.t)));
      assert ( (Usize.v tg < no_scan_tag /\ Usize.v tg = closure_tag ==>
                    (let start_of_env = start_env_clos_info g f_id in
                     let start_of_env_plus_one = Usize.add start_of_env 1UL in
                       (grph_succ_h_index ==  
                         create_successors_list_for_h_index g h_index wz start_of_env_plus_one))) \/
                (Usize.v tg < no_scan_tag /\ Usize.v tg <> closure_tag ==>
                    (grph_succ_h_index == 
                      create_successors_list_for_h_index g h_index wz 1UL)) \/
                (Usize.v tg > no_scan_tag ==>
                    (grph_succ_h_index ==  
                       Seq.empty #UInt64.t)));
      ()
    )
    else
     (
      assert (grph_succ_h_index == 
                      create_successors_list_for_h_index g h_index wz 1UL);
      assert ( (Usize.v tg < no_scan_tag /\ Usize.v tg = closure_tag ==>
                    (let start_of_env = start_env_clos_info g f_id in
                     let start_of_env_plus_one = Usize.add start_of_env 1UL in
                       (grph_succ_h_index ==  
                         create_successors_list_for_h_index g h_index wz start_of_env_plus_one))) \/
                (Usize.v tg < no_scan_tag /\ Usize.v tg <> closure_tag ==>
                    (grph_succ_h_index == 
                      create_successors_list_for_h_index g h_index wz 1UL)) \/
                (Usize.v tg > no_scan_tag ==>
                    (grph_succ_h_index ==  
                       Seq.empty #UInt64.t)));
      
       
      ()
     )
  )
  else
  (
    assert (grph_succ_h_index == Seq.empty #UInt64.t);
    
    assert ( (Usize.v tg < no_scan_tag /\ Usize.v tg = closure_tag ==>
                    (let start_of_env = start_env_clos_info g f_id in
                     let start_of_env_plus_one = Usize.add start_of_env 1UL in
                       (grph_succ_h_index ==  
                         create_successors_list_for_h_index g h_index wz start_of_env_plus_one))) \/
                (Usize.v tg < no_scan_tag /\ Usize.v tg <> closure_tag ==>
                    (grph_succ_h_index == 
                      create_successors_list_for_h_index g h_index wz 1UL)) \/
                (Usize.v tg > no_scan_tag ==>
                    (grph_succ_h_index ==  
                       Seq.empty #UInt64.t)));
    ()
  )

#restart-solver

let graph_successors_heap_create_successor_list_equivalence_lemma_all (g: heap {well_formed_heap2 g})
                                                                     
                                : Lemma
                                  (requires (forall x. is_valid_header1 x g ==>  succ_props_pre g x))
                                  
                                  (ensures  ((forall x. is_valid_header1 x g ==> succ_props g x))) =
  Classical.forall_intro (Classical.move_requires (graph_successors_heap_create_successor_list_equivalence_lemma g))
                            

let write_word_to_blue_object_field_lemma1 (g:heap(*{well_formed_heap2 g}*){write_word_to_blue_object_field_lemma_props1 g /\ Seq.length (objects2 0UL g) > 0})
                                          (x:hp_addr{first_field_of_blue g x})
                                          (v:hp_addr{first_field_of_any g v})
                          : Lemma
                            (ensures True) =
  let g' = write_word g x v in
  write_word_to_blue_object_field_lemma g x v;
  admit()

#reset-options "--z3rlimit 500"

let field_mem_props_pre1 (g:heap{Seq.length (objects2 0UL g) > 0}) =
  (forall x y. Seq.mem x (get_allocated_block_addresses g) /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                 is_hp_addr (read_word g y) /\ (isPointer y g) ==> 
                 is_hp_addr (read_word g y) /\
                 Usize.v (read_word g y) >= Usize.v mword /\
                 is_hp_addr (hd_address (read_word g y)))
                 
let allocs_subset_g_g' (g:heap{Seq.length (objects2 0UL g) > 0}) 
                       (g':heap{Seq.length (objects2 0UL g') > 0}) =
  (forall x. Seq.mem x (get_allocated_block_addresses g')  ==> Seq.mem x (get_allocated_block_addresses g)) /\
  (forall x. Seq.mem x (get_allocated_block_addresses g')  ==> field_reads_equal g g')


let field_mem_props_pre (g:heap{Seq.length (objects2 0UL g) > 0}) 
                          (g':heap{Seq.length (objects2 0UL g') > 0}) =
  
  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                 is_hp_addr (read_word g' y) /\ (isPointer y g') ==> 
                 is_hp_addr (read_word g y) /\
                 Usize.v (read_word g y) >= Usize.v mword /\
                 Usize.v (read_word g' y) >= Usize.v mword /\
                 is_hp_addr (hd_address (read_word g y)) /\
                 is_hp_addr (hd_address (read_word g' y)))

let field_mem_props1 (g:heap{Seq.length (objects2 0UL g) > 0}) 
                    (g':heap{Seq.length (objects2 0UL g') > 0 /\ field_mem_props_pre g g'}) =
  
  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) /\
                is_hp_addr (read_word g' y) /\ (isPointer y g') ==>
                
                 (Usize.v (tag_of_object1 (hd_address (read_word g' y)) g') <> infix_tag ==>
                    (Seq.mem (hd_address (read_word g' y)) (get_allocated_block_addresses g')))) /\

  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) /\
                is_hp_addr (read_word g' y) /\ (isPointer y g') ==>  
                (Usize.v (tag_of_object1 (hd_address (read_word g' y)) g') == infix_tag ==> 
                 UInt.fits (Usize.v (read_word g' y) - 
                                                   (Usize.v (wosize_of_object1 (hd_address (read_word g' y)) g') * Usize.v mword)) Usize.n /\
                 (let actual_succ = (Usize.sub (read_word g' y) 
                                        (Usize.mul (wosize_of_object1 (hd_address (read_word g' y)) g') mword)) in
                   Usize.v actual_succ >= Usize.v mword /\
                   (is_hp_addr actual_succ) /\
                   (Usize.v (tag_of_object1 (hd_address actual_succ) g') == closure_tag) /\
                   Seq.mem (hd_address actual_succ) (get_allocated_block_addresses g'))))

let allocs_subset (g:heap{Seq.length (objects2 0UL g) > 0}) 
                  (g':heap{Seq.length (objects2 0UL g') > 0}) =
 let allocs = (get_allocated_block_addresses g) in
 let allocs' = (get_allocated_block_addresses g') in
  (forall x. Seq.mem x allocs' ==>
             Seq.mem x allocs)

let allocs_wosize_tag_reads_equal (g:heap{Seq.length (objects2 0UL g) > 0}) 
                                  (g':heap{Seq.length (objects2 0UL g') > 0}) =
 let allocs = (get_allocated_block_addresses g) in
 let allocs' = (get_allocated_block_addresses g') in
  (forall x. Seq.mem x allocs' ==>
              getWosize(read_word g x) == getWosize(read_word g' x)) /\
  (forall x. Seq.mem x allocs' ==>
              getTag(read_word g x) == getTag(read_word g' x))

 let fields_within_limit_allocs (g:heap{Seq.length (objects2 0UL g) > 0}) =
 (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
        is_fields_within_limit1 x (getWosize (read_word g x)))

let field_reads_hd_equal1 (g:heap{Seq.length (objects2 0UL g) > 0}) 
                          (g':heap{Seq.length (objects2 0UL g') > 0}) =
  
  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                 is_hp_addr (read_word g' y) /\ (isPointer y g') ==> 
                 is_hp_addr (read_word g y) /\
                 Usize.v (read_word g y) >= Usize.v mword /\
                 Usize.v (read_word g' y) >= Usize.v mword /\
                 is_hp_addr (hd_address (read_word g y)) /\
                 is_hp_addr (hd_address (read_word g' y))) /\
  
  (forall x y. Seq.mem x (get_allocated_block_addresses g') /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                is_hp_addr (read_word g' y) /\ (isPointer y g') ==> 
                                                                    tag_of_object1 (hd_address (read_word g y)) g ==  tag_of_object1 (hd_address (read_word g' y)) g' /\
                                                                    wosize_of_object1 (hd_address (read_word g y)) g == wosize_of_object1 (hd_address (read_word g' y)) g')

#restart-solver

#restart-solver
(* hd_address (read_word g y) <> fp (address of the free list pointer = ), 
    y - field address of a location of an allocated object after heap, 
    where a pointer value is stored

    sw
    -----------------------------
    -----------------------------
    for every object in the object set,

     1. sweep body will not change the tg or wz of the header of that object.
     2. 
    
    iirespective of an object being infix or non infix, can we show that the sweep body does not change the tag and the wosize.
    

    infix object does not belong to object set. So sweep never encounters an infix object.

    o1 ----> o2 ; tag (header o2 in g) == tag (header o2 in g')
                  wz (header o2 in g) == wz (header o2 in g')

    proved - sweep does not change tag or wz of objects (does not include non-infix)

    This is true for non-infix.

    Now prove for infix

    Before the sweep, a non-infix object is a non-infix object.

    contradicts - sweep does not change a non-infix object to an infix object.

    let tg = tag_of_object1 hdr_succ g' in
    let tg1 = tag_of_object1 hdr_succ g in
    
    Property proved - (1) sweep does not change tg of object set object and object g == objectt g' (proved both)
    
    tg == infix 
    tg1 == tg (Since sweep does not change a non-infix to infix. (property 1)
    Another lemma should say, sweep does not encounter infix objects. This is needed for wz of infix objects.
    sweep will encounter every object in the object set. Sweep will not encounter an infix object
    Hence sweep will not change the wz of an infix object.
    
    tg == non-infix, then
    tg1 == tg (property 1)                
    

    The first field of a free list 

    First field cannot be another objects header, includes infix. (this is not defined yet.)


    *)

let is_fields_points_to_blocks2_lemma_for_sweep1  (h_index: hp_addr) 
                                                     (g:heap{Seq.length (objects2 0UL g) > 0}) 
                                                     (g':heap{Seq.length (objects2 0UL g') > 0}) 
                                                     (wz1: wosize{(is_fields_within_limit1 h_index wz1 /\
                                                                   is_fields_contents_within_limit2 h_index wz1 g')}) 
                                                     
                                                     (wz: wosize{(is_fields_within_limit1 h_index wz /\
                                                                    is_fields_contents_within_limit2 h_index wz g)})
                               : Lemma
                                  (requires 
                                            (*(wz1 == getWosize (read_word g' h_index)) /\*)
                                             allocs_subset g g' /\
                                             
                                             
                                             (wz == wz1) /\
                                             (Usize.v wz1 >= 0) /\
                                             (Usize.v wz1 <= Usize.v (getWosize(read_word g' h_index))) /\
                                             (Usize.v wz <= Usize.v (getWosize(read_word g h_index))) /\
                                             allocs_wosize_tag_reads_equal g g' /\
                                             fields_within_limit_allocs g /\
                                             check_all_block_fields_within_limit2 g (get_allocated_block_addresses g) /\
                                             check_fields_points_to_blocks2 g (get_allocated_block_addresses g) /\
                                             check_well_formed_closure_objs g (get_allocated_block_addresses g) /\
 
                                            (Seq.mem h_index (get_allocated_block_addresses g')) /\

                                            field_reads_equal g g' /\
                                            field_reads_hd_equal1 g g' /\

                                            is_fields_points_to_blocks2 h_index g wz
                                                                        (get_allocated_block_addresses g) /\
                                            field_mem_props1 g g'
                                          )
                                  (ensures is_fields_points_to_blocks2 h_index g' wz1 
                                                       (get_allocated_block_addresses g') == true
                                            ) = ()

#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let mark_and_sweep_lemma5 (g:heap{well_formed_heap2 g}) 
                          (st: seq Usize.t {stack_props_func g st })
                          (vl: seq Usize.t {vl_props_func g vl}) 
                          (root_set : seq Usize.t{root_props g root_set})

                          (c:color{c == 3UL})
                          (c1:color{c1 == 2UL})
                          (fp:hp_addr{refinements_on_free_list g fp})
                              
              : Lemma
                (requires (graph_creation_necessary_condition g /\
                          st_vl_root_set_subset_of_ff_allocs g st vl root_set /\
                          mutual_exclusivity_of_st_vl g st vl /\
                          pre_conditions_for_dfs_lemma_invoke g st vl root_set /\
                          
                          pre_conditions_necessary_for_sweep g st fp /\
                          graph_creation_necessary_condition (mark5 g st)))

                (ensures  ( let g1 = mark5 g st in
                            well_formed_heap2 (fst (sweep_with_free_list3 g1 mword fp)))) = 
mark_and_sweep_lemma3 g st vl root_set c c1 fp;
let g1 = mark5 g st in
  assert (well_formed_heap2 g1);
  assert (Seq.length (objects2 0UL g1) > 0);
  field_limits_allocated_blocks_lemma g1;
  field_contents_within_limits_allocated_blocks_lemma g1;

  assert (forall x. Seq.mem x (get_allocated_block_addresses g1) ==> 
               is_fields_within_limit1 x (getWosize (read_word g1 x)));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g1) ==> 
               is_fields_contents_within_limit2 x (getWosize (read_word g1 x)) g1);
  fieldaddress_within_limits_lemma_x_all1 g1;
  
  assert (Usize.v fp >= Usize.v mword /\ 
          Seq.mem (hd_address fp) (objects2 0UL g1) /\ 
          color_of_object1 (hd_address fp) g1 == blue /\
          (forall x y. Seq.mem x (objects2 0UL g1) /\ Seq.mem y (objects2 0UL g1) ==>
          Usize.v (getWosize (read_word g1 x)) + Usize.v (getWosize (read_word g1 y)) < heap_size));
  
  let g2, _ = sweep_with_free_list3 g1 mword fp in

  assert (objects2 0UL g1 == objects2 0UL g2);

  assert (well_formed_heap2 g1);

  assert (Seq.length (objects2 0UL g1) > 0);

  sweep_with_free_list_well_formedness_lemma_2 g1 mword fp;
  
  assert (check_all_block_fields_within_limit2 g2 (get_allocated_block_addresses g2) /\
          check_well_formed_closure_objs g2 (get_allocated_block_addresses g2));
  
  sweep_with_free_list3_well_formedness_part_lemma1 g1 mword fp; 

  sweep_with_free_list3_heap_lemma2 g1 fp; 

  (*From, mark_and_sweep_lemma3, 
    assert let g1 = mark5 g st in
                             let g2, _ =  sweep_with_free_list3 g1 mword fp in
                             (forall x y. Seq.mem (hd_address y) (get_allocated_block_addresses g2) ==>  
                                      (Seq.mem x (G.successors (create_graph_from_heap g1) y) ==> 
                                       Seq.mem (hd_address x) (get_allocated_block_addresses g2))
                                         )
    Earlier proved that (G.successors (create_graph_from_heap g1) y == create_successors_list_for_h_index g h_index wz (field_scan start index)
    (1)Create a wrapper lemma to bring this condition into context.

    For the three branches according to, > no_scan, <no_scan and non-closure, >no_scan and closure,
     prove that,
      (forall x y. Seq.mem x (get_allocated_block_addresses g1) /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g1 x)) * Usize.v mword) /\
                is_hp_addr (read_word g1 y) /\ (isPointer y g1) ==>
                
                 (Usize.v (tag_of_object1 (hd_address (read_word g1 y)) g1) <> infix_tag ==>
                    (Seq.mem ((read_word g1 y)) (create_successors_list_for_h_index g1 x wz (field_scan start index))))) /\

  (forall x y. Seq.mem x (get_allocated_block_addresses g1) /\ 
                Usize.v y >= Usize.v x + Usize.v mword /\
                Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g1 x)) * Usize.v mword) /\
                is_hp_addr (read_word g1 y) /\ (isPointer y g1) ==>  
                (Usize.v (tag_of_object1 (hd_address (read_word g1 y)) g1) == infix_tag ==> 
                 UInt.fits (Usize.v (read_word g1 y) - 
                                                   (Usize.v (wosize_of_object1 (hd_address (read_word g1 y)) g1) * Usize.v mword)) Usize.n /\
                 (let actual_succ = (Usize.sub (read_word g1 y) 
                                        (Usize.mul (wosize_of_object1 (hd_address (read_word g1 y)) g1) mword)) in
                   Usize.v actual_succ >= Usize.v mword /\
                   (is_hp_addr actual_succ) /\
                   (Usize.v (tag_of_object1 (hd_address actual_succ) g1) == closure_tag) /\
                   Seq.mem (actual_succ) (create_successors_list_for_h_index g1 x wz (field_scan start index)))))
  
  (2)Prove, field_reads_hd_equal1 g1 g2.

  (3)Then, we can replace g2 in place of g1 in checks like is_hp_addr (read_word g1 y) /\ (isPointer y g1) ==> (Usize.v (tag_of_object1 (hd_address (read_word g1 y)) g1)

  (4)Since the above are members of create_successors_list_for_h_index, from mark_and_sweep_lemma3 post condition, we know that all such successors are mem (get_allocated_block_addresses g2),

  therefore, we can replace (get_allocated_block_addresses g2) in place of create_successors_list_for_h_index in the above condition. Which is the pre-condition required to invoke, 

  is_fields_points_to_blocks2_lemma_for_sweep1 for all allocated objects of g2.
 
  (5)A wrapper lemma need to be created to call is_fields_points_to_blocks2_lemma_for_sweep1 for all allocated objects. This will prove the below assume.
        *)
  assume (forall x. Seq.mem x (get_allocated_block_addresses g2) ==>
                              is_fields_points_to_blocks2 x g2 (getWosize (read_word g2 x)) (get_allocated_block_addresses g2));

  assert (well_formed_heap2 g2);
  ()

#restart-solver

#restart-solver

#restart-solver

#restart-solver
#restart-solver

#restart-solver

let sweep_props_black_to_white (g1:heap)
                               (g2: heap )=
 (forall x. Seq.mem x (objects2 (hd_address mword) g1) /\ color_of_object1 x g1 == black <==> 
           Seq.mem x (objects2 (hd_address mword) g2) /\ color_of_object1 x g2 == white)


let sweep_props_black_to_white1 (g1:heap)
                                (g2: heap)=
 (forall x. Seq.mem x (objects2 0UL g1) /\ color_of_object1 x g1 == black <==> 
                    Seq.mem x (objects2 0UL g2) /\ color_of_object1 x g2 == white)

let sweep_props_black_to_white2 (g1:heap)
                                (g2: heap) =
 
 (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ color_of_object1 (hd_address x) g1 == black <==> 
                    Seq.mem (hd_address x) (objects2 0UL g2) /\ color_of_object1 (hd_address x) g2 == white)


 let sweep_props_black_to_white3 (g1:heap)
                                (g2: heap) =
 
  (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==> 
                    Seq.mem (hd_address x) (objects2 0UL g2) /\ isWhiteObject1 (hd_address x) g2)



let sub_graph_vertices_after_sweep_reachable_lemma1 (g:heap{well_formed_heap2 g}) 
                                               (st: seq Usize.t {stack_props_func g st})
                                               (vl: seq Usize.t {vl_props_func g vl}) 
                                               (root_set : seq Usize.t{root_props g root_set})
 
                                               (c:color{c == 3UL})
                                               (c1:color{c1 == 2UL})
                                               (fp:hp_addr{refinements_on_free_list g fp})
                                
                 : Lemma
                   (requires  graph_creation_necessary_condition g /\
                              
                              st_vl_root_set_subset_of_ff_allocs g st vl root_set /\ 

                              mutual_exclusivity_of_st_vl g st vl /\
                              
                              pre_conditions_for_dfs_lemma_invoke g st vl root_set /\
                              
                              pre_conditions_necessary_for_sweep g st fp /\
                             
                             (well_formed_heap2 (fst (sweep_with_free_list3 (mark5 g st) mword fp))) /\
                             
                             graph_creation_necessary_condition (fst (sweep_with_free_list3 (mark5 g st) mword fp))) 
                   
                   (ensures (let g1 = mark5 g st in
                             let g2, _ =  sweep_with_free_list3 g1 mword fp in
                             let grph = create_graph_from_heap g in 
                             let grph_sweep = create_graph_from_heap g2 in
                             let allocs_sweep = get_allocated_block_addresses g2 in
                             (forall x. Seq.mem x ((grph_sweep).vertices) <==>
                                  (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                              G.reachfunc grph o x z1)))) =
  let grph = create_graph_from_heap g in 
  let g1 = mark5 g st in
  all_black_objs_after_mark_is_reachable g st vl root_set c c1;
  (*assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==>
                                (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                              G.reachfunc grph o x z1));*)
  
  
  let g2, _ = sweep_with_free_list3 g1 mword fp in
  (*assert (forall x. Seq.mem x (objects2 (hd_address mword) g1) /\ color_of_object1 x g1 == black <==> 
                    Seq.mem x (objects2 (hd_address mword) g2) /\ color_of_object1 x g2 == white);*)
  assert (sweep_props_black_to_white g1 g2);
  assert (sweep_props_black_to_white1 g1 g2);
  assert (sweep_props_black_to_white2 g1 g2);
  assert (sweep_props_black_to_white3 g1 g2);
  
  (*assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isBlackObject1 (hd_address x) g1 <==> 
                    Seq.mem (hd_address x) (objects2 0UL g2) /\ isWhiteObject1 (hd_address x) g2);

  assert (forall x. Seq.mem (hd_address x) (objects2 0UL g2) /\ isWhiteObject1 (hd_address x) g2 <==>
                    (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                              G.reachfunc grph o x z1));*)
  
  graph_vertices_after_sweep_lemma g st vl root_set c c1 fp;
  
  assert (well_formed_heap2 g2);
  assert (graph_creation_necessary_condition g2);
  let grph_sweep = create_graph_from_heap g2 in 

  (*assert (forall x. Seq.mem x ((grph_sweep).vertices) <==>
                                     Seq.mem (hd_address x) (objects2 0UL g2) /\ 
                                      isWhiteObject1 (hd_address x) g2);

  assert (forall x. Seq.mem x ((grph_sweep).vertices) <==>
                    (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                                              G.reachfunc grph o x z1));*)

  
  assert (let g1 = mark5 g st in
                             let g2, _ =  sweep_with_free_list3 g1 mword fp in
                             let grph = create_graph_from_heap g in 
                             let grph_sweep = create_graph_from_heap g2 in
                             let allocs_sweep = get_allocated_block_addresses g2 in
                             (forall x. Seq.mem x ((grph_sweep).vertices) <==>
                                  (exists o (z1: G.reach grph o x) . Seq.mem o root_set /\
                                              G.reachfunc grph o x z1)));
  ()



#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"
#push-options "--split_queries always"

#restart-solver

#restart-solver

#restart-solver

let create_edge_list_from_heap1_pre_condition_on_seq (g:heap{well_formed_heap2 g})
                                                    (f: seq Usize.t) =
    all_mem_of_allocated_blocks f g /\
    within_heap_all f /\
    multiple_of_mword_all f /\
    all_valid_headers f g /\
    (G.is_vertex_set f) /\
    all_objects_and_their_field_pointers_are_within_heap_size f g /\
    all_field_address_are_word_aligned  f g


(*(forall x y. Seq.mem (x,y) edge_list_from_heap_sweep  <==>
                    Seq.mem (hd_address x) allocs_sweep /\
                    Seq.mem (hd_address y) allocs_sweep /\
                    Seq.mem (x,y) (create_edge_list_from_heap1 g1 allocs_mark))*)

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver

#restart-solver


let rec create_edge_list_from_heap1_subset_lemma    (g1:heap{well_formed_heap2 g1})
                                                    (f1: seq Usize.t 
                                                       {create_edge_list_from_heap1_pre_condition_on_seq g1 f1})
                                                    (g2:heap{well_formed_heap2 g2})
                                                    (f2: seq Usize.t 
                                                       {create_edge_list_from_heap1_pre_condition_on_seq g2 f2})
                       : Lemma 
                         (requires ((forall x. Seq.mem x f2 ==> Seq.mem x f1) /\
                                     field_reads_equal g1 g2 /\
                                     (forall x. Seq.mem x (get_allocated_block_addresses g2) ==> is_hp_addr x) /\
                                      (forall x. Seq.mem x (get_allocated_block_addresses g2) ==>
                                                 getWosize(read_word g2 x) == getWosize(read_word g1 x)) /\
                                      (forall x. Seq.mem x (get_allocated_block_addresses g2) ==>
                                                 getTag(read_word g2 x) == getTag(read_word g1 x)) /\
                                      check_well_formed_closure_objs g2 f2 /\
                                      check_well_formed_closure_objs g1 f1))
                         (ensures (
                                    let s = create_edge_list_from_heap1 g2 f2 in
                                    let s1 = create_edge_list_from_heap1 g1 f1 in
                                       (forall x y. Seq.mem (x,y) s  <==>
                                                    Seq.mem (hd_address x) f2 /\
                                                    Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                                                    Seq.mem (x,y) s1)))
                         (decreases (length_fn f2)) = 
if length f2 = 0 then 
 (
   let e = Seq.empty #G.edge in
   seq_empty_lemma ();
   let s = create_edge_list_from_heap1 g2 f2 in

   let s1 = create_edge_list_from_heap1 g1 f1 in

   assert (s == e);
   assert (forall x y. Seq.mem (x,y) s  ==>
                    Seq.mem (hd_address x) f2 /\
                    Seq.mem (hd_address y) f2);
   seq_empty_lemma1 f2;

   assert (forall x y. Seq.mem (x,y) s  <==>
                    Seq.mem (hd_address x) f2 /\
                    Seq.mem (hd_address y) f2 /\
                    Seq.mem (x,y) s1);

   assert (forall x y. Seq.mem (x,y) s  <==>
                    Seq.mem (hd_address x) f2 /\
                    Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                    Seq.mem (x,y) s1);

   ()
 )
 else
 (
   
   seq_non_empty_lemma f2;
   let hd = Seq.head f2 in
   assert (is_hp_addr hd);
   can_shift_forward_lemma f2 g2 hd;

   (*Since Seq lemmas are disbaled from calling from F* library, we need to explicitly prove the below basic seq properties*)
   (*Putting an assume for time being. lenght f1 > 0 since length f2 > 0 as f2 subset f1.*)
   assume (Seq.length f1 > 0);
   seq_non_empty_lemma f1;
   

  assume (Seq.mem hd f1);
  
   assert (Usize.v hd + Usize.v mword < heap_size);
   let tl = Seq.tail f2 in
   G.is_vertex_set_lemma f2;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f2;
   assert (~(Seq.mem hd tl));
   
   length_fn_lemma f2;
   
   let s1 = create_edge_list_from_heap1 g1 f1 in

   let rest_of_f = create_edge_list_from_heap1 g2 tl in
   
   create_edge_list_from_heap1_subset_lemma g1 f1 g2 tl;

   assert (forall x y. Seq.mem (x,y) rest_of_f  <==>
                                        Seq.mem (hd_address x) tl /\
                                        Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                                        Seq.mem (x,y) s1);

   let tg = tag_of_object1 hd g2 in
   let tg1 = tag_of_object1 hd g1 in
   
   assert (tg == tg1);
   
   if (Usize.v tg < no_scan_tag) then 
   (
     let wz = getWosize (read_word g2 hd) in
     let f_id = f_address hd in
     f_address_lemma tl hd;
     
     if (Usize.v tg = closure_tag) then
     (
       
       assert (Usize.v f_id >= Usize.v mword /\
               (is_valid_header1 (hd_address f_id) g2) /\
               (Usize.v (tag_of_object1 (hd_address f_id) g2) == closure_tag));
      
     
       assert (Usize.v (wosize_of_object1 (hd_address f_id) g2) >= 2);

       let start_env = start_env_clos_info g2 f_id in
       let start_env_plus_one = Usize.add start_env 1UL in

       assert ((Usize.v start_env <= Usize.v (wosize_of_object1 (hd_address f_id) g2)) /\
             Usize.v start_env >= 1);
       
       let edge_pairs_for_hd = create_edge_pairs_for_h_index g2 hd wz start_env_plus_one in
       
       let s = create_edge_list_from_heap1 g2 f2 in

       
       let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
       Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
       (*Prove this on *)
       assume (forall x y. Seq.mem (x,y) (edge_pairs_for_hd)  <==>
                                                    Seq.mem (hd_address x) f2 /\
                                                    Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                                                    Seq.mem (x,y) s1);
       
       assert (forall x. Seq.mem (hd_address x) tl  ==> Seq.mem  (hd_address x) f2);


       assert (forall x y. Seq.mem (x,y) rest_of_f  ==>
                                        Seq.mem (hd_address x) f2 /\
                                        Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                                        Seq.mem (x,y) s1);                     

      assert (forall x y. Seq.mem (x,y) rest_of_f  <==>
                                        Seq.mem (hd_address x) tl /\
                                        Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                                        Seq.mem (x,y) s1);

      assert (forall x y. Seq.mem (x,y) s  <==>
                                        Seq.mem (hd_address x) f2 /\
                                        Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                                        Seq.mem (x,y) s1);
      
      
      ()
     )
     else
     (
       let edge_pairs_for_hd = create_edge_pairs_for_h_index g2 hd wz 1UL in
       
       let s = create_edge_list_from_heap1 g2 f2 in                                                 
       
       
       let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
       Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
       assume (forall x y. Seq.mem (x,y) (edge_pairs_for_hd)  <==>
                                                    Seq.mem (hd_address x) f2 /\
                                                    Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                                                    Seq.mem (x,y) s1);
       
       
       assert (forall x y. Seq.mem (x,y) rest_of_f  <==>
                                        Seq.mem (hd_address x) tl /\
                                        Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                                        Seq.mem (x,y) s1);

       assert (forall x y. Seq.mem (x,y) s  <==>
                                        Seq.mem (hd_address x) f2 /\
                                        Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                                        Seq.mem (x,y) s1);
       ()
     )
   )
   else
   (
     (*branch type checked when other branches are commented out*)
     let edge_pairs_for_hd = Seq.empty #G.edge in
     seq_empty_lemma ();
     
     let f_id = f_address hd in
     
     f_address_lemma tl hd;
     
    
     
     let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
     Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
     Seq.append_empty_l rest_of_f;

     let s = create_edge_list_from_heap1 g2 f2 in  

     assert (forall x y. Seq.mem (x,y) rest_of_f  <==> Seq.mem (x,y) s);
     
     
     assert (forall x y. Seq.mem (x,y) s  <==>
                                        Seq.mem (hd_address x) tl /\
                                        Seq.mem (hd_address y) (get_allocated_block_addresses g2) /\
                                        Seq.mem (x,y) s1);
     
     
     assert (~(exists x y. Seq.mem (x,y) s /\ (hd_address x) == hd));
     assume (~(exists x y. Seq.mem (x,y) s1 /\ (hd_address x) == hd));
     assert (forall x. Seq.mem (hd_address x) f2 <==> (hd_address x) == hd \/ Seq.mem (hd_address x) tl);
     
    

     assert (forall x y. Seq.mem (x,y) s  <==>
                                        (Seq.mem (hd_address x) f2)  /\
                                        (Seq.mem (hd_address y) (get_allocated_block_addresses g2)) /\
                                        Seq.mem (x,y) s1);
     ()
   )
)


#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let sub_graph_edges_after_sweep_remains_same_lemma1 (g:heap{well_formed_heap2 g}) 
                                               (st: seq Usize.t {stack_props_func g st})
                                               (vl: seq Usize.t {vl_props_func g vl}) 
         
                                               (root_set : seq Usize.t{root_props g root_set})
 
                                               (c:color{c == 3UL})
                                               (c1:color{c1 == 2UL})
                                               (fp:hp_addr{refinements_on_free_list g fp})
                                
                 : Lemma
                   (requires  graph_creation_necessary_condition g /\
                              
                              st_vl_root_set_subset_of_ff_allocs g st vl root_set /\ 

                              mutual_exclusivity_of_st_vl g st vl /\
                              
                              pre_conditions_for_dfs_lemma_invoke g st vl root_set /\
                              
                              pre_conditions_necessary_for_sweep g st fp /\
                             
                             (well_formed_heap2 (fst (sweep_with_free_list3 (mark5 g st) mword fp))) /\

                             graph_creation_necessary_condition (mark5 g st) /\
                             
                             graph_creation_necessary_condition (fst (sweep_with_free_list3 (mark5 g st) mword fp))) 
                   
                   (ensures (let g1 = mark5 g st in
                             let g2, _ =  sweep_with_free_list3 g1 mword fp in
                             let grph = create_graph_from_heap g in 
                             let grph_sweep = create_graph_from_heap g2 in
                             let allocs_sweep = get_allocated_block_addresses g2 in
                             (forall x y. Seq.mem (x,y) ((grph_sweep).edge_set) <==>
                                            Seq.mem x ((grph_sweep).vertices) /\
                                            Seq.mem y ((grph_sweep).vertices) /\
                                            Seq.mem (x,y) ((grph).edge_set))))  =

// Proving Strategy
//-------------------------------
let grph = create_graph_from_heap g in 
let g1 = mark5 g st in
  
let g2, _ = sweep_with_free_list3 g1 mword fp in
assert (well_formed_heap2 g2);
assert (graph_creation_necessary_condition g2);
let grph_sweep = create_graph_from_heap g2 in 
let grph_sweep_edges = grph_sweep.edge_set in
let grph_sweep_vertices = grph_sweep.vertices in

let grph_mark = create_graph_from_heap g1 in
let grph_mark_edges = grph_mark.edge_set in
let grph_mark_vertices = grph_mark.vertices in

assert (forall x y. Seq.mem (x,y) grph_sweep_edges ==> Seq.mem x grph_sweep_vertices /\
                                                       Seq.mem y grph_sweep_vertices);

let allocs_initial_heap = get_allocated_block_addresses g in
let allocs_mark = get_allocated_block_addresses g1 in
let allocs_sweep = get_allocated_block_addresses g2 in
let grph_edge_set = grph.edge_set in
sweep_with_free_list3_well_formedness_part_lemma1 g1 mword fp;
assert (forall x. Seq.mem x allocs_sweep ==> Seq.mem x allocs_mark);

(*This proof only requires induction hypothesis, as base case is proved on mark5_body. Deferring to do later*)
assume (allocs_initial_heap == allocs_mark);
assert (forall x. Seq.mem x allocs_sweep ==> Seq.mem x allocs_initial_heap);
assert (forall x. Seq.mem x grph_sweep_vertices <==> Seq.mem (hd_address x) allocs_sweep);
assert (forall x. Seq.mem x grph.vertices <==> Seq.mem (hd_address x) allocs_initial_heap);

assert (forall x. Seq.mem (hd_address x) allocs_sweep ==> Seq.mem (hd_address x) allocs_initial_heap);
//assert (forall x. Seq.mem (hd_address x) allocs_sweep ==> Seq.mem (hd_address x) allocs_initial_heap <==> Seq.mem x grph.vertices) ;

mark5_graph_lemma g st;
assert (grph_mark == grph);
assert (grph_mark.edge_set == grph.edge_set);
assert (create_edge_list_for_graph g1 == create_edge_list_for_graph g);

assert (create_edge_list_from_heap1 g1 allocs_mark == create_edge_list_from_heap1 g allocs_initial_heap);

let edge_list_from_heap_sweep = create_edge_list_from_heap1 g2 allocs_sweep in

(*create_edge_list_from_heap1_subset_lemma as proved above is called to remove the below assume*) 
assume (forall x y. Seq.mem (x,y) edge_list_from_heap_sweep  <==>
                    Seq.mem (hd_address x) allocs_sweep /\
                    Seq.mem (hd_address y) allocs_sweep /\
                    Seq.mem (x,y) (create_edge_list_from_heap1 g1 allocs_mark));

assert (forall x y. Seq.mem (x,y) edge_list_from_heap_sweep  <==>
                    Seq.mem x grph_sweep_vertices /\
                    Seq.mem y grph_sweep_vertices /\
                    Seq.mem (x,y) (create_edge_list_from_heap1 g1 allocs_mark));

assert (forall x y. Seq.mem (x,y) edge_list_from_heap_sweep  <==>
                    Seq.mem x grph_sweep_vertices /\
                    Seq.mem y grph_sweep_vertices /\
                    Seq.mem (x,y) (create_edge_list_from_heap1 g allocs_initial_heap));

assert (forall x y. Seq.mem (x,y) edge_list_from_heap_sweep  <==>
                    Seq.mem x grph_sweep_vertices /\
                    Seq.mem y grph_sweep_vertices /\
                    Seq.mem (x,y) (create_edge_list_for_graph g));

assert (forall x y. Seq.mem (x,y) edge_list_from_heap_sweep  <==>
                    Seq.mem x grph_sweep_vertices /\
                    Seq.mem y grph_sweep_vertices /\
                    Seq.mem (x,y) grph.edge_set);

assert (forall x y. Seq.mem (x,y) edge_list_from_heap_sweep  <==>
                    Seq.mem x grph_sweep_vertices /\
                    Seq.mem y grph_sweep_vertices /\
                    Seq.mem (x,y) grph.edge_set);
()



(*--------------------------------------------------------------------------------------------------------------------------------------------*)                                      
(*let sweep_with_free_list_well_formedness_lemma 
                              (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ 
                                     write_word_to_blue_object_field_lemma_props1 g})
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)/\ 
                                             (Seq.length (objects2 (hd_address f_index) g) > 0)
                              })
                              (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                           Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                           color_of_object1 (hd_address fp) g == blue /\
                                          (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                          Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
              : Lemma
                (requires  (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                      is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                          (check_well_formed_closure_objs g (get_allocated_block_addresses g) == true))
                (ensures  (well_formed_heap2 (fst (sweep_with_free_list3 g mword fp)))) =
  let g' = (fst (sweep_with_free_list3 g mword fp)) in
  assert (forall x. Seq.mem x (objects2 0UL g) ==> Usize.v (getWosize (read_word g x)) > 0);
  
  sweep_with_free_list3_well_formedness_part_lemma1 g mword fp;
  assert (let allocs' = (get_allocated_block_addresses g') in
          (forall x. Seq.mem x allocs' ==>
                            Seq.mem x (get_allocated_block_addresses g)) /\
                                        
          (forall x. Seq.mem x allocs' ==>
                            getWosize(read_word g' x) == getWosize(read_word g x)) /\
          (forall x. Seq.mem x allocs' ==>
                            getTag(read_word g' x) == getTag(read_word g x)) /\
          (Seq.length (objects2 0UL g') > 0) /\
          field_reads_equal g g');
  check_well_formed_closure_objs_lemma2 g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
  assert ((forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    Seq.mem x (get_allocated_block_addresses g)) /\
        (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                   getWosize (read_word g x) == getWosize (read_word g' x)));
  assert (field_reads_of_allocs_of_two_heaps_are_equal g g' (get_allocated_block_addresses g'));
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> 
                    is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
  check_all_block_fields_within_limit2_lemma_for_sweep g g' (get_allocated_block_addresses g) (get_allocated_block_addresses g');
  assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> 
                    is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
  assert (check_all_block_fields_within_limit2 g' (get_allocated_block_addresses g'));
  assert (check_well_formed_closure_objs g' (get_allocated_block_addresses g'));

  (*Prove this*)
  assume (forall x. Seq.mem x (get_allocated_block_addresses g') ==>
                    is_fields_points_to_blocks2 x g' (getWosize (read_word g' x)) (get_allocated_block_addresses g'));

  assert ((check_fields_points_to_blocks2 g' (get_allocated_block_addresses g')));
  assert (well_formed_heap2 g');
  ()

(*Currently the below are proved for proving the well-formedness of heap g2 till this point,
   g - initial heap before the GC, g1 - the heap resulted after mark, g2 - the heap resulted after sweep
   1.  for all allocated objects in g2, their successors in heap g1 are members 
      of the allocated objects in g2*)





(*************************************REMOVE SWEEP WITH FREELIST AND COALESCING************************************************)
(*Sweep with freelist and coalescing*)
let sweep_body_with_free_list_and_coalescing (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0) /\ write_word_to_blue_object_field_lemma_props1 g})
                                             (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ 
                                                              Seq.mem (hd_address f_index) (objects2 0UL g)})
                                             (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                                         color_of_object1 (hd_address fp) g == blue /\
                                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
            : Tot (p:heap_heap_addr_pair) =
                            
 let h_index = hd_address f_index in
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white || c = blue) then 
 (
   let g' = colorHeader3 h_index g blue in
   assert (objects2 0UL g == objects2 0UL g');
   
   assert (Usize.v fp % Usize.v mword == 0);

   let hd_fp = hd_address fp in
   let fp_wz_sz = getWosize (read_word g' hd_fp) in
   let fp_wz_sz' = getWosize (read_word g hd_fp) in
   assert (fp_wz_sz == fp_wz_sz');
   let fp_color = getColor (read_word g' hd_fp) in
   assert (fp_color == blue);
   let fp_wz_sz_plus_one = Usize.add fp_wz_sz 1UL in
   let next_obj_offset = Usize.mul fp_wz_sz_plus_one mword in
   let next_obj = Usize.add fp next_obj_offset in
   if (next_obj = f_index) then
   (
     let hd_f_index = hd_address f_index in
     let f_index_wz = getWosize (read_word g' hd_f_index) in
     let f_index_wz' = getWosize (read_word g hd_f_index) in
     assert (f_index_wz == f_index_wz');
     assert (Seq.mem hd_fp (objects2 0UL g') /\ Seq.mem hd_f_index (objects2 0UL g));
     let new_wz = Usize.add fp_wz_sz f_index_wz in
     let tg = getTag (read_word g' hd_fp) in
     
     assert (Usize.v new_wz <= Usize.v max_wosize);
     let h = makeHeader new_wz fp_color tg in 
     let g1 = write_word g' hd_fp h in
     write_word_lemma g' hd_fp h;
     write_word_lemma1 g' hd_fp h;
     assert (forall (i:hp_addr). i <> hd_fp ==> getWosize (read_word g1 i) == getWosize (read_word g' i));
     assert (forall (i:Usize.t{Usize.v i < heap_size /\ Usize.v i % 8 == 0}). i <> hd_fp ==>  getWosize (read_word g' i) == getWosize (read_word g1 i));
     assert (Usize.v new_wz < heap_size);
     let fp_color1 = getColor (read_word g1 hd_fp) in
     assert (fp_color1 == blue);
     let wd_sz = getWosize (read_word g1 hd_fp) in
     assert (wd_sz == new_wz);
     assert (Usize.v new_wz > 0);
     assert (Seq.length (objects2 0UL g) > 0);
     assert (Seq.length (objects2 0UL g') > 0);
     assert (Seq.mem hd_fp (objects2 0UL g));
     assert (Seq.mem hd_fp (objects2 0UL g'));
     assert (Seq.length (objects2 0UL g') > 0);
     assert (Usize.v (getWosize (read_word g' hd_fp)) > 0);
     assert (Usize.v (getWosize (read_word g1 hd_fp)) > 0);
     assert (Usize.v hd_fp + ((Usize.v (getWosize (read_word g1 hd_fp)) +  1) * Usize.v mword) <= heap_size);
     let hd_fp_next =  Usize.add hd_fp (Usize.mul (Usize.add (getWosize (read_word g1 hd_fp)) 1UL) mword) in
     assert (Usize.v hd_fp_next <= heap_size);
     assert (forall x. Seq.mem x (objects2 0UL g') /\ x <> hd_fp ==>  getWosize (read_word g' x) == getWosize (read_word g1 x));
     assert (forall x. Seq.mem x (objects2 0UL g') ==> Usize.v (getWosize (read_word g' x)) > 0);
     assert (forall x. Seq.mem x (objects2 0UL g') /\ x <> hd_fp ==> Usize.v (getWosize (read_word g1 x)) > 0);
     assert (Usize.v (getWosize (read_word g1 hd_fp)) > 0);
     assume (forall x. Seq.mem x (objects2 0UL g') ==> Usize.v x + Usize.v (getWosize (read_word g' x)) < heap_size);//Prove this from obects2 set construction
     assert (forall x. Seq.mem x (objects2 0UL g') /\ x <> hd_fp ==>  Usize.v x + Usize.v (getWosize (read_word g' x)) < heap_size);
     assert (Usize.v hd_fp + Usize.v (getWosize (read_word g' hd_fp)) < heap_size);
     assert (Usize.v hd_fp + Usize.v (getWosize (read_word g1 hd_fp)) < heap_size);
     assert (forall x. Seq.mem x (objects2 0UL g') /\ x <> hd_fp ==>  Usize.v x + Usize.v (getWosize (read_word g1 x)) < heap_size);
     (g1,fp)

   )
   else
   (
     let g1 = write_word g' fp f_index in
     //write_word_to_blue_object_field_lemma1 g' fp f_index;
     write_word_to_blue_object_field_lemma g' fp  f_index;
     //assert (well_formed_heap2 g1);
     assert (objects2 0UL g == objects2 0UL g');
     assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
     (g1,f_index)

   )
 )
 else
 (
   assert (c == black);
   let g' = colorHeader3 h_index g white in
   assert (objects2 0UL g == objects2 0UL g');
      
   //assert (well_formed_heap2 g');
   assert (Usize.v fp >= Usize.v mword);
   //assert (is_valid_header (hd_address fp) g');
   assert (color_of_object1 (hd_address fp) g == blue);
   assert (color_of_object1 (hd_address fp) g' == blue);
   assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   (g',fp)
 )

#restart-solver

#push-options "--split_queries always"


let rec sweep_with_free_list_coalescing (g:heap{noGreyObjects g /\ (Seq.length (objects2 0UL g) > 0)})
                             
                              (f_index:hp_addr{Usize.v f_index >= Usize.v mword /\ Seq.mem (hd_address f_index) (objects2 0UL g)(*/\ 
                                             (Seq.length (objects2 (hd_address f_index) g) > 0)*)
                              })
                             
                             (fp:hp_addr{Usize.v fp >= Usize.v mword /\ 
                                         Seq.mem (hd_address fp) (objects2 0UL g) /\ 
                                         color_of_object1 (hd_address fp) g == blue /\
                                         (forall x y. Seq.mem x (objects2 0UL g) /\ Seq.mem y (objects2 0UL g) ==>
                                                                 Usize.v (getWosize (read_word g x)) + Usize.v (getWosize (read_word g y)) < heap_size)})
          : Tot (p:heap_heap_addr_pair) 
           (decreases (heap_size - Usize.v f_index)) =

 let h_index = hd_address f_index in
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let f_index_new =  Usize.add h_index_new mword in
 wosize_plus_one_times_mword_multiple_of_mword wz;
 assert (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0);
 assert (Usize.v h_index_new % Usize.v mword == 0);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
 sum_of_multiple_of_mword_is_multiple_of_mword h_index_new mword;

 assert (Usize.v (Usize.add h_index_new mword) % Usize.v mword == 0);
 assert (Usize.v f_index_new % Usize.v mword == 0);
 
 let g', fp' = sweep_body_with_free_list_and_coalescing g f_index fp in
 assume (noGreyObjects g' /\ (Seq.length (objects2 0UL g') > 0));
 assume (Usize.v fp' >= Usize.v mword /\ 
        Seq.mem (hd_address fp') (objects2 0UL g') /\ 
        color_of_object1 (hd_address fp') g' == blue /\
       (forall x y. Seq.mem x (objects2 0UL g') /\ Seq.mem y (objects2 0UL g') ==>
                         Usize.v (getWosize (read_word g' x)) + Usize.v (getWosize (read_word g' y)) < heap_size));

 if Usize.v f_index_new >= heap_size then
 (
   (g',fp')
 )
 else
 (
   //assert (h_index_new = hd_address f_index_new);
   assert (Usize.v f_index_new < heap_size);
   assert (Usize.v f_index_new >= Usize.v mword);
   assert (UInt.fits (Usize.v f_index_new - Usize.v mword) Usize.n);

   assert (Seq.length (objects2 0UL g) > 0 /\ Seq.mem h_index (objects2 0UL g));
   objects2_mem_lemma1_app1 h_index g;
   assert (Seq.mem h_index_new (objects2 0UL g));
   //assume (forall x. Seq.mem x (objects2 0UL g) /\ x <> h_index ==> Seq.mem x (objects2 0UL g'));
   assert (h_index_new <> h_index);
   //assert (Seq.mem h_index_new (objects2 0UL g'));
   
  
   assert (Usize.v f_index_new >= Usize.v mword); 
   //assert (Seq.mem h_index_new (objects2 0UL g'));
   assert (Usize.v f_index_new % Usize.v mword == 0);
   assert (Usize.v f_index_new < heap_size);
   assert (is_hp_addr f_index_new);
   assert (Usize.v h_index_new < heap_size);
   assert (Seq.length (objects2 0UL g') > 0);
   
   assume (mem (hd_address f_index_new) (objects2 0UL g'));
   let g'',fp'' = sweep_with_free_list_coalescing g' f_index_new fp' in
   (g'',fp'')
 )

#restart-solver
*)

(* hd_address (read_word g y) <> fp (address of the free list pointer = ), 
    y - field address of a location of an allocated object after heap, 
    where a pointer value is stored

    sw
    -----------------------------
    -----------------------------
    for every object in the object set,

     1. sweep body will not change the tg or wz of the header of that object.
     2. 
    
    iirespective of an object being infix or non infix, can we show that the sweep body does not change the tag and the wosize.
    

    infix object does not belong to object set. So sweep never encounters an infix object.

    o1 ----> o2 ; tag (header o2 in g) == tag (header o2 in g')
                  wz (header o2 in g) == wz (header o2 in g')

    proved - sweep does not change tag or wz of objects (does not include non-infix)

    This is true for non-infix.

    Now prove for infix

    Before the sweep, a non-infix object is a non-infix object.

    contradicts - sweep does not change a non-infix object to an infix object.

    let tg = tag_of_object1 hdr_succ g' in
    let tg1 = tag_of_object1 hdr_succ g in
    
    Property proved - (1) sweep does not change tg of object set object and object g == objectt g' (proved both)
    
    tg == infix 
    tg1 == tg (Since sweep does not change a non-infix to infix. (property 1)
    Another lemma should say, sweep does not encounter infix objects. This is needed for wz of infix objects.
    sweep will encounter every object in the object set. Sweep will not encounter an infix object
    Hence sweep will not change the wz of an infix object.
    
    tg == non-infix, then
    tg1 == tg (property 1)                
    

    The first field of a free list 

    First field cannot be another objects header, includes infix. (this is not defined yet.)


    *)
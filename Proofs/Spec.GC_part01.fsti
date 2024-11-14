module Spec.GC_part01

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
let max_wosize_lemma () : Lemma (ensures (Usize.v max_wosize = pow2 54 - 1)) =
  assert (Usize.v (Usize.shift_left 1UL 54ul) == pow2 54 % pow2 64);
   Math.Lemmas.pow2_lt_compat 64 54;
   Math.Lemmas.small_mod (pow2 54) (pow2 64)

let max_color_size_lemma () :Lemma (ensures (Usize.v max_color = pow2 2 - 1)) =
   assert (Usize.v (Usize.shift_left 1UL 2ul) == pow2 2 % pow2 64);
   Math.Lemmas.pow2_lt_compat 64 2;
   Math.Lemmas.small_mod (pow2 2) (pow2 64)



let max_tag_size_lemma  () :Lemma (ensures (Usize.v max_tag = pow2 8 - 1)) =
   assert (Usize.v (Usize.shift_left 1UL 8ul) == pow2 8 % pow2 64);
   Math.Lemmas.pow2_lt_compat 64 8;
   Math.Lemmas.small_mod (pow2 8) (pow2 64)

(*---------------------------------------------------------------------------------------------------------------------*)

(*Definitions*)
type heap = g:seq U8.t{Seq.length g == heap_size /\ is_heap_size_multiple_of_mwords ()}

type wosize = sz:Usize.t{0 <= Usize.v sz /\ Usize.v sz <= Usize.v max_wosize}

type color = cl:Usize.t{0 <= Usize.v cl /\ Usize.v cl <= Usize.v max_color}

type tag = tg:Usize.t{0 <= Usize.v tg /\ Usize.v tg <= Usize.v max_tag}

let is_size_fits_after_subtraction (x:Usize.t)
                                   (y:Usize.t)
                       : Tot (b:bool{b == true <==> UInt.fits (Usize.v x - Usize.v y) Usize.n}) =
  UInt.fits (Usize.v x - Usize.v y) Usize.n

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
let getWosize (h:Usize.t)
          :Tot (wz:wosize{wz == Usize.shift_right h 10ul}) =
 let _ = max_wosize_lemma () in
 let _ = assert (Usize.v max_wosize = pow2 54 - 1) in
 let wz = Usize.shift_right h 10ul in
 assert (Usize.v wz == Usize.v h/ pow2 10);
 assert (Usize.v wz <= Usize.v max_wosize);
 assert (Usize.v wz >= 0);
 wz


/// Extract color from header value
let getColor  (h:Usize.t)
          : Tot (c:color{c = Usize.logand (Usize.shift_right h 8ul) 3UL}) =
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


/// Extract tag from header value
let getTag  (h:Usize.t) 
          : Tot (tg:tag{tg == Usize.logand h 255UL}) =
 let _ = max_tag_size_lemma () in
 assert (Usize.v max_tag = pow2 8 - 1);
 let t = Usize.logand h 255UL in
 UInt.logand_le #64 (Usize.v h) 255;
 assert (Usize.v max_tag <= pow2 8 - 1);
 assert (Usize.v t <= 255);
 assert (Usize.v t <= Usize.v max_tag);
 t


let color_of_object1   (v_id: hp_addr)
                       (g:heap)
             : Tot (c:color{c == getColor(read_word g v_id)})  =
  let hd_val = read_word g v_id in
  let c = getColor (hd_val) in
  c


let wosize_of_object1 (v_id: hp_addr) 
                        (g:heap)
             :Tot (w:wosize{w == getWosize(read_word g v_id)}) =
  let hd_val = read_word g v_id in
  let w = getWosize (hd_val) in
  w


let tag_of_object1   (v_id: hp_addr)
                     (g:heap)
             :Tot (t:tag{t == getTag(read_word g v_id)}) =
  let hd_val = read_word g v_id in
  let t = getTag (hd_val) in
  t

let isBlueObject1  (v_id: hp_addr)
                   (g:heap) 
        :Tot (b: bool {b == true <==> (color_of_object1 v_id g) == blue}) =
 if color_of_object1 v_id g = blue then true
 else
  false

let isWhiteObject1  (v_id: hp_addr)
                     (g:heap) 
        : Tot (b: bool {b == true <==> (color_of_object1 v_id g) == white}) =
  if color_of_object1 v_id g = white then true
 else
  false

let isGrayObject1   (v_id: hp_addr)
                    (g:heap)
        : Tot (b: bool {b == true <==> (color_of_object1 v_id g) == gray}) =
  if color_of_object1 v_id g = gray then true
 else
  false

let isBlackObject1   (v_id: hp_addr)
                     (g:heap) 
        : Tot (b: bool {b == true <==> (color_of_object1 v_id g) == black}) =
 if color_of_object1 v_id g = black then true
 else
  false

open FStar.FunctionalExtensionality
open FStar.UInt

#push-options "--z3rlimit 500 --fuel 0 --ifuel 1" (*Be careful to use this. Always set fuel limits to default or higher if
                                                 recursive calls dont work as expected*)

#push-options "--split_queries always"

#restart-solver

let makeHeader   (wz:wosize)
                 (c:color)
                 (tg:tag) 
             :Tot (h:Usize.t{wz == getWosize h /\
                            c == getColor h /\
                            tg == getTag h}) =
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

#pop-options

#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"


let isPointer   (v_id: hp_addr) 
                (g:heap) 
           : Tot (b:bool{b == true <==> Usize.logand (read_word g v_id) 1UL == 0UL}) =
 if Usize.logand (read_word g v_id) 1UL = 0UL then true else false


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

let is_fields_within_limit1   (h_index: hp_addr) 
                               (wz: wosize)
              :Tot (b:bool{b == true <==> (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size)}) =
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


let rec is_fields_contents_within_limit2 (h_index: hp_addr) 
                                         (wz: wosize{is_fields_within_limit1 h_index wz}) 
                                         (g:heap(*{Usize.v (tag_of_object1 h_index g) < no_scan_tag /\
                                               Usize.v (tag_of_object1 h_index g) <> closure_tag}*)) 
                           :Tot (b:bool{b == true <==>  (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}).isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                          (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) >= Usize.v mword /\
                                                          Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) < heap_size) /\
                                                          is_hp_addr (read_word g (Usize.add h_index (Usize.mul i mword))))})
                            (decreases (Usize.v wz)) =
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



let wosize_times_mword_multiple_of_mword (wz:wosize)
                     :Lemma 
                      (ensures (Usize.v (Usize.mul wz mword) % Usize.v mword == 0)) = ()


let sum_of_multiple_of_mword_is_multiple_of_mword (x:Usize.t{Usize.v x % Usize.v mword == 0})
                                                  (y:Usize.t{Usize.v y % Usize.v mword == 0})
                                :Lemma 
                                 (ensures ((Usize.v x + Usize.v y) % Usize.v mword == 0)) = ()

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


let rec objects2   (h_index: hp_addr)
               (g:heap) 
       : Tot (s:seq Usize.t {Seq.length s > 0 ==> (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
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
                                                                     
                       (decreases (heap_size - Usize.v h_index)) =
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


/// Given the start address of an object, which is the address of the first field of the object, hd_address gets the header address of that object
let hd_address (st_index: hp_addr{UInt.fits (Usize.v st_index - Usize.v mword) Usize.n})
          : Tot (h:hp_addr{Usize.v h == Usize.v st_index - Usize.v mword}) = 
  let h_index = Usize.sub st_index mword in
  assert (Usize.v h_index % Usize.v mword == 0);
  assert (Usize.v h_index >= 0);
  assert (is_hp_addr h_index);
  h_index

#restart-solver 

let objects2_wosize_lemma  (h_index: hp_addr)
                           (g:heap)
                : Lemma
                  (ensures (Seq.length (objects2 h_index g) > 0) ==> Usize.v (getWosize (read_word g h_index)) > 0) =
  ()




let objects2_empty_lemma   (h_index: hp_addr)
                           (g:heap)
              :Lemma
                (requires (let wz = getWosize (read_word g h_index) in
                           let h_index_new = Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                           ( Usize.v wz > 0 /\
                             Usize.v h_index_new < heap_size)))
                
                (ensures (let wz = getWosize (read_word g h_index) in
                          let h_index_new = Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                          (Seq.length (objects2 h_index_new g) == 0 ==>
                          (objects2 h_index g) == (objects2 h_index_new g))
                         )
                ) =
 ()

let objects2_non_empty_lemma  (h_index: hp_addr)
                              (g:heap)
                :Lemma
                (requires (let wz = getWosize (read_word g h_index) in
                           let h_index_new = Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                           (Usize.v wz > 0 /\
                            Usize.v h_index_new < heap_size)))
                
                (ensures (let wz = getWosize (read_word g h_index) in
                          let h_index_new = Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                          (Seq.length (objects2 h_index_new g) > 0 ==>
                          (objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g))
                         )
                ) = ()



let objects2_singleton_lemma  (h_index: hp_addr)
                              (g:heap)
               : Lemma
                (requires (let wz = getWosize (read_word g h_index) in
                           let h_index_new = Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                           (Usize.v wz > 0 /\
                            Usize.v h_index_new == heap_size)))
                (ensures ((objects2 h_index g) == Seq.create 1 h_index)) = ()



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

let rec objects2_mem_lemma1     (h_index: hp_addr) 
                            (g:heap)
                           
                      
           : Lemma 
            (ensures ((Seq.length (objects2 h_index g) > 0  ==> (forall x. Seq.mem x (objects2 h_index g) /\ 
                                                                  Usize.v (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) < heap_size ==> 
                                                                       Seq.mem (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) 
                                                                           (objects2 h_index g)))))
            (decreases (heap_size - Usize.v h_index)) =
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



let rec objects2_equal_lemma  (h_index:hp_addr) 
                          (g:heap) 
                          (g':heap) 
                    : Lemma
                       (requires (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index)) =
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



let rec objects2_equal_lemma3  (h_index:hp_addr) 
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

                   
let rec objects2_length_lemma (h_index:hp_addr) 
                           (g:heap)
                    :Lemma
                     (ensures (Seq.length (objects2 h_index g) <= (heap_size - Usize.v h_index)))
                     (decreases (heap_size - Usize.v h_index)) =
  
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

let rec objects2_color_lemma  (h_index:hp_addr) 
                           (g:heap) 
                    : Lemma
                     (ensures (forall x. Seq.mem x (objects2 h_index g) ==> color_of_object1 x g == white \/
                                                                       color_of_object1 x g == gray \/
                                                                       color_of_object1 x g == black \/
                                                                       color_of_object1 x g == blue))
                     (decreases (heap_size - Usize.v h_index)) =
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

#restart-solver

let heap_remains_same_except_index_v_id  (v_id:hp_addr)
                                         (g:heap)
                                         (g':heap{Seq.length g == Seq.length g'}) =
  forall (x:Usize.t {Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). x <> v_id ==>
           read_word g x == read_word g' x 
           
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
                           :Tot (allocs: seq Usize.t {(forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
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


let get_allocated_block_addresses_lemma     (g:heap {Seq.length (objects2 0UL g) > 0}) 
                                            (g':heap{Seq.length (objects2 0UL g') > 0})
                                            (v_id:hp_addr) 
                                            (c:color)
                          : Lemma
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
                           (ensures (get_allocated_block_addresses g == get_allocated_block_addresses g')) =
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

let get_black_block_addresses   (g:heap {Seq.length (objects2 0UL g) > 0}) 
                                (allocs: seq Usize.t {Seq.equal allocs (get_allocated_block_addresses g) /\
                                                     (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x allocs ==> Seq.mem x (objects2 0UL g)) /\
                                                     (G.is_vertex_set allocs) /\
                                                     (G.subset_vertices allocs 
                                                       (objects2 0UL g)) /\
                                                     (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                               (isGrayObject1 x g) \/
                                                                               (isBlackObject1 x g))}) 
                           : Tot (blacks: G.vertex_list (*seq Usize.t*)
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
                                                        color_of_object1 x g == black)}) =
 let blacks =  get_color_based_block_picker g allocs black in
 assert (Seq.equal allocs (get_allocated_block_addresses g));
 assert ((forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g)) /\
         (forall x. Seq.mem x (objects2 0UL g) /\
                               ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                      Seq.mem x allocs));
 assert (forall x. Seq.mem x allocs /\ color_of_object1 x g == black ==> Seq.mem x blacks);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g ==>
                                                      Seq.mem x blacks);
 assert (forall x. Seq.mem x blacks ==> Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g);
 assert (forall x. Seq.mem x blacks <==> Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g);
 assert (forall x. Seq.mem x blacks ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (G.is_vertex_set blacks);
 assert (forall x. Seq.mem x blacks ==> Seq.mem x allocs);
 assert (G.subset_vertices blacks allocs /\
        (G.subset_vertices blacks (objects2 0UL g)));
 assert (forall x. Seq.mem x blacks ==> color_of_object1 x g == black);
 assert (forall x. Seq.mem x blacks <==> Seq.mem x allocs /\ color_of_object1 x g == black);
 assert (Seq.equal allocs (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x blacks <==> Seq.mem x (get_allocated_block_addresses g) /\ color_of_object1 x g == black);
 blacks


let get_gray_block_addresses   (g:heap {Seq.length (objects2 0UL g) > 0}) 
                               (allocs: seq Usize.t {Seq.equal allocs (get_allocated_block_addresses g) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                   (forall x. Seq.mem x allocs ==> Seq.mem x (objects2 0UL g)) /\
                                                    (G.is_vertex_set allocs) /\
                                                    (G.subset_vertices allocs 
                                                       (objects2 0UL g)) /\
                                                    (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                               (isGrayObject1 x g) \/
                                                                               (isBlackObject1 x g))}) 
                           : Tot (grays: G.vertex_list (*seq Usize.t*)
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
                                                        color_of_object1 x g == gray)}) =
 let grays =  get_color_based_block_picker g allocs 2UL in
 assert (Seq.equal allocs (get_allocated_block_addresses g));
 assert ((forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g)) /\
         (forall x. Seq.mem x (objects2 0UL g) /\
                               ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                      Seq.mem x allocs));
 assert (forall x. Seq.mem x allocs /\ color_of_object1 x g == gray ==> Seq.mem x grays);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g ==>
                                                      Seq.mem x grays);
 assert (forall x. Seq.mem x grays ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);
 assert (forall x. Seq.mem x grays <==>
   Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);
 assert (forall x. Seq.mem x grays ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (G.is_vertex_set grays);
 assert (forall x. Seq.mem x grays ==> Seq.mem x allocs);
 assert (G.subset_vertices grays allocs /\
          (G.subset_vertices  grays (objects2 0UL g)));
 assert (forall x. Seq.mem x grays ==> color_of_object1 x g == gray);
 assert (forall x. Seq.mem x grays <==> Seq.mem x allocs /\ color_of_object1 x g == gray);
 assert (Seq.equal allocs (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x grays <==> Seq.mem x (get_allocated_block_addresses g) /\ color_of_object1 x g == gray);
 grays


let get_white_block_addresses   (g:heap {Seq.length (objects2 0UL g) > 0}) 
                                (allocs: seq Usize.t {Seq.equal allocs (get_allocated_block_addresses g) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                   (forall x. Seq.mem x allocs ==> Seq.mem x (objects2 0UL g)) /\
                                                    (G.is_vertex_set allocs) /\
                                                    (G.subset_vertices allocs 
                                                       (objects2 0UL g)) /\
                                                    (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                               (isGrayObject1 x g) \/
                                                                               (isBlackObject1 x g))}) 
                           : Tot (whites: G.vertex_list (*seq Usize.t*)
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
                                                        color_of_object1 x g == white)}) =
 let whites =  get_color_based_block_picker g allocs white in
 assert (Seq.equal allocs (get_allocated_block_addresses g));
 assert ((forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g)) /\
         (forall x. Seq.mem x (objects2 0UL g) /\
                               ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                      Seq.mem x allocs));
 assert (forall x. Seq.mem x allocs /\ color_of_object1 x g == white ==> Seq.mem x whites);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isWhiteObject1 x g ==>
                                                      Seq.mem x whites);
 assert (forall x. Seq.mem x whites ==> Seq.mem x (objects2 0UL g) /\ isWhiteObject1 x g);
 assert (forall x. Seq.mem x whites <==>
   Seq.mem x (objects2 0UL g) /\ isWhiteObject1 x g);
 assert (forall x. Seq.mem x whites ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (G.is_vertex_set whites);
 assert (forall x. Seq.mem x whites ==> Seq.mem x allocs);
 assert (G.subset_vertices whites allocs /\
          (G.subset_vertices whites (objects2 0UL g)));
 assert (forall x. Seq.mem x whites ==> color_of_object1 x g == white);
 assert (forall x. Seq.mem x whites <==> Seq.mem x allocs /\ color_of_object1 x g == white);
 assert (Seq.equal allocs (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x whites <==> Seq.mem x (get_allocated_block_addresses g) /\ color_of_object1 x g == white);
 whites

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

#reset-options "--split_queries always"

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

#push-options "--split_queries always"

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

#restart-solver

let rec is_fields_contents_within_limit2_lemma  (h_index: hp_addr) 
                                                (wz: wosize{is_fields_within_limit1 h_index wz}) 
                                                (wz': wosize{is_fields_within_limit1 h_index wz'})
                                                (g:heap) 
                                                (g':heap) 
                                          
                           : Lemma
                            (requires (wz == wz') /\
                                      (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}). 
                                                    
                                                    Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) == 
                                                    Usize.v (read_word g' (Usize.add h_index (Usize.mul i mword)))))
                                                                 
                            (ensures (is_fields_contents_within_limit2 h_index wz g == true <==>
                                      is_fields_contents_within_limit2 h_index wz' g' == true))
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


let rec check_all_block_fields_within_limit2 (g:heap{Seq.length (objects2 0UL g) > 0})
                                             (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                              (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x f' ==> 
                                                                 Seq.mem x (get_allocated_block_addresses g)) /\
                                                               (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g x)))})
                               :Tot (b: bool{b == true <==> (forall x. Seq.mem x f' ==> 
                                            is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)})
                                (decreases length f') =
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
             
               




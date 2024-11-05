module Spec.Graph3

open FStar.Seq
open FStar.Seq.Base
open FStar.Classical
open FStar.FunctionalExtensionality


let rec count l x =
 if length l = 0 then 0
 else
   (
     if (head l) = x then
       1 + count (tail l) x
     else
           count (tail l) x
   )

let rec count_lemma_helper (l:vertex_list)
                           (x:vertex_id)
                 : Lemma
                   (requires (count l x == 1))
                   (ensures (Seq.length l > 0 /\ x <> head l ==> count (tail l) x == 1))
                   (decreases length l) = 
 if length l = 0 then ()
 else
   (
     if (head l) = x then
      ()
     else
        count_lemma_helper (tail l) x   
   )
   
let rec is_vertex_set (l: seq vertex_id)
                  : Tot (bool)
            (decreases length l)= 
if length l = 0 then true else not(mem (head l) (tail l)) && is_vertex_set (tail l)


let rec count_zero_lemma (l: seq vertex_id)
                     (x:vertex_id {~(Seq.mem x l)})
              : Lemma 
                (ensures (count l x == 0)) 
                (decreases length l)= 
 if length l = 0 then ()
 else
  (
     if (head l) = x then
       ()
     else
      (
        assert (~(Seq.mem x (tail l)));
        count_zero_lemma (tail l) x;
        ()
      )

  )

let rec is_vertex_set_count_lemma (l: seq vertex_id)
                                  (x:vertex_id {Seq.mem x l})
                            : Lemma 
                              (requires is_vertex_set l)
                              (ensures count l x == 1)
                              (decreases length l) = 
 if length l = 0 then ()
 else
 (
   if head l = x then
     (
       assert (~(Seq.mem x (tail l)));
       count_zero_lemma (tail l) x;
       ()
     )
   else
    (
      is_vertex_set_count_lemma (tail l) x
    )
   
 )

let rec is_vertex_set_count_lemma1 (l: seq vertex_id)
                                   (x:vertex_id {Seq.mem x l})
                            : Lemma 
                              (requires is_vertex_set l /\ Seq.length l > 0)
                              (ensures count l x == 1)
                              (decreases length l) = 
 if length l = 0 then ()
 else
 (
   if head l = x then
     (
       assert (~(Seq.mem x (tail l)));
       count_zero_lemma (tail l) x;
       ()
     )
   else
    (
      is_vertex_set_count_lemma1 (tail l) x
    )
   
 )
  
 
let is_vertex_set_count_lemma_all l = 
Classical.forall_intro (Classical.move_requires (is_vertex_set_count_lemma l))


let is_vertex_set_count_lemma_all1 l = 
Classical.forall_intro (Classical.move_requires (is_vertex_set_count_lemma1 l))


let is_vertex_set_lemma (l: seq vertex_id)
                      : Lemma (ensures (is_vertex_set l /\ length l > 0 ==> is_vertex_set (tail l)))
                        (decreases length l) = ()

let is_vertex_set_cons hd l = 
 if length l = 0 then () else 
 (
   assert (~(Seq.mem hd l));
   lemma_tl hd l;
   let l'' = cons hd l in
   is_vertex_set_lemma l;
   assert (is_vertex_set (tail l));
   ()
 )

let is_vertex_set_lemma1 l = ()

let is_vertex_set_lemma2 l = () 

let slice_mem_helper_lemma (s: vertex_list{(Seq.length s) > 0})
                           (s': vertex_list{Seq.equal s' (Seq.slice s 0 (Seq.length s - 1))})
                           (x:vertex_id)
                  : Lemma
                    (requires (Seq.mem x s'))
                    (ensures (Seq.mem x s)) =
 Seq.lemma_mem_snoc s' (Seq.index s (Seq.length s - 1))

                    
let slice_mem_lemma (s: vertex_list{(Seq.length s) > 0})
                    (s': vertex_list{Seq.equal s' (Seq.slice s 0 (Seq.length s - 1))})
                : Lemma 
                  (ensures (forall x. Seq.mem x s' ==> Seq.mem x s))=
Classical.forall_intro (Classical.move_requires (slice_mem_helper_lemma s s'))


let slice_mem_helper_lemma_edge (s: edge_list{(Seq.length s) > 0})
                                (s': edge_list{Seq.equal s' (Seq.slice s 0 (Seq.length s - 1))})
                                (x:edge)
                  : Lemma
                    (requires (Seq.mem x s'))
                    (ensures (Seq.mem x s)) =
 Seq.lemma_mem_snoc s' (Seq.index s (Seq.length s - 1))

                    
let slice_mem_lemma_edge (s: edge_list{(Seq.length s) > 0})
                         (s': edge_list{Seq.equal s' (Seq.slice s 0 (Seq.length s - 1))})
                : Lemma 
                  (ensures (forall x. Seq.mem x s' ==> Seq.mem x s))=
Classical.forall_intro (Classical.move_requires (slice_mem_helper_lemma_edge s s'))


let vertex_set_uniqueness (l: seq vertex_id{length l > 0})
                   : Lemma
                     (requires (forall x. Seq.mem x l ==> count l x == 1))
                     (ensures (forall x. Seq.mem x (tail l) ==> count l x == 1)) = 
  ()

let vertex_set_uniqueness1 (l: seq vertex_id{length l > 0})
                   : Lemma
                     (requires (forall x. Seq.mem x l ==> count l x == 1))
                     (ensures (forall x. Seq.mem x (Seq.slice l 0 (length l - 1)) ==> count l x == 1)) = 
  slice_mem_lemma l (Seq.slice l 0 (length l - 1));
  ()                

let rec slice_uniqueness_lemma (s:vertex_set)
                              
                   : Lemma
                     (requires (length s > 0))
                     (ensures (is_vertex_set (slice s 0 (length s - 1)))) 
                     (decreases (length s)) = 
let tl_s = tail s in
  if length tl_s = 0 then
    () 
 else
 (
   assert (is_vertex_set tl_s);
   slice_uniqueness_lemma tl_s; // Calling this proves the lemma for tail s
   let s1 = slice s 0 (length s - 1) in
   let s' = slice tl_s 0 (length tl_s - 1) in
   assert (is_vertex_set s'); // Proved through induction hypothesis
   assert (~(mem (head s) (tl_s)));
   assert (~(mem (head s) (slice tl_s 0 (length tl_s))));
   slice_mem_lemma tl_s (slice tl_s 0 (length tl_s - 1)); // all elem in slice of tail s will be there in tail s
   assert (~(mem (head s) (slice tl_s 0 (length tl_s - 1)))); // so if head s is not there in tail s, then it will not be
                                                              // there in slice of tail s
   assert (is_vertex_set s1);
   assert (~(mem (head s1) (tail s1)));
   let e = index s (length s - 1) in
   assert (mem e s);
   
   ()
 )

let is_vertex_set_lemma3 l = 
  if not (is_vertex_set l) then ()
  else
  (
    assert (is_vertex_set l);
    if length l > 0 then
      slice_uniqueness_lemma l
    else
    ()
  )

let is_vertex_set_lemma4 l = ()

let rec is_vertex_set_lemma5 l = 
 if not (is_vertex_set l) then ()
  else
  (
    assert (is_vertex_set l);
    if length l > 0 then 
     (
      
      let s' = Seq.slice l 0 (Seq.length l - 1) in
      is_vertex_set_lemma3 l;
      if Seq.length (tail l) > 0 then
       (
         assert (Seq.index (Seq.tail l) (Seq.length (Seq.tail l) - 1) == Seq.index l (Seq.length l - 1));
         is_vertex_set_lemma5 (Seq.tail l);
         assert (~(Seq.mem (Seq.index (Seq.tail l) (Seq.length (Seq.tail l) - 1)) 
                 (Seq.slice (tail l) 0 (Seq.length (Seq.tail l) - 1))));
         assert (~(Seq.mem (Seq.index l (Seq.length l - 1)) 
                 (Seq.slice (tail l) 0 (Seq.length (Seq.tail l) - 1))));

         slice_mem_lemma (tail l) (slice (tail l) 0 (length (tail l) - 1)); 
         // all elem in slice of tail s will be there in tail s
         assert (~(mem (head l) (slice (tail l) 0 (length (tail l) - 1))));
         assert (~(mem (head l) (tail l)));
         assert (head l <> Seq.index l (length l - 1));
         assert (~(Seq.mem (Seq.index l (Seq.length l - 1)) (Seq.slice l 0 (Seq.length l - 1))));
         ()
       )
      else
       ()
     )
    else
    ()
  )

let is_vertex_set_lemma6 l i = ()

let is_vertex_set_lemma7 l i = ()

let rec is_edge_set  (e: seq edge)
             :  Tot (bool)
               (decreases length e)=
if length e = 0 then true else not(mem (head e) (tail e)) && is_edge_set (tail e)

let is_edge_set_lemma l = ()

let is_edge_set_lemma1 l = ()

let is_edge_set_lemma2 l = ()

let rec slice_uniqueness_lemma_edge (s:edge_set)
                     
                   : Lemma
                     (requires (length s > 0))
                     (ensures (is_edge_set (slice s 0 (length s - 1)))) 
                     (decreases (length s)) = 
let tl_s = tail s in
  if length tl_s = 0 then
    () 
 else
 (
   assert (is_edge_set tl_s);
   slice_uniqueness_lemma_edge tl_s; // Calling this proves the lemma for tail s
   let s1 = slice s 0 (length s - 1) in
   let s' = slice tl_s 0 (length tl_s - 1) in
   assert (is_edge_set s'); // Proved through induction hypothesis
   assert (~(mem (head s) (tl_s)));
   assert (~(mem (head s) (slice tl_s 0 (length tl_s))));
   slice_mem_lemma_edge tl_s (slice tl_s 0 (length tl_s - 1)); // all elem in slice of tail s will be there in tail s
   assert (~(mem (head s) (slice tl_s 0 (length tl_s - 1)))); // so if head s is not there in tail s, then it will not be
                                                              // there in slice of tail s
   assert (is_edge_set s1);
   assert (~(mem (head s1) (tail s1)));
   let e = index s (length s - 1) in
   assert (mem e s);
   
   ()
 )

let is_edge_set_lemma3 l = 
   if not (is_edge_set l) then ()
  else
  (
    assert (is_edge_set l);
    if length l > 0 then
      slice_uniqueness_lemma_edge l
    else
    ()
  )

#restart-solver 


let is_edge_set_lemma4 l = ()

let vertex_mem  (x: vertex_id)
                (vs:  vertex_list)
        : Tot (b:bool(*{b = true <==> (Seq.mem x vs /\ (exists i. Seq.index vs i = x))}*)) =
if mem x vs then
 let _ = mem_index x vs in
  true else 
  false  


let edge_mem (e:edge)
             (es: edge_list)
        : Tot (b:bool{b = true <==> mem e es}) =
if mem e es then true else false

(*let get_v_attribute #a #b g v =  index (g.v_map) (UInt32.v v) 
let get_e_attribute #a #b g e = index (g.e_map) (index_mem e (g.edge_set))
let set_v_attribute #a #b g v value = 
{
    vertices  = g.vertices;    
    edge_set  = g.edge_set;
    v_map     = upd g.v_map (UInt32.v v) value;      
    e_map     = g.e_map;        
}
let set_e_attribute #a #b g e value =
{
    vertices  = g.vertices;    
    edge_set  = g.edge_set;
    v_map     = g.v_map;      
    e_map     = upd g.e_map (index_mem e (g.edge_set)) value   
}
*)
let cardinality #a #b g
           : Tot nat =
let v = g.vertices in length v

let reachfunc  #a #b g x y r
        : Tot bool  = true

let rec subset_vertices  (s1: seq vertex_id{is_vertex_set s1})
                         (s2: seq vertex_id{is_vertex_set s2})
             :  Pure (bool)
                (requires True)
                (ensures (fun b -> (forall x. mem x s1 ==> mem x s2) <==> (b = true))) 
                (decreases (length s1))= 

if length s1 = 0 then true else mem (head s1) s2 && subset_vertices (tail s1) s2



let rec subset_edges (e1: seq edge)
                     (e2: seq edge)
            :   Pure (bool)
                (requires True)
                (ensures (fun b -> (forall x. mem x e1 ==> mem x e2) <==> (b = true))) 
                (decreases (length e1)) =
if length e1 = 0 then true else mem (head e1) e2 && subset_edges (tail e1) e2    

let edge_rel  #a #b g x y 
       : Tot (b:bool{b = true <==> mem_graph_edge g x y}) =
if (mem_graph_edge g x y) then true else false

let rec vertices_in_path  #a #b g x y r
                  : Tot (seq vertex_id) 
                    (decreases r)  = 
match r with
| ReachRefl  g x          -> empty
| ReachTrans  g x z y r_xz -> if ReachRefl? r_xz then 
                                empty 
                             else 
                                (lemma_tl z (vertices_in_path g x z r_xz); cons z (vertices_in_path g x z r_xz))

let rec subset_vertices_in_path #a #b g s1 s2
                         : Pure (bool)
                           (requires True)
                           (ensures (fun b -> (forall x. mem x s1 ==> mem x s2) <==> (b = true)))
                           (decreases (length s1))=
 if length s1 = 0 then true else mem (head s1) s2 && subset_vertices_in_path g (tail s1) s2

let subset_vertices_in_path_lemma #a #b g s1 s2
            : Lemma (ensures (forall x. (subset_vertices_in_path g s1 s2 /\ mem x s1) ==> mem x s2))
                    [SMTPat (subset_vertices_in_path g s1 s2)]  = ()

let rec get_index (s1:vertex_set)
                  (x:vertex_id{mem x s1}) 
       : Tot (n:nat{n < length s1 /\ index s1 n == x}) 
         (decreases (length s1)) =
if (head s1 = x) then 0 else 1 + get_index (tail s1) x

#push-options "--z3rlimit 100"

let rec remove (s1: vertex_set)
               (x: vertex_id{mem x s1})
  : Tot (r: vertex_set{ ~(mem x r)/\
                      (length r + 1 == length s1)/\
                     (forall y. y <> x ==> (mem y r <==> mem y s1))})
    (decreases (length s1))
  =  if head s1 = x then
      let _ = assert(is_vertex_set (tail s1)) in
      let _ = assert(~(mem x (tail s1))) in
      (tail s1)
    else
    (lemma_eq_elim (tail (cons (head s1) (remove (tail s1) x)))
              (remove (tail s1) x);
      cons (head s1) (remove (tail s1) x))
     (*(lemma_tl (head s1)(remove (tail s1) x);
       cons (head s1) (remove (tail s1) x))*)


let rec subset_lemma (s1: vertex_set)
                     (s2: vertex_set)
       :Lemma (requires (subset_vertices  s1 s2))
              (ensures (length s1 <= length s2))
               (decreases (length s1))
              [SMTPat (subset_vertices s1 s2)]
               = 

if length s1 = 0 then () else (assert (forall x. mem x s1 ==> mem x s2); 
let _ = assert (length (tail s1) <= length s1) in 
let _ = assert (mem (head s1) s2) in
let _ = assert (length (remove s2 (head s1)) <= length s2) in
let _ = assert (subset_vertices (tail s1) (remove s2 (head s1))) in
let _ = subset_lemma (tail s1) (remove s2 (head s1)) in 
())

let rec is_vertex_set_lemma8  (l: vertex_set) 
                          (x: vertex_id{mem x l})
                      :Lemma (ensures (is_vertex_set (remove l x))) 
                       (decreases length l) = 
 if head l = x then
  (
      let _ = assert(is_vertex_set (tail l)) in
      let _ = assert(~(mem x (tail l))) in
      ()
  )
    else
  (
      let tl = tail l in
      let hd = head l in
      let r_tl = remove tl x in
      assert (is_vertex_set tl);
      assert (mem x tl);
      is_vertex_set_lemma8 tl x;
      assert (is_vertex_set r_tl);
      lemma_eq_elim (tail (cons hd r_tl))
              (remove (tail l) x);
      assert (~(Seq.mem (head l) r_tl));
      let l1 = cons (head l) (remove (tail l) x) in
      assert (is_vertex_set l1);
      ()
   )
                      
let subset_equal (s1: seq vertex_id{is_vertex_set s1})
               (s2: seq vertex_id{is_vertex_set s2})
            : Lemma
              (requires (subset_vertices s1 s2) /\ (subset_vertices s2 s1))
              (ensures (Seq.length s1 == Seq.length s2)) = ()

#restart-solver 

let rec subset_of_each_other (s1: seq vertex_id{is_vertex_set s1})
                             (s2: seq vertex_id{is_vertex_set s2})
           :Lemma 
            (requires (subset_vertices s1 s2) /\ Seq.length s1 == Seq.length s2)
            (ensures (subset_vertices s2 s1)) 
            (decreases (length s1))= 
 
 if length s1 = 0 then ()
 else
 (
   assert (length s1 > 0);
   assert (length s2 > 0);
   assert (length s1 == length s2);
   assert (subset_vertices (tail s1) s2);
   assert (subset_vertices (tail s1) (remove s2 (head s1)));
   assert (length (tail s1) == length (remove s2 (head s1)));
   assert (is_vertex_set (tail s1));
   assert (is_vertex_set (remove s2 (head s1)));
   subset_of_each_other (tail s1) (remove s2 (head s1));
   assert (subset_vertices (remove s2 (head s1)) (tail s1));
   assert (forall x. mem x (remove s2 (head s1)) ==> mem x (tail s1));
   assert (~(mem (head s1) (tail s1)));
   assert (~(mem (head s1) (remove s2 (head s1))));
   assert (mem (head s1) s2);
   assert (mem (head s1) (cons (head s1) (tail s1)));
   assert (cons (head s1) (tail s1) == s1);
   assert (subset_vertices s2 s1);
   ()
 )


let vertices_in_sub_path_lemma #a #b g x y r
                                 
              : Lemma (ensures (forall w r_xw. (mem_graph_edge g w y /\ (r == ReachTrans g x w y r_xw) ==> 
                                                    subset_vertices_in_path g (vertices_in_path g x w r_xw) 
                                                                                (vertices_in_path g x y r)))) =
match r with
| ReachRefl  g x          -> ()
| ReachTrans  g x w y r_xw -> if ReachRefl? r_xw then 
                                ()
                             else 
                             (  let _ = assert (mem_graph_edge g w y) in
                                lemma_tl w (vertices_in_path g x w r_xw);
                                let _ = assert (subset_vertices_in_path g (vertices_in_path g x w r_xw) 
                                                                                (vertices_in_path g x y r)) in 
                                ())


                                                                                
let vertices_in_sub_path_lemma_mem  (#a:eqtype)
                                    (#b:eqtype) 
                                    (g:graph_state #a #b) 
                                    (x:vertex_id{mem_graph_vertex g x})
                                    (y:vertex_id{mem_graph_vertex g y})
                                    (r: reach g x y)
                        : Lemma (ensures(forall a z r_xz. mem a (vertices_in_path g x y r) /\ mem_graph_edge g z y /\ 
                                                r == ReachTrans g x z y r_xz ==> 
                                                  mem a (vertices_in_path g x z r_xz) \/ a = z)) 
                          (decreases r) = 
match r with
| ReachRefl  g x          -> ()
| ReachTrans  g x w y r_xw -> if ReachRefl? r_xw then 
                                ()
                             else 
                             (  let _ = assert (mem_graph_edge g w y) in
                                lemma_tl w (vertices_in_path g x w r_xw);
                                ()
                             )

let vertices_in_sub_path_lemma_reach (#a:eqtype)
                                     (#b:eqtype) 
                                     (g:graph_state #a #b) 
                                     (x:vertex_id{mem_graph_vertex g x})
                                     (y:vertex_id{mem_graph_vertex g y})
                                     (r: reach g x y)
                                     (z: vertex_id{mem_graph_vertex g z /\ mem_graph_edge g z y})
                                     (r_xz: reach g x z)
                                     
                                     (k: vertex_id{mem_graph_vertex g k /\ mem k (vertices_in_path g x y r)})
                                     
                                     (r1: reach g k z)
                                     (r2: reach g k y {r2 == ReachTrans g k z y r1})
                                     
                        : Lemma 
                          (requires ((r == ReachTrans g x z y r_xz) /\ (subset_vertices_in_path g (vertices_in_path g k z r1) 
                                                                     (vertices_in_path g x z r_xz))))
                          (ensures(subset_vertices_in_path g (vertices_in_path g k y r2) 
                                                             (vertices_in_path g x y r)))
                          (decreases r)  =  

match r with
 | ReachRefl  g x          -> ()
 | ReachTrans  g x z y r_xz -> if ReachRefl? r_xz then 
                                ()
                             else 
                             (
                               let _ = assert (subset_vertices_in_path g (vertices_in_path g k z r1) 
                                                                     (vertices_in_path g x z r_xz)) in
                               let _ = assert (forall v. mem v (vertices_in_path g k z r1) ==> mem v (vertices_in_path g x z r_xz)) in 

                               lemma_tl z (vertices_in_path g x z r_xz);
                               lemma_tl z (vertices_in_path g k z r1);
                               
                               let _ = assert((forall v. mem v (vertices_in_path g k y r2) /\ 
                                                        mem_graph_edge g z y /\
                                                        r2 == ReachTrans g k z y r1 /\
                                                        r == ReachTrans g x z y r_xz ==> mem v (vertices_in_path g x y r))) in
                               ()
                             )

#restart-solver

let rec path_length  (#a:eqtype)
                     (#b:eqtype) 
                     (g:graph_state #a #b) 
                     (x:vertex_id{mem_graph_vertex g x})
                     (y:vertex_id{mem_graph_vertex g y})
                     (r: reach g x y)
        :  Tot nat 
           (decreases r) =
match r with
| ReachRefl  g x -> 0
| ReachTrans g x z y  r_xz -> 1 + (path_length g x z r_xz)

(*x..........a...............z-y*)

(*If a......z is a subpath of x......z, then if we extend z with y through one edge, then a........z-y is a subpath of
 x........z-y. That is a......y is a subpath of x........y*)

let rec reach_vertices_in_path_lemma (#a:eqtype)
                                     (#b:eqtype) 
                                     (g:graph_state #a #b) 
                                     (x:vertex_id{mem_graph_vertex g x})
                                     (y:vertex_id{mem_graph_vertex g y})
                                     (r: reach g x y)
                         : Lemma (ensures (forall a. mem a (vertices_in_path g x y r) ==> 
                                             (exists (r1: reach g a y). reachfunc g a y r1 /\
                                          subset_vertices_in_path g (vertices_in_path g a y r1) 
                                                                      (vertices_in_path g x y r) /\
                                          (path_length g a y r1) < (path_length g x y r) ))) 
                          (decreases r)
= match r with
| ReachRefl g x -> ()
| ReachTrans g x z y r_xz ->  let _ = reach_vertices_in_path_lemma g x z r_xz in
                            let _ = assert (forall a. mem a (vertices_in_path g x z r_xz) ==> 
                                                 (exists (r1: reach g a z). reachfunc g a z r1 /\
                                               subset_vertices_in_path g (vertices_in_path g a z r1) 
                                                            (vertices_in_path g x z r_xz)  /\ 
                                                (path_length g a z r1) < (path_length g x z r_xz))) in
                             let _ = vertices_in_sub_path_lemma g x y r in 
                                   
                             let _ = assert (subset_vertices_in_path g (vertices_in_path g x z r_xz) 
                                                                           (vertices_in_path g x y r)) in
                             let _ = vertices_in_sub_path_lemma_mem g x y r in
                             let _ = assert (forall a. mem a (vertices_in_path g x y r) ==> 
                                                  mem a (vertices_in_path g x z r_xz) \/ a = z ) in
                             let _ = assert ((path_length g x y r) = 1 + (path_length g x z r_xz)) in
                               
                             let r2 = ReachTrans g z z y (ReachRefl g z) in
                             
                             assert (exists (r1:reach g z y).reachfunc g z y r1);
                             let _ = assert (reachfunc g y y (ReachRefl g y)) in
                             let aux_1 k 
                                   : Lemma 
                                     (requires (mem k (vertices_in_path g x z r_xz))) 
                                      
                                     (ensures (exists (r1: reach g k y). reachfunc g k y r1 /\ 
                                               (path_length g k y r1) < (path_length g x y r) /\
                                               subset_vertices_in_path g (vertices_in_path g k y r1) 
                                                                           (vertices_in_path g x y r)))
                                =
                                exists_elim (exists (r1: reach g k y). reachfunc g k y r1 /\ 
                                             path_length g k y r1 < path_length g x y r /\ 
                                             subset_vertices_in_path g (vertices_in_path g k y r1) 
                                                                         (vertices_in_path g x y r))
                                ()
                                (fun (r1: reach g k z{reachfunc g k z r1 /\ 
                                                        subset_vertices_in_path g (vertices_in_path g k z r1) 
                                                                                    (vertices_in_path g x z r_xz) /\ 
                                                        (path_length g k z r1) < (path_length g x z r_xz)}) -> 
                                  let r2 = ReachTrans g k z y r1 in
                                  let _ = vertices_in_sub_path_lemma g k y r2 in 
                                  (*x.........a.............z----y*)
                                  let _ = assert (subset_vertices_in_path g (vertices_in_path g k z r1) 
                                                                           (vertices_in_path g k y r2)) in
                                  (*a.........z C a........y*)                                         
                                  let _ = assert (subset_vertices_in_path g (vertices_in_path g k z r1) 
                                                                           (vertices_in_path g x z r_xz)) in
                                  (*a.........z C x..........z*)
                                  lemma_tl z (vertices_in_path g x z r_xz);
                                  lemma_tl z (vertices_in_path g k z r1);
                                  let _ = assert (subset_vertices_in_path g (vertices_in_path g k y r2) 
                                                                               (vertices_in_path g x y r)) in
                                  let _ = assert ((path_length g k z r1) < (path_length g x z r_xz)) in
                                  let _ = assert ((path_length g k y r2) = 1 + (path_length g k z r1)) in
                                  let _ = assert ((path_length g k y r2) < (path_length g x y r)) in
                                              ()) in
                             let _ = forall_intro (move_requires aux_1) in
                             let _ = assert (forall k. mem k (vertices_in_path g x z r_xz) ==> 
                                                       (exists (r1: reach g k y). reachfunc g k y r1 /\ 
                                                       (path_length g k y r1) < (path_length g x y r))) in
                             
                             let _ = assert ((mem z (vertices_in_path g x y r)) ==> ~(ReachRefl? r_xz)) in
                             let _ = assert ((mem z (vertices_in_path g x y r)) ==> 
                                                    (path_length g x z r_xz) >= 1) in
                             assert (exists (r1:reach g z y).reachfunc g z y r1);
                             assert ((forall a. mem a (vertices_in_path g x y r) ==> 
                                             (exists (r1: reach g a y). reachfunc g a y r1 /\
                                          subset_vertices_in_path g (vertices_in_path g a y r1) 
                                                                      (vertices_in_path g x y r) /\
                                          (path_length g a y r1) < (path_length g x y r) )));
                             ()                                        
                             
                           

let rec shortest_path_lemma (#a:eqtype)
                            (#t:eqtype) 
                            (g:graph_state #a #t) 
                            (s:vertex_id{mem_graph_vertex g s})
                            (b:vertex_id{mem_graph_vertex g b})
                            (r: reach g s b)
                            
                 :  Lemma 
                    (ensures (exists (rs: reach g s b). ~(vertex_mem s (vertices_in_path g s b rs)) /\ 
                             subset_vertices_in_path g (vertices_in_path g s b rs) 
                                                          (vertices_in_path g s b r)))
                    (decreases (path_length g s b r))                  = 
if not(mem s (vertices_in_path g s b r)) then
    let _ = assert (~(mem s (vertices_in_path g s b r))) in
    ()
  else
    let _ = reach_vertices_in_path_lemma g s b r in
    let _ = assert (exists (r1: reach g s b). reachfunc g s b r1 /\ 
                    subset_vertices_in_path g (vertices_in_path g s b r1) 
                                (vertices_in_path g s b r) /\ 
                   (path_length g s b r1) < (path_length g s b r)) in
    exists_elim (exists (rs: reach g s b). ~(mem s (vertices_in_path g s b rs)) /\ 
                   subset_vertices_in_path g (vertices_in_path g s b rs) 
                                               (vertices_in_path g s b r) )
    ()
    (fun (r1: reach g s b{reachfunc g s b r1 /\ 
        subset_vertices_in_path g (vertices_in_path g s b r1) 
                    (vertices_in_path g s b r) /\ 
       (path_length g s b r1) < (path_length g s b r)}) ->
        let _ = shortest_path_lemma g s b r1 in
        let _ = assert (exists (rs: reach g s b). ~(mem s (vertices_in_path g s b rs)) /\ 
                       subset_vertices_in_path g (vertices_in_path g s b rs) 
                                                   (vertices_in_path g s b r) ) in
        ()
      )

let reach_reflexive_constructor   (#a:eqtype)
                                  (#t:eqtype)
                                  (g:graph_state #a #t)
                                  (x: vertex_id{mem_graph_vertex g x})
                                
                   :   Tot (reach g x x) = 
ReachRefl g x

let edge_reach_constructor        (#a:eqtype)
                                  (#t:eqtype)
                                  (g:graph_state #a #t)
                                  (x: vertex_id{mem_graph_vertex g x})
                                  (y: vertex_id{mem_graph_vertex g y /\  mem_graph_edge g x y})
               
                   :   Tot (reach g x y) =
 ReachTrans g x x y (ReachRefl g x)
(* x..............x----------y *)
(* | ReachRefl x x| edge x y | *)
            

let reflex_lemma    (#a:eqtype)
                    (#t:eqtype)
                    (g:graph_state #a #t)
                    (x: vertex_id{mem_graph_vertex g x})
                    
           : Lemma
             (ensures (exists (r: (reach g x x)). (reachfunc g x x r))) =
 let r = ReachRefl g x in
            assert (reachfunc g x x r)

let reflex_lemma1   (#a:eqtype)
                    (#t:eqtype) 
                    (g:graph_state #a #t) 
                    (x: vertex_id{mem_graph_vertex g x}) 
                    
            : Lemma
              (ensures (reachfunc g x x (ReachRefl g x))) = ()

let rec reflex_lemma_list (#a:eqtype)
                          (#t:eqtype)
                          (g:graph_state #a #t)
                          (l: seq vertex_id{is_vertex_set l /\ subset_vertices l (g.vertices)})
           :  Lemma
              (ensures (forall x. mem x l ==> (exists (r: (reach g x x)). (reachfunc g x x r))))(decreases (length l))=
if length l = 0 then () else 
(let r = ReachRefl g (head l) in
 assert (reachfunc g (head l) (head l) r);
 reflex_lemma_list g (tail l))

let reachability_lemma   (#a:eqtype)
                         (#t:eqtype)
                         (g:graph_state #a #t) 
                         (x: vertex_id{mem_graph_vertex g x})
                         (y: vertex_id{mem_graph_vertex g y})
                         (r: reach g x y) 
                         
             :  Lemma
                (ensures (x = y  \/ (exists (z: vertex_id{mem_graph_vertex g z}) (r1: (reach g x z)). mem_graph_edge g z y))) =
match r with
  | ReachRefl  _ _ -> ()
  | ReachTrans  _ x z y _  -> ()

let add_to_vertex_set   (#a:eqtype)
                        (#t:eqtype)
                        (g:graph_state #a #t)
                        (y: vertex_id{mem_graph_vertex g y})
                        (l: vertex_set {subset_vertices l (g.vertices)})
             :  Tot (vertex_set) = 
if mem y l then l else (lemma_tl y l; cons y l)

let append_reach    (#a:eqtype)
                    (#t:eqtype)
                    (g:graph_state #a #t)
                    (x: vertex_id{mem_graph_vertex g x})
                    (y: vertex_id{mem_graph_vertex g y})
                    (l: seq vertex_id {is_vertex_set l /\  subset_vertices l (g.vertices)})
                 
          :     Lemma
                (requires ((exists (r1: reach g x y). reachfunc g x y r1) /\ (forall z. mem z l ==> 
                          (exists (r2: reach g x z). reachfunc g x z r2))))
                (ensures (forall z. vertex_mem z (add_to_vertex_set g y l) ==> (exists (r2: reach g x z). reachfunc g x z r2))) = 
let _ = assert ((exists (r1: reach g x y). reachfunc g x y r1)) in  
let _ = assert ((forall z. mem z l ==> 
                          (exists (r2: reach g x z). reachfunc g x z r2))) in
let l1 = add_to_vertex_set g y l in
lemma_tl y l;
()


#push-options "--z3rlimit 2000"

let rec successors_fn (#a:eqtype)
                      (#t:eqtype)
                      (g:graph_state #a #t)
                      (i: vertex_id {mem_graph_vertex g i})
                      (e: edge_set{(forall x. edge_mem x e ==> vertex_mem (fst x) (g.vertices) /\ 
                                     vertex_mem (snd x) (g.vertices))})
                                     
          :  Tot (sl : vertex_set{subset_vertices sl (g.vertices) /\
                                 (forall x. vertex_mem x sl <==> edge_mem (i,x) e)}) 
             (decreases (length e))=
if length e = 0 then empty else 
 (let f = fst (head e) in
  let s = snd (head e) in
  if f = i then
    (lemma_tl s (successors_fn g i (tail e));cons s (successors_fn g i (tail e)))
  else
    successors_fn g i (tail e))

#restart-solver


let rec test_snoc (i: nat)
                  (e: seq (nat & nat))
                                     
          :  Tot (sl : seq nat) 
             (decreases (length e))= 
if length e = 0 
then empty 
else 
   (
     let f = fst (head e) in
     let s = snd (head e) in
     let e' = test_snoc i (tail e) in
     if length e' = 0 
     then
     (*check whether the head is i. Since length e' = 0, we cannot snoc. if head = i then create a seq of legth 1. 
     else return empty*)
     (
      if f = i then (Seq.create 1 s) else
      empty
     )
     else
      if f = i 
      then 
        ( 
          lemma_tail_snoc e' s;
          let _ = assert (head (snoc e' s) == (head e')) in
          let _ = assert (tail (snoc e' s) == snoc (tail e') s) in
          snoc e' s)
        
      else
      (
        e'
     )
   )

#push-options "--z3rlimit 2000"

let snoc_helper_lemma1 (hd : vertex_id)
                      (tl_e' : vertex_set)
                      (s: vertex_id)
           : Lemma 
             (requires (~(mem hd tl_e') /\ (hd <> s) /\ ~(mem s tl_e')))
             (ensures (~(mem hd (snoc tl_e' s)))) = lemma_mem_snoc tl_e' s

let snoc_helper_lemma1_edge (hd : edge)
                            (tl_e' : edge_set)
                            (s: edge)
           : Lemma 
             (requires (~(mem hd tl_e') /\ (hd <> s) /\ ~(mem s tl_e')))
             (ensures (~(mem hd (snoc tl_e' s)))) = lemma_mem_snoc tl_e' s


let snoc_helper_lemma2 (hd : vertex_id)
                      (tl_e' : vertex_set)
                      (s: vertex_id)
           : Lemma 
             (requires (~(mem hd tl_e') /\ (hd <> s) /\ ~(mem s tl_e')))
             (ensures (~(mem hd (snoc tl_e' s)))) = lemma_mem_snoc tl_e' s

let snoc_helper_lemma2_edge (hd : edge)
                            (tl_e' : edge_set)
                            (s: edge)
           : Lemma 
             (requires (~(mem hd tl_e') /\ (hd <> s) /\ ~(mem s tl_e')))
             (ensures (~(mem hd (snoc tl_e' s)))) = lemma_mem_snoc tl_e' s
             
let rec snoc_uniqueness_lemma (s:vertex_id)
                              (e': vertex_set)
                   : Lemma
                     (requires (~(mem s e') /\ (length e' <> 0)))
                     (ensures (is_vertex_set (snoc e' s))) 
                     (decreases (length e')) = 
 let _ = lemma_tail_snoc e' s in
 let tl_e' = tail e' in
  if length tl_e' = 0 then
    () 
  else
    let _ = snoc_uniqueness_lemma s tl_e' in 
    let _ =  lemma_mem_snoc tl_e' s in 
    ()

let rec snoc_uniqueness_lemma_edge (s:edge)
                                   (e': edge_set)
                   : Lemma
                     (requires (~(mem s e') /\ (length e' <> 0)))
                     (ensures (is_edge_set (snoc e' s))) 
                     (decreases (length e')) = 
 let _ = lemma_tail_snoc e' s in
 let tl_e' = tail e' in
  if length tl_e' = 0 then
    () 
  else
    let _ = snoc_uniqueness_lemma_edge s tl_e' in 
    let _ =  lemma_mem_snoc tl_e' s in 
    ()

let snoc_unique_lemma s e' = snoc_uniqueness_lemma s e'

let snoc_unique_lemma_edge s e' = snoc_uniqueness_lemma_edge s e'

#push-options "--z3rlimit 100"

let rec successors_fn1 (#a:eqtype)
                       (#t:eqtype)
                      (g:graph_state #a #t)
                      (i: vertex_id {mem_graph_vertex g i})
                      (e: edge_set{(forall x. edge_mem x e ==> vertex_mem (fst x) (g.vertices) /\ 
                                     vertex_mem (snd x) (g.vertices))})
                                     
          :  Tot (sl : vertex_set{subset_vertices sl (g.vertices)  /\
                                 (forall x. vertex_mem x sl <==> edge_mem (i,x) e)}) 
             (decreases (length e))= 
if length e = 0 
then empty 
else 
   (
     let f = fst (head e) in
     let s = snd (head e) in
     let e' = successors_fn1 g i (tail e) in
     if length e' = 0 
     then
     (*check whether the head is i. Since length e' = 0, we cannot snoc. if head = i then create a seq of legth 1. 
     else return empty*)
     (
      if f = i then (Seq.create 1 s) else
      empty
     )
     else
      if f = i 
      then 
        ( if not (mem s e') then
          lemma_cons_snoc (head e') e' s;
          lemma_tail_snoc e' s;
          lemma_mem_snoc e' s;
          let e'' = snoc e' s in
          let _ = snoc_uniqueness_lemma s e' in
          e'')
       else
         e'
   )

let rec successors_fn2 i e =
if length e = 0 then empty else 
 (
  let f = fst (head e) in
  let s = snd (head e) in
  let sl' = successors_fn2  i (tail e) in
  assert (forall x. edge_mem (i,x) (tail e) ==> vertex_mem x sl');
  if f = i then
    (
     lemma_tl s sl';
     let sl =  cons s sl' in
     sl
    )
  else
    (
      sl'
    )
  )



let successors g i  =
let e = g.edge_set in
 successors_fn2 i e



let successors_successors_fn2_connect_lemma g i = ()
   

let rec successors_fn2_pick_second_lemma (i: vertex_id)
                                    (e: edge_list{(forall x. Seq.mem x e ==> (fst x == i))})
                         : Lemma 
                           (ensures successors_fn2 i e == pick_second e)
                           (decreases length e) = 
 if length e = 0 then () 
 else
 (
   let f = fst (head e) in
   let s = snd (head e) in
   assert (f == i);
   let sl' = successors_fn2  i (tail e) in
   successors_fn2_pick_second_lemma i (tail e);
   assert (successors_fn2 i (tail e) == pick_second (tail e));
   assert (sl' == pick_second (tail e));
   lemma_tl s sl';
   let sl =  cons s sl' in
   assert (sl == pick_second e);
   ()
 )

let rec successors_fn2_empty_if_no_fst_i_in_e (e1:edge_list)
                                              (i: vertex_id{~(exists x. Seq.mem x e1 /\ (fst x) == i)})
                        : Lemma
                          (ensures (successors_fn2 i e1 == Seq.empty))
                          (decreases length e1) = 
 if length e1 = 0 then () 
 else
 (
   let f = fst (head e1) in
   let s = snd (head e1) in
   assert (f <> i);
   let sl' = successors_fn2 i (tail e1) in
   assert (~(exists x. Seq.mem x (tail e1) /\ (fst x) == i));
   successors_fn2_empty_if_no_fst_i_in_e (tail e1) i;
   assert (successors_fn2 i (tail e1) == Seq.empty);
   lemma_tl s sl';
   let sl =  cons s sl' in
   assert (successors_fn2 i e1 == Seq.empty);
   ()
 )

let successors_fn2_empty_if_no_fst_tl_in_e (tl: vertex_list)
                                           (e:edge_list{forall x. Seq.mem x tl ==>
                                                                  ~(exists y. Seq.mem y e /\ (fst y) == x)})
                          : Lemma
                            (ensures (forall x. Seq.mem x tl ==> successors_fn2 x e == Seq.empty)) = 
 Classical.forall_intro (Classical.move_requires (successors_fn2_empty_if_no_fst_i_in_e e))

#restart-solver

#restart-solver

let seq_append_lemma (e: edge_list)
                     (e1:edge_list)
            : Lemma
              (requires length e == 0)
              (ensures Seq.append e e1 == e1) =
 Seq.lemma_eq_elim (Seq.append e e1) e1;
 ()
 

//#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

//#push-options "--z3rlimit 1000"

let rec successors_fn2_append_lemma (i: vertex_id)
                                    (e: edge_list (*{(forall x. Seq.mem x e ==> (fst x == i))}*))
                                    (e1:edge_list (*{~(exists x. Seq.mem x e1 /\ (fst x) == i)}*))
                                    (e2:edge_list{e2 == Seq.append e e1})
              : Lemma
                (ensures (successors_fn2 i e2 == Seq.append (successors_fn2 i e) (successors_fn2 i e1))) 
                (decreases length e) = 
 if length e = 0 then
 (
   Seq.lemma_eq_elim (Seq.append e e1) e1;
   Seq.lemma_eq_elim (Seq.append (successors_fn2 i e) (successors_fn2 i e1)) (successors_fn2 i e1);
   seq_append_lemma e e1;
   assert (Seq.append e e1 == e1);
   assert (Seq.append (successors_fn2 i e) (successors_fn2 i e1) == (successors_fn2 i e1));
   ()
 )
 else
 (
   Seq.lemma_eq_elim (Seq.append (tail e) e1) (tail e2);
   successors_fn2_append_lemma i (tail e) e1 (tail e2);
   assert (successors_fn2 i (tail e2) == Seq.append (successors_fn2 i (tail e)) (successors_fn2 i e1));
   let hd = Seq.head e in
   if fst hd = i then
   (
      assert (hd == Seq.head e2);
      Seq.lemma_eq_elim (cons (snd hd) (Seq.append (successors_fn2 i (tail e)) (successors_fn2 i e1)))
                        (Seq.append (successors_fn2 i e) (successors_fn2 i e1));
      assert (successors_fn2 i e2 == Seq.append (successors_fn2 i e) (successors_fn2 i e1));                  
      ()
         
   )
   else
   (
     Seq.lemma_eq_elim (Seq.append (successors_fn2 i (tail e)) (successors_fn2 i e1))
                       (Seq.append (successors_fn2 i e) (successors_fn2 i e1))
   )
 )

let successors_fn2_e2_is_successors_fn2_e_if_no_fst_i_in_e1 (i: vertex_id)
                                                            (e: edge_list {(forall x. Seq.mem x e ==> (fst x == i))})
                                                            (e1:edge_list{~(exists x. Seq.mem x e1 /\ (fst x) == i)})
                                                            (e2:edge_list{e2 == Seq.append e e1})
              : Lemma
                (successors_fn2 i e2 == successors_fn2 i e) =
 successors_fn2_append_lemma i e e1 e2;
 assert (successors_fn2 i e2 == Seq.append (successors_fn2 i e) (successors_fn2 i e1));
 successors_fn2_empty_if_no_fst_i_in_e e1 i;
 assert (successors_fn2 i e1 == Seq.empty);
 Seq.append_empty_r (successors_fn2 i e);
 assert (Seq.append (successors_fn2 i e) (successors_fn2 i e1) == (successors_fn2 i e));
 assert (successors_fn2 i e2 == successors_fn2 i e);
 ()
    

let successors_fn2_mem_lemma2_helper (e:edge_list)
                                     (e1:edge_list)
                                     (e2:edge_list{e2 == Seq.append e e1})
                                     (i: vertex_id{~(exists x. Seq.mem x e /\ (fst x) == i)})
                            : Lemma
                              (successors_fn2 i e2 == successors_fn2 i e1) = 
 
 successors_fn2_append_lemma i e e1 e2;
 assert (successors_fn2 i e2 == Seq.append (successors_fn2 i e) (successors_fn2 i e1));
 successors_fn2_empty_if_no_fst_i_in_e e i;
 assert (successors_fn2 i e == Seq.empty);
 Seq.append_empty_l (successors_fn2 i e1);
 assert (Seq.append (successors_fn2 i e) (successors_fn2 i e1) == (successors_fn2 i e1));
 assert (successors_fn2 i e2 == (successors_fn2 i e1));
 ()

let successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e (tl: vertex_list)
                                                             (e:edge_list{forall x. Seq.mem x tl ==>
                                                                  ~(exists y. Seq.mem y e /\ (fst y) == x)})
                                                             (e1:edge_list)
                                                             (e2:edge_list{e2 == Seq.append e e1}) 
              : Lemma
                (forall x. Seq.mem x tl ==> (successors_fn2 x e2 == successors_fn2 x e1)) =
  Classical.forall_intro (Classical.move_requires (successors_fn2_mem_lemma2_helper e e1 e2))

let rec subset_vertices_variant (s1: vertex_list{is_vertex_set s1}) 
                                (s2: vertex_list{is_vertex_set s2}) 
                :Pure (bool)
                (requires 
                      (forall x. Seq.mem x s1 ==> UInt.fits (Usize.v x - 8) Usize.n))
                       
                (ensures (fun b -> (forall x. Seq.mem x s1 ==> Seq.mem (previous x) s2) <==> (b = true))) 
                (decreases (length s1))=
if length s1 = 0 then true 
else
(
  assert (is_vertex_set s1);
  is_vertex_set_lemma s1;
  assert (is_vertex_set (tail s1));
  mem (previous (head s1)) s2 && subset_vertices_variant (tail s1) s2
)

let rec subset_variant_lemma (s1: vertex_set)
                             (s2: vertex_set)
       :Lemma (requires (forall x. Seq.mem x s1 ==> UInt.fits (Usize.v x - 8) Usize.n) /\
                        (subset_vertices_variant  s1 s2))
              (ensures (length s1 <= length s2))
               (decreases (length s1)) =  

if length s1 = 0 then () 
else 
(
 assert (forall x. mem x s1 ==> mem (previous x) s2); 
 let _ = assert (length (tail s1) <= length s1) in 
 let _ = assert (mem (previous (head s1)) s2) in
 let _ = assert (length (remove s2 (previous (head s1))) <= length s2) in
 is_vertex_set_lemma s1;
 is_vertex_set_lemma4 s1;
 assert (~(Seq.mem (head s1) (tail s1)));
 let _ = assert (subset_vertices_variant (tail s1) (remove s2 (previous (head s1)))) in
 subset_variant_lemma (tail s1) (remove s2 (previous (head s1))); 
()
)

let rec subset_of_each_other1 (s1: seq Usize.t{is_vertex_set s1})
                              (s2:  seq Usize.t{is_vertex_set s2})
           :Lemma 
            (requires (*(forall x. Seq.mem x s1 ==> is_hp_addr x) /\*)
                      (forall x. Seq.mem x s1 ==> UInt.fits (Usize.v x - 8) Usize.n) /\
                      (forall x. Seq.mem x s1 ==> Seq.mem (previous x) s2) /\ 
                      Seq.length s1 == Seq.length s2)
            (ensures (forall x. Seq.mem x s2 ==> Seq.mem (next x) s1)) 
            (decreases (length s1))= 
if length s1 = 0 then ()
 else
 (
   assert (length s1 > 0);
   assert (length s2 > 0);
   assert (length s1 == length s2);
   assert (forall x. Seq.mem x s1 ==> Seq.mem (previous x) s2);
   assert (forall x. Seq.mem x (tail s1) ==> Seq.mem (previous x) s2);
   assert (Seq.mem (previous (head s1)) s2);
   
   is_vertex_set_lemma s1; 
   is_vertex_set_lemma4 s1;
   assert (is_vertex_set (tail s1));
   assert (~(Seq.mem (head s1) (tail s1)));
   let l = remove s2 (previous (head s1)) in
   assert (forall x. Seq.mem x (tail s1) ==> Seq.mem (previous x) l);
   assert (Seq.length (tail s1) == Seq.length l);
   is_vertex_set_lemma8 s2 (previous (head s1));
   assert (is_vertex_set l);
  
   subset_of_each_other1 (tail s1) l;
   assert (forall x. Seq.mem x l ==> Seq.mem (next x) (tail s1));
   
   assert (~(mem (head s1) (tail s1)));
   assert (~(mem (previous (head s1)) l));
   assert (mem (previous (head s1)) s2);
   assert (mem (head s1) (cons (head s1) (tail s1)));
   assert (cons (head s1) (tail s1) == s1);
   assert (forall x. Seq.mem x s2 ==> Seq.mem (next x) s1);
   ()
 )


let successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e' (tl: vertex_list)
                                                             (e:edge_list{forall x. Seq.mem x tl  /\
                                                                          UInt.fits (Usize.v x + 8) Usize.n ==>
                                                                  ~(exists y. Seq.mem y e /\ (fst y) == next x)})
                                                             (e1:edge_list)
                                                             (e2:edge_list{e2 == Seq.append e e1}) 
                                   : Lemma
                                    (forall x. Seq.mem x tl ==> (successors_fn2 (next x) e2 == successors_fn2 (next x) e1)) = 
 Classical.forall_intro (Classical.move_requires (successors_fn2_mem_lemma2_helper e e1 e2));
 ()


let successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e''  (tl: vertex_list)
                                                                (e:edge_list{forall x. Seq.mem x tl  /\
                                                                          UInt.fits (Usize.v x + 8) Usize.n ==>
                                                                  ~(exists y. Seq.mem y e /\ (fst y) == next_wrapper x)})
                                                                (e1:edge_list)
                                                                (e2:edge_list{e2 == Seq.append e e1})
                                  : Lemma
                                    (forall x. Seq.mem x tl ==> (successors_fn2 (next_wrapper x) e2 == successors_fn2 (next_wrapper x) e1)) = 
 Classical.forall_intro (Classical.move_requires (successors_fn2_mem_lemma2_helper e e1 e2));
 ()


(*let f_address (h_index: hp_addr{UInt.fits (Usize.v h_index + Usize.v mword) Usize.n /\ (Usize.v h_index + Usize.v mword < heap_size)}) 
         : Tot (f:hp_addr{Usize.v f == Usize.v h_index + Usize.v mword})=
  let f_index = Usize.add h_index mword in
  assert (Usize.v f_index % Usize.v mword == 0);
  assert (Usize.v f_index >= 0);
  assert (is_hp_addr f_index);
  f_index*)
  
let rec edge_reach_lemma_succ_helper_lemma (#a:eqtype)
                                           (#t:eqtype)
                                           (g:graph_state #a #t)
                                           (e: seq (Usize.t & Usize.t){(forall x. mem x e ==> mem (fst x) (g.vertices) /\
                                                mem (snd x) (g.vertices)) (*/\ is_edge_set e*)})
                  
                            :  Lemma (ensures (forall x y. edge_mem (x,y) e ==> 
                                     reachfunc g x y (edge_reach_constructor g x y)))
                               (decreases (length e))= 
if length e = 0 then () else  edge_reach_lemma_succ_helper_lemma g (tail e)

let edge_reach_lemma_succ  (#a:eqtype)
                           (#t:eqtype)
                           (g:graph_state #a #t)
               
                         :  Lemma 
                            (ensures (forall x y. edge_mem(x,y) (g.edge_set) ==> 
                                      reachfunc g x y (edge_reach_constructor g x y))) = 
let e =  g.edge_set in
 edge_reach_lemma_succ_helper_lemma g e

let rec  succ_reach_lemma_helper (#a:eqtype)
                                 (#t:eqtype)
                                 (g:graph_state #a #t)
                                 (e: seq (Usize.t & Usize.t){(forall x. mem x e ==> mem (fst x) (g.vertices) /\
                                                mem (snd x) (g.vertices)) (*/\ is_edge_set e*)})
                                 (x: vertex_id{mem_graph_vertex g x})
             
                       : Lemma
                         (ensures (forall y. vertex_mem y (successors g x) ==> 
                                   reachfunc g x y (edge_reach_constructor g x y)))
                         (decreases (length e)) = 

if length e = 0 then () else
  succ_reach_lemma_helper g (tail e) x

let succ_reach_lemma   (#a:eqtype)
                       (#t:eqtype)
                       (g:graph_state #a #t)
                       (x: vertex_id{mem_graph_vertex g x})
                 
            :  Lemma
               (ensures (forall y. vertex_mem y (successors g x) ==> 
                             reachfunc g x y (edge_reach_constructor g x y))) =
let e = g.edge_set in
   succ_reach_lemma_helper g e x

let reach_lemma_transitive   (#a:eqtype)
                             (#t:eqtype)
                             (g:graph_state #a #t) 
                             (x: vertex_id{mem_graph_vertex g x})
                             (y: vertex_id{mem_graph_vertex g y /\ mem_graph_edge g x y})
                             (o: vertex_id{mem_graph_vertex g o})
                             (r: reach g o x)

              :   Lemma
                  (ensures (exists (z3: reach g o y). reachfunc g o y z3)) =
 assert (exists (r1: reach g o x). reachfunc g o x r1);
 let r2 = ReachTrans g o x y r in
 assert (reachfunc g o y r2)

let rec reach_lemma_transitive_list (#a:eqtype)
                                    (#t:eqtype)
                                     (g:graph_state #a #t)
                                     (x: vertex_id{mem_graph_vertex g x})
                                     (l: vertex_list{(forall x. Seq.mem x l ==> Seq.mem x (g.vertices)) /\ 
                                                     (forall y. vertex_mem y l ==> mem_graph_edge g x y)}) 
                                     (o: vertex_id{mem_graph_vertex g o})
                                     (r: reach g o x) 

              :   Lemma
                  (ensures (forall y. vertex_mem y l ==> 
                              (exists (z3: reach g o y). (reachfunc g o y z3)))) 
                  (decreases (length l))=
if length l = 0 then () else
    let r1 =  ReachTrans g o x (head l) r in
    reach_lemma_transitive_list g x (tail l) o r

let rec reachability_helper (#a:eqtype)
                            (#b:eqtype)
                            (g:graph_state #a #b)
                            (g':graph_state #a #b)
                            (root: vertex_id{mem_graph_vertex g root})
                            (x:vertex_id{mem_graph_vertex g x})
                            (p: reach g root x)
                                                  
                              : Lemma
                                (requires (g.vertices == g'.vertices /\ g.edge_set == g'.edge_set))
                                (ensures (exists (p1: reach g' root x).reachfunc g' root x p1)) 
                                (decreases p)= 
let _ = assert (g.vertices = g'.vertices /\ g.edge_set = g'.edge_set) in
match p with
        | ReachRefl  _ _  ->  let _ = assert (mem_graph_vertex g x) in 
                             let _ = assert (mem_graph_vertex g' x) in
                             let _ = assert (reachfunc g x x p) in
                             let _ = reflex_lemma g' x in
                             let _ = assert (exists (r: (reach g' x x)). (reachfunc g' x x r)) in
                             ()
      
        | ReachTrans g root w x r1  -> let _ = assert (mem_graph_vertex g x) in
                                   let _ = assert (mem_graph_vertex g root) in
                                   let _ = assert (mem_graph_vertex g w) in
                                   let _ = assert (mem_graph_vertex g' x) in
                                   let _ = assert (mem_graph_vertex g' root) in
                                   let _ = assert (mem_graph_vertex g' w) in
                                   let _ = assert (reachfunc g root x p) in
                                   let _ = assert (mem_graph_edge g w x) in
                                   let _ = assert (reachfunc g root w r1) in
                                   let _ = reachability_helper g g' root w r1 in
                                   let _ = assert (exists p. (reachfunc g' root w p)) in
                                   let _ = assert (exists (p:reach g' root w).reachfunc g' root w p) in
                                   let _ = assert (mem_graph_edge g' w x) in
                                   
                                   //Create witness for reach g' root w
                                   // use reach_lemma transitive g' root w x witness to conclude the proof
                                   exists_elim
                                   (exists (p1:reach g' root x).reachfunc g' root x p1)
                                   ()
                                   (fun (p: reach g' root w) -> let _ = reach_lemma_transitive g' w x root p in
                                                             let _ = assert (exists (z3: reach g' root x). reachfunc g' root x z3) in
                                                             () )
 
let reachability_helper1 (#a:eqtype)
                         (#b:eqtype)
                         (g:graph_state #a #b)
                         (g':graph_state #a #b)
                         (root: vertex_id{mem_graph_vertex g root})
                         (x:vertex_id{mem_graph_vertex g x})
                            
                                                  
                              : Lemma
                                (requires (g.vertices = g'.vertices /\ g.edge_set = g'.edge_set /\ 
                                                 (exists (p:reach g root x).reachfunc g root x p)))
                                (ensures (exists (p1: reach g' root x).reachfunc g' root x p1))   = 
exists_elim
(exists (p1:reach g' root x).reachfunc g' root x p1)
()
(fun (p: reach g root x) -> reachability_helper g g' root x p)

let reachability_non_dependent_on_attributes_lemma (#a:eqtype)
                                                   (#b:eqtype)
                                                   (g:graph_state #a #b)
                                                   (g':graph_state #a #b)
                                                   (root: vertex_id{mem_graph_vertex g root})
                                                  
                              : Lemma
                                (requires (g.vertices == g'.vertices /\ g.edge_set == g'.edge_set))
                                (ensures (forall x. mem_graph_vertex g x /\ 
                                            (exists (p: reach g root x).reachfunc g root x p) ==>
                                            (exists (p1: reach g' root x).reachfunc g' root x p1))) = 
let _ = assert (g.vertices == g'.vertices /\ g.edge_set == g'.edge_set) in
introduce forall x. mem_graph_vertex g x /\ (exists (p: reach g root x).reachfunc g root x p) ==>
                                            (exists (p1: reach g' root x).reachfunc g' root x p1)
with introduce _ ==> _
    with _. (
    assert ((exists (p: reach g root x).reachfunc g root x p));
    reachability_helper1 g g' root x;
    assert (exists (p1: reach g' root x).reachfunc g' root x p1)
)

let succ_reach_transitive_lemma    (#a:eqtype)
                                   (#t:eqtype)
                                   (g:graph_state #a #t)
                                   (o: vertex_id{mem_graph_vertex g o})
                                   (x: vertex_id{mem_graph_vertex g x})
                                   (r: reach g o x) 
                        
                   :   Lemma
                       (ensures (forall y. vertex_mem y (successors g x) ==> 
                                  (exists (r1: reach g o y).reachfunc g o y r1))) =
 let s = successors g x in
 let _ = succ_reach_lemma g x in
 assert (exists (r2: reach g o x).reachfunc g o x r2);
 let _ = reach_lemma_transitive_list g x s o r in
 ()


#restart-solver

let succ_reach_transitive_lemma1   (#a:eqtype)
                                   (#t:eqtype)
                                   (g:graph_state #a #t)
                                   (o: vertex_id{mem_graph_vertex g o})
                                   (x: vertex_id{mem_graph_vertex g x})
                                   
                     :  Lemma
                        (requires (exists (p: (reach g o x)). reachfunc g o x p))
                        (ensures (forall y. vertex_mem y (successors g x) ==> 
                                                  (exists (r1: reach g o y).reachfunc g o y r1))) =
 let _ = assert (exists (r2: reach g o x).reachfunc g o x r2) in
 let _ = succ_reach_lemma g x in
// let _ = assert (forall y. List.Tot.mem y (successors g x) ==> (exists (r1: reach g x y).reachfunc g x y r1)) in
 let l = successors g x in
 if length l = 0 then () else
    exists_elim
             (forall y. mem y l ==> (exists (r1: reach g o y).reachfunc g o y r1))
             ()
             (fun (p: reach g o x) ->
                                       match p with
                                        | ReachRefl  _ _  -> ()
                                        | ReachTrans  _ _ _ _ _  -> reach_lemma_transitive_list g x l o p)
 
(*x ---------------------------------------- y*)
(*| ---------------------r1------------------|*)
(*x - z ------------------------------------ y*)
(*x - z -------------------------------- p - y*)

(*ReachTrans x - z ---------- p - y *)
(*           | ----r3-------- | - | *)
(*           | ----------r1------ | *)
                                        
#push-options "--z3rlimit 2000"

let rec succ_reach_transitive_lemma3  (#a:eqtype)
                                      (#t:eqtype)
                                      (g:graph_state #a #t)
                                      (x: vertex_id{mem_graph_vertex g x})
                                      (y: vertex_id{mem_graph_vertex g y})
                                      (r: reach g x y{ReachRefl? r = false})

                      :  Lemma
                         (ensures (exists (z: vertex_id{mem z (successors g x)}). 
                                     (exists (r2: reach g z y).reachfunc g z y r2 /\
                                        subset_vertices_in_path g (vertices_in_path g z y r2) 
                                                                               (vertices_in_path g x y r) /\
                                        (~(ReachRefl? r2) ==> mem z (vertices_in_path g x y r)) /\
                                        (ReachRefl? r2 ==> (mem_graph_edge g x y) /\ r ==
                                        ReachTrans g x x y (ReachRefl g x)))))
                                        (decreases r) =
match r with
| ReachTrans g x w y r_xw -> if ReachRefl? r_xw (*path length = 0*) then
                                    let _ = assert (mem_graph_edge g x y) in
                                    let _ = assert (mem y (successors g x)) in
                                    let r_xy = ReachRefl g y in
                                    let _ = assert (reachfunc g y y r_xy) in
                                    ()
                                else
                                    (*x.........w...........y*)
                                    let _ = succ_reach_transitive_lemma3 g x w r_xw in

                                    (*Now, from x........w, there exists a successor z of x through which w is reachable*)
                                    (*Using the successor z, we need to prove z......y is also reachable*)
                                    exists_elim
                                    (exists (z: vertex_id{mem z (successors g x)}). 
                                                   (exists  (r_zy: reach g z y).reachfunc g z y r_zy /\
                                                    mem z (successors g x ) /\ 
                                                    subset_vertices_in_path g (vertices_in_path g z y r_zy) 
                                                                (vertices_in_path g x y r) /\
                                                    (~(ReachRefl? r_zy) ==> mem z (vertices_in_path g x y r)) /\
                                                    (ReachRefl? r_zy ==> (mem_graph_edge g x y) /\ r == 
                                                                 ReachTrans g x x y (ReachRefl g x))))
                                    ()
                                    (fun (z: vertex_id{mem z (successors g x) /\ 
                                                   (exists (r_zw: reach g z w). reachfunc g z w r_zw /\
                                                   subset_vertices_in_path g (vertices_in_path g z w r_zw) 
                                                               (vertices_in_path g x w r_xw) /\
                                                   (~(ReachRefl? r_zw) ==> mem z (vertices_in_path g x w r_xw)) /\
                                                   (ReachRefl? r_zw ==> (mem_graph_edge g x w) /\ r_xw ==
                                                             ReachTrans g x x w (ReachRefl g x)))}) -> 
                                     exists_elim
                                      (exists  (r_zy: reach g z y).reachfunc g z y r_zy /\ 
                                       mem z (successors g x) /\
                                       subset_vertices_in_path g (vertices_in_path g z y r_zy) 
                                                                   (vertices_in_path g x y r) /\
                                       (~(ReachRefl? r_zy) ==> mem z (vertices_in_path g x y r)) /\
                                       (ReachRefl? r_zy ==> (mem_graph_edge g x y) /\ r == 
                                                          ReachTrans g x x y (ReachRefl g x)))
                                      ()
                                      (fun (r_zw: reach g z w{subset_vertices_in_path g (vertices_in_path g z w r_zw) 
                                                                                          (vertices_in_path g x w r_xw) /\
                                       (*r_zw does not have zero length ==> mem z (x........w)*)                                                  
                                       (~(ReachRefl? r_zw) ==> mem z (vertices_in_path g x w r_xw)) /\
                                       (*r_zw has zero length ==> x-w is an edge and r_xw = x..............x-w*)
                                                                                          (*|...Refl.......|*)
                                                                                          (*|......Trans.....|*)
                                       (ReachRefl? r_zw ==> (mem_graph_edge g x w) /\ r_xw == 
                                                              ReachTrans g x x w (ReachRefl g x))}) ->
                                                              
                                            let _ = assert (~(ReachRefl? r_zw) ==> mem z (vertices_in_path g x w r_xw)) in  
                                            let _ = assert (ReachRefl? r_zw ==> (mem_graph_edge g x w) /\ r_xw == 
                                                              ReachTrans g x x w (ReachRefl g x)) in
                                            let _ = assert (subset_vertices_in_path g (vertices_in_path g z w r_zw) 
                                                                                          (vertices_in_path g x w r_xw)) in                 
                                            let r_zy = ReachTrans g z w y r_zw in 
                                            let _ = assert (mem z (successors g x)) in
                                            
                                            let _ = vertices_in_sub_path_lemma g x y r in
                                            let _ = assert (subset_vertices_in_path g (vertices_in_path g z w r_zw) 
                                                                                      (vertices_in_path g x w r_xw)) in
                                            let _ = assert (mem_graph_edge g w y) in
                                           // let _ = vertices_in_sub_path_lemma_succ_reach g x y r w r_xw z r_zw r_zy in
                                            lemma_tl w (vertices_in_path g z w r_zw);
                                            lemma_tl w (vertices_in_path g x w r_xw);
                                            let _ = assert (subset_vertices_in_path g (vertices_in_path g z y r_zy) 
                                                                                      (vertices_in_path g x y r)) in
                                           
                                            let _ = assert (ReachRefl? r_zw ==> vertices_in_path g x y r = cons z empty) in
                                            let _ = assert ((ReachRefl? r_zw ==> (mem_graph_edge g x w) /\ r_xw == 
                                                              ReachTrans g x x w (ReachRefl g x))) in
                                            let _ = assert (~(ReachRefl? r_zw) ==> mem z (vertices_in_path g x w r_xw)) in
                                            ()
                                       
                                      )
                                    )
  
(*Set operations and lemmas implemented on lists for graph manipulation*****************************************************)

let graph_subset_itself (#a:eqtype)
                        (#t:eqtype) 
                        (g:graph_state #a #t) 
                        : Lemma (ensures (subset_vertices g.vertices g.vertices)) = ()
                      
let empty_is_subset_of_all_sets (#a:eqtype)
                                (#t:eqtype) 
                                (g:graph_state #a #t)
       : Lemma (ensures (forall s. subset_vertices s g.vertices ==> subset_vertices (empty) s /\ 
                                               subset_vertices empty g.vertices)) = ()

let createEmptySet   (#a:eqtype)
                     (#t:eqtype) 
                     (g:graph_state #a #t) 
         : vs: vertex_set{subset_vertices vs (g.vertices)} = empty 

let empty_set_mem   (vl: vertex_set {vl == empty}) 
                    (r: vertex_set) 
     : Lemma (ensures (forall (x:vertex_id) . ((mem x vl) ==> ~(mem x r)) /\ ((mem x r) ==> ~ (mem x vl)))) = ()
      
let nonEmpty_set (s: vertex_set) 
            : Tot bool = if (length s <> 0) then true else false 

let is_emptySet (s: vertex_set)
            : Tot bool = if length s = 0 then true else false 

let empty_set_subset_all_sets   (s: vertex_set{is_emptySet s})
                                (vl: vertex_set)
                : Lemma (subset_vertices s vl) = ()

let negation_nonEmpty_implies_empty (s: vertex_set) 
                : Lemma (~(nonEmpty_set s) ==> is_emptySet s) = ()

let get_head    (#a:eqtype)
                (#t:eqtype)
                (g:graph_state #a #t)
                (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})
        : Tot (x: vertex_id{mem_graph_vertex g x /\ vertex_mem x s /\ (x == index s 0)}) = head s

let get_tail    (#a:eqtype)
                (#t:eqtype) 
                (g:graph_state #a #t) 
                (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})
            : Tot (s': vertex_set{subset_vertices s' (g.vertices) /\ (forall x. vertex_mem x s' ==> vertex_mem x s) /\
                       equal s' (tail s)}) = tail s

let get_last_elem g s = index s (length s - 1)


#push-options "--z3rlimit 100"

let get_first g s = 
 let s' = slice s 0 (length s - 1) in
 let _ = slice_mem_lemma s s' in
 assert (forall x. Seq.mem x s' ==> Seq.mem x s);
 assert (is_vertex_set s);
 if length s' > 0 then
   (
     lemma_tail_snoc s' (index s (length s - 1));
     lemma_mem_snoc s' (index s (length s - 1));
     slice_uniqueness_lemma s;
     assert (forall x. Seq.mem x s /\ (x <> (index s (length s - 1))) ==> Seq.mem x s');
     s'
   )
 else
 (
  s'
 )

let head_tail_set_connect_lemma   (#a:eqtype)
                                  (#t:eqtype) 
                                  (g:graph_state #a #t) 
                                  (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})
                : Lemma 
                  (ensures (forall c. vertex_mem c r /\ ~(vertex_mem c (get_tail g r)) ==> c = (get_head g r))) = ()

let last_first_set_connect_lemma_helper g r c = ()

let rec last_first_set_connect_lemma2 (#a:eqtype)
                                      (#t:eqtype)
                                      (g:graph_state #a #t)
                                      (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})
                                 
                 :Lemma 
                  (ensures (~(vertex_mem (get_last_elem g r) (get_first g r))))
                  (decreases (length r))= 

 let f = get_first g r in
 let tl = tail r in
 assert (is_vertex_set f);
 assert (is_vertex_set tl);
 if length tl > 0 then
   (
    last_first_set_connect_lemma2 g tl; // Keep the below asserts to know the proof flow
    assert (~(vertex_mem (get_last_elem g tl) (get_first g tl)));
    assert (mem (get_last_elem g tl) tl);
    assert (forall x. mem x tl ==> x <> head r);
    assert ((get_last_elem g tl) <> head r);
    ()
   )
 else
 ()



let last_first_set_connect_lemma g r = 
 Classical.forall_intro (Classical.move_requires (last_first_set_connect_lemma_helper g r))
 
  
let head_tail_set_connect_lemma1   (#a:eqtype)
                                   (#t:eqtype) 
                                   (g:graph_state #a #t) 
                                   (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})
                 : Lemma 
                  (ensures (forall c. vertex_mem c r /\ c <> (get_head g r) ==> vertex_mem c (get_tail g r))) = ()

let last_first_set_connect_lemma1_helper g r c = ()

let last_first_set_connect_lemma1 g r = ()

let get_head_mem_lemma    (#a:eqtype)
                          (#t:eqtype) 
                          (g:graph_state #a #t) 
                          (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})
                : Lemma (ensures (~(vertex_mem (get_head g s) (get_tail g s)))) = ()

//#restart-solver 

let get_tail_mem_lemma   (#a:eqtype)
                         (#t:eqtype) 
                         (g:graph_state #a #t) 
                         (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})
                         (vl: vertex_set{subset_vertices s (g.vertices) /\ (forall x. vertex_mem x s ==> ~(vertex_mem x vl))})
                :  Lemma (ensures (forall x. vertex_mem x (get_tail g s) ==> ~(vertex_mem x vl))) = ()

let get_tail_length_lemma   (#a:eqtype)
                            (#t:eqtype) 
                            (g:graph_state #a #t) 
                            (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})
                            
                : Lemma (ensures (cardinal1 (get_tail g s) < cardinal1 s)) = ()   
                    
let get_last_mem_lemma g s = 
  assert (is_vertex_set s);
  assert (is_vertex_set (tail s));
  let e = get_last_elem g s in
  let s' = get_first g s in
  assert (is_vertex_set s');
  last_first_set_connect_lemma2 g s;
  assert (~(mem e s'));
  ()

let get_first_mem_lemma  (#a:eqtype)
                         (#t:eqtype) 
                         (g:graph_state #a #t) 
                         (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})
                         (vl: vertex_set{subset_vertices s (g.vertices) /\ (forall x. vertex_mem x s ==> ~(vertex_mem x vl))}) 
                  :  Lemma (ensures (forall x. vertex_mem x (get_first g s) ==> ~(vertex_mem x vl)))  = 
 assert (forall x. vertex_mem x (get_first g s) ==> ~(vertex_mem x vl));  
 ()

let get_first_length_lemma  (#a:eqtype)
                            (#t:eqtype) 
                            (g:graph_state #a #t) 
                            (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})
                            
                  : Lemma (ensures (cardinal1 (get_first g s) < cardinal1 s)) = () 
                    
let insert_to_vertex_set_cons (#a:eqtype)
                              (#t:eqtype) 
                              (g:graph_state #a #t) 
                              (x: vertex_id{mem_graph_vertex g x}) 
                              (s: vertex_set{subset_vertices s (g.vertices)}) 
                            
                      : Tot(s':vertex_set{subset_vertices s' (g.vertices) /\ (cardinal1 (g.vertices) >= cardinal1 s') /\ 
                                               (subset_vertices s s')}) =
 if mem x s then s else (lemma_tl x s;cons x s)

let insert_to_vertex_set_snoc (#a:eqtype)
                              (#t:eqtype) 
                              (g:graph_state #a #t) 
                              (x: vertex_id{mem_graph_vertex g x}) 
                              (s: vertex_set{subset_vertices s (g.vertices)}) 
                            
                      : Tot(s':vertex_set{(subset_vertices s' (g.vertices)) /\ 
                                          (cardinal1 (g.vertices) >= cardinal1 s') /\ 
                                          (subset_vertices s s') /\ 
                                          (vertex_mem x s') /\
                                          (~(exists y. (Seq.mem y s') /\ ~(Seq.mem y s) /\ y <> x))}) = 
 if mem x s then 
 (
   let s' = s in
   assert (~(exists y. (Seq.mem y s') /\ ~(Seq.mem y s) /\ y <> x));
   s'
 )
 else
 ( 
   if length s = 0 then 
     (
       let s' = Seq.create 1 x in
       assert (~(exists y. (Seq.mem y s') /\ ~(Seq.mem y s) /\ y <> x));
       s'
     ) 
   else 
   (
      lemma_tail_snoc s x;
      snoc_uniqueness_lemma x s;
      lemma_mem_snoc s x; 
      let s' = snoc s x in
      assert (~(exists y. (Seq.mem y s') /\ ~(Seq.mem y s) /\ y <> x));
      s'
   )
)

let insert_to_vertex_set #a #t g x s  = 
     insert_to_vertex_set_snoc g x s



let reach_singleton   (#a:eqtype)
                      (#t:eqtype) 
                      (g:graph_state #a #t) 
                      (x: vertex_id{mem_graph_vertex g x})
                      (r : vertex_set{r == insert_to_vertex_set g x (createEmptySet g)}) 
             :  Lemma (ensures (forall y. vertex_mem y r ==> (exists (z1: reach g x y). reachfunc g x y z1))) = 
let _ = assert (cardinal1 r == 1) in
let _ = assert (mem x r) in
let _ = reflex_lemma g x in
let _ = assert (exists (z1: reach g x x). reachfunc g x x z1) in
()


#restart-solver

let reach_empty (#a:eqtype)
                (#t:eqtype) 
                (g:graph_state #a #t) 
                (x: vertex_id{mem_graph_vertex g x})
                (vl: vertex_set{subset_vertices vl (g.vertices) /\ vl == empty})
        : Lemma (ensures (forall y. vertex_mem y vl ==> (exists (z1: reach g x y). reachfunc g x y z1))) = ()

let reach_from_x_equals_reach_from_singleton_x_set   (#a:eqtype)
                                                     (#t:eqtype) 
                                                     (g:graph_state #a #t) 
                                                     (x: vertex_id{mem_graph_vertex g x})
                                                     (r : vertex_set{r == insert_to_vertex_set g x (createEmptySet g)}) 
        : Lemma (ensures (forall y (z2: reach g x y). (reachfunc g x y z2) ==> 
                            (exists p (z3: reach g p y). reachfunc g p y z3 /\ vertex_mem p r))) = 
let _ = reflex_lemma g x in ()
                            
let insert_to_vertex_set_lemma   (#a:eqtype)
                                 (#t:eqtype) 
                                 (g:graph_state #a #t) 
                                 (x: vertex_id{mem_graph_vertex g x}) 
                                 (vl: vertex_set{subset_vertices vl (g.vertices)}) 
                            
                  : Lemma(ensures (forall y. vertex_mem y (insert_to_vertex_set g x vl) ==> vertex_mem y vl \/ y = x)) = 
     

if mem x vl then ()
 else
 ( if length vl = 0 
   then 
     ()
   else 
   (lemma_tail_snoc vl x;snoc_uniqueness_lemma x vl;lemma_mem_snoc vl x; ())
 )

let insert_to_vertex_set_nonEmpty_lemma   (#a:eqtype)
                                          (#t:eqtype) 
                                          (g:graph_state #a #t) 
                                          (x: vertex_id{mem_graph_vertex g x}) 
                                          (s: vertex_set{subset_vertices s (g.vertices)}) 
                         : Lemma (ensures nonEmpty_set (insert_to_vertex_set g x s)) = 
if mem x s then ()
 else
 ( if length s = 0 
   then 
     ()
   else 
   (lemma_tail_snoc s x;snoc_uniqueness_lemma x s;lemma_mem_snoc s x; ())
 )

let insert_to_vertex_set_head_tail_mem_neg_lemma  (#a:eqtype)
                                                  (#t:eqtype) 
                                                  (g:graph_state #a #t) 
                                                  (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r}) 
                                                  (b: vertex_id{mem_graph_vertex g b})
                      : Lemma (requires (b <> get_head g r /\ ~(vertex_mem b (get_tail g r))))
                              (ensures (~(vertex_mem b r))) = ()

let insert_to_vertex_set_last_first_mem_neg_lemma g r b = ()

let insert_to_vertex_set_head_tail_mem_lemma   (#a:eqtype)
                                               (#t:eqtype) 
                                               (g:graph_state #a #t) 
                                               (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r}) 
                                               (vl: vertex_set{subset_vertices vl (g.vertices)}) 

          :  Lemma (ensures (((vertex_mem (get_head g r) vl) /\
                             (forall y. vertex_mem y (get_tail g r) ==> vertex_mem y vl)) ==> subset_vertices r vl)) = ()
           
let insert_to_vertex_set_last_first_mem_lemma g r vl = ()

let insert_to_vertex_set_reach_lemma   (#a:eqtype)
                                       (#t:eqtype) 
                                       (g:graph_state #a #t) 
                                       (o: vertex_id{mem_graph_vertex g o}) 
                                       (x: vertex_id{mem_graph_vertex g x /\ (exists (z1: reach g o x). reachfunc g o x z1)}) 
                                       (vl: vertex_set{subset_vertices vl (g.vertices) /\
                                                         (forall x. vertex_mem x vl ==> 
                                                           (exists (z1: reach g o x). reachfunc g o x z1))}) 

                                 :  Lemma
                                    (ensures (forall y. vertex_mem y (insert_to_vertex_set g x vl)
                                             ==> (exists (z1: reach g o y). reachfunc g o y z1))) = 
if mem x vl then ()
 else
 ( if length vl = 0 
   then 
     ()
   else 
   (lemma_tail_snoc vl x;snoc_uniqueness_lemma x vl;lemma_mem_snoc vl x; ())
 )

let insert_to_vertex_set_reach_lemma_root_set (#a:eqtype)
                                              (#t:eqtype) 
                                              (g:graph_state #a #t) 
                                              (o: vertex_id{mem_graph_vertex g o}) 
                                              (x: vertex_id{mem_graph_vertex g x /\ (exists (z1: reach g o x). reachfunc g o x z1)}) 
                                              (vl: vertex_set{subset_vertices vl (g.vertices)})
                                              (root_set : vertex_set{subset_vertices root_set (g.vertices)  /\
                                                 vertex_mem o root_set /\
                                                 (forall x. vertex_mem x vl ==> (exists o (z1: reach g o x). vertex_mem o root_set /\
                                                              reachfunc g o x z1))})

                                 :  Lemma
                                    (ensures (forall y. vertex_mem y (insert_to_vertex_set g x vl)
                                             ==> (exists o (z1: reach g o y). reachfunc g o y z1 /\ vertex_mem o root_set))) = 
if mem x vl then ()
 else
 ( if length vl = 0 
   then 
     ()
   else 
   (
     lemma_tail_snoc vl x;snoc_uniqueness_lemma x vl;lemma_mem_snoc vl x; ())
   )

let insert_to_vertex_set_mem_lemma (#a:eqtype)
                                   (#t:eqtype) 
                                   (g:graph_state #a #t) 
                                   (x: vertex_id{mem_graph_vertex g x}) 
                                   (vl: vertex_set{subset_vertices vl (g.vertices)}) 

                                    : Lemma
                                       (requires (~(vertex_mem x vl)))
                                       (ensures (vertex_mem x (insert_to_vertex_set g x vl))) = 
 if mem x vl then ()
 else
 ( if length vl = 0 
   then 
     ()
   else 
   (
     lemma_tail_snoc vl x;snoc_uniqueness_lemma x vl;lemma_mem_snoc vl x; ())
   )

let insert_to_vertex_set_length_lemma     (#a:eqtype)
                                          (#t:eqtype) 
                                          (g:graph_state #a #t) 
                                          (x: vertex_id{mem_graph_vertex g x}) 
                                          (vl: vertex_set{subset_vertices vl (g.vertices)}) 

                                   :  Lemma
                                       (requires (~(vertex_mem x vl)))
                                       (ensures (cardinal1 (insert_to_vertex_set g x vl) > cardinal1 vl)) = 
if mem x vl then ()
 else
 ( if length vl = 0 
   then 
     ()
   else 
   (
     lemma_tail_snoc vl x;snoc_uniqueness_lemma x vl;lemma_mem_snoc vl x; ())
   )

let insert_to_vertex_set_mem_negation_lemma   (#a:eqtype)
                                              (#t:eqtype) 
                                              (g:graph_state #a #t) 
                                              (x: vertex_id{mem_graph_vertex g x}) 
                                              (vl: vertex_set{subset_vertices vl (g.vertices)}) 
                                              (s: vertex_set{subset_vertices vl (g.vertices)}) 

                                    : Lemma
                                       (requires ((forall y. vertex_mem y vl ==> ~(vertex_mem y s)) /\ ~(vertex_mem x s)))
                                       (ensures (forall y. vertex_mem y (insert_to_vertex_set g x vl) ==> ~(vertex_mem y s))) = 
if mem x vl then ()
 else
 ( if length vl = 0 
   then 
     ()
   else 
   (
     lemma_tail_snoc vl x;snoc_uniqueness_lemma x vl;lemma_mem_snoc vl x; ())
   )

let rec union_vertex_sets_cons (#a:eqtype)
                               (#t:eqtype) 
                               (g:graph_state #a #t) 
                               (l1: vertex_set{subset_vertices l1 (g.vertices) }) 
                               (l2: vertex_set{subset_vertices l2 (g.vertices)}) 
             
                       : Tot(l: vertex_set{(forall x. vertex_mem x l <==> vertex_mem x l1 \/ vertex_mem x l2) /\ 
                                subset_vertices l (g.vertices)}) 
                                (decreases (length l1)) = 

if length l1 = 0 then l2 
  else
   if mem (head l1) l2 then 
      union_vertex_sets_cons g (tail l1) l2
   else
      (lemma_tl (head l1) (union_vertex_sets_cons g (tail l1) l2);
       cons (head l1) (union_vertex_sets_cons g (tail l1) l2))

let rec union_vertex_sets_snoc (#a:eqtype)
                               (#t:eqtype) 
                               (g:graph_state #a #t) 
                               (l1: vertex_set{subset_vertices l1 (g.vertices) }) 
                               (l2: vertex_set{subset_vertices l2 (g.vertices)}) 
             
                       : Tot(l: vertex_set{(forall x. vertex_mem x l <==> vertex_mem x l1 \/ vertex_mem x l2) /\ 
                                subset_vertices l (g.vertices)}) 
                                (decreases (length l1)) = 
(*Case 1: union l1 l2 = l2, if l1 is empty
  Case 2: union l1 l2 = union (tail l1) l2, if (head l1) is a memeber of l2
  Case 3: union l1 l2 = Seq (head l1), if union (tail l1) l2 is empty, this happens when l2 is also empty
  Case 4: union l1 l2 = snoc (union (tail l1) l2) (head l1), if (union (tail l1) l2) is not empty*)

(*Case 1*)
if length l1 = 0 then l2 
  else
  (*Case 2*)
  
   if mem (head l1) l2 then 
      union_vertex_sets_snoc g (tail l1) l2
   else
     ( (*Case 3*)
        let u = (union_vertex_sets_snoc g (tail l1) l2) in
         if length u = 0 then (Seq.create 1 (head l1)) 
         
         (*Case 4*)
         
         else
         (
           lemma_tail_snoc (union_vertex_sets_snoc g (tail l1) l2) (head l1);
           snoc_uniqueness_lemma (head l1) (union_vertex_sets_snoc g (tail l1) l2);
           lemma_mem_snoc (union_vertex_sets_snoc g (tail l1) l2) (head l1); 
           snoc (union_vertex_sets_snoc g (tail l1) l2) (head l1))) 

let rec union_vertex_sets_snoc1(l1: vertex_set) 
                               (l2: vertex_set) 
             
                       : Tot(l: vertex_set{(forall x. vertex_mem x l <==> vertex_mem x l1 \/ vertex_mem x l2)}) 
                                (decreases (length l1)) = 
(*Case 1: union l1 l2 = l2, if l1 is empty
  Case 2: union l1 l2 = union (tail l1) l2, if (head l1) is a memeber of l2
  Case 3: union l1 l2 = Seq (head l1), if union (tail l1) l2 is empty, this happens when l2 is also empty
  Case 4: union l1 l2 = snoc (union (tail l1) l2) (head l1), if (union (tail l1) l2) is not empty*)

(*Case 1*)
if length l1 = 0 then l2 
  else
  (*Case 2*)
  
   if mem (head l1) l2 then 
      union_vertex_sets_snoc1 (tail l1) l2
   else
     ( (*Case 3*)
        let u = (union_vertex_sets_snoc1  (tail l1) l2) in
         if length u = 0 then (Seq.create 1 (head l1)) 
         
         (*Case 4*)
         
         else
         (
           lemma_tail_snoc (union_vertex_sets_snoc1 (tail l1) l2) (head l1);
           snoc_uniqueness_lemma (head l1) (union_vertex_sets_snoc1 (tail l1) l2);
           lemma_mem_snoc (union_vertex_sets_snoc1 (tail l1) l2) (head l1); 
           snoc (union_vertex_sets_snoc1 (tail l1) l2) (head l1)))


let rec union_vertex_sets_snoc2(l1: vertex_list) 
                               (l2: vertex_set) 
             
                       : Tot(l: vertex_list{(forall x. vertex_mem x l <==> vertex_mem x l1 \/ vertex_mem x l2) /\
                                             (length l1 == 0 ==> l == l2)})
                                (decreases (length l1)) = 

if length l1 = 0 then l2 
  else
  (
    let u = union_vertex_sets_snoc2 (tail l1) l2 in
    let hd = head l1 in
    if mem hd l2 then 
      u
    else
     ( 
       if length u = 0 then 
          let s = (Seq.create 1 hd) in 
          assert (Seq.mem hd s);
          s
         else
         (
           if (mem hd u) then
             u
           else
           (
             lemma_tail_snoc u hd;
             lemma_mem_snoc u hd; 
             snoc u hd
           )
         )
     ) 
 )

let rec union_vertex_sets_snoc2_uniqueness_lemma (l1: vertex_list) 
                                                 (l2: vertex_set) 
                                  : Lemma 
                                    (ensures (is_vertex_set (union_vertex_sets_snoc2 l1 l2)))
                                    (decreases (length l1))= 
if length l1 = 0 then () 
  else
  (
    let u = union_vertex_sets_snoc2 (tail l1) l2 in
    let hd = head l1 in
    if mem hd l2 then 
      let _ = union_vertex_sets_snoc2_uniqueness_lemma (tail l1) l2 in
      let _ = assert (is_vertex_set u) in
      ()
    else
     ( 
       if length u = 0 then ()
         else
         (
           if (mem hd u) then
             union_vertex_sets_snoc2_uniqueness_lemma (tail l1) l2 
           else
           (
             lemma_tail_snoc u hd;
             union_vertex_sets_snoc2_uniqueness_lemma (tail l1) l2;
             snoc_uniqueness_lemma hd u;
             lemma_mem_snoc u hd; 
             ()
           )
         )
     ) 
 )                          

let union_vertex_sets (#a:eqtype)
                      (#t:eqtype) 
                      (g:graph_state #a #t) 
                      (l1: vertex_set{subset_vertices l1 (g.vertices) }) 
                      (l2: vertex_set{subset_vertices l2 (g.vertices)}) 
             
                       : Tot(l: vertex_set{(forall x. vertex_mem x l <==> vertex_mem x l1 \/ vertex_mem x l2) /\ 
                                subset_vertices l (g.vertices)}) 
                                (decreases (length l1)) = union_vertex_sets_snoc g l1 l2

let union_vertex_sets1 l1 l2 = union_vertex_sets_snoc1 l1 l2

let union_vertex_sets2 l1 l2 = 
  union_vertex_sets_snoc2_uniqueness_lemma l1 l2;
  union_vertex_sets_snoc2 l1 l2

let  union_vertex_sets_subset_lemma g l1 l2 = 
  if length l1 = 0 then ()
  else
   if mem (head l1) l2 then 
      ()
   else
     (
        let u = (union_vertex_sets_snoc1 (tail l1) l2) in
         if length u = 0 then ()
         else
         (
           lemma_tail_snoc (union_vertex_sets_snoc1(tail l1) l2) (head l1);
           snoc_uniqueness_lemma (head l1) (union_vertex_sets_snoc1 (tail l1) l2);
           lemma_mem_snoc (union_vertex_sets_snoc1 (tail l1) l2) (head l1); 
           ())) 

let union_vertex_sets_subset_lemma1 g l1 l2 =
 if length l1 = 0 then () 
  else
  (
    let u = union_vertex_sets_snoc2 (tail l1) l2 in
    let hd = head l1 in
    if mem hd l2 then 
      let _ = union_vertex_sets_snoc2_uniqueness_lemma (tail l1) l2 in
      let _ = assert (is_vertex_set u) in
      ()
    else
     ( 
       if length u = 0 then ()
         else
         (
           if (mem hd u) then
             union_vertex_sets_snoc2_uniqueness_lemma (tail l1) l2 
           else
           (
             lemma_tail_snoc u hd;
             union_vertex_sets_snoc2_uniqueness_lemma (tail l1) l2;
             snoc_uniqueness_lemma hd u;
             lemma_mem_snoc u hd; 
             ()
           )
         )
     ) 
 )                          


 
let union_vertex_sets_reach_lemma1  g o l1 l2 =
 
if length l1 = 0 then ()
  else
   if mem (head l1) l2 then 
      ()
   else
     (
        let u = (union_vertex_sets_snoc1 (tail l1) l2) in
         if length u = 0 then ()
         else
         (
           lemma_tail_snoc (union_vertex_sets_snoc1 (tail l1) l2) (head l1);
           snoc_uniqueness_lemma (head l1) (union_vertex_sets_snoc1 (tail l1) l2);
           lemma_mem_snoc (union_vertex_sets_snoc1 (tail l1) l2) (head l1); 
           ())) 

let union_vertex_sets_mem_lemma1 g l1 l2 vl =
  if length l1 = 0 then ()
  else
   if mem (head l1) l2 then 
      ()
   else
     (
        let u = (union_vertex_sets_snoc1 (tail l1) l2) in
         if length u = 0 then ()
         else
         (
           lemma_tail_snoc (union_vertex_sets_snoc1 (tail l1) l2) (head l1);
           snoc_uniqueness_lemma (head l1) (union_vertex_sets_snoc1 (tail l1) l2);
           lemma_mem_snoc (union_vertex_sets_snoc1 (tail l1) l2) (head l1); 
           ())) 

let union_vertex_sets_reach_lemma2 g o l1 l2 = union_vertex_sets_snoc2_uniqueness_lemma l1 l2

let union_vertex_sets_mem_lemma2 g l1 l2 vl = union_vertex_sets_snoc2_uniqueness_lemma l1 l2


let rec push_to_vertex_set (#a:eqtype)
                           (#t:eqtype)
                           (g:graph_state #a #t)
                           (l1: vertex_set{subset_vertices l1 (g.vertices)}) 
                           (l2: vertex_set{subset_vertices l2 (g.vertices) /\ (forall x. vertex_mem x l1 ==> ~(vertex_mem x l2))}) 
             
                     : Tot(l: vertex_set{(forall x. vertex_mem x l <==> vertex_mem x l1 \/ vertex_mem x l2) /\ 
                                subset_vertices l (g.vertices)})
                                (decreases (length l1)) =
if length l1 = 0 then l2 
else
(
  let tl_new = (push_to_vertex_set g (tail l1) l2) in
  let hd_l1 = head l1 in
   if length tl_new = 0 then (Seq.create 1 hd_l1)
   else
   (
     lemma_tail_snoc tl_new hd_l1;
     snoc_uniqueness_lemma hd_l1 tl_new;
     lemma_mem_snoc tl_new hd_l1; 
     snoc tl_new hd_l1))        
                                
let union_vertex_sets_reach_lemma   (#a:eqtype)
                                    (#t:eqtype) 
                                    (g:graph_state #a #t) 
                                    (o: vertex_id{mem_graph_vertex g o}) 
                                    (l1: vertex_set{subset_vertices l1 (g.vertices)}) 
                                    (l2: vertex_set{subset_vertices l2 (g.vertices)}) 

                                :  Lemma
                                    (requires (forall x. (vertex_mem x l1 \/ vertex_mem x l2
                                             ==> (exists (z1: reach g o x). reachfunc g o x z1))))
                                    (ensures (forall x. (vertex_mem x (union_vertex_sets g l1 l2)
                                             ==> (exists (z1: reach g o x). reachfunc g o x z1)))) =
 
if length l1 = 0 then ()
  else
   if mem (head l1) l2 then 
      ()
   else
     (
        let u = (union_vertex_sets_snoc g (tail l1) l2) in
         if length u = 0 then ()
         else
         (
           lemma_tail_snoc (union_vertex_sets_snoc g (tail l1) l2) (head l1);
           snoc_uniqueness_lemma (head l1) (union_vertex_sets_snoc g (tail l1) l2);
           lemma_mem_snoc (union_vertex_sets_snoc g (tail l1) l2) (head l1); 
           ())) 
      
      
let union_vertex_sets_mem_lemma   (#a:eqtype)
                                  (#t:eqtype) 
                                  (g:graph_state #a #t) 
                                  (l1: vertex_set{subset_vertices l1 (g.vertices)}) 
                                  (l2: vertex_set{subset_vertices l2 (g.vertices)}) 
                                  (vl: vertex_set{subset_vertices vl (g.vertices)})
                   :   Lemma
                       (requires (forall x. vertex_mem x vl ==> ~(vertex_mem x l1) /\ ~(vertex_mem x l2)))
                       (ensures (forall x. vertex_mem x vl ==> ~(vertex_mem x (union_vertex_sets g l1 l2)))) = 

if length l1 = 0 then ()
  else
   if mem (head l1) l2 then 
      ()
   else
     (
        let u = (union_vertex_sets_snoc g (tail l1) l2) in
         if length u = 0 then ()
         else
         (
           lemma_tail_snoc (union_vertex_sets_snoc g (tail l1) l2) (head l1);
           snoc_uniqueness_lemma (head l1) (union_vertex_sets_snoc g (tail l1) l2);
           lemma_mem_snoc (union_vertex_sets_snoc g (tail l1) l2) (head l1); 
           ())) 

let rec successor_push  (l: vertex_list) 
                        (vl: vertex_set)
                        (st:vertex_set {(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                         (Seq.length st > 0)})
              : Tot (st':vertex_set)
                (decreases length l) = 
 if length l = 0 then st
 else
 (
   let hd = Seq.head l in
   let tl = Seq.tail l in
   let l' = successor_push tl vl st in
   if Seq.mem hd vl || Seq.mem hd st then l'
   else
   (
     assert (~(Seq.mem hd vl) /\ ~(Seq.mem hd st));
     lemma_mem_snoc st hd;
     lemma_tail_snoc st hd;
     snoc_uniqueness_lemma hd st;
     let st' = snoc st hd in
     assert (is_vertex_set st');
     st'
   )
 )

#restart-solver 

let push_to_stack_graph (#a:eqtype)
                        (#t:eqtype) 
                        (g:graph_state #a #t) 
                        (vl: vertex_set{subset_vertices vl g.vertices})
                        (st:vertex_set {(subset_vertices st g.vertices) /\ 
                                        (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                        (x: Usize.t{~(Seq.mem x st) /\
                                     ~(Seq.mem x vl) /\ 
                                      (mem_graph_vertex g x)
                                    })
                                
            : Tot (st': vertex_set {(subset_vertices st' g.vertices) /\ 
                                    (Seq.mem x st') /\
                                    (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                    (forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
                                    (forall x. Seq.mem x st  ==> Seq.mem x st')}) = 
 if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    assert (Seq.mem x stk');
    is_vertex_set_lemma2 stk';
    assert (is_vertex_set stk');
    assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st));
    assert (forall x. Seq.mem x vl ==> ~(Seq.mem x stk'));
    assert (forall x. Seq.mem x stk' ==> ~(Seq.mem x vl));
    assert (forall x. Seq.mem x st ==> Seq.mem x stk');
    stk'
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  assert (is_vertex_set st);
  assert (~(Seq.mem x st));
  snoc_unique_lemma x st;
  assert (is_vertex_set st');
  assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st'));
  assert (forall x. Seq.mem x st' ==> ~(Seq.mem x vl));
  assert (forall x. Seq.mem x st ==> Seq.mem x st');
  st'
)


let push_to_stack_graph1  (vl: vertex_set)
                          (st:vertex_set { 
                                        (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                          (x: Usize.t{~(Seq.mem x st) /\
                                     ~(Seq.mem x vl)})
                                     
                                
            : Tot (st': vertex_set {(Seq.mem x st') /\
                                    (forall x. Seq.mem x st  ==> Seq.mem x st') /\
                                    (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                    (forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
                                    (Seq.length st > 0 ==> st' == snoc st x) /\
                                    (Seq.length st == 0 ==> st'== Seq.create 1 x)}) = 
if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    assert (Seq.mem x stk');
    is_vertex_set_lemma2 stk';
    assert (is_vertex_set stk');
    assert (forall x. Seq.mem x st ==> Seq.mem x stk');
    stk'
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  assert (is_vertex_set st);
  assert (~(Seq.mem x st));
  snoc_unique_lemma x st;
  assert (is_vertex_set st');
  assert (forall x. Seq.mem x st ==> Seq.mem x st');
  st'
)
                                    
let push_to_stack_graph_lemma (#a:eqtype)
                              (#t:eqtype) 
                              (g:graph_state #a #t) 
                              (vl: vertex_set{subset_vertices vl g.vertices})
                              (st:vertex_set {(subset_vertices st g.vertices) /\ 
                                        (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                              (x: Usize.t{~(Seq.mem x st) /\
                                     ~(Seq.mem x vl) /\ 
                                      (mem_graph_vertex g x)
                                    })
                   : Lemma
                     (requires Seq.length st == 0)
                     (ensures push_to_stack_graph g vl st x == Seq.create 1 x) = ()

let push_to_stack_graph_lemma1 (#a:eqtype)
                               (#t:eqtype) 
                               (g:graph_state #a #t) 
                               (vl: vertex_set{subset_vertices vl g.vertices})
                               (st:vertex_set {(subset_vertices st g.vertices) /\ 
                                        (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                               (x: Usize.t{~(Seq.mem x st) /\
                                     ~(Seq.mem x vl) /\ 
                                      (mem_graph_vertex g x)
                                    })
                   : Lemma
                     (requires Seq.length st > 0)
                     (ensures push_to_stack_graph g vl st x == snoc st x) = ()



#restart-solver

let successor_push_body  (#a:eqtype)
                         (#t:eqtype) 
                         (g:graph_state #a #t) 
                         (l: vertex_list{forall x. Seq.mem x l ==> Seq.mem x g.vertices}) 
                         (vl: vertex_set{subset_vertices vl g.vertices})
                         (st:vertex_set {(subset_vertices st g.vertices) /\
                                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                         (j:nat {j < Seq.length l})
               : Tot (st':vertex_set {(subset_vertices st' g.vertices) /\
                                      (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                      (forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
                                      (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                      (~(Seq.mem (Seq.index l j) vl) /\ ~(Seq.mem (Seq.index l j) st) ==>
                                            st' == push_to_stack_graph g vl st (Seq.index l j)) /\
                                      ((Seq.mem (Seq.index l j) vl) \/ (Seq.mem (Seq.index l j) st) ==>
                                            st' == st)}) = 
  let succ = Seq.index l j in
 
  if not(Seq.mem succ vl) && not(Seq.mem succ st) then
    (
      let st' =  push_to_stack_graph g vl st succ in
      assert (subset_vertices st' g.vertices);
      assert (is_vertex_set st');
      assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st'));
      assert (forall x. Seq.mem x st' ==> ~(Seq.mem x vl));
      assert (forall x. Seq.mem x st ==> Seq.mem x st');
      assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl));
      assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl) ==> Seq.mem succ st');
      assert (st' == push_to_stack_graph g vl st succ);
      st'
    )
  else
     (
       let st' = st in
       assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl) ==> Seq.mem succ st');
       assert (st' == st);
       st'
     )

let successor_push_body1 (l: vertex_list) 
                         (vl: vertex_set)
                         (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                         (j:nat {j < Seq.length l})
               : Tot (st':vertex_set {(forall x. Seq.mem x st ==> Seq.mem x st') /\
                                      (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                      (forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
                                      (~(Seq.mem (Seq.index l j) vl) /\ ~(Seq.mem (Seq.index l j) st) ==>
                                            st' == push_to_stack_graph1 vl st (Seq.index l j)) /\
                                      ((Seq.mem (Seq.index l j) vl) \/ (Seq.mem (Seq.index l j) st) ==>
                                            st' == st)}) = 
 let succ = Seq.index l j in
 
  if not(Seq.mem succ vl) && not(Seq.mem succ st) then
    (
      let st' =  push_to_stack_graph1 vl st succ in
      assert (is_vertex_set st');
      assert (forall x. Seq.mem x st ==> Seq.mem x st');
      assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl));
      assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl) ==> Seq.mem succ st');
      assert (st' == push_to_stack_graph1 vl st succ);
      st'
    )
  else
    (
       let st' = st in
       assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl) ==> Seq.mem succ st');
       assert (st' == st);
       st'
    )

#restart-solver 

let rec successor_push_itr (#a:eqtype)
                           (#t:eqtype) 
                           (g:graph_state #a #t) 
                           (l: vertex_list{forall x. Seq.mem x l ==> Seq.mem x g.vertices}) 
                           (vl: vertex_set{subset_vertices vl g.vertices})
                           (st:vertex_set {(subset_vertices st g.vertices) /\
                                   (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                   (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                           (j:nat (*{j <= Seq.length l}*))
               : Tot (st':vertex_set{(subset_vertices st' g.vertices) /\
                                     (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                     (forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
                                     (forall x. Seq.mem x st ==> Seq.mem x st')})
                 (decreases (Seq.length l - j)) = 
 if j >= Seq.length l then 
   st
 else
 (
   let j' = j + 1 in
   assert (j < Seq.length l);
   let st' = successor_push_body g l vl st j in
   assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st'));
   assert (forall x. Seq.mem x st' ==> ~(Seq.mem x vl));
   assert (forall x. Seq.mem x st ==> Seq.mem x st');
   assert (subset_vertices st' g.vertices);
   let st'' = successor_push_itr g l vl st' j' in
   st''
 )

let rec successor_push_itr1 (l: vertex_list) 
                            (vl: vertex_set)
                            (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                           (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                            (j:nat)
               : Tot (st':vertex_set{(forall x. Seq.mem x st ==> Seq.mem x st') /\
                                     (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                     (forall x. Seq.mem x st' ==> ~(Seq.mem x vl))})
                 (decreases (Seq.length l - j)) = 
 if j >= Seq.length l then 
   st
 else
 (
   let j' = j + 1 in
   assert (j < Seq.length l);
   let st' = successor_push_body1 l vl st j in
   
   assert (forall x. Seq.mem x st ==> Seq.mem x st');
   
   let st'' = successor_push_itr1 l vl st' j' in
   st''
 )

#restart-solver 

let successor_push_itr_lemma (#a:eqtype)
                                 (#t:eqtype) 
                                 (g:graph_state #a #t) 
                                 (l: vertex_list{forall x. Seq.mem x l ==> Seq.mem x g.vertices}) 
                                 (vl: vertex_set{subset_vertices vl g.vertices})
                                 (st:vertex_set {(subset_vertices st g.vertices) /\
                                                 (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                 (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                                 (j:nat (*{j <= Seq.length l}*))
                 : Lemma 
                   (requires j < Seq.length l)
                   (ensures (successor_push_itr g l vl st j == 
                                      successor_push_itr g l vl (successor_push_body g l vl st j) (j + 1))) = ()

let successor_push_itr_lemma1 (#a:eqtype)
                              (#t:eqtype) 
                              (g:graph_state #a #t) 
                              (l: vertex_list{forall x. Seq.mem x l ==> Seq.mem x g.vertices}) 
                              (vl: vertex_set{subset_vertices vl g.vertices})
                              (st:vertex_set {(subset_vertices st g.vertices) /\
                                                 (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                 (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                              (j:nat (*{j <= Seq.length l}*))
                 : Lemma 
                   (requires j >= Seq.length l)
                   (ensures (successor_push_itr g l vl st j == st)) = ()

let successor_push_itr1_lemma (l: vertex_list) 
                              (vl: vertex_set)
                              (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                              (j:nat)
                 : Lemma 
                   (requires j < Seq.length l)
                   (ensures (successor_push_itr1 l vl st j == 
                                      successor_push_itr1 l vl (successor_push_body1 l vl st j) (j + 1))) = ()


let successor_push_itr1_lemma1 (l: vertex_list) 
                               (vl: vertex_set)
                               (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                              (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                               (j:nat)
                 : Lemma 
                   (requires j == Seq.length l)
                   (ensures (successor_push_itr1 l vl st j == st)) = ()

let push_to_stack_graph1_subset_lemma  (#a:eqtype)
                                       (#t:eqtype) 
                                       (g:graph_state #a #t) 
                                       (vl: vertex_set)
                                       (st:vertex_set { 
                                                       (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                       (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                                       (x: Usize.t{~(Seq.mem x st) /\
                                                    ~(Seq.mem x vl)})
                  : Lemma
                   (requires (mem_graph_vertex g x) /\
                             (subset_vertices vl g.vertices) /\
                             (subset_vertices st g.vertices))
                   (ensures subset_vertices (push_to_stack_graph1 vl st x) g.vertices) = 
 if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    assert (Seq.mem x stk');
    is_vertex_set_lemma2 stk';
    assert (is_vertex_set stk');
    assert (forall x. Seq.mem x st ==> Seq.mem x stk');
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  assert (is_vertex_set st);
  assert (~(Seq.mem x st));
  snoc_unique_lemma x st;
  assert (is_vertex_set st');
  assert (forall x. Seq.mem x st ==> Seq.mem x st');
  ()
)
          
let successor_push_body1_subset_lemma (#a:eqtype)
                                      (#t:eqtype) 
                                      (g:graph_state #a #t) 
                                      (l: vertex_list) 
                                      (vl: vertex_set)
                                      (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                     (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                                      (j:nat{j < Seq.length l})
                 : Lemma
                   (requires (forall x. Seq.mem x l ==> Seq.mem x g.vertices) /\
                             (subset_vertices vl g.vertices) /\
                             (subset_vertices st g.vertices))
                   (ensures subset_vertices (successor_push_body1 l vl st j) g.vertices) = 
let succ = Seq.index l j in
 
  if not(Seq.mem succ vl) && not(Seq.mem succ st) then
    (
      let st' =  push_to_stack_graph1 vl st succ in
      push_to_stack_graph1_subset_lemma g vl st succ;
      assert (is_vertex_set st');
      assert (forall x. Seq.mem x st ==> Seq.mem x st');
      assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl));
      assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl) ==> Seq.mem succ st');
      assert (st' == push_to_stack_graph1 vl st succ);
      ()
    )
  else
    (
       let st' = st in
       assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl) ==> Seq.mem succ st');
       assert (st' == st);
       ()
    )

#restart-solver 

let rec successor_push_itr1_subset_lemma (#a:eqtype)
                                         (#t:eqtype) 
                                         (g:graph_state #a #t) 
                                         (l: vertex_list) 
                                         (vl: vertex_set)
                                         (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                                         (j:nat)
                 : Lemma
                   (requires (forall x. Seq.mem x l ==> Seq.mem x g.vertices) /\
                             (subset_vertices vl g.vertices) /\
                             (subset_vertices st g.vertices))
                   (ensures subset_vertices (successor_push_itr1 l vl st j) g.vertices)
                   (decreases (Seq.length l - j)) =
 if j >= Seq.length l then 
   ()
 else
 (
   let j' = j + 1 in
   assert (j < Seq.length l);
   let st' = successor_push_body1 l vl st j in
   successor_push_body1_subset_lemma g l vl st j;
   assert (forall x. Seq.mem x st ==> Seq.mem x st');
   
   let st'' = successor_push_itr1 l vl st' j' in
   successor_push_itr1_subset_lemma g l vl st' j';
   ()
 )

let successor_equals_if_graph_equals_lemma (#a:eqtype)
                                           (#t:eqtype) 
                                           (g:graph_state #a #t)
                                           (g1:graph_state #a #t)
                                           (i: vertex_id {mem_graph_vertex g i})
                       : Lemma
                         (requires g == g1)
                         (ensures (successors g i == successors g1 i)) = ()

#restart-solver

let push_to_stack_graph1_reach_lemma (#a:eqtype)
                                     (#t:eqtype) 
                                     (g:graph_state #a #t) 
                                     (vl: vertex_set)
                                     (st:vertex_set { 
                                                       (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                       (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                                     (root_set : vertex_set{subset_vertices root_set (g.vertices)})
                                     (x: Usize.t{~(Seq.mem x st) /\
                                                    ~(Seq.mem x vl)})
                                     
                  : Lemma
                    (requires ((forall y. vertex_mem y st ==> (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1)) /\
                               (Seq.mem x g.vertices) /\
                               (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1)))
                    (ensures (forall y. vertex_mem y (push_to_stack_graph1 vl st x) ==> (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1))) =
if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    assert (Seq.mem x stk');
    is_vertex_set_lemma2 stk';
    assert (is_vertex_set stk');
    assert (forall x. Seq.mem x st ==> Seq.mem x stk');
    assert (forall y. vertex_mem y stk' ==> (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1));
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  assert (is_vertex_set st);
  assert (~(Seq.mem x st));
  snoc_unique_lemma x st;
  assert (is_vertex_set st');
  assert (forall x. Seq.mem x st ==> Seq.mem x st');
  assert (forall y. vertex_mem y st' ==> (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1));
  ()
)

#restart-solver 

let slice_membership_lemma_x (#a:eqtype)
                             (#t:eqtype) 
                             (g:graph_state #a #t)                                                                              
                             (l: vertex_list{(forall x. Seq.mem x l ==> Seq.mem x g.vertices)})
                             (i:nat{i <= (Seq.length l)})
                             (x: vertex_id {Seq.mem x (Seq.slice l i (Seq.length l))})
                 : Lemma
                   (ensures Seq.mem x g.vertices) = 
 let l' = Seq.slice l i (Seq.length l) in
 let id = index_mem x l' in
 assert (Seq.index l' id == x);
 lemma_index_slice l i (Seq.length l) id;
 assert (Seq.index l (id + i) == x);
 assert (Seq.mem x l);
 assert (Seq.mem x g.vertices);
 ()

#restart-solver

(*let slice_membership_lemma_reach_x_2 (#a:eqtype)
                                     (#t:eqtype)
                                     (g:graph_state #a #t)
                                     (r : vertex_list{(forall x. vertex_mem x r ==> vertex_mem x (g.vertices))})
                                     (y:vertex_id{Seq.mem y r})
                                     (root_set : vertex_set{subset_vertices root_set (g.vertices)})
                   : Lemma
                   (requires ((forall x. vertex_mem x r ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\
                                                                         reachfunc g o x z1))))
                   (ensures exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1)*)
let successor_push_body1_reach_lemma  (#a:eqtype)
                                      (#t:eqtype) 
                                      (g:graph_state #a #t) 
                                      (l: vertex_list) 
                                      (vl: vertex_set)
                                      (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                     (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                                      (j:nat{j < Seq.length l})
                                      (root_set : vertex_set{subset_vertices root_set (g.vertices)})
                            : Lemma 
                              (requires ((forall x. vertex_mem x st ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1)) /\
                                         (forall y. vertex_mem y l ==>   (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1)) /\
                                         (forall x. Seq.mem x l ==> Seq.mem x g.vertices)))
                              (ensures ((forall x. vertex_mem x (successor_push_body1 l vl st j) ==> 
                                               (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1)))) = 
  let succ = Seq.index l j in
  assert (Seq.mem succ l);
  assert (Seq.mem succ g.vertices);
  if not(Seq.mem succ vl) && not(Seq.mem succ st) then
    (
      assert ((forall y. vertex_mem y st ==> (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1)));
      assert (Seq.mem succ g.vertices);
      let st' =  push_to_stack_graph1 vl st succ in
      slice_membership_lemma_reach_x_2 g l succ root_set;
      assert (exists o (z1: reach g o succ) . vertex_mem o root_set /\ reachfunc g o succ z1);
      
      push_to_stack_graph1_reach_lemma g vl st root_set succ;
      assert (forall x. vertex_mem x (push_to_stack_graph1 vl st succ) ==> 
                                               (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1));
      ()
    )
  else
    (
       let st' = st in
       assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl) ==> Seq.mem succ st');
       assert (st' == st);
       ()
    )

let rec successor_push_itr1_reach_lemma  (#a:eqtype)
                                         (#t:eqtype) 
                                         (g:graph_state #a #t) 
                                         (l: vertex_list) 
                                         (vl: vertex_set)
                                         (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                                         (j:nat)
                                         (root_set : vertex_set{subset_vertices root_set (g.vertices)})
                 : Lemma
                   (requires ((forall x. vertex_mem x st ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1)) /\
                             (forall y. vertex_mem y l ==>   (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1)) /\
                             (forall x. Seq.mem x l ==> Seq.mem x g.vertices)))
                   (ensures ((forall x. vertex_mem x (successor_push_itr1 l vl st j) ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1)))) 
                   (decreases (Seq.length l - j)) = 
 if j >= Seq.length l then 
   ()
 else
 (
   let j' = j + 1 in
   assert (j < Seq.length l);
   let st' = successor_push_body1 l vl st j in
   successor_push_body1_reach_lemma g l vl st j root_set;
   assert (forall x. vertex_mem x st' ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1));
   assert (forall x. Seq.mem x st ==> Seq.mem x st');
   
   let st'' = successor_push_itr1 l vl st' j' in
   let _ = successor_push_itr1_reach_lemma g l vl st' j' root_set in
  
   assert (forall x. vertex_mem x st'' ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1));
   ()
 )

let successor_push_body1_absent_element_lemma  (l: vertex_list) 
                                               (vl: vertex_set)
                                               (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                              (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                                               (j:nat{j < Seq.length l})
                              : Lemma 
                                (ensures (~(Seq.mem (Seq.index l j) vl) ==> Seq.mem (Seq.index l j) (successor_push_body1 l vl st j))) =
                                              
  let succ = Seq.index l j in
  assert (Seq.mem succ l);
  
  if not(Seq.mem succ vl) && not(Seq.mem succ st) then
    (
      let st' =  push_to_stack_graph1 vl st succ in
      assert (Seq.mem succ st');
      ()
    )
  else
    (
       let st' = st in
       assert (~(Seq.mem succ st) /\ ~(Seq.mem succ vl) ==> Seq.mem succ st');
       assert (st' == st);
       assert (Seq.mem succ vl \/ Seq.mem succ st);
       if (Seq.mem succ st) then
         (
           assert (Seq.mem succ st');
           ()
         )
       else
         (
           assert (~(Seq.mem succ st'));
           ()
         )
    )

let rec successor_push_itr1_absent_element_lemma (l: vertex_list) 
                                                 (vl: vertex_set)
                                                 (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                                (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                                                 (j:nat)
                                      : Lemma
                                        (requires j <= Seq.length l)
                                        (ensures (forall x. Seq.mem x (Seq.slice l j (Seq.length l)) /\ ~(Seq.mem x vl) ==>
                                                        (Seq.mem x (successor_push_itr1 l vl st j))))
                                        (decreases (Seq.length l - j)) = 
 if j >= Seq.length l then 
   ()
 else
 (
   let j' = j + 1 in
   assert (j < Seq.length l);
   let st' = successor_push_body1 l vl st j in
   successor_push_body1_absent_element_lemma  l vl st j;
   assert (~(Seq.mem (Seq.index l j) vl) ==> Seq.mem (Seq.index l j) (successor_push_body1 l vl st j));
   let st'' = successor_push_itr1 l vl st' j' in
   successor_push_itr1_absent_element_lemma l vl st' j';
   assert (forall x. Seq.mem x (Seq.slice l j' (Seq.length l)) /\ ~(Seq.mem x vl) ==>
                                                        (Seq.mem x (successor_push_itr1 l vl st' j')));
   assert (~(Seq.mem (Seq.index l j) vl) ==> Seq.mem (Seq.index l j) st');
   assert (forall x. Seq.mem x (Seq.slice l j (Seq.length l)) /\ ~(Seq.mem x vl) ==>
                                                        (Seq.mem x (successor_push_itr1 l vl st j)));
   ()
 )
                                            
                                                  
let successor_push_itr1_absent_element_l_lemma (l: vertex_list) 
                                                   (vl: vertex_set)
                                                   (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                                (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})
                                    : Lemma
                                      (ensures (forall x. Seq.mem x l /\ ~(Seq.mem x vl) ==> (Seq.mem x (successor_push_itr1 l vl st 0)))) =
 assert (Seq.slice l 0 (Seq.length l) == l);
 assert (0 <= Seq.length l);
 successor_push_itr1_absent_element_lemma l vl st 0;
 assert (forall x. Seq.mem x l /\ ~(Seq.mem x vl) ==> (Seq.mem x (successor_push_itr1 l vl st 0)));
 ()





(*val remove_absent_element_lemma :   (#a:eqtype)->
                                    (#t:eqtype) ->
                                    (g:graph_state #a #t) ->
                                    (l:vertex_list{forall x. Seq.mem x l ==> Seq.mem x (g.vertices)})->
                                    (vl:vertex_set{subset_vertices vl (g.vertices)}) ->
                  
                                    Lemma ((forall x. vertex_mem x l /\ ~(vertex_mem x vl) ==> 
                                             vertex_mem x (remove_all_instances_of_vertex_from_vertex_set l vl)))*)




let rec remove_all_instances_of_vertex_from_vertex_set_cons (l: vertex_list) 
                                                            (vl: vertex_set) 
                                                 : Tot (l':vertex_set {(forall x. vertex_mem x l' ==> vertex_mem x l) /\
                                                                       (forall x. mem x vl ==> ~(mem x l')) /\
                                                                       (forall x. mem x l' ==> ~(mem x vl))}) 
                                                   (decreases (length l))=
 
if length l = 0 then empty 
else
 if mem (head l) vl then remove_all_instances_of_vertex_from_vertex_set_cons (tail l) vl
 else
 (
   let u = (remove_all_instances_of_vertex_from_vertex_set_cons (tail l) vl) in
   if mem (head l) u then u
   else
   (
     lemma_tl (head l) u;
     let u' = cons (head l) u in
     u'
   )
)


let rec remove_all_instances_of_vertex_from_vertex_set_snoc (l: vertex_list) 
                                                            (vl: vertex_set) 
                                                 :Tot (l':vertex_set
                                                              {(forall x. vertex_mem x l' ==> vertex_mem x l) /\
                                                              (forall x. mem x vl ==> ~(mem x l')) /\
                                                              (forall x. mem x l' ==> ~(mem x vl))}) 
                                                   (decreases (length l))=
if length l = 0 then empty
  else
  (
   if mem (head l) vl then remove_all_instances_of_vertex_from_vertex_set_snoc (tail l) vl
   else
   (
     let u = remove_all_instances_of_vertex_from_vertex_set_snoc (tail l) vl in
     if length u = 0 then
      (Seq.create 1 (head l)) 
     else
     ( 
       assert (length u <> 0);
       if (mem (head l) u) then u
       else
       (
          assert (~(mem (head l) u));
          lemma_tail_snoc u (head l);
          snoc_uniqueness_lemma (head l) u;
          lemma_mem_snoc u (head l); 
          snoc u (head l)
       )
     )
   )
)  

let remove_all_instances_of_vertex_from_vertex_set (l: vertex_list) 
                                                   (vl: vertex_set) 
                                                 : Tot (l': vertex_set{(forall x. vertex_mem x l' ==> vertex_mem x l) /\
                                                              (forall x. mem x vl ==> ~(mem x l')) /\
                                                              (forall x. mem x l' ==> ~(mem x vl))}) 
                                                   (decreases (length l))= 

 remove_all_instances_of_vertex_from_vertex_set_cons l vl

let rec remove_all_instances_of_vertex_from_vertex_set_mem (l: vertex_list) 
                                                           (vl: vertex_set) 
                                                    :  Lemma 
                                                       (ensures (forall x. vertex_mem x 
                                                                   (remove_all_instances_of_vertex_from_vertex_set l vl) ==>
                                                                     vertex_mem x l)) 
                                                       (decreases (length l)) = 
if length l = 0 then ()
  else
  (
   if mem (head l) vl then remove_all_instances_of_vertex_from_vertex_set_mem (tail l) vl
   else
   (
     let u = remove_all_instances_of_vertex_from_vertex_set_snoc (tail l) vl in
     if length u = 0 then
      () 
     else
     ( 
       assert (length u <> 0);
       if (mem (head l) u) then remove_all_instances_of_vertex_from_vertex_set_mem (tail l) vl
       else
       (
          assert (~(mem (head l) u));
          lemma_tail_snoc u (head l);
          snoc_uniqueness_lemma (head l) u;
          lemma_mem_snoc u (head l); 
          remove_all_instances_of_vertex_from_vertex_set_mem (tail l) vl
       )
     )
   )
)  

let rec remove_lemma_correctness (l:seq vertex_id{is_vertex_set l})
                                 (vl:seq vertex_id{is_vertex_set vl})
                    : Lemma (ensures ((forall x. mem x vl ==> 
                                  ~(mem x (remove_all_instances_of_vertex_from_vertex_set l vl)))))
                      (decreases (length l))
                      [SMTPat (remove_all_instances_of_vertex_from_vertex_set l vl)] = 
if length l = 0 then ()
  else
  (
   if mem (head l) vl then remove_lemma_correctness (tail l) vl
   else
   (
     let u = remove_all_instances_of_vertex_from_vertex_set_snoc (tail l) vl in
     if length u = 0 then
      () 
     else
     ( 
       assert (length u <> 0);
       if (mem (head l) u) then remove_lemma_correctness (tail l) vl
       else
       (
          assert (~(mem (head l) u));
          lemma_tail_snoc u (head l);
          snoc_uniqueness_lemma (head l) u;
          lemma_mem_snoc u (head l); 
          remove_lemma_correctness (tail l) vl
       )
     )
   )
 )  
                      
let rec remove_lemma_correctness1  (l:seq vertex_id{is_vertex_set l})
                                   (vl:seq vertex_id{is_vertex_set vl})
                    :  Lemma (ensures((forall x. mem x (remove_all_instances_of_vertex_from_vertex_set l vl) ==> 
                                            ~(mem x vl)))) 
                       (decreases (length l)) =
if length l = 0 then ()
  else
  (
   if mem (head l) vl then remove_lemma_correctness1 (tail l) vl
   else
   (
     let u = remove_all_instances_of_vertex_from_vertex_set_snoc (tail l) vl in
     if length u = 0 then
      () 
     else
     ( 
       assert (length u <> 0);
       if (mem (head l) u) then remove_lemma_correctness1 (tail l) vl
       else
       (
          assert (~(mem (head l) u));
          lemma_tail_snoc u (head l);
          snoc_uniqueness_lemma (head l) u;
          lemma_mem_snoc u (head l); 
          remove_lemma_correctness1 (tail l) vl
       )
     )
   )
 )  


let rec remove_lemma_subset #a #t g l vl
                            
            :  Lemma (ensures(is_vertex_set (remove_all_instances_of_vertex_from_vertex_set l vl) /\
                               subset_vertices (remove_all_instances_of_vertex_from_vertex_set l vl) (g.vertices))) 
               (decreases (length l)) = 
if length l = 0 then ()
  else
  (
   if mem (head l) vl then remove_lemma_subset g (tail l) vl
   else
   (
     let u = remove_all_instances_of_vertex_from_vertex_set_snoc (tail l) vl in
     if length u = 0 then
      () 
     else
     ( 
       assert (length u <> 0);
       if (mem (head l) u) then remove_lemma_subset g (tail l) vl
       else
       (
          assert (~(mem (head l) u));
          lemma_tail_snoc u (head l);
          snoc_uniqueness_lemma (head l) u;
          lemma_mem_snoc u (head l); 
          remove_lemma_subset g (tail l) vl
       )
     )
   )
 )                                 

let rec remove_absent_element_lemma #a #t g l vl 
                  
               :  Lemma (ensures((forall x. vertex_mem x l /\ ~(vertex_mem x vl) ==> 
                                             vertex_mem x (remove_all_instances_of_vertex_from_vertex_set l vl))))
                  (decreases (length l)) =

if length l = 0 then ()
else
 if mem (head l) vl then 
 (
  let _ = remove_absent_element_lemma g (tail l) vl in
  ()
 ) 
 else
 (
   let u = (remove_all_instances_of_vertex_from_vertex_set_cons (tail l) vl) in
   let _ = remove_absent_element_lemma g (tail l) vl in
   if mem (head l) u then  ()
   
   else
   (
     lemma_tl (head l) u;
     let u' = cons (head l) u in
     assert ((forall x. (vertex_mem x (tail l) /\ ~(vertex_mem x vl)) ==> 
                                             vertex_mem x (remove_all_instances_of_vertex_from_vertex_set (tail l) vl)));
     assert (forall x. (vertex_mem x l /\ ~(vertex_mem x vl)) ==> 
                                             vertex_mem x (remove_all_instances_of_vertex_from_vertex_set l vl));
     ()
   )
)


let rec remove_lemma_reach #a #t g x' l vl 
        
          :  Lemma (ensures(forall y. mem y (remove_all_instances_of_vertex_from_vertex_set l vl) ==>
                                        (exists(p:(reach g x' y)).reachfunc g x' y p))) 
             (decreases (length l)) =  

if length l = 0 then ()
  else
  (
   if mem (head l) vl then remove_lemma_reach g x' (tail l) vl
   else
   (
     let u = remove_all_instances_of_vertex_from_vertex_set_snoc (tail l) vl in
     if length u = 0 then
      () 
     else
     ( 
       assert (length u <> 0);
       if (mem (head l) u) then remove_lemma_reach g x' (tail l) vl
       else
       (
          assert (~(mem (head l) u));
          lemma_tail_snoc u (head l);
          snoc_uniqueness_lemma (head l) u;
          lemma_mem_snoc u (head l); 
          remove_lemma_reach g x' (tail l) vl
       )
     )
   )
)  

#restart-solver


#restart-solver




#restart-solver 

let vertices_in_path_concat  (#a:eqtype)
                             (#t:eqtype)
                             (g:graph_state #a #t) 
                             (s:vertex_id{mem_graph_vertex g s}) 
                             (b:vertex_id{mem_graph_vertex g b}) 
                             (r_sb: reach g s b) 
                             (r:vertex_set{subset_vertices r g.vertices /\ ~(is_emptySet r)})
                                     
                      : Lemma 
                         (requires(negation_nonEmpty_implies_empty r;forall c. vertex_mem c (vertices_in_path g s b r_sb) ==> c <> (get_head g r) /\ 
                                                    ~(vertex_mem c (get_tail g r)))) 
                         (ensures (forall c. vertex_mem c (vertices_in_path g s b r_sb) ==> ~(vertex_mem c r))) = ()

let  vertices_in_path_concat1  (#a:eqtype)
                               (#t:eqtype) 
                               (g:graph_state #a #t) 
                               (s:vertex_id{mem_graph_vertex g s}) 
                               (b:vertex_id{mem_graph_vertex g b}) 
                               (r_sb: reach g s b) 
                               (r:vertex_set{subset_vertices r g.vertices /\ ~(is_emptySet r)})
                                     
                       : Lemma 
                         (requires(negation_nonEmpty_implies_empty r;
                                   forall c. vertex_mem c (vertices_in_path g s b r_sb) ==> c <> (get_last_elem g r) /\ 
                                                    ~(vertex_mem c (get_first g r)))) 
                         (ensures (forall c. vertex_mem c (vertices_in_path g s b r_sb) ==> ~(vertex_mem c r))) = ()


#restart-solver

let vertices_in_path_neg_lemma   (#a:eqtype)
                                 (#t:eqtype) 
                                 (g:graph_state #a #t) 
                                 (s:vertex_id{mem_graph_vertex g s}) 
                                 (b:vertex_id{mem_graph_vertex g b}) 
                                 (r_sb: reach g s b) 
                                 (vl:vertex_set{subset_vertices vl g.vertices})
                                 (x: vertex_id{mem_graph_vertex g x})
                             : Lemma 
                                 (requires (~(vertex_mem x (vertices_in_path g s b r_sb)) /\
                                             (vertex_mem s vl ==> vertex_mem x (vertices_in_path g s b r_sb))))
                                 (ensures (~(vertex_mem s vl))) = ()
#restart-solver

let index_cannot_exceed_len_helper (#a:eqtype)
                                   (#t:eqtype)
                                   (len:nat)
                                   (i:nat)
                                   (g:graph_state #a #t)
                                   (s:vertex_set{subset_vertices s g.vertices})
                                   (x:vertex_id{mem_graph_vertex g x /\ (~(vertex_mem x s))})
                      :Lemma
                       (ensures (exists y. vertex_mem y g.vertices /\ ~(vertex_mem y s))) = ()
#restart-solver

let is_vertex_set_slice (#a:eqtype)
                        (#t:eqtype)
                        (g:graph_state #a #t)
                        (v_id:vertex_id{mem_graph_vertex g v_id})
                        (len: nat)
                        (i:nat{i < len})
                        (vs:Seq.seq vertex_id{(len == Seq.length vs) /\  
                                              (is_vertex_set (Seq.slice vs 0 i)) /\
                                             ~(mem_of_seq v_id (Seq.slice vs 0 i)) /\
                                              (subset_vertices (Seq.slice vs 0 i) (g.vertices)) /\
                                              (Seq.index (Seq.slice vs 0 (i + 1)) i == v_id) /\
                                              (mem_of_seq v_id (Seq.slice vs 0 (i + 1)))})
              : Lemma 
                (ensures (is_vertex_set (Seq.slice vs 0 (i + 1)) /\ (subset_vertices (Seq.slice vs 0 (i + 1)) (g.vertices)))) = 
let _ = assert (mem_of_seq v_id (Seq.slice vs 0 (i + 1))) in
let _ = assert (~(mem_of_seq v_id (Seq.slice vs 0 i))) in
let _ = assert (is_vertex_set (Seq.slice vs 0 i)) in
let _ = assert ((Seq.slice vs 0 (i + 1)) == snoc (Seq.slice vs 0 i) v_id) in
let _ = assert (forall y. vertex_mem y (Seq.slice vs 0 i) ==> y <> v_id) in
let _ =  assert (subset_vertices (Seq.slice vs 0 i) (g.vertices)) in
if i = 0 then () 
else 
(
  let _ = assert (i <> 0) in
  let _ = assert (Seq.head (Seq.slice vs 0 i) <> v_id) in
  lemma_tail_snoc (Seq.slice vs 0 i) v_id;
  snoc_uniqueness_lemma v_id (Seq.slice vs 0 i);
  lemma_mem_snoc (Seq.slice vs 0 i) v_id;
  let _ = assert (is_vertex_set (Seq.slice vs 0 (i + 1))) in
  let _ =  assert (subset_vertices (Seq.slice vs 0 (i + 1)) (g.vertices)) in
  ()
)


let is_vertex_set_slice1  (v_id:vertex_id) 
                          (len: nat)
                          (i:nat{i < len}) 
                          (vs:Seq.seq vertex_id{(len == Seq.length vs) /\  
                                              (is_vertex_set (Seq.slice vs 0 i)) /\
                                             ~(mem_of_seq_upto_index v_id vs i) /\
                                              (Seq.index (Seq.slice vs 0 (i + 1)) i == v_id) /\
                                              (mem_of_seq_upto_index v_id vs (i + 1))}) 
             : Lemma 
                (ensures (is_vertex_set (Seq.slice vs 0 (i + 1)))) = 
if i = 0 then () 
else 
(
  
  lemma_tail_snoc (Seq.slice vs 0 i) v_id;
  snoc_uniqueness_lemma v_id (Seq.slice vs 0 i);
  lemma_mem_snoc (Seq.slice vs 0 i) v_id;
  ()
)

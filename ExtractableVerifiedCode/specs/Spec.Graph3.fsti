module Spec.Graph3

open FStar.Seq
open FStar.Seq.Base

module H = FStar.HyperStack
module HA = FStar.HyperStack.All

module Usize = FStar.UInt64

type vertex_id = Usize.t
type edge = vertex_id & vertex_id 
/// Depreciated currently. This can be used if attributes to vertices and edges needs to be encoded as part of the graph. This can well be added as separate attribute maps.
/// type v_map (#a:Type) = vertex_id -> Tot a

/// type e_map (#b:Type) = edge -> Tot b


type vertex_list = seq vertex_id 
type edge_list = seq edge 

#restart-solver

let rec no_duplicates (ds: seq vertex_id)
        : Tot (bool)
          (decreases (Seq.length ds)) =

if length ds = 0 then true else 

 not(Seq.mem (Seq.index ds (Seq.length ds - 1)) (Seq.slice ds 0 (Seq.length ds - 1))) 
      && no_duplicates (Seq.slice ds 0 (Seq.length ds - 1))
     
let rec no_duplicates' (ds: seq vertex_id)
        : Tot (bool)
          (decreases (Seq.length ds)) =

if length ds = 0 then true else
not(Seq.mem (Seq.head ds) (Seq.tail ds)) 
      && no_duplicates' (Seq.tail ds)

val count :   (#a: eqtype) ->
              (l: seq a) ->
              (x: a) ->
          Tot (nat)
          (decreases length l)

val is_vertex_set :  (vertex_list) ->
                     Tot (bool)

val is_vertex_set_count_lemma_all : (l: seq vertex_id) ->
                              Lemma 
                              (requires is_vertex_set l)
                              (ensures (forall x. Seq.mem x l ==> count l x == 1))

val is_vertex_set_count_lemma_all1 : (l: seq vertex_id) ->
                              Lemma 
                              (requires is_vertex_set l /\ Seq.length l > 0)
                              (ensures (forall x. Seq.mem x l ==> count l x == 1))
                              
val is_vertex_set_lemma : (l: vertex_list) ->
                        Lemma (ensures (is_vertex_set l /\ length l > 0 ==> is_vertex_set (tail l)))

val is_vertex_set_cons : (hd:vertex_id) ->
                         (l: seq vertex_id{is_vertex_set l}) ->
                     Lemma
                     (requires ~(Seq.mem hd l))
                     (ensures (is_vertex_set (cons hd l)))
                     (decreases (length l))

val is_vertex_set_lemma1 : (l: vertex_list) ->
                        Lemma (ensures (length l == 0 ==> is_vertex_set l))

val is_vertex_set_lemma2 : (l: vertex_list) ->
                        Lemma (ensures (length l == 1 ==> is_vertex_set l))

let vertex_set = v: vertex_list{is_vertex_set v}

val is_vertex_set_lemma3 : (l: seq Usize.t) ->
                        Lemma (ensures (is_vertex_set l /\ length l > 0 ==> is_vertex_set (slice l 0 (length l - 1))))
                        
val is_vertex_set_lemma4 : (l: vertex_list) ->
                        Lemma (ensures (is_vertex_set l /\ length l > 0 ==> ~(Seq.mem (Seq.head l) (Seq.tail l))))

val is_vertex_set_lemma5 : (l: vertex_list) ->
                        Lemma (ensures (is_vertex_set l /\ length l > 0 ==> ~(Seq.mem (Seq.index l (length l - 1)) 
                                                          (slice l 0 (length l - 1)))))
                        (decreases length l)

val is_vertex_set_lemma6 : (l: vertex_list) ->
                           (i:UInt32.t) ->
                      Lemma
                      (ensures ((UInt32.v i < Seq.length l) /\ 
                                 is_vertex_set (Seq.slice l (UInt32.v i) (Seq.length l))) ==>
                                 is_vertex_set (Seq.slice l (UInt32.v i + 1) (Seq.length l)))

val is_vertex_set_lemma7 : (l: vertex_list) ->
                           (i:UInt32.t) ->
                     Lemma 
                     (ensures (UInt32.v i < Seq.length l) /\
                              is_vertex_set (Seq.slice l (UInt32.v i) (Seq.length l)) ==>
                                ~(Seq.mem (Seq.index l (UInt32.v i)) (Seq.slice l (UInt32.v i + 1) (Seq.length l))))
                     

val is_edge_set :  (edge_list) ->
                     Tot (bool)

val is_edge_set_lemma : (l: edge_list) ->
                        Lemma (ensures (is_edge_set l /\ length l > 0 ==> is_edge_set (tail l)))

val is_edge_set_lemma1 : (l: edge_list) ->
                        Lemma (ensures (length l == 0 ==> is_edge_set l))

val is_edge_set_lemma2 : (l: edge_list) ->
                        Lemma (ensures (length l == 1 ==> is_edge_set l))

let edge_set   = e: edge_list{is_edge_set e }

val is_edge_set_lemma3 : (l: edge_list) ->
                        Lemma (ensures (is_edge_set l /\ length l > 0 ==> is_edge_set (slice l 0 (length l - 1))))
                        

val is_edge_set_lemma4 : (l: edge_list) ->
                        Lemma (ensures (is_edge_set l /\ length l > 0 ==> ~(Seq.mem (Seq.head l) (Seq.tail l))))

val vertex_mem: v_id:vertex_id -> 
                vs:vertex_list -> 
                b:bool{(b = true ==> Seq.mem v_id vs) /\
                       (b == false ==> ~(Seq.mem v_id vs) /\
                       (b == false ==> (forall (j:nat). j < Seq.length vs ==> Seq.index vs j <> v_id)))}

let rec mem_index_count (#a:eqtype) (x:a) (s:Seq.seq a)
    : Lemma 
            (ensures ((forall i. Seq.index s i <> x) ==> Seq.count x s == 0))
            (decreases (Seq.length s)) = 
if Seq.length s = 0 then () else 
  mem_index_count x (tail s) 


val edge_mem: e_id:edge -> es:edge_list -> b:bool{b = true <==> Seq.mem e_id es}

/// Currently not used--------------------------------------------------------------------------------------------------------------------
type vertex_map (a:Type0) (len:nat) = s:seq a{length s == len} 
 
type edge_map (b:Type0) (len:nat) = s:seq b{length s == len}
/// --------------------------------------------------------------------------------------------------------------------------------------
(*A graph is represented using 2 fields:
  1. A sequence of vertices. Vertex_id 0 will be in index 0, vertex_id n will be in index n like that
  2. A sequence of edges.
/// --------------------------------------------------------------------------------------------------------------------------------------
  /// Not used
  3. A sequence of map of vertex_id to its attributes of type option alpha. When a vertex_id is removed from a graph, its
     correcponding attribute should be made None. If a vertex_id is added to a graph, then its attribute should be Some alpha.
  4. A sequence of map of edge to its attributes of type option bete. When an edge is removed from a graph, its 
     correcponding attribute should be made None. If an edge is added to a graph, then its attribute should be Some beta.
     First, the index of edge is found out from edge_set. Then that index in e_map will be updated with the attribute value*)
/// ---------------------------------------------------------------------------------------------------------------------------------------

noeq type graph_state (#a:eqtype) (#b:eqtype) = {

 vertices       : v:vertex_list{is_vertex_set v}; 
 edge_set       : e: edge_list {(forall x. edge_mem x e ==> vertex_mem (fst x) vertices /\
                                vertex_mem (snd x) vertices)}
}


(*val get_v_attribute : (#a:eqtype)-> 
                      (#b:eqtype)->
                      (g:graph_state #a #b) ->
                      (v:vertex_id{vertex_mem v (g.vertices) /\ UInt32.v v < (length g.vertices)}) -> Tot a
val get_e_attribute : (#a:eqtype)-> 
                      (#b:eqtype)->
                      (g:graph_state #a #b) ->
                      (e:edge{mem e (g.edge_set) /\ index_mem e (g.edge_set) < (length g.edge_set)}) ->  Tot b 
val set_v_attribute : (#a:eqtype)-> 
                      (#b:eqtype)->
                      (g:graph_state #a #b) ->
                      (v:vertex_id{vertex_mem v (g.vertices) /\ UInt32.v v < (length g.vertices)}) -> 
                      (value: a) ->
                      (graph_state #a #b)
                      
val set_e_attribute : (#a:eqtype)-> 
                      (#b:eqtype)->
                      (g:graph_state #a #b) ->
                      (e:edge{mem e (g.edge_set) /\ index_mem e (g.edge_set) < (length g.edge_set)}) -> 
                      (value: b) ->
                      (graph_state #a #b)*)

val cardinality : (#a:eqtype)-> 
                      (#b:eqtype)->
                  (g:graph_state #a #b) -> 
                  Tot nat

 let cardinal1 vs = length vs


let mem_graph_vertex (#a:eqtype)
                     (#b:eqtype)
                     (g:graph_state #a #b) 
                     (x: vertex_id) 
         : Tot (b: bool {b = true <==> vertex_mem x g.vertices}) = 
if (vertex_mem x (g.vertices)) then true else false

let mem_graph_edge (#a:eqtype)
                   (#b:eqtype)
                   (g:graph_state #a #b) 
                   (x: vertex_id) 
                   (y: vertex_id) 
          : Tot (b: bool {b = true <==> edge_mem (x,y) (g.edge_set) /\ mem_graph_vertex g x /\
                             mem_graph_vertex g y})= 
if (edge_mem (x,y) (g.edge_set) && mem_graph_vertex g x && mem_graph_vertex g y) then true else false 

(*Reachability defined as an inductive predicate and lemmas on reachability**************************************************)
noeq type reach: (#a:eqtype)-> 
                 (#b:eqtype)->
                 (g:graph_state #a #b) ->
                 (x:vertex_id{mem_graph_vertex g x}) -> 
                 (y:vertex_id{mem_graph_vertex g y}) -> Type =

  | ReachRefl  :  (#a:eqtype)-> 
                  (#b:eqtype)->
                  (g:graph_state #a #b) ->
                  (x:vertex_id{mem_graph_vertex  g x}) ->
                  (reach g x x)


  | ReachTrans :  (#a:eqtype)-> 
                  (#b:eqtype)->
                  (g:graph_state #a #b) ->
                  (x:vertex_id{mem_graph_vertex g x}) ->
                  (y:vertex_id{mem_graph_vertex g y}) ->
                  (z:vertex_id{mem_graph_vertex g z /\ mem_graph_edge g y z}) ->
                 
                  (reach g x y) ->
                  (reach g x z)  


val reachfunc: (#a:eqtype)-> 
               (#b:eqtype)->
               (g:graph_state #a #b) ->
               (x:vertex_id{mem_graph_vertex g x}) ->
               (y:vertex_id{mem_graph_vertex g y}) ->
               (r: reach g x y) ->
               Tot bool


val subset_vertices : (s1: vertex_list{is_vertex_set s1}) ->
                      (s2: vertex_list{is_vertex_set s2}) ->
                Pure (bool)
                (requires True)
                (ensures (fun b -> (forall x. vertex_mem x s1 ==> vertex_mem x s2) <==> (b = true)))

val edge_rel  :  (#a:eqtype)-> 
                 (#b:eqtype)->
                 (g:graph_state #a #b) ->
                 (x: vertex_id)->
                 (y: vertex_id) ->
         Tot (b:bool{b = true <==> mem_graph_edge g x y})

val vertices_in_path :(#a:eqtype)-> 
                      (#b:eqtype)->
                      (g:graph_state #a #b) ->
                      (x:vertex_id{mem_graph_vertex g x}) ->
                      (y:vertex_id{mem_graph_vertex g y}) ->
                      (r: reach g x y) ->
                      Tot vertex_list

val subset_vertices_in_path :  (#a:eqtype)-> 
                                (#b:eqtype)->
                                (g:graph_state #a #b) ->
                                (s1: vertex_list)->
                                (s2: vertex_list) ->
                                Pure (bool)
                                (requires True)
                                (ensures (fun b -> (forall x. vertex_mem x s1 ==> vertex_mem x s2) <==> (b = true)))

val subset_vertices_in_path_lemma : (#a:eqtype)-> 
                                    (#b:eqtype)->
                                    (g:graph_state #a #b) ->
                                    (s1: vertex_list)->
                                    (s2: vertex_list) ->
                                    Lemma (ensures (forall x. (subset_vertices_in_path g s1 s2 /\ vertex_mem x s1) ==> 
                                                          vertex_mem x s2))
                                   [SMTPat (subset_vertices_in_path g s1 s2)]
                                   
val remove :   (s1: vertex_set)->
               (x: vertex_id{mem x s1})->
   Tot (r: vertex_set{ ~(mem x r)/\
                      (length r + 1 == length s1)/\
                     (forall y. y <> x ==> (mem y r <==> mem y s1))})


val subset_lemma   : (s1: vertex_set) ->
                     (s2: vertex_set) ->
                     Lemma (requires (subset_vertices s1 s2))
                     (ensures (cardinal1 s1 <= cardinal1 s2))
                     [SMTPat (subset_vertices s1 s2)]

val is_vertex_set_lemma8 : (l: vertex_set) ->
                           (x: vertex_id{mem x l})->
                        Lemma (ensures (is_vertex_set (remove l x)))
                        

let slice_membership_lemma_reach_x_2 (#a:eqtype)
                                     (#t:eqtype)
                                     (g:graph_state #a #t)
                                     (r : vertex_list{(forall x. vertex_mem x r ==> vertex_mem x (g.vertices))})
                                     (y:vertex_id{Seq.mem y r})
                                     (root_set : vertex_set{subset_vertices root_set (g.vertices)})
                   : Lemma
                   (requires ((forall x. vertex_mem x r ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\
                                                                         reachfunc g o x z1))))
                   (ensures (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1)) = ()

val subset_equal : (s1: seq vertex_id{is_vertex_set s1}) ->
                   (s2: seq vertex_id{is_vertex_set s2}) ->
              Lemma
              (requires (subset_vertices s1 s2) /\ (subset_vertices s2 s1))
              (ensures (Seq.length s1 == Seq.length s2))

val subset_of_each_other :(s1: seq vertex_id{is_vertex_set s1}) ->
                          (s2: seq vertex_id{is_vertex_set s2}) ->
            Lemma 
            (requires (subset_vertices s1 s2) /\ Seq.length s1 == Seq.length s2)
            (ensures (subset_vertices s2 s1)) 

val vertices_in_sub_path_lemma : (#a:eqtype)-> 
                                 (#b:eqtype)->
                                 (g:graph_state #a #b) ->
                                 (x:vertex_id{mem_graph_vertex g x}) ->
                                 (y:vertex_id{mem_graph_vertex g y}) ->
                                 (r: reach g x y) ->
                                 
                                 Lemma (ensures (forall w r_xw. (mem_graph_edge g w y /\ (r == ReachTrans g x w y r_xw) ==> 
                                                    subset_vertices_in_path g (vertices_in_path g x w r_xw) 
                                                                                (vertices_in_path g x y r))))
val path_length :   (#a:eqtype)-> 
                    (#b:eqtype)->
                    (g:graph_state #a #b) ->
                    (x:vertex_id{mem_graph_vertex g x}) ->
                    (y:vertex_id{mem_graph_vertex g y}) ->
                    (r: reach g x y) ->
                    Tot nat

val reach_vertices_in_path_lemma :   (#a:eqtype)-> 
                                     (#b:eqtype)->
                                     (g:graph_state #a #b) ->
                                     (x:vertex_id{mem_graph_vertex g x}) ->
                                     (y:vertex_id{mem_graph_vertex g y}) ->
                                     (r: reach g x y) ->
                           
                                     Lemma 
                                     (ensures (forall a. vertex_mem a (vertices_in_path g x y r) ==> 
                                             (exists (r1: reach g a y). reachfunc g a y r1 /\
                                          subset_vertices_in_path g (vertices_in_path g a y r1) 
                                                                      (vertices_in_path g x y r) /\
                                          (path_length g a y r1) < (path_length g x y r) )))

val shortest_path_lemma :   (#a:eqtype)->
                            (#t:eqtype) ->
                            (g:graph_state #a #t) ->
                            (s: vertex_id{mem_graph_vertex g s}) ->
                            (b: vertex_id{mem_graph_vertex g b}) ->
                            (r: reach g s b) ->
                            
                            Lemma 
                            (ensures (exists (rs: reach g s b). ~(vertex_mem s (vertices_in_path g s b rs)) /\ 
                             subset_vertices_in_path g (vertices_in_path g s b rs) 
                                                          (vertices_in_path g s b r)))

val reach_reflexive_constructor : (#a:eqtype)->
                                  (#t:eqtype) ->
                                  (g:graph_state #a #t) ->
                                  (x: vertex_id{mem_graph_vertex g x}) ->
                                
                                  Tot (reach g x x) 

val edge_reach_constructor      : (#a:eqtype)->
                                  (#t:eqtype) ->
                                  (g:graph_state #a #t) ->
                                  (x: vertex_id{mem_graph_vertex g x}) ->
                                  (y: vertex_id{mem_graph_vertex g y /\  mem_graph_edge g x y}) ->
               
                                  Tot (reach g x y)
            

val reflex_lemma :  (#a:eqtype)->
                    (#t:eqtype) ->
                    (g:graph_state #a #t) ->
                    (x: vertex_id{mem_graph_vertex g x}) ->
                    
                    Lemma
                   (ensures (exists (r: (reach g x x)). (reachfunc g x x r))) 
                   
val reflex_lemma1 : (#a:eqtype)->
                    (#t:eqtype) ->
                    (g:graph_state #a #t) ->
                    (x: vertex_id{mem_graph_vertex g x}) ->
                    
                    Lemma
                   (ensures (reachfunc g x x (ReachRefl g x))) 


val reflex_lemma_list : (#a:eqtype)->
                        (#t:eqtype) ->
                        (g:graph_state #a #t) ->
                        (l: vertex_set{subset_vertices l (g.vertices)}) ->
                    Lemma
                   (ensures (forall x. vertex_mem x l ==> (exists (r: (reach g x x)). (reachfunc g x x r)))) 

val reachability_lemma : (#a:eqtype)->
                         (#t:eqtype) ->
                         (g:graph_state #a #t) ->
                         (x: vertex_id{mem_graph_vertex g x}) ->
                         (y: vertex_id{mem_graph_vertex g y}) ->
                         (r: reach g x y) ->
                         
                         Lemma
                         (ensures (x = y  \/ (exists (z: vertex_id{mem_graph_vertex g z}) (r1: (reach g x z)). mem_graph_edge g z y)))

val add_to_vertex_set : (#a:eqtype)->
                        (#t:eqtype) ->
                        (g:graph_state #a #t) ->
                        (y: vertex_id{mem_graph_vertex g y}) ->
                        (l: vertex_set {subset_vertices l (g.vertices)}) ->
                   Tot (vertex_set)

val  append_reach : (#a:eqtype)->
                    (#t:eqtype) ->
                    (g:graph_state #a #t) ->
                    (x: vertex_id{mem_graph_vertex g x}) ->
                    (y: vertex_id{mem_graph_vertex g y}) ->
                    (l: vertex_set {subset_vertices l (g.vertices)}) ->
                 
                    Lemma
                    (requires ((exists (r1: reach g x y). reachfunc g x y r1) /\ (forall z. vertex_mem z l ==> 
                               (exists (r2: reach g x z). reachfunc g x z r2))))
                    (ensures (forall z. vertex_mem z (add_to_vertex_set g y l) ==> (exists (r2: reach g x z). reachfunc g x z r2)))

val snoc_unique_lemma : (s:vertex_id) ->
                        (e': vertex_set) ->
                    Lemma
                     (requires (~(mem s e') /\ (length e' <> 0)))
                     (ensures (is_vertex_set (snoc e' s))) 
                     
val snoc_unique_lemma_edge : (s:edge) ->
                             (e': edge_set) ->
                    Lemma
                     (requires (~(mem s e') /\ (length e' <> 0)))
                     (ensures (is_edge_set (snoc e' s))) 

val successors_fn2 :  (i: vertex_id)->
                      (e: edge_list)->
           Tot (sl : vertex_list{(forall x. vertex_mem x sl <==> edge_mem (i,x) e) /\
                                  (forall x. edge_mem (i,x) e ==> vertex_mem x sl)})
           (decreases length e)                      
         
                     
(*Finds successors of i, from the edge_set of graph g*)
val successors    : (#a:eqtype)->
                    (#t:eqtype) ->
                    (g:graph_state #a #t) ->
                    (i: vertex_id {mem_graph_vertex g i}) ->
                    
                    Tot (sl : vertex_list{(forall x. Seq.mem x sl ==> Seq.mem x (g.vertices)) /\
                             (forall x. vertex_mem x sl <==> mem_graph_edge g i x) /\
                             (forall x. vertex_mem x sl <==> edge_mem (i,x) g.edge_set)}) 

val successors_successors_fn2_connect_lemma : (#a:eqtype)->
                                              (#t:eqtype) ->
                                              (g:graph_state #a #t) ->
                                              (i: vertex_id {mem_graph_vertex g i}) ->
                            Lemma
                            (ensures (successors g i == successors_fn2 i g.edge_set))
         

let rec pick_second (s:seq edge) 
                    
               : Tot (seq Usize.t)
                 (decreases length s) = 
  if length s = 0 then Seq.empty
  else
  (
    let hd = Seq.head s in
    assert (hd == Seq.index s 0);
    let tl = Seq.tail s in
    assert (tl == Seq.slice s 1 (length s));
    let second_val = snd hd in
    let rest_vals = pick_second tl in
    lemma_tl second_val rest_vals;
    let sl = cons second_val rest_vals in
    sl
  )

let pick_second_lemma (s:seq edge)
              : Lemma
                (requires (Seq.length s > 0))
                (ensures (pick_second s == Seq.cons (snd (Seq.head s)) (pick_second (Seq.tail s)))) = ()

let rec pick_second_length_lemma (s:seq edge) 
                      : Lemma
                        (ensures Seq.length (pick_second s) == Seq.length s)
                        (decreases length s) = 
 if length s = 0 then ()
  else
  (
    let hd = Seq.head s in
    assert (hd == Seq.index s 0);
    let tl = Seq.tail s in
    assert (tl == Seq.slice s 1 (length s));
    let second_val = snd hd in
    let rest_vals = pick_second tl in
    pick_second_length_lemma tl;
    assert (Seq.length rest_vals == Seq.length tl);
    lemma_tl second_val rest_vals;
    let sl = cons second_val rest_vals in
    assert (Seq.length sl == (Seq.length rest_vals) + 1);
    assert (Seq.length sl == Seq.length tl + 1);
    assert (Seq.length sl == Seq.length s);
    ()
  )

let rec pick_second_mem_lemma (#a:eqtype)
                              (#t:eqtype)
                              (g:graph_state #a #t)
                              (s:seq edge{forall x. Seq.mem x s ==> mem_graph_vertex g (snd x)}) 
                      : Lemma
                        (ensures (forall x. Seq.mem x (pick_second s) ==>  mem_graph_vertex g x))
                        (decreases length s) = 
 if length s = 0 then ()
  else
  (
    let hd = Seq.head s in
    assert (hd == Seq.index s 0);
    let tl = Seq.tail s in
    assert (tl == Seq.slice s 1 (length s));
    let second_val = snd hd in
    let rest_vals = pick_second tl in
    pick_second_mem_lemma g tl;
    assert (forall x. Seq.mem x (pick_second tl) ==>  mem_graph_vertex g x);
    lemma_tl second_val rest_vals;
    let sl = cons second_val rest_vals in
    assert (forall x. Seq.mem x (pick_second s) ==>  mem_graph_vertex g x);
    ()
  )
  

val successors_fn2_pick_second_lemma : (i: vertex_id) ->
                                       (e: edge_list{(forall x. Seq.mem x e ==> (fst x == i))}) ->
                           Lemma 
                           (ensures successors_fn2 i e == pick_second e)


val successors_fn2_e2_is_successors_fn2_e_if_no_fst_i_in_e1 : (i: vertex_id) ->
                                                              (e: edge_list{(forall x. Seq.mem x e ==> (fst x == i))}) ->
                                                              (e1:edge_list{~(exists x. Seq.mem x e1 /\ (fst x) == i)}) ->
                                                              (e2:edge_list{e2 == Seq.append e e1})->
                Lemma
                (successors_fn2 i e2 == successors_fn2 i e)


val successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e : (tl: vertex_list) ->
                                                               (e:edge_list{forall x. Seq.mem x tl ==>
                                                                  ~(exists y. Seq.mem y e /\ (fst y) == x)}) ->
                                                               (e1:edge_list) ->
                                                               (e2:edge_list{e2 == Seq.append e e1}) ->
                Lemma
                (forall x. Seq.mem x tl ==> (successors_fn2 x e2 == successors_fn2 x e1))

let next (h_index: Usize.t{UInt.fits (Usize.v h_index + 8) Usize.n}) 
         : Tot (f:Usize.t{Usize.v f == Usize.v h_index + 8})=
  let f_index = Usize.add h_index 8UL in
 
  f_index

let previous (st_index: Usize.t{UInt.fits (Usize.v st_index - 8) Usize.n})
          : Tot (h:Usize.t{Usize.v h == Usize.v st_index - 8}) = 
  let h_index = Usize.sub st_index 8UL in
  h_index

#restart-solver 

val subset_vertices_variant :   (s1: vertex_list{is_vertex_set s1}) -> 
                                (s2: vertex_list{is_vertex_set s2}) ->
                 Pure (bool)
                (requires 
                      (forall x. Seq.mem x s1 ==> UInt.fits (Usize.v x - 8) Usize.n))
                       
                (ensures (fun b -> (forall x. Seq.mem x s1 ==> Seq.mem (previous x) s2) <==> (b = true))) 
                
val subset_variant_lemma :   (s1: vertex_set)->
                             (s2: vertex_set)->
        Lemma (requires (forall x. Seq.mem x s1 ==> UInt.fits (Usize.v x - 8) Usize.n) /\
                        (subset_vertices_variant  s1 s2))
              (ensures (length s1 <= length s2))
               
val subset_of_each_other1 :   (s1: seq Usize.t{is_vertex_set s1})->
                              (s2:  seq Usize.t{is_vertex_set s2}) ->
            Lemma 
            (requires (*(forall x. Seq.mem x s1 ==> is_hp_addr x) /\*)
                      (forall x. Seq.mem x s1 ==> UInt.fits (Usize.v x - 8) Usize.n) /\
                      (forall x. Seq.mem x s1 ==> Seq.mem (previous x) s2) /\ 
                      Seq.length s1 == Seq.length s2)
            (ensures (forall x. Seq.mem x s2 ==> Seq.mem (next x) s1)) 
            (decreases (length s1))


type hp_addr = h:Usize.t {Usize.v h >= 0 /\ Usize.v h < 1024 /\ (Usize.v h % 8 == 0)}


let next_wrapper (h_index: hp_addr{UInt.fits (Usize.v h_index + 8) Usize.n /\ (Usize.v h_index + 8 < 1024)})
           : Tot (p:hp_addr{Usize.v p == Usize.v h_index + 8})= 
  let p = next h_index in
  assert (Usize.v h_index % 8 == 0);
  assert (Usize.v p == Usize.v h_index + 8);
  assert (Usize.v p < 1024);
  assert (Usize.v p % 8 == 0);
  p
  
val successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e' : (tl: vertex_list)->
                                                                (e:edge_list{forall x. Seq.mem x tl  /\
                                                                          UInt.fits (Usize.v x + 8) Usize.n ==>
                                                                  ~(exists y. Seq.mem y e /\ (fst y) == next x)})->
                                                                (e1:edge_list)->
                                                                (e2:edge_list{e2 == Seq.append e e1})-> 
                                    Lemma
                                    (forall x. Seq.mem x tl ==> (successors_fn2 (next x) e2 == successors_fn2 (next x) e1))

val successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e'' : (tl: vertex_list)->
                                                                (e:edge_list{forall x. Seq.mem x tl  /\
                                                                          UInt.fits (Usize.v x + 8) Usize.n ==>
                                                                  ~(exists y. Seq.mem y e /\ (fst y) == next_wrapper x)})->
                                                                (e1:edge_list)->
                                                                (e2:edge_list{e2 == Seq.append e e1})-> 
                                    Lemma
                                    (forall x. Seq.mem x tl ==> (successors_fn2 (next_wrapper x) e2 == successors_fn2 (next_wrapper x) e1))

   
val edge_reach_lemma_succ : (#a:eqtype)->
                            (#t:eqtype) ->
                            (g:graph_state #a #t) ->
               
               Lemma 
               (ensures (forall x y. edge_mem(x,y) (g.edge_set) ==> 
                           reachfunc g x y (edge_reach_constructor g x y)))


val succ_reach_lemma : (#a:eqtype)->
                       (#t:eqtype) ->
                       (g:graph_state #a #t) ->
                       (x: vertex_id{mem_graph_vertex g x}) ->
                 
                 Lemma
                 (ensures (forall y. vertex_mem y (successors g x) ==> 
                             reachfunc g x y (edge_reach_constructor g x y))) 


val reach_lemma_transitive : (#a:eqtype)->
                             (#t:eqtype) ->
                             (g:graph_state #a #t) ->
                             (x: vertex_id{mem_graph_vertex g x}) ->
                             (y: vertex_id{mem_graph_vertex g y /\ mem_graph_edge g x y}) ->
                             (o: vertex_id{mem_graph_vertex g o}) ->
                             (r: reach g o x) ->

                             Lemma
                             (ensures (exists (z3: reach g o y). reachfunc g o y z3))

val reach_lemma_transitive_list  :  (#a:eqtype)->
                                    (#t:eqtype) ->
                                    (g:graph_state #a #t) ->
                                    (x: vertex_id{mem_graph_vertex g x}) ->
                                    (l: vertex_list{(forall x. Seq.mem x l ==> Seq.mem x (g.vertices)) /\ 
                                                     (forall y. vertex_mem y l ==> mem_graph_edge g x y)}) ->
                                    (o: vertex_id{mem_graph_vertex g o}) ->
                                    (r: reach g o x) ->

                                    Lemma
                                    (ensures (forall y. vertex_mem y l ==> 
                                                   (exists (z3: reach g o y). (reachfunc g o y z3))))

val reachability_non_dependent_on_attributes_lemma :  (#a:eqtype)->
                                                      (#b:eqtype) ->
                                                      (g:graph_state #a #b) ->
                                                      (g':graph_state #a #b) ->
                                                      (root: vertex_id{mem_graph_vertex g root}) ->
                                                  
                                 Lemma
                                (requires (g.vertices == g'.vertices /\ g.edge_set == g'.edge_set))
                                (ensures (forall x. mem_graph_vertex g x /\ 
                                            (exists (p: reach g root x).reachfunc g root x p) ==>
                                            (exists (p1: reach g' root x).reachfunc g' root x p1)))

val succ_reach_transitive_lemma :  (#a:eqtype)->
                                   (#t:eqtype) ->
                                   (g:graph_state #a #t) ->
                                   (o: vertex_id{mem_graph_vertex g o}) ->
                                   (x: vertex_id{mem_graph_vertex g x}) ->
                                   (r: reach g o x) ->
                        
                                   Lemma
                                   (ensures (forall y. vertex_mem y (successors g x) ==> 
                                                  (exists (r1: reach g o y).reachfunc g o y r1))) 

val succ_reach_transitive_lemma1 : (#a:eqtype)->
                                   (#t:eqtype) ->
                                   (g:graph_state #a #t) ->
                                   (o: vertex_id{mem_graph_vertex g o}) ->
                                   (x: vertex_id{mem_graph_vertex g x}) ->
                                   
                                   Lemma
                                   (requires (exists (p: (reach g o x)). reachfunc g o x p))
                                   (ensures (forall y. vertex_mem y (successors g x) ==> 
                                                  (exists (r1: reach g o y).reachfunc g o y r1))) 
                                        


val succ_reach_transitive_lemma3 :   (#a:eqtype)->
                                     (#t:eqtype) ->
                                     (g:graph_state #a #t) ->
                                     (x: vertex_id{mem_graph_vertex g x}) ->
                                     (y: vertex_id{mem_graph_vertex g y}) ->
                                     (r: reach g x y{ReachRefl? r = false})->

                                     Lemma
                                     (ensures (exists (z: vertex_id{vertex_mem z (successors g x)}). 
                                                  (exists (r2: reach g z y).reachfunc g z y r2 /\
                                                   subset_vertices_in_path g (vertices_in_path g z y r2) 
                                                                               (vertices_in_path g x y r) /\
                                               (~(ReachRefl? r2) ==> vertex_mem z (vertices_in_path g x y r)) /\
                                               (ReachRefl? r2 ==> (mem_graph_edge g x y) /\ r ==
                                                ReachTrans g x x y (ReachRefl g x)))))

val createEmptySet : (#a:eqtype)->
                     (#t:eqtype) ->
                     (g:graph_state #a #t) -> 
         vs: vertex_set{subset_vertices vs (g.vertices) /\ vs == empty}

val empty_set_mem : (vl: vertex_set {vl == empty}) -> 
                    (r: vertex_set) ->
      Lemma (ensures (forall (x:vertex_id) . ((mem x vl) ==> ~(mem x r)) /\ ((mem x r) ==> ~ (mem x vl))))

val nonEmpty_set : (s: vertex_set) -> 
                   (b: bool{b == true <==> length s > 0})

val is_emptySet : (s: vertex_set) -> 
                  (b: bool{b == true <==> length s == 0 })

val empty_set_subset_all_sets : (s: vertex_set{is_emptySet s}) ->
                                (vl: vertex_set) ->
                Lemma (subset_vertices s vl)
                
val negation_nonEmpty_implies_empty : (s: vertex_set) ->
                Lemma (~(nonEmpty_set s) ==> is_emptySet s)


val get_head  : (#a:eqtype)->
                (#t:eqtype) ->
                (g:graph_state #a #t) ->
                (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})->
                Tot (x: vertex_id{mem_graph_vertex g x /\ vertex_mem x s /\ (x == index s 0)})
                

val get_tail  : (#a:eqtype)->
                (#t:eqtype) ->
                (g:graph_state #a #t) ->
                (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})->
                Tot (s': vertex_set{subset_vertices s' (g.vertices) /\ (forall x. vertex_mem x s' ==> vertex_mem x s) /\
                                     equal s' (tail s)})

val get_last_elem  : (#a:eqtype)->
                     (#t:eqtype) ->
                     (g:graph_state #a #t) ->
                     (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})->
                Tot (x: vertex_id{mem_graph_vertex g x /\ vertex_mem x s /\ (x == index s (length s - 1))})

val get_first  :(#a:eqtype)->
                (#t:eqtype) ->
                (g:graph_state #a #t) ->
                (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})->
                Tot (s': vertex_set{equal s' (slice s 0 (length s - 1)) /\
                                   (forall x. vertex_mem x s' ==> vertex_mem x s) /\
                                   subset_vertices s' (g.vertices) /\
                                   (forall x. Seq.mem x s /\ (x <> (index s (length s - 1))) ==> Seq.mem x s')})



val head_tail_set_connect_lemma : (#a:eqtype)->
                                  (#t:eqtype) ->
                                  (g:graph_state #a #t) ->
                                  (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})->
                   Lemma 
                  (ensures (forall c. vertex_mem c r /\ ~(vertex_mem c (get_tail g r)) ==> c = (get_head g r)))

val last_first_set_connect_lemma_helper : (#a:eqtype)->
                                          (#t:eqtype) ->
                                          (g:graph_state #a #t) ->
                                          (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})->
                                          (c:vertex_id{vertex_mem c r}) ->
                   Lemma 
                  (ensures (~(vertex_mem c (get_first g r)) ==> c = (get_last_elem g r)))

val last_first_set_connect_lemma : (#a:eqtype)->
                                   (#t:eqtype) ->
                                   (g:graph_state #a #t) ->
                                   (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})->
                   Lemma 
                  (ensures (forall c. vertex_mem c r /\ ~(vertex_mem c (get_first g r)) ==> c = (get_last_elem g r)))

val head_tail_set_connect_lemma1 : (#a:eqtype)->
                                   (#t:eqtype) ->
                                   (g:graph_state #a #t) ->
                                   (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})->
                   Lemma 
                  (ensures (forall c. vertex_mem c r /\ c <> (get_head g r) ==> vertex_mem c (get_tail g r)))

val last_first_set_connect_lemma1_helper : (#a:eqtype)->
                                           (#t:eqtype) ->
                                           (g:graph_state #a #t) ->
                                           (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})->
                                           (c:vertex_id{vertex_mem c r}) ->
                   Lemma 
                  (ensures (c <> (get_last_elem g r) ==> vertex_mem c (get_first g r)))

val last_first_set_connect_lemma1 : (#a:eqtype)->
                                    (#t:eqtype) ->
                                    (g:graph_state #a #t) ->
                                    (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})->
                   Lemma 
                  (ensures (forall c. vertex_mem c r /\ c <> (get_last_elem g r) ==> vertex_mem c (get_first g r)))


val get_head_mem_lemma  : (#a:eqtype)->
                          (#t:eqtype) ->
                          (g:graph_state #a #t) ->
                          (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})->
                   Lemma (ensures (~(vertex_mem (get_head g s) (get_tail g s))))

val get_tail_mem_lemma : (#a:eqtype)->
                         (#t:eqtype) ->
                         (g:graph_state #a #t) ->
                         (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})->
                         (vl: vertex_set{subset_vertices s (g.vertices) /\ (forall x. vertex_mem x s ==> ~(vertex_mem x vl))}) ->
                    Lemma (ensures (forall x. vertex_mem x (get_tail g s) ==> ~(vertex_mem x vl)))   

val get_tail_length_lemma : (#a:eqtype)->
                            (#t:eqtype) ->
                            (g:graph_state #a #t) ->
                            (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})->
                            
                    Lemma (ensures (cardinal1 (get_tail g s) < cardinal1 s))   

val get_last_mem_lemma  : (#a:eqtype)->
                          (#t:eqtype) ->
                          (g:graph_state #a #t) ->
                          (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})->
                   Lemma (ensures (~(vertex_mem (get_last_elem g s) (get_first g s))))

val get_first_mem_lemma : (#a:eqtype)->
                         (#t:eqtype) ->
                         (g:graph_state #a #t) ->
                         (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})->
                         (vl: vertex_set{subset_vertices s (g.vertices) /\ (forall x. vertex_mem x s ==> ~(vertex_mem x vl))}) ->
                    Lemma (ensures (forall x. vertex_mem x (get_first g s) ==> ~(vertex_mem x vl)))   

val get_first_length_lemma : (#a:eqtype)->
                            (#t:eqtype) ->
                            (g:graph_state #a #t) ->
                            (s: vertex_set{subset_vertices s (g.vertices) /\ nonEmpty_set s})->
                            
                    Lemma (ensures (cardinal1 (get_first g s) < cardinal1 s))   



(*Inserts a x vertex to a passed in vertex set s if x is not memeber of s *)
val insert_to_vertex_set : (#a:eqtype)->
                           (#t:eqtype) ->
                           (g:graph_state #a #t) ->
                           (x: vertex_id{mem_graph_vertex g x}) ->
                           (s: vertex_set{subset_vertices s (g.vertices)}) ->
                            
                            Tot(s':vertex_set{subset_vertices s' (g.vertices) /\ (cardinal1 (g.vertices) >= cardinal1 s') /\ 
                                               (subset_vertices s s') /\ vertex_mem x s' /\ (length s <= length s') /\
                                                (~(vertex_mem x s) ==> length s' == length s + 1) /\
                                                (~(vertex_mem x s) ==> Seq.index s' (length s) == x) /\
                                                (~(vertex_mem x s) /\ (length s > 0) ==> (s' == (Seq.snoc s x))) /\
                                                (vertex_mem x s ==> s' == s) /\
                                                (~(vertex_mem x s) /\ (length s == 0) ==> (s' == Seq.create 1 x)) /\
                                                (~(exists y. (Seq.mem y s') /\ ~(Seq.mem y s) /\ y <> x))})
(*Useful to write a auxillary function with all post conditions and just call that auxillary post condition function instead of all conditions.*)

val reach_singleton : (#a:eqtype)->
                      (#t:eqtype) ->
                      (g:graph_state #a #t) ->
                      (x: vertex_id{mem_graph_vertex g x})->
                      (r : vertex_set{r == insert_to_vertex_set g x (createEmptySet g)}) ->
               Lemma (ensures (forall y. vertex_mem y r ==> (exists (z1: reach g x y). reachfunc g x y z1)))

val reach_empty : (#a:eqtype)->
                  (#t:eqtype) ->
                  (g:graph_state #a #t) ->
                  (x: vertex_id{mem_graph_vertex g x})->
                  (vl: vertex_set{subset_vertices vl (g.vertices) /\ vl == empty})->
               Lemma (ensures (forall y. vertex_mem y vl ==> (exists (z1: reach g x y). reachfunc g x y z1)))

val reach_from_x_equals_reach_from_singleton_x_set : (#a:eqtype)->
                                                     (#t:eqtype) ->
                                                     (g:graph_state #a #t) ->
                                                     (x: vertex_id{mem_graph_vertex g x})->
                                                     (r : vertex_set{r == insert_to_vertex_set g x (createEmptySet g)}) ->
               Lemma (ensures (forall y (z2: reach g x y). (reachfunc g x y z2) ==> 
                            (exists p (z3: reach g p y). reachfunc g p y z3 /\ vertex_mem p r)))

val insert_to_vertex_set_lemma : (#a:eqtype)->
                                 (#t:eqtype) ->
                                 (g:graph_state #a #t) ->
                                 (x: vertex_id{mem_graph_vertex g x}) ->
                                 (vl: vertex_set{subset_vertices vl (g.vertices)}) ->
                            
              Lemma(ensures (forall y. vertex_mem y (insert_to_vertex_set g x vl) ==> vertex_mem y vl \/ y = x))

val insert_to_vertex_set_nonEmpty_lemma : (#a:eqtype)->
                                          (#t:eqtype) ->
                                          (g:graph_state #a #t) ->
                                          (x: vertex_id{mem_graph_vertex g x}) ->
                                          (s: vertex_set{subset_vertices s (g.vertices)}) ->
                           Lemma (ensures nonEmpty_set (insert_to_vertex_set g x s))
                           

val insert_to_vertex_set_head_tail_mem_neg_lemma :(#a:eqtype)->
                                                  (#t:eqtype) ->
                                                  (g:graph_state #a #t) ->
                                                  (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r}) ->
                                                  (b: vertex_id{mem_graph_vertex g b})->
                        Lemma (requires (b <> get_head g r /\ ~(vertex_mem b (get_tail g r))))
                              (ensures (~(vertex_mem b r)))
                           

val insert_to_vertex_set_last_first_mem_neg_lemma :(#a:eqtype)->
                                                  (#t:eqtype) ->
                                                  (g:graph_state #a #t) ->
                                                  (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r}) ->
                                                  (b: vertex_id{mem_graph_vertex g b})->
                        Lemma (requires (b <> get_last_elem g r /\ ~(vertex_mem b (get_first g r))))
                              (ensures (~(vertex_mem b r)))
                              
val insert_to_vertex_set_head_tail_mem_lemma : (#a:eqtype)->
                                               (#t:eqtype) ->
                                               (g:graph_state #a #t) ->
                                               (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r}) ->
                                               (vl: vertex_set{subset_vertices vl (g.vertices)}) ->

           Lemma (ensures (((vertex_mem (get_head g r) vl) /\
                             (forall y. vertex_mem y (get_tail g r) ==> vertex_mem y vl)) ==> subset_vertices r vl))
           
val insert_to_vertex_set_last_first_mem_lemma :(#a:eqtype)->
                                               (#t:eqtype) ->
                                               (g:graph_state #a #t) ->
                                               (r: vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r}) ->
                                               (vl: vertex_set{subset_vertices vl (g.vertices)}) ->

           Lemma (ensures (((vertex_mem (get_last_elem g r) vl) /\
                             (forall y. vertex_mem y (get_first g r) ==> vertex_mem y vl)) ==> subset_vertices r vl))


val insert_to_vertex_set_reach_lemma : (#a:eqtype)->
                                       (#t:eqtype) ->
                                       (g:graph_state #a #t) ->
                                       (o: vertex_id{mem_graph_vertex g o}) ->
                                       (x: vertex_id{mem_graph_vertex g x /\ (exists (z1: reach g o x). reachfunc g o x z1)}) ->
                                       (vl: vertex_set{subset_vertices vl (g.vertices) /\
                                                         (forall x. vertex_mem x vl ==> 
                                                           (exists (z1: reach g o x). reachfunc g o x z1))}) ->

                                       Lemma
                                       (ensures (forall y. vertex_mem y (insert_to_vertex_set g x vl)
                                             ==> (exists (z1: reach g o y). reachfunc g o y z1)))
                                             
val insert_to_vertex_set_reach_lemma_root_set : (#a:eqtype)->
                                                (#t:eqtype) ->
                                                (g:graph_state #a #t) ->
                                                (o: vertex_id{mem_graph_vertex g o}) ->
                                                (x: vertex_id{mem_graph_vertex g x /\ 
                                                     (exists (z1: reach g o x). reachfunc g o x z1)})-> 
                                                (vl: vertex_set{subset_vertices vl (g.vertices)}) ->
                                                (root_set : vertex_set{subset_vertices root_set (g.vertices)  /\
                                                            vertex_mem o root_set /\
                                                            (forall x. vertex_mem x vl ==> (exists o (z1: reach g o x). 
                                                               vertex_mem o root_set /\ reachfunc g o x z1))})->
                                       Lemma
                                       (ensures (forall y. vertex_mem y (insert_to_vertex_set g x vl)
                                             ==> (exists o (z1: reach g o y). reachfunc g o y z1 /\ vertex_mem o root_set)))
                                             
val insert_to_vertex_set_mem_lemma :   (#a:eqtype)->
                                       (#t:eqtype) ->
                                       (g:graph_state #a #t) ->
                                       (x: vertex_id{mem_graph_vertex g x}) ->
                                       (vl: vertex_set{subset_vertices vl (g.vertices)}) ->

                                       Lemma
                                       (requires (~(vertex_mem x vl)))
                                       (ensures (vertex_mem x (insert_to_vertex_set g x vl)))

val insert_to_vertex_set_length_lemma :   (#a:eqtype)->
                                          (#t:eqtype) ->
                                          (g:graph_state #a #t) ->
                                          (x: vertex_id{mem_graph_vertex g x}) ->
                                          (vl: vertex_set{subset_vertices vl (g.vertices)}) ->

                                       Lemma
                                       (requires (~(vertex_mem x vl)))
                                       (ensures (cardinal1 (insert_to_vertex_set g x vl) > cardinal1 vl))
val insert_to_vertex_set_mem_negation_lemma : (#a:eqtype)->
                                              (#t:eqtype) ->
                                              (g:graph_state #a #t) ->
                                              (x: vertex_id{mem_graph_vertex g x}) ->
                                              (vl: vertex_set{subset_vertices vl (g.vertices)}) ->
                                              (s: vertex_set{subset_vertices vl (g.vertices)}) ->

                                       Lemma
                                       (requires ((forall y. vertex_mem y vl ==> ~(vertex_mem y s)) /\ ~(vertex_mem x s)))
                                       (ensures (forall y. vertex_mem y (insert_to_vertex_set g x vl) ==> ~(vertex_mem y s)))

(*Performs set union of l1 and l2 which are subset vertex sets of the vertex set of the graph g*)
val union_vertex_sets    : (#a:eqtype)->
                           (#t:eqtype) ->
                           (g:graph_state #a #t) ->
                           (l1: vertex_set{subset_vertices l1 (g.vertices)}) ->
                           (l2: vertex_set{subset_vertices l2 (g.vertices)}) ->
             
                           Tot(l: vertex_set{(forall x. vertex_mem x l <==> vertex_mem x l1 \/ vertex_mem x l2) /\ 
                                subset_vertices l (g.vertices)})

val union_vertex_sets1    :(l1: vertex_set) ->
                           (l2: vertex_set) ->
             
                           Tot(l: vertex_set{(forall x. vertex_mem x l <==> vertex_mem x l1 \/ vertex_mem x l2)})

val union_vertex_sets_subset_lemma : (#a:eqtype)->
                                     (#t:eqtype) ->
                                     (g:graph_state #a #t) ->
                                     (l1: vertex_set{subset_vertices l1 (g.vertices)}) ->
                                     (l2: vertex_set{subset_vertices l2 (g.vertices)}) ->
                              Lemma
                              (ensures (subset_vertices (union_vertex_sets1 l1 l2) (g.vertices)))
                              

val union_vertex_sets_reach_lemma1 :(#a:eqtype)->
                                    (#t:eqtype) ->
                                    (g:graph_state #a #t) ->
                                    (o: vertex_id{mem_graph_vertex g o}) ->
                                    (l1: vertex_set{subset_vertices l1 (g.vertices)}) ->
                                    (l2: vertex_set{subset_vertices l2 (g.vertices)}) ->

                                    Lemma
                                    (requires ((forall x. (vertex_mem x l1 \/ vertex_mem x l2
                                             ==> (exists (z1: reach g o x). reachfunc g o x z1)))))
                                    (ensures (forall x. (vertex_mem x (union_vertex_sets1 l1 l2)
                                             ==> (exists (z1: reach g o x). reachfunc g o x z1))))
                                             
val union_vertex_sets_mem_lemma1 :(#a:eqtype)->
                                  (#t:eqtype) ->
                                  (g:graph_state #a #t) ->
                                  (l1: vertex_set{subset_vertices l1 (g.vertices)}) ->
                                  (l2: vertex_set{subset_vertices l2 (g.vertices)}) ->
                                  (vl: vertex_set{subset_vertices vl (g.vertices)})->
                       Lemma
                       (requires (forall x. vertex_mem x vl ==> ~(vertex_mem x l1) /\ ~(vertex_mem x l2)))
                       (ensures (forall x. vertex_mem x vl ==> ~(vertex_mem x (union_vertex_sets1 l1 l2 ))))
val push_to_vertex_set  : (#a:eqtype)->
                          (#t:eqtype) ->
                          (g:graph_state #a #t) ->
                          (l1: vertex_set{subset_vertices l1 (g.vertices)}) ->
                          (l2: vertex_set{subset_vertices l2 (g.vertices) /\ (forall x. vertex_mem x l1 ==> ~(vertex_mem x l2))}) ->
             
                           Tot(l: vertex_set{(forall x. vertex_mem x l <==> vertex_mem x l1 \/ vertex_mem x l2) /\ 
                                subset_vertices l (g.vertices)})


val union_vertex_sets_reach_lemma : (#a:eqtype)->
                                    (#t:eqtype) ->
                                    (g:graph_state #a #t) ->
                                    (o: vertex_id{mem_graph_vertex g o}) ->
                                    (l1: vertex_set{subset_vertices l1 (g.vertices)}) ->
                                    (l2: vertex_set{subset_vertices l2 (g.vertices)}) ->

                                    Lemma
                                    (requires (forall x. (vertex_mem x l1 \/ vertex_mem x l2
                                             ==> (exists (z1: reach g o x). reachfunc g o x z1))))
                                    (ensures (forall x. (vertex_mem x (union_vertex_sets g l1 l2)
                                             ==> (exists (z1: reach g o x). reachfunc g o x z1))))
                                             
val union_vertex_sets_mem_lemma : (#a:eqtype)->
                                  (#t:eqtype) ->
                                  (g:graph_state #a #t) ->
                                  (l1: vertex_set{subset_vertices l1 (g.vertices)}) ->
                                  (l2: vertex_set{subset_vertices l2 (g.vertices)}) ->
                                  (vl: vertex_set{subset_vertices vl (g.vertices)})->
                       Lemma
                       (requires (forall x. vertex_mem x vl ==> ~(vertex_mem x l1) /\ ~(vertex_mem x l2)))
                       (ensures (forall x. vertex_mem x vl ==> ~(vertex_mem x (union_vertex_sets g l1 l2 ))))

val push_to_stack_graph : (#a:eqtype) ->
                          (#t:eqtype) ->
                          (g:graph_state #a #t) ->
                          (vl: vertex_set{subset_vertices vl g.vertices})->
                          (st:vertex_set {(subset_vertices st g.vertices) /\ 
                                        (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))}) ->
                          (x: Usize.t{~(Seq.mem x st) /\
                                     ~(Seq.mem x vl) /\ 
                                      (mem_graph_vertex g x)
                                    }) ->
                                
              Tot (st': vertex_set {(subset_vertices st' g.vertices) /\ 
                                    (Seq.mem x st') /\
                                    (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                    (forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
                                    (forall x. Seq.mem x st  ==> Seq.mem x st')})

val push_to_stack_graph1 : (vl: vertex_set) ->
                           (st:vertex_set { 
                                        (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                           (x: Usize.t{~(Seq.mem x st) /\
                                     ~(Seq.mem x vl)})->
                                     
                                
              Tot (st': vertex_set {(Seq.mem x st') /\
                                    (forall x. Seq.mem x st  ==> Seq.mem x st') /\
                                    (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                    (forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
                                    (Seq.length st > 0 ==> st' == snoc st x) /\
                                    (Seq.length st == 0 ==> st'== Seq.create 1 x)})
val push_to_stack_graph_lemma : (#a:eqtype) ->
                                (#t:eqtype) -> 
                                (g:graph_state #a #t) ->
                                (vl: vertex_set{subset_vertices vl g.vertices})->
                                (st:vertex_set {(subset_vertices st g.vertices) /\ 
                                        (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                                (x: Usize.t{~(Seq.mem x st) /\
                                     ~(Seq.mem x vl) /\ 
                                      (mem_graph_vertex g x) 
                                    })->
                     Lemma
                     (requires Seq.length st == 0)
                     (ensures push_to_stack_graph g vl st x == Seq.create 1 x)


val push_to_stack_graph_lemma1 : (#a:eqtype)->
                                 (#t:eqtype) ->
                                 (g:graph_state #a #t) ->
                                 (vl: vertex_set{subset_vertices vl g.vertices})->
                                 (st:vertex_set {(subset_vertices st g.vertices) /\ 
                                        (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                                 (x: Usize.t{~(Seq.mem x st) /\
                                     ~(Seq.mem x vl) /\ 
                                      (mem_graph_vertex g x)
                                    })->
                     Lemma
                     (requires Seq.length st > 0)
                     (ensures push_to_stack_graph g vl st x == snoc st x)

val successor_push_body :(#a:eqtype) ->
                         (#t:eqtype) ->
                         (g:graph_state #a #t) ->
                         (l: vertex_list{forall x. Seq.mem x l ==> Seq.mem x g.vertices}) ->
                         (vl: vertex_set{subset_vertices vl g.vertices})->
                         (st:vertex_set {(subset_vertices st g.vertices) /\
                                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                         (j:nat {j < Seq.length l})->
                 Tot (st':vertex_set {(subset_vertices st' g.vertices) /\
                                      (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                      (forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
                                      (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                      (~(Seq.mem (Seq.index l j) vl) /\ ~(Seq.mem (Seq.index l j) st) ==>
                                            st' == push_to_stack_graph g vl st (Seq.index l j)) /\
                                      ((Seq.mem (Seq.index l j) vl) \/ (Seq.mem (Seq.index l j) st) ==>
                                            st' == st)})

val successor_push_body1 :(l: vertex_list) ->
                          (vl: vertex_set)->
                          (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                        (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                          (j:nat {j < Seq.length l})->
               Tot (st':vertex_set {(forall x. Seq.mem x st ==> Seq.mem x st') /\
                                      (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                      (forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
                                      (~(Seq.mem (Seq.index l j) vl) /\ ~(Seq.mem (Seq.index l j) st) ==>
                                            st' == push_to_stack_graph1 vl st (Seq.index l j)) /\
                                      ((Seq.mem (Seq.index l j) vl) \/ (Seq.mem (Seq.index l j) st) ==>
                                            st' == st)})
                                            
val successor_push_itr  :  (#a:eqtype) ->
                           (#t:eqtype) ->
                           (g:graph_state #a #t) ->
                           (l: vertex_list{forall x. Seq.mem x l ==> Seq.mem x g.vertices})-> 
                           (vl: vertex_set{subset_vertices vl g.vertices})->
                           (st:vertex_set {(subset_vertices st g.vertices) /\
                                   (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                   (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                           (j:nat (*{j <= Seq.length l}*))->
                Tot (st':vertex_set{(subset_vertices st' g.vertices) /\
                                     (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                     (forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
                                     (forall x. Seq.mem x st ==> Seq.mem x st')})

val successor_push_itr1: (l: vertex_list) ->
                         (vl: vertex_set)->
                         (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                           (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                         (j:nat)->
                Tot (st':vertex_set{(forall x. Seq.mem x st ==> Seq.mem x st') /\
                                     (forall x. Seq.mem x vl ==> ~(Seq.mem x st')) /\
                                     (forall x. Seq.mem x st' ==> ~(Seq.mem x vl))})

val successor_push_itr_lemma :   (#a:eqtype) ->
                                 (#t:eqtype) ->
                                 (g:graph_state #a #t) ->
                                 (l: vertex_list{forall x. Seq.mem x l ==> Seq.mem x g.vertices}) ->
                                 (vl: vertex_set{subset_vertices vl g.vertices})->
                                 (st:vertex_set {(subset_vertices st g.vertices) /\
                                                 (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                 (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                                 (j:nat (*{j <= Seq.length l}*))->
                   Lemma 
                   (requires j < Seq.length l)
                   (ensures (successor_push_itr g l vl st j == 
                                      successor_push_itr g l vl (successor_push_body g l vl st j) (j + 1)))
                                      
val  successor_push_itr_lemma1 : (#a:eqtype)->
                                 (#t:eqtype) ->
                                 (g:graph_state #a #t)-> 
                                 (l: vertex_list{forall x. Seq.mem x l ==> Seq.mem x g.vertices})-> 
                                 (vl: vertex_set{subset_vertices vl g.vertices})->
                                 (st:vertex_set {(subset_vertices st g.vertices) /\
                                                 (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                 (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                                 (j:nat (*{j <= Seq.length l}*))->
                   Lemma 
                   (requires j >= Seq.length l)
                   (ensures (successor_push_itr g l vl st j == st))

val successor_push_itr1_lemma :(l: vertex_list) ->
                               (vl: vertex_set)->
                               (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                               (j:nat)->
                   Lemma 
                   (requires j < Seq.length l)
                   (ensures (successor_push_itr1 l vl st j == 
                                      successor_push_itr1 l vl (successor_push_body1 l vl st j) (j + 1)))


val successor_push_itr1_lemma1: (l: vertex_list) ->
                                (vl: vertex_set)->
                                (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                              (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                                (j:nat)->
                  Lemma 
                   (requires j == Seq.length l)
                   (ensures (successor_push_itr1 l vl st j == st)) 
                   
val push_to_stack_graph1_subset_lemma: (#a:eqtype)->
                                       (#t:eqtype)-> 
                                       (g:graph_state #a #t)-> 
                                       (vl: vertex_set)->
                                       (st:vertex_set { 
                                                       (forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                       (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                                       (x: Usize.t{~(Seq.mem x st) /\
                                                    ~(Seq.mem x vl)})->
                  Lemma
                   (requires (mem_graph_vertex g x) /\
                             (subset_vertices vl g.vertices) /\
                             (subset_vertices st g.vertices))
                   (ensures subset_vertices (push_to_stack_graph1 vl st x) g.vertices)


val successor_push_body1_subset_lemma : (#a:eqtype)->
                                        (#t:eqtype) ->
                                        (g:graph_state #a #t) ->
                                        (l: vertex_list) ->
                                        (vl: vertex_set)->
                                        (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                     (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                                        (j:nat{j < Seq.length l})->
                   Lemma
                   (requires (forall x. Seq.mem x l ==> Seq.mem x g.vertices) /\
                             (subset_vertices vl g.vertices) /\
                             (subset_vertices st g.vertices))
                   (ensures subset_vertices (successor_push_body1 l vl st j) g.vertices)

val successor_push_itr1_subset_lemma :   (#a:eqtype)->
                                         (#t:eqtype) ->
                                         (g:graph_state #a #t)-> 
                                         (l: vertex_list)-> 
                                         (vl: vertex_set)->
                                         (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                                         (j:nat)->
                   Lemma
                   (requires (forall x. Seq.mem x l ==> Seq.mem x g.vertices) /\
                             (subset_vertices vl g.vertices) /\
                             (subset_vertices st g.vertices))
                   (ensures subset_vertices (successor_push_itr1 l vl st j) g.vertices)

val successor_equals_if_graph_equals_lemma :  (#a:eqtype)->
                                              (#t:eqtype) ->
                                              (g:graph_state #a #t)->
                                              (g1:graph_state #a #t)->
                                              (i: vertex_id {mem_graph_vertex g i})->
                        Lemma
                         (requires g == g1)
                         (ensures (successors g i == successors g1 i))

val successor_push_itr1_reach_lemma : (#a:eqtype)->
                                      (#t:eqtype) ->
                                      (g:graph_state #a #t)-> 
                                      (l: vertex_list) ->
                                      (vl: vertex_set)->
                                      (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                      (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                                      (j:nat)->
                                      (root_set : vertex_set{subset_vertices root_set (g.vertices)})->
                   Lemma
                   (requires ((forall x. vertex_mem x st ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1)) /\
                             (forall y. vertex_mem y l ==>   (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1)) /\
                             (forall x. Seq.mem x l ==> Seq.mem x g.vertices)))
                   (ensures ((forall x. vertex_mem x (successor_push_itr1 l vl st j) ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1)))) 

val successor_push_itr1_absent_element_l_lemma : (l: vertex_list)-> 
                                                 (vl: vertex_set)->
                                                 (st:vertex_set{(forall x. Seq.mem x vl ==> ~(Seq.mem x st)) /\
                                                                (forall x. Seq.mem x st ==> ~(Seq.mem x vl))})->
                                  Lemma
                                  (ensures (forall x. Seq.mem x l /\ ~(Seq.mem x vl) ==> (Seq.mem x (successor_push_itr1 l vl st 0))))

(*Removes all vertices from l which are part of vl*)
val remove_all_instances_of_vertex_from_vertex_set :   (l: vertex_list) ->
                                                       (vl: vertex_set) ->
                                                        Tot (l':vertex_set
                                                              {(forall x. vertex_mem x l' ==> vertex_mem x l) /\
                                                              (forall x. mem x vl ==> ~(mem x l')) /\
                                                              (forall x. mem x l' ==> ~(mem x vl))}) 
                                                              

val remove_all_instances_of_vertex_from_vertex_set_mem :   (l: vertex_list) ->
                                                           (vl: vertex_set) ->
                                                       Lemma 
                                                       (ensures (forall x. vertex_mem x 
                                                                   (remove_all_instances_of_vertex_from_vertex_set l vl) ==>
                                                                     vertex_mem x l))


val remove_lemma_correctness :   (l:vertex_set) ->
                                 (vl:vertex_set) ->
                                 Lemma ((forall x. vertex_mem x vl ==> 
                                           ~(vertex_mem x (remove_all_instances_of_vertex_from_vertex_set l vl))))
                                 [SMTPat (remove_all_instances_of_vertex_from_vertex_set l vl)]
                                 

val remove_lemma_correctness1 :   (l:vertex_set) ->
                                  (vl:vertex_set) ->
                                   Lemma ((forall x. vertex_mem x (remove_all_instances_of_vertex_from_vertex_set l vl) ==> 
                                            ~(vertex_mem x vl)))

val remove_lemma_subset :   (#a:eqtype)->
                            (#t:eqtype)->
                            (g:graph_state #a #t)->
                            (l:vertex_list{forall x. Seq.mem x l ==> Seq.mem x (g.vertices)})->
                            (vl:vertex_set{subset_vertices vl (g.vertices)})->
                            
              Lemma 
              (ensures(is_vertex_set (remove_all_instances_of_vertex_from_vertex_set l vl) /\
                       subset_vertices (remove_all_instances_of_vertex_from_vertex_set l vl) (g.vertices)))

val remove_absent_element_lemma :   (#a:eqtype)->
                                    (#t:eqtype) ->
                                    (g:graph_state #a #t) ->
                                    (l:vertex_list{forall x. Seq.mem x l ==> Seq.mem x (g.vertices)})->
                                    (vl:vertex_set{subset_vertices vl (g.vertices)}) ->
                  
                                    Lemma ((forall x. vertex_mem x l /\ ~(vertex_mem x vl) ==> 
                                             vertex_mem x (remove_all_instances_of_vertex_from_vertex_set l vl)))
               
val remove_lemma_reach    : (#a:eqtype)->
                            (#t:eqtype) ->
                            (g:graph_state #a #t) ->
                            (x': vertex_id{mem_graph_vertex g x'}) ->
                            (l: vertex_list{(forall y. vertex_mem y l ==>
                                               (exists(p:(reach g x' y)).reachfunc g x' y p)) /\
                                             (forall x. Seq.mem x l ==> Seq.mem x g.vertices)}) ->
                            (vl:vertex_set) ->
        
                            Lemma (forall y. vertex_mem y (remove_all_instances_of_vertex_from_vertex_set l vl) ==>
                                        (exists(p:(reach g x' y)).reachfunc g x' y p))

val vertices_in_path_concat: (#a:eqtype)->
                             (#t:eqtype) ->
                             (g:graph_state #a #t) ->
                             (s:vertex_id{mem_graph_vertex g s}) ->
                             (b:vertex_id{mem_graph_vertex g b}) ->
                             (r_sb: reach g s b) ->
                             (r:vertex_set{subset_vertices r g.vertices /\ ~(is_emptySet r)})->
                                     
                         Lemma 
                         (requires(negation_nonEmpty_implies_empty r;forall c. vertex_mem c (vertices_in_path g s b r_sb) ==> c <> (get_head g r) /\ 
                                                    ~(vertex_mem c (get_tail g r)))) 
                         (ensures (forall c. vertex_mem c (vertices_in_path g s b r_sb) ==> ~(vertex_mem c r)))

val vertices_in_path_concat1: (#a:eqtype)->
                             (#t:eqtype) ->
                             (g:graph_state #a #t) ->
                             (s:vertex_id{mem_graph_vertex g s}) ->
                             (b:vertex_id{mem_graph_vertex g b}) ->
                             (r_sb: reach g s b) ->
                             (r:vertex_set{subset_vertices r g.vertices /\ ~(is_emptySet r)})->
                                     
                         Lemma 
                         (requires(negation_nonEmpty_implies_empty r;
                                   forall c. vertex_mem c (vertices_in_path g s b r_sb) ==> c <> (get_last_elem g r) /\ 
                                                    ~(vertex_mem c (get_first g r)))) 
                         (ensures (forall c. vertex_mem c (vertices_in_path g s b r_sb) ==> ~(vertex_mem c r)))
                         


val vertices_in_path_neg_lemma : (#a:eqtype)->
                                 (#t:eqtype) ->
                                 (g:graph_state #a #t) ->
                                 (s:vertex_id{mem_graph_vertex g s}) ->
                                 (b:vertex_id{mem_graph_vertex g b}) ->
                                 (r_sb: reach g s b) ->
                                 (vl:vertex_set{subset_vertices vl g.vertices})->
                                 (x: vertex_id{mem_graph_vertex g x})->
                                 Lemma 
                                 (requires (~(vertex_mem x (vertices_in_path g s b r_sb)) /\
                                             (vertex_mem s vl ==> vertex_mem x (vertices_in_path g s b r_sb))))
                                 (ensures (~(vertex_mem s vl)))
                                
let mem_of_seq_upto_index (v_id: Usize.t)
                          (vs: Seq.seq Usize.t)
                          (i:nat{i <= Seq.length vs})
                          
        : Tot (b:bool{(b = true ==> Seq.mem v_id (Seq.slice vs 0 i)) /\
                       (b == false ==> ~(Seq.mem v_id (Seq.slice vs 0 i)) /\
                       (b == false ==> (forall (j:nat). j < Seq.length (Seq.slice vs 0 i) ==> 
                                             Seq.index (Seq.slice vs 0 i) j <> v_id)))}) = 
let vs' = Seq.slice vs 0 i in
if Seq.mem v_id vs' then
 let _ = Seq.mem_index v_id vs' in
 true 
else 
 false  

let mem_of_seq (v_id: Usize.t)
               (vs: Seq.seq Usize.t)
        : Tot (b:bool{(b = true ==> Seq.mem v_id vs) /\
                       (b == false ==> ~(Seq.mem v_id vs) /\
                       (b == false ==> (forall (j:nat). j < Seq.length vs ==> Seq.index vs j <> v_id)))}) = 
if Seq.mem v_id vs then
 let _ = Seq.mem_index v_id vs in
 true 
else 
 false  

let mem_snoc (l:Seq.seq Usize.t)
             (vs: Seq.seq Usize.t)
             (i:nat{i < Seq.length l})
             (j:nat{j < Seq.length vs})

       : Lemma
         (requires (forall x. mem_of_seq_upto_index x l i ==> mem_of_seq_upto_index x vs j) /\
                    (mem_of_seq_upto_index (Seq.index l i) vs j))
         (ensures (forall x. mem_of_seq_upto_index x l (i + 1) ==> mem_of_seq_upto_index x vs j)) = 
 let _ = Seq.lemma_slice_snoc l 0 (i + 1) in ()



val is_vertex_set_slice : (#a:eqtype)->
                          (#t:eqtype) ->
                          (g:graph_state #a #t) ->
                          (v_id:vertex_id{mem_graph_vertex g v_id}) ->
                          (len: nat)->
                          (i:nat{i < len}) ->
                          (vs:Seq.seq vertex_id{(len == Seq.length vs) /\  
                                              (is_vertex_set (Seq.slice vs 0 i)) /\
                                             ~(mem_of_seq v_id (Seq.slice vs 0 i)) /\
                                              (subset_vertices (Seq.slice vs 0 i) (g.vertices)) /\
                                              (Seq.index (Seq.slice vs 0 (i + 1)) i == v_id) /\
                                              (mem_of_seq v_id (Seq.slice vs 0 (i + 1)))}) ->
                Lemma 
                (ensures (is_vertex_set (Seq.slice vs 0 (i + 1)) /\ (subset_vertices (Seq.slice vs 0 (i + 1)) (g.vertices))))

val is_vertex_set_slice1 :(v_id:vertex_id) ->
                          (len: nat)->
                          (i:nat{i < len}) ->
                          (vs:Seq.seq vertex_id{(len == Seq.length vs) /\  
                                              (is_vertex_set (Seq.slice vs 0 i)) /\
                                             ~(mem_of_seq_upto_index v_id vs i) /\
                                              (Seq.index (Seq.slice vs 0 (i + 1)) i == v_id) /\
                                              (mem_of_seq_upto_index v_id vs (i + 1))}) ->
                Lemma 
                (ensures (is_vertex_set (Seq.slice vs 0 (i + 1))))
                
(*val is_vertex_set_slice_sub : (len: nat) ->
                              (vs:Seq.seq vertex_id{(len == Seq.length vs) /\
                                                    (is_vertex_set vs)})->
                         
                Lemma 
                (ensures (forall j. 0 <= j /\ j <= len ==> (is_vertex_set (Seq.slice vs 0 j))))*)


/// val lemma_contains_empty (#a:Type) : Lemma (forall (x:a). ~ (contains Seq.empty x))


let empty_seq_mem_lemma (l1: Seq.seq UInt32.t{Seq.length l1 == 0})
                        (l2: Seq.seq UInt32.t{Seq.length l2 > 0})
               : Lemma (ensures (forall x. Seq.mem x l1 ==> Seq.mem x l2)) = 
let _ = assert (Seq.equal l1 Seq.empty) in
let _ = Seq.lemma_contains_empty #UInt32.t in
let _ = assert (forall (x:UInt32.t). ~(Seq.contains Seq.empty x)) in
()

/// (forall x. mem_of_seq_upto_index x (B.as_seq h l1) i ==> 
///                                    mem_of_seq_upto_index x (B.as_seq h l2) 
///                                    (UInt32.v (Seq.index (B.as_seq h index_buf) 0)
///
/// let _ = assert (mem_of_seq_upto_index x (B.as_seq h3 l2) 
///                                    (UInt32.v (Seq.index (B.as_seq h3 index_buf) 0))) in
///
/// (forall x. mem_of_seq_upto_index x (B.as_seq h3 l1) (UInt32.v i + 1) ==> 
///                                    mem_of_seq_upto_index x (B.as_seq h3 l2) 
///                                    (UInt32.v (Seq.index (B.as_seq h3 index_buf) 0))
///
///
/// 

let seq_union_lemma (l1: Seq.seq Usize.t)
                    (l2: Seq.seq Usize.t)
                    (i:nat{i < Seq.length l1})
                    (j:nat{j < Seq.length l2 /\ (Seq.length l1 < Seq.length l2 - j)})
                    (x:Usize.t{x == Seq.index l1 i})
           : Lemma
             (requires ((forall y. mem_of_seq_upto_index y l1 i ==> mem_of_seq_upto_index y l2 j) /\
                        mem_of_seq_upto_index x l2 j))
             (ensures ((forall y. mem_of_seq_upto_index y l1 (i + 1) ==> mem_of_seq_upto_index y l2 j))) = 
Seq.lemma_slice_snoc l1 0 (i + 1)

module DFS2

open FStar.Classical

open Spec.Graph3


type stack_vl_pair = vertex_set & vertex_set

#restart-solver 

let dfs_body (#a:eqtype)
              (#t:eqtype)
              (g:graph_state #a #t)
              (r : vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})
              (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                                (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                                (forall x. vertex_mem x r ==> ~(vertex_mem x vl))})
        : Tot (st_vl:stack_vl_pair{subset_vertices (fst st_vl) (g.vertices) /\
                                   subset_vertices (snd st_vl) (g.vertices) /\
                                   (forall x. vertex_mem x (snd st_vl) ==> ~(vertex_mem x (fst st_vl))) /\
                                   (forall x. vertex_mem x (fst st_vl) ==> ~(vertex_mem x (snd st_vl))) /\
                                   subset_vertices vl (snd st_vl) /\
                                   (forall x. Seq.mem x (get_first g r) ==> Seq.mem x (fst st_vl)) /\
                                   ~(Seq.mem (get_last_elem g r) (fst st_vl))}) = 
  let x = get_last_elem g r in
  
  let xs = get_first g r in
  let s = successors g x in  
  let vl' = insert_to_vertex_set g x vl in
  
 
  let _ = get_last_mem_lemma g r in

  let r' = successor_push_itr1 s vl' xs 0 in
  successor_push_itr1_subset_lemma g s vl' xs 0;
  
  let _ = insert_to_vertex_set_mem_negation_lemma g x vl xs in
  assert (subset_vertices r' (g.vertices));
  assert ((forall x. vertex_mem x vl' ==> ~(vertex_mem x r')) /\
         (forall x. vertex_mem x r' ==> ~(vertex_mem x vl')));
  assert (forall x. Seq.mem x (get_first g r) ==> Seq.mem x r');
  assert (~(Seq.mem (get_last_elem g r) r'));
  (r',vl')

let rec dfs (#a:eqtype)
            (#t:eqtype)
            (g:graph_state #a #t)
            (r : vertex_set{subset_vertices r (g.vertices)})
            (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                              (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                              (forall x. vertex_mem x r ==> ~(vertex_mem x vl))})
       : Tot (vl': vertex_set{subset_vertices vl' (g.vertices) /\ (subset_vertices vl vl') /\ (subset_vertices r vl')}) 
         (decreases %[cardinal1 (g.vertices) - cardinal1 vl;cardinal1 r]) = 
 if (is_emptySet r) then 
   vl
 else 
 (
  
  let r',vl' = dfs_body g r vl in
  let vl1 = dfs g r' vl'  in
  vl1
 )

let rec dfs_subset_prop  (#a:eqtype)
                         (#t:eqtype)
                         (g:graph_state #a #t)
                         (r : vertex_set{subset_vertices r (g.vertices)})
                         (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                                (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                                (forall x. vertex_mem x r ==> ~(vertex_mem x vl))})
                         
       : Lemma (ensures(subset_vertices r (dfs g r vl)))
          (decreases %[cardinal1 (g.vertices) - cardinal1 vl;cardinal1 r]) = 
if (is_emptySet r) then 
   ()
 else 
 (
  
  let r',vl' = dfs_body g r vl in
  let vl1 = dfs g r' vl'  in
  dfs_subset_prop g r' vl';
  ()
 )

let dfs_lemma (#a:eqtype)
              (#t:eqtype)
              (g:graph_state #a #t)
              (r : vertex_set{subset_vertices r (g.vertices)})
              (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                               (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                               (forall x. vertex_mem x r ==> ~(vertex_mem x vl))})
                         
       : Lemma
         (requires nonEmpty_set r)
         (ensures (dfs g r vl == dfs g (fst (dfs_body g r vl)) (snd (dfs_body g r vl)))) = ()


#restart-solver


#restart-solver 
let dfs_body_forward_lemma (#a:eqtype)
                           (#t:eqtype)
                           (g:graph_state #a #t)
                           (r : vertex_set{subset_vertices r (g.vertices) /\ nonEmpty_set r})
                           (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                                (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                                (forall x. vertex_mem x r ==> ~(vertex_mem x vl))})
                           (root_set : vertex_set{subset_vertices root_set (g.vertices)  /\  
                                         (forall x. vertex_mem x r ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\
                                                                         reachfunc g o x z1))/\ 
                                         (forall x. vertex_mem x vl ==> (exists o (z1: reach g o x). vertex_mem o root_set /\
                                                                         reachfunc g o x z1))})
              : Lemma
                (requires nonEmpty_set r)
                (ensures ((forall x. vertex_mem x (fst (dfs_body g r vl)) ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\
                                                                            reachfunc g o x z1))/\ 
                          (forall x. vertex_mem x (snd (dfs_body g r vl)) ==> (exists o (z1: reach g o x). vertex_mem o root_set /\
                                                                         reachfunc g o x z1)))) = 
  let x = get_last_elem g r in
  assert ((forall x. vertex_mem x r ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\
                                                                       reachfunc g o x z1)));
  assert (Seq.mem x r);
  assert (exists o (z1: reach g o x) . vertex_mem o root_set /\ reachfunc g o x z1);
                                                                            
  let xs = get_first g r in
  let s = successors g x in  
  let vl' = insert_to_vertex_set g x vl in
  
 
  let _ = get_last_mem_lemma g r in
  
  let r' = successor_push_itr1 s vl' xs 0 in
  successor_push_itr1_subset_lemma g s vl' xs 0;
  
  (*OUTPUT OF SUCCESSOR_PUSH IS EITHER IN XS OR IN a Subset of s *)
  let _ = insert_to_vertex_set_mem_negation_lemma g x vl xs in
  let _ = exists_elim 
          ((forall x. vertex_mem x r' ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\
                                                                         reachfunc g o x z1))/\ 
           (forall x. vertex_mem x vl' ==> (exists o (z1: reach g o x). vertex_mem o root_set /\
                                                                         reachfunc g o x z1)))
           ()
           (fun (o:vertex_id{mem_graph_vertex g o /\ ( exists (r1:reach g o x).reachfunc g o x r1) /\  vertex_mem o root_set}) -> 
              
              let _ = succ_reach_transitive_lemma1 g o x in
              assert (forall y. vertex_mem y s ==> (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1));
              assert (forall y. vertex_mem y xs ==> (exists o (z1: reach g o y) . vertex_mem o root_set /\ reachfunc g o y z1));
              assert (forall x. Seq.mem x s ==> Seq.mem x g.vertices);
              assert ((forall x. Seq.mem x vl' ==> ~(Seq.mem x xs)) /\
                     (forall x. Seq.mem x xs ==> ~(Seq.mem x vl)));
                     
              //let _ = remove_lemma_reach g o s vl' in
              successor_push_itr1_reach_lemma g s vl' xs 0 root_set;
              assert (forall x. vertex_mem x r' ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\
                                                                         reachfunc g o x z1));
              let _ = insert_to_vertex_set_reach_lemma_root_set g o x vl root_set in
              assert (forall x. vertex_mem x vl' ==> (exists o (z1: reach g o x). vertex_mem o root_set /\
                                                                         reachfunc g o x z1));
              ()) in 
   
  ()
  

let rec dfs_lemma_forward (#a:eqtype)
                           (#t:eqtype)
                           (g:graph_state #a #t)
                           (r : vertex_set{subset_vertices r (g.vertices)})
                           (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                                (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                                (forall x. vertex_mem x r ==> ~(vertex_mem x vl))})
                          
                           (root_set : vertex_set{subset_vertices root_set (g.vertices)  /\  
                                         (forall x. vertex_mem x r ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\
                                                                         reachfunc g o x z1))/\ 
                                         (forall x. vertex_mem x vl ==> (exists o (z1: reach g o x). vertex_mem o root_set /\
                                                                         reachfunc g o x z1))})
            
       : Lemma 
         (ensures(forall x. vertex_mem x (dfs g r vl) ==> (exists o (z1: reach g o x) . vertex_mem o root_set /\
                                                                         reachfunc g o x z1))) 
         (decreases %[cardinal1 (g.vertices) - cardinal1 vl;cardinal1 r]) = 
 if (is_emptySet r) then 
   ()
 else 
 (
    let r',vl' = dfs_body g r vl in
    let vl1 = dfs g r' vl'  in
    dfs_body_forward_lemma g r vl root_set;
    dfs_lemma_forward g r' vl' root_set
 )


#restart-solver

#push-options "--split_queries always"


#push-options "--z3rlimit 500"

let rec dfs5 (#a:eqtype)
             (#t:eqtype)
             (g:graph_state #a #t)
             (r : vertex_set{subset_vertices r (g.vertices)})
             (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                                (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                                (forall x. vertex_mem x r ==> ~(vertex_mem x vl))})
             

       : Tot (vl': vertex_set{subset_vertices vl' (g.vertices) /\ (subset_vertices vl vl') /\ (subset_vertices r vl')}) 

         (decreases %[cardinal1 (g.vertices) - cardinal1 vl;cardinal1 r]) = 
if (is_emptySet r) then vl
 
 else 
  let _ = negation_nonEmpty_implies_empty r in
  
  let x = get_last_elem g r in
  
  let xs = get_first g r in
  let s = successors g x in
  let vl' = insert_to_vertex_set g x vl in
  let _ = insert_to_vertex_set_length_lemma g x vl in
  let _ = insert_to_vertex_set_mem_lemma g x vl in
  
  let _ = get_last_mem_lemma g r in
  
  let s' = remove_all_instances_of_vertex_from_vertex_set s vl' in
  let _ = remove_lemma_subset g s vl' in
  
  
  let r' = union_vertex_sets g s' xs in
  
  let _ = insert_to_vertex_set_mem_negation_lemma g x vl xs in
  
  let _ = union_vertex_sets_mem_lemma g s' xs vl' in
  
  let vl1 = dfs5 g r' vl' in
  let _ = insert_to_vertex_set_last_first_mem_lemma g r vl1 in
  vl1


let rec dfs7 (#a:eqtype)
             (#t:eqtype)
             (g:graph_state #a #t)
             (r : vertex_set{subset_vertices r (g.vertices)})
             (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                                (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                                (forall x. vertex_mem x r ==> ~(vertex_mem x vl))})
             

       : Tot (vl': vertex_set{subset_vertices vl' (g.vertices) /\ (subset_vertices vl vl') /\ (subset_vertices r vl')}) 

         (decreases %[cardinal1 (g.vertices) - cardinal1 vl;cardinal1 r]) = 
if (is_emptySet r) then vl
 
 else 
  let _ = negation_nonEmpty_implies_empty r in
  
  let x = get_last_elem g r in
  
  let xs = get_first g r in
  let s = successors g x in
  let vl' = insert_to_vertex_set g x vl in
  let _ = insert_to_vertex_set_length_lemma g x vl in
  let _ = insert_to_vertex_set_mem_lemma g x vl in
  
  let _ = get_last_mem_lemma g r in
  
  let r' = successor_push_itr1 s vl' xs 0 in
  successor_push_itr1_subset_lemma g s vl' xs 0;
  
  let _ = insert_to_vertex_set_mem_negation_lemma g x vl xs in
  
  
  let vl1 = dfs7 g r' vl' in
  let _ = insert_to_vertex_set_last_first_mem_lemma g r vl1 in
  vl1

#restart-solver 

let rec dfs_equality_lemma (#a:eqtype)
                           (#t:eqtype)
                           (g:graph_state #a #t)
                           (r : vertex_set{subset_vertices r (g.vertices)})
                           (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                                (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                                (forall x. vertex_mem x r ==> ~(vertex_mem x vl))})
            : Lemma
              (ensures (dfs g r vl == dfs7 g r vl))
              (decreases %[cardinal1 (g.vertices) - cardinal1 vl;cardinal1 r]) = 
if (is_emptySet r) then ()
 
 else 
  let _ = negation_nonEmpty_implies_empty r in
  
  let x = get_last_elem g r in
  
  let xs = get_first g r in
  let s = successors g x in
  let vl' = insert_to_vertex_set g x vl in
  let _ = insert_to_vertex_set_length_lemma g x vl in
  let _ = insert_to_vertex_set_mem_lemma g x vl in
  
  let _ = get_last_mem_lemma g r in
  
  
  let r' = successor_push_itr1 s vl' xs 0 in
  successor_push_itr1_subset_lemma g s vl' xs 0;
  
 
  
  let _ = insert_to_vertex_set_mem_negation_lemma g x vl xs in
  
 
  let r_b, v_b = dfs_body g r vl in

  assert (r' == r_b);
  assert (vl' == v_b);
  
  let vl1 = dfs7 g r' vl' in
  let vl2 = dfs g r_b v_b in
  let _ = dfs_equality_lemma g r' vl' in
  let _ = insert_to_vertex_set_last_first_mem_lemma g r vl1 in
  assert (vl1 == vl2);
  ()




#restart-solver

#push-options "--z3rlimit 2000"


#restart-solver

let rec dfs5_lemma_backward (#m:eqtype) 
                            (#t:eqtype) 
                            (g:graph_state #m #t) 
                            (r : vertex_set{subset_vertices r (g.vertices)}) 
                            (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                                (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                                (forall x. vertex_mem x r ==> ~(vertex_mem x vl))}) 
                            (root_set : vertex_set{subset_vertices root_set (g.vertices)})

                  
        :Lemma
          (requires ((forall o x (z2: reach g o x). (reachfunc g o x z2) /\ vertex_mem o root_set ==> 
                          (vertex_mem x vl \/ (exists y (z3: reach g y x). reachfunc g y x z3 /\ vertex_mem y r))) /\
                     (forall c b (r_cb: reach g c b). (vertex_mem c vl /\ reachfunc g c b r_cb /\ ~(c = b)) ==>
                           (vertex_mem b vl \/ vertex_mem b r \/ (exists d. vertex_mem d r /\ 
                              vertex_mem d (vertices_in_path g c b r_cb))))))
          (ensures (forall o x (z2: reach g o x). (reachfunc g o x z2) /\ vertex_mem o root_set ==> vertex_mem x (dfs5 g r vl))) 
          (decreases %[cardinal1 (g.vertices) - cardinal1 vl;cardinal1 r]) = 
 if (is_emptySet r) then ()
 else 
  let _ = negation_nonEmpty_implies_empty r in
  let x = get_last_elem g r in
  let xs = get_first g r in
  let s = successors g x in
  assert (forall y. vertex_mem y s <==> mem_graph_edge g x y);
  let vl' = insert_to_vertex_set g x vl in
  let _ = insert_to_vertex_set_length_lemma g x vl in
  let _ = insert_to_vertex_set_mem_lemma g x vl in
  let _ = get_last_mem_lemma g r in
  let s' = remove_all_instances_of_vertex_from_vertex_set s vl' in
  let _ = remove_lemma_subset g s vl' in
  let r' = union_vertex_sets g s' xs in
  let _ = insert_to_vertex_set_mem_negation_lemma g x vl xs in
  let _ = union_vertex_sets_mem_lemma g s' xs vl' in
  let vl1 = dfs5 g r' vl' in
  let _ = insert_to_vertex_set_last_first_mem_lemma g r vl1 in
  let _ = insert_to_vertex_set_lemma g x vl in
  let _ = assert (forall k. vertex_mem k vl' ==> vertex_mem k vl \/ k = x) in

  (*k mem vl
    k to p is reachable
    k <> p
    p not mem vl'
    c mem xs
    c mem k---> p path
    -----------------------------------
    c mem r'*)
  let _ = assert (forall k p r_kp c. (vertex_mem k vl /\ reachfunc g k p r_kp /\ ~(k = p) /\ ~(vertex_mem p vl') /\ 
                              vertex_mem c xs /\ vertex_mem c (vertices_in_path g k p r_kp)) ==> vertex_mem c r' ) in

  (*k mem vl
    k to p is reachable
    k <> p
    p not mem vl
    p mem xs
    ----------------------------------
    p mem r'
  *)
  
  let _ = assert (forall k p r_kp. (vertex_mem k vl /\ reachfunc g k p r_kp /\ ~(k = p) /\ 
                              ~(vertex_mem p vl') /\ vertex_mem p xs) ==> vertex_mem p r' ) in 
  (*Removal of x does not break reachability to some b. This lemma is important because it bounds the length
                   of the path*) 

  (*x is top of the stack
   x to b is reachable through r_xb
   x <> b
   b not mem vl'
   b not mem xs
   all c in x to b path is not mem of xs
   -----------------------------------------
   prove - b mem r' or
           exists c in r' which is in the path from x to b
   That is b should be part of successors of x or there exists c which is part of successors of x and c is in path from x to b
   *)
  
  let path_induct_lemma (b:vertex_id{mem_graph_vertex g b}) 
                        (r_xb:reach g x b)
           : Lemma 
             (requires (reachfunc g x b r_xb /\ ~(x = b) /\ ~(vertex_mem b vl') /\ ~(vertex_mem b xs) /\ 
                             (forall c. vertex_mem c (vertices_in_path g x b r_xb) ==> ~(vertex_mem c xs))))
             (ensures (vertex_mem b r' \/ (exists c. vertex_mem c r' /\ vertex_mem c (vertices_in_path g x b r_xb)))) =
                    
   match r_xb with
                    | ReachTrans g x x1 b r_x1 ->  if ReachRefl? r_x1 then
                                                  (  assert (x == x1);
                                                     assert (mem_graph_vertex g x1);
                                                     assert (mem_graph_edge g x1 b);
                                                     assert (s == successors g x);
                                                     assert (forall y. vertex_mem y s <==> mem_graph_edge g x y);
                                                     let _ = assert (vertex_mem b (successors g x)) in
                                                     let _ = assert (~(vertex_mem b vl')) in
                                                     let _ = remove_absent_element_lemma g (successors g x) vl' in
                                                     let _ = assert (vertex_mem b s') in
                                                     let _ = assert (vertex_mem b r') in
                                                     ()
                                                  )
                                                  else
                                                     let _ = shortest_path_lemma g x b r_xb in
                                  
                                                      exists_elim (vertex_mem b r' \/  (exists c. vertex_mem c r' /\ 
                                                                    vertex_mem c (vertices_in_path  g x b r_xb)))
                                                      ()
                                  
                                                      (fun (rs: reach g x b{~(vertex_mem x (vertices_in_path g x b rs)) /\ 
                                                           subset_vertices_in_path g (vertices_in_path g x b rs) 
                                                                                     (vertices_in_path g x b r_xb)}) ->
                                                                
                                                            let _ = succ_reach_transitive_lemma3 g x b rs in 
         
                                                            exists_elim (vertex_mem b r' \/ 
                                                                   (exists c. vertex_mem c r' /\ 
                                                                       vertex_mem c (vertices_in_path g x b r_xb)))
                                                            
                                                            ()
                                                            
                                                            (fun (s: vertex_id{vertex_mem s (successors g x) /\ 
                                                                (exists  (r_sb: reach g s b).reachfunc g s b r_sb /\
                                                                subset_vertices_in_path g (vertices_in_path g s b r_sb) 
                                                                                          (vertices_in_path g x b rs) /\
                                                                (~(ReachRefl? r_sb) ==> vertex_mem s 
                                                                                 (vertices_in_path g x b rs)))}) ->
                                                            
                                                                 exists_elim (vertex_mem b r' \/ (exists c. vertex_mem c r' /\ 
                                                                              vertex_mem c (vertices_in_path g x b r_xb)))
                                                                 ()
                                                                (fun (r_sb: reach g s b{reachfunc g s b r_sb /\
                                                                       subset_vertices_in_path g (vertices_in_path g s b r_sb) 
                                                                                                 (vertices_in_path g x b rs) /\
                                                                        (~(ReachRefl? r_sb) ==> vertex_mem s 
                                                                                           (vertices_in_path g x b rs))}) ->
                                                      let _ = remove_absent_element_lemma g (successors g x) vl' in
                                
                                
                                                      let _ = insert_to_vertex_set_last_first_mem_neg_lemma g r b in
                                
                                                      (*notmem x (s---->b); all c. mem c xs ==> notmem c (s--->b)*)
                                 
                                                     let _ = vertices_in_path_concat g s b r_sb r in
                                 
                                                     ()))) in
                    
                    
(*path_induct_lemma completed here********************************************************************************************)                                                  

 let path_induct_lemma_mov b = move_requires (path_induct_lemma b) in 
 let _ = forall_intro_2 path_induct_lemma_mov in 
 (*Use of path_induct_lemma completed******************************************************************************************)
             
 (*Removal of x does not break reachability from vl, if the reachability is through x. Proving the existence of c
 which is in the path from k to b*)
 let visited_list_reachability_lemma k b r_kb 
          : Lemma 
            (requires ((vertex_mem k vl) /\ reachfunc g k b r_kb /\ ~(vertex_mem b vl') /\ ~(k = b) 
                      /\ ~(vertex_mem b r) /\ ~(vertex_mem b r') /\ vertex_mem x (vertices_in_path g k b r_kb)))
                                            
            (ensures (exists c. vertex_mem c r' /\ vertex_mem c (vertices_in_path g k b r_kb))) =
                              
                               let _ = reach_vertices_in_path_lemma g k b r_kb in (*b is reachable from all vertices in the path
                                                                                    from k to b. Hence b is also reachable
                                                                                   from x since x is in the path from k to b*)

                                (*The below witness creation makes the typechecking faster*)
                               
                               exists_elim (exists c. vertex_mem c r' /\ vertex_mem c (vertices_in_path g k b r_kb))
                               
                               ()
                               
                               (*Using the above fact from reach_vertices_in_path_lemma g k b r_kb lemma*)
                               (fun (r_xb: reach g x b{reachfunc g x b r_xb /\
                                   subset_vertices_in_path g (vertices_in_path g x b r_xb) 
                                                               (vertices_in_path g k b r_kb)}) ->
                          
                                   exists_elim (exists c. vertex_mem c r' /\ vertex_mem c (vertices_in_path g k b r_kb))
                                   
                                   ()

                                   (*From k....x--------->b path, x--------->b is taken out, x.....c------->b, c witness is created*)
                                   (fun (c: vertex_id{vertex_mem c r' /\ vertex_mem c (vertices_in_path g x b r_xb)}) ->
                                        let _ = assert (vertex_mem c (vertices_in_path g k b r_kb)) in
                              
                                        ())) in 
  (*visited_list_reachability_lemma k b completed here*************************************************************)
  let visited_list_reachability_lemma_mov k b = move_requires (visited_list_reachability_lemma k b) in
  let _ = forall_intro_3 visited_list_reachability_lemma_mov in

  (*Use of visited_list_reachability_lemma completed****************************************************************) 

  (*Using the above two lemmas, induction on path is made under control. Now with this context, we are proving that
                the removal of x will not break reachability by showing that r' will always contain some k through which b is
                reachable*)
  let reachability_thru_x_is_maintained_with_succ_x b r_xb 
        : Lemma 
          (requires ((reachfunc g x b r_xb) /\ ~(vertex_mem b vl') /\ ~(b = x) /\ 
                              (forall y. (vertex_mem y xs) ==> ~(exists r_yb. reachfunc g y b r_yb))))
                              
          (ensures (exists k r_kb. (vertex_mem k r') /\ reachfunc g k b r_kb)) =
          
              let _ = assert (forall y. (vertex_mem y xs) ==> ~(exists r_yb. reachfunc g y b r_yb) ) in   
              let _ = shortest_path_lemma g x b r_xb in (*Always a shortest path exists from x to b which does not 
                                                                     contain x as a member in the path x-------->b*)
              let _ = assert (exists (rs: reach g x b). ~(vertex_mem x (vertices_in_path g x b rs))) in
                                 
              exists_elim (exists k r_kb. (vertex_mem k r') /\ reachfunc g k b r_kb)
                                 
              ()
                                 
              (fun (rs: reach g x b{~(vertex_mem x (vertices_in_path g x b rs))}) ->
                              
                  let _ = succ_reach_transitive_lemma3 g x b rs in (*b is reachable through atleast one successor of x*)
                  let _ = assert (exists (s: vertex_id{vertex_mem s (successors g x)}). (exists  (r_sb: reach g s b).reachfunc g s b r_sb
                                                      /\ subset_vertices_in_path g (vertices_in_path g s b r_sb) 
                                                                                  (vertices_in_path g x b rs)
                                                      /\ (~(ReachRefl? r_sb) ==> vertex_mem s (vertices_in_path g x b rs))
                                                      /\ (ReachRefl? r_sb ==> (mem_graph_edge g x b)/\ rs == 
                                                         ReachTrans g x x b (ReachRefl g x))
                                                       )) in

   
                  exists_elim (exists k r_kb. (vertex_mem k r') /\ reachfunc g k b r_kb)
                     
                  ()

                  (*b is reachable through s, which is a successor of x*)
                  (fun (s: vertex_id{vertex_mem s (successors g x) /\ 
                                  (exists  (r_sb: reach g s b).reachfunc g s b r_sb /\
                                       subset_vertices_in_path g (vertices_in_path g s b r_sb) 
                                                                    (vertices_in_path g x b rs) /\
                                       (~(ReachRefl? r_sb) ==> vertex_mem s (vertices_in_path g x b rs)) /\
                                       (ReachRefl? r_sb ==> (mem_graph_edge g x b) /\ rs == 
                                                         ReachTrans g x x b (ReachRefl g x)))}) ->
                                                         
                                           let _ = assert (vertex_mem s (successors g x)) in
                                           
                                           exists_elim (exists k r_kb. (vertex_mem k r') /\ reachfunc g k b r_kb )
                         
                                           ()
                         
                                           (fun (r_sb: reach g s b{reachfunc g s b r_sb /\
                                                   subset_vertices_in_path g (vertices_in_path g s b r_sb) 
                                                                   (vertices_in_path g x b rs) /\
                                                   (~(ReachRefl? r_sb) ==> vertex_mem s (vertices_in_path g x b rs)) /\
                                                   (ReachRefl? r_sb ==> (mem_graph_edge g x b) /\ rs == 
                                                                    ReachTrans g x x b (ReachRefl g x))}) -> 

                                       (*Below two asserts are required for the proof**************************************)
                                                let _ = reflex_lemma1 g b in
                                                let _ = assert (reachfunc g b b (ReachRefl g b)) in 
                                                let _ = assert (vertex_mem b xs ==> 
                                                                   (exists y r_yb. (vertex_mem y xs) /\ reachfunc g y b r_yb)) in
                                                                   
                                                //let _ = insert_to_vertex_set_head_tail_lemma g r in
                                                let _ = insert_to_vertex_set_last_first_mem_neg_lemma g r b in
                                                let _ = assert (~(vertex_mem b r)) in
                                                let _ = assert (~(vertex_mem b vl)) in
                                                let _ = assert (vertex_mem s vl ==> 
                                                                    (exists c. vertex_mem c r /\ 
                                                                     vertex_mem c (vertices_in_path g s b r_sb))) in
                                                 
                                                 (*b is reachable from all vertices in the path s------->b*) 
                                                 let _ = reach_vertices_in_path_lemma g s b r_sb in 
                                                 
                                                 let _ = assert (forall c. vertex_mem c (vertices_in_path g s b r_sb) ==> 
                                                                      (exists r_cb. reachfunc g c b r_cb)) in
                                                 let _ = assert (forall y. (vertex_mem y xs) ==> 
                                                                    ~(exists r_yb. reachfunc g y b r_yb)) in
                                                 let _ = assert (forall y. (exists r_yb. reachfunc g y b r_yb) ==> 
                                                                    ~(vertex_mem y xs)) in
                                                 let _ = last_first_set_connect_lemma g r in                  
                                                 let _ = assert (forall c. vertex_mem c r /\ ~(vertex_mem c xs) ==> c = x) in
                                                 let _ = assert (forall c. (exists r_cb. vertex_mem c r /\ reachfunc g c b r_cb) ==> 
                                                                      c = x) in
                                                 let _ = assert (forall c r_cb. (vertex_mem c r /\ reachfunc g c b r_cb) ==> 
                                                                      c = x) in
                                                 let aux_2 c : 
                                                     Lemma (requires (vertex_mem c r /\ 
                                                                      vertex_mem c (vertices_in_path g s b r_sb))) 
                                                           (ensures (c = x)) =
                                                   let _ = assert (exists r_cb. reachfunc g c b r_cb) in
                                                   let _ = assert (exists r_cb. vertex_mem c r /\ 
                                                                       reachfunc g c b r_cb ==> c = x) in
                                     () in
                                
                                let _ = forall_intro (move_requires aux_2) in
                                let _ = assert (forall c. vertex_mem c r /\ vertex_mem c (vertices_in_path g s b r_sb) ==> c = x) in
                                let _ = assert (forall c. vertex_mem s vl /\ vertex_mem c r /\ 
                                                       vertex_mem c (vertices_in_path g s b r_sb) ==> c = x) in

                                let aux_3 (d:vertex_id)
                                     : Lemma 
                                       (requires vertex_mem s vl) 
                                        (ensures (vertex_mem x (vertices_in_path g s b r_sb))) =
                                  
                                       let _ = assert (exists c. vertex_mem c r /\ 
                                                         vertex_mem c (vertices_in_path g s b r_sb)) in
                                       
                                       exists_elim (vertex_mem x (vertices_in_path g s b r_sb))
                                       
                                       ()
                                  
                                       (fun (c: vertex_id{vertex_mem c r /\ vertex_mem c (vertices_in_path g s b r_sb)}) ->
                                    
                                       let _ = assert (c = x) in
                                       ()
                                  )
                                  in
                                  
                                  let _ = forall_intro (move_requires aux_3) in
                                  
                                             
                     (* Proof for ~(x = s):
                     Since x is in vl' and b is not in vl', hence x != b
                     Now, if x = s, then the path rs would be x->x->...->b, i.e. path length >= 2.
                     However, this would mean that x is on the path rs which is a contradiction.
                     Need to show as part of succ_reach_transitive_lemma3 that if input path length >= 2, then
                     the successor is part of the original path.*)

                  (*All vertices resulted from removing the vertices from (successors g x) which are present in vl' are
                    members of (successors g x)*)
                  
                  let _ = assert (~(vertex_mem s vl')) in
                  let _ = assert (vertex_mem s (successors g x)) in
                  
                  let _ = remove_absent_element_lemma g (successors g x) vl' in
                  
                  let _ = assert (vertex_mem s s') in (*Asserting that s will not be removed and it will be present in s'*)
                  
                  let _ = assert (vertex_mem s r') in (*Since s is present in s', it will be present in r'*)
                  
                  () (*Through s, b is still reachable from x. Hence s is that successor of x, which will not be removed
                       from (successors g x), since if it is present in vl, then that means x is present in a path from successors
                       to b and that is a contradiction since we induct on a shortest path where x is not present*)
                         )))  in  

  (*reachability_thru_x_is_maintained_with_succ_x completed********************************************************************************************************)
   let reachability_thru_x_is_maintained_with_succ_x_mov b = move_requires (reachability_thru_x_is_maintained_with_succ_x b) in
   let _ = forall_intro_2 reachability_thru_x_is_maintained_with_succ_x_mov in
       
  (*reachability_thru_x_is_maintained_with_succ_x usage completed**************************************************************************************************)
   
   (*All the above 3 lemmas deals with the breaking of reachability when x is removed from the stack. It asserts that when
     x is removed from stack, there exists some successor of x, which is added back to stack*)

   (*2 cases:  (1) All the vertices that are reachable from o through a vertex in stack other than x.
               (2) All the vertices that are reachable from o through x
    The reachability for case 1 vertices should happen through xs
    The reachability for case 2 vertices should happen throgh s'
    Since r' = union s' xs, both case 1 and case 2 are ensured.
    But this needs to be proved*)

   let _ = last_first_set_connect_lemma1 g r in
   
   
   (*let _ = assert (forall o x (z2: reach g o x). (reachfunc g o x z2) /\ vertex_mem o root_set ==> (vertex_mem x vl' \/ 
                            (exists y (z3: reach g y x). reachfunc g y x z3 /\ vertex_mem y r')))  in *)
   
   (*let _ = assert ((forall c b (r_cb: reach g c b). (vertex_mem c vl' /\ reachfunc g c b r_cb /\ ~(c = b)) ==>
                           (vertex_mem b vl' \/ vertex_mem b r' \/ (exists d. vertex_mem d r' /\ 
                              vertex_mem d (vertices_in_path g c b r_cb))))) in  *)
   
   
   let _ = dfs5_lemma_backward g r' vl' root_set in
   
   ()
   
   (******************************dfs4 backward reachability proof is completed********************************************)

let rec dfs7_lemma_backward (#m:eqtype) 
                            (#t:eqtype) 
                            (g:graph_state #m #t) 
                            (r : vertex_set{subset_vertices r (g.vertices)}) 
                            (vl: vertex_set{subset_vertices vl (g.vertices) /\ 
                                (forall x. vertex_mem x vl ==> ~(vertex_mem x r)) /\
                                (forall x. vertex_mem x r ==> ~(vertex_mem x vl))}) 
                            (root_set : vertex_set{subset_vertices root_set (g.vertices)})

                  
        :Lemma
          (requires ((forall o x (z2: reach g o x). (reachfunc g o x z2) /\ vertex_mem o root_set ==> 
                          (vertex_mem x vl \/ (exists y (z3: reach g y x). reachfunc g y x z3 /\ vertex_mem y r))) /\
                     (forall c b (r_cb: reach g c b). (vertex_mem c vl /\ reachfunc g c b r_cb /\ ~(c = b)) ==>
                           (vertex_mem b vl \/ vertex_mem b r \/ (exists d. vertex_mem d r /\ 
                              vertex_mem d (vertices_in_path g c b r_cb))))))
          (ensures (forall o x (z2: reach g o x). (reachfunc g o x z2) /\ vertex_mem o root_set ==> vertex_mem x (dfs7 g r vl))) 
          (decreases %[cardinal1 (g.vertices) - cardinal1 vl;cardinal1 r]) = 
 if (is_emptySet r) then ()
 else 
  let _ = negation_nonEmpty_implies_empty r in
  let x = get_last_elem g r in
  let xs = get_first g r in
  let s = successors g x in
  assert (forall y. vertex_mem y s <==> mem_graph_edge g x y);
  let vl' = insert_to_vertex_set g x vl in
  let _ = insert_to_vertex_set_length_lemma g x vl in
  let _ = insert_to_vertex_set_mem_lemma g x vl in
  let _ = get_last_mem_lemma g r in
  
  let r' = successor_push_itr1 s vl' xs 0 in
  successor_push_itr1_subset_lemma g s vl' xs 0;
  
  let _ = insert_to_vertex_set_mem_negation_lemma g x vl xs in
  
  let vl1 = dfs7 g r' vl' in
  let _ = insert_to_vertex_set_last_first_mem_lemma g r vl1 in
  let _ = insert_to_vertex_set_lemma g x vl in
  let _ = assert (forall k. vertex_mem k vl' ==> vertex_mem k vl \/ k = x) in
  (*k mem vl
    k to p is reachable
    k <> p
    p not mem vl'
    c mem xs
    c mem k---> p path
    -----------------------------------
    c mem r'*)
  let _ = assert (forall k p r_kp c. (vertex_mem k vl /\ reachfunc g k p r_kp /\ ~(k = p) /\ ~(vertex_mem p vl') /\ 
                              vertex_mem c xs /\ vertex_mem c (vertices_in_path g k p r_kp)) ==> vertex_mem c r' ) in

  (*k mem vl
    k to p is reachable
    k <> p
    p not mem vl
    p mem xs
    ----------------------------------
    p mem r'
  *)
  
  let _ = assert (forall k p r_kp. (vertex_mem k vl /\ reachfunc g k p r_kp /\ ~(k = p) /\ 
                              ~(vertex_mem p vl') /\ vertex_mem p xs) ==> vertex_mem p r' ) in 
  (*Removal of x does not break reachability to some b. This lemma is important because it bounds the length
                   of the path*) 

  (*x is top of the stack
   x to b is reachable through r_xb
   x <> b
   b not mem vl'
   b not mem xs
   all c in x to b path is not mem of xs
   -----------------------------------------
   prove - b mem r' or
           exists c in r' which is in the path from x to b
   That is b should be part of successors of x or there exists c which is part of successors of x and c is in path from x to b
   *)
    let path_induct_lemma (b:vertex_id{mem_graph_vertex g b}) 
                        (r_xb:reach g x b)
           : Lemma 
             (requires (reachfunc g x b r_xb /\ ~(x = b) /\ ~(vertex_mem b vl') /\ ~(vertex_mem b xs) /\ 
                             (forall c. vertex_mem c (vertices_in_path g x b r_xb) ==> ~(vertex_mem c xs))))
             (ensures (vertex_mem b r' \/ (exists c. vertex_mem c r' /\ vertex_mem c (vertices_in_path g x b r_xb)))) =
                    
   match r_xb with
                    | ReachTrans g x x1 b r_x1 ->  if ReachRefl? r_x1 then
                                                  (  assert (x == x1);
                                                     assert (mem_graph_vertex g x1);
                                                     assert (mem_graph_edge g x1 b);
                                                     assert (s == successors g x);
                                                     assert (forall y. vertex_mem y s <==> mem_graph_edge g x y);
                                                     let _ = assert (vertex_mem b (successors g x)) in
                                                     let _ = assert (~(vertex_mem b vl')) in
                                                     successor_push_itr1_absent_element_l_lemma s vl' xs;
                                                     //let _ = remove_absent_element_lemma g (successors g x) vl' in
                                                    // let _ = assert (vertex_mem b s') in
                                                     let _ = assert (vertex_mem b r') in
                                                     ()
                                                  )
                                                  else
                                                  (
                                                     let _ = shortest_path_lemma g x b r_xb in
                                  
                                                      exists_elim (vertex_mem b r' \/  (exists c. vertex_mem c r' /\ 
                                                                    vertex_mem c (vertices_in_path  g x b r_xb)))
                                                      ()
                                  
                                                      (fun (rs: reach g x b{~(vertex_mem x (vertices_in_path g x b rs)) /\ 
                                                           subset_vertices_in_path g (vertices_in_path g x b rs) 
                                                                                     (vertices_in_path g x b r_xb)}) ->
                                                                
                                                            let _ = succ_reach_transitive_lemma3 g x b rs in 
         
                                                            exists_elim (vertex_mem b r' \/ 
                                                                   (exists c. vertex_mem c r' /\ 
                                                                       vertex_mem c (vertices_in_path g x b r_xb)))
                                                            
                                                            ()
                                                            
                                                            (fun (s: vertex_id{vertex_mem s (successors g x) /\ 
                                                                (exists  (r_sb: reach g s b).reachfunc g s b r_sb /\
                                                                subset_vertices_in_path g (vertices_in_path g s b r_sb) 
                                                                                          (vertices_in_path g x b rs) /\
                                                                (~(ReachRefl? r_sb) ==> vertex_mem s 
                                                                                 (vertices_in_path g x b rs)))}) ->
                                                            
                                                                 exists_elim (vertex_mem b r' \/ (exists c. vertex_mem c r' /\ 
                                                                              vertex_mem c (vertices_in_path g x b r_xb)))
                                                                 ()
                                                                (fun (r_sb: reach g s b{reachfunc g s b r_sb /\
                                                                       subset_vertices_in_path g (vertices_in_path g s b r_sb) 
                                                                                                 (vertices_in_path g x b rs) /\
                                                                        (~(ReachRefl? r_sb) ==> vertex_mem s 
                                                                                           (vertices_in_path g x b rs))}) ->
                                                                           //let _ = remove_absent_element_lemma g (successors g x) vl' in
                                                                           successor_push_itr1_absent_element_l_lemma (successors g x) vl' xs;
                                
                                
                                                                           let _ = insert_to_vertex_set_last_first_mem_neg_lemma g r b in
                                
                                                                            (*notmem x (s---->b); all c. mem c xs ==> notmem c (s--->b)*)
                                 
                                                                           let _ = vertices_in_path_concat g s b r_sb r in
                                 
                                                                           ()))) ) in
                                                 
(*path_induct_lemma completed here********************************************************************************************) 
 
  let path_induct_lemma_mov b = move_requires (path_induct_lemma b) in 
  let _ = forall_intro_2 path_induct_lemma_mov in 
  (*Use of path_induct_lemma completed******************************************************************************************)

   (*Removal of x does not break reachability from vl, if the reachability is through x. Proving the existence of c
 which is in the path from k to b*)
 (*mem k vl
  k --> b
  not (mem b vl')
  k <> b
  not (mem b r)
  not (mem b r')
  mem x (k --> b)
  ---------------------------------------------
  exists c. mem c r' and 
            mem c (k--> b)
            
  *)


 let visited_list_reachability_lemma k b r_kb 
          : Lemma 
            (requires ((vertex_mem k vl) /\ reachfunc g k b r_kb /\ ~(vertex_mem b vl') /\ ~(k = b) 
                      /\ ~(vertex_mem b r) /\ ~(vertex_mem b r') /\ vertex_mem x (vertices_in_path g k b r_kb)))
                                            
            (ensures (exists c. vertex_mem c r' /\ vertex_mem c (vertices_in_path g k b r_kb))) =
                              
                               let _ = reach_vertices_in_path_lemma g k b r_kb in (*b is reachable from all vertices in the path
                                                                                    from k to b. Hence b is also reachable
                                                                                   from x since x is in the path from k to b*)

                                (*The below witness creation makes the typechecking faster*)
                               
                               exists_elim (exists c. vertex_mem c r' /\ vertex_mem c (vertices_in_path g k b r_kb))
                               
                               ()
                               
                               (*Using the above fact from reach_vertices_in_path_lemma g k b r_kb lemma*)
                               (fun (r_xb: reach g x b{reachfunc g x b r_xb /\
                                   subset_vertices_in_path g (vertices_in_path g x b r_xb) 
                                                               (vertices_in_path g k b r_kb)}) ->
                          
                                   exists_elim (exists c. vertex_mem c r' /\ vertex_mem c (vertices_in_path g k b r_kb))
                                   
                                   ()

                                   (*From k....x--------->b path, x--------->b is taken out, x.....c------->b, c witness is created*)
                                   (fun (c: vertex_id{vertex_mem c r' /\ vertex_mem c (vertices_in_path g x b r_xb)}) ->
                                        let _ = assert (vertex_mem c (vertices_in_path g k b r_kb)) in
                              
                                        ())) in 
  (*visited_list_reachability_lemma k b completed here*************************************************************)
  let visited_list_reachability_lemma_mov k b = move_requires (visited_list_reachability_lemma k b) in
  let _ = forall_intro_3 visited_list_reachability_lemma_mov in

  (*Use of visited_list_reachability_lemma completed****************************************************************) 
  (*Using the above two lemmas, induction on path is made under control. Now with this context, we are proving that
                the removal of x will not break reachability by showing that r' will always contain some k through which b is
                reachable*)

  (*x --> b
   not (mem b vl')
   b <> x
   forall y. mem y xs ==> not (y -> b)
   ----------------------------------------------------------
   exists k. mem k r' and
             k --> b
             *)
             
  let reachability_thru_x_is_maintained_with_succ_x b r_xb 
        : Lemma 
          (requires ((reachfunc g x b r_xb) /\ ~(vertex_mem b vl') /\ ~(b = x) /\ 
                              (forall y. (vertex_mem y xs) ==> ~(exists r_yb. reachfunc g y b r_yb))))
                              
          (ensures (exists k r_kb. (vertex_mem k r') /\ reachfunc g k b r_kb)) =
          
              let _ = assert (forall y. (vertex_mem y xs) ==> ~(exists r_yb. reachfunc g y b r_yb) ) in   
              let _ = shortest_path_lemma g x b r_xb in (*Always a shortest path exists from x to b which does not 
                                                                     contain x as a member in the path x-------->b*)
              let _ = assert (exists (rs: reach g x b). ~(vertex_mem x (vertices_in_path g x b rs))) in
                                 
              exists_elim (exists k r_kb. (vertex_mem k r') /\ reachfunc g k b r_kb)
                                 
              ()
                                 
              (fun (rs: reach g x b{~(vertex_mem x (vertices_in_path g x b rs))}) ->
                              
                  let _ = succ_reach_transitive_lemma3 g x b rs in (*b is reachable through atleast one successor of x*)
                  let _ = assert (exists (s: vertex_id{vertex_mem s (successors g x)}). (exists  (r_sb: reach g s b).reachfunc g s b r_sb
                                                      /\ subset_vertices_in_path g (vertices_in_path g s b r_sb) 
                                                                                  (vertices_in_path g x b rs)
                                                      /\ (~(ReachRefl? r_sb) ==> vertex_mem s (vertices_in_path g x b rs))
                                                      /\ (ReachRefl? r_sb ==> (mem_graph_edge g x b)/\ rs == 
                                                         ReachTrans g x x b (ReachRefl g x))
                                                       )) in

   
                  exists_elim (exists k r_kb. (vertex_mem k r') /\ reachfunc g k b r_kb)
                     
                  ()

                  (*b is reachable through s, which is a successor of x*)
                  (fun (s: vertex_id{vertex_mem s (successors g x) /\ 
                                  (exists  (r_sb: reach g s b).reachfunc g s b r_sb /\
                                       subset_vertices_in_path g (vertices_in_path g s b r_sb) 
                                                                    (vertices_in_path g x b rs) /\
                                       (~(ReachRefl? r_sb) ==> vertex_mem s (vertices_in_path g x b rs)) /\
                                       (ReachRefl? r_sb ==> (mem_graph_edge g x b) /\ rs == 
                                                         ReachTrans g x x b (ReachRefl g x)))}) ->
                                                         
                                           let _ = assert (vertex_mem s (successors g x)) in
                                           
                                           exists_elim (exists k r_kb. (vertex_mem k r') /\ reachfunc g k b r_kb )
                         
                                           ()
                         
                                           (fun (r_sb: reach g s b{reachfunc g s b r_sb /\
                                                   subset_vertices_in_path g (vertices_in_path g s b r_sb) 
                                                                   (vertices_in_path g x b rs) /\
                                                   (~(ReachRefl? r_sb) ==> vertex_mem s (vertices_in_path g x b rs)) /\
                                                   (ReachRefl? r_sb ==> (mem_graph_edge g x b) /\ rs == 
                                                                    ReachTrans g x x b (ReachRefl g x))}) -> 

                                       (*Below two asserts are required for the proof**************************************)
                                                let _ = reflex_lemma1 g b in
                                                let _ = assert (reachfunc g b b (ReachRefl g b)) in 
                                                let _ = assert (vertex_mem b xs ==> 
                                                                   (exists y r_yb. (vertex_mem y xs) /\ reachfunc g y b r_yb)) in
                                                                   
                                                //let _ = insert_to_vertex_set_head_tail_lemma g r in
                                                let _ = insert_to_vertex_set_last_first_mem_neg_lemma g r b in
                                                let _ = assert (~(vertex_mem b r)) in
                                                let _ = assert (~(vertex_mem b vl)) in
                                                let _ = assert (vertex_mem s vl ==> 
                                                                    (exists c. vertex_mem c r /\ 
                                                                     vertex_mem c (vertices_in_path g s b r_sb))) in
                                                 
                                                 (*b is reachable from all vertices in the path s------->b*) 
                                                 let _ = reach_vertices_in_path_lemma g s b r_sb in 
                                                 
                                                 let _ = assert (forall c. vertex_mem c (vertices_in_path g s b r_sb) ==> 
                                                                      (exists r_cb. reachfunc g c b r_cb)) in
                                                 let _ = assert (forall y. (vertex_mem y xs) ==> 
                                                                    ~(exists r_yb. reachfunc g y b r_yb)) in
                                                 let _ = assert (forall y. (exists r_yb. reachfunc g y b r_yb) ==> 
                                                                    ~(vertex_mem y xs)) in
                                                 let _ = last_first_set_connect_lemma g r in                  
                                                 let _ = assert (forall c. vertex_mem c r /\ ~(vertex_mem c xs) ==> c = x) in
                                                 let _ = assert (forall c. (exists r_cb. vertex_mem c r /\ reachfunc g c b r_cb) ==> 
                                                                      c = x) in
                                                 let _ = assert (forall c r_cb. (vertex_mem c r /\ reachfunc g c b r_cb) ==> 
                                                                      c = x) in
                                                 let aux_2 c : 
                                                     Lemma (requires (vertex_mem c r /\ 
                                                                      vertex_mem c (vertices_in_path g s b r_sb))) 
                                                           (ensures (c = x)) =
                                                   let _ = assert (exists r_cb. reachfunc g c b r_cb) in
                                                   let _ = assert (exists r_cb. vertex_mem c r /\ 
                                                                       reachfunc g c b r_cb ==> c = x) in
                                     () in
                                
                                let _ = forall_intro (move_requires aux_2) in
                                let _ = assert (forall c. vertex_mem c r /\ vertex_mem c (vertices_in_path g s b r_sb) ==> c = x) in
                                let _ = assert (forall c. vertex_mem s vl /\ vertex_mem c r /\ 
                                                       vertex_mem c (vertices_in_path g s b r_sb) ==> c = x) in

                                let aux_3 (d:vertex_id)
                                     : Lemma 
                                       (requires vertex_mem s vl) 
                                        (ensures (vertex_mem x (vertices_in_path g s b r_sb))) =
                                  
                                       let _ = assert (exists c. vertex_mem c r /\ 
                                                         vertex_mem c (vertices_in_path g s b r_sb)) in
                                       
                                       exists_elim (vertex_mem x (vertices_in_path g s b r_sb))
                                       
                                       ()
                                  
                                       (fun (c: vertex_id{vertex_mem c r /\ vertex_mem c (vertices_in_path g s b r_sb)}) ->
                                    
                                       let _ = assert (c = x) in
                                       ()
                                  )
                                  in
                                  
                                  let _ = forall_intro (move_requires aux_3) in
                                  
                                             
                     (* Proof for ~(x = s):
                     Since x is in vl' and b is not in vl', hence x != b
                     Now, if x = s, then the path rs would be x->x->...->b, i.e. path length >= 2.
                     However, this would mean that x is on the path rs which is a contradiction.
                     Need to show as part of succ_reach_transitive_lemma3 that if input path length >= 2, then
                     the successor is part of the original path.*)

                  (*All vertices resulted from removing the vertices from (successors g x) which are present in vl' are
                    members of (successors g x)*)
                  
                  (*let _ = assert (~(vertex_mem s vl')) in
                  let _ = assert (vertex_mem s (successors g x)) in*)
                  
                  //let _ = remove_absent_element_lemma g (successors g x) vl' in
                  successor_push_itr1_absent_element_l_lemma (successors g x) vl' xs;
                  
                  //let _ = assert (vertex_mem s s') in (*Asserting that s will not be removed and it will be present in s'*)
                  
                  let _ = assert (vertex_mem s r') in (*Since s is present in s', it will be present in r'*)
                  
                  ()(*Through s, b is still reachable from x. Hence s is that successor of x, which will not be removed
                       from (successors g x), since if it is present in vl, then that means x is present in a path from successors
                       to b and that is a contradiction since we induct on a shortest path where x is not present*)
                         )))  in  

  (*reachability_thru_x_is_maintained_with_succ_x completed********************************************************************************************************)
  let reachability_thru_x_is_maintained_with_succ_x_mov b = move_requires (reachability_thru_x_is_maintained_with_succ_x b) in
  let _ = forall_intro_2 reachability_thru_x_is_maintained_with_succ_x_mov in
       
  (*reachability_thru_x_is_maintained_with_succ_x usage completed**************************************************************************************************)
   
   (*All the above 3 lemmas deals with the breaking of reachability when x is removed from the stack. It asserts that when
     x is removed from stack, there exists some successor of x, which is added back to stack*)

   (*2 cases:  (1) All the vertices that are reachable from o through a vertex in stack other than x.
               (2) All the vertices that are reachable from o through x
    The reachability for case 1 vertices should happen through xs
    The reachability for case 2 vertices should happen throgh s'
    Since r' = union s' xs, both case 1 and case 2 are ensured.
    But this needs to be proved*)

   let _ = last_first_set_connect_lemma1 g r in
   
   
   (*let _ = assert (forall o x (z2: reach g o x). (reachfunc g o x z2) /\ vertex_mem o root_set ==> (vertex_mem x vl' \/ 
                            (exists y (z3: reach g y x). reachfunc g y x z3 /\ vertex_mem y r')))  in *)
   
   (*let _ = assert ((forall c b (r_cb: reach g c b). (vertex_mem c vl' /\ reachfunc g c b r_cb /\ ~(c = b)) ==>
                           (vertex_mem b vl' \/ vertex_mem b r' \/ (exists d. vertex_mem d r' /\ 
                              vertex_mem d (vertices_in_path g c b r_cb))))) in  *)
   let _ = dfs7_lemma_backward g r' vl' root_set in
   
   ()
 
   
   (******************************dfs4 backward reachability proof is completed********************************************)

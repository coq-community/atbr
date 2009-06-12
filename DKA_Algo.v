(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: DKA_Algo.v 875 2009-06-09 11:53:22Z braibant $ i*)

Require Import Common.
Require Import Classes.
Require Import SemiLattice.
Require Import SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.
Require Import BoolAlg.

Require        Force.
Require Export Utils_WF.

Require Export DKA_Sets.

Require Import Recdef.

Set Implicit Arguments.
Unset Printing Implicit Defensive.



Notation MX := (@X (@mx_Graph bool_Graph)).


Section Protect.

Existing Instance bool_Graph. 
Existing Instance bool_SemiLattice_Ops. 
Existing Instance bool_Monoid_Ops.


(* automates matriciels non déterministes à epsilon-transitions, 
   encodés par des matrices booléenes *)
Record bAut := {
  b_size:      state; 
  b_J:         MX(b_size,tt)(b_size,tt);
  b_M:         label -> MX(b_size,tt)(b_size,tt);
  b_U:         MX(1%nat,tt)(b_size,tt);
  b_V:         MX(b_size,tt)(1%nat,tt);
  b_max_label: label
}.

(* automates non déterministes, sans epsilon-transitions *)
Record NFA := {
  N_size:      state; 
  N_delta:     state -> label -> stateset;
  N_initiaux:  stateset;
  N_finaux:    stateset;
  N_max_label: label
}.

(* prédicat de bonne formation des automates non déterministe, 
   nécessaire pour énoncer la terminaison de l'algorithme de determinisation 
   on doit supposer que la fonction de transition est bien fichue, même en 
   dehors de ses bornes, pour pouvoir prouver la terminaison de la 
   déterminisation, sans sig types
 *)

Definition NFA_wf A :=
  let n := N_size A in
       below (N_initiaux A) n
    /\ below (N_finaux A)   n
    /\ (forall i b, (* i < n -> *) b < (N_max_label A) -> below (N_delta A i b) n)
    .


(* automates déterministes *)
Record DFA := {
  D_size:      state;
  D_delta:     state -> label -> state;
  D_initial:   state;
  D_finaux:    stateset;
  D_max_label: label
}.
 

 
                        (**************************)
                        (* Construction (Thomson) *)
                        (**************************)


(* il faut peute etre inserer des mx_force autour des produits, 
   et utiliser mx_bool_dot *)

Definition bPlus (A B: bAut) : bAut := @Build_bAut (b_size A + b_size B)
  (makeMat_blocks (b_J A) 0 0 (b_J B))
  (fun i =>  makeMat_blocks (b_M A i) 0 0 (b_M B i))
  (makeMat_blocks (b_U A) (b_U B) 0 0)
  (makeMat_blocks (b_V A) 0 (b_V B) 0)
  (Max.max (b_max_label A) (b_max_label B)).

Definition bDot (A B: bAut) : bAut := @Build_bAut (b_size A + b_size B)
  (makeMat_blocks (b_J A) (b_V A * b_U B) 0 (b_J B))
  (fun i =>  makeMat_blocks (b_M A i) 0 0 (b_M B i))
  (makeMat_blocks (b_U A) 0 0 0)
  (makeMat_blocks 0 0 (b_V B) 0)
  (Max.max (b_max_label A) (b_max_label B)).

Definition bpStar(A : bAut) : bAut := @Build_bAut (b_size A)
  (b_J A + b_V A * b_U A)
  (b_M A)
  (b_U A) 
  (b_V A)
  (b_max_label A).
 
Definition bVar (a : nat): bAut := @Build_bAut 2
  0
  (fun i => makeMat_blocks (x:=1) (y:=1) 0 (box 1 1 (fun _ _ => eq_nat_dec i a: @X bool_Graph tt tt)) 0 0)
  (makeMat_blocks (x:=1) (y:=1) 1 0 0 0)
  (makeMat_blocks (x:=1) (y:=1) 0 0 1 0)
  (S a).

Definition bZero : bAut := @Build_bAut 0
  0
  (fun i => 0)
  0
  0
  0.

Definition bOne : bAut := @Build_bAut 1
  1
  (fun i => 0)
  1
  1
  0.


 
Fixpoint X_to_bAut (x : Free.X) : bAut :=
  match x with 
    | Free.one => bOne
    | Free.zero => bZero
    | Free.dot x y => bDot (X_to_bAut x) (X_to_bAut y)
    | Free.plus x y => bPlus (X_to_bAut x) (X_to_bAut y)
    | Free.star x => bPlus bOne (bpStar (X_to_bAut x)) 
    | Free.var i => bVar i
  end.




                          (****************)
                          (* Epsilon_free *)
                          (****************)

Definition epsilon_free A : bAut := 
  let Js := mx_force (mxbool_star (b_J A)) in 
    @Build_bAut (b_size A)                
    0
    (Force.id (b_max_label A) (fun i => mxbool_dot (b_M A i) Js))
    (mx_force (mxbool_dot (b_U A) Js))  
    (b_V A)
    (b_max_label A).

End Protect.




                    (*******************************)
                    (* conversion bAut -> NFA *)
                    (*******************************)

Definition bAut_to_NFA A := Build_NFA
  (b_size A)
  (Force.id2 (b_size A) (b_max_label A) (fun p a => set_of_ones (fun i => !(b_M A a) p i) (b_size A)))
  (set_of_ones (fun i => !(b_U A) O i) (b_size A))
  (set_of_ones (fun i => !(b_V A) i O) (b_size A))
  (b_max_label A).


Lemma bAut_to_NFA_wf A: NFA_wf (bAut_to_NFA A).
Proof.
  repeat split.
  intros s Hs. simpl in *. eauto using In_set_of_ones_lt.
  intros s Hs. simpl in *. eauto using In_set_of_ones_lt.
  intros i b Hb s Hs. simpl in Hs.
  destruct (le_lt_dec (b_size A) i) as [Hi|Hi].
  unfold Force.id2 in Hs.
  rewrite Force.id_notid, Force.id_id in Hs by assumption.
  eauto using In_set_of_ones_lt.
  rewrite Force.id2_id in Hs by assumption.
  eauto using In_set_of_ones_lt.
Qed.


                        (********************************)
                        (* Determinisation (NFA -> DFA) *)
                        (********************************)



Module Det. Section S.

  Variable A : NFA.
  
  Let delta := N_delta A.
  Let initiaux := N_initiaux A.
  Let finaux := N_finaux A.
  Let size := N_size A.
  Let max_label := N_max_label A.

  Definition delta_set (q : stateset) (a : label): stateset := 
    StateSet.fold (fun x => StateSet.union (delta x a)) q StateSet.empty.

  Definition Todo := (stateset * state)%type.
  Definition Table := StateSetMap.t state.
  Definition Delta := StateMap.t (LabelMap.t state).
  Definition NTT := (state * StateSetMap.t state * list Todo)%type.
  Definition NTTD := (NTT * Delta)%type.
  Definition NTTC := (NTT * LabelMap.t state)%type.



  (* les deux zéros ne sont pas sensés être atteints *)
  Definition Delta_to_fun (d: Delta) s a :=
    match StateMap.find s d with
      | Some m => match LabelMap.find a m with
                    | Some t => t
                    | _ => O
                  end
      | _ => O
    end.

  Definition finals (table: Table) :=
    StateSetMap.fold 
      (fun p np acc => 
        if StateSet.exists_ (fun s => StateSet.mem s finaux) p 
          then StateSet.add np acc else acc
      ) table StateSet.empty.

  Definition insert_table (ntt: NTT) (q: stateset): state*NTT :=
    let '(next,table,todo) := ntt in
      match StateSetMap.find q table with
        | Some nq => (nq,ntt)
        | None => 
          let nq := next in
          let table := StateSetMap.add q nq table in
            (nq, (S next, table, (q,nq)::todo))
    end.

  Definition explore_labels (p: stateset) (np: state): NTTC -> NTTC := 
    fold_labels 
      (fun a acc => 
        let '(ntt,dp) := acc in
        let q := delta_set p a in 
        let '(nq,ntt) := insert_table ntt q in
        let dp := LabelMap.add a nq dp in
          (ntt,dp)
      ) max_label.
    

  (* prédicat ad-hoc pour tracer les appels récursifs de explore *)
  Inductive explore_calls: NTTD -> NTTD -> Prop :=
  | explore_call:
    forall (delta' : Delta) (next : nat) (table : StateSetMap.t nat) (todo : list Todo) 
      (p : stateset) (np : nat) (dp : StateMap.t nat) (ntt : NTT),
      explore_labels p np (next, table, todo, StateMap.empty nat) = (ntt, dp) ->
      explore_calls 
      (ntt, StateMap.add np dp delta')
      (next, table, (p, np) :: todo, delta').

  (* la terminaison sera prouvée plus tard *)
  Definition Termination := NFA_wf A -> well_founded explore_calls.
  Hypothesis H: Termination.
  Hypothesis A_wf: NFA_wf A.

  Function explore (nttd: NTTD) {wf explore_calls nttd}: NTTD := 
    let '(next,table,todo, delta') := nttd in
      match todo with
        | (p,np)::todo =>
          let '(ntt,dp) := explore_labels p np (next,table,todo,LabelMap.empty state) in 
            explore (ntt,StateMap.add np dp delta')
        | nil => nttd 
      end.
  Proof.
    intros. constructor. assumption.
    apply (guard 100 (H A_wf)).
  Defined.                      (* BUG: très long *)
  
  (* 0 est l'etat initial *)
  Definition build :=
    let init := (initiaux, O) in
    let table := StateSetMap.add initiaux O (StateSetMap.empty _) in      
    let '(next,table,_,delta') := explore (1%nat, table, init::nil, StateMap.empty _) in 
      Build_DFA next (Delta_to_fun delta') 0 (finals table) max_label.

End S. End Det.

Definition NFA_to_DFA (H: forall A, Det.Termination A) A := @Det.build A (H A).
Implicit Arguments NFA_to_DFA [].


(* calcul de l'automate déterminisé de l'expression a.
   l'hypothèse H correspond à la preuve de terminaison de l'algo *)
Definition X_to_DFA H a:=
  let thomson := X_to_bAut a in
  let epsf := epsilon_free thomson in
  let nfa := bAut_to_NFA epsf in
    NFA_to_DFA H nfa (bAut_to_NFA_wf _).


(* composition parallèle de deux automates déterministes
   (attention, l'état initial n'a aucun sens)
 *)
Definition merge_DFAs A B :=
  let sA := D_size A in
  let sB := D_size B in
  let s := (sA+sB)%nat in
  let k := Max.max (D_max_label A) (D_max_label B) in 
  (* damien: j'enleve ce force, qui embete un peu dans les preuves de wf, 
     et qui ne devrait pas etre important une fois passes en binaires 
     add: vérifier que c'est toujours gênant, maintenant qu'il y a le test 
     sur les max_label dans decide_Kleene *)
  let delta :=  (*Force.id2 s k*)  (fun p a => 
    match S p - sA with 
      | O => D_delta A p a
      | S p' => (D_delta B p' a + sA)%nat
    end)
  in
  let finaux := merge_plus sA (D_finaux B) (D_finaux A) in
    Build_DFA s delta 0%nat finaux k.



                        (*********************************)
                        (* Minimisation (DFA -> classes) *)
                        (*********************************)


Module SimpleMyhillNerode. Section S.

  Variable A: DFA.

  Let delta := D_delta A.
  Let size := D_size A.
  Let finaux := D_finaux A.
  Let max_label := D_max_label A.
  Definition smh_states := fold_labels (fun a acc => StateSet.add a acc) size (StateSet.empty).  
  Notation states := smh_states.
  Definition smh_non_finaux := StateSet.diff states finaux.
  Notation non_finaux := smh_non_finaux.

  Definition T := (StateSetSet.t * Label_x_StateSetSet.t)%type.
  
  Definition card_l := Label_x_StateSetSet.cardinal.

  Definition splittable p q a :=
    let cpl := StateSet.partition (fun i => StateSet.mem (delta i a) q) p in 
      if StateSet.is_empty (fst cpl) || StateSet.is_empty (snd cpl) 
        then None
        else Some cpl.

  Definition f_update_splitters p pf pt a L :=       
    let ap := (a,p) in
      Label_x_StateSetSet.add (a,pf) (Label_x_StateSetSet.add (a,pt) (Label_x_StateSetSet.remove ap L )).

  Definition update_splitters p pf pt:  label -> Label_x_StateSetSet.t -> Label_x_StateSetSet.t :=
    fold_labels (f_update_splitters p pf pt).
          
  Definition do_split a q :=
    StateSetSet.fold (fun p (acc: T) => 
      match splittable p q a with 
        | None => acc
        | Some (pf,pt) =>
          let (P,L) := acc in
            (StateSetSet.add pf (StateSetSet.add pt (StateSetSet.remove p P)), 
              update_splitters p pf pt max_label L)
      end).
 
  Inductive MN_calls: T -> T -> Prop :=
  | MN_call: 
    forall (P : StateSetSet.t) (L : Label_x_StateSetSet.t),
      forall (a : nat) (q : StateSet'.t),
        Label_x_StateSetSet.choose L = Some (a, q) ->
        MN_calls (do_split a q P (P, Label_x_StateSetSet.remove (a, q) L)) (P, L).
    
  Definition Termination := well_founded MN_calls. 
  Hypothesis H: Termination.

  Function MyhillNerode (PL : T) {wf MN_calls PL} : StateSetSet.t :=
    let (P,L) := PL in
      match Label_x_StateSetSet.choose L with
        | None => P
        | Some(a,q) => MyhillNerode (do_split a q P (P,Label_x_StateSetSet.remove (a,q) L))
      end.
  Proof.
    intros. constructor. assumption. 
    apply (guard 100 H). 
  Defined.                      (* BUG: long *)


  Definition partition_initiale := StateSetSet.union (StateSetSet.singleton finaux) (StateSetSet.singleton non_finaux).

  Definition coupes_initiales := 
    fold_labels (fun b acc => Label_x_StateSetSet.add (b,    finaux) acc) max_label 
    (fold_labels (fun b acc => Label_x_StateSetSet.add (b,non_finaux) acc) max_label 
      Label_x_StateSetSet.empty).

  Definition partition := MyhillNerode (partition_initiale,coupes_initiales).
  
  Definition equiv i j := StateSetSet.exists_ (fun s => StateSet.mem i s && StateSet.mem j s) partition.

End S. End SimpleMyhillNerode.

Module HopcroftMyhillNerode. Section S.

  Variable A: DFA.

  Let delta := D_delta A.
  Let size := D_size A.
  Let finaux := D_finaux A.
  Let max_label := D_max_label A.

  Let states := (fold_labels (fun a acc => StateSet.add a acc) size StateSet.empty).
  Let non_finaux := (StateSet.diff states finaux).
  
  Definition T := (StateSetSet.t * Label_x_StateSetSet.t)%type.
  
  Definition card_l := Label_x_StateSetSet.cardinal.

  Definition splittable p q a :=
    let cpl := StateSet.partition (fun i => StateSet.mem (delta i a) q) p in 
      if StateSet.is_empty (fst cpl) || StateSet.is_empty (snd cpl) 
        then None
        else Some cpl.
    
  Definition update_splitters p pf pt:  label -> Label_x_StateSetSet.t -> Label_x_StateSetSet.t :=
    fold_labels (fun a L  => 
      let ap := (a,p) in
      if Label_x_StateSetSet.mem ap L 
        then Label_x_StateSetSet.add (a,pf) (Label_x_StateSetSet.add (a,pt) (Label_x_StateSetSet.remove ap L ))
      else if le_lt_dec (StateSet.cardinal pf ) (StateSet.cardinal pt) 
        then Label_x_StateSetSet.add (a,pf) L
        else Label_x_StateSetSet.add (a,pt) L
    ).
          
  Definition do_split a q :=
    StateSetSet.fold (fun p (acc: T) => 
      match splittable p q a with 
        | None => acc
        | Some (pf,pt) =>
          let (P,L) := acc in
            (StateSetSet.add pf (StateSetSet.add pt (StateSetSet.remove p P)), 
              update_splitters p pf pt max_label L)
      end).
 
  Inductive MN_calls: T -> T -> Prop :=
  | MN_call: 
    forall (P : StateSetSet.t) (L : Label_x_StateSetSet.t),
      forall (a : nat) (q : StateSet'.t),
        Label_x_StateSetSet.choose L = Some (a, q) ->
        MN_calls (do_split a q P (P, Label_x_StateSetSet.remove (a, q) L)) (P, L).
    
  Definition Termination := well_founded MN_calls. 
  Hypothesis H: Termination.

  Function MyhillNerode (PL : T) {wf MN_calls PL} : StateSetSet.t :=
    let (P,L) := PL in
      match Label_x_StateSetSet.choose L with
        | None => P
        | Some(a,q) => MyhillNerode (do_split a q P (P,Label_x_StateSetSet.remove (a,q) L))
      end.
  Proof.
    intros. constructor. assumption. 
    apply (guard 100 H). 
  Defined.                      (* BUG: long *)

  Definition partition_initiale := StateSetSet.union (StateSetSet.singleton finaux) (StateSetSet.singleton non_finaux).

  Definition coupes_initiales := 
    if le_lt_dec (StateSet.cardinal finaux) (StateSet.cardinal non_finaux) 
      then fold_labels (fun b acc => Label_x_StateSetSet.add (b,    finaux) acc) max_label Label_x_StateSetSet.empty
      else fold_labels (fun b acc => Label_x_StateSetSet.add (b,non_finaux) acc) max_label Label_x_StateSetSet.empty.

  Definition partition := MyhillNerode (partition_initiale,coupes_initiales).
  
  Definition equiv i j := StateSetSet.exists_ (fun s => StateSet.mem i s && StateSet.mem j s) partition.

End S. End HopcroftMyhillNerode.

  
(******************************************************************)
(* assemblage des morceaux, pour obtenir la procedure de decision *)
(******************************************************************)


(* Module Min := HopcroftMyhillNerode. *)
Module Min := SimpleMyhillNerode.

(* comparaison de a et b *) 
Definition decide_Kleene 
  (HDet: forall A, Det.Termination A)
  (HMin: forall A, Min.Termination A)
  (a b: Free.X) := 
  let A := X_to_DFA HDet a in
  let B := X_to_DFA HDet b in
       (* ce test ne coûte rien (il bride potentiellement l'algo en présence de zéros
          mais ceux-ci seront nettoyés de toutes façons), 
          l'avantage est qu'il facilite pas mal les preuves *)
    eq_nat_dec (D_max_label A) (D_max_label B) 
    &&
    @Min.equiv (merge_DFAs A B) (HMin _) (D_initial A) (D_size A + D_initial B)%nat
    .


(*begintests
Require Import FreeKleeneAlg.
Section tests.

  Existing Instance KAF_Graph. 
  Existing Instance KAF_SemiLattice_Ops. 
  Existing Instance KAF_Monoid_Ops.
  Existing Instance KAF_Star_Op.  

  Let a := Free.var 0 : @X KAF_Graph tt tt.
  Let b := Free.var 1 : @X KAF_Graph tt tt.
  Let c := Free.var 2 : @X KAF_Graph tt tt.
  Let d := Free.var 3 : @X KAF_Graph tt tt.
  Let z := Free.var 4 : @X KAF_Graph tt tt.
  
  Let g := b * c * a. 
  Let h := (g*g#)#*a.
  
  Let e := a##*(h+g*g#+1)#.
  Let f := a#*h#*(g#*h#)#.
  Variable HDet : forall A, Det.Termination A.
  Variable HMin : forall A, Min.Termination A.

  Ltac pcheck v a b :=
    idtac a "==" b "   (" v ")";
    assert (decide_Kleene HDet HMin a b = v).
  Ltac check := vm_compute; try reflexivity  || idtac "Tactic was wrong".
  
  Goal True.
    idtac "".


    pcheck true  a a. Time check. 
    pcheck false a b. Time check.
    pcheck true  (a#) (a#). Time check.
    pcheck false (a#) (b#). Time check.
    pcheck true  (a*a#) (a#*a). Time check.
    pcheck true  (a##) (a#). Time check.
    pcheck false (a##) (a). Time check.
    pcheck true  (a*(b*a)#) ((a*b)#*a). Time check. 
    pcheck false (a*(b#+c)) (a*(b+c)#). Time check. 
    pcheck true  ((a+b)#) (a#*(b*a#)#). Time check. 
    pcheck true  ((a+b+c)#) (a#*(b#*(c*b#)#*a#)#). Time check. (* .13 *)
    pcheck false ((a+b+c)#) (a#*(b#*(b*c#)#*a#)#). Time check. (* .14 *)
    pcheck true  ((a+b+c+d)#) (a#*(b#*(c#*(d*c#)#*b#)#*a#)#). Time check. (* .56 *)
    pcheck false ((a+b+c+d)#) (a#*(b#*(c#*(c*d#)#*b#)#*a#)#). Time check. (* .57 *)
    pcheck true  ((a*b*c*d+d*c*b*a)#) ((a*b*c*d)#*(d*c*b*a*(a*b*c*d)#)#). Time check. (* 1. *)
    pcheck true  ((a*b*c*d*z+z*d*c*b*a)#) ((a*b*c*d*z)#*(z*d*c*b*a*(a*b*c*d*z)#)#). Time check. (* 2.4 *) 
    pcheck true  ((h+g*g#+1)#) (h#*(h#*g#)#). Time check. (* 3.7 *)
    pcheck false ((h+g*g#+1)#) (g#*(h#*h#)#). Time check. (* 3.9 *)
 
  Abort.

End tests.
endtests*)
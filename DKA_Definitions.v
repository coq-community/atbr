(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** In this file we define several types of automatas:
    - [MAUT] : automatas represented with matrices 
    - [eNFA] : non-deterministric automatas with epsilon transitions
    - [NFA] : non-deterministric automatas without epsilon transitions
    - [DFA] : deterministic automatas

    We also define useful notations, generic functions, and lemmas.  
*)

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import Monoid.
Require Import SemiLattice.
Require Import SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiLattice.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.
Require Export BoolView.
Require Export Model_RegExp.
        Export RegExp.Load.

Require Import MyFSets.
Require Import MyFSetProperties.
Require Import MyFMapProperties.
Require FMapAVL.

Require Numbers. Export Numbers.PositiveUtils.

Set Implicit Arguments.
Unset Strict Implicit.

Module Label := Pos_as_OT.
Module StateSet := NumSet.
Module StateSetProps := NumSetProps.

Module StateMap := NumMap.
Module StateMapProps := NumMapProps.

Module StateLabel := PairOrderedType NumOTA NumOTA.
Module StateLabelMap' := FMapAVL.Make StateLabel. Module StateLabelMap := FMapHide StateLabelMap'.
Module StateLabelMapProps := MyMapProps StateLabelMap.

Notation label := num (only parsing).         
Notation state := num (only parsing).
Notation stateset := StateSet.t.
Notation statemap := StateMap.t.
Notation statelabelmap := StateLabelMap.t.

Notation eq_state_bool := eqb.
Notation lt_state_bool := ltb.
Notation eq_label_bool := eqb.

Open Scope nat_scope.
Open Scope A_scope.

Notation nat_of_state := nat_of_num.
Notation state_of_nat := num_of_nat.

Definition statesetelt_of_nat: nat -> StateSet.elt := state_of_nat. 
Coercion statesetelt_of_nat : nat >-> StateSet.elt.

Definition statemapelt_of_nat: nat -> StateMap.key := state_of_nat. 
Coercion statemapelt_of_nat : nat >-> StateMap.key.

Definition numota_of_nat: nat -> NumOTA.t := state_of_nat.
Coercion numota_of_nat : nat >-> NumOTA.t.


Notation below := lt.
Definition setbelow s n := forall i, StateSet.In i s -> below i n.

Definition optionset_to_set o := 
  match o with 
    | Some p => p 
    | None => StateSet.empty 
  end.

Definition statemap_set_to_fun e := fun i => optionset_to_set (StateMap.find i e).

Notation fold_states := fold_num (only parsing).
Notation fold_labels := fold_num (only parsing).

Definition labelling max (mem: label -> bool): regex :=
  sum 0 max (fun a => xif (mem a) (RegExp.var (num_of_nat a): regex) 0).


(** High-level automata, represented with matrices *)
Module MAUT.
  Record t := build {
    size:    nat; 
    initial: KMX 1    size;
    delta:   KMX size size;
    final:   KMX size 1
  }.

  (** formal evaluation to a regex *)
  Definition eval A: regex := mx_to_scal (initial A * delta A # * final A).

  Inductive equal : relation t :=
  | equal_refl: forall n U U' (M M': KMX n n) V V', 
    U == U' -> M == M' -> V == V' -> equal (build U M V) (build U' M' V').
  
  Infix " [==] " := equal (at level 80).

  Instance equal_equiv : Equivalence equal. 
  Proof.
    constructor.
    intro x; destruct x. constructor; reflexivity.
    intros x y H. destruct H. constructor; auto.
    intros x y z Hxy Hyz. 
    assert (Sxy: size x = size y /\ 
                 mx_equal_at 1 (size x) (initial x) (initial y) /\
                 mx_equal_at (size x) (size x) (delta x) (delta y) /\
                 mx_equal_at (size x) 1 (final x) (final y)
    ). destruct Hxy. auto.
    clear Hxy.
    destruct Hyz. destruct x. simpl in Sxy. intuition. subst.
    constructor.
     transitivity U; assumption.
     transitivity M; assumption.
     transitivity V; assumption.
  Qed.
  
  Instance eval_compat : Proper (equal ==> Classes.equal tt tt) eval.
  Proof.
    intros A B H. destruct H. auto with compat. 
  Qed.

End MAUT.




(** Non deterministic automata, with epsilon transitions *)
Module eNFA.
  Record t := build {
    size:      state;                  (* next fresh state (= size) *)
    epsilon:   state -> stateset;      (* epsilon-transitions *)
    deltamap:  statelabelmap stateset; (* visible transitions (we keep a map for efficiency reasons) *)
    initial:   state;                  (* starting state *)
    final:     state;                  (* accepting state *)
    max_label: label                   (* maximal label + 1 *)
  }.

  Definition delta A a i := optionset_to_set (StateLabelMap.find (i,a) (deltamap A)).

  Definition well_founded A := well_founded (fun x y => StateSet.mem x (epsilon A y) = true).

  Notation belong s A := (below s (size A)).
  Notation setbelong s A := (setbelow s (size A)).
  
  Record bounded A := {
    bounded_delta: forall a i, setbelong (delta A a i) A;
    bounded_eps: forall i, setbelong (epsilon A i) A;
    bounded_initial: belong (initial A) A;
    bounded_final: belong (final A) A
  }.

  (** translation to matricial automata *)
  Definition to_MAUT A := 
    let n := nat_of_state (size A) in
      MAUT.build
      (mx_point 1 n 0 (initial A) 1)
      (mx_bool _ n n (fun i j => StateSet.mem j (epsilon A i)) 
         + box n n (fun i j => labelling (max_label A) 
                       (fun a => StateSet.mem j (delta A a i))))
      (mx_point n 1 (final A) 0 1).

  Definition eval := to_MAUT >> MAUT.eval.

End eNFA.


      

(** Non deterministic, epsilon-free automata *)
Module NFA.
  Record t := build {
    size:      state;          
    delta:     label -> state -> stateset; 
    initiaux:  stateset;
    finaux:    stateset;
    max_label: label
  }.

  Notation belong s A := (below s (size A)).
  Notation setbelong s A := (setbelow s (size A)).
  
  Record bounded A := {
    bounded_delta: forall a i, setbelow (delta A a i) (size A);
    bounded_initiaux: setbelong (initiaux A) A;
    bounded_finaux: setbelong (finaux A) A
  }.

  (** translation to matricial automata *)
  Definition to_MAUT A := 
    let n := nat_of_state (size A) in
      MAUT.build 
    (mx_bool _ 1 n (fun _ j => StateSet.mem j (initiaux A)))
    (box n n (fun i j => labelling (max_label A) 
                 (fun a => StateSet.mem j (delta A a i))))
    (mx_bool _ n 1 (fun i _ => StateSet.mem i (finaux A))).
  
  Definition eval := to_MAUT >> MAUT.eval.

  Definition change_initial A i := 
    build (size A) (delta A) i (finaux A) (max_label A).

End NFA.




(** Deterministic automata *)
Module DFA.
  Record t := build {
    size:      state;          
    delta:     label -> state -> state;
    initial:   state;
    finaux:    stateset;
    max_label: label
  }.

  Notation belong s A := (below s (size A)).
  Notation setbelong s A := (setbelow s (size A)).
  
  (* In order to ease the definition of merge, we require that
  the automata are bounded even outside their domain *)
  Record bounded A := {
    bounded_delta: forall a i,  belong (delta A a i) A;
    bounded_initial: belong (initial A) A;
    bounded_finaux: setbelong (finaux A) A
  }.

  (** translation to matricial automata *)
  Definition to_MAUT A := 
    let n := nat_of_state (size A) in
      MAUT.build 
      (mx_point 1 n 0 (initial A) 1)
      (box n n (fun i j => labelling (max_label A) 
                   (fun a => eq_state_bool (state_of_nat j) (delta A a i))))
      (mx_bool _ n 1 (fun i _ => StateSet.mem i (finaux A))).

  Definition eval := to_MAUT >> MAUT.eval.

  Definition change_initial A i := 
    build (size A) (delta A) i (finaux A) (max_label A).

End DFA.


(** algebraic lemmas, to prove correctness of determinisation and equivalence check  *)
Section filters.

  Context `{KA: KleeneAlgebra}.
  
  Lemma left_filter: forall i k k' j (s: X k k') m m' u (u': X i k') v (v': X k' j),
    u*s ==   u' ->
    m*s == s*m' ->
    v   == s*v' ->
    u'*m'#*v' == u*m#*v.
  Proof.
    intros until v'. intros Hu Hm Hv.
    rewrite Hv, <- Hu. monoid_normalize. 
    monoid_rewrite (comm_iter_left Hm). monoid_reflexivity.
  Qed.

  Lemma right_filter: forall i k k' j (s: X k' k) m m' u (u': X i k') v (v': X k' j),
      u == u'*s ->
    s*m == m'*s ->
    s*v == v'   ->
    u'*m'#*v' == u*m#*v.
  Proof.
    intros until v'. intros Hu Hm Hv.
    rewrite Hu, <- Hv. monoid_normalize. 
    monoid_rewrite (comm_iter_right Hm). monoid_reflexivity.
  Qed.

End filters.

(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Parallel composition of two DFAs.

    We use the pi0 and pi1 functions from [Numbers] to encode the
    disjoint union of states.
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
Require Import DKA_Definitions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Import DFA.

Definition merge_DFAs A B :=
  let s := max (pi0 (size A)) (pi1 (size B)) in
  let k := max_label A in       (* = max_label B, by assumption *)
  let delta := (fun a p => 
    match pimatch p with
      | inl p => pi0 (DFA.delta A a p)
      | inr p => pi1 (DFA.delta B a p)
    end)
  in
  let finaux := 
    StateSet.fold (fun x acc => StateSet.add (pi0 x) acc) (finaux A)
      (StateSet.fold (fun x acc => StateSet.add (pi1 x) acc) (finaux B) StateSet.empty)
  in
    DFA.mk s delta 0 finaux k.

Definition compare_DFAs T (equiv: DFA.t -> state -> state -> option T) A B :=
  equiv (merge_DFAs A B) (pi0 (initial A)) (pi1 (initial B)).

Lemma below_max_pi0: forall n m m', below n m -> below (pi0 n) (max (pi0 m) (pi1 m')).
Proof.
  intros. rewrite lt_nat_spec, max_spec. eapply lt_le_trans. 2: apply Max.le_max_l. 
  rewrite <- lt_nat_spec. apply lt_pi0. assumption.
Qed.

Lemma below_max_pi1: forall n m m', below n m' -> below (pi1 n) (max (pi0 m) (pi1 m')).
Proof.
  intros. rewrite lt_nat_spec, max_spec. eapply lt_le_trans. 2: apply Max.le_max_r. 
  rewrite <- lt_nat_spec. apply lt_pi1. assumption.
Qed.

 

Lemma merge_bounded: forall A B, bounded A -> bounded B -> bounded (merge_DFAs A B).
Proof.
  intros A B HA HB. constructor.
  intros a i. simpl. case_eq (pimatch i); intros p Hp.
   apply below_max_pi0. apply (bounded_delta HA). 
   apply below_max_pi1. apply (bounded_delta HB). 
   rewrite lt_nat_spec. apply le_lt_trans with (nat_of_state (pi0 (delta A 0 0))).
    apply le_O_n. rewrite <- lt_nat_spec. rapply below_max_pi0. apply (bounded_delta HA). 
  unfold finaux, merge_DFAs.
  apply NumSetProps.Props.fold_rec_nodep. apply NumSetProps.Props.fold_rec_nodep.
   intro i. NumSetProps.setdec.
   intros p a Hp IH x. NumSetProps.set_iff. intuition. subst.
    apply below_max_pi1. apply HB, Hp.
   intros p a Hp IH x. NumSetProps.set_iff. intuition. subst.
    apply below_max_pi0. apply HA, Hp.
Qed.

Lemma sum_collapse': forall k f b (j: state), (j<k)%nat -> 
  sum 0 k (fun i => xif (eqb (state_of_nat i) j && b i) (f i) (0: regex)) == xif (b j) (f j) 0.
Proof.
  intros. rewrite (sum_collapse (n:=j)); auto.
   cbn. rewrite id_num. bool_simpl. reflexivity.
   intros. num_analyse. num_omega. reflexivity.
Qed.

Lemma and_neutral_left: forall (A B: Prop), A -> (A/\B <-> B). Proof. tauto. Qed.

Lemma compare_compat: SetoidList.compat_op eq NumSet.Equal (fun x acc => NumSet.add (pi0 x) acc).
Proof. repeat intro. subst. rewrite H0. reflexivity. Qed.

Local Opaque equal dot star plus one zero eq_state_bool leq NumSet.add.
Lemma eval_left: forall (A B: DFA.t), bounded A ->
  eval (change_initial (merge_DFAs A B) (pi0 (initial A))) == eval A.
Proof.
  intros A B HA. apply mx_to_scal_compat. simpl.
  set (s := nat_of_state (max (pi0 (size A)) (pi1 (size B)))).

  apply left_filter with (box (size A) s 
    (fun i j => xif (eq_state_bool (state_of_nat j) (pi0 (state_of_nat i)) 
      && lt_state_bool i (size A)) (1: regex) (0: regex))).

   mx_intros i j Hi Hj. Transparent dot. simpl. fold_regex. Opaque dot. 
   apply bounded_initial in HA. 
   setoid_rewrite xif_dot. rewrite (sum_collapse (n:=initial A)). 2: num_omega. 
    bool_simpl. simpl. rewrite dot_neutral_left. apply xif_compat; auto. 
    rewrite id_num. rewrite bool_prop_iff. bool_connectors. num_prop. nat_prop.
    intuition; num_omega.
    simpl. intros x Hx. nat_analyse; simpl; auto with algebra.

   mx_intros i j Hi Hj. Transparent dot. simpl. fold_regex. Opaque dot. 
    unfold labelling. 
    setoid_rewrite xif_dot. setoid_rewrite dot_ann_left. setoid_rewrite dot_neutral_left.
    setoid_rewrite xif_sum_zero. rewrite sum_inversion. 
    setoid_rewrite sum_distr_left.
    rewrite sum_inversion. apply sum_compat. intros a Ha. simpl.
    setoid_rewrite dot_xif_zero. setoid_rewrite dot_neutral_right. setoid_rewrite xif_xif_and.
    rewrite sum_collapse'. setoid_rewrite <- andb_assoc. rewrite sum_collapse'.  
      apply xif_compat; auto. rewrite 2id_num. rewrite match_pi0. 
      rewrite bool_prop_iff. bool_connectors. num_prop. intuition. num_omega. apply (bounded_delta HA).
      unfold s. rewrite <- lt_nat_spec. apply below_max_pi0. num_omega.
      apply -> lt_nat_spec. apply (bounded_delta HA).

   mx_intros i j Hi Hj. Transparent dot. simpl. fold_regex. Opaque dot. 
    setoid_rewrite dot_xif_zero. setoid_rewrite dot_neutral_left.
    setoid_rewrite <- andb_assoc. rewrite sum_collapse'. apply xif_compat; auto.
    rewrite id_num. rewrite bool_prop_iff. bool_connectors. num_prop. StateSetProps.mem_prop.
    rewrite and_neutral_left by num_omega.
    (* BUG d'induction *)
    (* induction (finaux A) using StateSetProps.set_induction_above. *)
    generalize (finaux A). rapply StateSetProps.set_induction_above.
     intros t H.
     rewrite H at 1. StateSetProps.set_iff.
     rewrite StateSetProps.Props.fold_1b by auto with set. 
     apply StateSetProps.Props.fold_rec_nodep. 
      StateSetProps.setdec.
      intros. StateSetProps.set_iff. intuition. discriminate.
     intros p x IHx H2 H t H1.
     Transparent NumSet.add.
     rewrite H1 at 1. rewrite (StateSetProps.fold_equal _ compare_compat _ H1); auto.
     rewrite StateSetProps.fold_add_above; ti_auto.
     StateSetProps.set_iff. rewrite <- IHx. intuition (try subst; auto using pi0_inj). 
     repeat intro. psubst. rewrite H3. reflexivity.
    apply -> lt_nat_spec. apply below_max_pi0. num_omega. 
    Opaque NumSet.add.
  Qed.

Lemma eval_right: forall (A B: DFA.t), bounded B -> max_label A = max_label B ->
  eval (change_initial (merge_DFAs A B) (pi1 (initial B))) == eval B.
Proof. 
  intros A B HB H. apply mx_to_scal_compat. simpl. rewrite H. clear H.
  set (s := nat_of_state (max (pi0 (size A)) (pi1 (size B)))).

  apply left_filter with (box (size B) s 
    (fun i j => xif (eq_state_bool (state_of_nat j) (pi1 (state_of_nat i)) 
      && lt_state_bool i (size B)) (1: regex) (0: regex))).
  
   mx_intros i j Hi Hj. Transparent dot. simpl. fold_regex. Opaque dot. 
   apply bounded_initial in HB. 
   setoid_rewrite xif_dot. rewrite (sum_collapse (n:=initial B)). 2: num_omega. 
    bool_simpl. simpl. rewrite dot_neutral_left. apply xif_compat; auto. 
    rewrite id_num. rewrite bool_prop_iff. bool_connectors. num_prop. nat_prop.
    intuition; num_omega.
    simpl. intros x Hx. nat_analyse; simpl; auto with algebra.

   mx_intros i j Hi Hj. Transparent dot. simpl. fold_regex. Opaque dot. 
    unfold labelling. 
    setoid_rewrite xif_dot. setoid_rewrite dot_ann_left. setoid_rewrite dot_neutral_left.
    setoid_rewrite xif_sum_zero. rewrite sum_inversion. 
    setoid_rewrite sum_distr_left.
    rewrite sum_inversion. apply sum_compat. intros a Ha. simpl.
    setoid_rewrite dot_xif_zero. setoid_rewrite dot_neutral_right. setoid_rewrite xif_xif_and.
    rewrite sum_collapse'. setoid_rewrite <- andb_assoc. rewrite sum_collapse'.  
      apply xif_compat; auto. rewrite 2id_num. rewrite match_pi1. 
      rewrite bool_prop_iff. bool_connectors. num_prop. intuition. num_omega. apply (bounded_delta HB).
      unfold s. rewrite <- lt_nat_spec. apply below_max_pi1. num_omega.
      apply -> lt_nat_spec. apply (bounded_delta HB).

   mx_intros i j Hi Hj. Transparent dot. simpl. fold_regex. Opaque dot. 
    setoid_rewrite dot_xif_zero. setoid_rewrite dot_neutral_left.
    setoid_rewrite <- andb_assoc. rewrite sum_collapse'. apply xif_compat; auto.
    rewrite id_num. rewrite bool_prop_iff. bool_connectors. num_prop. StateSetProps.mem_prop.
    rewrite and_neutral_left by num_omega.
    apply StateSetProps.Props.fold_rec_nodep. 
     (* BUG d'induction *)
     (* induction (finaux B) using StateSetProps.set_induction_above. *)
     generalize (finaux B). rapply StateSetProps.set_induction_above.
      intros t H. rewrite H at 1. rewrite StateSetProps.Props.fold_1b by auto with set. StateSetProps.set_iff. tauto.
      intros p x IHx H2 H t H1.
      rewrite H1 at 1. rewrite StateSetProps.Props.fold_2; eauto with typeclass_instances. 
     StateSetProps.set_iff. rewrite <- IHx. intuition (try subst; auto using pi1_inj).
     Transparent NumSet.add.
     repeat intro. subst. rewrite H3. reflexivity.
     repeat intro. StateSetProps.set_iff. tauto.
     intro. rewrite H1. StateSetProps.set_iff. tauto.
    intros x a _. StateSetProps.set_iff. intuition psubst. discriminate.
    apply -> lt_nat_spec. apply below_max_pi1. num_omega.
    Opaque NumSet.add.
Qed.


Section S.

  Variable T: Type.
  Variable equiv: t -> state -> state -> option T.
  Hypothesis equiv_correct: forall A i j, bounded A -> belong i A -> belong j A -> 
    (equiv A i j = None <-> eval (change_initial A i) == eval (change_initial A j)).

  Theorem correct: forall A B,
    bounded A -> bounded B -> max_label A = max_label B -> (compare_DFAs equiv A B = None <-> eval A == eval B).
  Proof.
    unfold compare_DFAs. intros A B HA HB H.
    rewrite <- (eval_left B HA).
    rewrite <- (eval_right HB H).
    apply equiv_correct.
    apply merge_bounded; assumption.
    simpl. apply below_max_pi0. eapply bounded_initial, HA.
    simpl. apply below_max_pi1. eapply bounded_initial, HB.
  Qed.

End S.



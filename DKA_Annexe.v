(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id$ i*)

Require Import Common.
Require Import Classes.
Require Import SemiLattice.
Require Import Monoid.
Require Import ATBR.SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiLattice.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.
Require Import BoolAlg.
Require Import FreeKleeneAlg.
Require Import Functors MxFunctors.
Require        Force.

Require Export DKA_Algo.
Require Export DKA_Convert.
Require Export DKA_Sets.


Set Implicit Arguments.
Unset Printing Implicit Defensive.


Section Protect.

  Opaque equal dot plus one zero star.
  
  Existing Instance bool_SemiLattice_Ops. 
  Existing Instance bool_Monoid_Ops.
  Existing Instance bool_Star_Op.
  Existing Instance bool_SemiLattice.
  Existing Instance bool_Monoid.
  Existing Instance bool_SemiRing.
  Existing Instance bool_KleeneAlgebra.
  
  Existing Instance KAF_SemiLattice_Ops. 
  Existing Instance KAF_Monoid_Ops.
  Existing Instance KAF_Star_Op.
  Existing Instance KAF_SemiLattice.
  Existing Instance KAF_Monoid.
  Existing Instance KAF_SemiRing.
  Existing Instance KAF_KleeneAlgebra.



  (* Automates matriciels de haut niveau *)

  Record MAut := {
    M_size:      state; 
    M_M:         KMX(M_size,M_size);
    M_U:         KMX(1%nat,M_size);
    M_V:         KMX(M_size,1%nat)
  }.

  Inductive MAut_eq: MAut -> MAut -> Prop :=
  | MAut_refl: forall n M M' U U' V V', M==M' -> U==U' -> V==V' -> 
    MAut_eq (@Build_MAut n M U V) (@Build_MAut n M' U' V').

  Definition eval_M A := M_U A * M_M A # * M_V A.

  Global Instance MAut_eq_Eq: Equivalence MAut_eq. 
  Proof.
    constructor; repeat intro.
    destruct x. constructor; reflexivity.
    destruct H. constructor; auto.
    destruct H. 
    (* do_depind' ltac:(fun hyp => case hyp) H0. *)
     dependent destruction H0.
     constructor; eauto using (Graph.equal_trans (G:=@mx_Graph KAF_Graph)).
  Qed.
  (* on se mange un axiome ici... faudrait voir pour le transferer en un axiome JMeq *)
  (*   Print Assumptions MAut_eq_Eq. *)

  Global Instance eval_M_compat: 
    Morphism (MAut_eq ==> equal (Graph:=@mx_Graph KAF_Graph) (1%nat,tt) (1%nat,tt)) eval_M.
  Proof.
    intros A B H. destruct H. auto with compat. 
  Qed.



  (* Automates matriciels booleens, et conversion vers les hauts-niveau *)

  Definition bAut_to_MAut A :=
    @Build_MAut
    (b_size A)
    (convert (b_J A) + convert_sum (b_max_label A) (b_M A))
    (convert (b_U A))
    (convert (b_V A)).

  Definition eval_b A := eval_M (bAut_to_MAut A).

  Inductive bAut_eq: bAut -> bAut -> Prop :=
  | Aut_refl: forall n J J' M M' U U' V V' k, J==J' -> (forall i, i<k -> M i == M' i) -> U==U' -> V==V' -> 
    bAut_eq (@Build_bAut n J M U V k) (@Build_bAut n J' M' U' V' k).

  Lemma bAut_MAut_eq: forall A B, bAut_eq A B -> MAut_eq (bAut_to_MAut A) (bAut_to_MAut B).
  Proof.
    intros A B H.
    dependent destruction H.
    constructor; simpl.
    rewrite H. apply plus_compat; trivial. 
    apply sum_compat. intros. rewrite H0 by assumption. reflexivity.
    apply convert_compat. assumption. 
    apply convert_compat. assumption. 
  Qed.

  Lemma eval_b_compat: forall A B, bAut_eq A B -> eval_b A == eval_b B.
  Proof.
    intros A B H.
    apply eval_M_compat.
    apply bAut_MAut_eq.
    assumption.
  Qed.



  (* Conversion NFA vers Matriciel booleen *)

  Definition NFA_to_bAut A := 
    @Build_bAut (N_size A) 0
    (fun a => box (G:=bool_Graph) _ _ (fun i j => StateSet.mem j (N_delta A i a)))
    (box (G:=bool_Graph) _ _ (fun _ s => StateSet.mem s (N_initiaux A)))
    (box (G:=bool_Graph) _ _ (fun t _ => StateSet.mem t (N_finaux A)))    
    (N_max_label A)
    .
  Definition eval_N A := eval_b (NFA_to_bAut A).



  (* Conversion DFA vers Matriciel booleen *)

  Definition DFA_to_bAut A := 
    @Build_bAut (D_size A) 0
    (fun a => 
      box (G:=bool_Graph) _ _ (fun i j => eq_nat_dec (D_delta A i a) j))
    (box (G:=bool_Graph) _ _ (fun _ s => eq_nat_dec s (D_initial A)))
    (box (G:=bool_Graph) _ _ (fun t _ => StateSet.mem t (D_finaux A)))    
    (D_max_label A)
    .
  Definition eval_D A := eval_b (DFA_to_bAut A).



  (* Pour la minimisation, fonction de mise a jour de l'etat initial d'un DFA *)

  Definition change_initial_D A i :=
    @Build_DFA (D_size A) (D_delta A) i (D_finaux A) (D_max_label A).




  (* Predicats de bonne formation des automates *)

  Definition bAut_wf A := 
    forall l, b_max_label A <= l -> b_M A l == 0.

(*- cette définition a fini dans DKA_Algo -*)
(*   Definition NFA_wf A := *)
(*     let n := N_size A in *)
(*        below (N_initiaux A) n *)
(*     /\ below (N_finaux A)   n *)
(*     /\ (forall i b, i < n -> b < (N_max_label A) -> below (N_delta A i b) n) *)
(*       . *)

  Definition DFA_wf A :=
    let n := D_size A in
       D_initial A < n 
    /\ below (D_finaux A) n
    /\ (forall i b, i < n -> b < D_max_label A -> D_delta A i b < n)
      .


  Lemma merge_DFAs_wf A B: DFA_wf A -> DFA_wf B -> D_max_label A = D_max_label B -> DFA_wf (merge_DFAs A B).
  Proof.
    intros A B (HAi&HAf&HAd) (HBi&HBf&HBd) H.
    repeat split; simpl.
    omega.
    apply merge_below; assumption.
    intros i b Hi Hb.
    rewrite H in HAd. rewrite H, Max.max_l in Hb by trivial.  
    (* rewrite Force.id2_id by assumption. *)
    destruct_blocks. 
     apply lt_trans with (D_size A); auto with omega.
     rewrite plus_comm. apply plus_lt_compat_l. auto with omega.
  Qed.



  (* résultats préliminaires pour la preuve finale, par l'automate mergé *)

  Definition DFA_to_MAut A := bAut_to_MAut (DFA_to_bAut A).

  Definition change_initial_M A i :=
    @Build_MAut (M_size A) (M_M A) (box _ _ (fun _ j => BoolAlg.convert tt tt (eq_nat_dec j i))) (M_V A).

  Definition change_initial_b A i :=
    @Build_bAut (b_size A) (b_J A) (b_M A) (box (G:=bool_Graph) _ _ (fun _ j => eq_nat_dec j i)) (b_V A) (b_max_label A).

  Definition empty_initial_M A :=
    @Build_MAut (M_size A) (M_M A) 0 (M_V A).

  Lemma eval_empty_initial A: eval_M (empty_initial_M A) == 0.
  Proof.
    intro. unfold eval_M. simpl. semiring_reflexivity.
  Qed.

  Lemma merge_DFAs_b A B u: DFA_wf A -> D_max_label A = D_max_label B -> 
    bAut_eq 
      (DFA_to_bAut (change_initial_D (merge_DFAs A B) u))
      (change_initial_b (bPlus (DFA_to_bAut A) (DFA_to_bAut B)) u).
  Proof.
    intros A B u (HAi&HAf&HAd) H. constructor; trivial; simpl.
    apply (zero_makeMat_blocks (G:=bool_Graph)).
    rewrite <- H, Max.max_l by trivial.
    intros a Ha. 
    Transparent equal. intros i j Hi Hj.  Opaque equal.
    simpl. destruct_blocks; simpl.
     trivial.
     destruct_nat_dec; simpl; trivial. specialize (HAd i a). subst. omega_false.
     destruct_nat_dec; simpl; trivial. 
     destruct_nat_dec; simpl; trivial. 

    Transparent equal. intros i [|] Hi Hj; try omega_false; clear Hj.  Opaque equal. simpl in *. 
    Transparent Peano.minus. unfold Peano.minus at -1. Opaque Peano.minus. 
    destruct_blocks.
    rewrite mem_merge_1 by omega. trivial. 
    rewrite mem_merge_2. 
     replace (i-D_size A) with n by omega. trivial.
     omega.
     apply HAf.
  Qed.

  Lemma change_initial_Mb A u:
    MAut_eq 
      (change_initial_M (bAut_to_MAut A) u) 
      (bAut_to_MAut (change_initial_b A u)).
  Proof.
    intros. constructor; simpl; trivial.
  Qed.

  Global Instance change_initial_M_compat: Morphism (MAut_eq ==> @eq nat ==> MAut_eq) change_initial_M.
  Proof.
    intros A B H v u Hu; subst.
    destruct H. constructor; trivial.
  Qed.



End Protect.




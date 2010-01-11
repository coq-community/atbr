(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

Require Import Common. 
Require Import List.
Require Import SetoidList.

Section defs.

Variable A : Type.
Variable eqA : relation A.

Hypothesis eqA_dec : forall x y:A, {eqA x y} + {~ eqA x y}.

Hypothesis eqA_refl : forall x, eqA x x.
Hypothesis eqA_trans : forall x y z:A, eqA x y -> eqA y z -> eqA x z.
Hypothesis eqA_sym : forall x y:A, eqA x y -> eqA y x.

Hint Resolve eqA_refl eqA_trans.
Hint Immediate eqA_dec eqA_sym.

Instance eqA_equivalence : Equivalence (eqA).
split; repeat intro; eauto. 
Qed.

Fixpoint theta x l :=
  match l with
    | nil => 0%nat
    | t :: l => if eqA_dec x t then 0%nat else S (theta x l) 
  end.

  (***********************************************************)
  (*     ----------->----- nth ----->-------                 *)
  (*     |                                 |                 *)
  (* entiers                               A                 *)
  (*     |----------<-----theta ----<------|                 *)
  (* predicat < PQ                        InA L              *)
  (*                                                         *)
  (* egalite de leibniz                   eqA                *)
  (***********************************************************)

   Global Instance theta_compat :
Proper (
  eqA ==>
  (@eq (list A))  ==>
  @eq nat) (theta).
Proof.
  unfold Proper, respectful. repeat intro. 
  subst. 

  induction y0. simpl. reflexivity.
  simpl. repeat (destruct eqA_dec). reflexivity. apply False_ind. apply n. eauto.
    apply False_ind. apply n. eauto.
    congruence. 
Qed.

Lemma theta_nth_iso s L : List.In s L -> (forall y, eqA (List.nth (theta s L) L y) s).
Proof. 
  intros. 
  induction L.
    simpl. tauto_false.
  
    simpl.
      destruct (eqA_dec). auto.
      elim H.
      intros Heq.   contradiction n. subst; auto. 
          tauto.
Qed.

Lemma theta_nth_iso_eqA s L : (InA eqA) s L -> (forall y, eqA (List.nth (theta s L) L y) s).
Proof. 
  intros. 
  induction L. rewrite InA_nil in H. tauto_false.
  
    simpl.
      destruct (eqA_dec). auto.
      inversion H. subst. tauto_false.
      subst. apply IHL. auto.
Qed.

Lemma theta_correction_In_lt s L : In s L -> theta s L < (List.length L).
Proof.
  intros.
  induction L. tauto_false.
  simpl. destruct (eqA_dec s a).  auto with arith. apply lt_n_S. apply IHL.
  elim H; trivial.  intros Heq. destruct Heq. apply False_ind; auto.
Qed.

Lemma theta_correction_InA_lt s L : InA eqA s L -> theta s L < (List.length L).
Proof.
  intros.
  induction L. 
    rewrite InA_nil in H. tauto_false.
    
    simpl. destruct (eqA_dec s a).  auto with arith. apply lt_n_S. apply IHL.
    inversion H. subst. tauto_false.
    subst. apply H1.
Qed.

Lemma nth_theta_iso n y L : n < List.length L -> NoDupA eqA L -> theta (List.nth n L y) L = n.
Proof.
  intros. revert H; revert n.
  induction L. simpl in *; intros; omega_false. 
  simpl. intros. destruct n.
  destruct eqA_dec. auto. apply False_ind; apply n; auto.
  destruct eqA_dec. 
  inversion H0; subst. elim H3. 
  (* setoid_rewrite manquant dans InA *)
  rewrite <- e. apply In_InA. constructor; eauto. apply nth_In.
  apply lt_S_n. auto.
  rewrite IHL. reflexivity. inversion H0. auto. omega.
Qed.

Lemma theta_inversion x y L : NoDupA eqA L -> InA eqA x L -> InA eqA y L ->  theta x L = theta y L ->  eqA x y.
Proof.
  intros. induction L.  inversion H0.
  simpl in *.

  destruct (eqA_dec x a); destruct (eqA_dec y a); simpl in *.
    eapply eqA_trans; eauto. 
    discriminate. 
    discriminate.
    inversion H0; inversion H1; inversion H; subst; try tauto_false. 
    
    apply IHL; auto.
Qed.

  

End defs.
  

(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Simple properties about Kleene algebras *)

From ATBR Require Import Common.
From ATBR Require Import Classes.
From ATBR Require Import Graph.
From ATBR Require Import Monoid.
From ATBR Require Import SemiLattice.
From ATBR Require Import SemiRing.

Set Implicit Arguments.
Unset Strict Implicit.

Section Props0.

  Context `{KA: KleeneAlgebra}.

  (** other induction schemes  *)
  Lemma star_destruct_right_old A B: forall (a: X A A) (b c: X B A), b+c*a <== c  ->  b*a# <== c.
  Proof.
    intros; transitivity (c*a#).
     rewrite <- H; semiring_reflexivity.
     apply star_destruct_right.
     rewrite <- H at -1; auto with algebra. 
  Qed.

  Lemma star_destruct_left_old A B: forall (a: X A A) (b c: X A B), b+a*c <== c  ->  a#*b <== c.
  Proof.
    intros; transitivity (a#*c).
     rewrite <- H; semiring_reflexivity.
     apply star_destruct_left.
     rewrite <- H at -1; auto with algebra. 
  Qed.

  Lemma star_destruct_right_one A: forall (a c: X A A), 1+c*a <== c  ->  a# <== c.
  Proof.
    intros. rewrite <- (dot_neutral_left (a#)).
    apply star_destruct_right_old. assumption.
  Qed.

  Lemma star_destruct_left_one A: forall (a c: X A A), 1+a*c <== c  ->  a# <== c.
  Proof.
    intros. rewrite <- (dot_neutral_right (a#)).
    apply star_destruct_left_old. assumption.
  Qed.

End Props0.

(** simple tactics to run an induction without having to remember which scheme to use  *)
Ltac star_left_induction :=
  first [ apply star_destruct_left |
          apply star_destruct_left_old |
          apply star_destruct_left_one ].

Ltac star_right_induction :=
  first [ apply star_destruct_right |
          apply star_destruct_right_old |
          apply star_destruct_right_one ].


(** simple properties  *)
Section Props1.

  Context `{KA: KleeneAlgebra}.
  Variable A: T. 

  #[global] Instance star_incr: 
  Proper ((leq A A) ==> (leq A A)) (star A).
  Proof.
    intros a b H.
    star_right_induction.
    rewrite H. rewrite star_make_left. reflexivity.
  Qed.

  #[global] Instance star_compat: Proper ((equal A A) ==> (equal A A)) (star A).
  Proof.
    intros a b H. apply leq_antisym; apply star_incr; apply equal_leq; auto. 
  Qed.
  
  Lemma one_leq_star_a (a: X A A): 1 <== a#.
  Proof.
    rewrite <- star_make_left; auto with algebra. 
  Qed.

  Lemma a_leq_star_a (a: X A A): a <== a#.
  Proof.
    rewrite <- star_make_left.
    rewrite <- one_leq_star_a. 
    semiring_reflexivity.
  Qed.

  Lemma star_mon_is_one (a: X A A): a <== 1 -> a# == 1.
  Proof.
    intro H.
    apply leq_antisym. 
    star_left_induction.
    rewrite H; semiring_reflexivity.
    apply one_leq_star_a.
  Qed.

  Lemma star_one: (1#: X A A) == 1.
  Proof.
    apply star_mon_is_one; reflexivity.
  Qed.
  
  Lemma star_zero: (0#: X A A) == 1.
  Proof.
    apply star_mon_is_one; apply zero_inf.
  Qed.

  Lemma star_a_a_leq_star_a (a: X A A): a#*a <== a#.
  Proof.
    rewrite <- star_make_left at 2.
    semiring_reflexivity.
  Qed.

  Lemma a_star_a_leq_star_a_a (a: X A A): a*a# <== a#*a.
  Proof.
    star_right_induction.
    rewrite star_a_a_leq_star_a at 1.
    apply plus_destruct_leq; auto.
    rewrite <- one_leq_star_a. semiring_reflexivity.
  Qed.

  Lemma star_make_right (a:X A A): 1+a*a# == a#.
  Proof. 
    apply leq_antisym.
    rewrite a_star_a_leq_star_a_a.
    apply plus_destruct_leq.
    apply one_leq_star_a.
    apply star_a_a_leq_star_a.

    star_right_induction.
    rewrite <- star_make_left at 2.
    semiring_reflexivity.
  Qed.

End Props1.

(** hints *)
#[global] Hint Extern 1 (equal _ _ _ _) => apply star_compat : compat algebra.
#[global] Hint Extern 0 (equal _ _ _ _) => apply star_make_left: algebra.
#[global] Hint Extern 0 (equal _ _ _ _) => apply star_make_right: algebra.
#[global] Hint Extern 0 (equal _ _ _ _) => apply star_one: algebra.
#[global] Hint Extern 0 (equal _ _ _ _) => apply star_zero: algebra.
#[global] Hint Extern 0 (leq _ _ _ _) => apply a_leq_star_a: algebra.
#[global] Hint Extern 0 (leq _ _ _ _) => apply one_leq_star_a: algebra.

#[global] Hint Rewrite @star_zero @star_one using ti_auto : simpl.
#[global] Hint Rewrite @star_mon_is_one using ti_auto : simpl.


(** dual Kleene algebra *)
Module Dual. Section Protect.
  Existing Instance Classes.Dual.Monoid_Ops.
  Existing Instance Classes.Dual.SemiLattice_Ops.
  Existing Instance Classes.Dual.Star_Op.
  Instance KleeneAlgebra `{KA: KleeneAlgebra}: KleeneAlgebra (Dual.Graph G).
  Proof.
    constructor.
    apply (@Dual.IdemSemiRing G). eauto with typeclass_instances.
    exact (@star_make_right _ _ _ _ KA).
    exact (@star_destruct_right _ _ _ _ KA).
    exact (@star_destruct_left _ _ _ _ KA).
  Defined.

End Protect. End Dual.


(** more properties  *)
Section Props2.
  Context `{KA: KleeneAlgebra}.
  Variable A: T.

  Lemma star_trans (a: X A A): a#*a# == a#.
  Proof.
    apply leq_antisym.
    star_right_induction.
    rewrite star_a_a_leq_star_a. reflexivity.
    rewrite <- one_leq_star_a at 3. semiring_reflexivity.
  Qed.

  Lemma star_idem (a: X A A): a## == a#.
  Proof.
    apply leq_antisym.
    star_right_induction.
    rewrite star_trans.
    rewrite (one_leq_star_a a). auto with algebra. 
    apply a_leq_star_a.
  Qed.

  Lemma a_star_a_leq_star_a: forall (a: X A A), a*a# <== a#.
  Proof.
    exact (star_a_a_leq_star_a (KA:=Dual.KleeneAlgebra) (A:=A)).
  Qed.

  Lemma star_distr (a b: X A A): (a + b)# == a# * (b*a#)#.
  Proof.
    apply leq_antisym.

    star_left_induction.

    semiring_normalize.
    ac_rewrite (star_make_right (b*a#)).
    rewrite <- (star_make_right a) at 4.
    semiring_reflexivity.

    rewrite <- (star_trans (a+b)).
    apply dot_incr.
     apply star_incr. auto with algebra.
     rewrite <- (star_idem (a+b)). apply star_incr.
    rewrite <- (a_star_a_leq_star_a (a+b)).
    apply dot_incr. auto with algebra. 
    apply star_incr. auto with algebra.
  Qed.

  Lemma semicomm_iter_right B (a: X A A) (b: X B B) (c: X B A): c*a <== b*c -> c*a# <== b#*c.
  Proof.
    intro H.
    star_right_induction.
    monoid_rewrite H.
    rewrite <- star_make_left at 2.
    semiring_reflexivity.
  Qed.

  Lemma wsemicomm_iter_right (a b : X A A): a*b <== b#*a  ->  a*b# <== b#*a.
  Proof.
    intros H.
    rewrite <- star_idem at 2.
    apply semicomm_iter_right; assumption. 
  Qed.
   
End Props2.

#[global] Hint Extern 1 (leq _ _ _ _) => apply star_incr: compat algebra.
#[global] Hint Extern 0 (equal _ _ _ _) => apply star_idem: algebra.
#[global] Hint Extern 0 (equal _ _ _ _) => apply star_trans: algebra.


(** more properties, by duality  *)
Section Props3.
  Context `{KA: KleeneAlgebra}.
  
  Lemma semicomm_iter_left: forall A B (a: X A A) (b: X B B) (c: X A B), a*c <== c*b -> a#*c <== c*b#.
  Proof.
    exact (semicomm_iter_right (KA:=Dual.KleeneAlgebra)).
  Qed.

  Lemma wsemicomm_iter_left: forall A (b a : X A A), a*b <== b*a#  ->  a#*b <== b*a#.
  Proof.
    exact (wsemicomm_iter_right (KA:=Dual.KleeneAlgebra)).
  Qed.

  Lemma comm_iter_left A B (x : X A B) a b:  a * x == x * b -> a# * x == x * b# .
  Proof.
    intro H.
    apply leq_antisym.
    apply semicomm_iter_left, equal_leq. trivial.
    apply semicomm_iter_right, equal_leq. auto. 
  Qed.

  Lemma move_star A (a: X A A): a#*a == a*a#.
  Proof. apply comm_iter_left; reflexivity. Qed.

  Lemma move_star2 A B (a: X A B) (b: X B A): (a*b)#*a == a*(b*a)#.
  Proof. apply comm_iter_left. semiring_reflexivity. Qed.

End Props3.

Section Props4.
  Context `{KA: KleeneAlgebra}.
  
  Lemma comm_iter_right: forall B A (x : X A B) a b,  x * a == b * x -> x * a# == b# * x .
  Proof.
    exact (comm_iter_left (KA:=Dual.KleeneAlgebra)).
  Qed.

End Props4.

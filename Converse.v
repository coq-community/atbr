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
Require Import ATBR.SemiRing.

Set Implicit Arguments.
Unset Strict Implicit.


Section ISR.

  Context `{CISR: ConverseIdemSemiRing}.

  Lemma conv_compat' A B: forall (x y: X A B), x` == y` -> x == y.
  Proof.
    intros A B x y H.
    rewrite <- (conv_invol x).
    rewrite <- (conv_invol y).
    apply conv_compat; exact H.
  Qed.

  Hint Rewrite conv_dot conv_plus conv_invol: conv_down.

  Ltac switch := 
    match goal with
      | |- _ ` == _ ` => apply conv_compat
      | |- _   == _   => apply conv_compat'
    end; autorewrite with conv_down.

  Existing Instance dot_compat_c.
  Lemma conv_one A: one A` == 1.
  Proof.
    intro A.
    rewrite <- (dot_neutral_left_c ((one A)`)).
    switch. apply dot_neutral_left_c.
  Qed.
  Hint Rewrite conv_one: conv_down.

  Lemma conv_zero A B: zero B A` == 0.
  Proof.
    intros A B.
    transitivity ((dot B A A 0 (0`))`). 
    switch.
    symmetry. apply dot_ann_left_c. 
    autorewrite with conv_down. apply dot_ann_left_c.
  Qed.
  Hint Rewrite conv_zero: conv_down.

  Instance CISR_ISR: IdemSemiRing. 
  Proof.
    intros. constructor. constructor.
    apply dot_compat_c.
    apply dot_assoc_c.
    apply dot_neutral_left_c.
    intros. switch. apply dot_neutral_left_c.
    apply CISR_SL.
    apply dot_ann_left_c.
    intros. switch. apply dot_ann_left_c.
    apply dot_distr_left_c.
    intros. switch. apply dot_distr_left_c.
  Qed.

  Global Instance conv_incr A B:
  Proper ((leq A B) ==> (leq B A)) (conv A B).
  Proof.
    unfold leq.
    intros A B x y H.
    rewrite <- H at 2. rewrite conv_plus. apply plus_com. 
  Qed.

  Lemma conv_incr' A B: forall (x y: X A B), x` <== y` -> x <== y.
  Proof.
    intros A B x y H.
    rewrite <- (conv_invol x).
    rewrite <- (conv_invol y).
    apply conv_incr; exact H.
  Qed.

End ISR.

Ltac conv_down :=
  repeat (
    rewrite conv_invol ||
    rewrite conv_dot ||
    rewrite conv_plus 
  );
  repeat (
    rewrite conv_one ||
    rewrite conv_zero
  ).

(* Hint Rewrite conv_dot conv_plus conv_invol conv_one conv_zero: conv_down. *)

Ltac switch := 
  match goal with
    | |- _ ` == _ ` => apply conv_compat
    | |- _   == _   => apply conv_compat'
    | |- _ ` <== _ ` => apply conv_incr
    | |- _   <== _   => apply conv_incr'
  end; conv_down.


Section KA.

  Context `{KA: ConverseKleeneAlgebra}.

  Existing Instance CISR_ISR.
  
  Lemma star_destruct_left_old' A B: forall (a: X A A) (b c: X A B), b+a*c <== c  ->  a#*b <== c.
  Proof.
    intros; transitivity (a#*c).
     rewrite <- H; semiring_reflexivity.
     apply star_destruct_left_c.
     rewrite <- H at -1; auto with algebra. 
  Qed.

  Lemma conv_star A (a: X A A): a# ` == a` #.
  Proof. 
    intros A a; apply leq_antisym.

    switch. 
    rewrite <- (dot_neutral_right (a#)).
    apply star_destruct_left_old'.
    switch.
    rewrite <- star_make_left_c at 2. aci_reflexivity.

    rewrite <- (dot_neutral_right (a`#)).
    apply star_destruct_left_old'.
    switch.
    rewrite <- star_make_left_c at 2. aci_reflexivity. 
  Qed.

  Instance CKA_KA: KleeneAlgebra.
  Proof.
    intros. constructor. apply CISR_ISR. 
    apply star_make_left_c.
    apply star_destruct_left_c.
    intros. switch. rewrite conv_star. 
    apply star_destruct_left_c. switch. assumption. 
  Qed.

End KA.

Ltac conv_down ::=
  repeat (
    rewrite conv_invol ||
    rewrite conv_star || 
    rewrite conv_dot ||
    rewrite conv_plus 
  );
  repeat (
    rewrite conv_one ||
    rewrite conv_zero
  ).

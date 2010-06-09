(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import Monoid.
Require Import SemiLattice.
Require Import ATBR.SemiRing.
Require Import KleeneAlgebra.
Require Import DecideKleeneAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.


Section Props1.

  Context `{KA: KleeneAlgebra}.
  
  (** * These two lemmas from Kleene Algebra are proven again here, using the tactic [kleene_reflexivity] *)
  Lemma move_star A: forall (a: X A A), a#*a == a*a#.
  Proof. intros. kleene_reflexivity. Qed.

  Lemma move_star2 A B: forall (a: X A B) (b: X B A), (a*b)#*a == a*(b*a)#.
  Proof. intros. kleene_reflexivity. Qed.


  (** * Below are simple proofs of standard lemmas about abstract rewriting *)
  Theorem SemiConfluence_is_WeakConfluence A:
    forall (a b : X A A), b * a# <== a# * b#  <->  b# * a# <== a# * b#.
  Proof.
    intros a b; split.
     apply wsemicomm_iter_left. 
     intro H. rewrite <- H. kleene_reflexivity.
  Qed.

  Theorem WeakConfluence_is_ChurchRosser A:
    forall (a b : X A A), b * a# <== a# * b#  <->  (a+b)# <== a# * b#.
  Proof.
    intros a b; split; intro H.

    star_left_induction.
    semiring_normalize. 
    rewrite H. kleene_reflexivity.

    rewrite <- H. kleene_reflexivity. 
  Qed.

End Props1.


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
Set Implicit Arguments.
Unset Strict Implicit.

Section equal.

  Context {G: Graph}.
  Variables A B: T.

  (* projections, pour mettre dans auto, ou faciliter certaines preuves manuelles *)
  Lemma equal_refl x: equal A B x x.
  Proof. intros; apply Equivalence_Reflexive. Qed.
  Lemma equal_sym x y: equal A B x y -> equal A B y x.
  Proof. intros; apply Equivalence_Symmetric; trivial. Qed.
  Lemma equal_trans x y z: equal A B x y -> equal A B y z -> equal A B x z.
  Proof. intros; eapply Equivalence_Transitive; eauto. Qed.

  (* lemmes pour résoudre automatiquement des questions d'indiçage (a la f_equal) *)
  Lemma equal_refl_f1 (f: nat -> X A B): 
    forall i i', i = i' -> f i == f i'.
  Proof. intros; subst; reflexivity. Qed.
  Lemma equal_refl_f2 (f: nat -> nat -> X A B): 
    forall i i' j j', i=i' -> j=j' -> f i j == f i' j'.
  Proof. intros; subst ; reflexivity. Qed.
  
  Lemma equal_refl_f1t Z (f: nat -> Z -> X A B): 
    forall t i i', i = i' -> f i t == f i' t.
  Proof. intros; subst ; reflexivity. Qed.
  Lemma equal_refl_f2t Z (f: nat -> nat -> Z -> X A B): 
    forall t i i' j j', i=i' -> j=j' -> f i j t == f i' j' t.
  Proof. intros; subst ; reflexivity. Qed.
  
End equal.


Hint Resolve @equal_refl.
Hint Immediate @equal_sym.
 
(* BUG coq ? si on met les [equal_refl_fit] en hints, il les met en eapply... 
   je les mets donc a la main *)
Hint Resolve @equal_refl_f1 @equal_refl_f2.
(* Hint Resolve @equal_refl_f1t @equal_refl_f2t *)
Hint Extern 1 (equal ?A ?B (?f (_: nat) ?t) (?f _ ?t)) => apply @equal_refl_f1t.
Hint Extern 2 (equal ?A ?B (?f (_: nat) (_: nat) ?t) (?f _ _ ?t)) => apply @equal_refl_f2t.  

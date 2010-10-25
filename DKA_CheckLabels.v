(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Reflexive algorithm to check that two regex have the same sets of variables.

    We also prove that equal regex necessarily have the same set of
    labels, and that the conversion into strict star form preserves
    this set.
    *)

Require Import Common.
Require Import Classes.
Require Import Graph.

Require Import DKA_Definitions.
Require Import StrictStarForm.

Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint collect e acc :=
  match e with
    | RegExp.var i => NumSet.add i acc
    | RegExp.plus a b => collect a (collect b acc)
    | RegExp.dot a b => collect a (collect b acc)
    | RegExp.star a => collect a acc
    | _ => acc
  end.

Definition same_labels a b : bool :=
  NumSet.equal (collect a NumSet.empty) (collect b NumSet.empty).

Infix " [=] " := NumSet.Equal (at level 80).

Section protect.

Local Instance collect_compat a: Proper (NumSet.Equal ==> NumSet.Equal) (collect a).
Proof.
  induction a; simpl; intros ? ? H; rewrite H; reflexivity. 
Qed.
Definition collect_compat' a x := @collect_compat a x.

Lemma collect_incr_2: forall a i acc, 
  NumSet.In i acc -> NumSet.In i (collect a acc). 
Proof.
  induction a; simpl; intros; auto.
  NumSetProps.setdec.
Qed.

Lemma collect_incr_1: forall a i acc acc', 
  NumSet.In i (collect a acc') -> NumSet.In i (collect a acc) \/ NumSet.In i acc'. 
Proof.
  induction a; simpl; intros i acc acc' Hi; auto.
   eapply IHa1 in Hi as [Hi|Hi]. left. apply Hi. eapply IHa2 in Hi as [Hi|Hi]; auto. left. apply collect_incr_2, Hi.
   eapply IHa1 in Hi as [Hi|Hi]. left. apply Hi. eapply IHa2 in Hi as [Hi|Hi]; auto. left. apply collect_incr_2, Hi.
   NumSetProps.setdec.
Qed.

Lemma collect_com: forall a b acc, collect a (collect b acc) [=] collect b (collect a acc).
Proof.
  induction a; simpl; intros; try reflexivity.
   rewrite IHa2, IHa1. reflexivity.
   rewrite IHa2, IHa1. reflexivity.
   apply IHa.
   revert acc. induction b; intro acc; simpl; try reflexivity.
    rewrite IHb1, IHb2. reflexivity.
    rewrite IHb1, IHb2. reflexivity.
    apply IHb.
    NumSetProps.setdec.
Qed.
   
Lemma collect_idem: forall a acc, collect a (collect a acc) [=] collect a acc.
Proof.
  induction a; simpl; intro; try reflexivity.
   rewrite (collect_com a2 a1). rewrite IHa1, IHa2. reflexivity.
   rewrite (collect_com a2 a1). rewrite IHa1, IHa2. reflexivity.
   apply IHa.
   NumSetProps.setdec.
Qed.

Lemma NumSetEqual_refl: forall x, x [=] x.
Proof. reflexivity. Qed.

Local Hint Resolve collect_compat' collect_idem collect_com NumSetEqual_refl.

Notation clean := RegExp.Clean.rewrite.

Ltac contradict := 
  match goal with 
    | H: RegExp.equal ?x ?y , Hx: RegExp.is_zero (clean ?x) = _ , Hy: RegExp.is_zero (clean ?y) = _ |- _ => 
      bycontradiction; apply RegExp.Clean.equal_rewrite_zero_equiv in H; rewrite H, Hy in Hx; discriminate Hx
  end.

Lemma equal_collect: forall a b, a==b -> 
  forall acc, collect (clean a) acc [=] collect (clean b) acc.
Proof.
  intros a b H. induction H; intro acc; simpl in *; RegExp.destruct_tests; simpl in*; auto; try contradict.
   rewrite (collect_com (clean z)). rewrite collect_idem. reflexivity.
   rewrite 2 (collect_com (clean y)). rewrite collect_idem. auto.
   rewrite IHequal1, IHequal2. reflexivity.
   rewrite IHequal1, IHequal2. reflexivity.
   rewrite IHequal1. apply IHequal2. 
   symmetry. apply IHequal.
Qed.
   
Theorem complete: forall a b, same_labels (clean a) (clean b) = false -> ~ a == b.
Proof.
  intros a b H H'. assert (F := equal_collect H' NumSet.empty). apply NumSet.equal_1 in F. 
  unfold same_labels in H. rewrite F in H. discriminate.
Qed.


(** Proof that rewriting a regex in strict star form preserves its set of labels *)

Notation ssf := StrictStarForm.rewrite.

Lemma collect_ssf_remove: forall a acc, collect (remove a) acc [=] collect a acc.
Proof.
  induction a; simpl; intro acc; auto. 
   case contains_one; simpl; auto.
    case contains_one; simpl; auto.
    unfold plus_but_one. RegExp.destruct_tests; simpl; auto.
     rewrite <- IHa1, IHa2. reflexivity.
     rewrite <- IHa2, IHa1. reflexivity.
     rewrite IHa1, IHa2. reflexivity.
   case contains_one; simpl; auto.
    unfold plus_but_one. RegExp.destruct_tests; simpl; auto.
     rewrite <- IHa1, IHa2. reflexivity.
     rewrite <- IHa2, IHa1. reflexivity.
     rewrite IHa1, IHa2. reflexivity.
    case contains_one; simpl; auto.
     unfold plus_but_one. RegExp.destruct_tests; simpl; auto.
      rewrite <- IHa1, IHa2. reflexivity.
      rewrite <- IHa2, IHa1. reflexivity.
      rewrite IHa1, IHa2. reflexivity.
Qed.

Lemma collect_ssf: forall a acc, collect (ssf a) acc [=] collect a acc.
Proof.
  induction a; simpl; unfold dot_but_one, plus_but_one, star_but_one; intro acc; auto;
    RegExp.destruct_tests; simpl; auto.
   rewrite <- IHa1, IHa2. reflexivity.
   rewrite <- IHa2, IHa1. reflexivity.
   rewrite IHa1, IHa2. reflexivity.
   rewrite IHa1, IHa2. reflexivity.
   rewrite <- IHa. rewrite <- collect_ssf_remove. rewrite (RegExp.Is_one O). reflexivity.
   rewrite collect_ssf_remove, IHa. reflexivity.
Qed.

Theorem same_labels_ssf: forall a b, same_labels a b = true -> same_labels (ssf a) (ssf b) = true.
Proof.
  intros. unfold same_labels. rewrite 2 collect_ssf. assumption.
Qed.

End protect.

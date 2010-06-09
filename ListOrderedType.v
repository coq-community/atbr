(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id$ i*)

Require Import FSets.
Require Import List.

Module Make(O: OrderedType) <: OrderedType.
  Module MO := OrderedTypeFacts O.
 
  Definition t := list O.t.
 
  Definition eq := eqlistA O.eq.
 
  Inductive lt_: t -> t -> Prop :=
  | lt_nil: forall a q, lt_ nil (a::q)
  | lt_head: forall a b qa qb, O.lt a b -> lt_ (a::qa) (b::qb)
  | lt_tail: forall a b qa qb, O.eq a b -> lt_ qa qb -> lt_ (a::qa) (b::qb)
    .
  Definition lt := lt_.
 
  Lemma eq_refl : forall x : t, eq x x.
  Proof. induction x; constructor; trivial. Qed.
 
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. induction 1; constructor; auto using O.eq_sym. Qed.
 
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq.
    intros x y z H; revert z; induction H; intros z H'; trivial.
    inversion_clear H'; constructor; eauto.
  Qed.
 
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros x y z H; revert z; induction H; intros z H'.
    inversion H'; constructor.
    inversion_clear H'. 
     apply lt_head; eauto using O.lt_trans.
     apply lt_head; eauto using MO.eq_lt.
    inversion_clear H'. 
     apply lt_head; eauto using MO.eq_lt.
     apply lt_tail; eauto using O.eq_trans.
   Qed.    

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    induction 1; intro He; inversion_clear He; auto.
    eapply O.lt_not_eq; eauto.
  Qed.
 
  Definition compare x y: Compare lt eq x y.
    revert y; induction x as [|a qa]; intros [|b qb].
    apply EQ; constructor.
    apply LT; constructor.
    apply GT; constructor.
    destruct (O.compare a b).
     apply LT; constructor; trivial.
     destruct (IHqa qb).
      apply LT, lt_tail; trivial.
      apply EQ; constructor; trivial.
      apply GT, lt_tail; auto using O.eq_sym.
     apply GT; constructor; trivial.
  Defined.
 
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    induction x as [|a qa]; intros [|b qb].
    left; constructor.
    right; intro H; inversion H.
    right; intro H; inversion H.
    destruct (O.eq_dec a b).
     destruct (IHqa qb).
      left; constructor; trivial.
      right; intro H; inversion_clear H; auto.
     right; intro H; inversion_clear H; auto.
  Defined.

End Make.

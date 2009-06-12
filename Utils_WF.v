(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: Utils_WF.v 878 2009-06-09 14:11:54Z pous $ i*)

Require Import Common.
Set Implicit Arguments.

Fixpoint guard A (R : A -> A -> Prop) (n : nat) (wfR : well_founded R) {struct n}: well_founded R :=
  match n with
    | 0 => wfR
    | S n => fun x => Acc_intro x (fun y _ => guard  n (guard n wfR) y)
  end.

Section lexico.
  Variables A B: Type.
  Variable R: relation A.
  Variable S: relation B.
  Inductive lexico: relation (A*B) :=
    | lexico_left: forall a a' b b', R a' a -> lexico (a',b') (a,b)
    | lexico_right: forall a b b', S b' b -> lexico (a,b') (a,b)
      .
  Hypothesis HR: well_founded R.
  Hypothesis HS: well_founded S.
  Theorem lexico_wf: well_founded lexico.
  Proof.
    intros [a b]. revert b.
    induction a as [a IHa] using (well_founded_induction HR).
    induction b as [b IHb] using (well_founded_induction HS).
    constructor. intros [a' b'] H. inversion_clear H; auto.
  Qed.
End lexico.

Section wf_incl.
  Variable A: Type.
  Variable S: relation A.
  Hypothesis HS: well_founded S.
  Variable R: relation A.
  Hypothesis H: forall a' a, R a' a -> S a' a.
  Theorem incl_wf: well_founded R.
  Proof.
    intros a. induction a as [a IHa] using (well_founded_induction HS).
    constructor. eauto.
  Qed.
End wf_incl.

Section wf_of.
  Variables U V: Type.
  Variable f: U -> V.
  Variable R: relation V.
  Hypothesis HR: well_founded R.
  Definition rel_of: relation U := fun a' a => R (f a') (f a).
  Theorem rel_of_wf: well_founded rel_of.
  Proof.
    unfold rel_of.
    intro a. remember (f a) as fa. revert a Heqfa.
    induction fa as [fa IHa] using (well_founded_induction HR).
    constructor. intros a' H. subst. eauto. 
  Qed.
End wf_of.

Section wf_to.
  Variables U V: Type.
  Variable f: U -> V.
  Variable R: relation U.
  Inductive rel_to: relation V :=
    rel_to_intro: forall a' a, R a' a -> rel_to (f a') (f a).
  Hypothesis HR: well_founded rel_to.
  Theorem rel_to_wf: well_founded R.
    intro a. remember (f a) as fa. revert a Heqfa.
    induction fa as [fa IHa] using (well_founded_induction HR).
    constructor. intros a' H. subst. eapply IHa; trivial. constructor. trivial.
  Qed.
End wf_to.

Section wf_lexico_incl.
  Variables U A B: Type.
  Variable f: U -> A*B.
  Variable RA: relation A.
  Variable RB: relation B.
  Hypothesis HRA: well_founded RA.
  Hypothesis HRB: well_founded RB.
  Variable R: relation U.
  Hypothesis H: forall u' u, R u' u -> lexico RA RB (f u') (f u).
  Theorem lexico_incl_wf: well_founded R.
  Proof.
    apply (rel_to_wf (f:=f)). eapply incl_wf. apply lexico_wf; eassumption. 
    intros [a' b'] [a b] [u' u Hab]. auto. 
  Qed.
End wf_lexico_incl.
   


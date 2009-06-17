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
Require        Converse.
Set Implicit Arguments.
Unset Strict Implicit.

Section Def.

  Definition rel A B := A -> B -> Prop.
  Definition rel_equal A B (R S: rel A B) := forall x y, R x y <-> S x y.
  Definition rel_union A B (R S: rel A B): rel A B := fun x y => R x y \/ S x y.
  Definition rel_inter A B (R S: rel A B): rel A B := fun x y => R x y /\ S x y.
  Definition rel_comp  A B C (R: rel A B) (S: rel B C): rel A C := fun x z => exists2 y, R x y & S y z.
  Definition rel_conv  A B (R: rel A B): rel B A := fun x y => R y x.
  Definition rel_id A: rel A A := @eq A.
  Definition rel_empty A B: rel A B := fun x y => False.
  Definition rel_top   A B: rel A B := fun x y => True.
  Fixpoint rel_iter A (R: rel A A) n: rel A A :=
    match n with
      | 0 => @rel_id A
      | S n => rel_comp (rel_iter R n) R
    end.
  Definition rel_star A (R: rel A A): rel A A := fun x y => exists n, rel_iter R n x y.

  Program Instance Rel_Graph: Graph := {
    T := Type;
    X := rel;
    equal := rel_equal
  }.
  Next Obligation.
    constructor; unfold rel_equal; repeat intro; intuition.
    apply H in H0; trivial.
    apply H in H0; trivial.
    apply H, H0 in H1; trivial.
    apply H0, H in H1; trivial.
  Qed.

  Instance Rel_SemiLattice_Ops: SemiLattice_Ops := {
    plus := rel_union;
    zero := rel_empty
  }.

  Instance Rel_Monoid_Ops: Monoid_Ops := {
    dot := rel_comp;
    one := rel_id
  }.
  
  Instance Rel_Star_Op: Star_Op := { 
    star := rel_star
  }.

  Instance Rel_Converse_Op: Converse_Op := { 
    conv := rel_conv
  }.
  
  Transparent equal.

  Instance Rel_SemiLattice: SemiLattice.
  Proof.
    constructor; compute; firstorder.
  Qed.

  
  Ltac destruct_ex := repeat match goal with 
                        | H : ex _ |- _ => destruct H 
                        | H : ex2 _ _ |- _ => destruct H
                        | H : ?A \/ ?B |- _ => destruct H 
                        | H : ?A , H' : (forall (x : ?A), _ ) |- _ => specialize (H' H); intuition
                             end.
  
  Instance Rel_ConverseSemiRing: ConverseIdemSemiRing.
  Proof.
    constructor; (exact Rel_SemiLattice || intros; compute; firstorder).
    destruct_ex; eauto.
    destruct_ex; eauto.
    subst; auto.
  Qed.

  Definition Rel_IdemSemiRing: IdemSemiRing := Converse.CISR_ISR.  

(*   Instance Rel_Monoid: Monoid := . *)
(*   Proof. *)
(*     constructor; compute; intuition (destruct_ex ; eauto). *)
(*     subst; auto. *)
(*     subst; auto. *)
(*   Qed. *)

  Lemma rel_leq A B: forall (a b: @X (Rel_Graph) A B), a<==b <-> forall x y, a x y -> b x y.
  Proof.
    compute. firstorder. 
  Qed.

  Instance Rel_ConverseKleeneAlgebra: ConverseKleeneAlgebra.
  Proof.
    constructor; 
      first [ 
        exact Rel_ConverseSemiRing |
        intros
      ].
    intros p q; split; intro H.
    destruct H as [H|[r [n H1] H2]].
    exists O; trivial. 
    exists (S n). exists r; trivial.
    destruct H as [[|n] H].
    left; trivial.
    right. destruct H as [r H1 H2]. exists r; trivial. exists n; trivial.
    
    apply <- rel_leq. intros x y [z [n Hn] H2]. 
    revert z Hn H2. induction n; intros z Hn H2.
     compute in Hn. rewrite Hn. trivial.
     destruct Hn as [t H1 H3].
     apply IHn in H1. trivial.
     apply -> rel_leq; eauto.  exists z; trivial. 
  Qed.

  Definition Rel_KleeneAlgebra: KleeneAlgebra := Converse.CKA_KA.  

End Def.


Module Load.

  Existing Instance Rel_Graph.
  Existing Instance Rel_SemiLattice_Ops.
  Existing Instance Rel_Monoid_Ops.
  Existing Instance Rel_Star_Op.
  Existing Instance Rel_Converse_Op.
  Existing Instance Rel_SemiLattice.
  Existing Instance Rel_KleeneAlgebra.
  
  Canonical Structure Rel_Graph.
  
  Transparent equal star plus dot one zero.

End Load.


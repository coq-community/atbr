(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Model of heterogeneous binary relations *)

From ATBR Require Import Common.
From ATBR Require Import Classes.
From ATBR Require        Converse.
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

  Program Instance rel_Graph: Graph := {
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

  Instance rel_SemiLattice_Ops: SemiLattice_Ops rel_Graph := {
    plus := rel_union;
    zero := rel_empty
  }.

  Instance rel_Monoid_Ops: Monoid_Ops rel_Graph := {
    dot := rel_comp;
    one := rel_id
  }.
  
  Instance rel_Star_Op: Star_Op rel_Graph := { 
    star := rel_star
  }.

  Instance rel_Converse_Op: Converse_Op rel_Graph := { 
    conv := rel_conv
  }.
  
  Transparent equal.

  Instance rel_SemiLattice: SemiLattice rel_Graph.
  Proof.
    constructor; compute; firstorder.
  Qed.

  
  Ltac destruct_ex := repeat match goal with 
                        | H : ex _ |- _ => destruct H 
                        | H : ex2 _ _ |- _ => destruct H
                        | H : ?A \/ ?B |- _ => destruct H 
                        | H : ?A , H' : (forall (x : ?A), _ ) |- _ => specialize (H' H); intuition
                             end.
  
  Instance rel_ConverseSemiRing: ConverseIdemSemiRing rel_Graph.
  Proof.
    constructor; (exact rel_SemiLattice || intros; compute; firstorder).
    destruct_ex; eauto.
    destruct_ex; eauto.
    subst; auto.
  Qed.

  Definition rel_IdemSemiRing: IdemSemiRing rel_Graph := Converse.CISR_ISR.  


  Lemma rel_leq A B: forall (a b: @X (rel_Graph) A B), a<==b <-> forall x y, a x y -> b x y.
  Proof.
    compute. firstorder. 
  Qed.

  Instance rel_ConverseKleeneAlgebra: ConverseKleeneAlgebra rel_Graph.
  Proof.
    constructor; 
      first [ 
        exact rel_ConverseSemiRing |
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

  Definition rel_KleeneAlgebra: KleeneAlgebra rel_Graph := Converse.CKA_KA.  

End Def.


(** Import this module to work with binary relations *)
Module Load.

  #[global] Existing Instance rel_Graph.
  #[global] Existing Instance rel_SemiLattice_Ops.
  #[global] Existing Instance rel_Monoid_Ops.
  #[global] Existing Instance rel_Converse_Op.
  #[global] Existing Instance rel_SemiLattice.
  #[global] Existing Instance rel_Star_Op.
  #[global] Existing Instance rel_KleeneAlgebra.
  
  Canonical Structure rel_Graph.
  
  Transparent equal plus dot one zero star. 

  Ltac fold_relAlg := 
    change rel_equal with (@equal rel_Graph); 
      change rel_id with (@one rel_Graph rel_Monoid_Ops);
        change rel_comp with (@dot rel_Graph rel_Monoid_Ops);
          change rel_union with (@plus rel_Graph rel_SemiLattice_Ops);
            change rel_empty with (@zero rel_Graph rel_SemiLattice_Ops);
              change rel_star with (@star rel_Graph rel_Star_Op).
    
End Load.


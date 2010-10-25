(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Model of homegeneous binary relations, from Coq standard library *)

Require Import Common.
Require Import Classes.
Require        Converse.

Require Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Def.

  Context {A: Type}.

  Definition comp (R S: relation A): relation A := 
    fun i k => exists j, R i j /\ S j k.
  Definition empty: relation A := fun x y => False.

  Program Instance Rel_Graph: Graph := {
    T := unit;
    X n m := relation A;
    equal n m := same_relation A
  }.
  Next Obligation.
    unfold same_relation, inclusion.
    constructor; firstorder. 
  Qed.

  Instance Rel_SemiLattice_Ops: SemiLattice_Ops := {
    plus n m := union A;
    zero n m := empty
  }.

  Instance Rel_Monoid_Ops: Monoid_Ops := {
    dot n m p := comp;
    one n := @eq A
  }.
  
  Instance Rel_Star_Op: Star_Op := { 
    star n := clos_refl_trans A
  }.

  Instance Rel_Converse_Op: Converse_Op := { 
    conv n m := transp A
  }.
  
  Transparent equal.

  Instance Rel_SemiLattice: SemiLattice.
  Proof. constructor; compute; firstorder. Qed.

  
  Ltac destruct_ex := 
    repeat 
      match goal with 
        | H : ex _ |- _ => destruct H 
        | H : ex2 _ _ |- _ => destruct H
        | H : ?A \/ ?B |- _ => destruct H 
        | H : ?A , H' : (forall (x : ?A), _ ) |- _ => 
          specialize (H' H); intuition
      end.
  
  Instance Rel_ConverseSemiRing: ConverseIdemSemiRing.
  Proof.
    constructor; (exact Rel_SemiLattice || intros; compute; firstorder).
    destruct_ex; eauto.
    destruct_ex; eauto.
    subst; auto.
  Qed.

  Definition Rel_IdemSemiRing: IdemSemiRing := Converse.CISR_ISR.  


  Lemma rel_leq n m: forall (a b: @X Rel_Graph n m), 
    a<==b <-> forall x y, a x y -> b x y.
  Proof. compute. firstorder. Qed.

  Instance Rel_ConverseKleeneAlgebra: ConverseKleeneAlgebra.
  Proof.
    constructor; 
      first [ 
        exact Rel_ConverseSemiRing |
        intros
      ].
    split; compute; intros x y H.
     destruct H as [->|[j [? ?]]].
      constructor 2.
      econstructor 3.
       eassumption.
       constructor; assumption.
     rewrite rtn1_trans_equiv in H.
     inversion_clear H; auto.
      right. eexists; split; eauto. rewrite rtn1_trans_equiv. assumption.
     
     rewrite rel_leq in *.
      intros x y [z [Hxz Hzy]]. 
      compute in Hxz. rewrite rtn1_trans_equiv in Hxz.
      induction Hxz; trivial.
       apply IHHxz. apply H. eexists; eauto.
  Qed.

  Definition Rel_KleeneAlgebra: KleeneAlgebra := Converse.CKA_KA.  

End Def.


(** Import this module to work with homogeneous binary relations *)
Module Load.

  Existing Instance Rel_Graph.
  Existing Instance Rel_SemiLattice_Ops.
  Existing Instance Rel_Monoid_Ops.
  Existing Instance Rel_Converse_Op.
  Existing Instance Rel_SemiLattice.
  Existing Instance Rel_Star_Op.
  Existing Instance Rel_KleeneAlgebra.
  
  Canonical Structure Rel_Graph.
  
  Transparent equal plus dot one zero star. 

  Ltac fold_RelAlg A := 
    change (same_relation A) with (@equal (@Rel_Graph A) tt tt); 
    change (@eq A) with (@one (@Rel_Graph A) Rel_Monoid_Ops tt);
    change (@comp A) with (@dot (@Rel_Graph A) Rel_Monoid_Ops tt tt tt);
    change (union A) with (@plus (@Rel_Graph A) Rel_SemiLattice_Ops tt tt);
    change (@empty A) with (@zero (@Rel_Graph A) Rel_SemiLattice_Ops tt tt);
    change (clos_refl_trans A) with (@star (@Rel_Graph A) Rel_Star_Op tt).
    
  (*begintests
  Require Import DecideKleeneAlgebra.
  Goal forall A (R S: relation A), same_relation _
    (clos_refl_trans _ (union _ R S))
    (comp (clos_refl_trans _ R) 
      (clos_refl_trans _ (comp S (clos_refl_trans _ R)))).
  Proof.
    intros.
    fold_RelAlg A.
    kleene_reflexivity.
  Qed.
  Print Assumptions Unnamed_thm.
  endtests*)

End Load.


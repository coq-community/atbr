(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Model of homegeneous binary relations, from Coq standard library *)

From ATBR Require Import Common.
From ATBR Require Import Classes.
From ATBR Require Converse.
From Coq Require Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Def.

  Context {A: Type}.

  Definition comp (R S: relation A): relation A := 
    fun i k => exists j, R i j /\ S j k.
  Definition empty: relation A := fun x y => False.

  Program Instance rel_Graph: Graph := {
    T := unit;
    X n m := relation A;
    equal n m := same_relation A
  }.
  Next Obligation.
    unfold same_relation, inclusion.
    constructor; firstorder. 
  Qed.

  Instance rel_SemiLattice_Ops: SemiLattice_Ops rel_Graph := {
    plus n m := union A;
    zero n m := empty
  }.

  Instance rel_Monoid_Ops: Monoid_Ops rel_Graph := {
    dot n m p := comp;
    one n := @eq A
  }.
  
  Instance rel_Star_Op: Star_Op rel_Graph := { 
    star n := clos_refl_trans A
  }.

  Instance rel_Converse_Op: Converse_Op rel_Graph := { 
    conv n m := transp A
  }.
  
  Transparent equal.

  Instance rel_SemiLattice: SemiLattice rel_Graph.
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
  
  Instance rel_ConverseSemiRing: ConverseIdemSemiRing rel_Graph.
  Proof.
    constructor; (exact rel_SemiLattice || intros; compute; firstorder).
    destruct_ex; eauto.
    destruct_ex; eauto.
    subst; auto.
  Qed.

  Definition rel_IdemSemiRing: IdemSemiRing rel_Graph := Converse.CISR_ISR.  


  Lemma rel_leq n m: forall (a b: @X rel_Graph n m), 
    a<==b <-> forall x y, a x y -> b x y.
  Proof. compute. firstorder. Qed.

  Instance rel_ConverseKleeneAlgebra: ConverseKleeneAlgebra rel_Graph.
  Proof.
    constructor; 
      first [ 
        exact rel_ConverseSemiRing |
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

  Definition rel_KleeneAlgebra: KleeneAlgebra rel_Graph := Converse.CKA_KA.  

End Def.


(** Import this module to work with homogeneous binary relations *)
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

  Ltac fold_relAlg A := 
    change (same_relation A) with (@equal (@rel_Graph A) tt tt); 
    change (@eq A) with (@one (@rel_Graph A) rel_Monoid_Ops tt);
    change (@comp A) with (@dot (@rel_Graph A) rel_Monoid_Ops tt tt tt);
    change (union A) with (@plus (@rel_Graph A) rel_SemiLattice_Ops tt tt);
    change (@empty A) with (@zero (@rel_Graph A) rel_SemiLattice_Ops tt tt);
    change (clos_refl_trans A) with (@star (@rel_Graph A) rel_Star_Op tt).
    
  (*begintests
  From ATBR Require Import DecideKleeneAlgebra.
  Goal forall A (R S: relation A), same_relation _
    (clos_refl_trans _ (union _ R S))
    (comp (clos_refl_trans _ R) 
      (clos_refl_trans _ (comp S (clos_refl_trans _ R)))).
  Proof.
    intros.
    fold_relAlg A.
    kleene_reflexivity.
  Qed.
  Print Assumptions Unnamed_thm.
  endtests*)

End Load.


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

Section Protect.

  Instance Prop_Graph: Graph := {
    T := unit;
    X A B := Prop;
    equal A B := iff;
    equal_equivalence A B := iff_equivalence
  }.

  Instance Prop_SemiLattice_Ops: SemiLattice_Ops := {
    plus A B := or;
    zero A B := False
  }.

  Instance Prop_Monoid_Ops: Monoid_Ops := {
    dot A B C := and;
    one A := True
  }.
  
  Instance Prop_Star_Op: Star_Op := { 
    star A x := True 
  }.

  Instance Prop_Converse_Op: Converse_Op := { 
    converse A B x := x
  }.
  
  Instance Prop_SemiLattice: SemiLattice.
  Proof.
    constructor; repeat intro; firstorder.
  Qed.

  Instance Prop_ConverseSemiRing: ConverseIdemSemiRing.
  Proof.
    constructor; (exact Prop_SemiLattice || intros; compute; firstorder).
  Qed.

  Definition Prop_IdemSemiRing: IdemSemiRing := Converse.CISR_ISR.  

  Lemma prop_leq A B: forall (a b: @X (Prop_Graph) A B), a<==b <-> a -> b.
  Proof.
    compute. firstorder. 
  Qed.

  Transparent equal.
  Instance Prop_ConverseKleeneAlgebra: ConverseKleeneAlgebra.
  Proof.
    constructor; 
      first [ 
        exact Prop_ConverseSemiRing |
        compute; tauto
      ].
  Qed.
  Opaque equal.

  Definition Prop_KleeneAlgebra: KleeneAlgebra := Converse.CKA_KA.  

End Protect.


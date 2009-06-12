(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: FreeKleeneAlg.v 875 2009-06-09 11:53:22Z braibant $ i*)

Require Import Common.
Require Import Classes.
Require        SemiLattice.
Require        SemiRing.
Require        KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.

Section Def.

  Instance KAF_Graph: Graph := {
    T := unit;
    X A B := KleeneAlgebra.Free.X;
    equal A B := KleeneAlgebra.Free.equal
  }.
  constructor; repeat intro. apply KleeneAlgebra.Free.equal_refl.
  apply KleeneAlgebra.Free.equal_sym;  trivial.
  eapply KleeneAlgebra.Free.equal_trans. apply H. apply H0.
  Defined.

  Instance KAF_SemiLattice_Ops: SemiLattice_Ops := {
    plus A B := KleeneAlgebra.Free.plus;
    zero A B := KleeneAlgebra.Free.zero
  }.

  Instance KAF_Monoid_Ops: Monoid_Ops := {
    dot A B C := KleeneAlgebra.Free.dot;
    one A := KleeneAlgebra.Free.one
  }.
  
  Instance KAF_Star_Op: Star_Op := { 
    star A x := KleeneAlgebra.Free.star x
  }.
  
  Instance KAF_SemiLattice: SemiLattice.
  Proof.
    constructor; repeat intro; simpl in *;
    constructor; assumption.
  Qed.

  Instance KAF_Monoid: Monoid.
  Proof.
    constructor; repeat intro; simpl in *;
      constructor; assumption.
  Qed.

  Instance KAF_SemiRing: IdemSemiRing.
  Proof.
    apply (Build_IdemSemiRing KAF_Monoid KAF_SemiLattice);
    repeat intro; simpl in *;
      constructor; assumption.
  Qed.

  Instance KAF_KleeneAlgebra: KleeneAlgebra.
  Proof.
    constructor; 
    try exact KAF_SemiRing;
    repeat intro; simpl in *;
      constructor; assumption.
  Qed.

End Def.


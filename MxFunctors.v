(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(* Extension of functors on base structures to functors on matrices *)

Require Import Common.
Require Import Classes.
Require Import Monoid.
Require Import SemiLattice.
Require Import SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiLattice.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.

Require Import Functors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
    
Transparent equal.

Section Defs.
  
  Context {G1: Graph} {G2: Graph}.
  Variable F: functor G1 G2.

  Notation MG1 := (@mx_Graph G1).
  Notation MG2 := (@mx_Graph G2).

  Definition mxF: functor MG1 MG2 :=
    @Build_functor MG1 MG2 
    (fun nA: MT => pair (fst nA) (fT F (snd nA))) 
    (fun nA mB M => box (fst nA) (fst mB) (fun i j => F _ _ (!M i j))).

  Global Instance mxgraph_functor {HF: graph_functor F}: graph_functor mxF.
  Proof.
    constructor. repeat intro. simpl. apply functor_compat. auto.
  Qed.

  Global Instance mxsemilattice_functor 
  {SLo1: SemiLattice_Ops (G:=G1)} {SLo2: SemiLattice_Ops (G:=G2)} 
  {HF: semilattice_functor F}: semilattice_functor mxF. 
  Proof.
    constructor. 
    apply mxgraph_functor.
    simpl. intros. apply functor_plus.
    simpl. intros. apply functor_zero.
  Qed.
  
  Global Instance mxsemiring_functor 
  `{SL1: SemiLattice (G:=G1)} `{SL2: SemiLattice (G:=G2)} 
  {Mo1: Monoid_Ops (G:=G1)} {Mo2: Monoid_Ops (G:=G2)} 
  {HF: semiring_functor F}: semiring_functor mxF.
  Proof.
    constructor. constructor.

     apply mxgraph_functor.
 
     simpl. intros. destruct B as [m B]; simpl fst in *; simpl snd in *.
     rewrite functor_sum. apply sum_compat. intros. apply functor_dot. 

     simpl. intros. BoolView.nat_analyse.
     apply functor_one. apply functor_zero.

     apply mxsemilattice_functor.
  Qed.

  Lemma functor_mx_blocks: 
    forall A B x y n m a b c d, 
      mxF _ _ (@mx_blocks _ A B x y n m a b c d) == 
      mx_blocks (mxF _ _ a) (mxF _ _ b) (mxF _ _ c) (mxF _ _ d).
  Proof. 
    simpl. intros. destruct_blocks; reflexivity. 
  Qed.

  Lemma functor_mx_sub: 
    forall A B n' m' x y n m M, 
      mxF _ _ (@mx_sub _ A B n' m' x y n m M) =
      mx_sub x y n m (mxF _ _ M).
  Proof. reflexivity. Qed.

  Lemma functor_mx_of_scal: 
    forall A B a, 
      mxF _ _ (@mx_of_scal _ A B a) =
      mx_of_scal (F _ _ a).
  Proof. reflexivity. Qed.

  Lemma functor_mx_to_scal: 
    forall A B M, 
      F _ _ (@mx_to_scal _ A B M) =
      mx_to_scal (mxF _ _ M).
  Proof. reflexivity. Qed.

  Global Instance mxkleene_functor 
  `{KA1: KleeneAlgebra (G:=G1)} `{KA2: KleeneAlgebra (G:=G2)} 
  {HF: kleene_functor F}: kleene_functor mxF.
  Proof.
    constructor. 
     apply mxsemiring_functor.

     destruct A as [n A]; unfold fst, snd in *.
     induction n; intro a.
     intros i j Hi; inversion Hi.

     unfold star, mx_Star_Op in *.
     unfold fst, snd.
     unfold star_rec at 1. fold (star_rec (A:=A) (n:=n)). unfold star_build.

     change (S n) with (1+n)%nat.
     rewrite functor_mx_blocks.
     rewrite functor_plus. 
     rewrite !functor_dot.
     rewrite !functor_mx_of_scal.
     rewrite functor_star.
     rewrite functor_mx_to_scal. 
     rewrite functor_plus. 
     rewrite functor_dot.
     do 4 rewrite functor_dot at 1.
     do 9 rewrite IHn at 1.
     unfold mx_sub00, mx_sub01, mx_sub10, mx_sub11.
     rewrite !functor_mx_sub. reflexivity.
   Qed.
  
End Defs.


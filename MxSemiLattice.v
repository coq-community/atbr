(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: MxSemiLattice.v 875 2009-06-09 11:53:22Z braibant $ i*)

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import MxGraph.
Require Import SemiLattice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Transparent equal.

Section Defs.

  Context `{SLo: SemiLattice_Ops}.

  Global Instance mx_SemiLattice_Ops: @SemiLattice_Ops mx_Graph := {
    plus nA mB M N := box (fst nA) (fst mB) (fun i j => !M i j + !N i j);
    zero nA mB := box (fst nA) (fst mB) (fun i j => 0)
  }.

  Context {SL: SemiLattice}.

  Global Instance mx_SemiLattice: @SemiLattice mx_Graph mx_SemiLattice_Ops.
  Proof. constructor; repeat intro; simpl in *; auto with algebra. Qed.

End Defs.

Notation Mplus := (@plus mx_Graph _) (only parsing).
Notation Mzero := (@zero mx_Graph _) (only parsing).
Notation Mleq := (@leq mx_Graph _) (only parsing).
Notation "M <== [ n , m ]  N" := (Mleq (n,_) (m,_) M N) (at level 80).

Section Props.

  Context `{SL: SemiLattice}.

  Lemma addMat_blocks A B x y n m:
    forall M M' N N' P P' Q Q',
      makeMat_blocks M N P Q
      +
      makeMat_blocks M' N' P' Q'
      ==
      @makeMat_blocks _ A B x y n m (M+M') (N+N') (P+P') (Q+Q').
  Proof.
    simpl. intros. destruct_blocks; reflexivity.
  Qed.

  Global Instance makeMat_blocks_incr A B x y n m:
  Morphism (
    (Mleq (x,A) (y,B))   ==>
    (Mleq (x,A) (m,B))  ==>
    (Mleq (n,A) (y,B))  ==>
    (Mleq (n,A) (m,B)) ==>
    (Mleq ((x+n)%nat,A) ((y+m)%nat,B)))
  (@makeMat_blocks G A B x y n m).
  Proof.  
    unfold Morphism, respectful, leq; intros.
    rewrite addMat_blocks.
    apply makeMat_blocks_compat; assumption.
  Qed.


  Lemma zero_makeMat_blocks A B x y n m: 
    0 == @makeMat_blocks _ A B x y n m 0 0 0 0.
  Proof.  
    simpl. intros. destruct_blocks; destruct_nat_dec; reflexivity.
  Qed.

  Lemma scal_to_Mat_compat_plus A B (a b: X A B):
    scal_to_Mat a + scal_to_Mat b == scal_to_Mat (a+b).
  Proof. repeat intro; reflexivity. Qed.

  Lemma subMat_add: forall A B x y n m n' m' (M N: MX(n',A)(m',B)), 
    subMat x y n m (M+N) = subMat x y n m M + subMat x y n m N.
  Proof. reflexivity. Qed.


  Lemma Mat_to_scal_compat_plus A B (a b : MX (1,A)%nat (1,B)%nat) : Mat_to_scal a + Mat_to_scal b == Mat_to_scal (a+b).
  Proof.
    repeat intro. unfold Mat_to_scal, fst in *. trivial.
  Qed.


  (* TODO passer ca dans MxSemiLattice *)
  Lemma rw_sum_wrt_blocks low up n m p q A B 
    (a : nat -> MX (n,A) (p,B)) 
    (b : nat -> MX (n,A) (q,B)) 
    (c : nat -> MX (m,A) (p,B))
    (d : nat -> MX (m,A) (q,B)): 
    sum  low up (fun u => makeMat_blocks (a u) (b u) (c u) (d u)) ==
    makeMat_blocks (sum low up a) (sum low up b)(sum low up c)(sum low up d) .
  Proof.
    intros.
    induction up.
    repeat intro; unfold fst , makeMat_blocks in *. simpl. destruct_blocks; reflexivity.   
    
    setoid_rewrite SemiLattice.sum_enter_right. rewrite IHup. setoid_rewrite  addMat_blocks.
    auto with compat.
  Qed.
  (*
  Lemma mx_column_leq: forall n m A B (M N: MX (n,A) (m,B)),
    (forall j, j < m -> subMat 0 j n 1 M <== subMat 0 j n 1 N) <-> M <== N.
  Proof.
    intros; unfold leq.
    setoid_rewrite <- subMat_add.
    apply mx_column_equal.
  Qed.
  *)

  Lemma mx_blocks_leq: forall A B x y n m (a a': MX(x,A)(y,B)) b b' c c' (d d': MX(n,A)(m,B)), 
    makeMat_blocks a b c d <== makeMat_blocks a' b' c' d' ->
    a<==a' /\ b<==b' /\ c<==c' /\ d<==d'.
  Proof.
    unfold leq. intros. apply mx_blocks_equal. 
    rewrite <- addMat_blocks. assumption.
  Qed.

End Props.


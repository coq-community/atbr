(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Properties of matrices over a semilattice (in particular, they form a semilattice)  *)

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import MxGraph.
Require Import SemiLattice.
Require Import BoolView.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Transparent equal.

Section Defs.

  Context `{SL: SemiLattice}.

  Global Instance mx_SemiLattice_Ops: @SemiLattice_Ops mx_Graph := {
    plus nA mB M N := box (fst nA) (fst mB) (fun i j => !M i j + !N i j);
    zero nA mB := box (fst nA) (fst mB) (fun i j => 0)
  }.

  Definition mx_point A B n m i j (x: X A B) : MX n m A B :=
    box n m (fun i' j' => xif (eq_nat_bool i i' && eq_nat_bool j j') x 0).

  Global Instance mx_SemiLattice: @SemiLattice mx_Graph mx_SemiLattice_Ops.
  Proof. constructor; repeat intro; simpl in *; auto with algebra. Qed.

End Defs.

Notation mx_plus := (@plus mx_Graph _) (only parsing).
Notation mx_zero := (@zero mx_Graph _) (only parsing).
Notation mx_leq n m A B := (@leq mx_Graph _ ((n)%nat,A) ((m)%nat,B)) (only parsing).
Notation "M <== [ n , m ]  N" := (mx_leq n m _ _ M N) (at level 80) : A_scope.

Section Props.

  Context `{SL: SemiLattice}.

  Variables A B: T.
  Notation MX n m := (MX n m A B).
  Notation mx_equal n m := (mx_equal n m A B) (only parsing).
  Notation mx_leq n m := (mx_leq n m A B) (only parsing).

  Lemma mx_blocks_plus x y n m:
    forall M M' N N' P P' Q Q',
      mx_blocks M N P Q
      +
      mx_blocks M' N' P' Q'
      ==
      @mx_blocks _ A B x y n m (M+M') (N+N') (P+P') (Q+Q').
  Proof.
    simpl. intros. destruct_blocks; reflexivity.
  Qed.

  Lemma mx_blocks_zero x y n m: 
    0 == @mx_blocks _ A B x y n m 0 0 0 0.
  Proof.  
    simpl. intros. destruct_blocks; reflexivity.
  Qed.

  Global Instance mx_blocks_incr x y n m:
  Proper (
    mx_leq x y ==>
    mx_leq x m ==>
    mx_leq n y ==>
    mx_leq n m ==>
    mx_leq (x+n) (y+m))
  (@mx_blocks G A B x y n m).
  Proof.  
    unfold Proper, respectful, leq; intros.
    rewrite mx_blocks_plus.
    auto with compat.
  Qed.

  Lemma mx_sub_plus x y n m n' m': forall M N: MX n' m', 
    mx_sub x y n m M + mx_sub x y n m N == mx_sub x y n m (M+N).
  Proof. reflexivity. Qed.

  Lemma mx_of_scal_plus: forall a b: X A B,
    mx_of_scal a + mx_of_scal b == mx_of_scal (a+b).
  Proof. reflexivity. Qed.

  Lemma mx_of_scal_zero: 0 == mx_of_scal (0: X A B).
  Proof. reflexivity. Qed.

  Lemma mx_to_scal_plus: forall a b: MX 1 1,
    mx_to_scal a + mx_to_scal b == mx_to_scal (a+b).
  Proof. reflexivity. Qed.

  Lemma mx_to_scal_zero: (0: X A B) == mx_to_scal 0.
  Proof. reflexivity. Qed.


  Lemma mx_blocks_sum low up n m p q 
    (a : nat -> MX n p) 
    (b : nat -> MX n q) 
    (c : nat -> MX m p)
    (d : nat -> MX m q): 
    sum low up (fun u => mx_blocks (a u) (b u) (c u) (d u)) ==
    mx_blocks (sum low up a) (sum low up b)(sum low up c)(sum low up d) .
  Proof.
    intros.
    induction up.
     simpl. intros. destruct_blocks; reflexivity.   
     setoid_rewrite sum_enter_right. rewrite IHup. setoid_rewrite mx_blocks_plus. auto with compat.
  Qed.

  Lemma mx_blocks_leq x y n m: forall (a a': MX x y) b b' c c' (d d': MX n m), 
    mx_blocks a b c d <== mx_blocks a' b' c' d' ->
    a<==a' /\ b<==b' /\ c<==c' /\ d<==d'.
  Proof.
    unfold leq. intros. apply mx_blocks_equal. 
    rewrite <- mx_blocks_plus. assumption.
  Qed.


  (* matrices with a single non-zero value *)

  Lemma mx_point_zero: forall n m i j, 0 == mx_point n m i j (0: X A B).
  Proof. 
    simpl; intros. nat_analyse; reflexivity. 
  Qed.

  Lemma mx_point_plus: forall n m i j (a b: X A B), mx_point n m i j a + mx_point n m i j b == mx_point n m i j (a+b).
  Proof.
    simpl; intros. nat_analyse; trivial with algebra. 
  Qed.

  Lemma mx_point_scal: forall (a: X A B), mx_point 1 1 0 0 a == mx_of_scal a.
  Proof.
    intro. mx_intros i j Hi Hj. reflexivity.
  Qed.

  Lemma mx_point_blocks00 n m x y: forall i j (a: X A B), i<n -> j<m ->
    mx_point (n+x) (m+y) i j a == mx_blocks (mx_point n m i j a) 0 0 0.
  Proof.
    simpl; intros. destruct_blocks; nat_analyse; trivial.
  Qed.

  Lemma mx_point_blocks01 n m x y: forall i j (a: X A B), i<n -> m<=j ->
    mx_point (n+x) (m+y) i j a == mx_blocks 0 (mx_point n y i (j-m) a) 0 0.
  Proof.
    simpl; intros. destruct_blocks; nat_analyse; trivial.
  Qed.

  Lemma mx_point_blocks10 n m x y: forall i j (a: X A B), n<=i -> j<m ->
    mx_point (n+x) (m+y) i j a == mx_blocks 0 0 (mx_point x m (i-n) j a) 0.
  Proof.
    simpl; intros. destruct_blocks; nat_analyse; trivial. 
  Qed.

  Lemma mx_point_blocks11 n m x y: forall i j (a: X A B), n<=i -> m<=j ->
    mx_point (n+x) (m+y) i j a == mx_blocks 0 0 0 (mx_point x y (i-n) (j-m) a).
  Proof.
    simpl; intros. destruct_blocks; nat_analyse; trivial.
  Qed.

  Global Instance mx_point_compat n m i j: 
  Proper (equal A B ==> mx_equal n m) (mx_point n m i j).
  Proof. 
    repeat intro. simpl. nat_analyse; trivial. 
  Qed.

End Props.

Hint Extern 1 (mx_equal _ _ _ _ _ _) => apply mx_point_compat: compat algebra.


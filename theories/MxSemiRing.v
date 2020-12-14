(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Properties of matrices over a semiring (in particular, they form a semiring)  *)

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import Monoid.
Require Import SemiLattice.
Require Import SemiRing.
Require Import MxGraph.
Require Import MxSemiLattice.
Require Import BoolView.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Transparent equal.

Section Defs.

  Context `{ISR: IdemSemiRing}.
  Variable A: T.
  Notation MX n m := (MX_ A n m).
  Notation mx_equal n m := (mx_equal_ A n m) (only parsing).

  Definition mx_dot n m p (M: MX n m) (N: MX m p): MX n p := 
    box n p (fun i j => sum 0 m (fun k => !M i k * !N k j)).
  Definition mx_one n: MX n n := 
    box n n (fun i j => if eq_nat_bool i j then 1 else 0).

  Global Instance mx_Monoid_Ops: Monoid_Ops (mx_Graph A) := {
    dot := mx_dot;
    one := mx_one }.

  Definition mx_bool n m (f: nat -> nat -> bool): MX n m :=
    box n m (fun i j => xif (f i j) 1 0).

  Lemma mx_dot_assoc n m p o (M: MX n m) (N: MX m p) (P: MX p o): M*(N*P) == (M*N)*P.
  Proof.
    intros i j Hi Hj. simpl.
    transitivity (sum 0 m (fun k => sum 0 p (fun k' => !M i k * !N k k' * !P k' j))).
     apply sum_compat; intros. 
     rewrite sum_distr_right; auto with algebra.

     rewrite sum_inversion.
     apply sum_compat; intros. 
     rewrite sum_distr_left; auto with algebra.
  Qed.

  Lemma mx_dot_neutral_left n m (M: MX n m): 1 * M == M.
  Proof.
    intros i j Hi Hj. simpl.
    rewrite (sum_cut_nth i)  by auto with arith; simpl.
    transitivity (0 + !M i j + 0); [|semiring_reflexivity].
    repeat apply plus_compat; try (apply sum_zero; intros);
      nat_analyse; semiring_reflexivity.
  Qed.
  
  Lemma mx_dot_neutral_right n m (M: MX m n): M * 1 == M.
  Proof.
    intros i j Hi Hj. simpl. 
    rewrite (sum_cut_nth j) by auto with arith; simpl.
    transitivity (0 + !M i j + 0); [|semiring_reflexivity].
    repeat apply plus_compat; try (apply sum_zero; intros); 
      nat_analyse; semiring_reflexivity.
  Qed.
  
  Global Program Instance mx_Monoid: Monoid (mx_Graph A) := {
    dot_assoc := mx_dot_assoc;
    dot_neutral_left := mx_dot_neutral_left;
    dot_neutral_right := mx_dot_neutral_right
  }. 
  Obligation 1. repeat intro. simpl. auto with compat. Qed.
  
  Global Instance mx_SemiRing: IdemSemiRing (mx_Graph A).
  Proof.
    constructor; repeat intro; simpl.
    exact mx_Monoid.
    apply mx_SemiLattice.
    apply sum_zero; auto with algebra. 
    apply sum_zero; auto with algebra. 
    rewrite <- sum_cut_fun; auto with algebra.
    rewrite <- sum_cut_fun; auto with algebra.
  Qed.

End Defs.

Notation mx_dot_ A := (@dot (mx_Graph A) (mx_Monoid_Ops A)) (only parsing).
Notation mx_one_ A := (@one (mx_Graph A) (mx_Monoid_Ops A)) (only parsing).

(*begintests
Section tac_tests.
  Context `{ISR: IdemSemiRing}.
  Variable A: T.
  Notation MX n m := (MX_ A n m).
  Variable x y z: X A A.
  Variables n m p: nat.
  Variables M N P : MX n m.
  Variables Q R : MX m p.

  Goal x*(z+y+z) == x*z+x*y.
    semiring_reflexivity.
  Qed.

  Goal x*(z+y+z) <== x*z+x*y.
    semiring_reflexivity.
  Qed.

  Goal x+y == z -> y+z+x == z.
    intro H.
    ac_rewrite H.
    apply plus_idem.
  Qed.

  Goal M+(N+M*1) == N+M.
    semiring_reflexivity.
  Qed.

  Goal M*Q+(N+M*1)*Q <== (N+M)*Q.
    semiring_reflexivity. 
  Qed.

  Goal N+M == P -> N+P+M == P.
    intro H.
    ac_rewrite H.
    apply plus_idem. 
  Qed.

  Goal M*0 == N*Q.
    rewrite dot_ann_right.
  Abort.

  Goal M*0+0*N == 0+0.
    autorewrite with simpl.
    reflexivity.
  Qed.

End tac_tests.
endtests*)

Section Props1.

  Context `{M: Monoid}.
  Variable A: T.
  Notation MX n m := (MX_ A n m).
  Notation mx_equal n m := (mx_equal_ A n m) (only parsing).

  Definition dot_scal_right n m (M: MX n m) (v: X A A): MX n m := 
    box n m (fun i j => !M i j * v).

  Definition dot_scal_left n m (v: X A A) (M: MX n m): MX n m := 
    box n m (fun i j => v * !M i j).

  Global Instance dot_scal_right_compat n m:
  Proper (mx_equal n m ==> equal A A  ==> mx_equal n m) (@dot_scal_right n m).
  Proof. repeat intro. simpl. auto with compat. Qed.
  
  Global Instance dot_scal_left_compat n m:
  Proper (equal A A ==> mx_equal n m ==> mx_equal n m) (@dot_scal_left n m).
  Proof. repeat intro. simpl. auto with compat. Qed.

End Props1.

Infix "'*" := dot_scal_left (at level 40): A_scope.
Infix "*'" := dot_scal_right (at level 40): A_scope.



Global Hint Extern 2 (mx_equal_ _ _ _ _ _) => apply dot_scal_left_compat: compat algebra.
Global Hint Extern 2 (mx_equal_ _ _ _ _ _) => apply dot_scal_right_compat: compat algebra.

Section Props2.

  Context `{ISR: IdemSemiRing}.
  Variable A: T.
  Notation MX n m := (MX_ A n m).
  Notation mx_equal n m := (mx_equal_ A n m) (only parsing).

  Lemma mx_blocks_dot n m n' m' p p': forall
    (a : MX n  m )
    (b : MX n  m')
    (c : MX n' m )
    (d : MX n' m')
    (a': MX m  p )
    (b': MX m  p')
    (c': MX m' p )
    (d': MX m' p'),
    mx_blocks a  b  c  d * mx_blocks a' b' c' d'
    == mx_blocks  
    (a * a' + b * c')  
    (a * b' + b * d')
    (c * a' + d * c') 
    (c * b' + d * d').
  Proof.
    simpl. intros. destruct_blocks.
  
    rewrite (plus_comm m), sum_cut. 
    apply plus_compat.
    apply sum_compat; intros. 
    destruct_blocks. reflexivity. lia_false.
    rewrite (plus_comm m), sum_shift. 
    apply sum_compat; intros.
    destruct_blocks. reflexivity.

    rewrite (plus_comm m), sum_cut. 
    apply plus_compat.
    apply sum_compat; intros. 
    destruct_blocks. reflexivity. lia_false.
    rewrite (plus_comm m), sum_shift. 
    apply sum_compat; intros.
    destruct_blocks. reflexivity.

    rewrite (plus_comm m), sum_cut. 
    apply plus_compat.
    apply sum_compat; intros. 
    destruct_blocks. reflexivity. lia_false.
    rewrite (plus_comm m), sum_shift. 
    apply sum_compat; intros.
    destruct_blocks. reflexivity.

    rewrite (plus_comm m), sum_cut. 
    apply plus_compat.
    apply sum_compat; intros. 
    destruct_blocks. reflexivity. lia_false.
    rewrite (plus_comm m), sum_shift. 
    apply sum_compat; intros.
    destruct_blocks. reflexivity.
  Qed.

  Lemma mx_blocks_one x n : 
    1 == @mx_blocks _ A x x n n 1 0 0 1.
  Proof.  
    simpl. intros. destruct_blocks; nat_analyse; reflexivity.
  Qed.

  Lemma dot_scal_left_is_dot n (M: MX 1 n) x:
    x '* M == mx_of_scal x * M.
  Proof.
    mx_intros i j Hi Hj.  simpl. auto with algebra. 
  Qed.

  Lemma dot_scal_left_one n m (M: MX n m): 1 '* M == M.
  Proof. 
    repeat intro; simpl. trivial with algebra. 
  Qed.

  Lemma dot_scal_left_zero n m x: x '* (0: MX n m) == 0.
    repeat intro; simpl. trivial with algebra. 
  Qed.

  Lemma dot_scal_left_dot n m p (M: MX n m) (P: MX m p) x:
    (x '* M) * P == x '* (M * P).
  Proof.
    repeat intro; simpl.
    rewrite sum_distr_right. apply sum_compat. intros. auto with algebra. 
  Qed.

  Lemma dot_scal_left_blocks n m p q 
    (N: MX n p) 
    (M: MX n q)
    (P: MX m p) 
    (Q: MX m q) x:
    x '* mx_blocks N M P Q
    == mx_blocks (x '* N) (x '* M) (x '* P) (x '* Q).
  Proof.
    repeat intro; simpl. destruct_blocks; reflexivity. 
  Qed.

  Lemma dot_scal_right_is_dot n x (M: MX 1 n):
    x '* M == mx_of_scal x * M.
  Proof.
    mx_intros i j Hi Hj.  simpl. auto with algebra. 
  Qed.
  
  Lemma dot_scal_right_one n m (M: MX n m): M *' 1 == M.
  Proof. 
    repeat intro; simpl. trivial with algebra. 
  Qed.

  Lemma dot_scal_right_zero n m x: (0: MX n m) *' x == 0.
    repeat intro; simpl. trivial with algebra. 
  Qed.

  Lemma dot_scal_right_dot n m p (M: MX n m) (P: MX m p) x:
    M * (P *' x) == (M * P) *' x.
  Proof.
    repeat intro; simpl.
    rewrite sum_distr_left. apply sum_compat. intros. auto with algebra. 
  Qed.

  Lemma dot_scal_right_blocks n m p q 
    (N: MX n p) 
    (M: MX n q)
    (P: MX m p) 
    (Q: MX m q) x:
    mx_blocks N M P Q *' x
    == mx_blocks (N *' x) (M *' x) (P *' x) (Q *' x).
  Proof.
    simpl. intros. destruct_blocks; reflexivity. 
  Qed.

  Lemma mx_of_scal_dot: forall a b: X A A, 
                        mx_of_scal a * mx_of_scal b == mx_of_scal (a*b).
  Proof. 
    repeat intro; simpl. trivial with algebra. 
  Qed.
  
  Lemma mx_of_scal_one: 1 == mx_of_scal (one A).
  Proof.
    intros; mx_intros i j Hi Hj. reflexivity.
  Qed.

  Lemma mx_to_scal_dot: forall a b: MX 1 1,
                        mx_to_scal a * mx_to_scal b == mx_to_scal (a*b).
  Proof.
    unfold mx_to_scal. 
    simpl. intros. auto with algebra. 
  Qed.
  
  Lemma mx_to_scal_one: one A == mx_to_scal 1.
  Proof. reflexivity. Qed.
  

  Lemma mx_point_dot n m o i j k: forall a b: X A A, j < m ->
    mx_point n m i j a * mx_point m o j k b == mx_point n o i k (a*b).
  Proof.
    repeat intro; simpl.
    rewrite (sum_cut_nth j) by assumption.
    rewrite 2sum_zero; intros.
     nat_analyse; simpl; semiring_reflexivity.
     nat_analyse; simpl; trivial with algebra.
     nat_analyse; simpl; trivial with algebra.
  Qed.

  Lemma mx_point_dot_zero n m o i j j' k: forall a b: X A A, j<>j' ->
    mx_point n m i j a * mx_point m o j' k b == 0.
  Proof.
    repeat intro; simpl.
    apply sum_zero. intros.
    nat_analyse; simpl; trivial with algebra.
  Qed.

  Lemma mx_point_one_left n m p i j: forall M: MX m p, j < m -> 
    mx_point n m i j 1 * M == box n p (fun s t =>  xif (eq_nat_bool i s) (!M j t) 0).
  Proof.
    intros.
    unfold mx_point.
    mx_intros s t Hs Ht. simpl. 
    rewrite (sum_cut_nth j) by auto.
    rewrite 2 sum_zero; intros; nat_analyse; simpl; semiring_reflexivity.  
  Qed.

  Lemma mx_point_center n m p q i j (M: MX n m) (N: MX p q): 
    i < m -> j < p -> 
    M * mx_point m p i j 1 * N == box n q (fun s t => !M s i * !N j t).
  Proof.
    intros Hi Hj x y Hx Hy. simpl.
    setoid_rewrite sum_distr_left.

    rewrite (sum_cut_nth j);auto. 
    rewrite sum_zero.
    rewrite (sum_cut_nth i). 
    
    setoid_rewrite sum_zero; intros; simpl; nat_analyse; simpl; try semiring_reflexivity.
    rewrite sum_zero. reflexivity.
    intros. bool_simpl; simpl. semiring_reflexivity.
    auto.
    intros. rewrite sum_zero. reflexivity.
    intros. nat_analyse; simpl; semiring_reflexivity.
  Qed.
    

End Props2.

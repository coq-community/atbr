(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.               *)
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

  Context {G: Graph} {Mo: Monoid_Ops} {SLo: SemiLattice_Ops}.

  Global Instance mx_Monoid_Ops: @Monoid_Ops mx_Graph := {
    dot nA mB pC M N := box (fst nA) (fst pC) (fun i j => sum 0 (fst mB) (fun k => !M i k * !N k j));
    one nA := box (fst nA) (fst nA) (fun i j => if eq_nat_bool i j then 1 else 0)
  }.

  Definition mx_bool A n m (f: nat -> nat -> bool) : MX n m A A :=
    box n m (fun i j => xif (f i j) 1 0).
  
  Context {ISR: IdemSemiRing}.

  Notation MX := (@X (@mx_Graph G)).

  Lemma mx_dot_assoc: forall nA mB pC oD (M: MX nA mB) (N: MX mB pC) (P: MX pC oD), M*(N*P) == (M*N)*P.
  Proof.
    intros [n A] [m B] [p C] [o D]; simpl. intros M N P i j Hi Hj.
    transitivity (sum 0 m (fun k => sum 0 p (fun k' => !M i k * !N k k' * !P k' j))).
     apply sum_compat; intros. 
     rewrite sum_distr_right; auto with algebra.

     rewrite sum_inversion.
     apply sum_compat; intros. 
     rewrite sum_distr_left; auto with algebra.
  Qed.

  Lemma mx_dot_neutral_left: forall nA mB (M: MX nA mB),  1 * M == M.
  Proof.
    intros [n A] [m B] M i j Hi Hj. simpl.
    rewrite (sum_cut_nth i)  by auto with arith; simpl.
    transitivity (0 + !M i j + 0); [|aci_reflexivity].
    repeat apply plus_compat; try (apply sum_zero; intros);
      nat_analyse; semiring_reflexivity.
  Qed.
  
  Lemma mx_dot_neutral_right: forall nA mB (M: MX nA mB),  M * 1 == M.
  Proof.
    intros [n A] [m B] M i j Hi Hj. simpl. 
    rewrite (sum_cut_nth j) by auto with arith; simpl.
    transitivity (0 + !M i j + 0); [|aci_reflexivity].
    repeat apply plus_compat; try (apply sum_zero; intros); 
      nat_analyse; semiring_reflexivity.
  Qed.
  
  Global Instance mx_Monoid: @Monoid mx_Graph mx_Monoid_Ops := {
    dot_assoc := mx_dot_assoc;
    dot_neutral_left := mx_dot_neutral_left;
    dot_neutral_right := mx_dot_neutral_right
  }. 
  Proof. repeat intro. simpl. auto with compat. Qed.
  
  Global Instance mx_SemiRing: @IdemSemiRing mx_Graph mx_Monoid_Ops mx_SemiLattice_Ops.
  Proof.
    constructor; repeat intro; simpl.
    exact mx_Monoid.
    exact mx_SemiLattice.
    apply sum_zero; auto with algebra. 
    apply sum_zero; auto with algebra. 
    rewrite <- sum_cut_fun; auto with algebra.
    rewrite <- sum_cut_fun; auto with algebra.
  Qed.

End Defs.

Notation mx_dot := (@dot mx_Graph _) (only parsing).
Notation mx_one := (@one mx_Graph _) (only parsing).

(*begintests
Section tac_tests.
  Context `{ISR: IdemSemiRing}.

  Variable A: T.
  Variable x y z: X A A.
  Variables nA nB nC: MT.
  Variables M N P : @X mx_Graph nA nB.
  Variables Q R : @X mx_Graph nB nC.

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

  Definition dot_scal_right A B C n m (M: MX n m A B) (v: X B C): MX n m A C := 
    box n m (fun i j => !M i j * v).

  Definition dot_scal_left A B C n m (v: X A B) (M: MX n m B C): MX n m A C := 
    box n m (fun i j => v * !M i j).

  Global Instance dot_scal_right_compat (n m : nat) (A B C: T):
  Proper (mx_equal n m A B ==> equal B C  ==> mx_equal n m A C) (@dot_scal_right A B C n m).
  Proof. repeat intro. simpl. auto with compat. Qed.
  
  Global Instance dot_scal_left_compat (n m : nat) (A B C: T):
  Proper (equal A B ==> mx_equal n m B C ==> mx_equal n m A C) (@dot_scal_left A B C n m).
  Proof. repeat intro. simpl. auto with compat. Qed.

End Props1.

Infix "'*" := dot_scal_left (at level 40): A_scope.
Infix "*'" := dot_scal_right (at level 40): A_scope.



Hint Extern 2 (mx_equal _ _ _ _ _ _) => apply dot_scal_left_compat: compat algebra.
Hint Extern 2 (mx_equal _ _ _ _ _ _) => apply dot_scal_right_compat: compat algebra.

Section Props2.

  Context `{ISR: IdemSemiRing}.

  Lemma mx_blocks_dot A B C n m n' m' p p': forall
    (a : MX n  m  A B)
    (b : MX n  m' A B)
    (c : MX n' m  A B)
    (d : MX n' m' A B)
    (a': MX m  p  B C)
    (b': MX m  p' B C)
    (c': MX m' p  B C)
    (d': MX m' p' B C),
    mx_blocks a  b  c  d * mx_blocks a' b' c' d'
    ==
    mx_blocks  
    (a * a' + b * c')  
    (a * b' + b * d')
    (c * a' + d * c') 
    (c * b' + d * d')
    .
  Proof.
    simpl. intros. destruct_blocks.
  
    rewrite (plus_comm m), sum_cut. 
    apply plus_compat.
    apply sum_compat; intros. 
    destruct_blocks. reflexivity. omega_false.
    rewrite (plus_comm m), sum_shift. 
    apply sum_compat; intros.
    destruct_blocks. reflexivity.

    rewrite (plus_comm m), sum_cut. 
    apply plus_compat.
    apply sum_compat; intros. 
    destruct_blocks. reflexivity. omega_false.
    rewrite (plus_comm m), sum_shift. 
    apply sum_compat; intros.
    destruct_blocks. reflexivity.

    rewrite (plus_comm m), sum_cut. 
    apply plus_compat.
    apply sum_compat; intros. 
    destruct_blocks. reflexivity. omega_false.
    rewrite (plus_comm m), sum_shift. 
    apply sum_compat; intros.
    destruct_blocks. reflexivity.

    rewrite (plus_comm m), sum_cut. 
    apply plus_compat.
    apply sum_compat; intros. 
    destruct_blocks. reflexivity. omega_false.
    rewrite (plus_comm m), sum_shift. 
    apply sum_compat; intros.
    destruct_blocks. reflexivity.
  Qed.

  Lemma mx_blocks_one A x n : 
    1 == @mx_blocks _ A A x x n n 1 0 0 1.
  Proof.  
    simpl. intros. destruct_blocks; nat_analyse; reflexivity.
  Qed.

  Lemma dot_scal_left_is_dot A B C n: forall (M: MX 1 n B C) (x: X A B),
    x '* M == mx_of_scal x * M.
  Proof.
    intros. mx_intros i j Hi Hj.  simpl. auto with algebra. 
  Qed.

  Lemma dot_scal_left_one A B n m: forall (M: MX n m A B), 1 '* M == M.
  Proof. 
    simpl. intros. trivial with algebra. 
  Qed.

  Lemma dot_scal_left_zero A B C n m: forall (x: X A B), x '* (0: MX n m B C) == 0.
    simpl; intros. trivial with algebra. 
  Qed.

  Lemma dot_scal_left_dot A B C D n m p: forall (M: MX n m A B) (P: MX m p B C) (x: X D A),
    (x '* M) * P == x '* (M * P).
  Proof.
    simpl. intros.
    rewrite sum_distr_right. apply sum_compat. intros. auto with algebra. 
  Qed.

  Lemma dot_scal_left_blocks A B C n m p q: forall 
    (N: MX n p A B) 
    (M: MX n q A B)
    (P: MX m p A B) 
    (Q: MX m q A B) (x : X C A),
    x '* mx_blocks N M P Q
    == mx_blocks (x '* N) (x '* M) (x '* P) (x '* Q).
  Proof.
    simpl. intros. destruct_blocks; reflexivity. 
  Qed.

  Lemma dot_scal_right_is_dot A B C n: forall (x: X A B) (M: MX 1 n B C),
    x '* M == mx_of_scal x * M.
  Proof.
    intros. mx_intros i j Hi Hj.  simpl. auto with algebra. 
  Qed.
  
  Lemma dot_scal_right_one: forall A B n m (M: MX n m A B), M *' 1 == M.
  Proof. 
    simpl. intros. trivial with algebra. 
  Qed.

  Lemma dot_scal_right_zero A B C n m: forall (x: X B C), (0: MX n m A B) *' x == 0.
    simpl; intros. trivial with algebra. 
  Qed.

  Lemma dot_scal_right_dot A B C D n m p: forall (M: MX n m A B) (P: MX m p B C) (x: X C D),
    M * (P *' x) == (M * P) *' x.
  Proof.
    simpl. intros.
    rewrite sum_distr_left. apply sum_compat. intros. auto with algebra. 
  Qed.

  Lemma dot_scal_right_blocks A B C n m p q: forall 
    (N: MX n p A B) 
    (M: MX n q A B)
    (P: MX m p A B) 
    (Q: MX m q A B) (x : X B C),
    mx_blocks N M P Q *' x
    == mx_blocks (N *' x) (M *' x) (P *' x) (Q *' x).
  Proof.
    simpl. intros. destruct_blocks; reflexivity. 
  Qed.

  Lemma mx_of_scal_dot A B C: forall (a: X A B) (b: X B C),
    mx_of_scal a * mx_of_scal b == mx_of_scal (a*b).
  Proof. 
    simpl. intros. trivial with algebra. 
  Qed.
  
  Lemma mx_of_scal_one A: 1 == mx_of_scal (1: X A A).
  Proof.
    intros; mx_intros i j Hi Hj. reflexivity.
  Qed.

  Lemma mx_to_scal_dot A B C: forall (a: MX 1 1 A B) (b: MX 1 1 B C),
    mx_to_scal a * mx_to_scal b == mx_to_scal (a*b).
  Proof.
    unfold mx_to_scal. 
    simpl. intros. auto with algebra. 
  Qed.
  
  Lemma mx_to_scal_one A: (1: X A A) == mx_to_scal 1.
  Proof. reflexivity. Qed.
  

  Lemma mx_point_dot A B C n m o i j k: forall (a: X A B) (b: X B C), j < m ->
    mx_point n m i j a * mx_point m o j k b == mx_point n o i k (a*b).
  Proof.
    simpl. intros.
    rewrite (sum_cut_nth j) by assumption.
    rewrite 2sum_zero; intros.
     nat_analyse; simpl; semiring_reflexivity.
     nat_analyse; simpl; trivial with algebra.
     nat_analyse; simpl; trivial with algebra.
  Qed.

  Lemma mx_point_dot_zero A B C n m o i j j' k: forall (a: X A B) (b: X B C), j<>j' ->
    mx_point n m i j a * mx_point m o j' k b == 0.
  Proof.
    simpl. intros.
    apply sum_zero. intros.
    nat_analyse; simpl; trivial with algebra.
  Qed.

  Lemma mx_point_one_left A B n m p i j : forall (M: MX m p A B ),j < m -> 
    mx_point n m i j 1 * M == box n p (fun s t =>  xif (eq_nat_bool i s) (!M j t) 0).
  Proof.
    intros.
    unfold mx_point.
    mx_intros s t Hs Ht. simpl. 
    rewrite (sum_cut_nth j) by auto.
    rewrite 2 sum_zero; intros; nat_analyse; simpl; semiring_reflexivity.  
  Qed.

  Lemma mx_point_center A B C n m p q i j : forall (M : MX n m A B) (N : MX p q B C), 
    i < m -> j < p -> 
    M * mx_point m p i j 1 * N == box n q (fun s t => !M s i * !N j t).
  Proof.
    intros M N Hi Hj; simpl.
    intros x y Hx Hy.
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




(*
Section test_factorisation_par_les_duaux.
  Lemma dot_neutral_left' `{ISR: IdemSemiRing}: forall (nA mB : T) (M : MX nA mB), 1 * M == M.
  Proof.
    intros.
    Set Printing All.
    set (rg := @Graph.Reversed G).
    set (mg := @mx_Graph G).
    set (rmg := @Graph.Reversed mg).
    set (mrg := @mx_Graph rg).
    set (rSLo := @SemiLattice.Reversed_Ops G SLo).
    set (mSLo := @mx_SemiLattice_Ops G SLo).
    set (rmSLo := @SemiLattice.Reversed_Ops mg mSLo).
    set (mrSLo := @mx_SemiLattice_Ops rg rSLo).
    set (rMo := @Monoid.Reversed_Ops G Mo).
    set (mMo := @mx_Monoid_Ops G Mo SLo H).
    set (rmMo := @Monoid.Reversed_Ops mg mMo).
    set (mrMo := @mx_Monoid_Ops rg rMo rSLo _).
    set (rSRo := @SemiRing.Reversed_Ops G Mo SLo H).
    set (mSRo := @mx_SemiRing_Ops G Mo SLo H _ _).
    set (rmSRo := @SemiRing.Reversed_Ops mg mMo mSLo mSRo).
    set (mrSRo := @mx_SemiRing_Ops rg rMo rSLo H _ _).
    set (t := @dot_neutral_right mrg mrMo (@mx_Monoid rg rMo rSLo rSRo (@SemiRing.Reversed G Mo SLo H ISR))).
    set (t' := @dot_neutral_right rmg rmMo (@Monoid.Reversed mg mMo (@ISR_Monoid mg _ _ _ (@mx_SemiRing G Mo SLo H ISR)))).
    exact t'.
    exact t'.


  Variable G: Graph.
  Variable ISRo: SemiRing_Ops G.
  Variable ISR: IdemSemiRing ISRo.

  Lemma dual_dot: forall nA mB pC (M: MX nA mB) (N: MX mB pC),
    M*N == (@dot _ (Monoid.Reversed_Ops _) _ _ _ N M).
  Proof. reflexivity. Qed.

  Lemma dual_one: forall (nA: MT),
    one nA == (@one _ (Monoid.Reversed_Ops _) nA).
  Proof. reflexivity. Qed.

  Lemma dual_equal: forall (nA mB: MT) (M N: MX nA mB),
    equal nA mB M N <-> @equal (Graph.Reversed (mx_Graph G)) mB nA M N.
  Proof. reflexivity. Qed.

  Lemma dot_neutral_left': forall (nA mB : T) (M : MX nA mB), 1 * M == M.
  Proof.
    intros.
    rewrite dual_one, dual_dot, dual_equal.
    try refine (dot_neutral_right (Reversed _) M).
  Abort.
End test_factorisation_par_les_duaux.
*)

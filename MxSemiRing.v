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
Require Import Graph.
Require Import Monoid.
Require Import SemiLattice.
Require Import ATBR.SemiRing.
Require Import MxGraph.
Require Import MxSemiLattice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Transparent equal.

Section Defs.

  Context {G: Graph} {Mo: Monoid_Ops} {SLo: SemiLattice_Ops}.

  Global Instance mx_Monoid_Ops: @Monoid_Ops mx_Graph := {
    dot nA mB pC M N := box (fst nA) (fst pC) (fun i j => sum 0 (fst mB) (fun k => !M i k * !N k j));
    one nA := box (fst nA) (fst nA) (fun i j => if eq_nat_dec i j then 1 else 0)
  }.
  
  Context {ISR: IdemSemiRing}.

  Lemma mx_dot_assoc A B C D (M: MX A B) (N: MX B C) (P: MX C D) : M*(N*P) == (M*N)*P.
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
      destruct_nat_dec; semiring_reflexivity.
  Qed.
  
  Lemma mx_dot_neutral_right: forall nA mB (M: MX nA mB),  M * 1 == M.
  Proof.
    intros [n A] [m B] M i j Hi Hj. simpl. 
    rewrite (sum_cut_nth j) by auto with arith; simpl.
    transitivity (0 + !M i j + 0); [|aci_reflexivity].
    repeat apply plus_compat; try (apply sum_zero; intros); 
      destruct_nat_dec; semiring_reflexivity.
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

Notation Mdot := (@dot mx_Graph _) (only parsing).
Notation Mone := (@one mx_Graph _) (only parsing).

(*begintests
Section tac_tests.
  Context `{ISR: IdemSemiRing}.

  Variable A: T.
  Variable x y z: X A A.
  Variables nA nB nC: MT.
  Variables M N P : MX nA nB.
  Variables Q R : MX nB nC.

  Goal x*(z+y+z) == x*z+x*y.
    semiring_reflexivity.
  Qed.

  Goal x*(z+y+z) <== x*z+x*y.
    semiring_reflexivity.
  Qed.
(* ac_rewrite ne marche plus...
  Goal x+y == z -> y+z+x == z.
    intro H.
    ac_rewrite H.
    apply plus_idem.
  Qed.
*)
  Goal M+(N+M*1) == N+M.
    semiring_reflexivity.
  Qed.

  Goal M*Q+(N+M*1)*Q <== (N+M)*Q.
    semiring_reflexivity. 
  Qed.
(*
  Goal N+M == P -> N+P+M == P.
    intro H.
    ac_rewrite H.
    apply plus_idem. 
  Qed.
*)
  Goal M*0 == N*Q.
    rewrite dot_ann_right.
  Abort.

  Goal M*0+0*N == 0+Mzero _ _.
    autorewrite with simpl.
    reflexivity.
    (* c'est bizarre qu'il n'y arrive pas... *)
(*     Print HintDb typeclass_instances. *)
    apply @mx_SemiLattice; eapply @ISR_SemiLattice; trivial.
  Qed.

End tac_tests.
endtests*)

Section Props1.

  Context `{Mo: Monoid_Ops}.

  Definition dot_scal_right A B C n m 
    (M: MX(n,A)(m,B)) (v: X B C): MX(n,A)(m,C) := 
    box n m (fun i j => !M i j * v).

  Definition dot_scal_left A B C n m 
    (v: X A B) (M: MX(n,B)(m,C)): MX(n,A)(m,C) := 
    box n m (fun i j => v * !M i j).

  Context {M: Monoid}.

  Global Instance dot_scal_right_compat (n m : nat) (A B C: T):
  Morphism ((Mequal(n,A)(m,B)) ==> (equal B C)  ==> (Mequal(n,A)(m,C))) (@dot_scal_right A B C n m).
  Proof. repeat intro. simpl. auto with compat. Qed.
  
  Global Instance dot_scal_left_compat (n m : nat) (A B C: T):
  Morphism ((equal A B) ==> (Mequal(n,B)(m,C)) ==> (Mequal(n,A)(m,C))) (@dot_scal_left A B C n m).
  Proof. repeat intro. simpl. auto with compat. Qed.

End Props1.


(* Hint Resolve  *)
(*   @dot_scal_left_compat @dot_scal_right_compat *)
(*   : compat algebra. *)

Hint Extern 2 (Mequal _ _ _ _) => apply dot_scal_left_compat: compat algebra.
Hint Extern 2 (Mequal _ _ _ _) => apply dot_scal_right_compat: compat algebra.

Section Props2.

  Context `{ISR: IdemSemiRing}.

  Lemma Mat_blocks_dot A B C n m n' m' p p'
    (a: MX(n, A) (m, B))
    (b: MX(n, A) (m', B))
    (c: MX(n', A) (m, B))
    (d: MX(n', A) (m', B))
    
    (a': MX(m, B) (p, C))
    (b': MX(m, B) (p', C))
    (c': MX(m', B) (p, C))
    (d': MX(m', B) (p', C))
    :	
    (makeMat_blocks a  b  c  d) *
    (makeMat_blocks a' b' c' d')
    ==
    makeMat_blocks  
    (a * a' + b * c')  
    (a * b' + b * d')
    (c * a' + d * c') 
    (c * b' + d * d')
    .
  Proof.
    simpl. intros. destruct_blocks.
  
    (* et au niveau des symetries, kek ca dit ? *)
  
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

  Lemma one_makeMat_blocks A x n : 
    1 == @makeMat_blocks _ A A x x n n 1 0 0 1.
  Proof.  
    simpl. intros. destruct_blocks; destruct_nat_dec; reflexivity.
  Qed.

  (*
  Lemma one_makeMat_blocks_S A n : 
    1 == @makeMat_blocks _ A A 1 1 n n (scal_to_Mat 1) 0 0 1.
  Proof.  
    repeat intro; simpl. unfold makeMat_blocks, scal_to_Mat.
    destruct_blocks; destruct_nat_dec; reflexivity.
  Qed.
  *)

  Lemma dot_scal_right_is_dot A B C n (M: MX (n,A) (1%nat,B)) (x: X B C):
    dot_scal_right M x == M * scal_to_Mat x.
  Proof.
    simpl. intros. rewrite plus_neutral_right; auto with compat omega.
  Qed.
  
  Lemma dot_scal_left_is_dot A B C n (M: MX(1%nat,B) (n,C)) (x: X A B):
    dot_scal_left x M == scal_to_Mat x * M.
  Proof.
    simpl. intros. rewrite plus_neutral_right; auto with compat omega.
  Qed.

  Lemma dot_scal_left_one: forall A B n m (M: MX (n,A) (m,B)), dot_scal_left 1 M == M.
  Proof. 
    simpl. intros. trivial with algebra. 
  Qed.

  Lemma dot_scal_left_zero A B C n m (x : X A B) : dot_scal_left x (0 : MX (n,B) (m,C)) == 0.
    unfold dot_scal_left; simpl; intros; semiring_reflexivity.
  Qed.

  Lemma dot_scal_left_compat_dot A B C D n m p  (M :MX (n,A) (m,B)) (P : MX (m,B) (p,C)) (x : X D A) : 
    (dot_scal_left x M )* P == dot_scal_left x (M * P).
  Proof.
    unfold dot_scal_left.
    repeat intro. simpl.
    rewrite sum_distr_right. apply sum_compat. intros. semiring_reflexivity.
  Qed.
  
  Lemma dot_scal_left_compat_dot_r01 A B  n m p  (M :MX (n,A) (m,A)) (P : MX (m,A) (p,B)) (x : X A A) : 
    (forall i j, i < n -> j < m -> ((!M i j == 0) \/ (!M i j == 1))) ->
    M *(dot_scal_left x P ) == dot_scal_left x (M * P).
  Proof.
    repeat intro; unfold fst, snd in *; simpl.
    rewrite sum_distr_right; apply sum_compat; intros.
    destruct (H i (0+n0)%nat); 
      ( omega || (rewrite H3; semiring_reflexivity)).
  Qed.

  Lemma dot_scal_right_one: forall A B n m (M: MX (n,A) (m,B)), dot_scal_right M 1 == M.
  Proof. 
    simpl. intros. trivial with algebra. 
  Qed.
  
  Lemma scal_to_Mat_compat_dot A B C (a: X A B) (b: X B C): 
    scal_to_Mat a * scal_to_Mat b == scal_to_Mat (a*b).
  Proof. 
    simpl. intros. trivial with algebra. 
  Qed.
  
  Lemma scal_to_Mat_one A: 1 == @scal_to_Mat G A A 1.
  Proof. 
    simpl. intros. destruct_nat_dec; reflexivity. 
  Qed.

  Lemma Mat_to_scal_compat_dot A B C a b :
    (Mat_to_scal a : X A B)* (Mat_to_scal b : X B C) == Mat_to_scal (a*b).
  Proof.
    unfold Mat_to_scal. 
    simpl. intros. semiring_reflexivity. 
  Qed.
  
 (*  Lemma Mat_to_scal_zero : Mat_to_scal (0 : KMX (1%nat,1%nat)) == 0. *)
  Lemma Mat_to_scal_zero A B : Mat_to_scal (0 : MX (1%nat,A) (1%nat,B)) == 0.
  Proof.
    intros;  unfold Mat_to_scal.  reflexivity.
  Qed.


  Lemma dot_scal_left_compat_blocks A B C n m p q 
    (N :  MX (n,A) (p,B)) (M : MX (n,A) (q,B))
    (P :  MX (m,A) (p,B)) (Q : MX (m,A) (q,B)) (x : X C A) :
    (dot_scal_left x (makeMat_blocks N M P Q) ) == makeMat_blocks (dot_scal_left x N) (dot_scal_left x M)(dot_scal_left x P)(dot_scal_left x Q).
  Proof.
    repeat intro. unfold dot_scal_left, makeMat_blocks. simpl. destruct_blocks; reflexivity. 
  Qed.

  (*
  Lemma subMat_dot_column: forall A B n m j (M: MX(n,A)(n,A)) (Y: MX(n,A)(m,B)), 
    subMat 0 j n 1 (M * Y) = M * subMat 0 j n 1 Y.
  Proof. reflexivity. Qed.

  Lemma line_dot_subMat: forall A B n m i (Y: MX(m,B)(n,A)) (M: MX(n,A)(n,A)) , 
    subMat i 0 1 n (Y * M) = subMat i 0 1 n Y * M.
  Proof. reflexivity. Qed.
  *)

  Definition base_line k n A : MX (1%nat, A) (n,A) := box 1 n (fun _ j => if eq_nat_dec j k then 1 else 0).

  Lemma base_line_equiv n m A B (M N : MX (n,A) (m,B)) : (forall k , k < n -> base_line k n A * M == base_line k n A * N) <-> M == N.
  Proof.
    split; repeat intro.
    assert (H' := H i H0 0%nat j). unfold base_line in H'. simpl in H'.  
    transitivity (0 + !M i j + 0); [aci_reflexivity |]. 
    transitivity (0 + !N i j + 0); [| aci_reflexivity].
    eapply equal_trans; [| eapply equal_trans].   Focus 2. apply H'. auto. auto. 
    
    rewrite (sum_cut_nth i); auto.
    repeat apply plus_compat; first [symmetry ; apply sum_zero; intros; destruct_nat_dec; auto with algebra | destruct_nat_dec; auto with algebra].

    rewrite (sum_cut_nth i); auto.
    repeat apply plus_compat; first [ apply sum_zero; intros; destruct_nat_dec; auto with algebra | destruct_nat_dec; auto with algebra].

    (* autre sens *)
    unfold base_line. simpl.
    unfold fst, snd in *.
    
    (* BUG : on ne peut pas faire le at 2 sans faire le symmetry *)
    rewrite (sum_cut_nth k) at 1; auto. symmetry.
    rewrite (sum_cut_nth k); auto. symmetry.
    unfold fst, snd in *. 
    repeat (apply plus_compat).
    apply sum_compat; intros; destruct_nat_dec; simpl. apply dot_compat; [ auto |  apply H;  unfold fst in *; omega]. 
    destruct_nat_dec. apply dot_compat; [ auto |  apply H;  unfold fst in *; omega]. 
    apply sum_compat; intros; destruct_nat_dec; simpl. apply dot_compat; [ auto |  apply H;  unfold fst in *; omega]. 
  Qed.

  Lemma dirac_ligne n m A B  (M : MX (n,A) (m,B)) (Q : MX (1%nat,A) (n,A)) s:
    s < n -> !Q O s == 1 -> (forall i, i <> s -> !Q O i == 0) -> 
    Q * M == box 1 m (fun _ j => !M s j).
  Proof.
    intros n m A B M Q s H Hs Hi.
    repeat intro. simpl. 
   
    destruct i; [| omega_false].
    rewrite (sum_cut_nth s) by auto. simpl. rewrite Hs.
    transitivity (0 + !M s j + 0); [|aci_reflexivity].
    repeat apply plus_compat. 
     apply sum_zero; intros. rewrite Hi by auto. semiring_reflexivity. 
     monoid_reflexivity.
     apply sum_zero; intros. rewrite Hi by omega. semiring_reflexivity.
  Qed.      

  Lemma dirac_column n m A B  (M : MX (n,A) (m,B)) (Q : MX (m,B) (1%nat,B)) s:
    s < m -> !Q s 0%nat == 1 -> (forall i, i <> s -> !Q i 0%nat == 0) -> 
    M * Q == box n 1 (fun i _ => !M i s).
  Proof.
    intros n m A B M Q s H Hs Hi.
    repeat intro. simpl. 
   
    destruct j; [| omega_false].
    rewrite (sum_cut_nth s) by auto. simpl. rewrite Hs.
    transitivity (0 + !M i s + 0); [|aci_reflexivity].
    repeat apply plus_compat. 
     apply sum_zero; intros. rewrite Hi by auto. semiring_reflexivity. 
     monoid_reflexivity.
     apply sum_zero; intros. rewrite Hi by omega. semiring_reflexivity.
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

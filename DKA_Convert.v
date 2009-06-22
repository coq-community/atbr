(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

Require Import Common.
Require Import Classes.
Require Import SemiLattice.
Require Import ATBR.SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.
Require Import BoolAlg.
Require Import FreeKleeneAlg.
Require Import Functors MxFunctors.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Notation "'BMX' ( n , m )" :=  (@X (@mx_Graph bool_Graph) ((n :nat), tt) ((m :nat), tt) ) (at level 0). 
Notation "'KMX' ( n , m )" :=  (@X (@mx_Graph KAF_Graph) ((n :nat), tt) ((m :nat) , tt) ) (at level 0). 
Notation KAF := (@X KAF_Graph tt tt). 

Section Protect.

  Existing Instance bool_SemiLattice_Ops. 
  Existing Instance bool_Monoid_Ops.
  Existing Instance bool_Star_Op.
  Existing Instance bool_SemiLattice.
  Existing Instance bool_Monoid.
  Existing Instance bool_SemiRing.
  Existing Instance bool_KleeneAlgebra.
  
  Existing Instance KAF_SemiLattice_Ops. 
  Existing Instance KAF_Monoid_Ops.
  Existing Instance KAF_Star_Op.
  Existing Instance KAF_SemiLattice.
  Existing Instance KAF_Monoid.
  Existing Instance KAF_SemiRing.
  Existing Instance KAF_KleeneAlgebra.

  Definition var i : KAF := Free.var i.

  Definition convert n m: BMX(n,m) -> KMX(n,m) := mxF convert (n,tt) (m,tt).

  Definition convert_sum n k (f: nat -> BMX(n,n)) := 
    SemiLattice.sum 0 k (fun i => dot_scal_left (var i) (convert (f i))).
    
  Global Instance convert_compat (n m : nat):
  Morphism (
    (@equal (@mx_Graph bool_Graph) (n,tt) (m,tt))   ==>
    (@equal (@mx_Graph KAF_Graph)  (n,tt) (m,tt)))
  (@convert n m).
  Proof.
    intros. apply (functor_compat (F:=mxF (BoolAlg.convert (G:=KAF_Graph) (t:=tt))) (A:=(n,tt)) (B:=(m,tt))).
  Qed.

  Lemma convert_blocks : forall n m p q ( a : BMX (n,p)) (b : BMX (n,q)) (c : BMX (m,p)) (d: BMX(m,q)) , 
    convert (makeMat_blocks a b c d) == makeMat_blocks (convert a) (convert b) (convert c) (convert d).
  Proof.
    intros. refine (functor_makeMat_blocks (F:=BoolAlg.convert) _ _ _ _).
  Qed. 
  
  Lemma convert_plus n m (a b : BMX(n,m)) : convert (a + b) == convert a + convert b. 
  Proof.
    intros. apply (functor_plus (F:=mxF (BoolAlg.convert (G:=KAF_Graph) (t:=tt))) a b).
  Qed.
  
  Lemma convert_dot n m p (a : BMX(n,m))  (b : BMX(m,p)): convert (a * b) == convert a * convert b.
    intros. apply (functor_dot (F:=mxF (BoolAlg.convert (G:=KAF_Graph) (t:=tt))) a b).
  Qed.
  
  Lemma convert_star n (a : BMX (n,n)): convert (a#) == (convert a) #.
  Proof.
    intros. apply (functor_star (F:=mxF (BoolAlg.convert (G:=KAF_Graph) (t:=tt))) a).
  Qed.
  
  Lemma convert_zero n m : convert (0 : BMX (n,m)) == 0.
  Proof. 
    intros. apply (functor_zero (F:=mxF (BoolAlg.convert (G:=KAF_Graph) (t:=tt))) (n,tt) (m,tt)).
  Qed.
  
  Lemma convert_one n : convert (1 : BMX (n,n)) == 1.
  Proof. 
    intros. apply (functor_one (F:=mxF (BoolAlg.convert (G:=KAF_Graph) (t:=tt))) (n,tt)).
  Qed.

  
  Lemma convert_sum_compat n (M N: nat -> BMX(n,n)) k:
    (forall i, i<k -> M i == N i) -> convert_sum k M == convert_sum k N.
  Proof. 
    intros.
    unfold convert_sum.
    induction k.
      unfold sum. semiring_reflexivity.
      
      rewrite 2 sum_enter_right.  
(* rewrite dot_distr_left, dot_distr_right. rewrite IHk; auto. *)
      apply plus_compat. apply IHk; intuition.
      apply dot_scal_left_compat. reflexivity.
      apply convert_compat.  auto.
  Qed.

  (* (nouveau) lemme joli de thomas *)
  Lemma convert_sum_commute n m (M : nat -> BMX (n,n)) (M' : nat -> BMX (m,m)) X k : 
    (forall x, (x < k -> (M x) * X == X * (M' x))) -> 
    (convert_sum k M) * convert X == convert X * (convert_sum k M').
  Proof.
    intros.
    unfold convert_sum.
    induction k.
      unfold sum. semiring_reflexivity.
      
      rewrite 2 sum_enter_right.  rewrite dot_distr_left, dot_distr_right. rewrite IHk; auto.
      apply plus_compat;[reflexivity|].
      rewrite (dot_scal_left_compat_dot (G := KAF_Graph)).
      rewrite <- convert_dot. rewrite H; auto with arith.
    
      rewrite (dot_scal_left_compat_dot_r01 (G := KAF_Graph)). rewrite convert_dot. reflexivity.
    
      intros. unfold convert. compute. destruct X. destruct (x i j). right; apply Free.equal_refl. 
      left; constructor.
  Qed.

(*  
  (* ancien lemme joli de thomas *)
  Lemma old_convert_sum_commute n m (M : nat -> BMX (n,n)) (M' : nat -> BMX (m,m)) X k : 
    (forall x, (x < k -> (M x) * X == X * (M' x))) -> 
    (convert_sum k M)# * convert X == convert X * (convert_sum k M')#.
  Proof.
    intros.
    assert (convert_sum k M * convert X == convert X * convert_sum k M').
    unfold convert_sum.
    induction k.
      unfold sum. semiring_reflexivity.
      
      rewrite 2 sum_enter_right.  rewrite dot_distr_left, dot_distr_right. rewrite IHk; auto.
      apply plus_compat;[reflexivity|].
      rewrite (dot_scal_left_compat_dot (G := KAF_Graph)).
      rewrite <- convert_dot. rewrite H; auto with arith.
    
      rewrite (dot_scal_left_compat_dot_r01 (G := KAF_Graph)). rewrite convert_dot. reflexivity.
    
      intros. unfold convert. compute. destruct X. destruct (x i j). right; apply Free.equal_refl. 
      left; constructor.
    
    (* BUG *)
    assert ((convert_sum k M )#* convert X == convert X * (convert_sum k M')#).
    apply (comm_iter_left). assumption.
    apply H1.
  Qed.
*)

End Protect.


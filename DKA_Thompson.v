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
Require Import SemiLattice.
Require Import Monoid.
Require Import ATBR.SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiLattice.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.
Require Import BoolAlg.
Require Import FreeKleeneAlg.

Require Import DKA_Annexe.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Section Protect.

  Opaque equal dot plus one zero star.

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



  (* reprise de la construction de Thompson, à plus haut niveau *)

  Definition MPlus (A B: MAut) : MAut := @Build_MAut (A.(M_size) + B.(M_size))
    (makeMat_blocks A.(M_M) 0 0 B.(M_M))
    (makeMat_blocks A.(M_U) B.(M_U) 0 0)
    (makeMat_blocks A.(M_V) 0 B.(M_V) 0).

  Definition MDot (A B: MAut) : MAut := @Build_MAut (A.(M_size) + B.(M_size))
    (makeMat_blocks A.(M_M) (A.(M_V) * B.(M_U)) 0 B.(M_M))
    (makeMat_blocks A.(M_U) 0 0       0)
    (makeMat_blocks 0       0 B.(M_V) 0).

  Definition MpStar(A : MAut) : MAut := @Build_MAut A.(M_size)
    (A.(M_M) + A.(M_V) * A.(M_U))
    A.(M_U) 
    A.(M_V).

  Definition MVar (a : nat): MAut := @Build_MAut 2
    (makeMat_blocks (x:=1) (y:=1) 0 (scal_to_Mat (var a)) 0 0)
    (makeMat_blocks (x:=1) (y:=1) 1 0 0 0)
    (makeMat_blocks (x:=1) (y:=1) 0 0 1 0).

  Definition MZero : MAut := @Build_MAut 0 0 0 0.
 
  Definition MOne : MAut := @Build_MAut 1 1 1 1.

  Fixpoint X_to_MAut (x : Free.X) : MAut :=
    match x with 
      | Free.one => MOne
      | Free.zero => MZero
      | Free.dot x y => MDot (X_to_MAut x) (X_to_MAut y)
      | Free.plus x y => MPlus (X_to_MAut x) (X_to_MAut y)
      | Free.star x => MPlus MOne (MpStar (X_to_MAut x)) 
      | Free.var i => MVar i
    end.


  (* on montre dans le reste de ce fichier que la construction precedente 
     correspond bien a celle de DKA_Algo. 
     *)


  (* les automates construits (par DKA_Algo) sont bien formés *)
  Lemma X_to_bAut_wf a: bAut_wf (X_to_bAut a).
  Proof.
    induction a; intros b Hb; simpl in *; trivial.
    
    rewrite (IHa1 b), (IHa2 b) by eauto using le_trans, Max.le_max_r, Max.le_max_l.
    symmetry. apply (zero_makeMat_blocks (G:=bool_Graph)).

    rewrite (IHa1 b), (IHa2 b) by eauto using le_trans, Max.le_max_r, Max.le_max_l.
    symmetry. apply (zero_makeMat_blocks (G:=bool_Graph)).
    
    rewrite (IHa b) by assumption. 
    change (S (b_size (X_to_bAut a))) with (1+b_size (X_to_bAut a))%nat.
    symmetry. apply (zero_makeMat_blocks (G:=bool_Graph)).

    destruct_nat_dec. 
    symmetry. simpl. change 2 with (1+1)%nat.
    rewrite (zero_makeMat_blocks (G:=bool_Graph)) at 1.
    refine (makeMat_blocks_compat _ _ _ _); reflexivity.
  Qed.
  Local Hint Resolve X_to_bAut_wf.


  Instance MPlus_compat: Proper (MAut_eq ==> MAut_eq ==> MAut_eq) MPlus.
  Proof.
    intros A A' HA B B' HB. destruct HA. destruct HB.
    constructor; simpl; change (S O) with (1+0)%nat; apply (makeMat_blocks_compat (G:=KAF_Graph)); trivial. 
  Qed.

  Instance MDot_compat: Proper (MAut_eq ==> MAut_eq ==> MAut_eq) MDot.
  Proof.
    intros A A' HA B B' HB. destruct HA. destruct HB.
    constructor; simpl; change (S O) with (1+0)%nat; apply (makeMat_blocks_compat (G:=KAF_Graph)); auto with compat. 
  Qed.

  Instance MpStar_copmat: Proper (MAut_eq ==> MAut_eq) MpStar.
  Proof.
    intros A A' HA. destruct HA. 
    constructor; simpl; auto with compat.
  Qed.
  

  Lemma max_plus: forall n m, (Max.max n m = (Max.max n m - n) + n)%nat.
  Proof. intros. pose proof (Max.le_max_l n m). omega. Qed.

  Lemma truncate_sum A B: bAut_wf A \/ b_max_label A = b_max_label B -> 
   sum 0 (Max.max (b_max_label A) (b_max_label B))
     (fun u : nat => dot_scal_left (var u) (convert (b_M A u))) == 
   sum 0 (b_max_label A)
     (fun i : nat => dot_scal_left (var i) (convert (b_M A i))).
  Proof.
    intros.
    rewrite max_plus. rewrite sum_cut. rewrite plus_com. rewrite sum_zero. trivial with algebra. 
    intros n Hn. 
    destruct H.
     rewrite (H (b_max_label A+0+n)%nat) by omega. 
     rewrite convert_zero. apply (dot_scal_left_zero (G:=KAF_Graph)).
     rewrite H, Max.max_r in Hn; trivial. omega_false.
  Qed.

  (* on montre que les constructions se correspondent deux a deux *)

  Lemma bMDot A B: bAut_wf A -> bAut_wf B ->
    MAut_eq 
      (bAut_to_MAut (bDot A B))
      (MDot (bAut_to_MAut A) (bAut_to_MAut B)).
  Proof.
    intros. constructor; simpl.

    unfold convert_sum. setoid_rewrite convert_blocks. setoid_rewrite convert_zero.
    setoid_rewrite dot_scal_left_compat_blocks.
    rewrite rw_sum_wrt_blocks. rewrite (addMat_blocks (G:=KAF_Graph)).
    setoid_rewrite sum_zero at 2 3.
    apply (makeMat_blocks_compat (G:=KAF_Graph));
      try apply (plus_compat (G:=@mx_Graph KAF_Graph)); trivial with algebra.
    apply truncate_sum; auto.
    rewrite convert_dot. trivial with algebra. 
    rewrite Max.max_comm. apply truncate_sum; auto. 
    intros; apply (dot_scal_left_zero (G:=KAF_Graph)).
    intros; apply (dot_scal_left_zero (G:=KAF_Graph)).

    change (S O) with (1+O)%nat. rewrite convert_blocks.
    setoid_rewrite convert_zero. reflexivity.
    
    change (S O) with (1+O)%nat. rewrite convert_blocks.
    setoid_rewrite convert_zero. reflexivity.
  Qed.

  (* ce lemme est réutilisé dans DecideKleeneAlgebra, pour merge_DFAs_Maut, 
     d'où son type un peu tordu *)
  Lemma bMPlus A B: (bAut_wf A /\ bAut_wf B) \/ b_max_label A = b_max_label B ->
    MAut_eq 
      (bAut_to_MAut (bPlus A B))
      (MPlus (bAut_to_MAut A) (bAut_to_MAut B)).
  Proof.
    intros. constructor; simpl.

    unfold convert_sum. setoid_rewrite convert_blocks. setoid_rewrite convert_zero.
    setoid_rewrite dot_scal_left_compat_blocks.
    rewrite rw_sum_wrt_blocks. rewrite (addMat_blocks (G:=KAF_Graph)).
    setoid_rewrite sum_zero at 2 3.
    apply (makeMat_blocks_compat (G:=KAF_Graph)); 
      try apply (plus_compat (G:=@mx_Graph KAF_Graph)); trivial with algebra.
    apply truncate_sum; intuition.
    rewrite Max.max_comm. apply truncate_sum; intuition.
    intros; apply (dot_scal_left_zero (G:=KAF_Graph)).
    intros; apply (dot_scal_left_zero (G:=KAF_Graph)).

    change (S O) with (1+O)%nat. rewrite convert_blocks.
    setoid_rewrite convert_zero. reflexivity.
    
    change (S O) with (1+O)%nat. rewrite convert_blocks.
    setoid_rewrite convert_zero. reflexivity.    
  Qed.

  Lemma bMpStar A: bAut_wf A -> 
    MAut_eq 
      (bAut_to_MAut (bpStar A))
      (MpStar (bAut_to_MAut A)).
  Proof.
    intros. constructor; simpl; trivial.
    rewrite convert_plus, convert_dot. aci_reflexivity.
  Qed.

  Lemma bMOne: MAut_eq (bAut_to_MAut bOne) MOne.
  Proof.
    constructor; simpl; rewrite convert_one; trivial with algebra.
  Qed.

  Lemma bMZero: MAut_eq (bAut_to_MAut bZero) MZero.
  Proof.
    constructor; simpl; rewrite convert_zero; trivial with algebra.
  Qed.

  Lemma bMVar a: MAut_eq (bAut_to_MAut (bVar a)) (MVar a).
  Proof.
    constructor; simpl; change 2%nat with (1+1)%nat.
     unfold convert_sum.
     setoid_rewrite convert_blocks. setoid_rewrite convert_zero.
     rewrite sum_enter_right. rewrite sum_zero. rewrite dot_scal_left_compat_blocks. rewrite 2 plus_neutral_left.
     refine (makeMat_blocks_compat _ _ _ _); try apply (dot_scal_left_zero (G:=KAF_Graph)).
     rewrite dot_scal_left_is_dot. rewrite <- (dot_neutral_right (scal_to_Mat (var a))).
     apply dot_compat; trivial. Transparent equal. intros [|] [|] Hi Hj; try omega_false. Opaque equal.
     simpl. destruct_nat_dec. compute. reflexivity. 
     intros m Hm. simpl. destruct_nat_dec. simpl. rewrite convert_zero.
     rewrite <- (zero_makeMat_blocks (G:=KAF_Graph)). apply (dot_scal_left_zero (G:=KAF_Graph)).
     
     change 1%nat with (1+0)%nat. rewrite convert_blocks, convert_one, !convert_zero. reflexivity.
     change 1%nat with (1+0)%nat. rewrite convert_blocks, convert_one, !convert_zero. reflexivity.  
  Qed.


  (* ca permet de conclure *)

  Lemma X_to_bMAut: forall a,
    MAut_eq (bAut_to_MAut (X_to_bAut a)) (X_to_MAut a).
  Proof.
    induction a; simpl.
    apply bMOne.
    apply bMZero.
    rewrite bMDot by trivial. rewrite IHa1, IHa2. reflexivity.
    rewrite bMPlus by auto. rewrite IHa1, IHa2. reflexivity.
    rewrite bMPlus, bMOne, bMpStar; trivial. rewrite IHa. reflexivity.
     left; split; intros b Hb; trivial. simpl. apply X_to_bAut_wf. trivial. 
    apply bMVar.
  Qed.

  Lemma eval_bM: forall a,
    eval_b (X_to_bAut a) == eval_M (X_to_MAut a).
  Proof.
    intro. apply eval_M_compat.
    apply X_to_bMAut.
  Qed.
(*   Print Assumptions Compute_MCompute. *)

End Protect.

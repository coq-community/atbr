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
Require Import SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiLattice.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.
Require Import BoolAlg.
Require Import FreeKleeneAlg.
Require        Force.

Require Import DKA_Annexe.
Require Import DKA_Thompson.
Require        DKA_Determinisation.
Require        DKA_Minimisation.

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

  Notation NFA_to_DFA := (NFA_to_DFA DKA_Determinisation.Termination).
  Notation   X_to_DFA := (  X_to_DFA DKA_Determinisation.Termination).


  (* correction de la construction haut niveau de Thompson *)


  Lemma eval_Plus: forall A B, eval_M (MPlus A B) == eval_M A + eval_M B.
  Proof.
    intros [na Ma Ua Va] [nb Mb Ub Vb]. unfold eval_M. simpl.
    rewrite (star_diagonal_blocks (G:=KAF_Graph)).
    change (S O) with (1+0)%nat.
    rewrite ! (Mat_blocks_dot (G:=KAF_Graph)).
    rewrite makeMat_blocks_degenerate_00.
    semiring_reflexivity. 
  Qed.

  Lemma eval_Dot: forall A B, eval_M (MDot A B) == eval_M A * eval_M B.
  Proof.
    intros [na Ma Ua Va] [nb Mb Ub Vb]. unfold eval_M. simpl.
    rewrite (star_trigonal_blocks (G:=KAF_Graph)).
    change (S O) with (1+0)%nat.
    rewrite ! (Mat_blocks_dot (G:=KAF_Graph)).
    rewrite makeMat_blocks_degenerate_00.
    semiring_reflexivity. 
  Qed.

  Lemma eval_pStar: forall A, eval_M (MpStar A) == eval_M A * eval_M A#.
  Proof.
    intros [na Ma Ua Va]. unfold eval_M. simpl.
    rewrite star_distr.
    rewrite <- 3 dot_assoc.
    rewrite move_star2.
    monoid_reflexivity.
  Qed.

  Lemma eval_Var: forall a, eval_M (MVar a) == scal_to_Mat (var a).
  Proof.
    intro a. unfold eval_M. simpl.
    change 2%nat with (1+1)%nat.
    rewrite (star_trigonal_blocks (G:=KAF_Graph)).
    change 1%nat with (1+0)%nat.
    rewrite ! (Mat_blocks_dot (G:=KAF_Graph)).
    rewrite makeMat_blocks_degenerate_00.
    rewrite star_zero.
    semiring_reflexivity.
  Qed.

  Lemma eval_One: eval_M MOne == scal_to_Mat 1.
  Proof.
    unfold eval_M. simpl.
    rewrite star_one.
    rewrite <- scal_to_Mat_one.
    monoid_reflexivity.
  Qed.

  Lemma eval_Zero: eval_M MZero == scal_to_Mat 0.
  Proof.
    unfold eval_M. simpl.
    rewrite dot_ann_right.
    reflexivity.
  Qed.
    
  Lemma eval_X_to_MAut: forall (a: KAF), eval_M (X_to_MAut a) == scal_to_Mat a.
  Proof.
    induction a.
    apply eval_One.
    apply eval_Zero.
    simpl. rewrite eval_Dot. rewrite IHa1, IHa2. refine (scal_to_Mat_compat_dot _ _); auto with typeclass_instances.
    simpl. rewrite eval_Plus. rewrite IHa1, IHa2. reflexivity. 
    simpl. 
     rewrite eval_Plus, eval_One, eval_pStar.  
     rewrite <- scal_to_Mat_one. rewrite star_make_right. 
     rewrite IHa. symmetry. refine (scal_to_Mat_compat_star _).  auto with typeclass_instances.
    simpl. apply eval_Var.
  Qed.

  Theorem eval_X_to_bAut: forall (a: KAF), eval_b (X_to_bAut a) == scal_to_Mat a.
  Proof.
    intro a. rewrite eval_bM. apply eval_X_to_MAut.
  Qed.
  



  (* correction du retrait des epsilon-transitions *)

  Definition epsilon_free' A : bAut := 
    let Js := b_J A # in 
      @Build_bAut (b_size A)                
      0
      (fun i => b_M A i * Js)
      (b_U A * Js)  
      (b_V A)
      (b_max_label A).

  (* todo: on ne gagne pas tant par ce detour... *)
  Lemma epsilon_epsilon': forall A, eval_b (epsilon_free A) == eval_b (epsilon_free' A).
  Proof.
    intros [a J M U V k]. unfold eval_b, eval_M, bAut_to_MAut; simpl.
    repeat apply dot_compat; trivial.
    rewrite mx_force_id. rewrite mxbool_dot_dot. rewrite mx_force_id. rewrite mxbool_star_star. reflexivity.
    apply star_compat, plus_compat; trivial.
    apply sum_compat. intros n H.
    refine (dot_scal_left_compat _ _); auto with typeclass_instances.  
    rewrite Force.id_id by assumption. 
    rewrite mxbool_dot_dot. rewrite mx_force_id. rewrite mxbool_star_star. reflexivity.
  Qed.

  Theorem eval_epsilon_free: forall A, eval_b (epsilon_free A) == eval_b A.
  Proof.
    setoid_rewrite epsilon_epsilon'.
    intros [a J M U V k]. unfold eval_b, eval_M, bAut_to_MAut; simpl.
    rewrite convert_zero. rewrite plus_neutral_left.
    rewrite star_distr. rewrite dot_assoc.
    repeat apply dot_compat; trivial.
    rewrite convert_dot, convert_star. reflexivity.
    apply star_compat. unfold convert_sum.
    rewrite sum_distr_left. apply sum_compat. intros. rewrite (dot_scal_left_compat_dot (G := KAF_Graph)).
    refine (dot_scal_left_compat _ _); auto with typeclass_instances.  
    rewrite convert_dot, convert_star. reflexivity.
  Qed.




  (* traduction automate matriciel epsilon-free -> NFA *)

  Lemma eval_bAut_to_NFA: forall A, b_J A == 0 -> eval_N (bAut_to_NFA A) == eval_b A.
  Proof.
    intros [n J M U V k] HJ. unfold bAut_to_NFA, eval_N, NFA_to_bAut. simpl.
    apply eval_b_compat. constructor; auto.
    
    Transparent equal. intros b Hb i j Hi Hj. Opaque equal. 
    simpl. rewrite Force.id2_id by assumption.
    simpl. rewrite mem_set_of_ones; auto.

    Transparent equal. intros [|] j Hi Hj. Opaque equal. simpl. rewrite mem_set_of_ones; auto. omega_false. 
    Transparent equal. intros i [|] Hi Hj. Opaque equal. simpl. rewrite (mem_set_of_ones (fun j => !(V) j O)); auto. omega_false.
  Qed.




  (* Bonne formation et correction des DFAs construits à partir d'une expression *)

  Lemma X_to_DFA_wf: forall (a: KAF), DFA_wf (X_to_DFA a).
  Proof.
    intros. apply DKA_Determinisation.well_formed.
  Qed.

  Theorem eval_X_to_DFA: forall (a: KAF), eval_D (X_to_DFA a) == scal_to_Mat a.
  Proof.
    intros. unfold DKA_Algo.X_to_DFA.
    rewrite DKA_Determinisation.eval.
    rewrite eval_bAut_to_NFA by trivial.
    rewrite eval_epsilon_free.
    apply eval_X_to_bAut.
  Qed.




  (* Assemblage et correction finale, par l'automate mergé *)

  Lemma merge_DFAs_lt_first (a b : DFA) :DFA_wf a -> D_initial  a < D_size (merge_DFAs a b).
  Proof.
    intros.  unfold merge_DFAs. simpl. unfold DFA_wf in H. intuition omega.
  Qed.

  Lemma merge_DFAs_lt_second a b : DFA_wf a -> DFA_wf b -> D_size a + D_initial b < D_size (merge_DFAs a b).
  Proof.
    intros a b Ha Hb.  unfold merge_DFAs. simpl. unfold DFA_wf in Ha, Hb. intuition omega.
  Qed.

  Lemma merge_DFAs_M A B u: DFA_wf A -> D_max_label A = D_max_label B ->
    MAut_eq 
      (DFA_to_MAut (change_initial_D (merge_DFAs A B) u))
      (change_initial_M (MPlus (DFA_to_MAut A) (DFA_to_MAut B)) u).
  Proof.
    intros.
    unfold DFA_to_MAut at -1.
    rewrite <- bMPlus by auto.
    rewrite change_initial_Mb.
    apply bAut_MAut_eq.
    apply merge_DFAs_b; assumption.
  Qed.

  Lemma change_initial_first A B: DFA_wf A ->
    MAut_eq
      (change_initial_M (MPlus (DFA_to_MAut A) B) (D_initial A))
      (MPlus (DFA_to_MAut A) (empty_initial_M B)).
  Proof.
    intros A B (HAi&HAf&HAd). constructor; trivial.
    Transparent equal. intros [|] j Hi Hj; try omega_false. Opaque equal.
    simpl. destruct_nat_dec; destruct_blocks; simpl; trivial; try discriminate.
    omega_false.
  Qed.

  Lemma merge_first A B: D_max_label A = D_max_label B -> DFA_wf A -> 
    eval_D (change_initial_D (merge_DFAs A B) (D_initial A)) == eval_D A.
  Proof.
    intros A B HB HA. unfold eval_D, eval_b.
    fold (DFA_to_MAut (change_initial_D (merge_DFAs A B) (D_initial A))).
    rewrite merge_DFAs_M by trivial.
    generalize (DFA_to_MAut B); clear HB B; intro B.
    rewrite change_initial_first; trivial.
    rewrite eval_Plus.
    rewrite eval_empty_initial. trivial with algebra.
  Qed.

  Lemma change_initial_second A B:
    MAut_eq
      (change_initial_M (MPlus A (DFA_to_MAut B)) (M_size A + D_initial B))
      (MPlus (empty_initial_M A) (DFA_to_MAut B)).
  Proof.
    intros. constructor; trivial.
    Transparent equal. intros [|] j Hi Hj; try omega_false. Opaque equal.
    simpl. destruct_blocks; destruct_nat_dec; trivial. 
  Qed.

  Lemma merge_second A B: D_max_label A = D_max_label B -> DFA_wf A ->
    eval_D (change_initial_D (merge_DFAs A B) (D_size A + D_initial B)) == eval_D B.
  Proof.
    intros A B HB HA. unfold eval_D, eval_b.
    fold (DFA_to_MAut (change_initial_D (merge_DFAs A B) (D_size A + D_initial B))).
    rewrite merge_DFAs_M by trivial.
    change (D_size A) with (M_size (DFA_to_MAut A)).
    generalize (DFA_to_MAut A); clear HA HB A; intro A.
    rewrite change_initial_second; trivial.
    rewrite eval_Plus.
    rewrite eval_empty_initial. trivial with algebra.
  Qed.


  Theorem Kozen: forall (a b: KAF), decide_Kleene DKA_Determinisation.Termination DKA_Minimisation.Termination a b = true -> a == b.
  Proof.
    unfold decide_Kleene. intros.

    set (n := (D_max_label (X_to_DFA a))) in *. 
    set (m := (D_max_label (X_to_DFA b))) in *.
    destruct (eq_nat_dec n m). simpl in H.
    (* BUG a reporter: le admit est lent *)
    (*  admit. *)
    2: discriminate.
    
    pose proof (X_to_DFA_wf a) as HA.
    pose proof (X_to_DFA_wf b) as HB. 

    apply Meq_to_eq. 
    rewrite <- 2 eval_X_to_DFA. 
    rewrite <- (merge_first _ e HA). 
    rewrite <- (merge_second _ e HA). 
    apply DKA_Minimisation.correct; auto using   merge_DFAs_lt_first , merge_DFAs_lt_second.

    apply merge_DFAs_wf; trivial. 
  Qed.

(*   Print Assumptions Kozen. *)

End Protect.


Ltac kleene_reflexivity := abstract
  let G := get_Graph in
    Quote.quote (KleeneAlgebra.FreeEval.Quote (G:=G)) (KleeneAlgebra.FreeEval.eval_equal (G:=G));
      apply Kozen; vm_compute; (reflexivity || fail "Not a Kleene Algebra theorem").

(*begintests

Section test.

  Context `{KA: KleeneAlgebra}.

  Goal forall A B (a: X A B) (b: X B A), a*(b*a)# == (a*b)#*a.
    intros.
    kleene_reflexivity.
  Qed.

  Goal forall A B (a: X A B) (b: X B A), a*(b*a) == (a*b)#*a .
    intros.
    try kleene_reflexivity.
    idtac.                      (* s'il n'y a plus de sous-but, c'est que kleene_reflexivity a foiré *)
  Abort.

End test.

endtests*)

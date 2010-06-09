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
Require Import Graph.
Require Import Monoid.
Require Import SemiLattice.
Require Import ATBR.SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiLattice.
Require Import MxSemiRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Transparent equal.

Section Defs.

  Context {G: Graph} {Mo: Monoid_Ops} {SLo: SemiLattice_Ops} {Ko: Star_Op}.

  (* notations pour accélérer les typeclasses *)
  Notation MG := (@mx_Graph G).
  Notation MX := (@X MG).
  Notation X := (@X G).
  Notation "x * y" := (@dot MG (@mx_Monoid_Ops G Mo SLo) _ _ _ x y).
  Notation "x + y" := (@plus MG (@mx_SemiLattice_Ops G SLo) _ _ x y).

(*      
  Fixpoint star_rec n A (M: MX (n,A) (n,A)) {struct n}: MX (n,A) (n,A) :=
    match n with
      | 0 => M
      | S n => 
        let a := subMat 0 O 1 1 M in 
        let b := subMat 0 1 1 n M in
        let c := subMat 1 0 n 1 M in
        let d := subMat 1 1 n n M in
        let e := star_rec d in
        let be:= b*e in
        let ec:= e*c in
        let f := Mat_to_scal (a + be*c) # in
        let fbe := dot_scal_left f be in
        let ecf := dot_scal_right ec f in
          makeMat_blocks 
          (scal_to_Mat f)
          fbe 
          ecf
          (e + ecf*be) 
    end.
*)

  Definition star_build A x n
    (sx: MX(x,A)(x,A) -> MX(x,A)(x,A))
    (sn: MX(n,A)(n,A) -> MX(n,A)(n,A))
    (M: MX(x+n,A)%nat(x+n,A)%nat): MX(x+n,A)%nat(x+n,A)%nat :=
    let a := sub00 M in
    let b := sub01 M in
    let c := sub10 M in
    let d := sub11 M in
    let e := sn d in
    let be:= b*e in
    let ec:= e*c in
    let f := sx (a + be*c) in
    let fbe := f*be in
    let ecf := ec*f in
      makeMat_blocks f fbe ecf (e + ecf*be).
  Implicit Arguments star_build [A].

  Fixpoint star_rec A n: MX (n,A) (n,A) -> MX (n,A) (n,A) :=
    match n with
      | 0 => fun M => M
      | S n => fun M =>
        star_build 1 n (fun a => scal_to_Mat (Mat_to_scal a #)) (@star_rec A n) M
    end.

  Global Instance mx_Star_Op: @Star_Op MG :=
    fun nA M => star_rec (n:=fst nA) M.
  
  Definition mx_star_block A x n := star_build x n (@star_rec A x) (@star_rec A n).

  Context {KA: KleeneAlgebra}.

  Lemma mx_star_compat nA: forall (M N: MX nA nA), M==N -> M# == N# .
  Proof.
    destruct nA as [n A]; intros M N; unfold star, mx_Star_Op; induction n; intro.
    assumption.
    unfold fst, snd in *.
    simpl star_rec. unfold star_build.
    change (S n) with (1+n)%nat. 
    auto 13 with compat.
    (*
    apply makeMat_blocks_compat.
    apply scal_to_Mat_compat.
    apply star_compat.
    apply Mat_to_scal_compat.
    apply plus_compat.
    apply sub00_compat; auto.  
    apply dot_compat.
    apply dot_compat.
    apply sub01_compat; auto.
    apply IHn. 
    apply sub11_compat; auto.
    apply sub10_compat; auto.

    ...
    *)
  Qed.

  Definition prop_star_make_left n A f := forall M: MX(n,A)(n,A), 1 + f M * M == f M.

  Lemma build_star_make_left x n A sx sn:
    prop_star_make_left sx ->
    prop_star_make_left sn ->
    prop_star_make_left (@star_build A x n sx sn).
  Proof.
    intros Hx Hn M.
    unfold star_build.
    set (a := sub00 M).
    set (b := sub01 M).
    set (c := sub10 M).
    set (d := sub11 M).
    set (e := sn d).
    set (be:= b*e).
    set (ec:= e*c).
    set (g := a + be*c).
    set (f := sx g).
    set (fbe := f*be).
    set (ecf := ec*f).
    rewrite (decomposeMat_blocks M).
    unfold fst, snd in *. fold a; fold b; fold c; fold d.
    rewrite one_makeMat_blocks, Mat_blocks_dot, addMat_blocks.
    apply makeMat_blocks_compat.
  
    unfold fbe, f. rewrite <- dot_assoc, <- dot_distr_right. apply Hx. 

    unfold fbe, be. transitivity ((f*b)*(1+e*d)). semiring_reflexivity.
    unfold e. rewrite (Hn d). monoid_reflexivity.

    unfold ecf, ec, be. transitivity ((e*c)*(1+f*(a+b*e*c))). semiring_reflexivity.
    unfold f; rewrite <- (Hx g) at 2.
    unfold g, be; semiring_reflexivity.

    unfold ecf, ec, be. transitivity ((1+e*c*f*b)*(1+e*d)).
    (*     TODO: dans ce genre de buts, on gagne pas mal a faire le menage... comprendre *)
    clearbody b c d e f. clear - KA. (* Time *) semiring_reflexivity.
    unfold e at 2; rewrite (Hn d). unfold e; semiring_reflexivity.
  Qed.

  Lemma mx_star_make_left nA (M: MX nA nA): 1 + M# * M == M#. 
  Proof.
    destruct nA as [n A]; unfold star, mx_Star_Op, fst, snd.
    revert M; induction n.

    intros M i j Hi Hj; inversion Hi.
 
    simpl star_rec. change (S n) with (1+n)%nat. apply build_star_make_left.
     intros M [|] [|] Hi Hj; try omega_false. 
     unfold scal_to_Mat, Mat_to_scal. simpl.
     rewrite <- star_make_left at 2. aci_reflexivity.

     exact IHn.
  Qed.

  Lemma mx_star_block_make_left A x n (M: MX(x+n,A)%nat(x+n,A)%nat):
    Mone(_,A) + mx_star_block M * M == mx_star_block M. 
  Proof.
    apply build_star_make_left; intro; unfold snd; apply mx_star_make_left.
  Qed.

 
  Lemma decomp_dot_leq_left A B x n m (a: MX(x,A)(x,A)) b c (d: MX(n,A)(n,A)) (Y: MX(x+n,A)%nat(m,B)):
    makeMat_blocks a b c d * Y <== Y <-> 
(*       let z := @subMat _ A B _ _ 0 0 x m Y in *)
(*       let y := @subMat _ A B _ _ x 0 n m Y in *)
      let z := sub01 (y:=0) Y in
      let y := sub11 (y:=0) Y in
        a*z <== z /\ b*y <== z /\ c*z <== y /\ d*y <== y.
  Proof.
    change m with (0+m)%nat in *.
    split; intro H.
    rewrite (decomposeMat_blocks Y) in H at 2.
    rewrite (decomposeMat_blocks Y) in H at 1.
    rewrite Mat_blocks_dot in H.
    destruct (mx_blocks_leq H) as (_&H1&_&H2).
    destruct (leq_destruct_plus H1) as [H11 H12]; clear H1.
    destruct (leq_destruct_plus H2) as [H21 H22]; clear H2.
    repeat split; assumption.

    rewrite (decomposeMat_blocks Y) at 2.
    rewrite (decomposeMat_blocks Y) at 1.
    rewrite Mat_blocks_dot.
    do 2 intuition.
    apply makeMat_blocks_incr; 
      apply plus_destruct_leq; simpl Peano.plus in *; trivial;
        repeat intro; omega_false.
  Qed. 



  Definition prop_star_destruct_left n A f := 
    forall mB (M: MX(n,A)(n,A)) (Y: MX(n,A)mB), 
      M * Y <== Y  ->  f M * Y <== Y.

  Lemma build_star_destruct_left x n A sx sn:
    prop_star_destruct_left sx ->
    prop_star_destruct_left sn ->
    prop_star_destruct_left (@star_build A x n sx sn).
  Proof.
    intros Hx Hn [m B] M Y H.
    
    unfold star_build.
    set (a := sub00 M).
    set (b := sub01 M).
    set (c := sub10 M).
    set (d := sub11 M).
    set (e := sn d).
    set (be:= b*e).
    set (ec:= e*c).
    set (g := a + be*c).
    set (f := sx g).
    set (fbe := f*be).
    set (ecf := ec*f).

    rewrite (decomposeMat_blocks M) in H.
    unfold fst, snd in *.
    fold a in H; fold b in H; fold c in H; fold d in H.

    rewrite -> decomp_dot_leq_left in H. destruct H as (H30&H31&H32&H33).
    unfold fst, snd in *.
    set (z := sub01 (y:=0) Y) in *.
    set (y := sub11 (y:=0) Y) in *.

    assert (H34: e*y <== y). 
     unfold e. apply Hn, H33.
    clear H33.

    assert (H36: b*e*y <== z). 
     monoid_rewrite H34. exact H31.
    clear H31.

    assert (H39: (a+b*e*c)*z <== z).
     rewrite dot_distr_left; apply plus_destruct_leq; trivial. (* 30 *)
     monoid_rewrite H32. exact H36.                            (* 32 36 *)
    clear H30.

    assert (H40: f*z <== z). unfold f. 
     apply Hx, H39.
    clear H39.

    assert (H42: f*b*e*y <== z).
     monoid_rewrite H36. exact H40. (* 36 40  *)

    assert (H45: e*c*f*z <== y).
     monoid_rewrite H40. monoid_rewrite H32. exact H34. (* 32 34 40 *)
    clear H32.

    assert (H47: e*c*f*b*e*y <== y).
     monoid_rewrite H36. exact H45. (* 36 45 *)
    clear H36.

    rewrite -> decomp_dot_leq_left. unfold fst, snd; fold z; fold y. 
    repeat split.

    exact H40.
    rewrite <- H42; monoid_reflexivity.
    exact H45. 
    clear H40 H42 H45.
    patched semiring_normalize; apply plus_destruct_leq.
    exact H34. exact H47. 
  Qed.


  Lemma mx_star_destruct_left: forall nA mB (M: MX nA nA) (Y: MX nA mB), M*Y <== Y  ->  M#*Y <== Y.
  Proof.
    intros [n A]; induction n. 

    intros mB M Y H i j Hi; inversion Hi.

    unfold star, mx_Star_Op, fst, snd. simpl star_rec.
    change (S n) with (1+n)%nat.
    apply build_star_destruct_left; trivial.

    intros [m B] M Y H [|] j Hi Hj. 2:omega_false.
    unfold scal_to_Mat, Mat_to_scal. simpl.
    rewrite plus_neutral_right. apply star_destruct_left.
    specialize (H O j Hi Hj). simpl in H. rewrite plus_neutral_right in H. assumption.
  Qed.

  Lemma mx_star_block_destruct_left: forall A x n mB (M: MX(x+n,A)%nat(x+n,A)%nat) (Y: MX _ mB), 
    M * Y <== Y  ->  mx_star_block M * Y <== Y.
  Proof.
    intros A x n.
    apply build_star_destruct_left; intro; apply mx_star_destruct_left.
  Qed.


  Lemma decomp_dot_leq_right A x n mB (a: MX(x,A)(x,A)) b c (d: MX(n,A)(n,A)) (Y: MX mB(x+n,A)%nat):
    Y * makeMat_blocks a b c d <== Y <-> 
      let y := sub10 (x:= 0) Y in
      let z := sub11 (x:= 0) (y:=x) Y in
        y * a <== y /\ z * c <== y /\
        y * b <== z  /\ z * d <== z.
  Proof.
    destruct mB as [m B].  change m with (0+m)%nat in *.
    intros. split; intro H. 
    rewrite (decomposeMat_blocks Y) in H at 2.
    rewrite (decomposeMat_blocks Y) in H at 1.
    rewrite Mat_blocks_dot in H.
    destruct (mx_blocks_leq H) as (H0&H1&H2&H3).
    destruct (leq_destruct_plus H0) as [H01 H02]; clear H0.
    destruct (leq_destruct_plus H1) as [H11 H12]; clear H1.
    destruct (leq_destruct_plus H2) as [H21 H22]; clear H2.
    destruct (leq_destruct_plus H3) as [H31 H32]; clear H3.
    repeat split; assumption.

    rewrite (decomposeMat_blocks Y) at 2.
    rewrite (decomposeMat_blocks Y) at 1.
    rewrite Mat_blocks_dot.
    do 2 intuition.
    apply makeMat_blocks_incr; 
      apply plus_destruct_leq; simpl Peano.plus in *; trivial;
        repeat intro; omega_false.
  Qed. 


  Definition prop_star_destruct_right n A f := 
    forall mB (M: MX(n,A)(n,A)) (Y: MX mB (n,A)), 
      Y * M <== Y  ->  Y * f M <== Y.

  
  Lemma build_star_destruct_right x n A sx sn:
    prop_star_destruct_right sx ->
    prop_star_destruct_right sn ->
    prop_star_destruct_right (@star_build A x n sx sn).
  Proof.
    intros Hx Hn [m B] M Y H.
    
    unfold star_build.
    set (a := sub00 M).
    set (b := sub01 M).
    set (c := sub10 M).
    set (d := sub11 M).
    set (e := sn d).
    set (be:= b*e).
    set (ec:= e*c).
    set (g := a + be*c).
    set (f := sx g).
    set (fbe := f*be).
    set (ecf := ec*f).

    rewrite (decomposeMat_blocks M) in H.
    unfold fst, snd in *.
    fold a in H; fold b in H; fold c in H; fold d in H.

    rewrite -> decomp_dot_leq_right in H. destruct H as (H30&H31&H32&H33).
    unfold fst, snd in *.

    set (y := sub10 (x:=0) Y)in*.
    set (z := sub11 (x := 0) (y:=x) Y)in*.

    assert (H34: z*e <== z). unfold e. apply Hn, H33. clear H33.
    assert (H35: z*e*c <== z*c). monoid_rewrite H34. reflexivity.
    assert (H36: z*e*c<== y). rewrite <- H31. trivial. 
    assert (H39: y*(a+b*e*c) <== y).
      rewrite dot_distr_right; apply plus_destruct_leq; trivial. (* 30 *)
      patched semiring_normalize.  
      monoid_rewrite H32. 
      exact H36.         
    assert (H40 : y * f <== y).  unfold f. apply Hx, H39.
    assert (H42: z*e*c*f <== y). monoid_rewrite H36. exact H40.
    assert (H45:y*f*b*e <== z). rewrite H40. rewrite H32. exact H34. 
    assert (H46:z*e*c*f*b*e <== y*f*b*e). rewrite H36. reflexivity.
    assert (H47:z*e*c*f*b*e <==z). rewrite <- H45 at 2. exact H46. 


    clear - KA Ko SLo Mo G H40 H42 H45 H34 H47.
    (* BUG     clear - H40 H42 H45 H34 H47. *)
    
    rewrite -> decomp_dot_leq_right. unfold fst, snd; fold z; fold y.
    unfold ecf, fbe, ec, be. repeat split.

    exact H40. 

    (* BUG cf ci dessus, clean - vire trop de choses patched monoid_normalize. *)
    rewrite  <- H42.  monoid_reflexivity.
    unfold fbe, be. patched monoid_normalize. exact H45.
    clear H40 H42 H45.
    patched semiring_normalize; apply plus_destruct_leq.
    exact H34. exact H47. 
  Qed.

  Lemma mx_star_destruct_right: forall nA mB (M: MX nA nA) (Y: MX mB nA), Y*M <== Y  ->  Y*M# <== Y.
  Proof.
    intros [n A]; induction n. 

    intros mB M Y H i j Hi Hj; inversion Hj. 

    unfold star, mx_Star_Op, fst, snd. simpl star_rec.
    change (S n) with (1+n)%nat.
    apply build_star_destruct_right; trivial.

    intros [m B] M Y H i [|] Hi Hj. 2:omega_false.
    unfold scal_to_Mat, Mat_to_scal. simpl.
    rewrite plus_neutral_right. apply star_destruct_right.
    specialize (H i O Hi Hj). simpl in H. rewrite plus_neutral_right in H. assumption.

  Qed.


  Global Instance mx_KleeneAlgebra: 
    @KleeneAlgebra MG mx_Monoid_Ops mx_SemiLattice_Ops mx_Star_Op.
  Proof.
    constructor; intros.
    exact mx_SemiRing.
    apply mx_star_make_left.
    apply mx_star_destruct_left; assumption.
    apply mx_star_destruct_right; assumption.
  Qed.
(*
  Global Instance mx_KleeneAlgebra: @KleeneAlgebra mx_Graph mx_Monoid_Ops mx_SemiLattice_Ops mx_Star_Op := {
    KA_ISR := mx_SemiRing; 
    star_make_left := mx_star_make_left;
    star_destruct_left := mx_star_destruct_left;
    star_destruct_right := mx_star_destruct_right
  }.
*)

  Variable A: T.

  Lemma mx_star_blocks': forall x n (M: MX(x+n,A)%nat(x+n,A)%nat), M# == mx_star_block M.
  Proof.
    intros.
    apply leq_antisym.
    apply star_destruct_right_one.
    rewrite mx_star_block_make_left. reflexivity.
    rewrite <- (dot_neutral_right (mx_star_block M)).
    rewrite (one_leq_star_a M).
    apply mx_star_block_destruct_left.
    rewrite <- star_make_right at 2.
    auto with algebra.
  Qed.
    
  Lemma mx_star_blocks: forall x n (a: MX(x,A)(x,A)) (b: MX(x,A)(n,A)) (c: MX(n,A)(x,A)) (d: MX(n,A)(n,A)),
    let e := d# in
    let be:= b*e in
    let ec:= e*c in
    let f := (a + be*c)# in
    let fbe := f*be in
    let ecf := ec*f in
      (makeMat_blocks a b c d)# == makeMat_blocks f fbe ecf (e + ecf*be).
  Proof.
    intros. rewrite mx_star_blocks'. unfold mx_star_block, star_build. 
    repeat match goal with |- context[star_rec ?M] => change (star_rec M) with (M#) end.
    (* ces rewrites devraient marcher...
    unfold fst, snd in *.
    setoid_rewrite mx_block_00. setoid_rewrite mx_block_01. 
    setoid_rewrite mx_block_10. setoid_rewrite mx_block_11. 
    *)
    apply makeMat_blocks_compat;
    auto 9 using mx_block_00, mx_block_01, mx_block_10, mx_block_11 with compat.
  Qed.

  Lemma star_trigonal_blocks n m (M: MX(n,A)(n,A)) (N: MX(m,A)(m,A)) (P: MX(n,A)(m,A)): 
    (makeMat_blocks M P 0 N)# == makeMat_blocks (M#)  (M# * P * N#)  0 (N#).
  Proof.
    intros. rewrite mx_star_blocks. apply makeMat_blocks_compat.
     apply star_compat. semiring_reflexivity.
     rewrite dot_ann_right, plus_neutral_right. trivial with algebra.
     semiring_reflexivity.
     semiring_reflexivity.     
  Qed.

  Lemma star_diagonal_blocks n m (M: MX(n,A)(n,A)) (N: MX(m,A)(m,A)) :
    (makeMat_blocks M 0 0 N)# == makeMat_blocks (M#) 0 0 (N#).
  Proof.
    intros. rewrite star_trigonal_blocks. apply makeMat_blocks_compat; trivial.
    semiring_reflexivity.
  Qed.
  
  Lemma Mat_to_scal_compat_star (a : MX (1%nat,A) (1%nat,A)) : Mat_to_scal (a #) ==  (Mat_to_scal a) #.
  Proof.
    unfold Mat_to_scal; simpl; intros.
    destruct_blocks. rewrite plus_neutral_right;
    semiring_reflexivity.
    omega_false.
  Qed.

  Lemma scal_to_Mat_compat_star (a : X A A) : scal_to_Mat (a #) ==  (scal_to_Mat a) #.
  Proof.
    intros [|] [|] Hi Hj; try omega_false.
    simpl. destruct_blocks. 
    rewrite plus_neutral_right. reflexivity.
    discriminate H.
  Qed.

End Defs.

(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Properties of matrices over a Kleene algebra (in particular, they form a typed Kleene algebra)  *)

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import Monoid.
Require Import SemiLattice.
Require Import SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiLattice.
Require Import MxSemiRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PreDefs.

  Local Transparent equal.

  Context `{KA: KleeneAlgebra}.
  Variable A: T.
  Notation mx_equal n m := (mx_equal_ A n m) (only parsing).
  Notation mx_leq n m := (mx_leq_ A n m) (only parsing).

  Notation MX n m := (@X (mx_Graph A) (n%nat) (m%nat)).
  Notation X := (@X G A A).
  Notation SMX n := (MX n n).

  (** block construction of the star operation over matrices  *)
  Definition star_build x n (sx: SMX x -> SMX x) (sn: SMX n -> SMX n) (M:  SMX (x+n)): SMX (x+n) :=
    let a := mx_sub00 M in
    let b := mx_sub01 M in
    let c := mx_sub10 M in
    let d := mx_sub11 M in
    let e := sn d in
    let be:= b*e in
    let ec:= e*c in
    let f := sx (a + be*c) in
    let fbe := f*be in
    let ecf := ec*f in
      mx_blocks f fbe ecf (e + ecf*be).

  (** recursive construction *)
  Fixpoint star_rec n: SMX n -> SMX n :=
    match n with
      | 0 => fun M => M
      | S n => fun M =>
        star_build (fun a => mx_of_scal (mx_to_scal a #)) (@star_rec n) M
    end.

  Definition mx_star_block x n := star_build (@star_rec x) (@star_rec n).

  Definition prop_star_make_left n f := forall M: SMX n, 1 + f M * M == f M.

  (** below, we prove that the operation we constructed is actually the star operation over matrices  *)

  Lemma build_star_make_left x n sx sn:
    prop_star_make_left sx ->
    prop_star_make_left sn ->
    prop_star_make_left (@star_build x n sx sn).
  Proof.
    intros Hx Hn M.
    unfold star_build.
    set (a := mx_sub00 M).
    set (b := mx_sub01 M).
    set (c := mx_sub10 M).
    set (d := mx_sub11 M).
    set (e := sn d).
    set (be:= b*e).
    set (ec:= e*c).
    set (g := a + be*c).
    set (f := sx g).
    set (fbe := f*be).
    set (ecf := ec*f).
    setoid_rewrite (mx_decompose_blocks M).
    fold a; fold b; fold c; fold d.
    clearbody a b c d. clear M.
    rewrite mx_blocks_one, mx_blocks_dot, mx_blocks_plus.
    apply mx_blocks_compat.
  
    unfold fbe, f. rewrite <- dot_assoc, <- dot_distr_right. apply Hx. 

    unfold fbe, be. transitivity ((f*b)*(1+e*d)). clear - KA. semiring_reflexivity.
    unfold e. clearbody f. rewrite (Hn d). semiring_reflexivity. 
    (* BUG: le rewrite ne passe pas sans le clearbody *)

    unfold ecf, ec, be. transitivity ((e*c)*(1+f*(a+b*e*c))). clear - KA. semiring_reflexivity.
    unfold f. clearbody f. rewrite <- (Hx g) at 2. (* BUG: idem *)
    reflexivity.

    unfold ecf, ec, be. transitivity ((1+e*c*f*b)*(1+e*d)).
    clearbody e f. clear - KA. semiring_reflexivity.
    unfold e. clearbody e. rewrite (Hn d). semiring_reflexivity. (* BUG: idem *)
  Qed.


  Lemma decomp_dot_leq_left x n m (a: SMX x) b c (d: SMX n) (Y: MX (x+n) m):
    mx_blocks a b c d * Y <== Y <-> 
      let z := mx_sub01 (y:=0) Y in
      let y := mx_sub11 (y:=0) Y in
        a*z <== z /\ b*y <== z /\ c*z <== y /\ d*y <== y.
  Proof.
    change m with (0+m)%nat in *.
    split; intro H.
    rewrite (mx_decompose_blocks Y) in H at 2.
    rewrite (mx_decompose_blocks Y) in H at 1.
    rewrite mx_blocks_dot in H.
    destruct (mx_blocks_leq H) as (_&H1&_&H2).
    destruct (leq_destruct_plus H1) as [H11 H12]; clear H1.
    destruct (leq_destruct_plus H2) as [H21 H22]; clear H2.
    repeat split; assumption.

    rewrite (mx_decompose_blocks Y) at 2.
    rewrite (mx_decompose_blocks Y) at 1.
    rewrite mx_blocks_dot.
    do 2 intuition.
    apply mx_blocks_incr; 
      apply plus_destruct_leq; simpl Peano.plus in *; trivial;
        repeat intro; lia_false.
  Qed. 

  Definition prop_star_destruct_left n f := 
    forall m (M: SMX n) (Y: MX n m), 
      M * Y <== Y  ->  f M * Y <== Y.

  Lemma build_star_destruct_left x n sx sn:
    prop_star_destruct_left sx ->
    prop_star_destruct_left sn ->
    prop_star_destruct_left (@star_build x n sx sn).
  Proof.
    intros Hx Hn m M Y H.
    
    unfold star_build.
    set (a := mx_sub00 M).
    set (b := mx_sub01 M).
    set (c := mx_sub10 M).
    set (d := mx_sub11 M).
    set (e := sn d).
    set (be:= b*e).
    set (ec:= e*c).
    set (g := a + be*c).
    set (f := sx g).
    set (fbe := f*be).
    set (ecf := ec*f).

    rewrite (mx_decompose_blocks M) in H.
    fold a in H; fold b in H; fold c in H; fold d in H.
    clearbody a b c d. clear M.

    rewrite -> decomp_dot_leq_left in H. destruct H as (H30&H31&H32&H33).
    set (z := mx_sub01 (y:=0) Y) in *.
    set (y := mx_sub11 (y:=0) Y) in *.
    rewrite -> decomp_dot_leq_left. fold z; fold y. 
    clearbody y z. clear Y.

    assert (H34: e*y <== y). 
     unfold e. apply Hn, H33.
    clear H33.

    assert (H36: b*e*y <== z). 
     monoid_rewrite H34. exact H31.
    clear H31.

    assert (H39: (a+b*e*c)*z <== z).
     rewrite dot_distr_left; apply plus_destruct_leq; trivial. 
     monoid_rewrite H32. exact H36.                            
    clear H30.

    assert (H40: f*z <== z). unfold f. 
     apply Hx, H39.
    clear H39.

    assert (H42: f*b*e*y <== z).
     monoid_rewrite H36. exact H40. 

    assert (H45: e*c*f*z <== y).
     monoid_rewrite H40. monoid_rewrite H32. exact H34. 
    clear H32.

    assert (H47: e*c*f*b*e*y <== y).
     monoid_rewrite H36. exact H45. 
    clear H36.

    repeat split.
      exact H40.
      rewrite <- H42. unfold fbe, be. semiring_reflexivity.
      exact H45. 
      clear H40 H42 H45.
      unfold ecf, ec, be.
      semiring_normalize; apply plus_destruct_leq.
      exact H34. exact H47. 
  Qed.


  Lemma decomp_dot_leq_right x n m (a: SMX x) b c (d: SMX n) (Y: MX m (x+n)):
    Y * mx_blocks a b c d <== Y <-> 
      let y := mx_sub10 (x:= 0) Y in
      let z := mx_sub11 (x:= 0) (y:=x) Y in
        y * a <== y /\ z * c <== y /\
        y * b <== z  /\ z * d <== z.
  Proof.
    change m with (0+m)%nat in *.
    split; intro H. 
    rewrite (mx_decompose_blocks Y) in H at 2.
    rewrite (mx_decompose_blocks Y) in H at 1.
    rewrite mx_blocks_dot in H.
    destruct (mx_blocks_leq H) as (H0&H1&H2&H3).
    destruct (leq_destruct_plus H0) as [H01 H02]; clear H0.
    destruct (leq_destruct_plus H1) as [H11 H12]; clear H1.
    destruct (leq_destruct_plus H2) as [H21 H22]; clear H2.
    destruct (leq_destruct_plus H3) as [H31 H32]; clear H3.
    repeat split; assumption.

    rewrite (mx_decompose_blocks Y) at 2.
    rewrite (mx_decompose_blocks Y) at 1.
    rewrite mx_blocks_dot.
    do 2 intuition.
    apply mx_blocks_incr; 
      apply plus_destruct_leq; simpl Peano.plus in *; trivial;
        repeat intro; lia_false.
  Qed. 

  Definition prop_star_destruct_right n f := 
    forall m (M: SMX n) (Y: MX m n), 
      Y * M <== Y  ->  Y * f M <== Y.
  
  Lemma build_star_destruct_right x n sx sn:
    prop_star_destruct_right sx ->
    prop_star_destruct_right sn ->
    prop_star_destruct_right (@star_build x n sx sn).
  Proof.
    intros Hx Hn m M Y H.
    
    unfold star_build.
    set (a := mx_sub00 M).
    set (b := mx_sub01 M).
    set (c := mx_sub10 M).
    set (d := mx_sub11 M).
    set (e := sn d).
    set (be:= b*e).
    set (ec:= e*c).
    set (g := a + be*c).
    set (f := sx g).
    set (fbe := f*be).
    set (ecf := ec*f).

    rewrite (mx_decompose_blocks M) in H.
    fold a in H; fold b in H; fold c in H; fold d in H.
    clearbody a b c d. clear M.

    rewrite -> decomp_dot_leq_right in H. destruct H as (H30&H31&H32&H33).
    set (y := mx_sub10 (x:=0) Y)in*.
    set (z := mx_sub11 (x:=0) Y)in*.
    rewrite -> decomp_dot_leq_right. fold z; fold y. 
    clearbody y z. clear Y.

    assert (H34: z*e <== z). unfold e. apply Hn, H33. clear H33.
    assert (H35: z*e*c <== z*c). monoid_rewrite H34. reflexivity.
    assert (H36: z*e*c<== y). rewrite <- H31. trivial. 
    assert (H39: y*(a+b*e*c) <== y).
      rewrite dot_distr_right; apply plus_destruct_leq; trivial. (* 30 *)
      rewrite 2dot_assoc, H32. exact H36.         

    assert (H40: y*f <== y).  unfold f. apply Hx, H39.
    assert (H42: z*e*c*f <== y). rewrite H36. exact H40.
    assert (H45: y*f*b*e <== z). rewrite H40. rewrite H32. exact H34. 
    assert (H46: z*e*c*f*b*e <== y*f*b*e). rewrite H36. reflexivity.
    assert (H47: z*e*c*f*b*e <==z). rewrite <- H45 at 2. exact H46. 

    clear - KA H40 H42 H45 H34 H47.
    repeat split.
      exact H40. 
      rewrite  <- H42. unfold ecf, ec. semiring_reflexivity.
      unfold fbe, be. semiring_normalize. exact H45.
      semiring_normalize; apply plus_destruct_leq.
       unfold ecf, ec, be. semiring_normalize. exact H47. 
       exact H34. 
  Qed.

End PreDefs.


Section Defs.

  Context `{KA: KleeneAlgebra}.
  Variable A: T.
  Notation mx_equal n m := (mx_equal_ A n m) (only parsing).
  Notation mx_leq n m := (mx_leq_ A n m) (only parsing).

  Notation X := (@X G A A).
  Notation MX n m := (MX_ A n m).
  Notation SMX n := (MX_ A n n).

  Global Instance mx_Star_Op: Star_Op (mx_Graph A) := { star n := @star_rec _ _ _ _ _ _ }.


  Lemma mx_star_compat n (M N: MX n n): M==N -> M# == N# .
  Proof.
    unfold star, mx_Star_Op. induction n; intro. 
    assumption.
    Opaque equal.
    cbn. 
    change (S n) with (1+n)%nat. 
    auto 13 with compat.
    Transparent equal.
    (*
    apply mx_blocks_compat.
    apply mx_of_scal_compat.
    apply star_compat.
    apply mx_to_scal_compat.
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

  Lemma mx_star_make_left n: forall M: MX n n, 1 + M# * M == M#. 
  Proof.
    unfold star, mx_Star_Op.
    induction n; intro M.
     mx_intros i j Hi Hj. 
 
     Opaque one dot plus. simpl. Transparent one dot plus.
     change (S n) with (1+n)%nat. 
     apply build_star_make_left. 
      intro N; mx_intros i j Hi Hj. 
      unfold mx_to_scal. simpl.
      rewrite <- star_make_left at 2. semiring_reflexivity.
      exact IHn.
  Qed.

  Lemma mx_star_block_make_left x n: forall M: MX (x+n) (x+n),
    1 + mx_star_block M * M == mx_star_block M. 
  Proof.
    apply build_star_make_left; intro; rapply mx_star_make_left.
  Qed.

 

  Lemma mx_star_destruct_left: forall n m (M: MX n n) (Y: MX n m), M*Y <== Y  ->  M#*Y <== Y.
  Proof.
    induction n; intros.
     mx_intros i j Hi Hj.

     unfold star, mx_Star_Op.
     Opaque one dot plus leq. simpl. Transparent one dot plus leq.
     change (S n) with (1+n)%nat.
     apply build_star_destruct_left; trivial.
     clear - KA.
     intros m M Y H; mx_intros i j Hi Hj.
     unfold mx_of_scal. simpl.
     rewrite plus_neutral_right. apply star_destruct_left.
     specialize (H O j (le_n _) Hj). simpl in H. rewrite plus_neutral_right in H. assumption.
  Qed.

  Lemma mx_star_block_destruct_left: forall x n m (M: MX (x+n) (x+n)) (Y: MX (x+n) m), 
    M * Y <== Y  ->  mx_star_block M * Y <== Y.
  Proof.
    intros x n m. apply build_star_destruct_left; intros ? ? ?; apply mx_star_destruct_left.
  Qed.


  Lemma mx_star_destruct_right: forall n m (M: MX n n) (Y: MX m n), Y*M <== Y  ->  Y*M# <== Y.
  Proof.
    induction n; intros. 
     mx_intros i j Hi Hj.

     unfold star, mx_Star_Op.
     Opaque one dot plus leq. simpl. Transparent one dot plus leq.
     change (S n) with (1+n)%nat.
     apply build_star_destruct_right; trivial.
     clear - KA.
     intros m M Y H; mx_intros i j Hi Hj.
     unfold mx_of_scal. simpl.
     rewrite plus_neutral_right. apply star_destruct_right.
     specialize (H i O Hi (le_n _)). simpl in H. rewrite plus_neutral_right in H. assumption.
  Qed.



  Global Instance mx_KleeneAlgebra: KleeneAlgebra (mx_Graph A).
  Proof.
    constructor; intros.
    apply mx_SemiRing.
    apply mx_star_make_left.
    apply mx_star_destruct_left; assumption.
    apply mx_star_destruct_right; assumption.
  Qed.


  (** additional properties of block matrices  *)

  Lemma mx_blocks_star': forall x n (M: MX (x+n) (x+n)), M# == mx_star_block M.
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
    
  Lemma mx_blocks_star: forall x n (a: MX x x) (b: MX x n) (c: MX n x) (d: MX n n),
    let e := d# in
    let be:= b*e in
    let ec:= e*c in
    let f := (a + be*c)# in
    let fbe := f*be in
    let ecf := ec*f in
      (mx_blocks a b c d)# == mx_blocks f fbe ecf (e + ecf*be).
  Proof.
    intros. rewrite mx_blocks_star'. unfold mx_star_block, star_build. 
    repeat match goal with |- context[star_rec ?M] => change (star_rec M) with (M#) end.
    Opaque equal.
    apply mx_blocks_compat;
    auto 9 using mx_block_00, mx_block_01, mx_block_10, mx_block_11 with compat.
    Transparent equal.
  Qed.

  Lemma mx_blocks_star_trigonal n m (M: MX n n) (N: MX m m) (P: MX n m): 
    (mx_blocks M P 0 N)# == mx_blocks (M#)  (M# * P * N#)  0 (N#).
  Proof.
    intros. rewrite mx_blocks_star. apply mx_blocks_compat.
     apply star_compat. semiring_reflexivity.
     rewrite dot_ann_right, plus_neutral_right. trivial with algebra.
     semiring_reflexivity.
     semiring_reflexivity.     
  Qed.

  Lemma mx_blocks_star_diagonal n m (M: MX n n) (N: MX m m) :
    (mx_blocks M 0 0 N)# == mx_blocks (M#) 0 0 (N#).
  Proof.
    intros. rewrite mx_blocks_star_trigonal. apply mx_blocks_compat; trivial.
    semiring_reflexivity.
  Qed.
  
  Lemma mx_to_scal_star (a: MX 1 1): mx_to_scal (a #) ==  (mx_to_scal a) #.
  Proof.
    simpl. destruct_blocks. 
     rewrite plus_neutral_right. reflexivity.
     discriminate.
  Qed.

  Lemma mx_of_scal_star (a: X): mx_of_scal (a #) ==  (mx_of_scal a) #.
  Proof.
    mx_intros i j Hi Hj. 
    simpl. destruct_blocks. 
    rewrite plus_neutral_right. reflexivity.
    discriminate.
  Qed.

End Defs.

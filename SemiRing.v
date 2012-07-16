(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Properties, definitions, hints and tactics for semirings :
   - [semiring_reflexivity] solves the equational theory
   - [semiring_normalize] normalizes the goal by developping expressions
   - [semiring_clean] removes annihilators
   - [semiring_cleanassoc] just normalizes parentheses
   *)

Require Import MyFSets MyFSetProperties.

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import Monoid.
Require Import SemiLattice.
Require Import Numbers.
Require        Reification.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Hint Extern 0 (equal _ _ _ _) => first [ 
    apply dot_ann_left
  | apply dot_ann_right
  | apply dot_distr_left
  | apply dot_distr_right
]: algebra.

(* Hint Resolve @dot_ann_left @dot_ann_right @dot_distr_left @dot_distr_right: algebra. *)
Hint Rewrite @dot_ann_left @dot_ann_right using ti_auto: simpl.


(** Free, syntactic, model of semirings, to obtain write reflexive tactics *)
Module U.

  Inductive X :=
  | one: X
  | zero: X
  | dot: X -> X -> X
  | plus: X -> X -> X
  | var: positive -> X.

  Inductive equal: X -> X -> Prop :=
  | refl_one: equal one one
  | refl_zero: equal zero zero
  | refl_var: forall i, equal (var i) (var i)

  | dot_assoc: forall x y z, equal (dot x (dot y z)) (dot (dot x y) z)
  | dot_neutral_left: forall x, equal (dot one x) x
  | dot_neutral_right: forall x, equal (dot x one) x

  | plus_neutral_left: forall x, equal (plus zero x) x
  | plus_idem: forall x, equal (plus x x) x
  | plus_assoc: forall x y z, equal (plus x (plus y z)) (plus (plus x y) z)
  | plus_com: forall x y, equal (plus x y) (plus y x)

  | dot_ann_left: forall x, equal (dot zero x) zero
  | dot_ann_right: forall x, equal (dot x zero) zero
  | dot_distr_left: forall x y z, equal (dot (plus x y) z) (plus (dot x z) (dot y z))
  | dot_distr_right: forall x y z, equal (dot x (plus y z)) (plus (dot x y) (dot x z))

  | dot_compat: forall x x', equal x x' -> forall y y', equal y y' -> equal (dot x y) (dot x' y')
  | plus_compat: forall x x', equal x x' -> forall y y', equal y y' -> equal (plus x y) (plus x' y')
  | equal_trans: forall x y z, equal x y -> equal y z -> equal x z
  | equal_sym: forall x y, equal x y -> equal y x.

  Import Positive PositiveUtils.
  Notation S := Datatypes.S.

  Module VLstA := ListOrderedTypeAlt NumOTA.
  Module VLst := OrderedType_from_Alt VLstA.   
  Module VLSet' := FSetList.Make VLst. Module VLSet := FSetHide VLSet'.
  Module VLSetProps := MySetProps VLSet.
  Ltac setdec := VLSetProps.setdec.

  Definition is_zero t := match t with zero => true | _ => false end.
  Definition is_one t := match t with one => true | _ => false end.

  Fixpoint norm_aux n b a x y := 
    (* equal b+a*x*y *)
    match n with 
      | O => VLSet.empty        (* absurd *)
      | S n => 
        match x with
          | one => norm_aux' n b a y
          | zero => b
          | dot x1 x2 => norm_aux n b a x1 (dot x2 y)
          | plus x1 x2 => norm_aux n (norm_aux n b a x1 y) a x2 y
          | var i => norm_aux' n b (List.cons i a) y
        end
    end

  with norm_aux' n b a y :=
    (* equal b+a*y *)
    match n with 
      | O => VLSet.empty        (* absurd *)
      | S n => 
        match y with
          | one => VLSet.add a b
          | zero => b
          | dot y1 y2 => norm_aux n b a y1 y2
          | plus y1 y2 => norm_aux' n (norm_aux' n b a y1) a y2
          | var i => VLSet.add (List.cons i a) b
        end
    end.

  Fixpoint size x :=
    (match x with
      | zero => 1
      | one => 1
      | var _ => 1
      | plus x y => 1 + size x + size y
      | dot x y => 1 + 2*size x + size y
    end)%nat.

  Definition X_to_VLSet x := norm_aux' (S (size x)) VLSet.empty List.nil x.

  Definition fdot i acc := if is_one acc then (var i) else dot acc (var i).
  Definition VLst_to_X m := List.fold_right fdot one m.

  Definition fplus m acc := if is_zero acc then VLst_to_X m else plus acc (VLst_to_X m).
  Definition VLSet_to_X s := VLSet.fold fplus s zero.

  (** normalisation and decision functions *)
  Definition norm p := VLSet_to_X (X_to_VLSet p).
  Definition decide x y := VLSet.equal (X_to_VLSet x) (X_to_VLSet y).


(*begintests
  Goal norm (dot (var 2) (plus one (var 1))) = norm (plus (var 2) (dot (var 2) (var 1))).
    reflexivity.
  Qed.
  
  Goal
    let x := (dot (var 3) (plus one (plus (var 1) (dot (plus (dot (var 2) one) (var 2)) (var 3))))) in
    let y := (plus (var 3) (plus (var 3) (plus x (dot (plus (dot (var 2) one) x) (var 3))))) in
    let z := dot (dot x y) (plus x (dot (plus zero x) y)) in
    let nz := norm (dot z x) in True.
    Time vm_compute.    (* 6 *)  (* 4.22 2.86 1.02  *)  (* 20.4 12.5 4.0 3.0 *)
  Abort.
endtests*)


  (** cleaning functions  *)
  Fixpoint clean0 (x: X): X := 
    match x with
      | dot x y => 
        let x := clean0 x in
          let y := clean0 y in
            if is_zero x then zero
              else if is_zero y then zero
                else dot x y
      | plus x y => 
        let x := clean0 x in
          let y := clean0 y in
            if is_zero x then y
              else if is_zero y then x
                else plus x y
      | x => x
    end.

  Fixpoint clean1 (x: X): X := 
    match x with
      | dot x y => 
        let x := clean1 x in
          let y := clean1 y in
            if is_one x then y
              else if is_one y then x
                else dot x y
      | plus x y => plus (clean1 x) (clean1 y)
      | x => x
    end.

  Definition cplus a x := if is_zero a then x else plus a x.
  Definition cdot a x := if is_one a then x else dot a x.
  Fixpoint clean_sum a x := 
    match x with
      | zero => a
      | one => cplus a one
      | var i => cplus a (var i)
      | dot x1 x2 => cplus a (clean_prod (clean_prod one x1) x2)
      | plus x1 x2 => clean_sum (clean_sum a x1) x2
    end
  with clean_prod a x := 
    match x with
      | zero => zero
      | one => a
      | var i => cdot a (var i)
      | dot x1 x2 => clean_prod (clean_prod a x1) x2
      | plus x1 x2 => cdot a (clean_sum (clean_sum zero x1) x2)
    end.

  Lemma Is_zero t : is_zero t = true -> t = zero.
  Proof. destruct t; simpl; intuition discriminate. Qed.

  Lemma Is_one t : is_one t = true -> t = one.
  Proof. destruct t; simpl; intuition discriminate. Qed.

  Ltac destruct_tests := 
    repeat (
      repeat match goal with
               | H: is_zero ?x = _ |- _ => rewrite H
               | H: is_one  ?x = _ |- _ => rewrite H
               | H: is_zero ?x = _, H': context[is_zero ?x] |- _ => rewrite H in H'
               | H: is_one  ?x = _, H': context[is_one  ?x] |- _ => rewrite H in H'
             end;
      repeat match goal with 
               | |- context[is_zero ?x] => 
                 match x with 
                   | context[is_zero ?y] => fail 1
                   |  _ => let Z := fresh "Z" in 
                     case_eq (is_zero x); intro Z; try (rewrite (Is_zero Z) in *; clear Z)
                 end
               | |- context[is_one ?x] => 
                 match x with 
                   | context[is_one ?y] => fail 1
                   |  _ => let O := fresh "O" in 
                     case_eq (is_one x); intro O; try (rewrite (Is_one O) in *; clear O)
                 end
             end;
      try discriminate).



  Section correctness.          (* used to protect instances *)

    Lemma equal_refl: forall x, equal x x.
    Proof. induction x; constructor; assumption. Qed.
  
    Local Hint Constructors equal.
    Local Hint Resolve equal_refl.
  
    Instance equivalence_equal: Equivalence equal.
    Proof. 
      constructor.
       exact equal_refl.
       exact equal_sym.
       exact equal_trans.
    Qed.
    Instance plus_compat_free: Proper (equal ==> equal ==> equal) plus := plus_compat.
    Instance dot_compat_free: Proper (equal ==> equal ==> equal) dot := dot_compat.
  
  
    Lemma VLst_add: forall i q, equal (VLst_to_X (List.cons i q)) (dot (VLst_to_X q) (var i)).
    Proof.
      simpl; unfold fdot; intros. destruct_tests; auto. 
    Qed.
  
    Lemma Hdc: SetoidList.compat_op eq equal fdot.
    Proof. 
      intros i j x y H H'; subst; unfold fdot. destruct_tests; auto with compat.
       rewrite <- H'. symmetry; constructor.
       rewrite H'. constructor.
    Qed.
  
    Lemma VLst_to_X_compat: forall i j, VLst.eq i j -> equal (VLst_to_X i) (VLst_to_X j).
    Proof.
      unfold VLst_to_X. intros i j H. apply VLstA.reflect in H. subst. reflexivity.
    Qed.
  
    Lemma Hpc: SetoidList.compat_op VLst.eq equal fplus.
    Proof. 
      intros i j H x y H'; unfold fplus.
      destruct_tests; rewrite (VLst_to_X_compat H); auto with compat.
       rewrite <- H'. symmetry; constructor.
       rewrite H'. constructor.
    Qed. 
  
    Lemma Hpt: SetoidList.transpose equal fplus.
    Proof.
      intros i j z. unfold fplus. destruct_tests; auto with compat.
       rewrite plus_com. auto.
       rewrite plus_com. auto.
       rewrite <- plus_assoc, (plus_com (VLst_to_X j)). constructor.
    Qed.
  
    Lemma VLSet_add: forall m q, equal (VLSet_to_X (VLSet.add m q)) (plus (VLSet_to_X q) (VLst_to_X m)).
    Proof.
      induction q as [|q1 q2 IH z Hz Hq] using VLSetProps.P.set_induction; unfold VLSet_to_X.
       rewrite (VLSetProps.P.fold_add _ Hpc Hpt) by setdec.
       rewrite VLSetProps.P.fold_1b by assumption.
       unfold fplus; simpl. symmetry. constructor. 
  
       destruct (VLSetProps.P.In_dec m q2) as [Hn|Hn].
        rewrite (VLSetProps.add_fold _ Hpc _ Hn).
        rewrite <- (VLSetProps.P.fold_equal _ Hpc Hpt _ (VLSetProps.P.add_remove Hn)).
        rewrite (VLSetProps.P.fold_add _ Hpc Hpt). (* by setdec. *)
        unfold fplus. destruct_tests; auto.
        rewrite <- plus_assoc, plus_idem; reflexivity.
        setdec.
        
        rewrite (VLSetProps.P.fold_add _ Hpc Hpt _ Hn).
        unfold fplus. destruct_tests; auto.
    Qed.
  
    Lemma VLSet_to_X_compat: forall i j, VLSet.eq i j -> equal (VLSet_to_X i) (VLSet_to_X j).
    Proof. intros. apply (VLSetProps.fold_equal _ Hpc). assumption. Qed.
  
  
  
    Lemma normalize_aux n: 
      (forall b a x y, 2*size x + size y < n -> 
        equal 
        (plus (VLSet_to_X b) (dot (dot (VLst_to_X a) x) y))
        (VLSet_to_X (norm_aux n b a x y)))%nat
      /\
      (forall b a y, size y < n ->
        equal 
        (plus (VLSet_to_X b) (dot (VLst_to_X a) y))
        (VLSet_to_X (norm_aux' n b a y)))%nat.
    Proof.
      induction n; split; intros; try elim (lt_n_O _ H); 
        destruct IHn as [IHnorm_aux IHnorm_aux'].
  
      (* norm_aux *)
      destruct x; simpl in *.
      rewrite dot_neutral_right; apply IHnorm_aux'; omega.
      rewrite dot_ann_right, dot_ann_left, plus_com; apply plus_neutral_left.
      rewrite <- IHnorm_aux, ! dot_assoc; trivial; simpl; omega.
      rewrite <- 2 IHnorm_aux, dot_distr_right, dot_distr_left; trivial; omega.
      rewrite <- IHnorm_aux'. rewrite VLst_add. reflexivity. omega.
  
      (* norm_aux' *)
      destruct y; simpl in *.
      rewrite dot_neutral_right. symmetry. apply VLSet_add. 
      rewrite dot_ann_right, plus_com; apply plus_neutral_left.
      rewrite <- IHnorm_aux, dot_assoc; trivial; omega.
      rewrite <- 2 IHnorm_aux', dot_distr_right; trivial; omega. 
      rewrite VLSet_add. rewrite VLst_add. reflexivity.
    Qed.
  
    (** correctness of the normalisation function  *)
    Lemma norm_correct: forall x, equal x (norm x).
    Proof.
      intro x; unfold norm, X_to_VLSet.
      rewrite <- (proj2 (normalize_aux _) _ _ _ (le_n _)).
      rewrite dot_neutral_left, plus_neutral_left; reflexivity.
    Qed.
  
    (** correctness of the decision function  *)
    Theorem decide_correct: forall x y, decide x y = true -> equal x y.
    Proof.
      intros x y H.
      transitivity (norm x); [ apply norm_correct | ].
      transitivity (norm y); [ | symmetry; apply norm_correct ].
      apply VLSet_to_X_compat.
      apply VLSet.equal_2.  
      assumption. 
    Qed.
  
  
    (** correctness of the cleaning functions  *)
    Lemma clean0_correct: forall x, equal x (clean0 x).
    Proof.
      induction x; simpl; auto; destruct_tests; auto.
      rewrite IHx1; trivial.
      rewrite IHx2; trivial.
      rewrite IHx1, <- IHx2; trivial.
      rewrite <- IHx1, IHx2; trivial.
      rewrite plus_com; trivial.
    Qed.    
  
    Lemma clean1_correct: forall x, equal x (clean1 x).
    Proof.
      induction x; simpl; auto; destruct_tests; auto.
      rewrite IHx1, <- IHx2; trivial.
      rewrite <- IHx1, IHx2; trivial.
    Qed.    
  
    Lemma clean_correct: forall x, equal x (clean1 (clean0 x)).
    Proof.
      intro. 
      rewrite <- clean1_correct.
      apply clean0_correct.
    Qed.
    
    Lemma cdot_correct: forall x a, equal (cdot a x) (dot a x).
    Proof. intros. unfold cdot. destruct_tests; auto. Qed.
  
    Lemma cplus_correct: forall x a, equal (cplus a x) (plus a x).
    Proof. intros. unfold cplus. destruct_tests; auto. Qed.
  
    Lemma lambda_and_l: forall T (P Q: T -> Prop), 
      (forall a, P a /\ Q a) -> forall a, P a.
    Proof. intros. destruct (H a). trivial. Qed.
  
    Lemma lambda_and_r: forall T (P Q: T -> Prop), 
      (forall a, P a /\ Q a) -> forall a, Q a.
    Proof. intros. destruct (H a). trivial. Qed.
  
    Lemma clean_assoc_aux: forall x a, 
      equal (plus a x) (clean_sum a x) /\ equal (dot a x) (clean_prod a x).
    Proof.
      induction x; simpl; intro a; split; 
        rewrite ?cdot_correct, ?cplus_correct; 
        try rewrite <- (lambda_and_r IHx2);
        try rewrite <- (lambda_and_l IHx2);
        try rewrite <- (lambda_and_r IHx1);
        try rewrite <- (lambda_and_l IHx1);
          auto.
      rewrite plus_com; auto.
    Qed.
  
    Lemma clean_assoc_correct: forall x, equal x (clean_sum zero (clean0 x)).
    Proof.
      intro. 
      rewrite <- (proj1 (clean_assoc_aux (clean0 x) zero)). 
      rewrite <- clean0_correct. 
      auto.
    Qed.
  
    
    (** preparation for the untyping theorem  *)
    Lemma clean0_idem: forall x, clean0 (clean0 x) = clean0 x.
    Proof.
      intro x; induction x; trivial; simpl.
      
      destruct_tests; trivial.
      simpl. rewrite IHx1, IHx2. destruct_tests; reflexivity.
  
      destruct_tests; trivial.
      simpl. rewrite IHx1, IHx2. destruct_tests; reflexivity.
    Qed.
  
    Lemma equal_clean_zero_equiv : forall x y, equal x y -> is_zero (clean0 x) = is_zero (clean0 y). 
    Proof.
      intros; induction H; simpl; destruct_tests; reflexivity. 
    Qed.
     
    Inductive sequal: X -> X -> Prop :=
    | sequal_refl_one: sequal one one
    | sequal_refl_zero: sequal zero zero
    | sequal_refl_var: forall i, sequal (var i) (var i)
      
    | sequal_dot_assoc: forall x y z, sequal (dot x (dot y z)) (dot (dot x y) z)
    | sequal_dot_neutral_left: forall x, sequal (dot one x) x
    | sequal_dot_neutral_right: forall x, sequal (dot x one) x
    | sequal_dot_distr_left: forall x y z, is_zero (clean0 z) = false -> sequal (dot (plus x y) z) (plus (dot x z) (dot y z))
    | sequal_dot_distr_right:  forall x y z, is_zero (clean0 x) = false -> sequal (dot x (plus y z)) (plus (dot x y) (dot x z))
  
    | sequal_plus_assoc: forall x y z, sequal (plus x (plus y z)) (plus (plus x y) z)
    | sequal_plus_idem: forall x, sequal (plus x x) x
    | sequal_plus_com: forall x y, sequal (plus x y) (plus y x)
  
    | sequal_dot_compat: forall x x', sequal x x' -> forall y y', sequal y y' -> sequal (dot x y) (dot x' y')
    | sequal_plus_compat: forall x x', sequal x x' -> forall y y', sequal y y' -> sequal (plus x y) (plus x' y')
    | sequal_trans: forall x y z, sequal x y -> sequal y z -> sequal x z
    | sequal_sym: forall x y, sequal x y -> sequal y x
        .
  
    Lemma sequal_equal x y: sequal x y -> equal x y .
    Proof.
      intros; induction H; solve [constructor; auto | eapply equal_trans; eauto].
    Qed.
  
    Lemma sequal_refl: forall x, sequal x x.
    Proof. 
      induction x; constructor; assumption.
    Qed.
    Hint Local Resolve sequal_refl.
    
    Lemma sequal_clean_zero_equiv x : sequal (clean0 x) zero -> is_zero (clean0 x) = true.
    Proof.
      intros; rewrite <- (clean0_idem x). apply sequal_equal in H.
      rewrite (equal_clean_zero_equiv H). reflexivity.
    Qed.
  
    Theorem equal_to_sequal : forall x y, equal x y -> sequal (clean0 x) (clean0 y).
    Proof.
      intros; induction H; simpl; trivial; destruct_tests; trivial; 
        solve 
          [ constructor; rewrite ? clean0_idem; trivial
          | rewrite (sequal_clean_zero_equiv IHequal1) in *; discriminate
          | rewrite (sequal_clean_zero_equiv IHequal2) in *; discriminate
          | rewrite (sequal_clean_zero_equiv (sequal_sym IHequal1)) in *; discriminate
          | rewrite (sequal_clean_zero_equiv (sequal_sym IHequal2)) in *; discriminate
          | econstructor; eauto
          ].
    Qed.

  End correctness.


  (** Erasure funciton, from typed syntax (reified) to the above untyped syntax *)
  Section erase.

    Context `{env: Reification.Env}.
    Import Reification.Semiring.

    (** erasure function, from typed syntax to untyped syntax *)
    Fixpoint erase n m (x: X n m): U.X :=
      match x with 
        | dot _ _ _ x y => U.dot (erase x) (erase y)
        | plus _ _ x y => U.plus (erase x) (erase y)
        | zero _ _ => U.zero
        | one _ => U.one
        | var i => U.var i
      end.

  End erase.


  (** Untyping theorem for semirings, to obtain reflexive typed tactics *)
  Section faithful.

    Import Reification Classes.
    Context `{ISR: IdemSemiRing} {env: Env}.
    Notation feval := Semiring.eval.

    Inductive eval: forall A B, U.X -> X (typ A) (typ B) -> Prop :=
    | e_one: forall A, @eval A A U.one 1
    | e_zero: forall A B, @eval A B U.zero 0
    | e_dot: forall A B C x y x' y', @eval A B x x' -> @eval B C y y' -> @eval A C (U.dot x y) (x'*y')
    | e_plus: forall A B x y x' y', @eval A B x x' -> @eval A B y y' -> @eval A B (U.plus x y) (x'+y')
    | e_var: forall i, eval (U.var i) (unpack (val i)).
    Implicit Arguments eval [].
    Hint Local Constructors eval.

    (** evaluation of erased terms *)
    Lemma eval_erase_feval: forall n m a, eval n m (erase a) (feval a).
    Proof. induction a; constructor; trivial. Qed.  
  
  
    (** inversion lemmas about evaluations  *)
    Lemma eval_dot_inv: forall n p u v c, eval n p (U.dot u v) c -> 
      exists m, exists a, exists b, c = a*b /\ eval n m u a /\ eval m p v b.
    Proof. intros. dependent destruction H. eauto 6. Qed.
  
    Lemma eval_one_inv: forall n m c, eval n m U.one c -> c [=] one (typ n) /\ n=m.
    Proof. intros. dependent destruction H. split; reflexivity. Qed.
 
    Lemma eval_plus_inv: forall n m x y z, eval n m (U.plus x y) z -> 
      exists x', exists y', z=x'+y' /\ eval n m x x' /\ eval n m y y'.
    Proof. intros. dependent destruction H. eauto. Qed.
  
    Lemma eval_zero_inv: forall n m z, eval n m U.zero z -> z=0. 
    Proof. intros. dependent destruction H. auto. Qed.
  
    Lemma eval_var_inv: forall n m i c, eval n m (U.var i) c -> c [=] unpack (val i) /\ n=src_p (val i) /\ m=tgt_p (val i).
    Proof. intros. dependent destruction H. intuition reflexivity. Qed.
 
    Ltac eval_inversion :=
      repeat match goal with 
               | H : eval _ _ ?x _ |- _ => eval_inversion_aux H x 
             end
      with eval_inversion_aux H x :=
        let H1 := fresh in
          match x with 
            | U.dot _ _ => destruct (eval_dot_inv H) as (?&?&?&H1&?&?); subst; try rewrite H1
            | U.one => destruct (eval_one_inv H) as [H1 ?]; auto; subst; apply eqd_inj in H1; subst
            | U.zero => pose proof (eval_zero_inv H); subst
            | U.plus _ _ => destruct (eval_plus_inv H) as (?&?&H1&?&?); auto; subst
            | U.var _ => destruct (eval_var_inv H) as (H1&?&?); auto; subst; apply eqd_inj in H1; subst
          end; clear H.
  

    Lemma eval_type_inj_left: forall A A' B x z z', 
      eval A B x z -> eval A' B x z' -> A=A' \/ clean0 x = U.zero.
    Proof.
      intros A A' B x z z' H; revert A' z'; induction H; intros A' z' H';
        eval_inversion; intuition.
      
      destruct (IHeval2 _ _ H3) as [HB | Hy].
       destruct HB.
       destruct (IHeval1 _ _ H2) as [HA | Hx]; auto.
       right; simpl. rewrite Hx. reflexivity.
       right; simpl. rewrite Hy. destruct_tests; reflexivity.
      
      destruct (IHeval2 _ _ H3) as [HB | Hy]; auto.
      destruct (IHeval1 _ _ H2) as [HA | Hx]; auto.
      right; simpl. rewrite Hx, Hy; simpl. reflexivity.
    Qed.

    Lemma eval_type_inj_right: forall A B B' x z z', eval A B x z -> 
      eval A B' x z' -> B=B' \/ clean0 x = U.zero.
    Proof.
      intros A B B' x z z' H; revert B' z'; induction H; intros B' z' H';
        eval_inversion; intuition.

      destruct (IHeval1 _ _ H2) as [HB | Hx].
       destruct HB.
       destruct (IHeval2 _ _ H3) as [HA | Hy]; auto.
       right; simpl. rewrite Hy. destruct_tests; reflexivity.
       right; simpl. rewrite Hx. reflexivity.
       
      destruct (IHeval2 _ _ H3) as [HB | Hy]; auto.
      destruct (IHeval1 _ _ H2) as [HA | Hx]; auto.
      right; simpl. rewrite Hx, Hy; simpl. reflexivity.
    Qed.

    Lemma eval_clean_zero: forall x A B z, eval A B x z -> is_zero (clean0 x) = true -> z==0.
    Proof.
      induction x; simpl; intros A B z Hz H; try discriminate; eval_inversion.
      reflexivity.

      case_eq (is_zero (clean0 x1)); intro Hx1. 
       rewrite (IHx1 _ _ _ H1 Hx1); apply dot_ann_left.
       case_eq (is_zero (clean0 x2)); intro Hx2.
        rewrite (IHx2 _ _ _ H2 Hx2); apply dot_ann_right.
        rewrite Hx1, Hx2 in H; discriminate.

      case_eq (is_zero (clean0 x1)); intro Hx1;
      case_eq (is_zero (clean0 x2)); intro Hx2;
       rewrite Hx1, Hx2, ?Hx1 in H; try discriminate.
       rewrite (IHx1 _ _ _ H1 Hx1), (IHx2 _ _ _ H2 Hx2); apply plus_idem.
    Qed.

    Lemma eval_clean: forall A B x y, eval A B x y -> exists2 z, eval A B (clean0 x) z & y==z.
    Proof.
      intros A B x y H; induction H; simpl.

      exists 1; auto.

      exists 0; auto.

      destruct_tests.
       exists 0; auto.
       destruct IHeval1 as [z Hz Hxz]; clear IHeval2.
       rewrite Hxz, (eval_zero_inv Hz); apply dot_ann_left.

       exists 0; auto.
       destruct IHeval2 as [z Hz Hyz]; clear IHeval1.
       rewrite Hyz, (eval_zero_inv Hz); apply dot_ann_right.

       destruct IHeval1; destruct IHeval2; eauto with compat.

      destruct_tests.
       destruct IHeval2 as [y'' Hy'' Hy]; exists y''; auto.
       destruct IHeval1 as [z Hz Hxz].
       rewrite Hxz, (eval_zero_inv Hz), Hy. apply plus_neutral_left.

       destruct IHeval1 as [y'' Hy'' Hy]; exists y''; auto.
       destruct IHeval2 as [z Hz Hxz].
       rewrite Hxz, (eval_zero_inv Hz), Hy. apply plus_neutral_right.

       destruct IHeval1; destruct IHeval2; eauto with compat.
             
      eexists; auto.
    Qed.


    Lemma eval_inj: forall A B x y z, eval A B x y -> eval A B x z -> y==z.
    Proof.
      intros A B x y z H; revert z; induction H; intros; eval_inversion; trivial.

      destruct (eval_type_inj_left H0 H4) as [HB | Hx].
       destruct HB.
       rewrite (IHeval1 _ H3), (IHeval2 _ H4); reflexivity.
       rewrite (eval_clean_zero H0), (eval_clean_zero H4) by (rewrite Hx; reflexivity).
       rewrite 2 dot_ann_right; reflexivity.

      rewrite (IHeval1 _ H3), (IHeval2 _ H4); reflexivity.
    Qed.

    Lemma and_idem: forall (A: Prop), A -> A/\A.
    Proof. tauto. Qed.

    Ltac split_IHeval :=
      repeat match goal with 
               | H: (forall A B x', eval A B ?x x' -> _) /\ _ ,
                 Hx: eval ?A ?B ?x ?x' |- _ => destruct (proj1 H _ _ _ Hx); clear H
               | H: _ /\ forall A B x', eval A B ?x x' -> _  ,
                 Hx: eval ?A ?B ?x ?x' |- _ => destruct (proj2 H _ _ _ Hx); clear H
             end;
      repeat match goal with 
               | H: (forall A B x', eval A B ?x x' -> _) 
                 /\ (forall A B y', eval A B ?y y' -> _) |- _ => destruct H
             end.
  
    Lemma eval_sequal: forall x y, sequal x y -> forall A B x', eval A B x x' -> 
      exists2 y', eval A B y y' & x'==y'.
    Proof.
      intros x y H.
      cut ((forall A B x', eval A B x x' -> exists2 y', eval A B y y' & x'==y')
              /\ (forall A B y', eval A B y y' -> exists2 x', eval A B x x' & y'==x')); [tauto| ].
      induction H; (apply and_idem || split); intros A B xe Hx; 
        eval_inversion; split_IHeval;
        eauto with algebra; eauto using Graph.equal_trans.

      (* dot_distr_left *)
      destruct (eval_type_inj_left H4 H5) as [HB | Hz]; [ destruct HB | rewrite Hz in H; discriminate ].
      eexists; eauto.
      rewrite (eval_inj H4 H5); symmetry; apply dot_distr_left.

      (* dot_distr_right *)
      destruct (eval_type_inj_right H2 H3) as [HB | Hz]; [ destruct HB | rewrite Hz in H; discriminate ].
      eexists; eauto.
      rewrite (eval_inj H3 H2); symmetry; apply dot_distr_right.

      (* plus idem *)
      eexists; eauto.
      rewrite (eval_inj H0 H1); apply plus_idem.
    Qed.
    
    (** untyping theorem  *)
    Theorem equal_eval: forall x' y', U.equal x' y'-> 
      forall A B x y, eval A B x' x -> eval A B y' y -> x==y.
    Proof.
      intros x' y' H A B x y Hx Hy.
      destruct (eval_clean Hx) as [x1 Hx1 Hx1'].
      destruct (eval_clean Hy) as [y1 Hy1 Hy1'].
      destruct (eval_sequal (equal_to_sequal H) Hx1) as [y2 Hy2 Hy2'].
      rewrite Hx1', Hy1', Hy2'.
      rewrite (eval_inj Hy2 Hy1).
      reflexivity.
    Qed.

    (* other formulation, using the intermediate reification syntax *)
    Theorem erase_faithful: forall n m (a b: Semiring.X n m), 
      U.equal (erase a) (erase b) -> feval a == feval b.
    Proof. intros. eapply equal_eval; eauto using eval_erase_feval. Qed.

    (* combination with the untyped decision procedure, to get the reflexive tactic *)
    Lemma decide_typed: forall n m (a b: Semiring.X n m), 
      decide (erase a) (erase b) = true -> feval a == feval b.
    Proof. intros. apply erase_faithful, decide_correct. assumption. Qed.

    (* for the semiring_normalize tactic *)
    Lemma normalizer {n} {m} {R} `{T: Transitive (Classes.X (typ n) (typ m)) R} `{H: subrelation _ (equal _ _) R} 
      norm (Hnorm: forall x, U.equal x (norm x)): 
      forall a b a' b',
        (* utiliser le prédicat d'évaluation permet d'éviter de repasser en OCaml 
           pour inventer le témoin typé... par contre, le terme de preuve grossit. *)
        (let na := norm (erase a) in eval n m na a') ->
        (let nb := norm (erase b) in eval n m nb b') ->
        R a' b' -> R (feval a) (feval b).
    Proof.
      intros until b'; intros Ha Hb Hab.
      transitivity a'.
       apply H. eapply equal_eval; eauto using eval_erase_feval. 
       rewrite Hab.
       apply H. symmetry. eapply equal_eval; eauto using eval_erase_feval. 
    Qed.

  End faithful.
  Implicit Arguments normalizer [[G] [Mo] [SLo] [ISR] [env] [n] [m] [R] [T] [H] norm a b].

End U.

(** the reflexive tactics for semirings  *)
Ltac semiring_reflexivity := 
  unfold leq; 
  semiring_reify; intros;
  apply U.decide_typed; vm_compute; 
    (reflexivity || fail "Not an idempotent semiring theorem").

Ltac semiring_normalize_ Hnorm :=
  let t := fresh "t" in
  let e := fresh "e" in
  let l := fresh "l" in
  let r := fresh "r" in
  let x := fresh "x" in
  let solve_eval :=
    intro x; vm_compute in x; subst x;
      repeat econstructor;
        match goal with |- U.eval (U.var ?i) _ => eapply (U.e_var (env:=e) i) end
  in
    semiring_reify; intros t e l r;
      eapply (U.normalizer Hnorm); 
        [ solve_eval | 
          solve_eval |
            compute [t e Reification.unpack Reification.val Reification.typ
              Reification.tgt Reification.src Reification.tgt_p Reification.src_p
              Reification.sigma_get Reification.sigma_add Reification.sigma_empty 
              FMapPositive.PositiveMap.find FMapPositive.PositiveMap.add 
              FMapPositive.PositiveMap.empty ] ];
        clear t e l r.

Ltac semiring_normalize  := semiring_normalize_ U.norm_correct.
Ltac semiring_clean      := semiring_normalize_ U.clean_correct.
Ltac semiring_cleanassoc := semiring_normalize_ U.clean_assoc_correct.

(*begintests
Section tests.
  Context `{ISR: IdemSemiRing}.
  Variable A B: T.
  Variables a b c: X A A.
  Variable f: X A A -> X A A.


  Goal 
    let z1 := a*(b+c+1*f a)*(1+(b+c)*0*a+c*1) in
    let z2 := (a*f a+a*c)*(c+1) + a*b*c+a*b in
      z1*z1*z1 == z2*z2*z2.
    intros; unfold z1, z2. 
(*     Time semiring_clean. *)
(*     Time semiring_cleanassoc. *)
(*     Time semiring_normalize.  *)
    Time semiring_reflexivity. 
  Qed.

  Goal a+a <== a.
    semiring_reflexivity.
    Show Proof.
  Qed.
  
  Goal a*1*b == 1*a*(b*(c+a)).
    semiring_normalize.
    admit.
    Show Proof.
  Qed.

  Require Import SemiLattice.
  Goal a*b == c*c -> c*a*(1+b+0)*(0*a+b+1)*a+0 == c*c*c*(1+b)*a+c*a*a.
    intro H.
    semiring_clean.
    semiring_normalize.
    monoid_rewrite H.
    semiring_cleanassoc.
    aac_reflexivity.
    Show Proof.
  Qed.
End tests.
endtests*)


(** Various properties about semirings  *)
Section Props.

  Context `{ISR: IdemSemiRing}.

  Global Instance dot_incr A B C: 
  Proper ((leq A B) ==> (leq B C) ==> (leq A C)) (dot A B C).
  Proof.
    unfold leq; intros x y E x' y' E'.
    rewrite <- E, <- E'; semiring_reflexivity.
  Qed.

  Lemma sum_distr_right A B C (x: X A B) (f: nat -> X B C) i k:
    x * sum i k f == sum i k (fun u => x * f u).
  Proof.
    revert i; induction k; intro i; simpl_sum_r.
    apply dot_ann_right.
    rewrite dot_distr_right, IHk. reflexivity.
  Qed.

  Lemma semi_invert_left A B C  (x : X B A) (x' : X A B) (a b: X A C) : 
    x'*x == 1 -> x*a == x*b -> a == b.
  Proof.
    intros.
    rewrite <- (dot_neutral_left a).
    rewrite <- (dot_neutral_left b).
    rewrite <- H.
    rewrite <- 2 dot_assoc.
    auto with compat.
  Qed.
  
  Lemma semi_invert_right A B C (x : X C B) (x' : X B C) (a b: X A C) : 
    x * x' == 1 -> a*x == b*x -> a == b.
  Proof.
    intros.
    rewrite <- (dot_neutral_right a).
    rewrite <- (dot_neutral_right b).
    rewrite <- H.
    rewrite 2 dot_assoc.
    auto with compat.
  Qed.

  Lemma dot_xif_zero: forall b c A B C (x: X A B) (y: X B C), xif b x 0 * xif c y 0 == xif (b&&c) (x*y) 0.
  Proof. intros [] []; simpl; trivial with algebra. Qed. 

End Props.

(** setoid_rewrite based normalisation tactic *)
Ltac r_semiring_clean :=
  repeat 
    lazymatch goal with 
|  |- context [0 * ?x] => setoid_rewrite dot_ann_left
|  |- context [?x * 0] => setoid_rewrite dot_ann_right
|  |- context [?x * 1] => setoid_rewrite dot_neutral_right
|  |- context [1 * ?x] => setoid_rewrite dot_neutral_left
|  |- context [0 + ?x] => setoid_rewrite plus_neutral_left
|  |- context [?x + 0] => setoid_rewrite plus_neutral_right
  
end.


(* typical proof by duality *)
Lemma sum_distr_left `{ISR: IdemSemiRing}: forall A B C (x: X B A) (f: nat -> X C B),
  forall i k, sum i k f * x == sum i k (fun u => f u * x).
Proof. exact (@sum_distr_right _ _ _ (@Dual.IdemSemiRing _ _ _ ISR)). Qed.


Hint Extern 2 (leq _ _ _ _) => first [ 
    apply dot_incr
]: compat algebra.


(*begintests
Goal forall `{ISR: IdemSemiRing} A (x y z: X A A), x+y<==z*z -> sum 6 8 (fun _ => (x+y)*z) <== z.
  intros.
  setoid_rewrite H.
Abort.

Goal forall `{KA: KleeneAlgebra} A (x y z: X A A), x+y==z*z -> sum 6 8 (fun _ => (x+y)*z) <== z#.
  intros.
  setoid_rewrite H.
Abort.
endtests*)


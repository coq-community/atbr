(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id$ i*)

Require        ListOrderedType.
Require        FSets.

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import Monoid.
Require Import SemiLattice.
Require        Quote.

Set Implicit Arguments.
Unset Strict Implicit.

(* cf. Structure.txt pour la politique *)
Hint Extern 0 (equal _ _ _ _) => first [ 
    apply dot_ann_left
  | apply dot_ann_right
  | apply dot_distr_left
  | apply dot_distr_right
]: algebra.

(* Hint Resolve @dot_ann_left @dot_ann_right @dot_distr_left @dot_distr_right: algebra. *)
Hint Rewrite @dot_ann_left @dot_ann_right using ti_auto: simpl.


(* semiring libre non typé engendré par [nat] *)
Module Free.
  Inductive X :=
  | one: X
  | zero: X
  | dot: X -> X -> X
  | plus: X -> X -> X
  | var: nat -> X
    .

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
  | equal_sym: forall x y, equal x y -> equal y x  
    .

  Hint Local Constructors equal.

  Lemma equal_refl: forall x, equal x x.
  Proof. induction x; auto. Qed.

  Hint Local Resolve equal_refl.

  Module VLst := ListOrderedType.Make OrderedTypeEx.Nat_as_OT.
  Module VLSet' := FSetList.Make VLst. (* FSetAVL *)
  Module FSetHide (X : FSetInterface.S).
    Include X.
  End FSetHide.
  Module VLSet := FSetHide VLSet'.

  Module VLSetProps := FSetProperties.OrdProperties VLSet.
  Module VLSetDec := FSetDecide.Decide VLSet.
  Ltac fsetdec := VLSetDec.fsetdec.

  Definition is_zero t := match t with zero => true | _ => false end.
  Definition is_one t := match t with one => true | _ => false end.

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

(*   Ltac replace_tests := *)
(*     repeat match goal with *)
(*              | H: is_zero ?x = true |- _ => rewrite (Is_zero H) in *; clear H *)
(*              | H: is_one  ?x = true |- _ => rewrite (Is_one  H) in *; clear H *)
(*            end. *)


  Section Protect.

  Add Relation X equal
    reflexivity proved by equal_refl
    symmetry proved by equal_sym
      transitivity proved by equal_trans
        as free_equal_setoid_relation.

  Instance dot_compat': Proper (equal ==> equal ==> equal) dot := dot_compat.
  Instance plus_compat': Proper (equal ==> equal ==> equal) plus := plus_compat.
  Typeclasses Opaque dot_compat' plus_compat'.

  Fixpoint norm_aux n b a x y := 
    (* equal b+a*x*y *)
    match n with 
      | 0 => VLSet.empty               (* cas jamais atteint *)
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
      | 0 => VLSet.empty               (* cas jamais atteint *)
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

  Let fdot i acc := if is_one acc then (var i) else dot acc (var i).
  Definition VLst_to_X m := List.fold_right fdot one m.

  Let fplus m acc := if is_zero acc then VLst_to_X m else plus acc (VLst_to_X m).
  Definition VLSet_to_X s := VLSet.fold fplus s zero.

  Definition norm p := VLSet_to_X (X_to_VLSet p).

(*begintests
  Goal norm (dot (var 0) (plus one (var 1))) =
    plus (var 0) (dot(var 0) (var 1)).
    reflexivity.
  Qed.
  
  Goal
    let x := (dot (var 0) (plus one (plus (var 1) (dot (plus (dot (var 2) one) (var 2)) (var 0))))) in
    let y := (plus (var 0) (plus (var 0) (plus x (dot (plus (dot (var 2) one) x) (var 0))))) in
    let z := dot (dot x y) (plus x (dot (plus zero x) y)) in
      let nz := norm z in True.
    Time vm_compute.
  Abort.
endtests*)



  Lemma VLst_add: forall i q, equal (VLst_to_X (List.cons i q)) (dot (VLst_to_X q) (var i)).
  Proof.
    simpl; unfold fdot; intros. destruct_tests; auto. 
  Qed.

  Let Hdc: SetoidList.compat_op (@eq nat) equal fdot.
  Proof. 
    intros i j x y H H'; subst; unfold fdot. destruct_tests; auto with compat.
     rewrite <- H'. symmetry; constructor.
     rewrite H'. constructor.
  Qed.

  Lemma VLst_to_X_compat: forall i j, VLst.eq i j -> equal (VLst_to_X i) (VLst_to_X j).
  Proof.
   intros i j H. unfold VLst_to_X. induction H; simpl.
    constructor.
    apply Hdc; trivial.
  Qed.

  Let Hpc: SetoidList.compat_op VLst.eq equal fplus.
  Proof. 
    intros i j H x y H'; unfold fplus.
    destruct_tests; rewrite (VLst_to_X_compat H); auto with compat.
     rewrite <- H'. symmetry; constructor.
     rewrite H'. constructor.
  Qed. 

  Let Hpt: SetoidList.transpose equal fplus.
  Proof.
    intros i j z. unfold fplus. destruct_tests; auto with compat.
     rewrite plus_com. auto.
     rewrite plus_com. auto.
     rewrite <- plus_assoc, (plus_com (VLst_to_X j)). constructor.
  Qed.

  Lemma VLSet_add: forall m q, equal (VLSet_to_X (VLSet.add m q)) (plus (VLSet_to_X q) (VLst_to_X m)).
  Proof.
    induction q as [|q1 q2 IH z Hz Hq] using VLSetProps.P.set_induction; unfold VLSet_to_X.
     rewrite (VLSetProps.P.fold_add _ Hpc Hpt) by fsetdec.
     rewrite VLSetProps.P.fold_1b by assumption.
     unfold fplus; simpl. symmetry. constructor. 

     destruct (VLSetProps.P.In_dec m q2) as [Hn|Hn].
      rewrite (VLSetProps.add_fold _ Hpc _ Hn).
      rewrite <- (VLSetProps.P.fold_equal _ Hpc Hpt _ (VLSetProps.P.add_remove Hn)).
      rewrite (VLSetProps.P.fold_add _ Hpc Hpt) by fsetdec.
      unfold fplus. destruct_tests; auto.
      rewrite <- plus_assoc, plus_idem; reflexivity.

      rewrite (VLSetProps.P.fold_add _ Hpc Hpt _ Hn).
      unfold fplus. destruct_tests; auto.
  Qed.

  Lemma VLSet_to_X_compat: forall i j, VLSet.eq i j -> equal (VLSet_to_X i) (VLSet_to_X j).
  Proof. intros. apply (VLSetProps.fold_equal _ Hpc). assumption. Qed.



  (* preuve de correction de la fonction auxiliaire de normalisation *)
  Lemma normalize_aux n: 
    (forall b a x y, 2*size x + size y < n -> 
      equal 
      (plus (VLSet_to_X b) (dot (dot (VLst_to_X a) x) y))
      (VLSet_to_X (norm_aux n b a x y)))
    /\
    (forall b a y, size y < n ->
      equal 
      (plus (VLSet_to_X b) (dot (VLst_to_X a) y))
      (VLSet_to_X (norm_aux' n b a y))).
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

  (* correction de la normalisation *)
  Lemma normalize: forall x, equal x (norm x).
  Proof.
    intro x; unfold norm, X_to_VLSet.
    rewrite <- (proj2 (normalize_aux _) _ _ _ (le_n _)).
    rewrite dot_neutral_left, plus_neutral_left; reflexivity.
  Qed.

  Lemma reflect: forall x y, VLSet.equal (X_to_VLSet x) (X_to_VLSet y) = true -> equal x y.
  Proof.
    intros x y H.
    transitivity (norm x); [ apply normalize | ].
    transitivity (norm y); [ | symmetry; apply normalize ].
    apply VLSet_to_X_compat.
    apply VLSet.equal_2.  
    assumption. 
  Qed.


(*
  (* fonction auxiliaire pour ci-dessous *)
  Fixpoint swap_aux x0 m x {struct m} : prod X X :=
    match m with
      | O => match x with 
                 | plus q y0 => pair y0 (plus q x0) 
                 | y0 => pair y0 x0 (* on est au dernier *)
               end
      | S m => match x with 
                 | plus q y0 => let (ym, q') := swap_aux x0 m q in pair ym (plus q' y0)
                 | _ => pair zero (plus x x0) (* n'importe quoi, tant que c'est correct... *)
               end
    end.

  (* échange des termes n et m d'une somme (associée à gauche, le comptage part de la droite, à 0) *)
  Fixpoint do_swap n m x :=
    match n,m,x with
      | O,S m,plus q x0 => let (ym, q') := swap_aux x0 m q in plus q' ym
      | S m,O,plus q x0 => let (ym, q') := swap_aux x0 m q in plus q' ym
      | S n,S m,plus q x0 => plus (do_swap n m q) x0
      | _,_,_ => x
    end.

  (* test *)
  Goal do_swap 1 3 (plus (plus (plus (plus (var 4) (var 3)) (var 2)) (var 1)) (var 0))
    = (plus (plus (plus (plus (var 4) (var 1)) (var 2)) (var 3)) (var 0)).
    reflexivity.
  Qed.

  Lemma swap_aux_corr: forall x0 m x, equal (plus (snd (swap_aux x0 m x)) (fst (swap_aux x0 m x))) (plus x x0).
  Proof.
    induction m; intros; simpl.
    destruct x; try apply plus_com; simpl.
    rewrite <- 2 plus_assoc, (plus_com x0); reflexivity.
    destruct x; try (rewrite plus_com; apply plus_neutral_left); simpl.
    specialize (IHm x1).
    destruct (swap_aux x0 m x1); simpl.
    rewrite (plus_com x1), <- (plus_assoc x2), <- IHm.
    rewrite (plus_com x3), plus_assoc; reflexivity.
  Qed.
  Lemma swap: forall m n x, equal x (do_swap m n x).
  Proof.
    induction m; intros [|n] x; simpl;
      reflexivity || (destruct x; try reflexivity).
    generalize (swap_aux_corr x2 n x1); destruct (swap_aux x2 n x1); simpl; intro H.
    symmetry; exact H.
    generalize (swap_aux_corr x2 m x1); destruct (swap_aux x2 m x1); simpl; intro H.
    symmetry; exact H.
    rewrite <- IHm; reflexivity.
  Qed.

*)

  (* [clean x] retire tous les zéros du terme [x] (sauf, éventuellement, le dernier...) *)
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

  Lemma clean0_corr: forall x, equal x (clean0 x).
  Proof.
    induction x; simpl; auto; destruct_tests; auto.
    rewrite IHx1; trivial.
    rewrite IHx2; trivial.
    rewrite IHx1, <- IHx2; trivial.
    rewrite <- IHx1, IHx2; trivial.
    rewrite plus_com; trivial.
  Qed.    

  (* [clean x] retire tous les uns triviaux du terme [x] *)
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

  Lemma clean1_corr: forall x, equal x (clean1 x).
  Proof.
    induction x; simpl; auto; destruct_tests; auto.
    rewrite IHx1, <- IHx2; trivial.
    rewrite <- IHx1, IHx2; trivial.
  Qed.    

  Lemma clean_corr: forall x, equal x (clean1 (clean0 x)).
  Proof.
    intro. 
    rewrite <- clean1_corr.
    apply clean0_corr.
  Qed.

  (* fonction de simplification des 1 et de normalisation des
     parenthèses.  la distributivité et l'idempotence ne sont pas
     appliquées ; les zeros qui annihilent sont enlevés par une
     première phase de clean0 *)
  Let cplus a x := if is_zero a then x else plus a x.
  Let cdot a x := if is_one a then x else dot a x.
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
  
  Lemma cdot_corr: forall x a, equal (cdot a x) (dot a x).
  Proof. intros. unfold cdot. destruct_tests; auto. Qed.

  Lemma cplus_corr: forall x a, equal (cplus a x) (plus a x).
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
      rewrite ?cdot_corr, ?cplus_corr; 
      try rewrite <- (lambda_and_r IHx2);
      try rewrite <- (lambda_and_l IHx2);
      try rewrite <- (lambda_and_r IHx1);
      try rewrite <- (lambda_and_l IHx1);
        auto.
    rewrite plus_com; auto.
  Qed.

  Lemma clean_assoc_corr: forall x, equal x (clean_sum zero (clean0 x)).
  Proof.
    intro. 
    rewrite <- (proj1 (clean_assoc_aux (clean0 x) zero)). 
    rewrite <- clean0_corr. 
    auto.
  Qed.

  End Protect.



  (** Préliminaires pour la preuve de fidélité du foncteur d'oubli des
     types: en `nettoyant' et en factorisant une preuve non typée, on
     peut reconstruire une preuve typée. 
     
     on est obligé de nettoyer les preuves, car les annihilateurs
     permettent d'introduire artificiellement des 'fausses' preuves:

     x = x+0 = x+0;y = x+0;y' = x = ... = x'

     même si x et x' sont bien typés, y et y' ne le sont pas forcément.
     on s'en sort car la preuve de y=y' ne sert à rien.

     On s'occuppe des histoires de typage hors du module [Free] (dans
     Props(M).FreeEval, plus bas) ; ici, on montre seulement comment
     les preuves non typées se factorisent.
  **)

  (* idempotence de [clean0] *)
  Lemma clean0_idem: forall x, clean0 (clean0 x) = clean0 x.
  Proof.
    intro x; induction x; trivial; simpl.
    
    destruct_tests; trivial.
    simpl. rewrite IHx1, IHx2. destruct_tests; reflexivity.

    destruct_tests; trivial.
    simpl. rewrite IHx1, IHx2. destruct_tests; reflexivity.
  Qed.

  (* deux termes égaux se nettoient en [zero] en même temps *)
  Lemma equal_clean_zero_equiv : forall x y, equal x y -> is_zero (clean0 x) = is_zero (clean0 y). 
  Proof.
    intros; induction H; simpl; destruct_tests; reflexivity. 
  Qed.
   
  
  (* on introduit une seconde égalité, `forte', sans annihilateurs
     (ces preuves n'introduisent donc pas de zéros - à part par
     sequal_refl_zero, mais ces zéros là sont traités comme des
     variables).
     
     Attention, l'ordre des constructeurs est important pour les preuves plus bas *)
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

  (* l'égalité forte l'est *)
  Lemma sequal_equal x y: sequal x y -> equal x y .
  Proof.
    intros; induction H; solve [constructor; auto | eapply equal_trans; eauto].
  Qed.

  (* elle est réflexive *)
  Lemma sequal_refl: forall x, sequal x x.
  Proof. 
    induction x; constructor; assumption.
  Qed.
  Hint Local Resolve sequal_refl.
  
  (* conséquence de [equal_clean_zero_equiv], utile pour les analyses de cas ci-dessous*)
  Lemma sequal_clean_zero_equiv x : sequal (clean0 x) zero -> is_zero (clean0 x) = true.
  Proof.
    intros; rewrite <- (clean0_idem x). apply sequal_equal in H.
    rewrite (equal_clean_zero_equiv H). reflexivity.
  Qed.

  (* lemme de factorisation: toute preuve d'égalité se réduit par nettoyage en une preuve d'égalité forte *)
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


End Free.



(* Module d'évaluation depuis [Free], le semiring libre non typé,
   afin d'obtenir [quote], puis des tactiques de normalisation par reflection. *)
Module FreeEval. 
Section Params.
  Context `{ISR: IdemSemiRing}.

  Section Env.
    (* graphe d'évaluation et de typage des variables *)
    Variables s t: nat -> T.
    Variable f: forall i, X (s i) (t i).

    (* prédicat d'évaluation *)
    Inductive eval: forall A B, Free.X -> X A B -> Prop :=
    | e_one: forall A, @eval A A Free.one 1
    | e_zero: forall A B, @eval A B Free.zero 0
    | e_dot: forall A B C x y x' y', @eval A B x x' -> @eval B C y y' -> @eval A C (Free.dot x y) (x'*y')
    | e_plus: forall A B x y x' y', @eval A B x x' -> @eval A B y y' -> @eval A B (Free.plus x y) (x'+y')
    | e_var: forall i, @eval (s i) (t i) (Free.var i) (f i).
    Implicit Arguments eval [].
    Hint Local Constructors eval.
  
    (* lemmes d'inversion du prédicat d'évaluation *)
    Lemma eval_dot_inv: forall A C x y z, eval A C (Free.dot x y) z -> 
      exists B, exists x', exists y', JMeq z (x'*y') /\ eval A B x x' /\ eval B C y y'.
    Proof.
      intros.
      dependent destruction H; intros; try discriminate.
      exists B; exists x'; exists y'; repeat split; assumption.
    Qed.
  
    Lemma eval_one_inv: forall A B z, eval A B Free.one z -> JMeq z (one A) /\ A=B. 
    Proof.
      intros.
      dependent destruction H; intros; try discriminate.
      split; reflexivity.
    Qed.
  
    Lemma eval_plus_inv: forall A B x y z, eval A B (Free.plus x y) z -> 
      exists x', exists y', z = x'+y' /\ eval A B x x' /\ eval A B y y'.
    Proof.
      intros.
      dependent destruction H; intros; try discriminate.
      exists x'; exists y'; repeat split; assumption.
    Qed.
  
    Lemma eval_zero_inv: forall A B z, eval A B Free.zero z -> z = zero A B.
    Proof.
      intros.
      dependent destruction H; intros; try discriminate; reflexivity.
    Qed.
  
    Lemma eval_var_inv: forall A B i z, eval A B (Free.var i) z -> JMeq z (f i) /\ A=s i /\ B=t i.
    Proof.
      intros.
      dependent destruction H; intros; try discriminate.
      repeat split; reflexivity.
    Qed.
 
    Ltac destruct_or_rewrite H := 
    (* c'est pas tres satisfaisant, mais un coup il faut faire destruct, un coup case, 
       un coup rewrite, et parfois subst...  *)
      subst; try ((rewrite H || case H); clear H).
  
    (* inversion récursive d'hypothèses d'évaluation *)
    Ltac eval_inversion :=
      repeat match goal with 
               | H : eval _ _ ?x _ |- _ => eval_inversion_aux H x 
             end
      with eval_inversion_aux hyp t :=
        let H1 := fresh in let H2 := fresh in
          match t with 
            | Free.one => destruct (eval_one_inv hyp) as [H1 H2]; destruct_or_rewrite H2; destruct_or_rewrite H1
            | Free.zero => rewrite (eval_zero_inv hyp)
            | Free.dot _ _ => destruct (eval_dot_inv hyp) as (?B & ?x & ?y & H1 & ?H & ?H); destruct_or_rewrite H1
            | Free.plus _ _ => destruct (eval_plus_inv hyp) as (?x & ?y & H1 & ?H & ?H); destruct_or_rewrite H1
            | Free.var _ => destruct (eval_var_inv hyp) as (H1 & ?H & ?H); destruct_or_rewrite H1
          end; clear hyp.
  

    (* semi-injectivité du typage de l'evalutation : pour les nettoyés seulement *)
    Lemma eval_type_inj_left: forall A A' B x z z', eval A B x z -> eval A' B x z' -> A=A' \/ Free.clean0 x = Free.zero.
    Proof.
      intros A A' B x z z' H; revert A' z'; induction H; intros A' z' H';
        eval_inversion; intuition.
      
      destruct (IHeval2 _ _ H3) as [HB | Hy].
       destruct HB.
       destruct (IHeval1 _ _ H2) as [HA | Hx]; auto.
       right; simpl. rewrite Hx. reflexivity.
       right; simpl. rewrite Hy. Free.destruct_tests; reflexivity.
      
      destruct (IHeval2 _ _ H3) as [HB | Hy]; auto.
      destruct (IHeval1 _ _ H2) as [HA | Hx]; auto.
      right; simpl. rewrite Hx, Hy; simpl. reflexivity.
    Qed.

    Lemma eval_type_inj_right: forall A B B' x z z', eval A B x z -> eval A B' x z' -> B=B' \/ Free.clean0 x = Free.zero.
    Proof.
      intros A B B' x z z' H; revert B' z'; induction H; intros B' z' H';
        eval_inversion; intuition.

      destruct (IHeval1 _ _ H2) as [HB | Hx].
       destruct HB.
       destruct (IHeval2 _ _ H3) as [HA | Hy]; auto.
       right; simpl. rewrite Hy. Free.destruct_tests; reflexivity.
       right; simpl. rewrite Hx. reflexivity.
       
      destruct (IHeval2 _ _ H3) as [HB | Hy]; auto.
      destruct (IHeval1 _ _ H2) as [HA | Hx]; auto.
      right; simpl. rewrite Hx, Hy; simpl. reflexivity.
    Qed.

    
    (* qui se nettoie en zero s'evalue en zero *)
    Lemma eval_clean_zero: forall x A B z, eval A B x z -> Free.is_zero (Free.clean0 x) = true -> z==0.
    Proof.
      induction x; simpl; intros A B z Hz H; try discriminate; eval_inversion.
      reflexivity.

      case_eq (Free.is_zero (Free.clean0 x1)); intro Hx1. 
       rewrite (IHx1 _ _ _ H1 Hx1); apply dot_ann_left.
       case_eq (Free.is_zero (Free.clean0 x2)); intro Hx2.
        rewrite (IHx2 _ _ _ H2 Hx2); apply dot_ann_right.
        rewrite Hx1, Hx2 in H; discriminate.

      case_eq (Free.is_zero (Free.clean0 x1)); intro Hx1;
      case_eq (Free.is_zero (Free.clean0 x2)); intro Hx2;
       rewrite Hx1, Hx2, ?Hx1 in H; try discriminate.
       rewrite (IHx1 _ _ _ H1 Hx1), (IHx2 _ _ _ H2 Hx2); apply plus_idem.
    Qed.

    (* le nettoyage préserve l'évaluation *)
    Lemma eval_clean: forall A B x y, eval A B x y -> exists2 z, eval A B (Free.clean0 x) z & y==z.
    Proof.
      intros A B x y H; induction H; simpl.

      exists 1; auto.

      exists 0; auto.

      Free.destruct_tests.
       exists 0; auto.
       destruct IHeval1 as [z Hz Hxz]; clear IHeval2.
       rewrite Hxz, (eval_zero_inv Hz); apply dot_ann_left.

       exists 0; auto.
       destruct IHeval2 as [z Hz Hyz]; clear IHeval1.
       rewrite Hyz, (eval_zero_inv Hz); apply dot_ann_right.

       destruct IHeval1; destruct IHeval2; eauto with compat.

      Free.destruct_tests.
       destruct IHeval2 as [y'' Hy'' Hy]; exists y''; auto.
       destruct IHeval1 as [z Hz Hxz].
       rewrite Hxz, (eval_zero_inv Hz), Hy. apply plus_neutral_left.

       destruct IHeval1 as [y'' Hy'' Hy]; exists y''; auto.
       destruct IHeval2 as [z Hz Hxz].
       rewrite Hxz, (eval_zero_inv Hz), Hy. apply plus_neutral_right.

       destruct IHeval1; destruct IHeval2; eauto with compat.
             
      exists (f i); auto.
    Qed.


    (* injectivité de l'évaluation (seulement modulo l'égalité, pour gérer les zeros 
       qui cachent des types différents) *)
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

    (* decomposition et utilisation automatique des hypotheses de recurrence, 
       pour la preuve suivante *)
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
  
    (* lemme préliminaire pour le théorème eval_equal: validité de l'égalité forte *)
    Lemma eval_sequal: forall x y, Free.sequal x y -> forall A B x', eval A B x x' -> exists2 y', eval A B y y' & x'==y'.
    Proof.
      intros x y H.
      cut ((forall A B x', eval A B x x' -> exists2 y', eval A B y y' & x'==y')
              /\ (forall A B y', eval A B y y' -> exists2 x', eval A B x x' & y'==x')); [tauto| ].
      induction H; (apply and_idem || split); intros A B xe Hx; 
        eval_inversion; split_IHeval;
        eauto with algebra; eauto using equal_trans.

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
    
        
    (* on conclut par injectivité de l'évaluation *)
    Theorem eval_equal: forall A B x' y' x y, eval A B x' x -> eval A B y' y -> Free.equal x' y' -> x==y.
    Proof.
      intros A B x' y' x y Hx Hy H.
      destruct (eval_clean Hx) as [x1 Hx1 Hx1'].
      destruct (eval_clean Hy) as [y1 Hy1 Hy1'].
      destruct (eval_sequal (Free.equal_to_sequal H) Hx1) as [y2 Hy2 Hy2'].
      rewrite Hx1', Hy1', Hy2'.
      apply (eval_inj Hy2 Hy1).
    Qed.

  End Env.

  Instance Quote: Quote.EVAL G := {
    X' := Free.X;
    var := Free.var;
    eval := eval
  }.
  Proof.
    intros; split; intro.
    apply eval_var_inv; assumption.
    intuition; subst; rewrite H0; constructor.
  Defined.
End Params.
End FreeEval.

Ltac semiring_reflexivity := abstract
  let G := get_Graph in
    Quote.quote (FreeEval.Quote (G:=G)) (FreeEval.eval_equal (G:=G));
      apply Free.reflect; vm_compute; (reflexivity || fail "Not a SemiRing theorem").

Ltac semiring_normalize :=
  lazymatch goal with 
    | |- @equal ?G ?A ?B _ _ =>
        Quote.reduce
        (FreeEval.Quote (G:=G))
        (SemiLattice.equal_normalizer 
          (E:=FreeEval.Quote (G:=G))
          (FreeEval.eval_equal (G:=G))
           Free.normalize)
    | |- @leq ?G ?SLo ?A ?B _ _ => 
        Quote.reduce
        (FreeEval.Quote (G:=G))
        (SemiLattice.leq_normalizer (SLo := SLo)
          (E:=FreeEval.Quote (G:=G))
          (FreeEval.eval_equal (G:=G))
           Free.normalize)
    | _ => fail "Not an (in)equality"
  end.

Ltac semiring_clean :=
  lazymatch goal with 
    | |- @equal ?G ?A ?B _ _ =>
        Quote.reduce
        (FreeEval.Quote (G:=G))
        (SemiLattice.equal_normalizer 
          (E:=FreeEval.Quote (G:=G))
          (FreeEval.eval_equal (G:=G))
           Free.clean_corr)
    | |- @leq ?G ?SLo ?A ?B _ _ => 
        Quote.reduce
        (FreeEval.Quote (G:=G))
        (SemiLattice.leq_normalizer (SLo := SLo)
          (E:=FreeEval.Quote (G:=G))
          (FreeEval.eval_equal (G:=G))
           Free.clean_corr)
    | _ => fail "Not an (in)equality"
  end.

Ltac semiring_cleanassoc :=
  lazymatch goal with 
    | |- @equal ?G ?A ?B _ _ =>
        Quote.reduce
        (FreeEval.Quote (G:=G))
        (SemiLattice.equal_normalizer 
          (E:=FreeEval.Quote (G:=G))
          (FreeEval.eval_equal (G:=G))
           Free.clean_assoc_corr)
    | |- @leq ?G ?SLo ?A ?B _ _ => 
        Quote.reduce
        (FreeEval.Quote (G:=G))
        (SemiLattice.leq_normalizer (SLo := SLo)
          (E:=FreeEval.Quote (G:=G))
          (FreeEval.eval_equal (G:=G))
           Free.clean_assoc_corr)
    | _ => fail "Not an (in)equality"
  end.

(*begintests
Section tests.
  Context `{ISR: IdemSemiRing}.
  Variable A B: T.
  Variables a b c: X A A.
  Variable f: X A A -> X A A.

  Goal 
    let z1 := a*(b+c+1*f a)*(1+(b+c)*0*a+c*1) in
    let z2 := (a*f a+a*c)*(c+1) + a*b*c+a*b in
      z1*z1 == z2*z2.
    intros.
(*     Time semiring_clean. *)
(*     Time semiring_cleanassoc. *)
(*     Time semiring_normalize.  *)
    Time semiring_reflexivity. 
    (* en fait, le temps est principalement passé dans Quote *)
  Qed.

(* benchmarks:
          z1     z1^2  z1^3  z1^4 

quote     0.5    1.10  1.77  2.55 
compute   0.001  0.03  0.27  2.66 
    
avec l'ancienne méthode (sans FSets): 

quote     0.560  1.20  1.9   2.7  
compute   0.003  0.04  0.7   19.  

*)

  Goal a+a <== a.
    semiring_reflexivity.
  Qed.
  
  Goal a*b == c*c -> c*a*(1+b+0)*(0*a+b+1)*a+0 == c*c*c*(1+b)*a+c*a*a.
    intro H.
    semiring_clean.
    semiring_normalize.
    monoid_rewrite H.
    assoc_normalize.
    aci_reflexivity.
  Qed.
End tests.
endtests*)

  (* TODO: faire les tactiques de groupage et d'isolation, etc... 

     peut-on faire une tactique de factorisation !?
      non : ab+ac+bc = a(b+c)+bc = ab+(a+b)c
      par contre, pour la récriture modulo A (par continuation), 
      on peut avoir envie de developper, reecrire, puis refactoriser:

      si H: forall q, q;b;c = q;t
      ((a+b);b);c -norm-> a;b;c+b;b;c -H-> a;t+b;t  -?-> (a+b);t

      ou encore, avec les résidus, où l'utilisateur donnerait le facteur

   *)

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
    rewrite dot_distr_right, IHk; reflexivity.
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


(*   Goal forall A  (a : X A A), a+a*1+a+0*a+1*a+0*1 == a. *)
(*     intros. *)
(*   r_semiring_clean. *)
(*   semiring_reflexivity. *)
(* Qed. *)

End Props.

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

Lemma sum_distr_left `{ISR: IdemSemiRing} A B C (x: X B A) (f: nat -> X C B):
  forall i k, sum i k f * x == sum i k (fun u => f u * x).
Proof.
apply (@sum_distr_right _ _ _ (@Dual.IdemSemiRing _ _ _ ISR) A B C x f).
Qed.

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


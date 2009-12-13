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
Require        Quote.
Set Implicit Arguments.
Unset Strict Implicit.

(* propriétés des algèbres de Kleene (typées) *)
Section Props0.

  Context `{KA: KleeneAlgebra}.

  Lemma star_destruct_right_old A B: forall (a: X A A) (b c: X B A), b+c*a <== c  ->  b*a# <== c.
  Proof.
    intros; transitivity (c*a#).
     rewrite <- H; semiring_reflexivity.
     apply star_destruct_right.
     rewrite <- H at -1; auto with algebra. 
  Qed.

  Lemma star_destruct_left_old A B: forall (a: X A A) (b c: X A B), b+a*c <== c  ->  a#*b <== c.
  Proof.
    intros; transitivity (a#*c).
     rewrite <- H; semiring_reflexivity.
     apply star_destruct_left.
     rewrite <- H at -1; auto with algebra. 
  Qed.

  Lemma star_destruct_right_one A: forall (a c: X A A), 1+c*a <== c  ->  a# <== c.
  Proof.
    intros. rewrite <- (dot_neutral_left (a#)).
    apply star_destruct_right_old. assumption.
  Qed.

  Lemma star_destruct_left_one A: forall (a c: X A A), 1+a*c <== c  ->  a# <== c.
  Proof.
    intros. rewrite <- (dot_neutral_right (a#)).
    apply star_destruct_left_old. assumption.
  Qed.

End Props0.

Ltac star_left_induction :=
  first [ apply star_destruct_left |
          apply star_destruct_left_old |
          apply star_destruct_left_one ].

Ltac star_right_induction :=
  first [ apply star_destruct_right |
          apply star_destruct_right_old |
          apply star_destruct_right_one ].


Section Props1.

  Context `{KA: KleeneAlgebra}.


  Global Instance star_incr A: 
  Proper ((leq A A) ==> (leq A A)) (star A).
  Proof.
    intros A a b H.
    star_right_induction.
    rewrite H. rewrite star_make_left. reflexivity.
  Qed.

  Global Instance star_compat A: Proper ((equal A A) ==> (equal A A)) (star A).
  Proof.
    intros A a b H. apply leq_antisym; apply star_incr; apply equal_leq; auto. 
  Qed.
  
  Lemma one_leq_star_a A (a: X A A): 1 <== a#.
  Proof.
    intros; rewrite <- star_make_left; auto with algebra. 
  Qed.

  Lemma a_leq_star_a A (a: X A A): a <== a#.
  Proof.
    intros; rewrite <- star_make_left.
    rewrite <- one_leq_star_a. 
    semiring_reflexivity.
  Qed.

  Lemma star_mon_is_one A (a: X A A): a <== 1 -> a# == 1.
  Proof.
    intros A a H.
    apply leq_antisym. 
    star_left_induction.
    rewrite H; semiring_reflexivity.
    apply one_leq_star_a.
  Qed.

  Lemma star_one A: (1#: X A A) == 1.
  Proof.
    intro; apply star_mon_is_one; reflexivity.
  Qed.
  
  Lemma star_zero A: (0#: X A A) == 1.
  Proof.
    intro; apply star_mon_is_one; apply zero_inf.
  Qed.

  Lemma star_a_a_leq_star_a A (a: X A A): a#*a <== a#.
  Proof.
    intros A a; rewrite <- star_make_left at 2.
    semiring_reflexivity.
  Qed.

  Lemma a_star_a_leq_star_a_a A (a: X A A): a*a# <== a#*a.
  Proof.
    intros A a.
    star_right_induction.
    rewrite star_a_a_leq_star_a at 1.
    apply plus_destruct_leq; auto.
    rewrite <- one_leq_star_a. monoid_reflexivity.
  Qed.

  Lemma star_make_right A (a:X A A): 1+a*a# == a#.
  Proof. 
    intros A a; apply leq_antisym.
    rewrite a_star_a_leq_star_a_a.
    apply plus_destruct_leq.
    apply one_leq_star_a.
    apply star_a_a_leq_star_a.

    star_right_induction.
    rewrite <- star_make_left at 2.
    semiring_reflexivity.
  Qed.
  
End Props1.

Ltac r_kleenealgebra_clean :=
  repeat   
    lazymatch goal with 
|  |- context [0 #] => setoid_rewrite star_zero
|  |- context [1 #] => setoid_rewrite star_one
|  |- context [?x * 0] => setoid_rewrite dot_ann_right
|  |- context [?x * 1] => setoid_rewrite dot_neutral_right
|  |- context [1 * ?x] => setoid_rewrite dot_neutral_left
|  |- context [0 + ?x] => setoid_rewrite plus_neutral_left
|  |- context [?x + 0] => setoid_rewrite plus_neutral_right
  
end.

Hint Extern 1 (equal _ _ _ _) => apply star_compat; instantiate: compat algebra.
Hint Extern 0 (equal _ _ _ _) => apply star_make_left: algebra.
Hint Extern 0 (equal _ _ _ _) => apply star_make_right: algebra.
Hint Extern 0 (leq _ _ _ _) => apply a_leq_star_a: algebra.
Hint Extern 0 (leq _ _ _ _) => apply one_leq_star_a: algebra.
Hint Extern 0 (leq _ _ _ _) => apply star_one: algebra.
Hint Extern 0 (leq _ _ _ _) => apply star_zero: algebra.

Hint Rewrite @star_zero @star_one using ti_auto : simpl.
Hint Rewrite @star_mon_is_one using ti_auto; mon_check : simpl.

(* algèbre de Kleene libre non typée engendrée par [nat] *)
Module Free.
  Inductive X :=
  | one: X
  | zero: X
  | dot: X -> X -> X
  | plus: X -> X -> X
  | star: X -> X
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

  | star_make_left: forall a, equal (plus one (dot (star a) a)) (star a)
  | star_make_right: forall a, equal (plus one (dot a (star a))) (star a)
  | star_destruct_left: forall a x, equal (plus (dot a x) x) x -> equal (plus (dot (star a) x) x) x
  | star_destruct_right: forall a x, equal (plus (dot x a) x) x -> equal (plus (dot x (star a)) x) x

  | dot_compat: forall x x', equal x x' -> forall y y', equal y y' -> equal (dot x y) (dot x' y')
  | plus_compat: forall x x', equal x x' -> forall y y', equal y y' -> equal (plus x y) (plus x' y')
  | star_compat: forall x x', equal x x' -> equal (star x) (star x')
  | equal_trans: forall x y z, equal x y -> equal y z -> equal x z
  | equal_sym: forall x y, equal x y -> equal y x  
    .

  Lemma equal_refl: forall x, equal x x.
  Proof. induction x; constructor; assumption. Qed.

  Definition is_zero t := match t with zero => true | _ => false end.

  Lemma Is_zero t : is_zero t = true -> t = zero.
  Proof. intro t; destruct t; simpl; intuition discriminate. Qed.

  Ltac destruct_tests := 
    repeat (
      repeat match goal with
               | H: is_zero ?x = _ |- _ => rewrite H in *
             end;
      repeat (simpl is_zero; match goal with 
               | |- context[is_zero ?x] => 
                 match x with 
                   | context[is_zero ?y] => fail 1
                   |  _ => let Z := fresh "Z" in 
                     case_eq (is_zero x); intro Z; try (rewrite (Is_zero Z) in *; clear Z)
                 end
             end);
      try discriminate).

  (* [clean x] retire tous les zéros du terme [x] (sauf, éventuellement, le dernier...) *)
  Fixpoint clean (x: X): X := 
    match x with
      | dot x y => 
        let x := clean x in
          let y := clean y in
            if is_zero x then zero
              else if is_zero y then zero
                else dot x y
      | plus x y => 
        let x := clean x in
          let y := clean y in
            if is_zero x then y
              else if is_zero y then x
                else plus x y
      | star x => 
        let x := clean x in 
          if is_zero x then one else star x
      | x => x
    end.

  (* idempotence de [clean] *)
  Lemma clean_idem: forall x, clean (clean x) = clean x.
  Proof.
    intro x; induction x; trivial; simpl; destruct_tests; trivial; simpl.
    rewrite IHx1, IHx2. destruct_tests. trivial.
    rewrite IHx1, IHx2. destruct_tests. trivial.
    rewrite IHx. destruct_tests. trivial.
  Qed.

  (* deux termes égaux se nettoient en [zero] en même temps *)
  Lemma equal_clean_zero_equiv : forall x y, equal x y -> is_zero (clean x) = is_zero (clean y). 
  Proof.
    intros; induction H; simpl; destruct_tests; trivial.
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
  | sequal_dot_distr_left: forall x y z, is_zero (clean z) = false -> sequal (dot (plus x y) z) (plus (dot x z) (dot y z))
  | sequal_dot_distr_right:  forall x y z,  is_zero (clean x) = false -> sequal (dot x (plus y z)) (plus (dot x y) (dot x z))

  | sequal_plus_assoc: forall x y z, sequal (plus x (plus y z)) (plus (plus x y) z)
  | sequal_plus_idem: forall x, sequal (plus x x) x
  | sequal_plus_com: forall x y, sequal (plus x y) (plus y x)

  | sequal_star_make_left: forall a, sequal (plus one (dot (star a) a)) (star a)
  | sequal_star_make_right: forall a, sequal (plus one (dot a (star a))) (star a)
  | sequal_star_destruct_left: forall a x, is_zero (clean x) = false -> sequal (plus (dot a x) x) x -> sequal (plus (dot (star a) x) x) x
  | sequal_star_destruct_right: forall a x, is_zero (clean x) = false -> sequal (plus (dot x a) x) x -> sequal (plus (dot x (star a)) x) x

  | sequal_dot_compat: forall x x', sequal x x' -> forall y y', sequal y y' -> sequal (dot x y) (dot x' y')
  | sequal_plus_compat: forall x x', sequal x x' -> forall y y', sequal y y' -> sequal (plus x y) (plus x' y')
  | sequal_star_compat: forall x x', sequal x x' -> sequal (star x) (star x')
  | sequal_trans: forall x y z, sequal x y -> sequal y z -> sequal x z
  | sequal_sym: forall x y, sequal x y -> sequal y x
      .

  (* l'égalité forte l'est *)
  Lemma sequal_equal x y: sequal x y -> equal x y .
  Proof.
    intros; induction H; try solve [constructor; auto ].
    eapply equal_trans; eauto.
  Qed.

  (* elle est réflexive *)
  Lemma sequal_refl: forall x, sequal x x.
  Proof. 
    induction x; constructor; assumption.
  Qed.
  Local Hint Resolve sequal_refl.
  Local Hint Constructors sequal.

  (* conséquence de [equal_clean_zero_equiv], utile pour les analyses de cas ci-dessous*)
  Lemma sequal_clean_zero_equiv x : sequal (clean x) zero -> is_zero (clean x) = true.
  Proof.
    intros; rewrite <- (clean_idem x). apply sequal_equal in H.
    rewrite (equal_clean_zero_equiv H). reflexivity.
  Qed.

  (* lemme de factorisation: toute preuve d'égalité se réduit par nettoyage en une preuve d'égalité forte *)
  Theorem equal_to_sequal : forall x y, equal x y -> sequal (clean x) (clean y).
  Proof.
    intros; induction H; simpl in *; trivial; destruct_tests; simpl; trivial;
      solve 
        [ constructor; rewrite ? clean_idem; trivial
        | match goal with H: sequal (clean _) zero |- _ => 
            rewrite (sequal_clean_zero_equiv H) in *; discriminate end
        | match goal with H: sequal zero (clean _) |- _ => 
            rewrite (sequal_clean_zero_equiv (sequal_sym H)) in *; discriminate end
        | econstructor; eauto
        ].
  Qed.

End Free.


  
(* Module d'évaluation depuis [Free], l'algèbre de Kleene libre non typée,
   afin d'obtenir [quote], puis la tactique de décision par réflection. *)
Module FreeEval. 
Section Params.

  Context `{KA: KleeneAlgebra}.

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
    | e_star: forall A x x', @eval A A x x' -> @eval A A (Free.star x) (x'#)
    | e_var: forall i, @eval (s i) (t i) (Free.var i) (f i).
    Implicit Arguments eval [].
    Hint Local Constructors eval.
  
    (* lemmes d'inversion du prédicat d'évaluation *)
    Lemma eval_dot_inv: forall A C x y z, eval A C (Free.dot x y) z -> 
      exists B, exists x', exists y', JMeq z (x'*y') /\ eval A B x x' /\ eval B C y y'.
    Proof. intros. dependent destruction H. eauto 6. Qed.
  
    Lemma eval_one_inv: forall A B z, eval A B Free.one z -> JMeq z (one A) /\ A=B. 
    Proof. intros. dependent destruction H. auto. Qed.
  
    Lemma eval_plus_inv: forall A B x y z, eval A B (Free.plus x y) z -> 
      exists x', exists y', z = x'+y' /\ eval A B x x' /\ eval A B y y'.
    Proof. intros. dependent destruction H. eauto. Qed.
  
    Lemma eval_zero_inv: forall A B z, eval A B Free.zero z -> z = 0.
    Proof. intros. dependent destruction H. auto. Qed.
  
    Lemma eval_star_inv: forall A B x z, eval A B (Free.star x) z ->  exists x', JMeq z (x'#) /\ eval A A x x' /\ A=B. 
    Proof. intros. dependent destruction H. eauto. Qed.

    Lemma eval_var_inv: forall A B i z, eval A B (Free.var i) z -> JMeq z (f i) /\ A=s i /\ B=t i.
    Proof. intros. dependent destruction H. auto. Qed.
 
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
            | Free.star _ => destruct (eval_star_inv hyp) as (?x & H1 & ?H & H2); destruct_or_rewrite H2; destruct_or_rewrite H1
            | Free.var _ => destruct (eval_var_inv hyp) as (H1 & ?H & ?H); destruct_or_rewrite H1
          end; clear hyp.
  

    (* semi-injectivité du typage de l'evalutation : pour les nettoyés seulement *)
    Lemma eval_type_inj_left: forall A A' B x z z', eval A B x z -> eval A' B x z' -> A=A' \/ Free.clean x = Free.zero.
    Proof.
      intros A A' B x z z' H; revert A' z'; induction H; intros A' z' H';
        eval_inversion; intuition.
      
      destruct (IHeval2 _ _ H3) as [HB | Hx]. destruct HB.
       destruct (IHeval1 _ _ H2) as [HA | Hy]; auto.
       right; simpl. rewrite Hy. reflexivity.
       right; simpl. rewrite Hx. Free.destruct_tests; reflexivity.
      
      destruct (IHeval2 _ _ H3) as [HB | Hx]; auto.
      destruct (IHeval1 _ _ H2) as [HA | Hy]; auto.
      right; simpl. rewrite Hx, Hy. reflexivity.
    Qed.

    Lemma eval_type_inj_right: forall A B B' x z z', eval A B x z -> eval A B' x z' -> B=B' \/ Free.clean x = Free.zero.
    Proof.
      intros A B B' x z z' H; revert B' z'; induction H; intros B' z' H';
        eval_inversion; intuition.

      destruct (IHeval1 _ _ H2) as [HB | Hx]. destruct HB.
       destruct (IHeval2 _ _ H3) as [HA | Hy]; auto.
       right; simpl. rewrite Hy. Free.destruct_tests; reflexivity.
       right; simpl. rewrite Hx. reflexivity.
       
      destruct (IHeval2 _ _ H3) as [HB | Hx]; auto.
      destruct (IHeval1 _ _ H2) as [HA | Hy]; auto.
        right; simpl. rewrite Hx, Hy. reflexivity.
    Qed.

    (* qui se nettoie en zero s'evalue en zero *)
    Lemma eval_clean_zero: forall x A B z, eval A B x z -> Free.is_zero (Free.clean x) = true -> z==0.
    Proof.
      induction x; simpl; intros A B z Hz H; try discriminate; eval_inversion.
      reflexivity.

      case_eq (Free.is_zero (Free.clean x1)); intro Hx1. 
       rewrite (IHx1 _ _ _ H1 Hx1); apply dot_ann_left.
       case_eq (Free.is_zero (Free.clean x2)); intro Hx2.
        rewrite (IHx2 _ _ _ H2 Hx2); apply dot_ann_right.
        rewrite Hx1, Hx2 in H; discriminate.

      case_eq (Free.is_zero (Free.clean x1)); intro Hx1;
      case_eq (Free.is_zero (Free.clean x2)); intro Hx2;
       rewrite Hx1, Hx2, ?Hx1 in H; try discriminate.
       rewrite (IHx1 _ _ _ H1 Hx1), (IHx2 _ _ _ H2 Hx2); apply plus_idem.

      case_eq (Free.is_zero (Free.clean x)); intro Hx; rewrite Hx in H; discriminate.
    Qed.
    
    (* le nettoyage préserve l'évaluation *)
    Lemma eval_clean: forall A B x y, eval A B x y -> exists2 z, eval A B (Free.clean x) z & y==z.
    Proof.
      intros A B x y H; induction H; simpl; try (eexists; [ eauto || fail |]); trivial.

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

      Free.destruct_tests.
       exists 1; auto.
       destruct IHeval as [z Hz Hxz]. rewrite Hxz. eval_inversion. apply star_zero.
       destruct IHeval as [x'' Hx'' Hx]; eauto with compat. 
    Qed.


    (* injectivité de l'évaluation (seulement modulo l'égalité, pour gérer les zeros 
       qui cachent des types différents) *)
    Lemma eval_inj: forall A B x y z, eval A B x y -> eval A B x z -> y==z.
    Proof.
      intros A B x y z H; revert z; induction H; intros; 
        eval_inversion; auto with compat. 

      destruct (eval_type_inj_left H0 H4) as [HB | Hx].
       destruct HB.
       rewrite (IHeval1 _ H3), (IHeval2 _ H4); reflexivity.
       rewrite (eval_clean_zero H0), (eval_clean_zero H4) by (rewrite Hx; reflexivity).
       rewrite 2 dot_ann_right; reflexivity.
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


    Ltac eval_injection :=
      repeat match goal with
               | H: eval ?A ?B ?x ?z , H': eval ?A ?B  ?x ?z' |- _ => rewrite (eval_inj H H') in *; clear H
(*                | H: eval ?A ?B ?x ?z , H': eval ?A ?B' ?x ?z' |- _ => idestruct (eval_type_inj_right H H') *)
(*                | H: eval ?A ?B ?x ?z , H': eval ?A' ?B ?x ?z' |- _ => idestruct (eval_type_inj_left H H') *)
             end.

    (* lemme préliminaire pour le théorème eval_equal: validité de l'égalité forte *)
    Lemma eval_sequal: forall x y, Free.sequal x y -> forall A B x', eval A B x x' -> exists2 y', eval A B y y' & x'==y'.
    Proof.
      intros x y H.
      cut ((forall A B x', eval A B x x' -> exists2 y', eval A B y y' & x'==y')
              /\ (forall A B y', eval A B y y' -> exists2 x', eval A B x x' & y'==x')); [tauto| ].
      induction H; (apply and_idem || split); intros A B xe Hx; 
        eval_inversion; try solve [split_IHeval; eexists; [eauto; fail | eval_injection; auto with algebra ]].

      (* dot_distr_left *)
      destruct (eval_type_inj_left H4 H5) as [HB | Hz]; [ destruct HB | rewrite Hz in H; discriminate ].
      eexists; eauto.
      rewrite (eval_inj H4 H5); symmetry; apply dot_distr_left.

      (* dot_distr_right *)
      destruct (eval_type_inj_right H2 H3) as [HB | Hz]; [ destruct HB | rewrite Hz in H; discriminate ].
      eexists; eauto.
      rewrite (eval_inj H3 H2); symmetry; apply dot_distr_right.

      (* star_destruct_left lr *)
      eexists; eauto. eval_injection.
      apply star_destruct_left; unfold leq. 
      destruct (proj1 IHsequal _ _ (x0*y+y)) as [ y1 ? Hy1 ]; auto.
      rewrite Hy1. eval_injection. reflexivity.

      (* star_destruct_left rl *)
      destruct (proj2 IHsequal _ _ _ Hx) as [ x' Hx' ].
      eval_inversion.
      destruct (eval_type_inj_left H4 H6) as [HB | Hz]; [ destruct HB | rewrite Hz in H; discriminate ].
      eexists; eauto. eval_injection.
      symmetry; apply star_destruct_left; unfold leq.
      symmetry; assumption.

      (* star_destruct_right lr *)
      eexists; eauto. eval_injection.
      apply star_destruct_right; unfold leq. 
      destruct (proj1 IHsequal _ _ (x1*x0+x1)) as [ y1 ? Hy1 ]; auto.
      rewrite Hy1. eval_injection. reflexivity.

      (* star_destruct_left rl *)
      destruct (proj2 IHsequal _ _ _ Hx) as [ x' Hx' ].
      eval_inversion.
      destruct (eval_type_inj_right H4 H5) as [HB | Hz]; [ destruct HB | rewrite Hz in H; discriminate ].
      eexists; eauto. eval_injection.
      symmetry; apply star_destruct_right; unfold leq.
      symmetry; assumption.

      (* sequal_trans *)
      split_IHeval; eauto using equal_trans.
      split_IHeval; eauto using equal_trans.
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


(* Algèbre de Kleene Duale *)
Module Dual. Section Protect.

  Instance KleeneAlgebra `{KA: KleeneAlgebra}: 
    @KleeneAlgebra Dual.Graph Dual.Monoid_Ops Dual.SemiLattice_Ops Dual.Star_Op.
  Proof.
    constructor.
    exact Dual.IdemSemiRing.
    exact (@star_make_right _ _ _ _ KA).
    exact (@star_destruct_right _ _ _ _ KA).
    exact (@star_destruct_left _ _ _ _ KA).
  Defined.

End Protect. End Dual.


Section Props2.
  Context `{KA: KleeneAlgebra}.
  
  Section tests_quote.
    Variables A B C: T.
    Variable a: X A B.
    Variable b: X B A.
    Variable c: X B C.
    Goal (a*b)# * a*c == a*(b*a)# *(c+c).
      Quote.quote (FreeEval.Quote (G:=G)) (FreeEval.eval_equal (G:=G)).
    Abort.
  End tests_quote.

  (* ci-dessous, les lemmes d'égalité pure devraient passer avec [kleene_reflexivity] *)

  Lemma star_trans: forall A (a:X A A), a#*a# == a#.
  Proof.
    intros; apply leq_antisym.
    star_right_induction.
    rewrite star_a_a_leq_star_a; aci_reflexivity.
    rewrite <- one_leq_star_a at 3; monoid_reflexivity.
  Qed.

  Lemma star_idem: forall A (a:X A A), a## == a#.
  Proof.
    intros A a; apply leq_antisym.
    star_right_induction.
    rewrite star_trans.
    rewrite (one_leq_star_a a); aci_reflexivity.
    apply a_leq_star_a.
  Qed.

  Lemma a_star_a_leq_star_a A: forall (a: X A A), a*a# <== a#.
  Proof star_a_a_leq_star_a (KA:=Dual.KleeneAlgebra).

  Lemma star_distr A: forall (a b : X A A), (a + b)# == a# * (b*a#)#.
  Proof.
    intros A a b; apply leq_antisym.

    star_left_induction.

    semiring_normalize.
    ac_rewrite (star_make_right (b*a#)).
    rewrite <- (star_make_right a) at 4.
    semiring_reflexivity.

    rewrite <- (star_trans (a+b)).
    apply dot_incr.
     apply star_incr; aci_reflexivity.
     rewrite <- (star_idem (a+b)). apply star_incr.
    rewrite <- (a_star_a_leq_star_a (a+b)).
    apply dot_incr. auto with algebra. 
    apply star_incr. auto with algebra.
  Qed.

  Lemma semicomm_iter_right: forall A B (a: X A A) (b: X B B) (c: X B A), c*a <== b*c -> c*a# <== b#*c.
  Proof.
    intros A B a b c H.
    star_right_induction.
    monoid_rewrite H.
    rewrite <- star_make_left at 2.
    semiring_reflexivity.
  Qed.

  Lemma wsemicomm_iter_right A: forall (a b : X A A), a*b <== b#*a  ->  a*b# <== b#*a.
  Proof.
    intros A a b H.
    rewrite <- star_idem at 2.
    apply semicomm_iter_right; assumption. 
  Qed.
   
End Props2.

Section Props3.
  Context `{KA: KleeneAlgebra}.
  
  Lemma semicomm_iter_left A B: forall (a: X A A) (b: X B B) (c: X A B), a*c <== c*b -> a#*c <== c*b#.
  Proof semicomm_iter_right (KA:=Dual.KleeneAlgebra).

  Lemma wsemicomm_iter_left A: forall (b a : X A A), a*b <== b*a#  ->  a#*b <== b*a#.
  Proof wsemicomm_iter_right (KA:=Dual.KleeneAlgebra).

  Lemma comm_iter_left A B (x : X A B) a b :  a * x == x * b -> a# * x == x * b# .
  Proof.
    intros.
    apply leq_antisym.
    apply semicomm_iter_left, equal_leq. trivial.
    apply semicomm_iter_right, equal_leq. auto. 
  Qed.

  
  (** * These two lemmas can also be found in the Commutation file *)
  Lemma move_star A: forall (a: X A A), a#*a == a*a#.
  Proof. intros. apply comm_iter_left; reflexivity. Qed.

  Lemma move_star2 A B: forall (a: X A B) (b: X B A), (a*b)#*a == a*(b*a)#.
  Proof. intros. apply comm_iter_left. semiring_reflexivity. Qed.

End Props3.

Section Props4.
  Context `{KA: KleeneAlgebra}.
  
  Lemma comm_iter_right B A (x : X A B) a b :  x * a == b * x -> x * a# == b# * x .
  Proof comm_iter_left (KA:=Dual.KleeneAlgebra).

End Props4.

Hint Extern 1 (leq _ _ _ _) => apply star_incr: compat algebra.
Hint Extern 0 (equal _ _ _ _) => apply star_idem: algebra.
Hint Extern 0 (equal _ _ _ _) => apply star_trans: algebra.


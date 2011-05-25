(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Definition of the "strict star form" property for regular expressions, 
    together with an algorithm to put any regex into a strict star form one.


    Proof of correctness and completeness.
    Definition of the corresponding [kleene_ssf] tactic.
   *)

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import SemiLattice.
Require Import Monoid.
Require Import SemiRing.
Require Import KleeneAlgebra.
Require Import Model_RegExp. 
        Import RegExp.Load.
Require        Reification.

Require Import Bool. Open Scope lazy_bool_scope.


(* A regexp is [strict] if it does not accept the empty word *)
Inductive strict: regex -> Prop := 
| strict_zero: strict 0
| strict_var: forall i, strict (RegExp.var i)
| strict_plus: forall a b, strict a -> strict b -> strict (a+b)
| strict_dot_l: forall a b, strict a -> strict (a*b)
| strict_dot_r: forall a b, strict b -> strict (a*b).


(* Conversely, a regexp is [non_strict] if it does accept the empty word *)
Inductive non_strict: regex -> Prop := 
| non_strict_one: non_strict 1
| non_strict_star: forall a, non_strict (a#)
| non_strict_dot: forall a b, non_strict a -> non_strict b -> non_strict (a*b)
| non_strict_plus_l: forall a b, non_strict a -> non_strict (a+b)
| non_strict_plus_r: forall a b, non_strict b -> non_strict (a+b).

Lemma non_strict_not_strict: forall a, non_strict a -> ~ strict a.
Proof. induction 1; intro Ha; inversion_clear Ha; auto. Qed.


(* A regexp is [in_star_normal_form] if all stared sub-terms are strict *)
Inductive strict_star_form: regex -> Prop := 
| ssf_zero: strict_star_form 0
| ssf_one: strict_star_form 1
| ssf_var: forall i, strict_star_form (RegExp.var i)
| ssf_star: forall a, strict_star_form a -> strict a -> strict_star_form (a#)
| ssf_plus: forall a b, strict_star_form a -> strict_star_form b -> strict_star_form (a+b)
| ssf_dot: forall a b, strict_star_form a -> strict_star_form b -> strict_star_form (a*b).

(* The function [rewrite] below converts a regexp into an equivalent one, in star normal form *)

Fixpoint contains_one e : bool :=
  match e with 
    | RegExp.star a => true
    | RegExp.one => true
    | RegExp.plus a b => contains_one a ||| contains_one b
    | RegExp.dot a b => contains_one a &&& contains_one b
    | e => false
  end.

Definition plus_but_one a b := 
  if RegExp.is_one a then b 
    else if RegExp.is_one b then a
      else RegExp.plus a b.

Fixpoint remove e :=
  if contains_one e then 
    match e with
      | RegExp.plus a b => plus_but_one (remove a) (remove b)
      | RegExp.dot a b =>  plus_but_one (remove a) (remove b)
      | RegExp.star e => e
      | e => e 
    end
    else e.

Definition dot' a b := 
  if RegExp.is_one a then b 
    else if RegExp.is_one b then a
      else RegExp.dot a b.

Definition star' a :=
  if RegExp.is_one a then RegExp.one else RegExp.star a.

Fixpoint ssf e := 
  match e with 
    | RegExp.plus a b => RegExp.plus (ssf a) (ssf b)
    | RegExp.dot a b => dot' (ssf a) (ssf b)
    | RegExp.star e => star' (remove (ssf e))
    | e => e
  end.

Lemma star_plus_one: forall a: regex, (1+a)# == a#.
Proof.
  intros.
  rewrite star_distr, star_one, dot_neutral_right, dot_neutral_left. reflexivity.
Qed.

Lemma star_plus_star_1: forall a b: regex, (a+b)# == (a#+b)#.
  intros.
  setoid_rewrite star_distr. setoid_rewrite star_idem. reflexivity.
Qed.

Lemma star_plus_star: forall a b: regex, (a+b)# == (a#+b#)#.
Proof.
  intros.
  rewrite star_plus_star_1. rewrite plus_com. rewrite star_plus_star_1. rewrite plus_com. reflexivity.
Qed.

Lemma star_plus_but_one: forall a b: regex, (plus_but_one a b) # == (a + b)#.
Proof. 
  intros.
  unfold plus_but_one; RegExp.destruct_tests; fold_regex.
  rewrite star_plus_one. reflexivity.
  rewrite plus_com. rewrite star_plus_one. reflexivity.
  reflexivity.
Qed.

Lemma star'_star: forall a: regex, star' a == a# .
Proof.
  intros; unfold star'; RegExp.destruct_tests; fold_regex; auto with algebra.
Qed.

Lemma dot'_dot: forall a b: regex, dot' a b == a * b.
Proof.
  intros; unfold dot'; RegExp.destruct_tests; fold_regex; auto with algebra. 
Qed.  
  

Lemma contains_one_correct: forall a: regex, contains_one a = true -> a == a + 1.
Proof.
  intros.
  induction a; simpl in H; fold_regex. 
   auto with algebra.

   discriminate.
 
   destruct (contains_one a1). 2:discriminate.
   rewrite IHa1 by trivial.
   rewrite IHa2 by trivial.
   semiring_reflexivity.
  
   destruct (contains_one a1). 
    rewrite IHa1 by trivial. semiring_reflexivity.
    rewrite IHa2 by trivial. semiring_reflexivity.

   rewrite <- star_make_left. semiring_reflexivity.
         
   discriminate.
Qed.

Lemma star_dot_leq_star_plus: forall a b: regex, (a*b)# <== (a+b)#.
  intros a b. 
  (* TODO: debug very slow typeclass resolution... *)
  rewrite plus_com, star_distr. 
  transitivity (1*(a*b#)#); [rewrite dot_neutral_left|]; auto with algebra.
Qed.
  
Lemma star_plus_star_dot: forall a b: regex, 
  contains_one a = true -> contains_one b = true -> (a+b)# == (a*b)#.
Proof.
  intros.
  rewrite (contains_one_correct a), (contains_one_correct b); trivial.
  apply leq_antisym.
   apply star_incr. semiring_reflexivity.
   apply star_dot_leq_star_plus.
Qed.
  

Lemma star_remove: forall a: regex, remove a # == a #.
Proof.
  induction a; simpl; fold_regex; auto with algebra.
  case_eq (contains_one a1); intro Ha1; trivial.
  case_eq (contains_one a2); intro Ha2; trivial. 
  rewrite star_plus_but_one.
  rewrite star_plus_star. rewrite IHa1, IHa2. rewrite <- star_plus_star.
  apply star_plus_star_dot; assumption.
  
  case (contains_one a1 ||| contains_one a2); trivial.
  rewrite star_plus_but_one.
  rewrite star_plus_star. rewrite IHa1, IHa2. 
  symmetry. apply star_plus_star.
Qed.
  

(** correctness of the rewriting procedure *)
Theorem ssf_correct: forall a: regex, ssf a == a.
Proof.
  induction a; trivial; simpl; fold_regex; auto with compat.
  rewrite dot'_dot. auto with compat. 
  rewrite star'_star. rewrite star_remove. auto with compat.
Qed.  


(** tactic to put Kleene algebra expressions into strict star form *)
Theorem ssf_correct': forall e, RegExp.equal e (ssf e). 
Proof. intros. apply RegExp.equal_sym, ssf_correct. Qed.
Ltac kleene_ssf := kleene_normalize_ ssf_correct'.

(*
  Section test.
    Context `{KA: KleeneAlgebra}.
    Goal forall A (a b: X A A), (a*1)#*b == b+(a+1)#+b*1#.
      intros. kleene_ssf. 
    Abort.
    Goal forall A (a b: X A A), (a#+b)# <== b+((a+1)*b#)#.
      intros. kleene_ssf.
    Abort.
  End test.
*)

(** below: completeness of the rewriting procedure *)

Local Hint Constructors strict_star_form.
Local Hint Constructors strict.

Lemma remove_nf: forall a, strict_star_form a -> strict_star_form (remove a).
Proof.
  induction 1; simpl; auto. 

   unfold plus_but_one. 
   case_eq (contains_one a); intro Ha; simpl.
   RegExp.destruct_tests; auto. 
   case_eq (contains_one b); intro Hb; simpl; auto.
   RegExp.destruct_tests; auto. 

   unfold plus_but_one. 
   case_eq (contains_one a); intro Ha; simpl.
   case_eq (contains_one b); intro Hb; simpl; auto.
   RegExp.destruct_tests; auto. 
   RegExp.destruct_tests; auto.  
Qed.

Lemma contains_one_false_strict: forall a, contains_one a = false -> strict a.
Proof.
  induction a; simpl; intro Ha; try discriminate; auto.
  destruct (contains_one a1); auto. 
  destruct (contains_one a1); auto. discriminate.
Qed.
Local Hint Resolve contains_one_false_strict.

Lemma remove_strict: forall a, strict_star_form a -> RegExp.is_one (remove a) = false -> strict (remove a).
Proof.
  induction 1; simpl; auto.

   unfold plus_but_one.
   case_eq (contains_one a); intro Ha; simpl.
   RegExp.destruct_tests; auto.
   case_eq (contains_one b); intro Hb; simpl; auto.
   RegExp.destruct_tests; auto.

   unfold plus_but_one.
   case_eq (contains_one a); intro Ha; simpl; auto.
   case_eq (contains_one b); intro Hb; simpl; auto.
   RegExp.destruct_tests; auto.  
Qed.

(** completeness of the rewriting procedure *)
Theorem ssf_complete: forall a, strict_star_form (ssf a).
Proof.
  induction a; simpl; auto.
   unfold dot'. RegExp.destruct_tests; auto. 
   unfold star'. RegExp.destruct_tests; auto.
   constructor.
    apply remove_nf; trivial.
    apply remove_strict; trivial.
Qed.

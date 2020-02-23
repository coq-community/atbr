(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** This module aggregates all DKA_* modules, to obtain the decision
    procedure for Kleene algebras [kleene_reflexivity]. *)


Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import Converse.
Require Import DKA_Definitions.
Require        DKA_CheckLabels.
Require        DKA_Construction.
Require        DKA_Epsilon.
Require        DKA_Determinisation.
Require        DKA_Merge.
Require        DKA_DFA_Equiv. 
Require        StrictStarForm.
Require        Reification.

Require Import List.

Definition word := list positive.
Inductive CounterExample: Set :=
| NotLeq: word -> CounterExample
| NotGeq: word -> CounterExample
| DifferentAtomSets: CounterExample.


Definition X_to_DFA (a: regex) := 
  let a' := StrictStarForm.ssf a in
  let A  := DKA_Construction.X_to_eNFA a' in
  let A  := DKA_Epsilon.eNFA_to_NFA A (DKA_Construction.well_founded (StrictStarForm.ssf_complete a)) in
  let A  := DKA_Determinisation.NFA_to_DFA A in
      A.

Definition translate_ce (ce: option (bool*word)) := 
  match ce with
    | None => None
    | Some(b,w) => Some ((if b then NotLeq else NotGeq) (List.rev w))
  end.

Notation clean := RegExp.Clean.rewrite.

Definition decide_kleene a b :=
  let a := clean a in
  let b := clean b in
    if negb (DKA_CheckLabels.same_labels a b) then Some DifferentAtomSets
    else translate_ce (DKA_Merge.compare_DFAs DKA_DFA_Equiv.equiv (X_to_DFA a) (X_to_DFA b)).

Lemma X_to_DFA_correct: forall a, DFA.eval (X_to_DFA a) == a.
Proof.
  intro a. unfold X_to_DFA. 
  rewrite DKA_Determinisation.correct by apply DKA_Epsilon.bounded, DKA_Construction.bounded.
  rewrite DKA_Epsilon.correct by apply DKA_Construction.bounded.
  rewrite DKA_Construction.correct.
  apply StrictStarForm.ssf_correct.
Qed.

Lemma X_to_DFA_bounded: forall a, DFA.bounded (X_to_DFA a).
Proof.
  intro a. apply DKA_Determinisation.bounded, DKA_Epsilon.bounded, DKA_Construction.bounded.
Qed.

Lemma X_to_DFA_labels: forall a b, 
  DKA_CheckLabels.same_labels (clean a) (clean b) = true -> 
  DFA.max_label (X_to_DFA (clean a)) = DFA.max_label (X_to_DFA (clean b)).
Proof.
  intros. unfold X_to_DFA. 
  rewrite 2 DKA_Determinisation.preserve_max_label.
  rewrite 2 DKA_Epsilon.preserve_max_label.
  apply DKA_Construction.same_labels_max_label.
  apply DKA_CheckLabels.same_labels_ssf.
  assumption.
Qed.


Lemma translate_correct: forall ce, translate_ce ce = None <-> ce = None.
Proof. intros [[b w]|]; simpl; intuition discriminate. Qed.


Theorem Kozen94: forall a b, decide_kleene a b = None <-> a == b.
Proof.
  unfold decide_kleene. intros a b.
  case_eq (DKA_CheckLabels.same_labels (clean a) (clean b)); simpl; intros Hm. 

   rewrite translate_correct.
   rewrite DKA_Merge.correct; try apply X_to_DFA_bounded.
    setoid_rewrite X_to_DFA_correct.
    setoid_rewrite <- RegExp.Clean.correct.
    reflexivity.
    apply DKA_DFA_Equiv.correct.
    apply X_to_DFA_labels, Hm.

   split; intro H.
    discriminate H.
    exfalso. apply DKA_CheckLabels.complete in Hm. tauto.
Qed.

(* Print Assumptions Kozen94. *)

Import RegExp.Untype.
Import Reification.

Corollary dk_erase_correct `{KA: KleeneAlgebra} {env: Env}: 
  forall n m (a b: KA.X n m), decide_kleene (erase a) (erase b) = None -> KA.eval a == KA.eval b.
Proof. intros. apply erase_faithful. apply Kozen94. assumption. Qed.
        

Ltac display_counter_example e ce :=
  let eval_word w :=
    let rec build w :=
      lazymatch w with
      | nil => fail 0
      | ?x::nil => constr:(Reification.unpack (@Reification.val _ e x))
      | ?x::?q => let q := build q in constr:(q * Reification.unpack (@Reification.val _ e x))
      end
    in 
    let x := build w in 
    let x := eval compute [e Reification.unpack Reification.tgt Reification.src
      Reification.sigma_get Reification.sigma_add Reification.sigma_empty 
      FMapPositive.PositiveMap.find FMapPositive.PositiveMap.add 
      FMapPositive.PositiveMap.empty Reification.val] in x
    in x
  in
  match ce with
    | DifferentAtomSets => fail 1 "Not a Kleene algebra theorem: different atom sets"
    | NotGeq ?w => 
      (try let u := eval_word w in 
        fail 2 "Not a Kleene Algebra theorem: " u "does not belong to the left-hand side");
      fail 1 "Not a Kleene Algebra theorem: the empty word (1) does not belong to the left-hand side"
    | NotLeq ?w => 
      (try let u := eval_word w in 
        fail 2 "Not a Kleene Algebra theorem: " u "does not belong to the right-hand side");
      fail 1 "Not a Kleene Algebra theorem: the empty word (1) does not belong to the right-hand side"
  end.


(** the tactic for solving Kleene algebras equations *)
Ltac kleene_reflexivity := 
  let e := fresh "e" in
  unfold leq; 
  kleene_reify; intros t e l r;
  apply dk_erase_correct; vm_compute; 
  (reflexivity || lazymatch goal with |- Some ?w = None => display_counter_example e w end).

(** extension to Kleene algebras with converse *)
Ltac ckleene_reflexivity := converse_down; kleene_reflexivity.


Ltac kleene_ssf := StrictStarForm.kleene_ssf.
Ltac kleene_clean_zeros := Model_RegExp.kleene_clean_zeros.


(*begintests
Section test.

  Context `{KA: KleeneAlgebra}.

  Goal forall A B (a: X A B) (b: X B A), a*(b*a)# == (a*b)#*a.
    intros.
    Time kleene_reflexivity.
  Abort.

  Goal forall A (a b: X A A), (a+b)# == a#*(b*a#)#.
    intros.
    Time kleene_reflexivity.
  Abort.

  Goal forall A (a b: X A A), a*b# + a#*b# == a#*b#.
    intros.
    Time kleene_reflexivity.
  Abort.

  Goal forall A B (a c: X A B) (b: X B A), (a+c)*(b*a+b*c)# == (a*b+c*b)#*(a+c).
    intros.
    Time kleene_reflexivity.
  Abort.

  Goal forall A (a b: X A A), (a*b)# == (a+b)# .
    intros. 
    try kleene_reflexivity.
    idtac.
  Abort.

  Goal forall A B (a: X A B) (b: X B A), a*(b*a) == (a*b)#*a .
    intros. 
    try kleene_reflexivity.
    idtac.
  Abort.

  Goal forall A B (a: X A B) (b: X B A), a*b*a*b == a*b + a*b*a*b .
    intros. 
    try kleene_reflexivity.
    idtac.
  Abort.

  Goal forall A B (a: X A B) (b: X B A), a*b <== a*b*a*b.
    intros. 
    try kleene_reflexivity.
    idtac.
  Abort.

  Goal forall A B (a: X A B) (b: X B A) (c: X B B), a*c*(b*a)# == (a*b)#*a.
    intros. 
    try kleene_reflexivity.
    idtac.
  Abort.

  Goal forall A B (a: X A B) (b: X B A) (c: X B B), a*c*(b*a)# == (a*b)#*a*(1+c*0).
    intros. 
    try kleene_reflexivity.
    idtac.
  Abort.

  Goal forall A (a b: X A A), (a*0)#*b == b+0*a#+b*0#.
    intros. kleene_clean_zeros. 
  Abort.

  Goal forall A (a b: X A A), (a*0)# <== b+0*a#+0#.
    intros. kleene_clean_zeros. 
  Abort.

  Goal forall A (a b: X A A), ((1+b)*(1+a))# == (a+b)#.
    intros. kleene_ssf. 
  Abort.
  
End test.

Section ctest.

  Context `{KA: ConverseKleeneAlgebra}.

  Goal forall A B (a: X A B) (b: X B A), a`*(a*b)`# == (b*a)#`*a`.
    intros.
    Time ckleene_reflexivity.
  Abort.

End ctest.
endtests*)

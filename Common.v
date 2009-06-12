(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: Common.v 875 2009-06-09 11:53:22Z braibant $ i*)

Require Export Arith.
Require Export Omega.
Require Export Coq.Program.Equality.
Require Export Setoid.

(* resolution des contradictions *)
Ltac omega_false := elimtype False; unfold fst in *; omega.
Ltac tauto_false := elimtype False; unfold fst in *; tauto.

(* au cas ou *)
Bind Scope nat_scope with nat.

(* destruction recursive des tests sur entiers *)
Ltac destruct_nat_dec :=
  try omega_false;
    match goal with 
      | |- context c [le_lt_dec ?u ?v] => destruct (le_lt_dec u v); destruct_nat_dec
      | |- context c [eq_nat_dec ?u ?v] => destruct (eq_nat_dec u v); destruct_nat_dec
      | _ => idtac
    end.

(* presque comme lapply : poser une preuve incomplète *)
Ltac lpose H H' :=
  match type of H with
    | ?A -> ?B => assert (H': A); [|apply H in H']
  end.
Tactic Notation "lpose" constr(H) "as" ident(H') := lpose H H'.


(* destructeur qui marche parfois un peu mieux que destruct... *)
Ltac idestruct H := 
  let H' := fresh in generalize H; intro H'; destruct H'.

(* pour debugger *)
Ltac print_goal := match goal with |- ?x => idtac x end.

(* les deux bases de donnees principales *)
Create HintDb compat discriminated.
Create HintDb algebra discriminated.

(* pour reecrire des monotypes : mon_check sera une base 
   pour prouver qu'un elt est un monotype *)
Create HintDb mon_check.
Ltac mon_check := auto with mon_check.


(* a cause des typeclasses, il faut souvent inferer des instances en autorewrite *)
Ltac ti_auto := auto with typeclass_instances.

(* simplification par reecriture *)
Ltac rsimpl := simpl; autorewrite with simpl using ti_auto.

(* en dernier recours, on résout les buts sur nat avec omega *)
Hint Extern 9 (@eq nat ?x ?y) => instantiate; unfold fst in *; abstract omega: omega.
Hint Extern 9 (Peano.le ?x ?y) => instantiate; unfold fst in *; abstract omega: omega.
Hint Extern 9 (Peano.lt ?x ?y) => instantiate; unfold fst in *; abstract omega: omega.

(* une coercion utile pour écrire des programmes *)
Definition proj_sumbool (P Q: Prop) (a: {P} + {Q}) : bool :=
    if a then true else false.

Implicit Arguments proj_sumbool [P Q].

Coercion proj_sumbool: sumbool >-> bool.
  
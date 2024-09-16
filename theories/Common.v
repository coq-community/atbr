(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** This small module is imported in all our files, it exports useful
   modules and defines some basic utilities and tactics *)

From Coq Require Export Arith.
From Coq Require Export Lia.
From Coq Require Export BinNums BinPos PArith.Pnat.
From Coq.Program Require Export Equality.
From Coq Require Export Setoid Morphisms.

Set Implicit Arguments.

Bind Scope nat_scope with nat.

(** Functional composition *)
Definition comp A B C (f: A -> B) (g: B -> C) := fun x => g (f x).
Notation "f >> g" := (comp f g) (at level 50). 

(** This lemma is useful when applied in hypotyheses ([apply apply in H] makes it possible to specialize 
   an hypothesis [H] by generating the corresponding subgoals) *)
Definition apply X x Y (f: X -> Y) := f x.

(** Tactics to resolve a goal by using a contradiction in the hypotheses, using either [lia] or [tauto] *)
Ltac lia_false := exfalso; lia.
Ltac tauto_false := exfalso; tauto.

(** This destructor sometimes works better that the standard [destruct] *)
Ltac idestruct H := 
  let H' := fresh in generalize H; intro H'; destruct H'.

(** For debugging *)
Ltac print_goal := match goal with |- ?x => idtac x end.

(** This tactic allows one to infere maximally implicit arguments that failed to be inferred and were 
   replaced by sub-goals *)
Ltac ti_auto := eauto with typeclass_instances. 


(** The following databases are used all along the library:
   - <compat> contains most "compatibility with equality" and "monotonicity" lemmas: Morphisms with respects to 
   [Classes.equal] and [Classes.leq] ; it is useful to solve simple goals like [x <== y |- x*f x <== y*f y], 
   and to obtain new morphisms. These morphism are always called [f_compat] and [f_incr], where [f] is the 
   name of the compatible or monotone function.
   - <algebra> contains simple algebraic lemmas like [0 <== x], [1 <== x#], 
   and [x <== z -> y <== z -> x+y <== z], 
   that seem to be appropriate for [(e)auto] proof search. 
   - <simpl> is a rewriting database, to be used with the [rsimpl] tactic. It contains lemmas like [1*x == x] 
   [0# == 1] and provides a simple way to normalise the goal "in depth", using the setoid infrastructure.
   This is not really efficient, however.
   - <lia> contains hints to use [lia] when proof search failed ; this basically allows us to avoid 
   using [lia] in trivial cases.
*)
Create HintDb compat discriminated.
Create HintDb algebra discriminated.

Ltac rsimpl := simpl; autorewrite with simpl using ti_auto.

#[global] Hint Extern 9 (@eq nat ?x ?y) => abstract lia: lia.
#[global] Hint Extern 9 (Peano.le ?x ?y) => abstract lia: lia.
#[global] Hint Extern 9 (Peano.lt ?x ?y) => abstract lia: lia.

(** Tactic to use when apply does not smartly unify *)
Ltac rapply H := first 
  [ refine H
  | refine (H _)
  | refine (H _ _)
  | refine (H _ _ _)
  | refine (H _ _ _ _)
  | refine (H _ _ _ _ _)
  | refine (H _ _ _ _ _ _)
  | refine (H _ _ _ _ _ _ _)
  | refine (H _ _ _ _ _ _ _ _)
  | refine (H _ _ _ _ _ _ _ _ _)
  | refine (H _ _ _ _ _ _ _ _ _ _)
  | refine (H _ _ _ _ _ _ _ _ _ _ _)
  | refine (H _ _ _ _ _ _ _ _ _ _ _ _)
  | fail 1 "extend rapply"
  ].

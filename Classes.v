(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** This module defines all classes of our algebraic hierarchy *)

Require Import Common.

(** * Graph : base class of the hierarchy
   
   a multigraph with indexed equalities on vertices. *)

(* RMK: we do not separate operators (equal) from axioms
   (equal_equivalence) for this base class. This is to be able to add
   reflexivity as a trivial hint, and symmetry as an immediate
   one. This might change in the future, if the semantics of hints for
   lemmas with maximally inserted implicit arguments changes. 
   *)

Class Graph := {
  T: Type;
  X: T -> T -> Type;
  equal: forall A B, relation (X A B);
  equal_:> forall A B, Equivalence (equal A B)
}.

(*Arguments equal : simpl never.*)

Set Implicit Arguments.

Bind Scope A_scope with X.

Section Ops.
(** * Operations
   
   All operations are parametrised by the [Graph] base-class

*)
  Context (G: Graph).

  Class Monoid_Ops := {
    dot: forall A B C, X A B -> X B C -> X A C;
    one: forall A,     X A A      
  }.
  
  Class SemiLattice_Ops := {
    plus: forall A B, X A B -> X A B -> X A B;
    zero: forall A B, X A B;
    leq: forall A B: T, relation (X A B) := fun A B x y => equal A B (plus A B x y) y
  }.
  
  Class Star_Op := {
    star: forall A, X A A -> X A A
  }.
  
  Class Converse_Op := {
    conv: forall A B, X A B -> X B A
  }.

End Ops.

(** Notations for operations *)
Notation "x == y"  := (equal _ _ x y) (at level 70): A_scope. 
Notation "x <== y" := (leq _ _ x y) (at level 70): A_scope. 
Notation "x * y"   := (dot _ _ _ x y) (at level 40, left associativity): A_scope. 
Notation "x + y"   := (plus _ _ x y) (at level 50, left associativity): A_scope. 
Notation "x #"     := (star _ x) (at level 15, left associativity): A_scope.
Notation "x `"     := (conv _ _ x) (at level 15, left associativity): A_scope.  
Notation "1"       := (one _): A_scope. 
Notation "0"       := (zero _ _): A_scope. 

Open Scope A_scope.
Delimit Scope A_scope with A.


(* Unset Implicit Arguments. *)
Unset Strict Implicit.


Section Structures.
(** * Structures

   All structures are parametrised by both the [Graph] base-class and the corresponding operations.
   *)

  Context {G: Graph}.
  Context {Mo: Monoid_Ops G} {SLo: SemiLattice_Ops G} {Ko: Star_Op G} {Co: Converse_Op G}.

  Class Monoid := {
    dot_compat:> forall A B C, Proper (equal A B ==> equal B C ==> equal A C) (dot A B C);
    dot_assoc: forall A B C D (x: X A B) y (z: X C D), x*(y*z) == (x*y)*z;
    dot_neutral_left:  forall A B (x: X A B), 1*x == x;
    dot_neutral_right:  forall A B (x: X B A), x*1 == x
  }.
  
  Class SemiLattice := {
    plus_compat:> forall A B, Proper (equal A B ==> equal A B ==> equal A B) (plus A B);
    plus_neutral_left: forall A B (x: X A B), 0+x == x;
    plus_idem: forall A B (x: X A B), x+x == x;
    plus_assoc: forall A B (x y z: X A B), x+(y+z) == (x+y)+z;
    plus_com: forall A B (x y: X A B), x+y == y+x
  }.
 
  Class IdemSemiRing := {
    ISR_Monoid :> Monoid;
    ISR_SemiLattice :> SemiLattice;
    dot_ann_left:  forall A B C (x: X B C), zero A B * x == 0;
    dot_ann_right: forall A B C (x: X C B), x * zero B A == 0;
    dot_distr_left:  forall A B C (x y: X A B) (z: X B C), (x+y)*z == x*z + y*z;
    dot_distr_right: forall A B C (x y: X B A) (z: X C B), z*(x+y) == z*x + z*y
  }.

  Class KleeneAlgebra := {
    KA_ISR :> IdemSemiRing;
    star_make_left: forall A (a:X A A), 1 + a#*a == a#;
    star_destruct_left: forall A B (a: X A A) (c: X A B), a*c <== c  ->  a#*c <== c;
    star_destruct_right: forall A B (a: X A A) (c: X B A), c*a <== c  ->  c*a# <== c
  }.

  (** Once we add the converse operation, we no longer need some
     axioms from Monoid/SemiRing/KA.  This is why we do not use direct
     inheritance *)
  (* TODO: introduce an intermediate ConverseMonoid class *)

  Class ConverseIdemSemiRing := {
    CISR_SL :> SemiLattice;
    dot_compat_c: forall A B C, Proper (equal A B ==> equal B C ==> equal A C) (dot A B C);
    dot_assoc_c: forall A B C D (x: X A B) y (z: X C D), x*(y*z) == (x*y)*z;
    dot_neutral_left_c:  forall A B (x: X A B), 1*x == x;

    conv_compat:> forall A B, Proper (equal A B ==> equal B A) (conv A B);
    conv_invol: forall A B (x: X A B), x`` == x;
    conv_dot:  forall A B C (x: X A B) (y: X B C), (x*y)` == y`*x`;
    conv_plus:  forall A B (x y: X A B), (x+y)` == y`+x`;
    dot_ann_left_c:  forall A B C (x: X B C), zero A B * x == 0;
    dot_distr_left_c:  forall A B C (x y: X A B) (z: X B C), (x+y)*z == x*z + y*z
  }.
  
  Class ConverseKleeneAlgebra := {
    CKA_CISR :> ConverseIdemSemiRing;
    star_make_left_c: forall A (a:X A A), 1 + a#*a == a#;
    star_destruct_left_c: forall A B (a: X A A) (c: X A B), a*c <== c  ->  a#*c <== c
  }.
  
End Structures.

(** we want to keep the graph explicit, for better readability, (but
   we still want the graph to be maximally implicit in projections
   like [dot_assoc]. *)
Implicit Arguments Monoid [[Mo]].
Implicit Arguments SemiLattice [[SLo]].
Implicit Arguments IdemSemiRing [[Mo] [SLo]].
Implicit Arguments ConverseIdemSemiRing [[Mo] [SLo] [Co]].
Implicit Arguments KleeneAlgebra [[Mo] [SLo] [Ko]].
Implicit Arguments ConverseIdemSemiRing [[Mo] [SLo] [Co]].
Implicit Arguments ConverseKleeneAlgebra [[Mo] [SLo] [Co] [Ko]].



(** * Dual structures 

   These structures are obtained by reversing all arrows; they make it
   possible to factorise several proofs, by symmetry.  
   *) 

Module Dual. Section Protect.
  
  Local Transparent equal.

  Context (G: Graph).
  Context {Mo: Monoid_Ops G} {SLo: SemiLattice_Ops G} {Ko: Star_Op G} {Co: Converse_Op G}.
  
  Instance Graph: Graph := {
    T := T;
    X A B := X B A;
    equal A B := equal B A;
    equal_ A B := equal_ B A
  }.

  Instance Monoid_Ops: Monoid_Ops Graph := {
    dot A B C x y := @dot _ Mo C B A y x;
    one := @one _ Mo
  }.

  Instance SemiLattice_Ops: SemiLattice_Ops Graph := {
    plus A B := @plus _ SLo B A;
    zero A B := @zero _ SLo B A
  }.

  Instance Star_Op: Star_Op Graph := {
    star := @star _ Ko
  }.
      
  Instance Converse_Op: Converse_Op Graph := {
    conv A B := @conv _ Co B A
  }.

  Instance Monoid {M: Monoid G}: Monoid Graph := {
    dot_neutral_left := @dot_neutral_right _ _ M;
    dot_neutral_right := @dot_neutral_left _ _ M;
    dot_compat A B C x x' Hx y y' Hy := @dot_compat _ _ M C B A _ _ Hy _ _ Hx
  }.
  Proof.
    intros. symmetry. simpl. apply dot_assoc. 
  Defined.

  Instance SemiLattice {SL: SemiLattice G}: SemiLattice Graph := {
    plus_com A B := @plus_com _ _ SL B A;
    plus_idem A B := @plus_idem _ _ SL B A;
    plus_assoc A B := @plus_assoc _ _ SL B A;
    plus_compat A B := @plus_compat _ _ SL B A;
    plus_neutral_left A B := @plus_neutral_left _ _ SL B A
  }.

  Instance IdemSemiRing {ISR: IdemSemiRing G}: IdemSemiRing Graph.
  Proof.
    intros.
    constructor.
    exact Monoid. 
    exact SemiLattice.
    exact (@dot_ann_right _ _ _ ISR).
    exact (@dot_ann_left _ _ _ ISR).
    exact (@dot_distr_right _ _ _ ISR).
    exact (@dot_distr_left _ _ _ ISR).
  Defined.

End Protect. End Dual.

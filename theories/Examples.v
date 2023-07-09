(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** * Examples about uses of the ATBR library *)

From ATBR Require Import ATBR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** Setting *)

Section Setting.

  (** We assume a typed Kleene algebra (as described in [Classes]) *)
  Context `{KA: KleeneAlgebra}.

  (** printing * * *)
  (** This means we can write expressions like the following one, where
     - [a #]  is the Kleene star of [a], 
     - [a + b] is the sum of [a] and [b],
     - [a * b] is their product (or concatenation) 
     - [1]   is the neutral element for [*]
     - [0]   is the neutral element for [+]
     - [==]  is the equality associated to this algebraic structure
     - [<==] is the preorder associated to [+] ([x <== y] iff [x + y == y])
     *)

  Check forall A (a b c: X A A), 1+a#*b+(c*0+a*b*c)# == 1.

  (** In the previous expression, A is a "type", it makes sense in
     situations like the following, where 
     - R can be thought of as a relation from a set A to a set B, 
     - S as a relation from set B to set A,
     - T as a relation from A to C

     (As shown below, these `types' can also be seen as matrix dimensions.)
     *)

  Check forall A B C (R: X A B) (S: X B A) (T: X A C), ((R*S)# + 1) * T == 0.

End Setting.


(** ** Decision tactics  *)

Section Tactics.
  
  (** The main tactic of this library is [kleene_reflexivity] from
     file DecideKleeneAlgebra.v. This is a reflexive tactic that
     through automata constructions in order to solve (in)equations
     that are valid in any Kleene algebras: *)

  Section DKA.
  Context `{KA: KleeneAlgebra}.
  
  Variables A B: T.
  Variables a b c: X A A.
  Variable d: X A B.
  Variable e: X B A.

  Lemma star_distr: (a+b)# == a#*(b*a#)#.
    kleene_reflexivity.
  Qed.

  Goal (d*e)#*d == d*(e*d)#.
    kleene_reflexivity.
  Qed.

  Goal a#*(b+a#*(1+c))# == (a+b+c)#.
    kleene_reflexivity.
  Qed.
    
  Goal a*b*c*a*b*c*a# <== a#*(b*c+a)#.
    kleene_reflexivity.
  Qed.

  (** Note that kleene_reflexivity cannot use hypotheses (Horn theory
  of KA is undecidable) *)

  Goal a*b <== c -> a*(b*a)# <== c#*a.
    intro H. 
    try kleene_reflexivity. 
    rewrite <- H.
    kleene_reflexivity.
  Qed.

  (** kleene_reflexivity is a decision procedure, which means it also produces a
  counter-example when the goal is false. It typically reports a single string
  that appears on one side but not the other. *)
  Goal b# <== a*b*c.
    Fail kleene_reflexivity.
  Abort.

  Goal a <== b.
    Fail kleene_reflexivity.
  Abort.

  Goal a*b# <== a*b*c.
    Fail kleene_reflexivity.
  Abort.

  Goal b#*a# == b#*1*a.
    Fail kleene_reflexivity.
  Abort.

  End DKA.
  

  (** We also implemented reflexive decision tactics for the
     intermediate structures (lighter, faster). They work as soon as
     we provide enough structure (e.g. an idempotent semi-ring
     [IdemSemiRing], or even a [Monoid] or a [SemiLattice]); they can
     of course be used to solve simple goals in richer settings, like
     Kleene Agebras.  *)

  Section ISR.
  Context `{ISR: IdemSemiRing}.

  Variables A B: T.
  Variables a b c: X A A.
  Variable d: X A B.


  Goal (a+b)*(a+b) == a*a+a*b+b*a+b*b.
    semiring_reflexivity.
  Qed.

  Goal 0+b*a <== (a+b)*(1+a).
    semiring_reflexivity.
  Qed.

  Goal a*(b*1)*(c*d) == a*1*b*c*d.
    semiring_reflexivity.
  Qed.

  Goal a+(b+1)+(a+c) == 1+c+b+a+0.
    semiring_reflexivity.
  Qed.

  Goal a <== 1+c+b+a+0.
    semiring_reflexivity.
  Qed.

  (** On these simpler structures, we also have `normalisation' tactics: *)

  Goal a*1*(a+b)*d <== (a+b)*((a+(b+c))*d) + d*0.
    (** normalize expressions by expanding them *)
    semiring_normalize.
    (** just remove zeros and ones *)
    Restart. semiring_clean.
    (** remove zeros and ones and normalize parentheses *)
    Restart. semiring_cleanassoc.
    semiring_reflexivity.
  Qed.

  (** *** Rewriting tactics  

     When rewriting terms, handling associativity and commutativity
     explicitly can be tedious. We implemented ad-hoc tactics for
     rewriting *closed* equations modulo A and/or AC; we plan to
     investigate this problem in a more systematic way.  *)

  Goal c*d <== 0 -> a*b*c*d <== 0.
    intro H.
    (** parentheses do not match *)
    try rewrite H.
    monoid_rewrite H.
    semiring_reflexivity.
  Qed.

  Goal d <== c*d -> a*b*d <== a*b*c*d.
    intro H.
    (** parentheses do not match *)
    try rewrite <- H.
    monoid_rewrite <- H.
    semiring_reflexivity.
  Qed.

  Goal a+b+c <== c -> b+a+c+c <== c. 
    intro H.
    ac_rewrite H.
    semiring_reflexivity.
  Qed.

  End ISR.
End Tactics.


(** ** Examples about matrices  

  Our development makes an heavy use of matrices, so that we had to
  develop a bit of matrix theory, that could be reused in other
  contexts.  We give some examples about how to work with matrices in
  our setting.  *)


From ATBR Require ATBR_Matrices.
Section Matrices.

  Import ATBR_Matrices.

  (** Assume an underlying idempotent semi-ring  *)
  Context `{ISR: IdemSemiRing}.

  (** Notations are overloaded, thanks to the typeclass mechanism. We
  introduce specific notations to avoid confusion betwen matrices [MX] and
  their underlying elements [X]. *)

  Variable A: T.
  (** type of matrices over (X A A) *)
  Notation MX := (@X (mx_Graph A)).
  (** type of elements *)
  Notation X := (@X G).

  (** Constant-to-a 2x2 matrix, with elements of type X A A *)
  Definition constant (a: X A A): MX 2 2 := box 2 2 (fun i j => a).

  (** To retrieve the elements of a matrix, we use "!" (a notation for the "get" operation) *)
  Goal forall a, !(constant a) O O == a.
  Proof.
    intros. reflexivity.
  Qed.

  (** Dummy lemma, notice overloading of notations for [*] *)
  Lemma square_constant a: constant a * constant a == constant (a*a).
  Proof. 
    (** since the dimensions are known (and finite), the matricial product can be computed *)
    simpl.
    (** the [mx_intros] simple tactic introduces indices to prove a
    matricial equality; it is useful when considering vectors: only
    one dimension is introduced *)
    mx_intros i j Hi Hj.
    simpl.
    (* easy goal, on the underlying algebra *)
    semiring_reflexivity.
  Qed.

  (** Our tactics automatically work for matrices (matrices are just another idempotent semiring) *)
  Goal forall n m p (M: MX n m) (N: MX m p) (P: MX n p),
    M*1*N + P == P+M*N.
  Proof.
    intros.
    semiring_reflexivity.
  Qed.

  (** Block matrices manipulation *)
  Lemma square_triangular_blocks n m (M: MX n n) (N: MX n m) (P: MX m m):
    mx_blocks M N 0 P * mx_blocks M N 0 P == mx_blocks (M*M) (M*N+N*P) 0 (P*P).
  Proof.
    intros.
    rewrite mx_blocks_dot.
    apply mx_blocks_compat; semiring_reflexivity.
  Qed.

  (** (We will clean-up and document this library for matrices at some
     point, so that we do not give further details for now.) *)

End Matrices.



(** ** Using concrete structures 

     To work with a concrete given struture, you need to show that it
     satisfies the corresponding axioms. Examples are given in files
     Model_*.v

     For example, it is shown in Model_Relations.v that
     (heterogeneous) binary relations form a Kleene algebra with
     converse. This file can easily be adapted to use other
     definitions.
     *)


From ATBR Require Model_Relations.
Section Concrete.

  Import Model_Relations.
  Import Load.
  (* the latter line is required in order to register binary relations
     to the typeclass mechanism *)
  
  (** Any theorem we proved in an abstract structure now applies to
     binary relations *)
  Variable A: Set.
  Variables R S: rel A A.
  Check (star_distr R S).

  (** tactics work out of the box when using our notations *)
  Goal R*S==R -> R*(S+R#) == R#*R.
  Proof. 
    intro H.
    rewrite dot_distr_right, H.
    kleene_reflexivity.
  Qed.

  (* TOTHINK: also declare canonical structures for operations *)
  Canonical Structure rel_Monoid_Ops.
  Goal R*S==R -> rel_comp R (S+R#) == rel_comp (R#) R.
  Proof. 
    intro H.
    rewrite dot_distr_right, H.
    fold_relAlg.
    kleene_reflexivity.
  Qed.

End Concrete.


(** Similarly, homogeneous relations (from the standard library) are
    declared in Model_StdRelations, so that one can use our tactics to
    reason about these.  *)

From Coq Require Relations.
From ATBR Require Model_StdRelations.

Section Concrete'.

  Import Relations.
  Import Model_StdRelations.
  Import Load.
  
  Variable A: Set.
  Variables R S: relation A.

  Lemma example: same_relation _
    (clos_refl_trans _ (union _ R S))
    (comp (clos_refl_trans _ R) (clos_refl_trans _ (comp S (clos_refl_trans _ R)))).
  Proof.
    intros.
    fold_relAlg A.
    kleene_reflexivity.
  Qed.
  Print Assumptions example.
  
End Concrete'.

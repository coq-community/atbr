(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Class of "Strict Kleene Algebras" : those without a zero;
   extension of the [kleene_reflexivity] tactic to these structures,
   using a faithful embedding. *)

Require Import Common.
Require Import Classes.
Require Import DecideKleeneAlgebra.
Set Implicit Arguments.
Unset Printing Implicit Defensive.

Bind Scope SA_scope with X.

(** Strict Kleene Algebras operations *)
Class SKA_Ops (G: Graph) := {
  dot:  forall A B C, X A B -> X B C -> X A C;
  one:  forall A,     X A A;
  plus: forall A B, X A B -> X A B -> X A B;
  star: forall A, X A A -> X A A;
  leq:  forall A B: T, relation (X A B) := fun A B x y => equal A B (plus A B x y) y
}.


Notation "x == y"  := (equal _ _ x y) (at level 70): SA_scope. 
Notation "x <== y" := (leq _ _ x y) (at level 70): SA_scope. 
Notation "x * y"   := (dot _ _ _ x y) (at level 40, left associativity): SA_scope. 
Notation "x + y"   := (plus _ _ x y) (at level 50, left associativity): SA_scope. 
Notation "x #"     := (star _ x) (at level 15, left associativity): SA_scope.
Notation "1"       := (one _): SA_scope. 

Close Scope A_scope.
Open Scope SA_scope.
Delimit Scope SA_scope with SA.

(** Strict Kleene Algebras axioms *)
Class StrictKleeneAlgebra {G: Graph} {Ops: SKA_Ops G} := {
  dot_compat:> 
    forall A B C, Proper (equal A B ==> equal B C ==> equal A C) (dot A B C);
  plus_compat:> 
    forall A B, Proper (equal A B ==> equal A B ==> equal A B) (plus A B);
  dot_assoc: forall A B C D (x: X A B) y (z: X C D), x*(y*z) == (x*y)*z;
  dot_neutral_left:  forall A B (x: X A B), 1*x == x;
  dot_neutral_right:  forall A B (x: X A B), x*1 == x;
  plus_idem: forall A B (x: X A B), x+x == x;
  plus_assoc: forall A B (x y z: X A B), x+(y+z) == (x+y)+z;
  plus_com: forall A B (x y: X A B), x+y == y+x;
  dot_distr_left:  forall A B C (x y: X A B) (z: X B C), (x+y)*z == x*z + y*z;
  dot_distr_right: forall A B C (x y: X B A) (z: X C B), z*(x+y) == z*x + z*y;
  star_make_left: forall A (a:X A A), 1 + a#*a == a#;
  star_destruct_left: forall A B (a: X A A) (c: X A B), a*c <== c  ->  a#*c <== c;
  star_destruct_right: forall A B (a: X A A) (c: X B A), c*a <== c  ->  c*a# <== c
}.
Implicit Arguments StrictKleeneAlgebra [[Ops]].

(** Lifting an equivalence relation to option types  *)

Section oe.
  Variable A: Type.
  Variable R: relation A.
  Inductive oequal: relation (option A) :=
  | oe_some: forall x y, R x y -> oequal (Some x) (Some y)
  | oe_none: oequal None None.
  Hypothesis HR: Equivalence R.
  Lemma oequal_equivalence: Equivalence oequal.
  Proof.
    constructor.
     intros [x|]; constructor. reflexivity.
     intros x y [x' y' H|]; constructor. symmetry. assumption.
     intros x y z [x' y' H|] H'; trivial. 
      inversion_clear H'. constructor. rewrite H. assumption.
  Qed.
End oe.

Unset Strict Implicit.

(** Definition of the faithful embedding from Strict Kleene Algebras
   to Kleene Algebras *)

Section F.
  Context `{StrictKleeneAlgebra}.

  Instance oGraph: Graph := {
    T := T; 
    X A B := option (X A B);
    equal A B := oequal (equal A B)
  }.
  Proof.
    intros. apply oequal_equivalence, G. 
  Defined.

  Definition inj A B (x: X A B): @X oGraph A B := Some x. 
  Lemma faithful: forall A B (x y: X A B), inj x == inj y -> x == y.
  Proof. 
    intros A B x y Hxy. inversion_clear Hxy. assumption.
  Qed.

  Global Instance oMonoid_Ops: Monoid_Ops oGraph := {
    dot A B C x y := 
      match x,y with 
        | Some x, Some y => Some (x*y)
        | _,_ => None 
      end;
    one A := Some 1
  }.

  Global Instance oSemiLattice_Ops: SemiLattice_Ops oGraph := {
    plus A B x y := 
      match x,y with 
        | None,y => y 
        | x,None => x 
        | Some x, Some y => Some (x+y) 
      end;
    zero A B := None
  }.

  Global Instance oStar_Op: Star_Op oGraph := {
    star A x := 
      match x with 
        | None => Some 1
        | Some x => Some (x#) 
      end
  }.

  Instance oMonoid: Monoid oGraph.
  Proof.
    constructor; intros.
     intros _ _ [x x' Hx|] _ _ [y y' Hy|]; simpl; constructor. 
      apply dot_compat; assumption.
     destruct x; try constructor.
      destruct y; try constructor.
       destruct z; constructor. apply dot_assoc.
     destruct x; simpl; constructor. apply dot_neutral_left.
     destruct x; simpl; constructor. apply dot_neutral_right.
  Qed.

  Instance oSemiLattice: SemiLattice oGraph.
  Proof.
    constructor; intros.
     intros _ _ [x x' Hx|] _ _ [y y' Hy|]; simpl; constructor; trivial.
      apply plus_compat; assumption.
     destruct x; simpl; constructor. reflexivity.
     destruct x; simpl; constructor. apply plus_idem.
     destruct x; destruct y; destruct z; simpl; constructor; try reflexivity.
      apply plus_assoc.
     destruct x; destruct y; simpl; constructor; try reflexivity.
      apply plus_com.
  Qed.

  Instance oIdemSemiRing: IdemSemiRing oGraph.
  Proof.
    constructor; eauto with typeclass_instances; intros.
     destruct x; reflexivity.
     destruct x; destruct y; destruct z; simpl; constructor; try reflexivity.
      apply dot_distr_left.
     destruct x; destruct y; destruct z; simpl; constructor; try reflexivity.
      apply dot_distr_right.
  Qed.

  Global Instance oKleeneAlgebra: KleeneAlgebra oGraph.
  Proof.
    constructor; eauto with typeclass_instances.
     intros A [a|]; simpl; constructor; try reflexivity.
      apply star_make_left.
     intros A B [a|] [c|] Hac; simpl in *; try constructor. 
      apply star_destruct_left. inversion_clear Hac. assumption.
      rewrite dot_neutral_left. apply plus_idem.
     intros A B [a|] [c|] Hac; simpl in *; try constructor. 
      apply star_destruct_right. inversion_clear Hac. assumption.
      rewrite dot_neutral_right. apply plus_idem.
  Qed.
End F.

(** The exported tactic embeds the goal in Kleene algebras and calls [kleene_reflexivity] *)
Ltac skleene_reflexivity :=
  (* [parse] converts an expression of strict Kleene algebras into an expression of Kleene algebras *)
  let rec parse t := 
    match t with
      | @dot ?G ?O ?A ?B ?C ?x ?y =>
        let x := parse x in
        let y := parse y in 
          constr:(@Classes.dot (@oGraph G) (@oMonoid_Ops G O) A B C x y)
      | @one ?G ?O ?A =>
          constr:(@Classes.one (@oGraph G) (@oMonoid_Ops G O) A)
      | @plus ?G ?O ?A ?B ?x ?y =>
        let x := parse x in
        let y := parse y in 
          constr:(@Classes.plus (@oGraph G) (@oSemiLattice_Ops G O) A B x y)
      | @star ?G ?O ?A ?x =>
        let x := parse x in
          constr:(@Classes.star (@oGraph G) (@oStar_Op G O) A x)
      | _ => constr:(inj t)
    end
  in
  unfold leq;
  lazymatch goal with 
    | |- @equal ?G ?A ?B ?x ?y => 
      let x := parse x in
      let y := parse y in
        apply faithful; change (@equal (@oGraph G) A B x y); kleene_reflexivity
  end.

(*begintests
Section t.
  Context `{StrictKleeneAlgebra}.
  Lemma test: forall A B (a: X A B) (b: X B A), a*(b*a)# == (a*b)#*a.
  Proof.
    intros. 
    skleene_reflexivity.
  Qed.
  Lemma test': forall A (a b: X A A), (a+b+1)# == a#*(b*a#)#.
  Proof.
    intros. 
    skleene_reflexivity.
  Qed.
  Lemma test'': forall A (a b: X A A), (a*a+b)# <== a#*(b*a#)#.
  Proof.
    intros. 
    skleene_reflexivity.
  Qed.
  Lemma test''': forall A (a b: X A A), (a*a+b)# <== a*(b*a#)#.
  Proof.
    intros. 
    try skleene_reflexivity.
  Abort.
End t.
endtests*)

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

(** * Graph

   The carrier class and its axiomes. We cannot separate them without
   getting trouble from trivial (for reflexivity goals) since trivial
   won't allow the hints for typeclasses to be used.

  *)

(*
   damien: 
   on déroge à la règle de séparation opérateurs / axiomes
   pour la classe Graph, sans cela, comme l'ajout de hints 
   avec arguments maximalement insérés n'est pas bien géré,
   on ne peut pas laisser trivial gérer les buts de 
   réflexivité, ni auto être intelligent avec les lemmes de
   symétrie
 *)

Class Graph := {
  T: Type;
  X: T -> T -> Type;
  equal: forall A B, relation (X A B);
  equal_equivalence: forall A B, Equivalence (equal A B)
}.
Existing Instance equal_equivalence.
Typeclasses Opaque equal_equivalence.

Set Implicit Arguments.

Section Ops.
(** * Operations
   
   Operations do not inherits but the graph

*)
  Context {G: Graph}.

  Class Monoid_Ops := {
    dot: forall A B C, X A B -> X B C -> X A C;
    one: forall A,     X A A      
  }.
  
  Class SemiLattice_Ops := {
    plus: forall A B, X A B -> X A B -> X A B;
    zero: forall A B, X A B;
    leq: forall A B: T, relation (X A B) := fun A B x y => equal A B (plus A B x y) y
  }.
  
  Class CompleteLattice_Ops := 
    sup: forall A B, (X A B -> Prop) -> X A B
  .
  
  Class Inf_Op := 
    inf: forall A B, X A B -> X A B -> X A B
  .
  
  Class Residual_Ops := {
    ldiv: forall A B C, X A B -> X A C -> X B C; 
    rdiv: forall A B C, X B A -> X C A -> X C B 
  }.
  
  Class Star_Op := 
    star: forall A, X A A -> X A A
  .
  
  Class Converse_Op := 
    conv: forall A B, X A B -> X B A
  .

End Ops.

Notation "x  == y" := (equal _ _ x y) (at level 80): A_scope. 
Notation "x <== y" := (leq _ _ x y) (at level 80): A_scope. 
Notation "x * y"   := (dot _ _ _ x y) (at level 40, left associativity): A_scope. 
Notation "x + y"   := (plus _ _ x y) (at level 50, left associativity): A_scope. 
Notation "x ^ y"   := (inf _ _ x y) (at level 30, right associativity): A_scope.
Notation "x \ y"   := (ldiv _ _ _ x y) (at level 41, right associativity) : A_scope.
Notation "x / y"   := (rdiv _ _ _ y x) (at level 40, left associativity) : A_scope.
Notation "x #"     := (star _ x) (at level 15, left associativity): A_scope.
Notation "x `"     := (conv _ _ x) (at level 15, left associativity): A_scope.  
Notation "1"       := (one _): A_scope. 
Notation "0"       := (zero _ _): A_scope. 

Open Scope A_scope.


(* on voulait les seulement les arguments strictement implicites pour
   les operateurs, pour les axiomes, on veut bien les non-stricts *)
   
Unset Strict Implicit.


Section Structures.
(** * Algebraic hierarchy axioms *)

  Context {G: Graph}.

  Class Monoid {Mo: Monoid_Ops} := {
    dot_compat: forall A B C, Proper ((equal A B) ==> (equal B C) ==> (equal A C)) (dot A B C);
    dot_assoc: forall A B C D (x: X A B) y (z: X C D), x*(y*z) == (x*y)*z;
    dot_neutral_left:  forall A B (x: X A B), 1*x == x;
    dot_neutral_right:  forall A B (x: X A B), x*1 == x
  }.
  
  Class SemiLattice {SLo: SemiLattice_Ops} := {
    plus_compat: forall A B, Proper ((equal A B) ==> (equal A B) ==> (equal A B)) (plus A B);
    plus_neutral_left: forall A B (x: X A B), 0+x == x;
    plus_idem: forall A B (x: X A B), x+x == x;
    plus_assoc: forall A B (x y z: X A B), x+(y+z) == (x+y)+z;
    plus_com: forall A B (x y: X A B), x+y == y+x
  }.
 
  Class IdemSemiRing {Mo: Monoid_Ops} {SLo: SemiLattice_Ops} := {
    ISR_Monoid :> Monoid;
    ISR_SemiLattice :> SemiLattice;
    dot_ann_left:  forall A B C (x: X B C), zero A B * x == 0;
    dot_ann_right: forall A B C (x: X C B), x * zero B A == 0;
    dot_distr_left:  forall A B C (x y: X A B) (z: X B C), (x+y)*z == x*z + y*z;
    dot_distr_right: forall A B C (x y: X B A) (z: X C B), z*(x+y) == z*x + z*y
  }.
  
  Class ResIdemSemiRing {Mo: Monoid_Ops} {SLo: SemiLattice_Ops} {Ro: Residual_Ops} := {
    RISR_Monoid :> Monoid;
    RISR_SemiLattice :> SemiLattice;
    ldiv_def: forall A B C (x: X A B) (y: X A C) (z: X B C), z <== x\y <-> x*z <== y;
    rdiv_def: forall A B C (x: X B A) (y: X C A) (z: X C B), z <== y/x <-> z*x <== y  
  }. 

  Class KleeneAlgebra {Mo: Monoid_Ops} {SLo: SemiLattice_Ops} {Ko: Star_Op} := {
    KA_ISR :> IdemSemiRing;
    star_make_left: forall A (a:X A A), 1 + a#*a == a#;
    star_destruct_left: forall A B (a: X A A) (c: X A B), a*c <== c  ->  a#*c <== c;
    star_destruct_right: forall A B (a: X A A) (c: X B A), c*a <== c  ->  c*a# <== c
  }.
  
  Class ActionAlgebra {Mo: Monoid_Ops} {SLo: SemiLattice_Ops} {Ro: Residual_Ops} {Ko: Star_Op} := {
    AA_RISR :> ResIdemSemiRing;
    star_make: forall A (a: X A A), 1 + a + a#*a# <== a#;
    star_div_left: forall A (a: X A A), (a\a)# <== a\a;
    star_div_right: forall A (a: X A A), (a/a)# <== a/a
  }.
  
  Class ActionLattice {Mo: Monoid_Ops} {SLo: SemiLattice_Ops} {Ro: Residual_Ops} {Ko: Star_Op} {Io: Inf_Op} := {
    AL_AA :> ActionAlgebra;
    inf_compat: forall A B, Proper ((equal A B) ==> (equal A B) ==> (equal A B)) (inf A B);
    inf_idem: forall A B (x:X A B), x^x == x;
    inf_assoc: forall A B (x y z: X A B), (x^y)^z == x^(y^z);
    inf_com: forall A B (x y: X A B), x^y == y^x
  
  (* je rejette la distributivite, mais il faudrait comprendre les liens 
     avec l'axiome alternatif ci-dessous, [inf_def], et verifier que les automates ne
     marchent pas que pour les distributifs *)
  (* plus_distr_left: forall A B (x y z: X A B), (x^y)+z == (x^y)+(y^z); *)
  
  (* inf_def: forall A B (x y z: X A B), (x^y) <== z <-> (x<==z /\ y<==z) *)
  }.
  
  Class StarAllegory {Mo: Monoid_Ops} {SLo: SemiLattice_Ops} {Ro: Residual_Ops} {Ko: Star_Op} {Io: Inf_Op} {Co: Converse_Op} := {
  (* Damien: todo: quand on rajoute la converse, on peut simplifier
    les hypotheses sur l'action lattice... il faut reprendre une
    hierarchie parallele, mais j'attends que la premiere soit
    stabilisee *)
    SA_AL :> ActionLattice;
    modular_identity: forall A B C (x:X A B) (y:X B C) (z:X A C), (x*y) ^ z <== x*(y ^ (x`*z))
  }.


  Class ConverseIdemSemiRing {Mo: Monoid_Ops} {SLo: SemiLattice_Ops} {Co: Converse_Op} := {
    CISR_SL:> SemiLattice;

    (* pas besoin des *_right, on n'hérite donc pas de Monoid/IdemSemiRing directement *)
    dot_compat_c: forall A B C, Proper ((equal A B) ==> (equal B C) ==> (equal A C)) (dot A B C);
    dot_assoc_c: forall A B C D (x: X A B) y (z: X C D), x*(y*z) == (x*y)*z;
    dot_neutral_left_c:  forall A B (x: X A B), 1*x == x;
    dot_ann_left_c:  forall A B C (x: X B C), zero A B * x == 0;
    dot_distr_left_c:  forall A B C (x y: X A B) (z: X B C), (x+y)*z == x*z + y*z;

    conv_compat: forall A B, Proper ((equal A B) ==> (equal B A)) (conv A B);
    conv_invol: forall A B (x: X A B), x`` == x;
    conv_dot:  forall A B C (x: X A B) (y: X B C), (x*y)` == y`*x`;
    conv_plus:  forall A B (x y: X A B), (x+y)` == y`+x`
  }.
  
  Class ConverseKleeneAlgebra {Mo: Monoid_Ops} {SLo: SemiLattice_Ops} {Ko: Star_Op} {Co: Converse_Op} := {
    CKA_CISR :> ConverseIdemSemiRing;
    star_make_left_c: forall A (a:X A A), 1 + a#*a == a#;
    star_destruct_left_c: forall A B (a: X A A) (c: X A B), a*c <== c  ->  a#*c <== c
  }.
  
End Structures.
Existing Instance plus_compat.
Existing Instance dot_compat.
Existing Instance inf_compat. 
Existing Instance conv_compat.

Hint Opaque leq equal: compat algebra core.
Typeclasses Opaque equal leq dot plus star one zero ldiv rdiv inf.



(* Structures duales *)
Module Dual. Section Protect.
  Instance Graph `{Graph}: Graph := {
    T := T;
    X A B := X B A;
    equal A B := equal B A;
    equal_equivalence A B := equal_equivalence B A
  }.

  Instance Monoid_Ops `{Mo: Monoid_Ops}: @Monoid_Ops Graph := {
    dot A B C x y := @dot _ Mo C B A y x;
    one := @one _ Mo
  }.

  Instance SemiLattice_Ops `{SLo: SemiLattice_Ops}: @SemiLattice_Ops Graph := {
    plus A B := @plus _ SLo B A;
    zero A B := @zero _ SLo B A
  }.

  Instance CompleteLattice_Ops `{Co: CompleteLattice_Ops}: @CompleteLattice_Ops Graph := {
    sup A B := @sup _ Co B A
  }.

  Instance Inf_Op `{Io: Inf_Op}: @Inf_Op Graph := {
    inf A B := @inf _ Io B A
  }.

  Instance Residual_Ops `{Ro: Residual_Ops}: @Residual_Ops Graph := {
    ldiv := @rdiv _ Ro;
    rdiv := @ldiv _ Ro
  }.

  Instance Star_Op `{Ko: Star_Op}: @Star_Op Graph := {
    star := @star _ Ko
  }.
      
  Instance Converse_Op `{Co: Converse_Op}: @Converse_Op Graph := {
    conv A B := @conv _ Co B A
  }.

  Instance Monoid `{M: Monoid}: @Monoid Graph Monoid_Ops := {
    dot_neutral_left A B := @dot_neutral_right _ _ M B A;
    dot_neutral_right A B := @dot_neutral_left _ _ M B A;
    dot_compat A B C x x' Hx y y' Hy := @dot_compat _ _ M C B A _ _ Hy _ _ Hx
  }.
  Proof.
    intros. symmetry. simpl. apply dot_assoc. 
  Defined.

  Instance SemiLattice `{SL: SemiLattice}: @SemiLattice Graph SemiLattice_Ops := {
    plus_com A B := @plus_com _ _ SL B A;
    plus_idem A B := @plus_idem _ _ SL B A;
    plus_assoc A B := @plus_assoc _ _ SL B A;
    plus_compat A B := @plus_compat _ _ SL B A;
    plus_neutral_left A B := @plus_neutral_left _ _ SL B A
  }.

  Instance IdemSemiRing `{ISR: IdemSemiRing}: @IdemSemiRing Graph Monoid_Ops SemiLattice_Ops.
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

  Instance ResIdemSemiRing `{RISR: ResIdemSemiRing}:
  @ResIdemSemiRing Graph Monoid_Ops SemiLattice_Ops Residual_Ops. 
  Proof.
    intros.
    constructor.
    exact Monoid. 
    exact SemiLattice.
    exact (@rdiv_def _ _ _ _ RISR).
    exact (@ldiv_def _ _ _ _ RISR).
  Defined.

  (* KleeneAlgebra ne peut pas Ãªtre fait ici : prouver star_make_right demande du boulot *)

  Instance ActionAlgebra `{AA: ActionAlgebra}:
  @ActionAlgebra Graph Monoid_Ops SemiLattice_Ops Residual_Ops Star_Op. 
  Proof.
    intros.
    constructor.
    exact ResIdemSemiRing.
    exact (@star_make _ _ _ _ _ AA).
    exact (@star_div_right _ _ _ _ _ AA).
    exact (@star_div_left _ _ _ _ _ AA).
  Defined.

End Protect. End Dual.

Global Opaque equal.

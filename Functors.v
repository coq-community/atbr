(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

Require Import Common.
Require Import Classes.
Require Import SemiLattice.
Require Import KleeneAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.

Record functor (G1 G2: Graph) := {
  fT: @T G1 -> @T G2;
  fX:> forall A B, X A B -> X (fT A) (fT B)
}.  

Section Defs.
  
  Context {G1: Graph} {G2: Graph}.

  Class graph_functor (F: functor G1 G2) := 
    functor_compat: forall A B, Morphism ((equal A B) ==> (equal _ _)) (F A B).
  
  Definition faithful (F: functor G1 G2) :=
    forall A B x y, F A B x == F A B y -> x == y.

  Definition full (F: functor G1 G2) :=
    (* attenttion, définition vicieuse : on ne trouve x que lorsque y a un type de la forme FA -> FB *)
    forall A B y, exists x, F A B x == y.
  
  Class monoid_functor {Mo1: Monoid_Ops (G:=G1)} {Mo2: Monoid_Ops (G:=G2)} (F: functor G1 G2) := {
    monoid_graph_functor :> graph_functor F;
    functor_dot : forall A B C x y, F A C (x*y) == F A B x * F B C y;
    functor_one : forall A, F A A 1 == 1
  }.
  
  Class semilattice_functor 
  {SLo1: SemiLattice_Ops (G:=G1)} {SL2: SemiLattice_Ops (G:=G2)} (F: functor G1 G2) := {
    semilattice_graph_functor :> graph_functor F;
    functor_plus : forall A B x y, F A B (x+y) == F A B x + F A B y;
    functor_zero : forall A B, F A B 0 == 0
  }.
  
  Lemma  functor_incr `{SL1: SemiLattice (G:=G1)} `{SL2: SemiLattice (G:=G2)} {F: functor G1 G2} {HF: semilattice_functor F}:
    forall A B, Morphism ((leq A B) ==> (leq _ _)) (F A B).
  Proof.
    intros. intros x y H. unfold leq. rewrite <- functor_plus. apply functor_compat. trivial.
  Qed.

  Lemma  functor_sum {SL1: SemiLattice_Ops (G:=G1)} `{SL2: SemiLattice (G:=G2)} {F: functor G1 G2} {HF: semilattice_functor F}:
    forall A B i k f, F A B (sum i k f) == sum i k (fun i => F A B (f i)).
  Proof.
    intros. revert i; induction k; intro i.
    apply functor_zero.
    simpl. rewrite functor_plus. apply plus_compat; auto. 
  Qed.
  
  Class semiring_functor
  {Mo1: Monoid_Ops (G:=G1)} {Mo2: Monoid_Ops (G:=G2)} 
  {SLo1: SemiLattice_Ops (G:=G1)} {SL2: SemiLattice_Ops (G:=G2)} (F: functor G1 G2) := {
    semiring_monoid_functor :> monoid_functor F;
    semiring_semilattice_functor :> semilattice_functor F
  }.

  Lemma functor_star_leq `{KA1: KleeneAlgebra (G:=G1)} `{KA2: KleeneAlgebra (G:=G2)} {F: functor G1 G2} {HF: semiring_functor F}:
    forall A a, (F A A a)# <== F A A (a#).
  Proof.
    intros. 
    apply star_destruct_left_one.
    rewrite <- functor_one.
    rewrite <- functor_dot.
    rewrite <- functor_plus.
    apply functor_incr. rewrite star_make_right. reflexivity.
  Qed.

  (* la converse n'est pas forcément vraie, il faut introduire la classe suivante: *)
  
  Class kleene_functor 
  {Mo1: Monoid_Ops (G:=G1)} {Mo2: Monoid_Ops (G:=G2)} 
  {SLo1: SemiLattice_Ops (G:=G1)} {SL2: SemiLattice_Ops (G:=G2)} 
  {Ko1: Star_Op (G:=G1)} {Ko2: Star_Op (G:=G2)} (F: functor G1 G2) := {
    kleene_semiring :> semiring_functor F;
    functor_star: forall A a, F A A (a#) == (F A A a) #
  }.
  
End Defs.


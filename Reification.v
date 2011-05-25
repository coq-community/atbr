(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)


(** Inductives (syntax) and evaluation functions for reifying the various classes from [Classes] *)


Require Import Common Classes.
Require Import FMapPositive.
Require Import Eqdep.
Set Implicit Arguments.
Unset Strict Implicit.

(* generic environments *)
Definition sigma := PositiveMap.t.
Definition sigma_get A default (map: sigma A) (n: positive) : A :=
  match PositiveMap.find n map with 
    | None => default
    | Some x => x
  end.
Definition sigma_add := @PositiveMap.add.
Definition sigma_empty := @PositiveMap.empty.


(* packaged typed values *)
Record Pack {G: Graph} typ := pack { src_p: positive; tgt_p: positive; unpack: X (typ src_p) (typ tgt_p) }.

(* Value environment *)
Class Env {G: Graph} := env { typ: positive -> T; val: positive -> Pack typ }.

(* acces to domain/codomain informations *)
Definition src `{env: Env} i := typ (src_p (val i)).
Definition tgt `{env: Env} i := typ (tgt_p (val i)).


(* heterogeneous dependent equality over pairs of positives *)
Section S.
  Context `{env: Env}.
  
  Definition eqd n m p q (x: X (typ n) (typ m)) (y: X (typ p) (typ q)) := 
    eq_dep (prod positive positive) (fun i => X (typ (fst i)) (typ (snd i))) (n,m) x (p,q) y.
  
  Lemma pos_eq_dec: forall n m: positive, {n=m}+{n<>m}. 
  Proof. decide equality. Qed.

  Lemma eqd_inj: forall n m x y, @eqd n m n m x y -> x = y.
  Proof. intros. apply Eqdep_dec.eq_dep_eq_dec in H; trivial. decide equality; apply pos_eq_dec. Qed.

End S.
Infix " [=] " := eqd (at level 70). 

Module Semiring.
  Section S.
    Context `{env: Env}.
    Inductive X: positive -> positive -> Type :=
    | dot: forall A B C, X A B -> X B C -> X A C
    | one: forall A, X A A
    | plus: forall A B, X A B -> X A B -> X A B
    | zero: forall A B, X A B
    | var: forall i, X (src_p (val i)) (tgt_p (val i)).
    Context {Mo: Monoid_Ops G} {SLo: SemiLattice_Ops G}.
    Fixpoint eval n m (x: X n m): Classes.X (typ n) (typ m) :=
      match x with
        | dot _ _ _ x y => eval x * eval y
        | one _ => 1
        | plus _ _ x y => eval x + eval y
        | zero _ _ => 0
        | var i => unpack (val i)
      end.
  End S.
End Semiring.    

Module KA.
  Section S.
    Context `{env: Env}.
    Inductive X: positive -> positive -> Type :=
    | dot: forall A B C, X A B -> X B C -> X A C
    | one: forall A, X A A
    | plus: forall A B, X A B -> X A B -> X A B
    | zero: forall A B, X A B
    | star: forall A, X A A -> X A A
    | var: forall i, X (src_p (val i)) (tgt_p (val i)).
    Context {Mo: Monoid_Ops G} {SLo: SemiLattice_Ops G} {Ko: Star_Op G}.
    Fixpoint eval n m (x: X n m): Classes.X (typ n) (typ m) :=
      match x with
        | dot _ _ _ x y => eval x * eval y
        | one _ => 1
        | plus _ _ x y => eval x + eval y
        | zero _ _ => 0
        | star _ x => eval x #
        | var i => unpack (val i)
      end.
  End S.
End KA.    

Declare ML Module "reification". 

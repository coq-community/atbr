(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: Quote.v 875 2009-06-09 11:53:22Z braibant $ i*)

Require Import Common.
Require Import Classes.

Section Make.
  Context {G: Graph}.

  Class EVAL := {
    X': Type;
    var: nat -> X';
    eval: forall s t (f: forall i, X (s i) (t i)) A B, X' -> X A B -> Prop;
    eval_var: forall (s t: nat -> T) (f: forall i, X (s i) (t i)) A B,
      forall i x, eval s t f A B (var i) x <-> JMeq x (f i) /\ A=s i /\ B=t i
  }.

  Variable E: EVAL.
  
  (* fonctions d'ajout d'éléments, en tête d'environnements *)
  Definition tcons (A: T) t := fun i => match i with 0 => A | S i => t i end.
  Definition fcons A B (a: X A B) s t (f: forall i, X (s i) (t i)): forall i, X (tcons A s i) (tcons B t i) :=
    fun i => match i with 0 => a | S i => f i end.
  
  (* filtrage/insertion d'un atome en tête d'environnemt *)
  Lemma cons_eval: forall A B a s t f, 
    eval (tcons A s) (tcons B t) (fcons _ _ a s t f) A B (var 0) a.
  Proof. intros; rewrite -> eval_var; tauto. Qed.
  
  (* skip: l'atome doit être placé dans la queue de l'environnement *)
  Lemma tail_eval: forall A B a s t f i A' B' b, 
    eval s t f A' B' (var i) b -> 
    eval (tcons A s) (tcons B t) (fcons A B a s t f) A' B' (var (S i)) b.
  Proof.
    intros.
    rewrite -> eval_var.
    rewrite -> eval_var in H.
    tauto.
  Qed.

  (* prédicat débile, qui permet de garder deux valeurs dans le but (cf
     tactique [quote_monoid], qui a besoin de voir les existentielles de
     son contexte, et d'inventer une valeur de type [X A B] *)
  Inductive Keep (A B: T) (T': Type): X A B -> T' -> Prop := keep: forall x f, Keep A B T' x f.

  Lemma extend_1 P' P: 
    (forall s t f A B x' x, eval s t f A B x' x -> P' x' -> P A B x) ->
    forall s t f A B x' x, eval s t f A B x' x -> Keep A B _ x f -> P' x' -> P A B x.
  Proof. intros; eauto. Qed.

  Lemma extend_2 P' P: 
    (forall s t f A B x' y' x y, 
      eval s t f A B x' x -> eval s t f A B y' y -> P' x' y' -> P A B x y) ->
    forall s t f A B x' y' x y, 
      eval s t f A B x' x -> eval s t f A B y' y -> Keep A B _ x f -> P' x' y' -> P A B x y.
  Proof. intros; eauto. Qed.

  Lemma n_extend_1 Pn P n:
    (forall s t f A B x' x nx, 
      eval s t f A B x' x -> eval s t f A B (n x') nx -> Pn A B nx -> P A B x) ->
    forall s t f A B x' x nx, 
      eval s t f A B x' x -> Keep A B _ x f -> eval s t f A B (n x') nx -> Pn A B nx -> P A B x.
  Proof. intros; eauto. Qed.

  Lemma n_extend_2 Pn P n:
    (forall s t f A B x' y' x y nx ny,
      eval s t f A B x' x -> eval s t f A B y' y -> 
      eval s t f A B (n x') nx -> eval s t f A B (n y') ny -> Pn A B nx ny -> P A B x y) ->
    forall s t f A B x' y' x y nx ny,
      eval s t f A B x' x -> eval s t f A B y' y -> Keep A B _ x f -> 
      eval s t f A B (n x') nx -> eval s t f A B (n y') ny -> Pn A B nx ny -> P A B x y.
  Proof. intros; eauto. Qed.

End Make.

Ltac build_eval E := 
  solve [
    repeat constructor; 
      repeat (apply (cons_eval _ E) || eapply (tail_eval _ E _ _ _ _ _ _ _ _ _ _))
  ] || (print_goal; fail 1 "could not build an evaluation").

Ltac close_eval :=
  lazymatch goal with
    | |- Keep ?G ?A ?B ?T' ?x ?f => 
      instantiate; instantiate (1 := fun _ => x); apply keep
    | _ => print_goal; fail 2 "could not close the environment"
  end.

Ltac quote_ E p := 
  first [
    eapply (extend_2 _ E _ _ p); [
      build_eval E |
      build_eval E |
      close_eval   |
      instantiate
    ] |
    eapply (extend_1 _ E _ _ p); [
      build_eval E |
      close_eval   |
      instantiate
    ] |
    fail 1 "Quote.Typed.quote: mistyped argument"
  ]. 
Ltac quote E p := quote_ E p.

Ltac compute_term :=
  instantiate;
    let u := fresh in
      lazymatch goal with 
        | |- eval ?s ?t ?f ?A ?B ?x' _ => set (u:=x'); vm_compute in u; unfold u; clear u
        | _ => fail 1 "bug in [Quote.reduce] ? (check compute_term)"
      end.

(* TODO: voir comment inserer des abstract ici *)
Ltac reduce E p := 
  first [
    eapply (n_extend_2 _ E _ _ _ p); [
      build_eval E |
      build_eval E |
      close_eval   |
      compute_term; build_eval E |
      compute_term; build_eval E |
      unfold tcons, fcons; instantiate
    ] |
    eapply (n_extend_1 _ E _ _ _ p); [
      build_eval E |
      close_eval   |
      compute_term; build_eval E |
      unfold tcons, fcons; instantiate
    ] |
    fail 1 "Quote.Typed.reduce: mistyped argument"
  ]. 

(*begintests
Module tests. Section tests.
  Context {G: Graph}.
  Parameter p: forall A B, X A B -> X A B -> X A B.
  Parameter z: forall A B, X A B.
  Inductive X' := plus: X' -> X' -> X' | zero: X' | var : nat -> X'.
  Section f.
    Variables s t: nat -> T.
    Variable f: forall i, X (s i) (t i).
    Inductive eval: forall A B, X' -> X A B -> Prop :=
    | e_z: forall A B, eval A B zero (z A B)
    | e_p: forall A B x' y' x y, eval A B x' x -> eval A B y' y -> eval A B (plus x' y') (p A B x y)
    | e_var: forall i, eval _ _ (var i) (f i).
  End f.
  Program Instance E: EVAL G := {
    X' := X';
    var := var;
    eval := eval
  }.
  Admit Obligations.            (* tests *)
  Axiom reduce: forall s t f A B x' x, eval s t f A B x' x -> x'=zero -> x=z A B.
  Axiom reduce2: forall s t f A B x' y' x y, eval s t f A B x' x -> eval s t f A B y' y -> x'=y' -> x=y.

  Goal forall A B x y, p A B (p A B x y) y = z A B.
    intros.
    quote_ E reduce2.
  Abort.

  Fixpoint left p := match p with plus x _ => left x | _ => p end.
  Axiom nreduce2: forall s t f A B x' y' x y nx ny,
    eval s t f A B x' x -> eval s t f A B y' y -> eval s t f A B (left x') nx -> eval s t f A B (left y') ny -> nx=ny -> x=y.

  Goal forall A B x y, p A B (p A B x y) y = p A B x (p A B y (z A B)).
    intros.
    reduce E nreduce2.
  Abort.
End tests. End tests.
endtests*)

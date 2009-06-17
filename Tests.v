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
Require Import Classes.
Require Import Graph.
Require Import Monoid.
Require Import SemiLattice.
Require Import SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiLattice.
Require Import MxSemiRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section tests.

  Context `{KA: KleeneAlgebra}.

  Notation MG := (@mx_Graph G).
  Notation MX := (@X MG).
  Notation X := (@X G).

  Variables A B C: T.
  Variables nA mB nC: MT.

  Variable n: nat.
  Variables M N P: MX nA nA.

  (* reflexivity et normalize, sur == *)
  Goal M*(N+M)*N == (M*1)*((N+M)*N).
    monoid_reflexivity.
  Qed.

  Goal M*(N+M)*N == (M*1)*((N+M)*N).
    monoid_normalize. reflexivity.
  Qed.

  Goal forall n A (M: MX (n,A) (n,A)),  M*M == M*1*M.
    intros.
    patched monoid_normalize. reflexivity.
  Qed.

  Goal M+(N+M)+N*M+0 == N*M+N+M.
    aci_reflexivity.
  Qed.

  Goal M+(N+M)+N*M+0 == N*M+N+M.
    aci_normalize. reflexivity.
  Qed.

  Goal M*(N+M)*N == (M*1)*((N+M)*N) + M*N*N.
    semiring_reflexivity.
  Qed.

  Goal M*(N+M)*N == (M*1)*((N+M)*N) + M*N*N.
    semiring_normalize. reflexivity.
  Qed.



  (* reflexivity et normalize, sur <== *)
  Goal M*(N+M)*N <== (M*1)*((N+M)*N).
    monoid_reflexivity.
  Qed.

  Goal M*(N+M)*N <== (M*1)*((N+M)*N).
    monoid_normalize. reflexivity.
  Qed.

  Goal M+(N+M)+N*M+0 <== N*M+N+M+M*M*M.
    aci_reflexivity.
  Qed.

  Goal M+(N+M)+N*M+0 <== N*M+N+M.
    aci_normalize. reflexivity.
  Qed.

  Goal M*(N+M)*N <== (M*1)*((N+M)*N) + M*N*N + M*(1+N)*M.
    semiring_reflexivity.
  Qed.

  Goal M*(N+M)*N <== (M*1)*((N+M)*N) + M*N*N.
    semiring_normalize. reflexivity.
  Qed.


  (* rewrites simples *)
  Hypothesis H1: M == N.

  Goal P*M+N == P*N+N.
    rewrite H1.
    rewrite <- H1.
  Abort.

  Goal P*M+N <== P*N+N.
    rewrite H1.
    rewrite <- H1 at 3.
    rewrite <- H1 at 2.
  Abort.

  Hypothesis H2: M <== N.

  Goal M <== N*N.
    rewrite H2.
    patched rewrite <- H2 at 2.
  Abort.


  (* ac_rewrite *)
  Hypothesis H3: M+N+P == P.

  Goal M+P+M+N == P.
    ac_rewrite H3.
  Abort.

  Goal M+P+M+N <== P.
    ac_rewrite H3.
  Abort.

  Goal N*(M+P+M+N) == P.
    ac_rewrite H3.
  Abort.

  Goal N*(M+P+M+N) <== P.
    ac_rewrite H3.
  Abort.

  Hypothesis H4: M+N <== P.

  Goal P+N+M <== P.
    ac_rewrite H4.          
    rewrite plus_idem; reflexivity.
  Qed.

  (* monoid_rewrite  *)
  Hypothesis H5: M*N == N.

  Goal N*M*M*N == N*N.
    monoid_rewrite H5.
    monoid_rewrite H5.
    reflexivity.
  Qed.

  Goal P*M*M*N <== P*N.
    monoid_rewrite H5.
    monoid_rewrite H5.
    reflexivity.
  Qed.

  Goal P+M*M*N == N+P.
    monoid_rewrite H5.
    monoid_rewrite H5.
    aci_reflexivity.
  Qed.

  Hypothesis H6: M*N <== N.

  Goal P*M*M*N <== P*N.
    monoid_rewrite H6.
    monoid_rewrite H6.
    reflexivity.
  Qed.

  Goal P+M*M*N <== N+P.
    monoid_rewrite H6.
    monoid_rewrite H6.
    aci_reflexivity.
  Qed.

  Hypothesis H7: M <== M*N.

  Goal P*M <== P*M*N.
    monoid_rewrite <- H7.
    reflexivity.
  Qed.

End tests.

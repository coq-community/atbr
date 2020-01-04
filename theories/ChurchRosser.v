(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Short mechanised proofs of the Church-Rosser Theorems mentioned by Georg Struth in
   #<a href="http://link.springer.de/link/service/series/0558/bibs/2561/25610276.htm">
   Calculating Church-Rosser Proofs in Kleene Algebra</a>#.
*)

Require Import ATBR.

Set Implicit Arguments.
Unset Strict Implicit.

Section Props1.

  Context `{KA: KleeneAlgebra}.

  Theorem SemiConfluence_is_WeakConfluence A:
    forall (a b : X A A), b * a# <== a# * b#  <->  b# * a# <== a# * b#.
  Proof.
    intros a b; split.
     apply wsemicomm_iter_left. 
     intro H. rewrite <- H. kleene_reflexivity.
  Qed.

  Theorem SemiConfluence_is_ChurchRosser A:
    forall (a b : X A A), b * a# <== a# * b#  <->  (a+b)# <== a# * b#.
  Proof.
    intros a b; split; intro H.
     star_left_induction.
     semiring_normalize. 
     rewrite H. kleene_reflexivity.

     rewrite <- H. kleene_reflexivity. 
  Qed.

  Theorem WeakConfluence_is_ChurchRosser A:
    forall (a b : X A A), b# * a# <== a# * b#  <->  (a+b)# <== a# * b#.
  Proof.
    intros a b; split; intro H.
     star_left_induction.
     semiring_normalize. 
     rewrite (a_leq_star_a b) at 2.
     rewrite H. kleene_reflexivity.

     rewrite <- H. kleene_reflexivity. 
  Qed.


  Theorem BubbleSort A:
    forall (a b : X A A), b * a <== a * b  ->  (a+b)# <== a# * b#.
  Proof.
    intros a b; intro H.
     star_left_induction.
     semiring_normalize. 
     apply semicomm_iter_left, semicomm_iter_right in H.
     rewrite (a_leq_star_a b) at 2.
     rewrite H. kleene_reflexivity.
  Qed.

  Notation "a ^+" := (a * a#) (at level 15).


  Theorem WeakConfluence_is_ChurchRosser_plus A:
    forall (a b : X A A), b^+ * a# <== a# * b^+ + a^+ * b#  <->  (a+b)^+ <== a# * b^+ + a^+ * b#.
  Proof.
    intros a b; split; intro H.
     star_right_induction.
     rewrite (a_leq_star_a a) at 5. 
     rewrite <- (star_make_right b) at 2. 
     semiring_normalize.
     monoid_rewrite H. 
     unfold leq.  kleene_reflexivity.

     rewrite <- H. kleene_reflexivity. 
  Qed.


  Lemma star_plus_one A: forall (a: X A A), a# == (a+1)#.
  Proof. intros. kleene_reflexivity. Qed.

  Lemma star_plus_star A: forall (a b: X A A), (a+b)# == (a#+b#)#.
  Proof. intros. kleene_reflexivity. Qed.

  Theorem Hindley_Rosen A: forall (a b : X A A), 
    b*a <== a#*(b+1) -> b#*a# <== a#*b#.
  Proof.
    intros.
    do 2 rewrite (star_plus_one b) at 1.
    apply semicomm_iter_left.
    rewrite <- (star_idem a) at 2.
    apply semicomm_iter_right.
    semiring_normalize.
    rewrite H. kleene_reflexivity.
  Qed.

  Theorem Hindley_Rosen_union A:  forall (a b c : X A A), 
    c#*a# <== a#*c# ->
    c#*b# <== b#*c# ->
    c#*(a+b)# <== (a+b)#*c#.
  Proof.
    intros a b c Ha Hb.
    do 2 rewrite (star_plus_star a b) at 1.
    apply semicomm_iter_right.
    semiring_normalize. auto with compat.
  Qed.

End Props1.


Section Props2.

  Context `{KA: ConverseKleeneAlgebra}.

  Theorem Hindley_Rosen_confluent_union A: forall (a b : X A A), 
    a`#*a# <== a#*a`# ->
    b`#*b# <== b#*b`# ->
    a`#*b# <== b#*a`# ->
    (a+b)`#*(a+b)# <== (a+b)#*(a+b)`#.
  Proof.
    intros a b Ha Hb Hab.
    do 2 rewrite conv_plus at 1.
    do 2 rewrite (star_plus_star (b`) (a`)) at 1.
    apply semicomm_iter_left. semiring_normalize. 
    rewrite 2 Hindley_Rosen_union; trivial with algebra.
    switch. assumption.
  Qed.

End Props2.


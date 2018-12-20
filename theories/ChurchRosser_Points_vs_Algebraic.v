(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*             (see file LICENSE.txt for more details)                    *)
(*                                                                        *)
(*  Copyright 2009: Thomas Braibant, Damien Pous.                         *)
(**************************************************************************)

(** This file illustrates why it might be easier to work with binary
    relations in an algebraic setting, through a very simple
    Church-Rosser proof. The corresponding .v file is #<a
    href="ChurchRosser_Points_vs_Algebraic.v">here</a>#. *)

Require Import ATBR.
Require Import Relations.

Goal True. Abort.


(** * Standard proof: binary relations relate points to points *)
Section CR_points.
  
  Variable P: Set.
  Variables R S: relation P.

  (** notations for reflexive transitive closure and relations union *)
  Notation "R #" := (clos_refl_trans_1n _ R).
  Notation "R + S" := (union _ R S).

  Definition WeakConfluence :=
    forall p r q, R p r -> S# r q -> exists2 s, S# p s & R# s q.

  Definition ChurchRosser := 
    forall p q, (R+S)# p q -> exists2 s, S# p s & R# s q.


  (** naive proof *)
  Theorem WeakConfluence_is_ChurchRosser0: 
    WeakConfluence -> ChurchRosser.
  Proof.
    intros H p q Hpq. induction Hpq as [p | p q q' Hpq Hqq' IH].
     exists p. constructor. constructor.
     destruct Hpq as [Hpq|Hpq].
      destruct IH as [s' Hqs' Hs'q'].
      destruct (H p q s' Hpq Hqs') as [s Hps Hss'].
      exists s. assumption. 
      apply trans_rt1n. 
      apply rt_trans with s'; apply rt1n_trans; assumption. 
    
      destruct IH as [s Hqs Hsq'].
      exists s. 
      apply Relation_Operators.rt1n_trans with q; assumption.
      assumption.
  Qed.


  (** slightly more automatised proof *)
  Theorem WeakConfluence_is_ChurchRosser0': 
    WeakConfluence -> ChurchRosser.
  Proof.
    intros H p q Hpq. induction Hpq as [p | p q q' Hpq Hqq' IH].
     eexists; constructor. 
     destruct Hpq as [Hpq|Hpq].
      destruct IH as [s' Hqs' Hs'q'].
      destruct (H p q s' Hpq Hqs').
      eauto 6 using trans_rt1n, rt_trans, rt1n_trans.
    
      destruct IH as [s Hqs Hsq'].
      eauto using Relation_Operators.rt1n_trans. 
  Qed.  

End CR_points.



(** * Algebraic proof, using standard properties of binary relations *)
Section CR_algebra.

  (** we move to the algebraic setting  *)
  Context `{KA: KleeneAlgebra}.

  Variable A: T.
  Variables R S: X A A.


  (** same proof, without points ;
     '<==' corresponds to relations inclusion *)
  Theorem WeakConfluence_is_ChurchRosser1: 
    R * S# <== S# * R# -> (R+S)# <== S# * R#.
  Proof.
    intro H.
    star_left_induction.
    rewrite dot_distr_left.
    repeat apply plus_destruct_leq. 
     do 2 rewrite <- one_leq_star_a. 
     rewrite dot_neutral_left. reflexivity.
     rewrite dot_assoc. rewrite H. 
     rewrite <- dot_assoc. rewrite (star_trans R). reflexivity.
     rewrite dot_assoc. rewrite a_star_a_leq_star_a. reflexivity.
  Qed.


  (** with high-level tactics, some administrative step can be handled automatically *)
  Theorem WeakConfluence_is_ChurchRosser2:
    R * S# <== S# * R# -> (R+S)# <== S# * R#.
  Proof.
    intro H.
    star_left_induction.
    semiring_normalize.
    repeat apply plus_destruct_leq. 
     do 2 rewrite <- one_leq_star_a. semiring_reflexivity.
     rewrite H. monoid_rewrite (star_trans R). reflexivity.
     rewrite a_star_a_leq_star_a. reflexivity.
  Qed.


  (** even better, with our tactic for Kleene algebras *)
  Theorem WeakConfluence_is_ChurchRosser3:
    R * S# <== S# * R# -> (R+S)# <== S# * R#.
  Proof.
    intro H.
    star_left_induction.
    semiring_normalize. 
    rewrite H. 
    kleene_reflexivity.
  Qed.  

End CR_algebra.

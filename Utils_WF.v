(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Several results to ease the definition and the analysis of
   (well-founded) recursive functions *)

Require Import Common.
Set Implicit Arguments.

(** Trick to compute with well-founded recursions: lazily add 2^n
   Acc_intro constructors in front of a well_foundedness proof, so
   that the actual proof is never reached in practise *)
Fixpoint guard A (R: A -> A -> Prop) n (wfR: well_founded R): well_founded R :=
  match n with
    | 0 => wfR
    | S n => fun x => Acc_intro x (fun y _ => guard  n (guard n wfR) y)
  end.

(** Lexicographic product of two well-founded relations *)
Section lexico.
  Variables A B: Type.
  Variable R: relation A.
  Variable S: relation B.
  Inductive lexico: relation (A*B) :=
    | lexico_left: forall a a' b b', R a' a -> lexico (a',b') (a,b)
    | lexico_right: forall a b b', S b' b -> lexico (a,b') (a,b)
      .
  Hypothesis HR: well_founded R.
  Hypothesis HS: well_founded S.
  Theorem lexico_wf: well_founded lexico.
  Proof.
    intros [a b]. revert b.
    induction a as [a IHa] using (well_founded_induction HR).
    induction b as [b IHb] using (well_founded_induction HS).
    constructor. intros [a' b'] H. inversion_clear H; auto.
  Qed.
End lexico.

(** A relation contained in a well-founded relation is well-founded *)
Section wf_incl.
  Variable A: Type.
  Variable S: relation A.
  Hypothesis HS: well_founded S.
  Variable R: relation A.
  Hypothesis H: forall a' a, R a' a -> S a' a.
  Theorem incl_wf: well_founded R.
  Proof.
    intros a. induction a as [a IHa] using (well_founded_induction HS).
    constructor. eauto.
  Qed.
End wf_incl.

(** Equivalent of [well_founded_ltof], using an underlying well-founded relation *)
Section wf_of.
  Variables U V: Type.
  Variable f: U -> V.
  Variable R: relation V.
  Hypothesis HR: well_founded R.
  Definition rel_of: relation U := fun a' a => R (f a') (f a).
  Theorem rel_of_wf: well_founded rel_of.
  Proof.
    unfold rel_of.
    intro a. remember (f a) as fa. revert a Heqfa.
    induction fa as [fa IHa] using (well_founded_induction HR).
    constructor. intros a' H. subst. eauto. 
  Qed.
End wf_of.

(** Similarly, in the other direction  *)
Section wf_to.
  Variables U V: Type.
  Variable f: U -> V.
  Variable R: relation U.
  Inductive rel_to: relation V :=
    rel_to_intro: forall a' a, R a' a -> rel_to (f a') (f a).
  Hypothesis HR: well_founded rel_to.
  Theorem rel_to_wf: well_founded R.
    intro a. remember (f a) as fa. revert a Heqfa.
    induction fa as [fa IHa] using (well_founded_induction HR).
    constructor. intros a' H. subst. eapply IHa; trivial. constructor. trivial.
  Qed.
End wf_to.

(** Combination of the above reductions : reduction to a lexicographic product of two well-founded relations *)
Section wf_lexico_incl.
  Variables U A B: Type.
  Variable f: U -> A*B.
  Variable RA: relation A.
  Variable RB: relation B.
  Hypothesis HRA: well_founded RA.
  Hypothesis HRB: well_founded RB.
  Variable R: relation U.
  Hypothesis H: forall u' u, R u' u -> lexico RA RB (f u') (f u).
  Theorem lexico_incl_wf: well_founded R.
  Proof.
    apply (rel_to_wf (f:=f)). eapply incl_wf. apply lexico_wf; eassumption. 
    intros [a' b'] [a b] [u' u Hab]. auto. 
  Qed.
End wf_lexico_incl.
   

(** Lazy partial fixpoint operators (lazy iterator):
    we use these functions to avoid the computation of a (2^n) worst-case
    bound which is never reached in practise *)
Section powerfix.

  Variables A B: Type.
  Notation Fun := (A -> B).

  (** the three following functions "iterate" their [f] argument lazily: iteration stops whenever [f] 
     no longer makes recursive calls.
     - [powerfix' n f k] iterates [f] at most [(2^n-1)] times and then yields to [k] 
     - [powerfix n f k] iterates [f] at most [(2^n)] times and then yields to [k] 
     - [linearfix n f k] iterates [f] at most [n] times and then yields to [k] 
     *)
  Fixpoint powerfix' n (f: Fun -> Fun) (k: Fun): Fun := 
    fun a => match n with O => k a | S n => f (powerfix' n f (powerfix' n f k)) a end.
  Definition powerfix n f k a := f (powerfix' n f k) a.
  Fixpoint linearfix n (f: Fun -> Fun) (k: Fun): Fun :=
    fun a => match n with O => k a | S n => f (linearfix n f k) a end.

  (** [power n = 2^n] *)
  Fixpoint power n := match n with O => 1 | S n => 2*power n end.

  Lemma power_positive: forall n, 0 < power n.
  Proof. induction n; simpl; omega. Qed.

  (** Characterisation of [powerfix] with [linearfix] *)
  Section linear_carac.

    Context {R} `{E: Equivalence B R}.
    Variable f: Fun -> Fun.
    (** the functional [f] as to use its first argument "in extension" *)
    Hypothesis Hf: Proper (pointwise_relation A R ==> @eq A ==> R) f.

    Instance linearfix_compat n: 
      Proper (pointwise_relation A R ==> pointwise_relation A R) (linearfix n f).
    Proof.
      induction n; intros k k' H a; simpl. 
       apply H.
       apply Hf; auto.
    Qed.

    Lemma linearfix_plus: forall n m k, pointwise_relation A R 
      (linearfix n f (linearfix m f k)) (linearfix (n + m) f k).
    Proof.
      induction n; intros m k a; simpl.
       reflexivity.
       rewrite IHn. reflexivity.
    Qed.

    Instance powerfix'_compat n: 
      Proper (pointwise_relation A R ==> pointwise_relation A R) (powerfix' n f).
    Proof.
      induction n; intros k k' H a; simpl.
       apply H.
       apply Hf; auto.
    Qed.

    Instance powerfix_compat n: 
      Proper (pointwise_relation A R ==> pointwise_relation A R) (powerfix n f).
    Proof.
      intros k k' H. unfold powerfix. setoid_rewrite H. reflexivity.
    Qed. 

    Lemma powerfix'_linearfix: forall n k, 
      pointwise_relation A R (powerfix' n f k) (linearfix (pred (power n)) f k).
    Proof.
      induction n; intros; simpl; intro a.
       reflexivity.
       rewrite IHn. rewrite IHn.
       pose proof (power_positive n). 
       replace (pred (power n + (power n + 0))) with (S (pred (power n) + pred (power n))) by omega.
       rewrite linearfix_plus.
       reflexivity.
    Qed.

    (** The expected characterisation  *)
    Theorem powerfix_linearfix: forall n k, 
      pointwise_relation A R (powerfix n f k) (linearfix (power n) f k).
    Proof.
      intros. unfold powerfix. setoid_rewrite powerfix'_linearfix.
      generalize (power_positive n). destruct (power n). 
       intro. omega_false.
       intro. reflexivity.
    Qed.

  End linear_carac.

  (** [powerfix_invariant] gives an induction principle for [powerfix], that does not care 
     about the number of iterations -- in particular, the trivial "emptyfix" function : 
     ([fun f k a => k a]) satisfies the same induction principle, so that this can only be 
     used to reason about partial correctness. *)
  Section invariant.
    Variable P: Fun -> Prop.
    Hypothesis HP: forall k, P k -> P (fun a => k a).
    (* Alternative hypothesis: *)
    (* Hypothesis HP: Proper (pointwise_relation A (@eq B) ==> iff) P. *)
    Lemma powerfix'_invariant': forall n f g, (forall k, P k -> P (f k)) -> P g -> P (powerfix' n f g).
    Proof.
      induction n; intros f g Hf Hg; simpl; apply HP; auto.
    Qed.
    Lemma powerfix_invariant': forall n f g, (forall k, P k -> P (f k)) -> P g -> P (powerfix n f g).
    Proof.
      intros n f g Hf Hg. apply HP, Hf, powerfix'_invariant'; assumption. 
    Qed.
  End invariant.

End powerfix.

(** Another way to construct well-founded relations: start with a well-founded one (e.g., the empty one), 
   and progressively add pairs satisfying some acyclicity property w.r.t. the current relation *)
Section add_pair.
  Require Import Relations.

  Variable T: Set.
  Definition add_pair i j R: relation T := fun s t => s=i /\ t=j \/ R s t.
  
  Lemma wf_add_pair: forall R, well_founded R -> 
    forall i j, ~ clos_refl_trans T R j i -> well_founded (add_pair i j R).
  Proof. 
    intros R Hwf i j Hij.

    assert (Hi: forall v, clos_refl_trans _ R v i -> Acc (add_pair i j R) v).
     induction v as [v IH] using (well_founded_induction Hwf); intros Hui.
     constructor. intros u [[-> ->]|Huv]. 
      elim Hij. assumption.
      apply IH. assumption. 
      eauto using rt_trans, rt_step.

    intro v. induction v as [v IH] using (well_founded_induction Hwf).
    constructor. intros u [[-> ->] | Huv].
     apply Hi. constructor 2.
     apply IH. assumption.
  Qed.
End add_pair.  

(** An induction principle for [Fix], which is less demanding than the corresponding results 
   of the standard library (no additional hypothesis about [P] or [F]) *)
Section Fix_induction.
  Variable A: Type.
  Variable R: relation A.
  Hypothesis Hwf: well_founded R.
  Variable T: A -> Type.
  Variable F: forall x, (forall y, R y x -> T y) -> T x.
  Variable P: forall x, T x -> Prop.
  
  Hypothesis IH: forall x (G: forall y, R y x -> T y), (forall y (H: R y x), P (G y H)) -> P (F G).
  Theorem Fix_induction: forall x, P (Fix Hwf _ F x).
  Proof.
    unfold Fix. intro x. generalize (Hwf x) as Hx. 
    induction x as [x IHwf] using (well_founded_induction Hwf); intros.
    rewrite <- Fix_F_eq. auto.
  Qed.
End Fix_induction.
Arguments Fix_induction [A R] Hwf [T F P].

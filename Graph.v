(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Basic properties, definitions and hints about the [Classes.Graph] base-class *)

Require Import Common.
Require Import Classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section equal.

  Context {G: Graph}.
  Variables A B: T.

  (** projections, for auto, or to help in manual proofs *)
  Lemma equal_refl x: equal A B x x.
  Proof. intros; apply Equivalence_Reflexive. Qed.
  Lemma equal_sym x y: equal A B x y -> equal A B y x.
  Proof. intros; apply Equivalence_Symmetric; trivial. Qed.
  Lemma equal_trans x y z: equal A B x y -> equal A B y z -> equal A B x z.
  Proof. intros; eapply Equivalence_Transitive; eauto. Qed.

  (** Lemmas to solve automatically some index related goals (a la f_equal)*)
  Lemma equal_refl_f1 (f: nat -> X A B): 
    forall i i', i = i' -> f i == f i'.
  Proof. intros; subst; reflexivity. Qed.
  Lemma equal_refl_f2 (f: nat -> nat -> X A B): 
    forall i i' j j', i=i' -> j=j' -> f i j == f i' j'.
  Proof. intros; subst ; reflexivity. Qed.
  
  Lemma equal_refl_f1t Z (f: nat -> Z -> X A B): 
    forall t i i', i = i' -> f i t == f i' t.
  Proof. intros; subst ; reflexivity. Qed.
  Lemma equal_refl_f2t Z (f: nat -> nat -> Z -> X A B): 
    forall t i i' j j', i=i' -> j=j' -> f i j t == f i' j' t.
  Proof. intros; subst ; reflexivity. Qed.


  (** boolean test *)
  Definition xif (b: bool) (x y: X A B) := if b then x else y.

  Global Instance xif_compat: Proper (@eq bool ==> equal A B ==> equal A B ==> equal A B) xif.
  Proof. intros c b ->; repeat intro. destruct b; auto. Qed.

  Lemma xif_spec: forall b x y z, (b=true -> x==z) -> (b=false -> y==z) -> xif b x y == z.    
  Proof. intros. destruct b; auto. Qed.

  Lemma xif_false: forall b x y, b=false -> xif b x y == y.    
  Proof. intros ? ? ? ->; reflexivity. Qed. 

  Lemma xif_true: forall b x y, b=true -> xif b x y == x.    
  Proof. intros ? ? ? ->; reflexivity. Qed. 

  Lemma xif_idem: forall b x, xif b x x == x.
  Proof. destruct b; reflexivity. Qed.

  Lemma xif_idem': forall b x y, x == y -> xif b x y == x.
  Proof. intros b x y H. rewrite H. apply xif_idem. Qed.

  Lemma xif_xif_and: forall b c x y, xif b (xif c x y) y == xif (b&&c) x y.
  Proof. destruct b; reflexivity. Qed.

  Lemma xif_xif_or: forall b c x y, xif b x (xif c x y) == xif (b||c) x y.
  Proof. destruct b; reflexivity. Qed.

  Lemma xif_negb: forall b x y, xif (negb b) x y == xif b y x.
  Proof. destruct b; reflexivity. Qed.

End equal.


Lemma fun_xif {G G': Graph} A B A' B' (f: @X G A B -> @X G' A' B') b x y: f (xif b x y) == xif b (f x) (f y).
Proof. destruct b; reflexivity. Qed.



Section leq.
  (** Basic properties of the underlying preorder *)
  Context `{SL: SemiLattice}.
  Variables A B: T.

  Global Instance leq_refl: Reflexive (leq A B).
  Proof. intro. apply plus_idem. Qed.

  Global Instance leq_trans: Transitive (leq A B).
  Proof. 
    intros x y z E E'; unfold leq in *.
    rewrite <- E', plus_assoc, E; reflexivity. 
  Qed.

  Global Instance equal_leq: subrelation (equal A B) (leq A B).
  Proof.
    intros x y E; unfold leq; rewrite E; apply plus_idem.
  Qed.

  Global Instance equal_geq: subrelation (equal A B) (Basics.flip (leq A B)).
  Proof. repeat intro; apply equal_leq; symmetry; auto. Qed.

  Definition leq_antisym: Antisymmetric _ _ (leq A B).
    intros x y H1 H2; unfold leq in *; rewrite <- H2, plus_com, H1; reflexivity. 
  Qed.
End leq.


Hint Resolve @equal_refl.
Hint Immediate @equal_sym.
 
(* BUG : If we add [equal_refl_fit] as hints, they are added as eapply ...*)

Hint Resolve @equal_refl_f1 @equal_refl_f2.
(* Hint Resolve @equal_refl_f1t @equal_refl_f2t *)

Hint Extern 1 (equal ?A ?B (?f (_: nat) ?t) (?f _ ?t)) => apply @equal_refl_f1t.
Hint Extern 2 (equal ?A ?B (?f (_: nat) (_: nat) ?t) (?f _ _ ?t)) => apply @equal_refl_f2t.  

Hint Extern 3 (_ == _) => apply @xif_compat.

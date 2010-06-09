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
Require Import SemiLattice.
Require Import ATBR.SemiRing.
Require Import Monoid.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.
Require Import BoolAlg.
Require Import FreeKleeneAlg.
Require Import Force.
Require Import Isomorphism.
Require Import Functors MxFunctors.

Require Import DKA_Annexe.
Require Import DKA_Algo.

Require DKA_SimpleMinimisation.
Module Minimisation := DKA_SimpleMinimisation.

Import Min Minimisation.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Transparent equal.

Definition Termination := Minimisation.Termination.
  

Lemma alg_eval `{KleeneAlgebra} B B' A C: forall 
  (x :X B B') (u : X A B) m  (v : X B C) u' m' v',
  u' == u * x ->
  x * m'  == m * x ->
  x * v' == v ->
  u'*m'#*v' == u* m# *v.  
Proof.
  intros.
  rewrite  H0. 
  monoid_rewrite (comm_iter_right H1).
  semiring_normalize. monoid_rewrite H2. monoid_reflexivity.
Qed.

Section Correction.
  
  Existing Instance bool_SemiLattice_Ops. 
  Existing Instance bool_Monoid_Ops.
  Existing Instance bool_Star_Op.
  Existing Instance bool_SemiLattice.
  Existing Instance bool_Monoid.
  Existing Instance bool_SemiRing.
  Existing Instance bool_KleeneAlgebra.
  
  Existing Instance KAF_SemiLattice_Ops. 
  Existing Instance KAF_Monoid_Ops.
  Existing Instance KAF_Star_Op.
  Existing Instance KAF_SemiLattice.
  Existing Instance KAF_Monoid.
  Existing Instance KAF_SemiRing.
  Existing Instance KAF_KleeneAlgebra.
  
  


                         (********************)
                         (** * Myhill Nerode *)
                         (********************)

  Definition proj_sumbool (P Q: Prop) (a: {P} + {Q}) : bool :=
    if a then true else false.
  
  Implicit Arguments proj_sumbool [P Q].
  
  Coercion proj_sumbool: sumbool >-> bool.
  
  Section Minimisation.
  Variable AUT : DFA. 
  Hypothesis Hwf : DFA_wf AUT.
  Notation size := (D_size AUT).
  Notation delta := (D_delta AUT).
  Notation finaux := (D_finaux AUT).
  Notation max_label := (D_max_label AUT).
  Notation states := (smh_states AUT).
  Notation initial := (D_initial AUT).

  Definition partition_AUT : StateSetSet.t := Min.partition (Minimisation.Termination AUT). 
  Definition classes := StateSetSet.cardinal (partition_AUT).

  Definition classe : nat -> nat := fun s => classe AUT s.
  
  Definition is_in_classe_final : nat -> bool := fun x => StateSet.mem x  finaux .

  Notation Local "[ p ]" := (classe p).
  Definition caract n (s : nat) : BMX (1%nat, n) := box 1 n (fun _ j => eq_nat_dec s j: @X bool_Graph tt tt).
   
  Definition caract_AUT p : BMX (1%nat, size) := caract size p.

  Definition E p : BMX (1%nat,classes)  := caract classes p.  
  
  Lemma lt_states : forall x, x < size -> StateSet.In x states.
  Proof. 
     intros. apply -> DKA_Sets.fold_labels_add; auto.
  Qed.
 
  Lemma states_lt : forall x, StateSet.In x states ->  x < size .
  Proof. 
     intros. apply <- DKA_Sets.fold_labels_add; auto. 
  Qed.

  Lemma finaux_subset_states : StateSet.Subset finaux states.
  Proof.
    repeat intro. apply lt_states. unfold DFA_wf, below in Hwf. destruct Hwf as [ _ [Hfa _]].  apply Hfa. auto.
  Qed.
  
  Hint Resolve finaux_subset_states.
  
  Hint Resolve lt_states states_lt.
  
  (* On recupere les lemmes qui viennet de l'annexe *)

  Lemma classe_lt_classes : forall x, x < size -> (classe x < classes)%nat.
    intros. apply Minimisation.classe_lt_classes; auto. 
  Qed.
   
  Lemma classe_2 : forall j p a, j < size -> p < size -> a < max_label -> [j] = [p] -> [delta j a] = [delta p a].
    intros.
    unfold DFA_wf in Hwf.
    apply  Minimisation.classe_2; intuition.
  Qed.

  Lemma classe_3 : forall j p , j < size  -> p < size -> [j] = [p] -> StateSet.mem j finaux = StateSet.mem p finaux.
    intros.
    unfold DFA_wf in Hwf.
    apply  Minimisation.classe_3; intuition.
  Qed.

  Lemma classe_4 :  forall x y, x < size  -> y < size -> equiv (Minimisation.Termination AUT)  x y = true -> [x] = [y]. 
    intros. apply Minimisation.classe_4; auto.
  Qed.

  Lemma finaux_lt : forall p, StateSet.In p finaux -> p < size.
  Proof.
    intros.
    unfold DFA_wf in Hwf. auto.
  Qed.
  Hint Resolve finaux_lt.
  
  (* X_minimise i j == true <-> j in classe [i] *)
  (* transpose X_minimise i j == true <-> i in classe [j] *)  
  Notation Aut' := (DFA_to_bAut AUT)
    .
  Definition X_minimise : BMX (size, classes) := box (G := bool_Graph) size classes (fun i j =>  eq_nat_dec [i] j).
  Notation X := (convert X_minimise).
  Notation U := (b_U Aut').
  Notation V := (b_V Aut').
  Notation M := (b_M Aut').

  Definition bMrre_a   a : BMX (classes, classes) := MxGraph.transpose X_minimise * b_M Aut' a * X_minimise.
  Definition bUrre : BMX (1%nat, classes) := b_U Aut'* X_minimise.
  Definition bVrre  : BMX (classes, 1%nat) := MxGraph.transpose X_minimise * b_V Aut'.   
 
  Definition minimised  :=   @Build_bAut classes  (* classes (* on a un automate qui a un etat par classe *) *)
    0       (* toujours pas de J                         *)
    bMrre_a (* la nouvelle matrice de transition         *)
    bUrre   (* le vecteur initial nouvelle version       *)
    bVrre   (* les etats acceptants                      *)
    max_label.

  Lemma help1 A x : eval_b (DFA_to_bAut (change_initial_D A x)) == eval_b ( change_initial_b (DFA_to_bAut A) x).
  Proof.
    intros. unfold eval_b. apply eval_M_compat. apply bAut_MAut_eq.
    constructor; simpl; intuition. 
  Qed.

  Opaque equal dot plus one zero star.

  Lemma eq_nat_dec_eq i j: is_true (eq_nat_dec i j) <-> i=j. 
  Proof.
    destruct_nat_dec; simpl; firstorder.
  Qed.

  Lemma and_com P Q: P /\ Q <-> Q /\P.
  Proof. tauto. Qed.

  Lemma and_assoc P Q R: P /\ (Q /\ R) <-> (P /\ Q) /\ R.
  Proof. tauto. Qed.

  Lemma and_neutral_right (P Q: Prop): P -> (Q /\ P <-> Q).
  Proof. tauto. Qed.
    
  Lemma and_impl (P Q: Prop): (P -> Q) -> (P/\Q <-> P).
  Proof. tauto. Qed.

  Lemma and_impl' W (P Q: W -> Prop): (forall x, P x -> Q x) -> ((exists x, P x /\ Q x) <-> exists x, P x).
  Proof. firstorder. Qed.

  Lemma exists_eq W (v: W) (P: W -> Prop): (exists x, v=x /\ P x)  <-> P v.
  Proof. intros. firstorder. subst. assumption. Qed.


  Lemma eq_symm: forall A (i j: A), i = j <-> j = i.
  Proof. firstorder. Qed.

  Lemma minimisation_change x : x < size -> 
    eval_b (change_initial_b  Aut' x) == eval_b (change_initial_b (minimised) [x]).
  Proof.
   intros Hx.
   unfold change_initial_b.   simpl b_size. symmetry. apply alg_eval with  X; simpl.  
   
   (* bloc 1 : u' == u * x *)
   unfold X_minimise.      rewrite <- convert_dot. apply convert_compat. 
   mx_intros i j Hi Hj. simpl.
   apply bool_view. rewrite mxbool_dot_spec.
   simpl. setoid_rewrite eq_nat_dec_eq.  setoid_rewrite and_com; setoid_rewrite <- and_assoc.
   setoid_rewrite (eq_symm). setoid_rewrite exists_eq. intuition.
   
   (* bloc 2 : X * M' == M * X *)
    setoid_rewrite convert_zero. setoid_rewrite plus_neutral_left.
    symmetry. apply convert_sum_commute. unfold bMrre_a, X_minimise, MxGraph.transpose. do 2 setoid_rewrite dot_assoc. 
    intros b Hb. mx_intros i j Hi Hj.

    simpl.
    apply bool_view. simpl. do 3  setoid_rewrite mxbool_dot_spec. simpl. 
    setoid_rewrite eq_nat_dec_eq.
    setoid_rewrite and_com. setoid_rewrite <- and_assoc. 
    rewrite exists_eq. rewrite and_neutral_right. 2: unfold DFA_wf in Hwf; intuition.

    intuition. exists (delta i b). unfold DFA_wf in Hwf.
      intuition.
      exists i; intuition. 
      exists [i]; intuition auto using classe_lt_classes. 

      destruct H as [k [Hk' Hk]].
      destruct Hk' as [y [Hy [H' Hk']]].
      rewrite <- Hk' in *. clear Hk'. destruct Hk as [ <- _].  
      destruct H' as [k' [Hk' [Hk1 Hk2]]].  rewrite <- Hk2 in Hk1. clear Hk2. 
      apply classe_2; auto.

    (* bloc 3 X * V' == V*)
    unfold X_minimise. rewrite <-convert_dot. 
    apply convert_compat. 
    mx_intros i j Hi Hj. simpl.
    unfold bVrre, MxGraph.transpose. 
    apply bool_view. setoid_rewrite mxbool_dot_spec.  setoid_rewrite mxbool_dot_spec.  
    simpl. setoid_rewrite eq_nat_dec_eq.  setoid_rewrite and_com; setoid_rewrite <- and_assoc.
    setoid_rewrite exists_eq.
    
    intuition. destruct H0 as [k Hk].  destruct Hk as [Hk [Hk' Hk'']].
    rewrite Hk''. Transparent equal. simpl.  apply classe_3; auto.
    exists i; auto.
    apply classe_lt_classes; auto.
  Qed.

  End Minimisation.
  
  Theorem correct: forall A x y,
    x < D_size A ->     y < D_size A -> 
    DFA_wf A -> Min.equiv (Minimisation.Termination A) x y = true -> eval_D (change_initial_D A x) == eval_D (change_initial_D A y).
  Proof.
    intros.
    unfold eval_D.
    rewrite 2 help1.
    rewrite minimisation_change by auto. symmetry. rewrite minimisation_change by auto. symmetry. (* BUG : setoid_rewrite minimisation_change *)
    
    assert (classe A x = classe A y). apply classe_4; auto.
    rewrite H3. reflexivity.
  Qed.

End Correction.

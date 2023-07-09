(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Proof that the evaluation of a DFA is actually the language
   recognised by that DFA.
   
   This is required to prove the completeness of the decision
   procedure.
   *)

Require Import List.

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
Require Import MxKleeneAlgebra.
Require Import Functors.
Require Import MxFunctors.

Require Import DKA_Definitions.
Require Import Model_Languages.
        Import Model_Languages.Load.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation language := (LX label).
Notation LMX n m := (LMX label n m).
Notation Word := (list label).

Fixpoint regex_language (e: regex): language :=
  match e with 
    | RegExp.plus e f => regex_language e + regex_language f
    | RegExp.dot e f => regex_language e * regex_language f
    | RegExp.star e => regex_language e #
    | RegExp.one => 1
    | RegExp.zero => 0
    | RegExp.var a => (fun w => w = a::nil)
  end.

Lemma functor_xif `{HF: graph_functor} : 
  forall A B b (x y: X A B), F A B (xif b x y) == xif b (F A B x) (F A B y).
Proof.
  intros. destruct b; reflexivity.
Qed.

Definition regex_language_f  := 
  @Build_functor RegExp.re_Graph (@lang_Graph label) (fun A => A) (fun A B e => regex_language e).
 
Section protect.

Opaque dot plus star one zero.

Instance regex_language_graph_functor: graph_functor regex_language_f.
Proof. 
  constructor. intros [] [] x y H. induction H; simpl fX; simpl fT; auto with algebra. 
  apply star_destruct_left. assumption.
  apply star_destruct_right. assumption.
  transitivity (regex_language y); assumption.
Qed.

Instance regex_language_kleene_functor: kleene_functor regex_language_f.
Proof.
  constructor.
   constructor; constructor; eauto with typeclass_instances.
   intros. reflexivity.
Qed.

Ltac fold_regex_language := repeat match goal with |- context[regex_language ?e] => change (regex_language e) with (regex_language_f tt tt e) end.

Lemma dot_xifzero_left `{ISR: IdemSemiRing}: forall A B C b (x: X A B) (y: X B C), xif b x 0 * y == xif b (x*y) 0.
Proof. intros. destruct b; auto with algebra. Qed.
Lemma dot_boolxif_left `{ISR: IdemSemiRing}: forall A B b (x: X A B), xif b 1 0 * x == xif b x 0.
Proof. intros. rewrite dot_xifzero_left, dot_neutral_left. reflexivity. Qed.
Lemma dot_xifzero_right `{ISR: IdemSemiRing}: forall A B C b (x: X B A) (y: X C B), y * xif b x 0 == xif b (y*x) 0.
Proof. intros. destruct b; auto with algebra. Qed.
Lemma dot_boolxif_right `{ISR: IdemSemiRing}: forall A B b (x: X A B), x * xif b 1 0 == xif b x 0.
Proof. intros. rewrite dot_xifzero_right, dot_neutral_right. reflexivity. Qed.


Transparent dot plus star one zero. 

Lemma lang_sum: forall (f: nat -> language) w n i, sum i n f w <-> exists2 j, j<n & f (i+j)%nat w.
Proof.
  induction n. 
  - compute. firstorder.
    lia.
  - intros j. simpl. unfold lang_union. rewrite IHn. clear IHn. intuition. 
    exists O; auto with arith. rewrite plus_comm. assumption.
    destruct H0 as [k ? ?]. exists (Datatypes.S k); auto with arith. rewrite <- plus_n_Sm. assumption.
    destruct H as [[|k] ? ?].
    + left. rewrite plus_comm in H0. assumption.
    + right. exists k; auto with arith. rewrite <- plus_n_Sm in H0. assumption.
Qed.   

Lemma mx_leq_pointwise `{SL: SemiLattice}: forall n m A (M N: MX_ A n m), 
  M <== N <-> forall i j, i<n -> j<m -> !M i j <== !N i j.
Proof. intros. reflexivity. Qed.

Section s.
  Variable I: Type.
  Variable n m: nat.
  Variable M: I -> LMX n m.

  Definition mx_lang_Union: LMX n m := 
    box _ _ (fun i j => lang_Union (fun k => !(M k) i j): language).

  Lemma mx_lang_Union_spec: forall M', mx_lang_Union <== M' <-> forall i, M i <== M'.
  Proof.
    Opaque leq.
    intros. split.
    intros H u. rewrite <- H. unfold mx_lang_Union.
     rewrite (mx_leq_pointwise (G:=@lang_Graph label)).
     intros s t Hs Ht. simpl. rewrite <- leq_lang_Union. reflexivity. 
    intro H.
     rewrite (mx_leq_pointwise (G:=@lang_Graph label)).
     intros s t Hs Ht. simpl. rewrite -> lang_Union_spec. intro u. apply (H u _ _ Hs Ht). 
    Transparent leq.
  Qed.
  
  Lemma leq_mx_lang_Union: forall k, M k <== mx_lang_Union.
  Proof.
    intro k. apply -> (mx_lang_Union_spec mx_lang_Union). reflexivity.
  Qed.  
End s.

Lemma mx_star_charac: forall n (M: LMX n n), M# == mx_lang_Union (iter M).
Proof.
  intros.
  apply leq_antisym.
   star_left_induction. apply plus_destruct_leq. 
    rewrite <- (leq_mx_lang_Union _ O). reflexivity. 
    mx_intros s t Hs Ht. simpl. fold_langAlg label. apply sum_leq. intros k _ Hk. 
    rewrite lang_leq. intros w [u Hu [v [o Hv] ->]].
    exists (Datatypes.S o). simpl. rewrite lang_sum. exists k; auto. exists u; auto. exists v; auto.
  apply <- mx_lang_Union_spec. intro m. induction m.
   unfold iter. auto with algebra.
   change (iter M (Datatypes.S m)) with (M * (iter M m)). rewrite IHm. rewrite <- (star_make_right M) at 2.
   apply plus_make_right.
Qed.

#[local] Open Scope num_scope.

Section accept.

  Import DFA.
  Variable A : DFA.t.

  Fixpoint read (w: Word) i := 
    match w with
      | nil => i
      | a::w => read w (delta A a i)
    end.

  Definition bounded_word (w: Word) := forall a, List.In a w -> a < max_label A.

  Definition DFA_language : language := 
    fun w => StateSet.In (read w (initial A)) (finaux A) /\ bounded_word w.

  Lemma read_app: forall v w i, read (w++v) i = read v (read w i).
  Proof. induction w; intro k; simpl; auto. Qed.
  
End accept.



Lemma simpl_regex_language : forall A,
  mxF regex_language_f tt (MAUT.size (DFA.to_MAUT A)) (MAUT.size (DFA.to_MAUT A)) (MAUT.delta (DFA.to_MAUT A))
  == box (DFA.size A) (DFA.size A)
  (fun s t => sum 0 (DFA.max_label A)
     (fun i => xif (eqb (state_of_nat t) (DFA.delta A (num_of_nat i) s)) (regex_language (RegExp.var (num_of_nat i))) 0)).
Proof.
  intros A.
  Opaque regex_language_f. simpl. unfold labelling. Transparent regex_language_f.
  apply box_compat. intros s t.
  rewrite functor_sum.
  setoid_rewrite functor_xif. reflexivity.  
Qed.


Theorem language_DFA_eval: forall A, DFA.bounded A -> regex_language (DFA.eval A) == DFA_language A.
Proof.
  Opaque leq plus. 
  intros A HA. fold_regex_language.
  unfold DFA.eval, MAUT.eval, comp.
  rewrite functor_mx_to_scal.
  rewrite 2functor_dot.
  rewrite functor_star.
  rewrite simpl_regex_language.
  Opaque eq_nat_bool regex_language_f.
  simpl. bool_simpl. simpl. fold_langAlg label.
  Transparent regex_language_f.
  setoid_rewrite sum_distr_left.
  setoid_rewrite functor_xif.
  Transparent regex_language_f. simpl. fold_langAlg label. 
  setoid_rewrite dot_boolxif_right. 
  setoid_rewrite dot_boolxif_left.
  setoid_rewrite xif_xif_and. 
  rewrite sum_inversion.
  rewrite (sum_collapse (G:=@lang_Graph label) (n:=DFA.initial A)).
   2: apply DFA.bounded_initial in HA; num_lia.
   2: simpl; intros; fold_langAlg label. 
   2: apply sum_zero; intros; apply xif_false.
   2: bool_connectors; nat_prop; intuition. 
   simpl Peano.plus. bool_simpl.
   unfold DFA_language. 
   generalize (DFA.bounded_initial HA) as Hs.
   generalize (DFA.initial A) as s.
   intros s Hs.
   match goal with |- context[box ?n ?m ?f] => set (M:=box n m f) end.
   apply leq_antisym.
    apply sum_leq. simpl. fold_langAlg label. intros n _ Hn.
    rewrite (@mx_star_charac _ M s n); auto. 2: num_lia. simpl.
    bool_simpl. StateSetProps.mem_analyse; simpl. 2: fold_langAlg label; auto with algebra.
    rewrite lang_Union_spec. intro m. revert s Hs.
    induction m; intros s Hs.
     simpl. nat_analyse.
      rewrite lang_leq. intros x ->. rewrite id_num in i. split; auto. 
      intros a Ha. inversion Ha. 
      fold_langAlg label; auto with algebra.
     simpl. fold_langAlg label.
      rewrite id_num.
      setoid_rewrite sum_distr_left.
      rewrite sum_inversion.
      setoid_rewrite dot_xifzero_left.
      apply sum_leq. intros a _ Ha.
      rewrite (sum_collapse (G:=@lang_Graph label) (n:=DFA.delta A a s)). 
      simpl. rewrite id_num. bool_simpl. simpl.
      rewrite lang_leq. intros w [u -> [v Hv ->]]. simpl.
      setoid_rewrite lang_leq in IHm. split. 
       eapply IHm; auto. apply (DFA.bounded_delta HA).
       intros b [<-|Hb]. num_simpl. assumption. eapply (IHm (DFA.delta A a s)); eauto. apply (DFA.bounded_delta HA). 
      specialize (DFA.bounded_delta HA a s). num_lia. 
      intros. simpl in H. num_analyse. elim H. rewrite <- e. num_lia.
      reflexivity.

    rewrite lang_leq. 
     cut (forall w: Word, StateSet.In (read A w s) (DFA.finaux A) -> (forall a, In a w -> a < DFA.max_label A) -> 
       exists2 j, StateSet.In j (DFA.finaux A) & !((M:LMX _ _) #) s (nat_of_state j) w).
     intro C. intros w [Hw Hw']. destruct (C _ Hw Hw') as [j Hj Hj']. 
     rewrite lang_sum. exists (nat_of_state j).
      apply HA in Hj. num_lia. simpl. bool_simpl. rewrite (StateSet.mem_1 Hj). assumption.
     intro w. revert s Hs. induction w; simpl; intros s Hs Hw Hw'.
      assert (Hs': (s < DFA.size A)%nat). num_lia. 
      exists s; auto. 
      rewrite (@mx_star_charac _ M s s Hs' Hs' nil). exists O. simpl. bool_simpl. reflexivity.
      
      apply IHw in Hw; try apply (DFA.bounded_delta HA). clear IHw. destruct Hw as [j Hj' Hj].
      exists j; auto. 
      rewrite (fun Hs Hj => @mx_star_charac _ M s (nat_of_state j) Hs Hj (a::w)).
       2: num_lia. 2: apply HA in Hj'; num_lia.
      rewrite (fun Hs Hj => @mx_star_charac _ M (DFA.delta A a s) (nat_of_state j) Hs Hj w) in Hj.
       2: specialize (DFA.bounded_delta HA a s); num_lia. 2: apply HA in Hj'; num_lia.
      destruct Hj as [n Hn]. exists (Datatypes.S n). simpl. fold_langAlg label.
      rewrite lang_sum. exists (DFA.delta A a s). specialize (DFA.bounded_delta HA a s). num_lia.
      simpl Peano.plus. exists (a::nil).
      rewrite 2id_num.
      rewrite lang_sum. simpl. exists a.
       specialize (Hw' a). num_simpl. auto. 
       bool_simpl. reflexivity.
       exists w; auto.
      intros b Hb. auto.
Qed.

End protect.


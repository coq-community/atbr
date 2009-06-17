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

Require Export FSets FMaps.
Require        FMapAVL.
Require        FSetDecide. 

Set Implicit Arguments.

(* avl ou listes : aucun impact pour l'instant... *)
Module FSet := FSetList.
Module FMap := FMapList.

Module FSetHide (X : FSetInterface.S).
  Include X.
End FSetHide.

Module FMapHide (X : FMapInterface.S).
  Include X.
End FMapHide.

(* pour la determinisation *)
Module State  := Nat_as_OT.
Module StateSet' := FSet.Make(State).  Module StateSet := FSetHide StateSet'.
Module StateMap' := FMap.Make(State).  Module StateMap := FMapHide StateMap'.

Module StateSetMap' := FMap.Make(StateSet). Module StateSetMap := FMapHide StateSetMap'.
Module Label := State.
Module LabelMap := StateMap.

(* pour la minimisation *)
Module StateSetSet' := FSet.Make(StateSet).  Module StateSetSet := FSetHide StateSetSet'.
Module Label_x_StateSet := PairOrderedType Label StateSet.
Module Label_x_StateSetSet'  := FSet.Make Label_x_StateSet. Module Label_x_StateSetSet  := FSetHide Label_x_StateSetSet'.


(* propriétés *)

Module StateSetProp' := FSetEqProperties.EqProperties StateSet.
Module StateSetProp  := StateSetProp'.MP.
Module StateSetFact  := StateSetProp.FM.
Module StateSetOrdProp := FSetProperties.OrdProperties(StateSet).
Module StateMapFact  := FMapFacts.Facts StateMap.

Module StateSetSetProp' := FSetEqProperties.EqProperties StateSetSet.
Module StateSetSetProp := StateSetSetProp'.MP.
Module StateSetSetFact := StateSetSetProp.FM.
Module StateSetMapProp := FMapFacts.Properties StateSetMap.
Module StateSetMapFact := StateSetMapProp.F.

Module StateSetDecide    := FSetDecide.Decide StateSet.
Module StateSetSetDecide := FSetDecide.Decide StateSetSet.

Module Label_x_StateSetSet_Prop' := FSetEqProperties.EqProperties Label_x_StateSetSet. 
Module Label_x_StateSetSet_Prop := Label_x_StateSetSet_Prop'.MP.
Module Label_x_StateSetSet_Fact := Label_x_StateSetSet_Prop.FM.

Notation state := nat (only parsing).
Notation stateset := StateSet.t.
Notation label := nat (only parsing).


Ltac stateset_dec := (StateSetDecide.fsetdec).
Ltac statesetset_dec := (StateSetSetDecide.fsetdec).

Section fold_labels.
Fixpoint fold_labels T (f: label -> T -> T) a acc := 
  match a with
    | O => acc
    | S a => fold_labels f a (f a acc)
  end.

Lemma fold_labels_rec_nodep: forall T (P: T -> Prop) f a acc,
  P acc -> (forall acc a, P acc -> P (f a acc)) -> P (fold_labels f a acc).
Proof.
  intros T P f. induction a; simpl; auto. 
Qed.

 
Lemma fold_labels_add_Subset : forall n acc, StateSet.Subset acc (fold_labels StateSet.add n acc). 
Proof.
  intros. apply fold_labels_rec_nodep. reflexivity.
  intros. StateSetDecide.fsetdec.
Qed.

Lemma fold_labels_add_union : forall n acc, StateSet.eq (fold_labels StateSet.add n acc) (StateSet.union acc (fold_labels StateSet.add n StateSet.empty)).
Proof.
  assert (forall P, StateSet.Equal P (StateSet.union P StateSet.empty)).
  intros. 
  assert (StateSet.Empty StateSet.empty). auto. symmetry; apply StateSetProp.empty_union_2. auto.
  
  intros. revert acc. induction n.
  simpl. auto. 
  simpl. intros. setoid_rewrite IHn at 2. rewrite IHn.
  rewrite StateSetProp.double_inclusion.
  split; intros e He; revert He; StateSetFact.set_iff; intuition. (* a pity ...*)
Qed.

Lemma fold_labels_add n : forall x, x < n <-> StateSet.In x (fold_labels StateSet.add n StateSet.empty).
Proof.
  intros. induction n. split; intros; [omega_false | StateSetDecide.fsetdec].
  simpl. destruct (eq_nat_dec x n). rewrite e. intuition. apply  fold_labels_add_Subset. StateSetDecide.fsetdec.
  split; intros.

  assert (x < n). clear IHn. omega. apply -> IHn in H0. clear - H0. rewrite fold_labels_add_union. StateSetDecide.fsetdec.
  rewrite fold_labels_add_union in *. 
  revert H. StateSetFact.set_iff. intuition.
Qed.

End fold_labels.

Fixpoint set_of_ones (f: nat -> bool) k: stateset := 
  match k with
    | 0 => StateSet.empty
    | S k => 
      if f k
        then StateSet.add k (set_of_ones f k)
        else set_of_ones f k 
  end.
 
Lemma nmem_set_of_ones: forall f n i, n<=i -> StateSet.mem i (set_of_ones f n) = false.
Proof.
  induction n; simpl; intros i Hi.
  apply StateSetProp'.empty_mem.
  case (f n). rewrite StateSetProp'.add_mem_2; auto with omega.
  auto with omega.
Qed.   

Lemma mem_set_of_ones: forall f n i, i<n -> StateSet.mem i (set_of_ones f n) = f i.
Proof.   
  induction n; intros i Hi.
  inversion Hi.
  simpl. destruct (eq_nat_dec i n). subst.
  case (f n). apply StateSetProp'.add_mem_1.
  apply nmem_set_of_ones. trivial.
  case (f n). rewrite StateSetProp'.add_mem_2; auto with omega.
  auto with omega.
Qed.
  
Lemma In_set_of_ones_lt: forall n i f, StateSet.In i (set_of_ones f n) -> i < n.
Proof.
  induction n; simpl.
  stateset_dec.
  intros i f. case (f n); intro H.
  destruct (eq_nat_dec n i). omega.
  apply StateSet.add_3 in H; trivial. 
  apply IHn in H. omega.
  apply IHn in H. omega.
Qed.




(* merge_plus n s t = " n+s \cup t " *)
Definition merge_plus n := StateSet.fold (fun x acc => StateSet.add (x + n)%nat acc).

Definition below s n := StateSet.For_all (fun i => i<n) s.



Lemma _mem_merge_aux_0: Equivalence StateSet.Equal.
Proof. constructor; repeat intro; stateset_dec. Qed.

Lemma _mem_merge_aux_1: forall n, compat_op (@eq nat) StateSet.Equal (fun (x : nat) acc => StateSet.add (x + n)%nat acc).
Proof. repeat intro. subst. stateset_dec. Qed.

Lemma _mem_merge_aux_2: forall n, transpose StateSet.Equal (fun x acc => StateSet.add (x + n)%nat acc).
Proof. repeat intro. stateset_dec. Qed.

Lemma mem_merge_1: forall s i n t, i<n ->
  StateSet.mem i (merge_plus n s t) = StateSet.mem i t.
Proof.
  unfold merge_plus.
  intros.  apply StateSetProp.fold_rec_nodep. reflexivity.
  intros.
  remember (StateSet.mem i t) as b. 
  destruct b. 
     rewrite <- StateSetFact.mem_iff in *.
     StateSetFact.set_iff. right. assumption.

     rewrite <- StateSetFact.not_mem_iff in *.
     intro. apply H1. revert H2.
     StateSetFact.set_iff. intros [H' | H']; [omega_false | stateset_dec].
Qed.

Lemma below_false : forall t n i, below t n -> n <= i -> ~ StateSet.In i t. (* StateSet.mem i t = false. *)
Proof. 
  intros. 
  unfold below in H.  unfold StateSet.For_all in H. intro.
(*   rewrite <- StateSetFact.not_mem_iff. intro.   *)
  apply H in H1. omega_false.
Qed.

Lemma mem_In : forall a b x y, (StateSet.In x a <->  StateSet.In y b) <-> (StateSet.mem x a = StateSet.mem y b).
Proof.
  intros. case_eq (StateSet.mem x a); intros; 
  intuition  
  repeat
    match goal with 
      | H : true = StateSet.mem _ _  |- _  => symmetry in H
      | H : StateSet.mem _ _ = true  |- _  => rewrite <- StateSetFact.mem_iff in H
      | H : false = StateSet.mem _ _  |- _  => symmetry in H
      | H : StateSet.mem _ _ = false  |- _  => rewrite <- StateSetFact.not_mem_iff in H
      | |- true = StateSet.mem _ _=> symmetry
      | |- false = StateSet.mem _ _=> symmetry
      | |- StateSet.mem _ _ = true => rewrite <- StateSetFact.mem_iff
      | |- StateSet.mem _ _ = false=> rewrite <- StateSetFact.not_mem_iff

    end; intuition. 
Qed.
  


Lemma mem_merge_2: forall s i n t, n<=i -> below t n ->
  StateSet.mem i (merge_plus n s t) = StateSet.mem (i-n) s.
Proof.
  unfold merge_plus.
  intros. 
  set (Pred := fun Q acc =>  StateSet.In i acc <-> StateSet.In (i - n) Q).
  assert (Pred s (StateSet.fold (fun x acc => StateSet.add (x + n) acc) s t)).  
  apply StateSetProp.fold_rec_bis; subst Pred; cbv beta.
    intros. rewrite <- H1. apply H2.

    split; intros. apply False_ind. eapply (below_false H0). apply H. apply H1.
    apply False_ind. eapply StateSet.empty_1. apply H1. 
  
    
    intros. StateSetFact.set_iff. intuition.
  
  subst Pred; cbv beta in H1. 
  apply -> mem_In. apply H1.
Qed.

Lemma merge_below: forall n m s t, below t n -> below s m -> below (merge_plus n s t) (n+m).
Proof.
  unfold merge_plus.   intros.
  apply StateSetProp.fold_rec_nodep.
    unfold below, StateSet.For_all in *.
    intuition. specialize (H x H1). omega.

    unfold below, StateSet.For_all in *.
    intuition. specialize (H0 x H1). revert H3. StateSetFact.set_iff. intuition.
Qed.
  

Section lemmes_set_of_ones.

  Lemma _set_of_ones_le f n m  : n <= m   ->  StateSet.Subset (set_of_ones f n) (set_of_ones f m ).
  Proof.
    intros. 
    induction H.  stateset_dec. 
    
    simpl. destruct (f m). eapply StateSetProp.subset_trans. apply IHle.  stateset_dec.  
    assumption.
  Qed.
  
  Lemma _set_of_ones_correction1 f n : forall x, x < n -> (f x = true -> StateSet.In x (set_of_ones f n)).
  Proof.
    intros f n. 
    induction n. intros; inversion H. 
    intros. destruct (eq_nat_dec x n). subst.  simpl. rewrite H0. stateset_dec. 
    eapply _set_of_ones_le; [| apply IHn]. auto. omega. auto.
  Qed.
  
  Lemma _set_of_ones_correction2  f n x : StateSet.In x (set_of_ones f n ) -> (x < n /\ f x = true).
  Proof.
    intros f n.
    induction n.
      intros; simpl in H. stateset_dec.
      intros; simpl in H.
      destruct (eq_nat_dec x n). subst.
      Set Printing Coercions. destruct (f n). auto. 
      
      specialize (IHn n).  intuition (omega_false).    
      assert ( x < n /\ f x = true). apply IHn. 
      destruct (f n). eapply StateSet.add_3.  intro. apply n0. symmetry. apply H0. assumption. assumption.
      split; intuition (omega).
   Qed.
   
  Lemma set_of_ones_correction f n : forall x, x < n -> (StateSet.In x (set_of_ones f n) <-> f x = true).
  Proof.
    intros. 
    intuition (auto using _set_of_ones_correction1). 
    destruct (@_set_of_ones_correction2  f n x H0); trivial. 
  Qed.
  
  Lemma set_of_ones_correction' f n : forall x, StateSet.In x (set_of_ones f n) -> x < n.
  Proof.
    intros. elim (@_set_of_ones_correction2 f n x); intros.
    tauto.
    apply H.
  Qed.
  
  Lemma set_of_ones_compat' n f g : 
    (forall x, x < n -> f x = g x ) -> StateSet.eq (set_of_ones f n) (set_of_ones g n).
  Proof.
    intros. 
    rewrite StateSetProp.double_inclusion. split; repeat intro.
    assert (a < n) by eauto using set_of_ones_correction';
    destruct (f a); destruct (g a);rewrite set_of_ones_correction in *;
      solve [ assumption | rewrite <- H; assumption | rewrite -> H; assumption].
    assert (a < n) by eauto using set_of_ones_correction';
    destruct (f a); destruct (g a);rewrite set_of_ones_correction in *;
      solve [ assumption | rewrite <- H; assumption | rewrite -> H; assumption].
  Qed.

End lemmes_set_of_ones.

                             (*********)
                             (* Attic *)
                             (*********)

(** * Various lemmas used elsewhere in the development.
   Essentially, an add-on to the FSet library
*)
Section Attic.
Lemma compat_bool_neg A f : compat_bool (@eq A) f -> compat_bool (@eq A) (fun x => negb (f x)).
  repeat intro.  subst. auto.
Qed.

Implicit Arguments compat_bool_neg [A].

Lemma negb_f A (f : A -> bool) (x : A) : false = f x -> negb (f x) = true.
  repeat intro. rewrite <- H. reflexivity.
Qed.

Implicit Arguments negb_f [A].

Hint Resolve 
  compat_bool_neg (@compat_bool_neg StateSet.t) (@compat_bool_neg StateSet.elt)
  negb_f          (@negb_f StateSet.t)          (@negb_f StateSet.elt) .

Lemma cpl_fst_snd : forall A B (u : A) (v : B) (x : A *B), (u,v) = x -> (u = fst x) /\ (v = snd x).
Proof.
  intros.
  split; destruct H; reflexivity.  
Qed.

Lemma union_partition : forall f x t u, compat_bool (@eq StateSet.elt ) f -> (t,u) = StateSet.partition f x -> StateSet.Equal x (StateSet.union t u).
Proof.
  intros f x t u Hf Htu.
  apply cpl_fst_snd in Htu. destruct Htu as [Ht Hu].
  rewrite Ht, Hu.
  rewrite StateSet.partition_1, StateSet.partition_2; auto.
  repeat intro; intuition StateSetFact.set_iff.  
  remember (f a) as b; destruct b.  left. auto with set. 
  right. apply (StateSet.filter_3 (f:= fun x => negb (f x))); auto. 
  revert H. StateSetFact.set_iff. intuition  (eapply StateSet.filter_1; [| eassumption]; repeat intro; subst; auto).
  rewrite <- H. reflexivity. 
Qed.

Lemma inter_partition : forall f x t u, compat_bool (@eq StateSet.elt ) f -> 
  StateSet.eq (fst (StateSet.partition f x)) t ->
  StateSet.eq (snd (StateSet.partition f x)) u 
  -> StateSet.Empty (StateSet.inter t u).
Proof.
  intros f x t u Hf Ht Hu.

  rewrite StateSet.partition_1 in Ht by auto. 
  rewrite StateSet.partition_2 in Hu by auto.
  repeat intro. revert H. StateSetFact.set_iff.
  repeat intro.
  rewrite <- Ht, <-Hu in H. clear Ht Hu.
  set (g := fun x => negb (f x)).
  
  assert (Hdiscr : f a = true /\ g a = true).   destruct H as [Haf Hag]; split;  eapply StateSet.filter_2; eauto.
  subst g. destruct Hdiscr as [Haf Hag]. destruct Haf. destruct (f a); simpl in Hag; discriminate.
Qed.

Lemma inter_filter : forall (f : StateSet.elt -> bool) p, compat_bool StateSet.E.eq f -> 
  StateSet.Empty 
  (StateSet.inter 
    (StateSet.filter f p) 
    (StateSet.filter (fun x => negb (f x)) p)
    ).
Proof.
  intros. eapply inter_partition. 
  apply H. 
  apply StateSet.partition_1; auto.
  apply StateSet.partition_2; auto.
Qed.


Definition eq_option_stateset_X_stateset (a b : (option (StateSet.t * StateSet.t))) : Prop :=
  match (a,b) with
    | (Some a, Some b) => StateSet.eq (fst a) (fst b) /\ StateSet.eq (snd a) (snd b)
    | (None , None)    => True  
    | _ => False
  end.

Hint Unfold eq_option_stateset_X_stateset.

Global Instance eq_option_stateset_X_stateset_compat : Equivalence eq_option_stateset_X_stateset.
Opaque StateSet.eq.
split; compute; intuition. 
destruct x; intuition auto. 
destruct y; destruct x; intuition auto.
destruct z; destruct y; destruct x; intuition auto.
  destruct p1; destruct p0; destruct p; eauto.
  destruct p1; destruct p0; destruct p; eauto.
Defined.

Global Instance stateset_is_empty_compat : Proper (StateSet.eq ==> @eq bool) (StateSet.is_empty).
Proof.
  repeat intro. rewrite H. reflexivity.
Qed.

Definition stateset_X_stateset_eq a b : Prop :=
  StateSet.eq (fst a) (fst b) /\
  StateSet.eq (snd a) (snd b).

Global Instance partition_compat  : 
Proper ((pointwise_relation StateSet.elt (@eq bool) ) ==>   StateSet.eq ==>  stateset_X_stateset_eq) (StateSet.partition).
Proof.
  unfold stateset_X_stateset_eq.
  repeat intro. 
  split. rewrite 2 StateSet.partition_1; auto.
  apply StateSetFact.filter_ext; auto.
  rewrite 2 StateSet.partition_2; auto.
  apply StateSetFact.filter_ext; auto. 
  intros. rewrite H. reflexivity.
Qed.

Lemma partition_predicate p f : compat_bool StateSet.E.eq f ->
  (forall i, StateSet.In i (fst (StateSet.partition f p)) -> f i = true)
  /\   (forall i, StateSet.In i (snd (StateSet.partition f p)) -> f i = false)

.
Proof.
  intros.   
  split; intros.
  
  setoid_rewrite StateSet.partition_1 in H0; auto.
  eapply StateSet.filter_2; [| apply H0]; auto.
  setoid_rewrite StateSet.partition_2 in H0; auto.
  set (g := (fun x => negb (f x))) in *.
  setoid_replace (f i = false) with (g i = true) using relation iff.
  
  eapply StateSet.filter_2;  [| apply H0]; auto.

  subst g; simpl. 
  case_eq (f i); intuition; compute. 
Qed.

Lemma partition_union f p :  compat_bool StateSet.E.eq f ->
  StateSet.Equal p (StateSet.union (fst (StateSet.partition f p)) (snd (StateSet.partition f p))).
Proof.
  intros f p Hf.
  rewrite StateSet.partition_1; auto.  rewrite StateSet.partition_2; auto.
  repeat intro; intuition StateSetFact.set_iff.  
  remember (f a) as b; destruct b.
    left. auto with set. 
    right. eapply StateSet.filter_3; auto. 
    
  revert H. StateSetFact.set_iff. intuition  (eapply StateSet.filter_1; [| eassumption]; repeat intro; subst; auto).
  rewrite H. reflexivity. 
Qed.

Lemma partition_inter f p :  compat_bool StateSet.E.eq f ->
  StateSet.Empty (StateSet.inter (fst (StateSet.partition f p)) (snd (StateSet.partition f p))).
Proof.
  intros f p Hf.
  rewrite StateSet.partition_1; auto.
  rewrite StateSet.partition_2; auto. 
  repeat intro. revert H. StateSetFact.set_iff. repeat intro.
  set (g := fun x => negb (f x)).
  
  assert (Hdiscr : f a = true /\ g a = true).   destruct H as [Haf Hag]; split;  eapply StateSet.filter_2; eauto.
  subst g. destruct Hdiscr as [Haf Hag]. destruct Haf. destruct (f a); simpl in Hag; discriminate.
Qed.



End Attic.

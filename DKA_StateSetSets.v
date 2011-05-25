(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Properties about sets of sets, and maps over sets *)

Require Import Utils_WF.
Require Import DisjointSets.
Require Import DKA_Definitions.
Require Import MyFSets.
Require Import MyFSetProperties.
Require Import MyFMapProperties.
Require Import Common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module StateSetMap' := FMapAVL.Make StateSet. Module StateSetMap := FMapHide StateSetMap'.
Module StateSetMapProps := MyMapProps StateSetMap.
Notation statesetmap := StateSetMap.t. 

(* this module is used in proofs only, no need to go to AVL sets *)
Module StateSetSet' := FSetList.Make StateSet. Module StateSetSet := FSetHide StateSetSet'.
Module StateSetSetProps := MySetProps StateSetSet.
Notation statesetset := StateSetSet.t. 

(** map a function [f] over a set of statesets *)
Definition statesetset_map f t :=
  StateSetSet.fold (fun x acc => StateSetSet.add (f x) acc) t StateSetSet.empty.

(** properties of the above function *)
Section sssm.
  Variable t0: StateSetSet.t.
  Variable f: stateset -> stateset.

  Lemma statesetset_map_in p:
    StateSetSet.In p (statesetset_map f t0) -> exists2 q, StateSetSet.In q t0 & StateSet.Equal (f q) p.
  Proof.
    unfold statesetset_map.
    apply StateSetSetProps.Props.fold_rec_nodep. StateSetSetProps.setdec.
    intros q a Hq IH.  StateSetSetProps.Facts.set_iff. intros [Hp|Hp]; eauto. 
  Qed.

  Hypothesis Hf: forall p q, StateSetSet.In p t0 -> StateSetSet.In q t0 -> 
    (StateSet.Equal (f p) (f q) <-> StateSet.Equal p q).

  Lemma statesetset_map_cardinal:
    StateSetSet.cardinal (statesetset_map f t0) = StateSetSet.cardinal t0.
  Proof.
    refine (proj2 (StateSetSetProps.Props.fold_rec_bis 
      (P:=fun t a => (forall p, StateSetSet.In p t0 -> (StateSetSet.In (f p) a <-> StateSetSet.In p t)) /\  
        ((forall p, StateSetSet.In p t -> StateSetSet.In p t0) -> 
          StateSetSet.cardinal a = StateSetSet.cardinal t)) _ _ _) _); trivial. 
    intros. setoid_rewrite <- H. trivial. 
    split; trivial. StateSetSetProps.setdec. 
    intros p a t' Hp Hp' [IH IHc]. split.
    intros q Hq. 
    StateSetSetProps.Facts.set_iff. specialize (IH q Hq). rewrite Hf by auto. tauto.   
    intros Ht'.
    rewrite (StateSetSetProps.Props.cardinal_2 (s:=a) (x:=f p)); auto with map. 
    symmetry. rewrite (StateSetSetProps.Props.cardinal_2 (s:=t') (x:=p)); auto with map. 
    symmetry. rewrite IHc; auto. intros q Hq. apply Ht'. StateSetSetProps.setdec.
    rewrite IH; auto.
  Qed.
End sssm.

(** the only set whose all elements are below 0 is the empty set *)
Lemma below0_empty p: setbelow p (num_of_nat 0) -> StateSet.Equal p StateSet.empty.
Proof.
  intro H.
  apply StateSetProps.Props.empty_is_empty_1.
  rewrite StateSetProps.Props.elements_Empty.
  remember (StateSet.elements p) as l. destruct l as [|i l]. trivial.
  specialize (H i). apply apply in H. exfalso. clear - H. num_omega.
  rewrite StateSetProps.Facts.elements_iff. rewrite <- Heql. auto. 
Qed.


(** technical lemmas for using FSet lemmas *)
Lemma compat_split s: compat_bool StateSet.Equal (fun p => StateSet.mem s p).
Proof. intros ? ? H. rewrite H. trivial. Qed.
Lemma compat_negsplit s: compat_bool StateSet.Equal (fun p => negb (StateSet.mem s p)).
Proof. intros ? ? H. rewrite H. trivial. Qed.
Local Hint Resolve compat_split compat_negsplit.

Ltac solve_p1 := intros ? ? H'; rewrite H'; reflexivity.


(** bound of the cardinal of a set of bounded sets *)
Lemma card_pset (s: nat) t: (forall p, StateSetSet.In p t -> setbelow p (state_of_nat s)) -> 
  (StateSetSet.cardinal t <= power s)%nat.
Proof. 
  revert t. induction s; intros t H; simpl.
  (* the set of set contains at most the empty set *)
   destruct (StateSetSetProps.Props.cardinal_0 t) as (l&Hl&Hlt&->).
   setoid_rewrite Hlt in H. clear Hlt.
   destruct l as [|x [| y q]]; simpl; auto with arith. 
   exfalso. inversion_clear Hl. apply H0. left. clear H0 H1.
   rewrite (@below0_empty x), (@below0_empty y). reflexivity.
    apply H. right. left. reflexivity.
    apply H. left. reflexivity.

  (* for the inductive case, we partition the set according to the presence of [s] *)
  pose (t0 := StateSetSet.filter (fun p => StateSet.mem (state_of_nat s) p) t).
  pose (t1 := StateSetSet.filter (fun p => negb (StateSet.mem (state_of_nat s) p)) t).
  pose (t0' := statesetset_map (StateSet.remove (state_of_nat s)) t0).
  setoid_replace t with (StateSetSet.union t0 t1).
  rewrite StateSetSetProps.Props.union_cardinal.
  replace (StateSetSet.cardinal t0) with (StateSetSet.cardinal t0').
  assert (IH1 := IHs t1). apply apply in IH1. 
  assert (IH0 := IHs t0'). apply apply in IH0. 
  omega.

   subst t0' t0. clear t1 IH1 IH0. intros p Hp. 
   destruct (statesetset_map_in Hp) as [q Hq Hq']. revert Hq.
   rewrite StateSetSetProps.mem_iff.
   rewrite StateSetSetProps.EqProps.filter_mem by solve_p1.
   case_eq (StateSetSet.mem q t). 2:(intros; discriminate). simpl. intros Hq Hq''. 
   intros x Hx. 
   destruct (eq_num_dec x s). rewrite e, <- Hq' in Hx. 
    exfalso. revert Hx. clear. StateSetProps.setdec. 
   rewrite <- StateSetSetProps.mem_iff in Hq. 
   rewrite <- StateSetProps.mem_iff in Hq''. 
   specialize (H q Hq x). apply apply in H. clear - H n. num_omega. StateSetProps.setdec.

   subst t1. clear t0 t0' IH1. intro p. 
   rewrite StateSetSetProps.mem_iff.
   rewrite StateSetSetProps.EqProps.filter_mem by solve_p1. 
   case_eq (StateSetSet.mem p t). 2:(intros; discriminate). simpl. intros Hp Hp'. 
   intros x Hx. 
   destruct (eq_num_dec x s). subst. apply StateSet.mem_1 in Hx. rewrite Hx in Hp'. discriminate.
   apply StateSetSet.mem_2 in Hp. pose (H' := H p Hp x Hx). num_omega.

  subst t0' t0. clear t1.
  apply statesetset_map_cardinal. 
  intros p q.
  setoid_rewrite StateSetSetProps.mem_iff.
  do 2 rewrite StateSetSetProps.EqProps.filter_mem by solve_p1. 
  case (StateSetSet.mem p t). 2: (intros; discriminate).
  case (StateSetSet.mem q t). 2: (intros; discriminate). simpl.
  setoid_rewrite <- StateSetProps.mem_iff. try StateSetProps.setdec. (* BUG setdec*)
   split; intro Hpq.
    clear - H0 H1 Hpq. intro x. 
     generalize (Hpq x). clear Hpq. StateSetProps.set_iff. 
     destruct (eq_num_dec s x). subst. firstorder. firstorder. rewrite Hpq. reflexivity.

  subst t0 t1. clear t0'. intro x. 
  setoid_rewrite StateSetSetProps.mem_iff. 
  do 2 rewrite StateSetSetProps.EqProps.filter_mem by solve_p1.
  StateSetProps.mem_analyse; StateSetSetProps.mem_analyse; simpl; firstorder. 
  
  subst t0 t1. clear t0'. intro x. 
  rewrite StateSetSetProps.EqProps.union_filter by trivial.
  setoid_rewrite StateSetSetProps.mem_iff.
  rewrite StateSetSetProps.EqProps.filter_mem by solve_p1.
  rewrite andb_comm. StateSetProps.mem_analyse; reflexivity.
Qed.

(** domain of a statesetmap, to apply the above results to maps : *)
Section domain.
  Variable T: Type.

  Definition domain t := StateSetMap.fold (fun p (np: T) a => StateSetSet.add p a) t StateSetSet.empty.

  Lemma domain_spec: forall x t, StateSetSet.In x (domain t) <-> StateSetMap.In x t.
  Proof.
    intros x t. unfold domain. 
    refine (StateSetMapProps.fold_rec_bis (P:=fun m a => StateSetSet.In x a <-> StateSetMap.In x m) _ _ _).
     intros. rewrite <- H. assumption.
     StateSetSetProps.set_iff. StateSetMapProps.map_iff. tauto.
     intros. StateSetSetProps.set_iff. StateSetMapProps.map_iff. tauto.
  Qed.    

  Lemma cardinal_domain t: StateSetSet.cardinal (domain t) = StateSetMap.cardinal t.
  Proof.
    refine (proj2 (StateSetMapProps.fold_rec_bis 
      (P:=fun t a => (forall p, StateSetSet.In p a <-> StateSetMap.In p t) /\  
                     StateSetSet.cardinal a = StateSetMap.cardinal t) _ _ _)). 
    intros. setoid_rewrite <- H. trivial. 
    split; trivial. split. StateSetSetProps.setdec. StateSetMapProps.map_iff. tauto. 
    intros p np a t' Hp Hp' [IH IHc]. split.
    intro q. StateSetSetProps.set_iff. StateSetMapProps.map_iff. specialize (IH q). tauto.
    rewrite (StateSetMapProps.cardinal_2 Hp') by (intro; reflexivity). 
    rewrite (StateSetSetProps.Props.cardinal_2 (s:=a) (x:=p)). congruence. rewrite IH; trivial.
    auto with map.
  Qed.  

End domain.  




(** Results about the number of classes in a partition (for termination of the equivalence check) *)

Module DS := DisjointSets.PosDisjointSets.
Module DSUtils := DisjointSets.DSUtils Numbers.Positive DS.
Import DSUtils.Notations.

Definition add_classes t := fun i => StateSetSet.add (DS.class_of t (num_of_nat i)).
Fixpoint classes size t := 
  match size with
    | O => StateSetSet.empty
    | Datatypes.S n => add_classes t n (classes n t)
  end.
Definition measure size t := StateSetSet.cardinal (classes size t).


Lemma classes_compat: forall size `{DS.WF} {t'} `{DS.WF t'}, t [=T=] t' -> 
  StateSetSet.Equal (classes size t) (classes size t').
Proof.
   induction size as [|s IHs]; intros t t' H H'' Ht; simpl.
    reflexivity.
    apply StateSetSetProps.add_m; trivial.
    apply DSUtils.class_of_compat'; ti_auto.
    apply IHs; trivial. 
Qed.

Lemma measure_compat: forall size `{DS.WF} {t'} `{DS.WF t'}, t [=T=] t' -> measure size t = measure size t'.
Proof.
  intros.
  apply StateSetSetProps.Props.Equal_cardinal, classes_compat; trivial.
Qed.
  
Section protect.
(* Local Hint Resolve @DS.union_WF @DS.empty_WF: typeclass_instances. *)

Lemma measure_union_idem: forall `{DS.WF} size x y, {{t}} x y -> 
  measure size (DS.union t x y) = measure size t.
Proof.
  intros. eapply measure_compat; ti_auto. symmetry. apply DSUtils.eq_union; auto.
Qed.

Lemma in_classes: forall t size x, 
  StateSetSet.In x (classes size t) <-> exists2 y, y<size & StateSet.Equal x (DS.class_of t (state_of_nat y)).
Proof.
  induction size; intros x; simpl; unfold add_classes; StateSetSetProps.set_iff.
   intuition. destruct H. omega.
   rewrite IHsize. clear IHsize.
   completer idtac.
    symmetry in H. eauto with omega.
    destruct H. eauto with omega.
    destruct H as [y Hy H]. destruct (eq_nat_dec y size). subst. 
     symmetry in H. auto.
     right. exists y. omega. assumption. 
Qed.

Lemma in_classes_empty_below: forall size x, 
  StateSetSet.In x (classes size DS.empty) -> setbelow x (state_of_nat size).
Proof.
  intros size x H z. 
  rewrite in_classes in H. destruct H as [y Hy H].
  rewrite H. rewrite DSUtils.class_of_empty. StateSetProps.set_iff. 
  intro. psubst. num_omega.
Qed.

Lemma add_classes_empty: forall x a, 
  StateSetSet.Equal (add_classes DS.empty x a) (StateSetSet.add (StateSet.singleton x) a).
Proof.
  intros. unfold add_classes. 
  rewrite DSUtils.class_of_empty.
  reflexivity. 
Qed.

Lemma measure_empty: forall size, measure size DS.empty = size.
Proof.
  unfold measure. induction size as [|s IHs].
   reflexivity.
   simpl. rewrite add_classes_empty.
   rewrite StateSetSetProps.Props.add_cardinal_2. rewrite IHs. reflexivity. 
   clear IHs. induction s; simpl.
    StateSetSetProps.setdec.
    rewrite add_classes_empty. StateSetSetProps.set_iff. 
    clear. intros [H|H].
     eapply proj1 in H. apply apply in H. 2: rewrite StateSetProps.singleton_iff; trivial.
     revert H. StateSetProps.set_iff. intro. psubst. 
     revert H. generalize (statesetelt_of_nat s). intro. num_omega.
     apply in_classes_empty_below in H. specialize (H (Psucc (state_of_nat s))).
     apply apply in H. num_omega. auto with set.
Qed.

Lemma classes_union_strict: forall `{DS.WF} size (x y: state), 
  x < size -> y < size ->
  StateSetSet.Equal 
  (classes size (DS.union t x y)) 
  (StateSetSet.add (StateSet.union (DS.class_of t x) (DS.class_of t y))
    (StateSetSet.remove (DS.class_of t x)
      (StateSetSet.remove (DS.class_of t y)
      (classes size t)))).
Proof.
  intros t Ht size x y Hx Hy s.
   rewrite in_classes.
   StateSetSetProps.set_iff. rewrite in_classes.
   split.
    intros [z Hz H].
    destruct (@DSUtils.sameclass_spec t Ht x (state_of_nat z)) as [Hxz|Hxz]. 
     rewrite DSUtils.class_of_union_1 in H by auto. symmetry in H. auto. 
     destruct (@DSUtils.sameclass_spec t Ht y (state_of_nat z)) as [Hyz|Hyz]. 
      rewrite DSUtils.class_of_union_1 in H by auto. symmetry in H. auto. 
      rewrite DSUtils.class_of_union_2 in H by auto. right. 
       repeat split. eauto. 
       rewrite H. intro F. apply DSUtils.class_of_injective in F; auto.
       rewrite H. intro F. apply DSUtils.class_of_injective in F; auto.
       
    intros [H|[[[z Hz H] Hys]Hxs]].
     exists x; trivial. symmetry in H. rewrite DSUtils.class_of_union_1; auto. left. bool_simpl. reflexivity.
     exists z; trivial. rewrite DSUtils.class_of_union_2; auto. 
      intro F. apply Hxs. rewrite F, H. reflexivity.
      intro F. apply Hys. rewrite F, H. reflexivity.
Qed.

Lemma add_cardinal: forall s s' x, 
  Datatypes.S (StateSetSet.cardinal s) < StateSetSet.cardinal s' -> 
  StateSetSet.cardinal (StateSetSet.add x s) < StateSetSet.cardinal s'.
Proof.
  intros. destruct (StateSetSetProps.mem_spec x s) as [Hx|Hx]. 
   rewrite StateSetSetProps.Props.add_cardinal_1; auto with omega.
   rewrite StateSetSetProps.Props.add_cardinal_2; auto.
Qed.

Lemma rem_cardinal_lt: forall s x, 
  StateSetSet.In x s -> 
  StateSetSet.cardinal (StateSetSet.remove x s) < StateSetSet.cardinal s.
Proof.
  intros. rewrite <- (StateSetSetProps.Props.remove_cardinal_1 H) ; auto.
Qed.

Lemma measure_union_strict: forall `{DS.WF} size t' (x y: state), 
  x < size -> y < size ->
  DS.equiv t x y = (false,t') -> measure size (DS.union t x y) < measure size t.
Proof.
  intros. unfold measure.
  rewrite classes_union_strict; try eassumption.
  apply add_cardinal. rewrite StateSetSetProps.Props.remove_cardinal_1. apply rem_cardinal_lt.
   rewrite in_classes. exists y; trivial. bool_simpl; reflexivity.
   apply StateSetSet.remove_2. 
    intro F. apply DSUtils.class_of_injective in F; trivial. 
    apply (@Equivalence_Symmetric _ _ (@DS.sameclass_Equivalence _ H)) in F.
    rewrite <- DS.sameclass_equiv, H2 in F; trivial. discriminate.
    rewrite in_classes. exists x; trivial. bool_simpl; reflexivity.
Qed.

End protect.


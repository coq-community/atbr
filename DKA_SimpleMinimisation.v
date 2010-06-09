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
Require Import Functors MxFunctors.
Require Import Isomorphism.

Require Import DKA_Annexe. 
Require Import DKA_Sets.

        Import SimpleMyhillNerode.

Require CoLoR.Util.Multiset.MultisetNat.

Module Label_x_StateSetSetDecide := FSetDecide.Decide(Label_x_StateSetSet).
Module Label_x_StateSetSetFact := FSetFacts.Facts(Label_x_StateSetSet).

Notation In_L := Label_x_StateSetSet.In.
Notation In_P := StateSetSet.In.
Notation singleton := StateSetSet.singleton.
Notation "A ++ B" := (StateSetSet.union A B) .
Ltac lsetdec := Label_x_StateSetSetDecide.fsetdec.
Ltac fsetsetdec := StateSetSetDecide.fsetdec.
Ltac fsetdec := StateSetDecide.fsetdec.
Ltac rintro := repeat intro.
Ltac byContradiction := cut False ; [contradiction| idtac].
Hint Unfold StateSet.eq StateSetSet.eq.
Hint Unfold StateSet.Exists StateSetSet.Exists.


Ltac injection_clear H := 
  injection H; clear H; intros; subst.

Hint Resolve 
  compat_bool_neg (@compat_bool_neg StateSet.t) (@compat_bool_neg StateSet.elt)
  negb_f          (@negb_f StateSet.t)          (@negb_f StateSet.elt) .

Notation "x  =o= y" := (eq_option_stateset_X_stateset x y ) (at level 80). 
Notation "A [\] B" := (StateSetSet.diff A B)(at level 80, right associativity) . 
Notation ladd := Label_x_StateSetSet.add.
Notation sadd := StateSetSet.add.

Hint Extern 8  (?x = ?y) => subst ; (trivial || discriminate || tauto_false).
Hint Unfold eq_option_stateset_X_stateset.
(* Hint Extern 10 (compat_bool ?R ?f) => let H := fresh in intros ?x ?y H; rewrite H; reflexivity . *)

Lemma compat_bool_delta : forall a q (DFA : DFA), 
  compat_bool StateSet.E.eq
  (fun i : StateSet.elt => StateSet.mem (D_delta DFA i a) q).
Proof.
  intros a q DFA x y H; rewrite H; reflexivity.
Qed.

Lemma compat_bool_mem : forall a, 
 compat_bool StateSetSet.E.eq
     (fun P : StateSetSet.elt => StateSet.mem a P).
Proof.
   intros a x y H; rewrite H. reflexivity.
Qed.

Hint Resolve compat_bool_delta compat_bool_mem.

Lemma empty_diff_3 : forall P, StateSetSet.Equal (P [\] StateSetSet.empty) P.
  intros. apply StateSetSetProp.empty_diff_2. auto with sets.
Qed. 

(* TODO : remonter ça *)
Lemma is_empty_3 x : StateSet.is_empty x = false -> ~ StateSet.Empty x.
  intros. assert (forall b, b = false -> ~ b = true). firstorder. intro. apply H0 in H. apply H. auto with set. 
Qed.

Lemma empty_diff_4 : forall P, StateSetSet.Equal StateSetSet.empty (StateSetSet.diff P P).
Proof. intros. symmetry. apply StateSetSetProp.diff_subset_equal. reflexivity. Qed.

Lemma empty_union_1 : forall a b, StateSet.Empty (StateSet.union a b) -> StateSet.Empty a.
Proof.
    intros. 
    intros x Hx.  unfold StateSet.Empty in H. specialize (H x). apply H. 
    apply StateSet.union_2.
    apply Hx.
Qed.

Lemma empty_union_2 : forall a b, StateSet.Empty (StateSet.union a b) -> StateSet.Empty b.
Proof.
    intros. 
    intros x Hx.  unfold StateSet.Empty in H. specialize (H x). apply H. 
    apply StateSet.union_3.
    apply Hx.
Qed.

Lemma empty_union_3 : forall a b, StateSet.Empty a  -> StateSet.Empty b -> StateSet.Empty (StateSet.union a b).
Proof. intros. rewrite StateSetProp.empty_union_1; auto.
Qed.

Lemma In_excluded_middle : forall a P , StateSet.In a P \/ ~ StateSet.In a P.
Proof. intros. destruct (StateSetProp.In_dec a P); auto. Qed. 
  
Lemma in_empty : forall x p, StateSet.In x p -> StateSet.Empty p -> False.  Proof. unfold StateSet.Empty. firstorder. Qed.  


Hint Resolve In_excluded_middle empty_union_1 empty_union_2 empty_union_3: sets.

                           (*****************)
                           (** * Splittable *)
                           (*****************)

Section splittable.
(** We begin by writing a few lemmas about splittable :
   splittable p q a =o= Some (u,v) means that part of p (i.e. u) is sent to q by delta a while the other part (p\u == v) is not 
*)

  Variable DFA : DFA.

Global Instance splittable_compat : Proper ( StateSet.eq  ==> StateSet.eq ==> (Label.eq) ==> eq_option_stateset_X_stateset) (splittable DFA).
Proof.
  rintro.
  unfold splittable. 
  set (p :=StateSet.partition
               (fun i : StateSet.elt => StateSet.mem (D_delta DFA i x1) x0) x).
  set (q := StateSet.partition
               (fun i : StateSet.elt => StateSet.mem (D_delta DFA i y1) y0) y).

  assert (H' : stateset_X_stateset_eq p q). apply partition_compat. 
  rintro. rewrite ?H1, ?H, ?H0.  reflexivity. assumption. 
  set (a:= fst p);
  set (b:= snd p);
  set (c:= fst q);
  set (d:= snd q).
  assert (StateSet.eq a c). apply (proj1 H').
  assert (StateSet.eq b d). apply (proj2 H').

  case_eq (StateSet.is_empty a); 
  case_eq (StateSet.is_empty b);   
  case_eq (StateSet.is_empty c);   
  case_eq (StateSet.is_empty d); 
    simpl orb; red; intuition 
      ((
         match goal with 
            Ha : StateSet.is_empty ?a = true, Hb : StateSet.is_empty ?b = false, Hab : StateSet.eq ?a ?b  |- False => 
              rewrite Hab in Ha;rewrite Ha in Hb; discriminate
            | Ha : StateSet.is_empty ?a = true, Hb : StateSet.is_empty ?b = false, Hab : StateSet.eq ?b ?a  |- False  => 
              rewrite Hab in Hb; rewrite Hb in Ha; discriminate
          end
      ) || auto).
Qed.

Lemma splittable_partition : forall p q a u v, 
  splittable DFA p q a =o= Some (u,v) ->
  let part := (StateSet.partition
    (fun i : StateSet.elt => StateSet.mem (D_delta DFA i a) q)
    p) in 

  StateSet.Equal u (fst part)  /\    StateSet.Equal v (snd part).
Proof.
  intros.
  unfold splittable in H. subst part.
  set (part := (StateSet.partition
    (fun i : StateSet.elt => StateSet.mem (D_delta DFA i a) q)
    p)) in *.

  set (u' := fst part) in *; set (v' := snd part) in *.
  
  case_eq (StateSet.is_empty u'); 
  case_eq (StateSet.is_empty v');
  intros Hu Hv; rewrite Hu , Hv in H; simpl in H; try solve [unfold eq_option_stateset_X_stateset in H; intuition].
Qed.
 
Lemma splittable_0 : forall p q a u v, splittable DFA p q a =o= Some (u,v) ->
  StateSet.eq p (StateSet.union u v).
Proof.
  intros.
  apply splittable_partition in H. destruct H as [Hu Hv]. rewrite Hu, Hv. apply partition_union. auto.
Qed.

Lemma splittable_1 : forall x b n t, splittable DFA x b n =o= Some t -> ~ StateSet.Empty x.
Proof.
  intros x b n t H.

  unfold splittable in H.
  set (p := (StateSet.partition
                  (fun i : StateSet.elt => StateSet.mem (D_delta DFA i n) b)
                  x)) in *.
  set (u := fst p) in *; set (v := snd p) in *.
  
  case_eq (StateSet.is_empty u); 
  case_eq (StateSet.is_empty v);   
  intros Hu Hv; rewrite Hu , Hv in H; simpl in H; try solve [unfold eq_option_stateset_X_stateset in H; auto].
  assert ((u,v) = p). auto.
  assert (StateSet.eq x (StateSet.union u v)).
  eapply union_partition.  2: rewrite H0; subst p; reflexivity.
  intuition.
  intro Hemptyx. rewrite H1 in Hemptyx. clear H1.
  apply is_empty_3 in Hu. apply Hu. clear - Hemptyx. apply (empty_union_2 u v); auto.
Qed.

Lemma splittable_2 : forall p q a  u v, splittable DFA p q a =o= Some (u,v) ->
  StateSet.Subset u p /\ StateSet.Subset v p.
Proof.
  intros.
  apply splittable_0 in H.
  rewrite H. split; auto with set. 
Qed.

Lemma splittable_3 : forall p q a u v, splittable DFA p q a =o= Some (u,v) ->
  StateSet.Empty( StateSet.inter u v).
Proof.
  intros.

  apply (splittable_partition) in H. destruct H as [Hu Hv].
  rewrite Hu, Hv. 
  rewrite StateSet.partition_1, StateSet.partition_2; auto.

  apply inter_filter; auto.
Qed.

Lemma splittable_None p q a : splittable DFA p q a =o= None -> 
  forall x y, StateSet.In x p -> StateSet.In y p -> 
    StateSet.mem ((D_delta DFA) x a) q = StateSet.mem ((D_delta DFA) y a) q.
Proof.
  intros.
  rewrite <- mem_In.
  unfold splittable in H.
  set (part := (StateSet.partition
                  (fun i : StateSet.elt => StateSet.mem (D_delta DFA i a) q)
                  p)) in *.
  set (u := fst part) in *.
  set (v := snd part) in *.
  assert (StateSet.Equal p (StateSet.union u v)). 
  eapply union_partition. 2: subst u v; rewrite <- surjective_pairing; subst part; reflexivity. intuition.

  
  
  assert ((forall e, StateSet.In e u -> StateSet.mem (D_delta DFA e a) q = true) /\ 
    (forall e, StateSet.In e v -> StateSet.mem (D_delta DFA e a) q = false)).
  apply partition_predicate. rintro. rewrite H3. reflexivity.
  setoid_rewrite <- StateSetFact.mem_iff in H3.
  setoid_rewrite <- StateSetFact.not_mem_iff in H3.
  destruct H3.


  case_eq (StateSet.is_empty u); 
  case_eq (StateSet.is_empty v); intros Heu Hev; rewrite Heu, Hev in H; simpl in H; 
    try solve [
      (unfold eq_option_stateset_X_stateset in H; simpl in H; intuition auto)].
  
  assert (StateSet.Empty p). 
  rewrite H2. clear - Heu Hev.  
  rewrite <- StateSetFact.is_empty_iff in Heu, Hev. auto with sets. 
  (* TODO *)
  clear - H0 H5; byContradiction. apply (in_empty x p); auto.
 
  assert (StateSet.Equal p v).   rewrite <- StateSetFact.is_empty_iff in  Hev. clear - Hev H2. (rewrite H2, StateSetProp.empty_union_1;  reflexivity || auto).

  clear Heu Hev H2. 
  rewrite H5 in H0, H1; auto.
  assert (forall P Q, P\/~P -> Q\/~Q -> ((P <-> Q) <-> (~P <->~Q))). firstorder. rewrite H2 by auto. clear H2. intuition eauto. 

  assert (StateSet.Equal p u).   rewrite <- StateSetFact.is_empty_iff in  Heu. rewrite H2. apply StateSetProp.empty_union_2; auto. 
  clear Heu Hev H2. 
  rewrite H5 in H0, H1. clear H4 H5.
  intuition eauto.
Qed.


Lemma splittable_None_1 : forall p q a, 
    let part := (StateSet.partition
      (fun i : StateSet.elt => StateSet.mem (D_delta DFA i a) q) p) in 
    splittable DFA p q a =o= None <->
    StateSet.Empty (fst part) \/ StateSet.Empty (snd part).
Proof.
  intros.
  unfold splittable.  subst part.
  set (part := (StateSet.partition
               (fun i : StateSet.elt => StateSet.mem (D_delta DFA i a) q) p)).
  
  case_eq (StateSet.is_empty (fst part));
  case_eq (StateSet.is_empty (snd part));
  intros; unfold orb; intuition (reflexivity || auto with set).
  apply StateSet.is_empty_1 in H2. rewrite H2 in H0. discriminate.
  apply StateSet.is_empty_1 in H2. rewrite H2 in H. discriminate.
Qed.


Lemma splittable_None_2 : forall p q a , 
  (forall i, StateSet.In i p -> StateSet.In (D_delta DFA i a) q) -> splittable DFA p q a =o= None.
Proof.
  intros.
  apply <- splittable_None_1.
  right.
  rewrite StateSet.partition_2; auto.
  apply StateSet.is_empty_2.
  rewrite <-StateSetProp'.for_all_filter; auto.
  rewrite <- StateSetFact.for_all_iff; auto.
  intros x Hx. rewrite <- StateSetFact.mem_iff. auto.
Qed.


Lemma splittable_None_3 : forall p q a , 
  (forall i, StateSet.In i p -> ~StateSet.In (D_delta DFA i a) q) -> splittable DFA p q a =o= None.
Proof.
  intros.
  apply <- splittable_None_1.
  
  left. 

  rewrite StateSet.partition_1 by auto. apply StateSet.is_empty_2.
  assert (negb_involution : forall x, negb (negb x) = x). intros [|]; reflexivity. 
  
  rewrite (@StateSetFact.filter_ext (fun x => StateSet.mem (D_delta DFA x a) q) (fun x => negb (negb (StateSet.mem (D_delta DFA x a) q)))).
  2: auto.
  2 : symmetry; apply negb_involution.
  2 : reflexivity.
  rewrite <-StateSetProp'.for_all_filter by auto.
  rewrite <- StateSetFact.for_all_iff by auto.
  intros x Hx. apply negb_f. symmetry. rewrite <- StateSetFact.not_mem_iff. auto. 
Qed.



Lemma splittable_empty : forall p q a u v, 
    splittable DFA p q a =o= Some (u,v) ->
    ~ StateSet.Empty u /\ ~ StateSet.Empty v .
Proof.

  intros.
  unfold splittable in H. 
  set (part := (StateSet.partition
                  (fun i : StateSet.elt => StateSet.mem (D_delta DFA i a) q)
                  p)) in *.
  set (u' := fst part) in *.
  set (v' := snd part) in *.
  case_eq (StateSet.is_empty u');
    case_eq (StateSet.is_empty v'); unfold orb in H; intros Hu' Hv'; rewrite Hu' , Hv' in *.
  unfold eq_option_stateset_X_stateset in H; auto.
  unfold eq_option_stateset_X_stateset in H; auto.
  unfold eq_option_stateset_X_stateset in H; auto.
    unfold eq_option_stateset_X_stateset in H; auto.
    destruct H.
    split. apply is_empty_3. fold u' in H. simpl in H. rewrite <-H. trivial. 
    apply is_empty_3. fold u' in H. simpl in H. rewrite <-H0. trivial. 
  Qed.

(** 
   This is one of the main point for the Hopcroft algorithm : if we
   have split a set of states with respect to a pair (q,a), we do not
   need to split it again
   *)

Lemma splittable_4 : forall p q a u v, splittable DFA p q a =o= Some (u,v) ->
  splittable DFA u q a =o= None /\   splittable DFA v q a =o= None.
Proof.
 intros.
 apply splittable_partition in H.
 destruct H as [Hu Hv].
 split.    apply splittable_None_2. 
 intros. setoid_rewrite StateSetFact.mem_iff.
 rewrite StateSet.partition_1 in Hu by auto. rewrite Hu in H. clear Hu Hv.
 refine (StateSet.filter_2 _ H); auto.
 
 apply splittable_None_3. 
 intros. setoid_rewrite StateSetFact.mem_iff; auto.
 rewrite StateSet.partition_2 in Hv by auto. rewrite Hv in H. 
 assert (negb_morphism_not_iff : forall a , a <> true <-> negb a = true).
   intro b; destruct b; compute; intuition.

 rewrite negb_morphism_not_iff.

 refine (StateSet.filter_2 _ H); auto.
Qed.

(** Another important result : if p is included in q and q is not splittable wrt to a pair (r,b), p is not splittable either *)

Lemma splittable_5 p q r b: StateSet.Subset p q -> splittable DFA q r b =o= None -> splittable DFA p r b =o= None.
Proof.
  intros.
  assert (Hcompat :   compat_bool StateSet.E.eq
     (fun i : StateSet.elt => StateSet.mem (D_delta DFA i b) r)) by auto.

  rewrite splittable_None_1 in H0. elim H0; clear H0;  intro He; rewrite splittable_None_1. 
  left. rewrite StateSet.partition_1 in * by auto.
  setoid_rewrite StateSetFact.filter_subset; auto. apply He. auto. 
  
  right. rewrite StateSet.partition_2 in * by auto.
  setoid_rewrite StateSetFact.filter_subset. apply He. auto. assumption. 
Qed.

Lemma split_lt p q a pf pt : splittable DFA p q a = Some (pf, pt) -> 
  StateSet.cardinal pf < StateSet.cardinal p /\ StateSet.cardinal pt < StateSet.cardinal p.
Proof.
  intros.
  assert (splittable DFA p q a =o= Some (pf, pt)).
  rewrite H; reflexivity.
  assert (H' := splittable_empty _ _ _ _ _ H0).
  assert (H'' := splittable_0 _ _ _ _ _ H0).
  assert (H''' := splittable_3 _ _ _ _ _ H0).
  assert (StateSet.Equal StateSet.empty (StateSet.inter pf pt)). clear - H'''. symmetry. apply StateSetProp.empty_is_empty_1; auto.
  rewrite 2 StateSetProp.cardinal_Empty in H'.
  split. rewrite H''. rewrite StateSetProp.union_cardinal_inter. rewrite <- H1.
  rewrite StateSetProp.empty_cardinal. omega.
  rewrite H''. rewrite StateSetProp.union_cardinal_inter. rewrite <- H1.
  rewrite StateSetProp.empty_cardinal. omega.
Qed.

End splittable.  


                          (***************)
                          (* Termination *)
                          (***************)

Module StateSetSetOrdProp := FSetProperties.OrdProperties(StateSetSet).
Section Termination.

Import CoLoR.Util.Multiset.MultisetNat.
Open Scope msets_scope.

Variable DFA: DFA.

Definition P2mset P := StateSetSet.fold (fun p => union {{StateSet.cardinal p}}) P empty.

Lemma meq_Equivalence : Equivalence meq.
Proof.
  constructor ; eauto with multisets.
Qed.

Instance P2mset_compat : Proper (StateSetSet.Equal ==> meq) P2mset.
Proof.
  intros x y Hxy. unfold P2mset. 
  apply (StateSetSetOrdProp.fold_equal meq_Equivalence); auto.
  intros a b Hab u v Huv. apply union_morph; auto with multisets. apply singleton_morph. rewrite Hab. reflexivity.
Qed.

Lemma P2mset_add_1 x P :~In_P x P -> P2mset (sadd x P)  =mul= {{StateSet.cardinal x}} + P2mset P.
Proof.
intros. 
unfold P2mset at 1. rewrite StateSetSetProp.fold_add. reflexivity.  
apply meq_Equivalence.
intros a b Hab u v Huv. apply union_morph; auto with multisets. apply singleton_morph. rewrite Hab. reflexivity.
unfold transpose. intros.  setoid_rewrite union_assoc. apply union_morph; auto with multisets.  
auto.
Qed.

Lemma P2mset_add_2 x P :In_P x P -> P2mset (sadd x P)  =mul= P2mset P.
Proof.
intros. 
unfold P2mset at 1. rewrite StateSetSetProp.add_fold. reflexivity.  
apply meq_Equivalence.
intros a b Hab u v Huv. rewrite Hab, Huv. reflexivity.
unfold transpose. intros. setoid_rewrite union_assoc. apply union_morph; auto with multisets.  
auto.
Qed.

Lemma P2mset_empty : P2mset StateSetSet.empty =mul= empty.
Proof.
  unfold P2mset. 
  rewrite StateSetSetProp.fold_empty.
  reflexivity.
Qed.

Lemma P2mset_remove P z : In_P z P -> P2mset P =mul= P2mset (StateSetSet.remove z P) + {{StateSet.cardinal z}}.
Proof.
  intros HPz.
  rewrite <- (StateSetSetProp.add_remove HPz) at 1.
  rewrite P2mset_add_1. auto with multisets. 
  clear. fsetsetdec.
Qed.


Lemma P2mset_add_3 P x y :    P2mset (sadd x (sadd y P)) =mul= P2mset P + P2mset (sadd x (StateSetSet.singleton y)[\]P).
Proof.
  destruct (StateSetSetProp.In_dec y P);
    destruct (StateSetSetProp.In_dec x P).
  
  rewrite 2 P2mset_add_2; (auto).
  setoid_replace (sadd x (StateSetSet.singleton y) [\] P) with StateSetSet.empty  using relation StateSetSet.Equal by fsetsetdec.
  auto using P2mset_empty with multisets. fsetsetdec.
  
  setoid_replace (sadd x (StateSetSet.singleton y) [\] P) with (sadd x StateSetSet.empty)  using relation StateSetSet.Equal by fsetsetdec.
  rewrite P2mset_add_1. rewrite P2mset_add_2; auto. rewrite P2mset_add_1. setoid_rewrite P2mset_empty. auto with multisets. fsetsetdec. fsetsetdec.
  
  setoid_replace (sadd x (StateSetSet.singleton y) [\] P) with (sadd y StateSetSet.empty)  using relation StateSetSet.Equal by fsetsetdec.
  setoid_replace (sadd x (sadd y P)) with (sadd y P) using relation StateSetSet.Equal by fsetsetdec.
  rewrite 2 P2mset_add_1; auto. 
  auto using P2mset_empty with multisets. fsetsetdec.
  
  (* un peu plus de travail pour le dernier cas : pour ne pas avoir besoin de l'hypothèse en plus *)
  destruct (StateSetSet.E.eq_dec x y). 
      change (StateSetSet.E.eq) with (StateSet.Equal) in e. 
      setoid_replace (sadd x (StateSetSet.singleton y) [\] P) with (sadd y StateSetSet.empty)  by fsetsetdec.    
      setoid_replace (sadd x (sadd y P)) with (sadd y P) by fsetsetdec.
      rewrite 2 P2mset_add_1.  setoid_rewrite P2mset_empty. setoid_rewrite union_empty.  auto with multisets. fsetsetdec. auto.
      
      change (StateSetSet.E.eq) with (StateSet.Equal) in n1. 
      setoid_replace (sadd x (StateSetSet.singleton y) [\] P) with (sadd x(sadd y StateSetSet.empty)) by fsetsetdec.    
      rewrite 4 P2mset_add_1.  setoid_rewrite P2mset_empty. setoid_rewrite union_empty. rewrite union_assoc. rewrite union_comm. reflexivity.
    fsetsetdec. fsetsetdec. auto. fsetsetdec.
Qed.

Notation "m << n" := (MultisetGt gt n m) (at level 70).

Lemma mlt_carac m n: m<<n <-> MultisetGT gt n m.
Proof. 
  apply red_eq_direct.
  compute. intros. eapply lt_trans; eassumption. 
  compute. firstorder. 
Qed.



Lemma mlt_sadd_rem x y z P: 
  In_P z P -> 
  StateSet.cardinal x < StateSet.cardinal z ->
  StateSet.cardinal y < StateSet.cardinal z ->
(*   ~(StateSet.Equal x y) -> *)  (* on peut éventuellement demander ça, et le prouver dans split_lt *)
  P2mset (sadd x (sadd y (StateSetSet.remove z P))) << P2mset P.
Proof.
  intros Hzp Hxz Hyz.
  apply <- mlt_carac.
  apply MSetGT with 
    {{StateSet.cardinal z}} 
    (P2mset ((sadd x (StateSetSet.singleton y)) [\] (StateSetSet.remove z P)))
    (P2mset (StateSetSet.remove z P));
    auto with multisets.        

    (* un peu de manipulation de fsets *) 
    apply P2mset_remove; auto.
    
  generalize (StateSetSet.remove z P). clear. intro P.
    (* ok, fset *)    
    apply P2mset_add_3; auto.

  intros t Ht. exists (StateSet.cardinal z). auto with multisets.
  (* ok: un peu de fsets pour montrer que t=x ou t=y *)
  destruct (StateSetSetProp.In_dec y (StateSetSet.remove z P)) as [Hx | Hx];
    destruct (StateSetSetProp.In_dec x (StateSetSet.remove z P)) as [Hy | Hy].
  setoid_replace (sadd x (StateSetSet.singleton y)[\]StateSetSet.remove z P) with (StateSetSet.empty) in Ht by (clear - Hx Hy; fsetsetdec).
  byContradiction. clear - Ht. compute in Ht.  omega_false.
  
  setoid_replace (sadd x (StateSetSet.singleton y)[\]StateSetSet.remove z P) with (sadd x (StateSetSet.empty)) in Ht by (clear - Hx Hy; fsetsetdec).
  rewrite P2mset_add_1, P2mset_empty, union_empty in Ht. unfold MSet.member in Ht.
  destruct (eq_nat_dec t (StateSet.cardinal x)). rewrite e in *. omega.
  rewrite singleton_mult_notin  in Ht. omega_false. intro. apply n.  apply H. fsetsetdec.


  setoid_replace (sadd x (StateSetSet.singleton y)[\]StateSetSet.remove z P) with (sadd y (StateSetSet.empty)) in Ht by (clear - Hx Hy; fsetsetdec).
  rewrite P2mset_add_1, P2mset_empty, union_empty in Ht. unfold MSet.member in Ht.
  destruct (eq_nat_dec t (StateSet.cardinal y)). rewrite e in *. omega.
  rewrite singleton_mult_notin  in Ht. omega_false. intro. apply n.  apply H. fsetsetdec.
  

  (* encore un peu plus de boulot pour le dernier cas *)
  destruct (StateSetSet.E.eq_dec x y). 
       change (StateSetSet.E.eq) with (StateSet.Equal) in e.      
       setoid_replace (sadd x (StateSetSet.singleton y)[\]StateSetSet.remove z P) with (sadd y (StateSetSet.empty)) in Ht by (clear - e Hx Hy; fsetsetdec).
      rewrite P2mset_add_1, P2mset_empty, union_empty in Ht. unfold MSet.member in Ht.
      destruct (eq_nat_dec t (StateSet.cardinal y)). rewrite e in *. omega.
      rewrite singleton_mult_notin  in Ht. omega_false. intro. apply n.  apply H. fsetsetdec.
  
      change (StateSetSet.E.eq) with (StateSet.Equal) in n.                   
      setoid_replace (sadd x (StateSetSet.singleton y)[\]StateSetSet.remove z P) with (sadd x (sadd y (StateSetSet.empty))) in Ht by (clear - Hx Hy; fsetsetdec).
      rewrite 2 P2mset_add_1, P2mset_empty, union_empty in Ht by fsetsetdec. unfold MSet.member in Ht.
      rewrite union_mult in Ht.
      destruct (eq_nat_dec t (StateSet.cardinal y)). rewrite e in *. omega.
      destruct (eq_nat_dec t (StateSet.cardinal x)). rewrite e in *. omega.
      
      
      rewrite 2 singleton_mult_notin  in Ht. omega_false. intuition.  intuition.

Qed.



Lemma Termination: well_founded (MN_calls DFA).
Proof.
  eapply (lexico_incl_wf (fun PL: T => (fst PL, Label_x_StateSetSet.cardinal (snd PL)))).
  apply (rel_of_wf P2mset).
  apply (@mord_wf gt). compute. firstorder.
  apply lt_wf.
  apply lt_wf.
  
  
  intros [P' L'] [P L] H. simpl. inversion H. subst. clear H.
  set (Pred := fun Q (acc : T) => 
    (forall x, In_P x ( P[\]Q) -> In_P x (fst acc)) 
    /\ lexico (rel_of P2mset (MultisetLt gt)) lt
    (fst acc, Label_x_StateSetSet.cardinal (snd acc))
    (P, Label_x_StateSetSet.cardinal L)
  ).
  assert (Pred P (do_split DFA a q P (P, Label_x_StateSetSet.remove (a, q) L))).
  clear - H2. unfold do_split. 
  apply StateSetSetProp.fold_rec_bis; subst Pred; simpl.

   intros Q Q' acc HQ. setoid_rewrite HQ. trivial.

   split. 
    statesetset_dec.
    right. 
    generalize (Label_x_StateSetSet_Prop.remove_cardinal_1 (Label_x_StateSetSet.choose_1 H2)). omega.

   intros p [P' L'] Q Hp HpQ [IH1 IH2]. simpl in *.  
    split.
     intros x Hx. specialize (IH1 x). destruct (splittable DFA p q a) as [[? ?]|]; simpl; statesetset_dec.

     case_eq (splittable DFA p q a); [intros [pf pt] Hpft|auto]; simpl.
     unfold rel_of, MultisetLt, Relation_Operators.transp in *.
     left. 
     destruct (split_lt _ _ _ _ _ _ Hpft) as [Hpf Hpt]. clear Hpft.
     lpose (IH1 p) as Hp'. statesetset_dec. clear IH1 HpQ Q.
     inversion IH2; subst; clear IH2.
     apply mord_trans with (P2mset P'). assumption. apply mlt_sadd_rem; assumption.
     apply mlt_sadd_rem; assumption.

  rewrite H0 in H. apply proj2 in H. assumption.
Qed.

End Termination.

                           (**************)
                           (* Correction *)
                           (**************)

Section Correction.
Variable DFA : DFA.
Let delta := D_delta DFA.
Let max_label := D_max_label DFA.
Let finaux := D_finaux DFA.
Notation states := (smh_states DFA). 
Notation non_finaux := (smh_non_finaux DFA).
Let non_finaux := StateSet.diff states finaux.

Hypothesis finaux_subset_states : StateSet.Subset finaux states.
Hypothesis delta_states : forall p a, StateSet.In p states -> a < max_label -> StateSet.In (delta p a) states.

Lemma supplementaires_f_nf_1 : StateSet.Empty (StateSet.inter finaux non_finaux ).
Proof.
  unfold non_finaux.
  rintro. rewrite StateSetFact.inter_iff in H.  rewrite StateSetFact.diff_iff in H. intuition.
Qed.

Lemma supplementaires_f_nf_2 : StateSet.Equal (StateSet.union finaux non_finaux ) states.
Proof.
  unfold non_finaux.
  rintro. split; intros; fsetdec. 
Qed.




                             (**************)
                             (** * refine  *)
                             (**************)

(** * We state here the first part of our invariant
   refine P P' means that P' is coarser than P. Moreover, if P' distinguishes final and non final states, then P distinguishes them also *)
Definition refine P P' := 
  (forall x, StateSetSet.In x P -> StateSetSet.Exists (fun y => StateSet.Subset x y) P') /\
  (forall x a, StateSetSet.In x P' -> StateSet.In a x -> StateSetSet.Exists (fun y => StateSet.In a y) P).

(** refine is a partial order *)
Lemma refine_trans P Q R : refine P Q -> refine Q R -> refine P R.
  unfold refine. intros [H_P_Q H_Q_P] [H_Q_R H_R_Q]. split; intros.
  unfold StateSetSet.Exists in *. intuition.  intuition (eauto 200).
  specialize (H_P_Q x H).  destruct H_P_Q as [xQ [In_x_Q In_xQ_Qc]].
  specialize (H_Q_R xQ In_x_Q). destruct H_Q_R.
  exists x0.  intuition (try fsetdec). 
  
  clear H_P_Q  H_Q_R.
  specialize (H_R_Q x a H H0).  destruct H_R_Q as [xQ [In_x_Q In_xQ_Qc]].
  specialize (H_Q_P xQ a In_x_Q In_xQ_Qc). destruct H_Q_P.
  exists x0.  intuition ( fsetdec). 
Qed.

Hint Unfold refine.

Lemma refine_refl x : refine x x.
Proof.
  unfold refine. split; intros. exists x0. intuition (try fsetdec). 
  eauto.
Qed.

Global Instance refine_compat:
Proper ( 
  StateSetSet.eq ==> StateSetSet.eq ==> iff) refine.
Proof. 
  unfold Proper, respectful, pointwise_relation. intros x y Heq1 x' y' Heq2.
  unfold refine.  intuition.
  rewrite <- Heq1 in H. specialize (H0 x0 H). destruct H0. exists x1. rewrite ? Heq1 , Heq2 in *. intuition fsetdec.
  rewrite <- Heq2 in H. specialize (H1 x0 a H H2). destruct H1. exists x1. rewrite <- ? Heq1 , Heq2 in *. intuition fsetdec.
  rewrite Heq1 in H. specialize (H0 x0 H). destruct H0. exists x1. rewrite <- ? Heq1 , Heq2 in *. intuition fsetdec.
  rewrite Heq2 in H. specialize (H1 x0 a H H2). destruct H1. exists x1. clear H0. rewrite Heq1. intuition fsetdec.
Qed.

Hint Resolve refine_compat refine_refl refine_trans.
  
(** [refine_1] :
   If refine P P' then if x is in one class of P' then, x is in one of P *)
Lemma refine_1 : forall P P' x,  refine P P' -> StateSetSet.Exists (StateSet.In x) P' -> StateSetSet.Exists (StateSet.In x) P.
Proof.
  intros.
  destruct H0 as [p [Hp HpP']].
  unfold refine in H; destruct H as [_ H2]. specialize (H2 p x  Hp HpP').
  eauto.
Qed.

(** [refine_2] : 
   If [A] and [B] are disjoint sets, and P refines this partition, then each class of P is either included in A or in  BS
*)
Lemma refine_2 : forall P A B, StateSet.Empty (StateSet.inter A B) -> refine P (StateSetSet.union (StateSetSet.singleton A) (StateSetSet.singleton B)) -> 
  forall p, StateSetSet.In p P -> StateSet.Subset p A \/ StateSet.Subset p B.
Proof.
  intros P A B H_AnB [H_refine1  _] p In_p_P.
  specialize (H_refine1 p In_p_P). 
  destruct H_refine1 as [f [Hf Hfp]].
  rewrite StateSetSetFact.union_iff in Hf.  
  elim Hf; intros.
    left. 
    eapply StateSetProp.subset_trans. apply Hfp. rewrite (@StateSetSet.singleton_1 A f). apply StateSetProp.subset_refl. auto.

    right.
    eapply StateSetProp.subset_trans. apply Hfp. rewrite (@StateSetSet.singleton_1 B f). apply StateSetProp.subset_refl. auto.
Qed.

(** [refine_3] : 
   any partition in two disjoint classes of a set P refines P
   *)
Lemma refine_3 : forall P A B ,  StateSet.Empty (StateSet.inter A B) -> StateSet.Equal (StateSet.union A B) P -> refine (StateSetSet.union (StateSetSet.singleton A) (StateSetSet.singleton B)) (StateSetSet.singleton P).
Proof.

  intros.
  unfold refine. split. intros. exists P. split.  rewrite StateSetSetFact.singleton_iff. apply StateSet.eq_refl. rintro. 
  rewrite StateSetSetFact.union_iff in H1.   rewrite 2 StateSetSetFact.singleton_iff in H1.
  
  elim H1; intros.
  assert (StateSet.Equal A x). apply H3. rewrite <- H4 in H2.
  rewrite <- H0. clear - H2. fsetdec.

  assert (StateSet.Equal B x). apply H3. rewrite <- H4 in H2.
  rewrite <- H0. clear - H2. fsetdec.

  intros.
  rewrite StateSetSetFact.singleton_iff in H1. assert (StateSet.Equal P x). apply H1. rewrite <- H3 in *. clear H3 H1. rewrite <- H0 in H2. 
  rewrite StateSetFact.union_iff in H2. elim H2; clear H2;  intros.
  

  
  exists A.     rewrite StateSetSetFact.union_iff. intuition. 
  exists B.     rewrite StateSetSetFact.union_iff. intuition. 

Qed.

(** [refine_splittable_partition] :
   if we split a class in two, then the new partition we get refines the former one
   *)

Lemma refine_splittable_partition P x q u t a: 
  In_P x P -> 
  splittable DFA x q a =o= Some (u,t) ->
  refine (StateSetSet.add u (StateSetSet.add t (StateSetSet.remove x P))) P.
Proof.
  intros.
  unfold refine. intuition.
  assert (H' := splittable_2 _ _ _ _ _ _ H0).
  revert H1; StateSetSetFact.set_iff; intros [Hu | [Ht | Hxp]].

  clear - H H' Hu; exists x; intuition fsetdec.
  clear - H H' Ht; exists x; intuition fsetdec .
  exists x0; intuition.
  destruct (StateSet.eq_dec x0 x).
    destruct (StateSetProp.In_dec a0 u).
    exists u; intuition.
    destruct (StateSetProp.In_dec a0 t).
    exists t; intuition.
    byContradiction. assert (H' := splittable_0 _ _ _ _ _ _ H0). rewrite <- e in H'. clear e. rewrite  H' in H2. clear - H2 n n0.  fsetdec.
  exists x0. intuition. clear - n H2 H1 H.  fsetsetdec.

Qed.

(** Another part of our invariant, disjointness : 
   two classes of a partition do not overlap
   *)
Definition disjoint P :=
  forall x y, StateSetSet.In x P -> StateSetSet.In y P -> (StateSet.eq x y) \/ (StateSet.Empty (StateSet.inter x y )).


Instance disjoint_compat : Proper (StateSetSet.eq ==> iff) disjoint.
Proof.
rintro. unfold disjoint. split; intros. apply H0; rewrite H; auto. apply H0; rewrite <- H; auto.
Defined.

(* a tactic to help us proving stuff *)
Ltac disjoint_tac :=
  repeat match goal with 
    |   H' : StateSet.Equal ?a ?c |- StateSet.eq ?c ?d \/ StateSet.Empty (StateSet.inter ?c ?d) => 
       rewrite <- H' ; clear H'
    |   H' : StateSet.Equal ?b ?c |- StateSet.eq ?c ?d \/ StateSet.Empty (StateSet.inter ?c ?d) => 
       rewrite <- H' ; clear H'
    |   H' : StateSet.Equal ?a ?d |- StateSet.eq ?c ?d \/ StateSet.Empty (StateSet.inter ?c ?d) => 
       rewrite <- H' ; clear H'
    |   H' : StateSet.Equal ?b ?d |- StateSet.eq ?c ?d \/ StateSet.Empty (StateSet.inter ?c ?d) => 
       rewrite <- H' ; clear H'       
    |  |- StateSet.eq ?c ?c \/ _ => left; reflexivity
    |  H : StateSet.eq ?c ?d |- StateSet.eq ?c ?d \/ _ => left; assumption
    |  H : StateSet.Empty (StateSet.inter ?b ?a) |- _ \/ StateSet.Empty (StateSet.inter ?a ?b) => 
      right; rewrite StateSetProp.inter_sym; assumption
    |  H : StateSet.Empty (StateSet.inter ?a ?b) |- StateSet.Empty (StateSet.inter ?c ?d) => 
      assert (StateSet.Subset c a) by fsetdec;         
        assert (StateSet.Subset d b) by fsetdec; intuition (try fsetdec)   
      
    end.


Lemma disjoint_splittable_partition P x q u t a: 
  In_P x P -> 
  splittable DFA x q a =o= Some (u,t) ->
  disjoint P ->
  disjoint (StateSetSet.add u (StateSetSet.add t (StateSetSet.remove x P))).
Proof.
  
  unfold disjoint. 
  rename t into v.
  intros HxP Hsplit Hdisj y z.

  assert (StateSet.Empty( StateSet.inter u v)). apply (splittable_3 DFA x q a u v); auto.
  assert (StateSet.Subset u x /\ StateSet.Subset v x).  apply (splittable_2 DFA x q a u v); auto. 
  StateSetSetFact.set_iff.
  intros [Hy | [Hy | Hy]];
  intros [Hz | [Hz | Hz]]; intuition 
    (
      (specialize (Hdisj x z HxP H0); right; elim Hdisj; intro; intuition idtac; fsetdec )
      || (specialize (Hdisj x y HxP H0); right; elim Hdisj; intro; intuition idtac; fsetdec )
      ||     disjoint_tac
    ). 
    specialize (Hdisj y z H0 H4).
      destruct (StateSet.eq_dec y z). left; auto. clear - Hdisj n. right.  intuition. 
Qed.

(** [disjoint_refine] is a partial order *)
Definition disjoint_refine P' P := 
  disjoint P -> (refine P' P /\  disjoint P').

Instance disjoint_refine_refl: Reflexive (disjoint_refine). 
rintro. unfold disjoint_refine. intuition. 
Defined.

Instance disjoint_refine_trans: Transitive (disjoint_refine).
rintro. unfold disjoint_refine in *. intuition eauto.
Defined.

(** * We can now start to prove that our invariants holds on our functions *)
Lemma do_split_disjoint_refine P PL a q :
  disjoint_refine (fst PL) P ->
  (forall x, In_P x P -> In_P x (fst PL)) ->
  (disjoint_refine  (fst (do_split DFA a q P PL ))  P). 
Proof.
  intros Hdisj Hin.
  set (Pred := fun Q (acc : T) => (forall x, In_P x ( P[\]Q) -> In_P x (fst acc)) /\ disjoint_refine (fst acc) P).
  assert (Pred P (do_split DFA a q P PL)).
  unfold do_split.
  apply StateSetSetProp.fold_rec_bis; subst Pred; cbv beta.
    (* egalité *)
    simpl. intros. setoid_rewrite <- H. apply H0. 
    
    (* cas initial *)
    intros. split. clear - Hin. setoid_rewrite (empty_diff_3 P).  apply Hin.  assumption. 

    (* induction *)
    intros x [P' L'] Q HxP HxQ Hind ;    remember (splittable DFA x q a) as o; destruct o as [[pt pf] |]; simpl in *; split.
    intros y Hy.
    destruct (StateSetSetProp.In_dec y (P[\]Q)).
        StateSetSetFact.set_iff. right; right. split. apply (proj1 (Hind)); auto. clear - Hy i. fsetsetdec.
         byContradiction; clear - n Hy; fsetsetdec.
    eapply disjoint_refine_trans. 2: apply (proj2 Hind ).
      assert (splittable DFA x q a =o= Some (pt,pf)). rewrite Heqo. reflexivity.
      assert (In_P x P'). apply (proj1 Hind). clear - HxP HxQ; fsetsetdec.
      split.
      apply (refine_splittable_partition P' x q pt pf a H0 H).
 
      apply (disjoint_splittable_partition P' x q pt pf a H0 H H1).

    intros y Hy. 
    destruct (StateSetSetProp.In_dec y (P[\]Q)).
      eapply( proj1 Hind). auto.
       byContradiction; clear - n Hy; fsetsetdec.

    apply (proj2 Hind).

   (* Fin, on fini en virant le prédicat *)
   subst Pred. cbv beta in H. apply (proj2 H ).
Qed.



(** * Partition *)
Lemma disjoint_f_nf : disjoint (StateSetSet.union (StateSetSet.singleton non_finaux) (StateSetSet.singleton finaux)).
Proof.
  unfold disjoint. intros x y. StateSetSetFact.set_iff. intros.
  assert (H' : StateSet.Empty (StateSet.inter finaux non_finaux)). apply supplementaires_f_nf_1.
  intuition  disjoint_tac.
Qed.

Let partition := Min.partition (Termination DFA). 

Definition classes := StateSetSet.cardinal (partition).

Definition unsplittable P := forall Q Q' a,StateSetSet.In Q P ->  StateSetSet.In Q' P ->  a < max_label -> splittable DFA Q Q' a =o= None.

Lemma unsplittable_1 P : 
  unsplittable P->
  forall Q Q' x y a, StateSetSet.In Q P -> StateSetSet.In Q' P ->   StateSet.In x Q -> StateSet.In y Q -> a < max_label ->
  StateSet.mem ((D_delta DFA) x a) Q' = StateSet.mem ((D_delta DFA) y a) Q'.
Proof.
  intros. apply (H  Q Q' a) in H0; auto. apply (splittable_None _ _ _ _ H0) ;auto. 
Qed. 

                           (**************)
                           (* split_prop *)
                           (**************)
(** * This is the second half of our invariant : it specifies what is
   in L, the set of pairs we need to consider. Here it means that
   every interesting pair (a pair wrt to which not all classes have
   been split is in L *)

Definition split_prop P L :=
  (forall p q a uv,  a < max_label  -> In_P p P -> In_P q P -> splittable DFA p q a =o= Some uv  -> In_L (a,q) L).

Instance split_prop_compat :
Proper ( StateSetSet.eq  ==> Label_x_StateSetSet.eq ==> iff) (split_prop).
Proof.
  unfold split_prop.
  rintro; intuition. rewrite <- H0.
  refine (H1 p q a uv _ _ _ H5); auto; 
  match goal with | H : StateSetSet.eq ?y ?x , H' : ?P ?x |- ?P ?y =>  (rewrite  H; apply H') end.


  rewrite H0.
  refine (H1 p q a uv _ _ _ H5); auto; 
  match goal with | H : StateSetSet.eq ?x ?y , H' : ?P ?x |- ?P ?y =>  (rewrite <- H; apply H') end.
Qed.

Lemma split_prop_empty : forall P , split_prop P Label_x_StateSetSet.empty -> unsplittable P.
Proof.
  intros.
  unfold  unsplittable. unfold split_prop in H.

  intros p q a Hp Hq Ha . 
  case_eq (splittable DFA p q a). intros uv Huv.
  assert (Huv' : splittable DFA p q a =o= Some uv). rewrite Huv; auto.
  specialize (H p q a uv Ha Hp Hq Huv').
  byContradiction; clear - H; lsetdec. 
  auto.
Qed.

(** * In order to prove the correction of our algorithm, we need to relax our invariant for the inner loop [do_split]
   Here, the interesting cuts for P\Q are in L, or are in (a,q) :: L for Q
*)
Definition split_prop_partial P Q L q a := 
  (forall p r b uv, In_P p (P [\] Q) -> In_P r P -> b < max_label -> splittable DFA p r b =o= Some uv -> In_L (b,r) L)
  /\  
  (forall p r b uv, In_P p Q -> In_P r P -> b < max_label -> splittable DFA p r b =o= Some uv -> In_L (b,r) (ladd (a,q) L))

.

Instance split_prop_partial_compat :
Proper ( StateSetSet.eq  ==> StateSetSet.eq ==> Label_x_StateSetSet.eq ==> (StateSet.eq) ==> (@eq nat)  ==>  iff) (split_prop_partial).
Proof.
  unfold split_prop_partial.
  rintro; intuition. 
  
  rewrite <- H1.
  refine (H5 p r b uv _ _ _ H9); auto. 
  rewrite H;   rewrite H0; trivial.
  rewrite H; auto.
  
  assert (Label_x_StateSetSet.E.eq (x3,x2) (y3,y2) ).
  unfold Label_x_StateSetSet.E.eq.   simpl. rewrite <- H2, <- H3. intuition.
  rewrite <- H1, <- H10.
  
  refine (H6 p r b uv _ _ _ H9); auto. 
  rewrite H0; auto.
  rewrite H; auto.

  rewrite    H1.
  refine (H5 p r b uv _ _ _ H9); auto. 
  rewrite <- H;   rewrite <- H0; trivial.
  rewrite <- H; auto.

  assert (Label_x_StateSetSet.E.eq (x3,x2) (y3,y2) ).
  unfold Label_x_StateSetSet.E.eq.   simpl. rewrite <- H2, <- H3. intuition.
  rewrite  H1, H10.

  refine (H6 p r b uv _ _ _ H9); auto. 
  rewrite <- H0; auto.
  rewrite <- H; auto.
Qed.

(** * The initial step : going from [split_prop] to [split_prop_partial] *)
Lemma split_prop_to_partial P L q a  : 
  Label_x_StateSetSet.In (a,q) L ->
  split_prop P L   
  -> split_prop_partial P P (Label_x_StateSetSet.remove (a,q) L) q a .
Proof. 
  rintro.
  intros. unfold split_prop in H0.
  split; intros.
  byContradiction; clear - H1; fsetsetdec.
  rewrite Label_x_StateSetSet_Prop.add_remove; auto.
  eapply (H0 p); eauto. 
Qed.

(** * If Q is empty, then nobody can be cut wrt (a,q), and we can go back from split_prop_partial P StateSetSet.empty L q a to split_prop P L *)

Lemma partial_to_split_prop P L q a   : split_prop_partial P StateSetSet.empty L q a -> split_prop P L .
Proof.
  intros H.
  destruct H as [ H _]. 
  
  unfold split_prop. 
  intros p r b uv Hb Hp Hr Huv.
  eapply (H p); eauto. clear - Hp. fsetsetdec.
Qed.

(** * We define here some properties about fold_labels, namely that we
will use fold_labels in situations where it considers every letter
separately *) 

Definition slicing f : Prop := forall k n L, k < n -> (forall p, In_L (k,p) (fold_labels f n L) <-> In_L (k,p) (f k L)).

Definition preserving f : Prop :=
  (forall k n L, k <> n -> (forall p, In_L (k,p) (f n L) <->  In_L (k,p) L)).

Definition compat_eq f : Prop :=
  forall L L' x (n : nat), (In_L x L <-> In_L x L') -> (In_L x (f n L) <-> In_L x (f n L')).

Fixpoint fold_labels' T f a (acc: T) {struct a} : T := 
  match a with
    | 0 => acc
    | S b => f b (fold_labels' T f b acc)
  end.

Lemma fold_labels'_aux T a f (acc: T): fold_labels' T f (S a) acc = fold_labels' T (fun a => f (S a)) a (f 0 acc).
Proof.
  revert f acc; induction a; intros g acc.
  reflexivity.
  simpl in IHa. simpl fold_labels' at 1.
  rewrite IHa. reflexivity.
Qed.

Section f.
Variable f: nat -> Label_x_StateSetSet.t -> Label_x_StateSetSet.t.
Hypothesis Hf: Proper (@eq nat ==> Label_x_StateSetSet.Equal ==> Label_x_StateSetSet.Equal) f.
Hypothesis Hf': forall i j acc, i<>j -> Label_x_StateSetSet.Equal (f i (f j acc)) (f j (f i acc)).

Lemma fold_labels_compat i: Proper (Label_x_StateSetSet.Equal ==> Label_x_StateSetSet.Equal) (fold_labels (fun a => f (S a)) i).
Proof.
  induction i; intros x y H.
  trivial.
  simpl.
  apply IHi.
  apply Hf; trivial.
Qed.

Lemma fold_labels_aux a acc: 
  Label_x_StateSetSet.Equal (fold_labels f (S a) acc) (fold_labels (fun a => f (S a)) a (f 0 acc)).
Proof.
  induction a in acc |- *.
  reflexivity.
  simpl in *.
  rewrite IHa.
  apply fold_labels_compat. 
  apply Hf'. auto with arith.
Qed.
End f.

Section f'.
  Variable f: nat -> Label_x_StateSetSet.t -> Label_x_StateSetSet.t.
  Hypothesis Hf: Proper (@eq nat ==> Label_x_StateSetSet.Equal ==> Label_x_StateSetSet.Equal) f.
  Hypothesis Hf': forall i j acc, i<>j -> Label_x_StateSetSet.Equal (f i (f j acc)) (f j (f i acc)).

  Lemma fold_labels_eq a acc: Label_x_StateSetSet.Equal (fold_labels' _ f a acc) (fold_labels f a acc).
  Proof.
    revert f Hf Hf' acc. induction a; intros f Hf Hf' acc.
    reflexivity.
    rewrite fold_labels'_aux. 
    rewrite IHa; trivial. simpl.
    rewrite <- fold_labels_aux; trivial. reflexivity.
    intros x y H u v H'. apply Hf. congruence. assumption. 
    intros i j u H. apply Hf'. omega.
  Qed.
  
  Variable P: nat -> Label_x_StateSetSet.t -> Prop.
  Hypothesis HP: Proper (@eq nat ==> Label_x_StateSetSet.Equal ==> iff) P.

  Lemma fold_labels_rec: forall a acc,
    P O acc -> (forall n acc ,  P n acc -> P (S n) (f n acc)) -> 
    P a (fold_labels f a acc) .
  Proof. 
    induction a; intros acc H0 HS.
    trivial.
    rewrite <- fold_labels_eq.  simpl. rewrite fold_labels_eq.
    firstorder.
  Qed.
End f'.

Section f''.
  Variable f: nat -> Label_x_StateSetSet.t -> Label_x_StateSetSet.t.
  Hypothesis Hf: Proper (@eq nat ==> Label_x_StateSetSet.Equal ==> Label_x_StateSetSet.Equal) f.
  Hypothesis Hf': forall i j acc, i<>j -> Label_x_StateSetSet.Equal (f i (f j acc)) (f j (f i acc)).
  
  Lemma slicing_is_preserving: compat_eq f -> preserving f -> slicing f .
  Proof.
    unfold compat_eq, slicing, preserving; intros Hcomp Hpres k n L.  revert k.
    set( Pred := fun n acc => 
      (forall i, i < n -> forall p, In_L (i,p) acc <-> In_L (i,p) (f i L) )
      /\ (forall i, n <= i -> forall p, In_L (i, p) acc <-> In_L (i,p) L)).
    
    assert (Pred n (fold_labels f n L)).
    
    apply fold_labels_rec; trivial.
    
    intros x y H u v H'. unfold Pred. subst. setoid_rewrite H'. tauto.
    
    subst Pred; cbv beta; split; intros.
    omega_false.  reflexivity.
    
    subst Pred; cbv beta; split; intros.
    destruct (eq_nat_dec i n0).
    destruct H as [_ H]. clear H0. rewrite e. clear Hpres.
    apply Hcomp. apply H; auto.
    
    assert (i < n0) by omega.
    rewrite Hpres; auto. apply H; auto.
    assert (n0 <= i) by omega. rewrite Hpres; auto. apply (proj2 H); auto.
    
    subst Pred.
    
    simpl in H. intuition.
  Qed.
End f''.

(** * We show that the function that updates the splitters [f_update_splitters] is [preserving] *)
Lemma preserving_update_splitters  p pf pt : preserving (f_update_splitters p pf pt).
  unfold preserving.
  unfold f_update_splitters; intros; Label_x_StateSetSet_Fact.set_iff; simpl.
  assert (forall a b c q, (a /\ (b \/ c))\/ q <-> ((a /\ b) \/ ((a /\c) \/ q))) by firstorder auto.
  setoid_rewrite <- H0.
  split; [intros [[H' _] | [H' _]] ; intuition | intro; right; intuition]. 
   
Qed.

Lemma compat_eq_update_splitters p pf pt : compat_eq (f_update_splitters p pf pt).
Proof. 
  unfold compat_eq.
  unfold f_update_splitters; intros; Label_x_StateSetSet_Fact.set_iff; simpl.
  assert (or_iff :forall a b c , (b <-> c) -> ( a \/ b <-> a \/ c)) by firstorder auto.
    
  do 2 apply or_iff.
  assert (and_iff : forall a b c , (b <-> c) -> ( b /\ a <-> c /\ a)) by firstorder auto. 
  apply and_iff. 
  apply H.
Qed.
  
Section tautos.
Variable P: Prop.
Lemma and_true: True /\ P <-> P. Proof. tauto. Qed. 
Lemma and_false: False /\ P <-> False. Proof. tauto. Qed. 
Lemma or_true: True \/ P <-> True. Proof. tauto. Qed. 
Lemma or_false: False \/ P <-> P. Proof. tauto. Qed. 
Lemma not_true: ~ True <-> False. Proof. tauto. Qed. 
Lemma not_false: ~ False <-> True. Proof. tauto. Qed. 
End tautos.
Hint Rewrite and_true and_false or_true or_false not_true not_false: debile.

Lemma slicing_update_splitters p pf pt : slicing (f_update_splitters p pf pt).
Proof.
  intros.
  apply slicing_is_preserving; auto using compat_eq_update_splitters, preserving_update_splitters.
  intros x y H u v H'. subst. unfold f_update_splitters. rewrite H'. reflexivity.
  intros i j acc H. unfold f_update_splitters.
  intros [k l]. Label_x_StateSetSet_Fact.set_iff. unfold fst, snd.
  assert (forall a b c q, (a /\ (b \/ c))\/ q <-> ((a /\ b) \/ ((a /\c) \/ q))) by firstorder auto.
  setoid_rewrite <- H0.   setoid_rewrite <- H0. clear H0.
 
 

  (* ici, on aimerait bien que firstorder / tauto marche tout seul... *)
  destruct (eq_nat_dec i k); subst. 
   setoid_replace (k=k) with True by tauto. autorewrite with debile. 
   destruct (eq_nat_dec j k); subst. 
    setoid_replace (k=k) with True by tauto. autorewrite with debile. tauto. 
    setoid_replace (j=k) with False by tauto. autorewrite with debile. tauto.    
   setoid_replace (i=k) with False by tauto. autorewrite with debile. tauto.
Qed. 

Lemma In_slicing f n L: slicing f ->
  forall b r, b < n -> 
  In_L (b,r) (f b L)  -> In_L (b,r) (fold_labels f n L).
Proof.
  intros.
  unfold slicing in H.
  apply <- H; auto.
Qed.

(** * These are the two main lemmas for this part : 
   if (b,r) is in L, then it will be in the updated version of L
   and if r == u \/ r == v, then (b,r) will be in the updated version of L wrt to (u,v)
*)
Lemma In_update_splitters P L x u v:
 forall max_label r b, In_P r (sadd u (sadd v (StateSetSet.remove x P))) -> b < max_label ->  (In_P r P -> In_L (b,r) L) -> In_L (b,r) (update_splitters x u v max_label L  )
.
Proof.
  intros.
  apply In_slicing; auto.
  apply slicing_update_splitters.
  unfold f_update_splitters.
  revert H; StateSetSetFact.set_iff.
  Label_x_StateSetSet_Fact.set_iff;
  intros [Hru | [Hrv | HrP]];
   simpl; intuition.
Qed.

Lemma In_update_splitters_2 L r b : forall max_label x u v,
  b < max_label -> (StateSet.eq r u \/  StateSet.eq r v) ->  In_L (b,r) (update_splitters x u v max_label L).
Proof.
  intros.
  apply In_slicing; auto.
  apply slicing_update_splitters.
  unfold f_update_splitters.

  Label_x_StateSetSet_Fact.set_iff;
  
   simpl; intuition.
Qed.

Lemma split_prop_partital_Some P Q x L q a u v : 
  In_P x Q ->
  split_prop_partial P Q L q a ->
  splittable DFA x q a =o= Some (u,v) ->
  split_prop_partial (sadd u (sadd v (StateSetSet.remove x P))) (StateSetSet.remove x Q) (update_splitters x u v (D_max_label DFA) L) q a
  .
Proof.
  rename u into s; rename v into t.
  intros HxQ Hspp Hst.
  split; intros p r b uv Hp Hr Hb Huv.

  (* Four cases : p in [P \ Q, {t}, {s}, Q\{x}] the last one being a contradiction with Hp *)
  destruct (StateSetSetProp.In_dec p (StateSetSet.remove x Q)) as [Hp' | Hp'].
    clear - Hp' Hp. fsetsetdec.
  
  destruct (StateSetSetProp.In_dec p (P [\] Q)) as [Hp'' | Hp''].
    destruct Hspp as [ Hspp _].
      eapply In_update_splitters; auto. apply Hr. intro.
      eapply (Hspp p); eauto.

  (* It remains to show what happens when p \in {s,t} *)
  assert (StateSetSet.E.eq p s \/ StateSetSet.E.eq p t). clear - Hp HxQ Hp' Hp''. fsetsetdec. 

  destruct (Label_x_StateSetSet.E.eq_dec  (a,q) (b,r)) as [e|n]. 
  destruct e as [Hab Hqr]; simpl in Hab, Hqr. rewrite <- Hab , <- Hqr in Huv; clear Hab Hqr.
  byContradiction. elim H; intro H'; change StateSetSet.E.eq with StateSet.eq in H'; rewrite H' in Huv.
  apply splittable_4 in Hst. destruct Hst as [Hs _].  rewrite Hs in Huv. clear - Huv. auto.
  apply splittable_4 in Hst. destruct Hst as [_ Ht].  rewrite Ht in Huv. clear - Huv. auto.
  (* fin de ce cas *)

  destruct (Hspp) as [ _ Hspp].

  assert (copy : forall (A : Prop), A -> A /\ A) by intuition. 
  apply copy in Hr. destruct Hr as [Hr1 Hr2].

  revert Hr1; StateSetSetFact.set_iff. intros [Hrs | [ Hrt | Hrr]].
  apply In_update_splitters_2; auto.
  apply In_update_splitters_2; auto.
  eapply In_update_splitters; eauto using Hr2.  intros.

  case_eq (splittable DFA x r b).
  intros uv' Htemp. assert (Huv' :  splittable DFA x r b =o= Some uv').  rewrite Htemp; reflexivity. clear Htemp.
  specialize (Hspp x r b uv' HxQ  H0 Hb Huv' ).
  revert Hspp; Label_x_StateSetSetFact.set_iff; intros [Hfalse | Hfinish]; [byContradiction | apply Hfinish].
  apply n. apply Hfalse.
  intros Htemp. 
  (******)
  clear H0. clear  Hspp.
  byContradiction. (*splittable x r b = None alors que splittable s r b = Some*)
    assert(Htemp' : splittable DFA x r b =o= None). rewrite Htemp; reflexivity. clear Htemp.
    elim H; clear H; intro H; rewrite H in Huv; apply splittable_2 in Hst.
    eapply (splittable_5 _ s) in Htemp'.  rewrite Huv in Htemp'. clear - Htemp'. intuition. intuition.
    eapply (splittable_5 _ t) in Htemp'.  rewrite Huv in Htemp'. clear - Htemp'. intuition. intuition.

  (* conclusion*)

  destruct (Hspp) as [ _ Hspp]. 
  destruct (StateSetSetProp.In_dec r P).
  assert (In_L (b,r) (ladd (a,q) L)). eapply (Hspp p); eauto. fsetsetdec. 
  revert H. Label_x_StateSetSetFact.set_iff. intros [Heq | Hneq]. left. assumption. right. eapply In_update_splitters. apply Hr. auto. intros. assumption.
  destruct (Label_x_StateSetSet.E.eq_dec (a,q) (b,r) ) as [e|n'];
  Label_x_StateSetSetFact.set_iff. left. apply e. 
  right. eapply In_update_splitters; auto. apply Hr. intro. byContradiction. auto.
Qed.
  
Lemma split_prop_partial_None P Q  x L q a  :
   In_P x Q ->
   split_prop_partial P Q L q a ->
   splittable DFA x q a =o= None ->
   split_prop_partial P (StateSetSet.remove x Q) L q a. 
Proof. 
  intros HxQ Hspp Hsplit.
  split; intros p r b uv Hp Hr Hb Huv. 
  
  (* Three cases : p in [P \ Q, {x}, Q\{x}] the last one being a contradiction with Hp *)
  destruct (StateSetSetProp.In_dec p (P [\] Q)) as [Hp' | Hp'].
    destruct Hspp as [ Hspp _].
      eapply (Hspp p); eauto.
    
  destruct(StateSetSetProp.In_dec p (StateSetSet.remove x Q)) as [ Hp'' | Hp''].
     clear - Hp Hp' Hp''; fsetsetdec.

  
  destruct Hspp as [_ Hspp]. 
  assert (Hxp : StateSetSet.E.eq x p) by (clear - HxQ Hp Hp' Hp'' ;fsetsetdec).    

  assert (In_L (b,r) (ladd (a,q) L)). eapply (Hspp p); eauto.  
    rewrite <- Hxp. auto.
    
  destruct (Label_x_StateSetSet.E.eq_dec  (a,q) (b,r)) as [e|n].
    byContradiction. assert (None =o= Some uv). rewrite <- Hsplit, <- Huv. clear Hsplit Huv. rewrite Hxp.
      unfold Label_x_StateSetSet.E.eq in e. simpl in e. rewrite (proj1 e) , (proj2 e). reflexivity. auto.
    revert H; Label_x_StateSetSetFact.set_iff. intros [e | Hbr]; [byContradiction | auto]. apply n. apply e.
    
  destruct Hspp as [ _ Hspp].
     eapply (Hspp p); eauto. clear - Hp; fsetsetdec.
Qed.

(** * Main lemma : our invariant is preserved by [do_split] *)
Lemma do_split_split_prop_partial P L P' L' Q q a :  split_prop_partial P Q L q a ->
  (P',L') = do_split DFA a q  Q (P,L) -> split_prop_partial P' StateSetSet.empty L' q a.
Proof.

  intros HPL.
  unfold do_split.
  set (f := (fun (p : StateSetSet.elt) (acc : T) =>
          match splittable DFA p q a with
            | Some (pair pf pt) =>
              let (P0, L0) := acc in
                (StateSetSet.add pf (StateSetSet.add pt (StateSetSet.remove p P0)),
                  update_splitters p pf pt (D_max_label DFA) L0)
            | None => acc
          end)).

 set (Pred Q' acc :=  split_prop_partial P Q L q a -> split_prop_partial (fst acc) (StateSetSet.diff Q Q') (snd acc) q a).
 
 assert (Pred Q (StateSetSet.fold f Q (P,L))).
 Opaque split_prop_partial. 
 apply StateSetSetProp.fold_rec_bis.
   (* cas d'egalite *)  
   subst Pred; cbv beta; intros. rewrite <- H. auto.

   (* cas empty *)
   subst Pred. cbv beta. intros. simpl.   
   setoid_rewrite (empty_diff_3 Q). auto. 
   
   (* cas inductif *)
   subst Pred. subst f. cbv beta. intros.
   remember (splittable DFA x q a)as o; destruct o. destruct p; destruct a0. unfold fst,snd in *.
   setoid_replace (StateSetSet.diff Q (StateSetSet.add x s')) with (StateSetSet.remove x (StateSetSet.diff Q s')) using relation StateSetSet.Equal by fsetsetdec.
   apply split_prop_partital_Some; auto. clear - H H0; fsetsetdec. rewrite Heqo. reflexivity.
   setoid_replace (StateSetSet.diff Q (StateSetSet.add x s')) with (StateSetSet.remove x (StateSetSet.diff Q s')) using relation StateSetSet.Equal by ( clear - H H0;  fsetsetdec).
   apply split_prop_partial_None; auto. clear - H H0; fsetsetdec. rewrite Heqo; reflexivity. 
 
   (* conclusion *)
   subst Pred.  cbv beta in *. intros.  setoid_rewrite (empty_diff_4 Q).
   apply cpl_fst_snd in H0. destruct H0; subst. apply H. assumption.
 Qed.

Lemma do_split_split_prop P P' L L' a q: split_prop P L -> 
  Label_x_StateSetSet.In (a,q) L ->
  (P',L') = do_split DFA a q P (P,(Label_x_StateSetSet.remove (a,q) L)) -> split_prop P' L'.
Proof.
  intros.
  eapply partial_to_split_prop.
  eapply do_split_split_prop_partial.
  2:  apply H1.
  apply split_prop_to_partial. assumption. apply H.
Qed.
    



                 (*********************************)
                 (* Main lemmas about partitions  *)
                 (*********************************)

Lemma disjoint_partition_initiale :  disjoint (partition_initiale DFA). 
Proof.
   unfold partition_initiale.
   unfold disjoint. 
   intros.
   assert (H' := supplementaires_f_nf_1).
   fold finaux in H, H0.
   revert H H0; StateSetSetFact.set_iff. intros [Hx | Hx] [Hy | Hy];   disjoint_tac. right. apply H'.
Qed.
 
Section lset.
  Variable x : StateSet.t.
  Let laddx b L := (ladd (b,x) L).
  
  Lemma fold_labels_add_Subset : forall n acc, Label_x_StateSetSet.Subset acc (fold_labels laddx n acc). 
  Proof.
    intros. apply fold_labels_rec_nodep. reflexivity.
    intros. Label_x_StateSetSetDecide.fsetdec.
  Qed.

  Lemma fold_labels_add_union : forall n acc, Label_x_StateSetSet.eq (fold_labels laddx n acc) (Label_x_StateSetSet.union acc (fold_labels laddx n Label_x_StateSetSet.empty)).
  Proof.
    assert (forall P, Label_x_StateSetSet.Equal P (Label_x_StateSetSet.union P Label_x_StateSetSet.empty)).
    intros. 
    assert (Label_x_StateSetSet.Empty Label_x_StateSetSet.empty). auto. symmetry; apply Label_x_StateSetSet_Prop.empty_union_2. auto.
    
    intros. revert acc. induction n.
    simpl. auto. 
    simpl. intros. setoid_rewrite IHn at 2. rewrite IHn.
    set (y := fold_labels laddx n Label_x_StateSetSet.empty).
    rewrite Label_x_StateSetSet_Prop.double_inclusion.
    split; intros e H'; revert H'; Label_x_StateSetSetFact.set_iff; intro H'; intuition (lsetdec) . (* This is a pity ... *)
  Qed.

  Lemma fold_labels_add n : forall e, e < n <-> Label_x_StateSetSet.In (e,x) (fold_labels laddx n Label_x_StateSetSet.empty).
  Proof.
    intros. induction n. split; intros; [omega_false | Label_x_StateSetSetDecide.fsetdec].
    simpl. destruct (eq_nat_dec e n) as [Hen | Hen]. rewrite Hen. intuition. apply  fold_labels_add_Subset. Label_x_StateSetSetDecide.fsetdec.
    split; intros.
    
    assert (e < n). clear IHn. omega. apply -> IHn in H0. clear - H0. rewrite fold_labels_add_union. Label_x_StateSetSetDecide.fsetdec.
    rewrite fold_labels_add_union in *. 
    revert H. revert IHn. Label_x_StateSetSetFact.set_iff.  intuition ( try lsetdec). 2:omega.  
    revert H. unfold laddx. Label_x_StateSetSetFact.set_iff. simpl. intuition.
  Qed.
End lset.


Lemma initial_cover a q : In_P q (partition_initiale DFA) -> a < max_label -> In_L (a,q) (coupes_initiales DFA).
Proof.
  intros.
  unfold coupes_initiales. 
  unfold partition_initiale in H.
  
  rewrite fold_labels_add_union.
  Label_x_StateSetSet_Fact.set_iff.
  revert H; StateSetSetFact.set_iff;  intros [H | H]; [right | left].
    assert (Label_x_StateSetSet.E.eq (a,q) (a,D_finaux DFA)). unfold Label_x_StateSetSet.E.eq. simpl. intuition.
    rewrite H1.
    rewrite <- (@fold_labels_add (D_finaux DFA) (D_max_label DFA) a ). auto.

    assert (Label_x_StateSetSet.E.eq (a,q) (a, Correction.non_finaux )). unfold Label_x_StateSetSet.E.eq. simpl. intuition.
    rewrite H1.
    rewrite <- (@fold_labels_add ). auto.
Qed.

Lemma MyhillNerode_disjoint_refine PL : disjoint_refine (MyhillNerode (Termination DFA) PL) (fst PL). 
Proof. 
  intros. functional induction (MyhillNerode (Termination DFA) PL). reflexivity.
  simpl. eapply disjoint_refine_trans. apply IHt. eapply do_split_disjoint_refine. reflexivity.
  intros. simpl. auto.
Qed.


Lemma MyhillNerode_split_prop PL: split_prop (fst PL) (snd PL) -> unsplittable (MyhillNerode (Termination DFA) PL).
Proof.
  intros.
  functional induction (MyhillNerode (Termination DFA) PL). 
  apply split_prop_empty.  simpl in H. 
  assert (Label_x_StateSetSet.Empty L). apply Label_x_StateSetSet.choose_2; auto. 
  rewrite <- Label_x_StateSetSet_Prop.empty_is_empty_1 . apply H. apply H0.


  simpl in *. apply IHt.  eapply do_split_split_prop. apply H.  apply Label_x_StateSetSet.choose_1; eauto. 
  symmetry. apply surjective_pairing.
Qed.


Lemma partition_1 : unsplittable partition.
Proof.
  intros.
  unfold partition. unfold Min.partition.  apply MyhillNerode_split_prop. simpl.
  unfold split_prop. intros.   apply initial_cover; auto.
Qed.

Lemma partition_2' : refine  partition (partition_initiale DFA). 
Proof.
  intros. 
  unfold partition.
  unfold Min.partition. 
  refine (proj1 (MyhillNerode_disjoint_refine _ _)).
  simpl.  
  refine disjoint_partition_initiale.

Qed.

Lemma partition_2 : refine  partition (StateSetSet.singleton states).
Proof.
  intros.
  eapply refine_trans. apply partition_2'. unfold partition_initiale.
  refine (refine_3 states finaux non_finaux _ _ ). fold finaux. refine supplementaires_f_nf_1.
  apply supplementaires_f_nf_2.
Qed.

Lemma partition_3 : disjoint partition.
  unfold partition .
  refine (proj2 (MyhillNerode_disjoint_refine _ _)).
  simpl; unfold partition_initiale. rewrite StateSetSetProp.union_sym.
  apply disjoint_f_nf.
Qed.

(*****************************************************************************************************************)
(*                                                                                                               *)
(*                                       NE RIEN CHANGER CI DESSOUS                                              *)
(*                                                                                                               *)
(*****************************************************************************************************************)

                         (*********************)
                         (** * Equiv_classes  *)
                         (*********************)


(** [equiv_classes i ] renvoie un ensemble de classes contenant [i]. On verra ensuite que cet ensemble est soit vide, soit un singleton *)
Definition equiv_classes : nat -> StateSetSet.t := fun i =>
  StateSetSet.filter (fun x => StateSet.mem i x) partition.

Lemma equiv_classes_0 i : forall x, StateSetSet.In x (equiv_classes i) -> StateSet.In i x.
Proof.
  intros.
  unfold equiv_classes in H.
  rewrite StateSetFact.mem_iff.  change ((fun x => StateSet.mem i x)  x = true).
  eapply StateSetSet.filter_2. 
  unfold compat_bool. intros. 
  eapply StateSetFact.mem_m; auto.
  apply H.
Qed.

Lemma equiv_classes_1  : forall x, StateSet.In x states -> StateSetSet.Subset (equiv_classes x) partition.  
Proof.
  intros.
  unfold equiv_classes.
  rintro. 
  eapply StateSetSet.filter_1; [| apply H0].
      rintro. apply StateSetFact.mem_m; auto. 
Qed.

Lemma equiv_classes_2 : forall x, StateSet.In x states ->  ~StateSetSet.Empty (equiv_classes x).
Proof.
  intros.
  assert (StateSetSet.Exists (StateSet.In x) partition).
  eapply refine_1.
  apply partition_2.
  exists states; intuition. 
  
  unfold equiv_classes  in *.  rintro.
  unfold StateSetSet.Empty in H1. 
 
  destruct H0 as [P [H2 H3]]. 
  specialize (H1 P).
  apply H1. clear H1. 
  apply StateSetSet.filter_3.
    unfold compat_bool. intros. 
    eapply StateSetFact.mem_m; auto. 
    
    assumption.
    
    rewrite <- StateSetFact.mem_iff. assumption.
Qed.

Lemma equiv_classes_3 : forall x cl, StateSet.In x states -> StateSet.In x cl -> StateSetSet.In cl partition -> StateSetSet.In cl (equiv_classes x).
Proof.
  intros.
  unfold equiv_classes. apply StateSetSet.filter_3; auto.
  rewrite <- StateSetFact.mem_iff. auto.
Qed.

Hint Resolve equiv_classes_0 equiv_classes_1 equiv_classes_2 equiv_classes_3.

                          (*******************)
                          (** * Equiv_classe *)
                          (*******************)

Definition equiv_classe : nat -> StateSet.t := fun i =>
  match StateSetSet.choose (equiv_classes i) with
    | Some p => p
    | None => StateSet.empty
  end.

Lemma equiv_classe_0 x : StateSet.In x states -> StateSetSet.In (equiv_classe x) partition.
Proof.
  intros.
  unfold equiv_classe.
  remember (StateSetSet.choose (equiv_classes x)). destruct o.
  eapply StateSetSetProp.in_subset. 
  Focus 2. apply equiv_classes_1. apply H.
  eapply StateSetSet.choose_1. auto.
  
  symmetry in Heqo.
  assert (H' := StateSetSet.choose_2 Heqo). clear Heqo.
  assert (H'' := equiv_classes_2 x H). tauto_false.
Qed.

Lemma equiv_classe_ind P : forall x, StateSet.In x states -> (forall q, StateSetSet.In q (equiv_classes x) -> P q) -> P (equiv_classe x).
Proof.
  intros.
  assert (H' :=equiv_classe_0 x H).
  unfold equiv_classe.
  remember (StateSetSet.choose (equiv_classes x)). destruct o.
  assert (StateSetSet.In e (equiv_classes x)).  apply StateSetSet.choose_1. symmetry; auto.
  apply X. apply H0.
  assert (H'' := equiv_classes_2 x H).  
  cut False; [contradiction|]. 
  apply H''. apply StateSetSet.choose_2. symmetry in Heqo. auto.
Qed.

Lemma equiv_classe_1 : forall x  q, StateSet.In x states -> StateSetSet.In q (equiv_classes x) -> StateSet.eq q (equiv_classe x).
Proof.
  intros.
  apply equiv_classe_ind. auto.
  intros.
  assert (StateSetSet.In q partition).
  eapply equiv_classes_1; [| apply H0]; auto.
  assert (StateSetSet.In q0 partition).
  eapply equiv_classes_1; [| apply H1]; auto.
  
  destruct (partition_3 _ _ H2 H3); auto.
  
  cut False; [contradiction|]. 
  eapply H4.
  apply StateSet.inter_3; auto. 
  apply equiv_classes_0; eauto.
  apply equiv_classes_0; eauto.
Qed.
  
Lemma equiv_classe_2 : forall x, StateSet.In x states -> StateSet.In x (equiv_classe x).
Proof.
  intros.
  apply equiv_classe_ind. assumption.
  intros. apply equiv_classes_0. assumption.
Qed.

  
Lemma equiv_classe_3 : forall x, StateSet.In x states -> StateSetSet.In (equiv_classe x) (equiv_classes x).
Proof.
  intros.

  apply equiv_classe_ind. assumption.
  intros.  assumption. 
Qed.

Hint Resolve equiv_classe_0 equiv_classe_1 equiv_classe_2 equiv_classe_3.

(* This lemma differs from the filter_ext one in FSetFact *)
Lemma filter_ext : forall f f' s, compat_bool StateSet.eq f -> compat_bool StateSet.eq f' ->
  (forall x, StateSetSet.In x s -> f x = f' x) ->
  StateSetSet.Equal (StateSetSet.filter f s)  (StateSetSet.filter f' s).
Proof.
  intros f f' s Hf  Hf' Hff' x.
  do 2 (rewrite StateSetSetFact.filter_iff; auto).
  intuition ((rewrite Hff' || rewrite <-Hff'); auto) . 
Qed.  


Lemma equiv_classe_4 : forall p q a, StateSet.In p states -> StateSet.In q states -> a < max_label -> 
  StateSet.eq (equiv_classe p) (equiv_classe q) ->
  StateSet.eq (equiv_classe (delta p a)) (equiv_classe (delta q a)).
Proof.
  intros.
  assert (StateSetSet.eq (equiv_classes (delta p a)) (equiv_classes (delta q a))).
  unfold equiv_classes.

  apply filter_ext; auto.

    intros.
    eapply (unsplittable_1 partition);auto. apply partition_1; auto. apply equiv_classe_0;auto. rewrite H2. auto.
    
  apply equiv_classe_1; auto.
  rewrite <- H3.
  apply equiv_classe_3; auto.
Qed.

                             (***************)
                             (** * classe   *)
                             (***************)

Definition classe : nat -> nat := fun s => @theta StateSet.t StateSet.eq StateSet.eq_dec (equiv_classe s) (StateSetSet.elements partition).

Notation Local "[ p ]" := (classe p).

Lemma classe_lt_classes : forall x, StateSet.In x states -> (classe x < classes)%nat.
Proof.
  intros. unfold classes. unfold classe.
  rewrite StateSetSet.cardinal_1.
  apply theta_correction_InA_lt.
  auto.
  assert (H' := equiv_classe_0 x H).
  assert (H'' :=  StateSetSet.elements_1 H').
  apply H''.
Qed.


(* BUG : B. Barras : 
   without this strategy the following proof hangs on Qed.
*)
Strategy 1010 [Min.partition]. 
Lemma classe_1 j p : StateSet.In j states -> StateSet.In p states -> [j] = [p] -> StateSet.eq (equiv_classe j) (equiv_classe p).
Proof.  
  intros.  
  eapply theta_inversion. apply StateSet.eq_trans. apply StateSet.eq_sym. 
  Focus 4.
  unfold classe in H1.  eapply H1.
  apply StateSetSet.elements_3w.
  apply StateSetSet.elements_1. apply equiv_classe_0. assumption.
  apply StateSetSet.elements_1. apply equiv_classe_0. assumption.
Qed.
    
Lemma classe_2 : forall j p a, StateSet.In j states -> StateSet.In p states->  a < max_label -> [j] = [p] -> [delta j a] = [delta p a].
Proof.
  intros.  
  assert (StateSet.eq (equiv_classe j) (equiv_classe p)).
  apply classe_1; auto.
  assert (StateSet.eq (equiv_classe (delta j a)) (equiv_classe (delta p a))). apply equiv_classe_4; auto.
  unfold classe. apply theta_compat. apply StateSet.eq_trans. apply StateSet.eq_sym. assumption. reflexivity.
Qed.

Lemma negb_true : true = negb false.
Proof. reflexivity. Qed.

Lemma negb_false : false = negb true.
Proof. reflexivity. Qed.
Hint Immediate negb_false negb_true.

Lemma finality x a b : StateSet.In x states -> a = negb b  -> (StateSet.mem x non_finaux = a <-> StateSet.mem x finaux = b).
Proof.
  intros.
  assert (H' := supplementaires_f_nf_1).
  destruct a; destruct b; compute in H0; try discriminate; clear H0;
  rewrite <- StateSetFact.mem_iff , <- StateSetFact.not_mem_iff; 
  intuition fsetdec.
Qed.

Lemma classe_3 : forall j p , StateSet.In j states -> StateSet.In p states -> [j] = [p] -> StateSet.mem j finaux = StateSet.mem p finaux.
  intros.
  assert (StateSet.eq (equiv_classe j) (equiv_classe p)). apply classe_1; auto.
  assert (H' := refine_2 partition finaux non_finaux supplementaires_f_nf_1 partition_2' (equiv_classe j) (equiv_classe_0 j H)).
  intuition.
  assert (StateSet.Subset (equiv_classe p) finaux) by (rewrite <- H2; auto).
  assert (StateSet.In j finaux); auto. 
  assert (StateSet.In p finaux); auto. 
  rewrite StateSetFact.mem_iff in H5 , H6. rewrite H5 , H6. reflexivity.

  assert (StateSet.Subset (equiv_classe p) non_finaux) by (rewrite <- H2; auto).
  assert (StateSet.In j non_finaux); auto. 
  assert (StateSet.In p non_finaux); auto. 
  rewrite StateSetFact.mem_iff in H5 , H6.
  rewrite finality in H5, H6; auto. rewrite H5, H6. reflexivity. 
Qed.

Lemma classe_4 : forall x y, StateSet.In x states -> StateSet.In y states -> equiv (Termination DFA) x y = true -> [x] = [y].
Proof.
  intros x y Hx Hy H.
  unfold equiv in H. rewrite <- StateSetSetFact.exists_iff in H; auto.
  assert (StateSet.eq (equiv_classe x) (equiv_classe y)).
  
  destruct H as [cl [Hcl1 Hcl2]]. 
  rewrite andb_true_iff in Hcl2. 
    assert (Hx' : StateSet.In x cl) by intuition auto with set. 
    assert (Hy' : StateSet.In y cl) by intuition auto with set.  clear Hcl2. 

  assert (H' := partition_3).
  assert (In_P cl (equiv_classes x)) by  auto. 
  assert (In_P cl (equiv_classes y)) by auto. 
  transitivity cl; [symmetry |]; apply equiv_classe_1; auto.
   
  unfold classe. 
  apply theta_compat; eauto.
  (* compat_bool : *)intros a b Hab; rewrite Hab; reflexivity.
Qed.


End Correction.  


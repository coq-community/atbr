(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(* Removal of epsilon transitions: from eNFAs to NFAs *)

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

Require Import DKA_Definitions.

Require Import Utils_WF.
Require Import Relations.       
Require Import Eqdep_dec.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section fold'.
  Variable A: Type.
  Definition stateset_fold p (f: forall i, A -> StateSet.mem i p = true -> A) a :=
    StateSet.fold 
      (fun i a => 
        match StateSet.mem i p as x return StateSet.mem i p = x -> A with
          | true => fun H => f i a H
          | false => fun _ => a
        end refl_equal) p a.
  Implicit Arguments stateset_fold [].

  Lemma bool_dec' : forall a b: bool, a=b \/ a<>b.
  Proof. intros. destruct (bool_dec a b); auto. Qed.

  Lemma stateset_fold_rec_bis: 
    forall (P : stateset -> A -> Type) p (f : forall i, A -> StateSet.mem i p = true -> A) i,
      (forall u v a, StateSet.Equal u v -> P u a -> P v a) ->
      P StateSet.empty i ->
      (forall x a q (H: StateSet.mem x p = true), 
        ~StateSet.In x q -> P q a -> P (StateSet.add x q) (f x a H)) ->
      P p (stateset_fold p f i).
  Proof.
    intros P p f i Hc Hi Ha. refine (StateSetProps.Props.fold_rec_bis _ _ _); auto.
    clear i Hc Hi.
    intros x a q Hxp Hxq IHa.
    apply StateSet.mem_1 in Hxp.

    replace ((if StateSet.mem x p as x0 return (StateSet.mem x p = x0 -> A)
       then fun H : StateSet.mem x p = true => f x a H
       else fun _ : StateSet.mem x p = false => a) 
        refl_equal) with (f x a Hxp). auto.
    remember (f x a) as f'. clear.  revert Hxp f'. 
     destruct (StateSet.mem x p); intros.
      rewrite (eq_proofs_unicity bool_dec' Hxp refl_equal). reflexivity.
      discriminate.
  Qed.
End fold'.    
Implicit Arguments stateset_fold [A].


Section map_transitive_closure.
  
  Variable f: state -> stateset.
  Let R: relation state := fun i j => StateSet.mem i (f j) = true.
  
  Definition terminates := Init.Wf.well_founded R.
  Hypothesis Hwf: terminates.

  Definition rt_closure_aux: state -> statemap stateset -> statemap stateset * stateset :=
    Fix Hwf (fun _ => statemap stateset -> statemap stateset * stateset)
      (fun i rt_closure_aux acc => 
        match StateMap.find i acc with 
          | Some pi => (acc,pi)
          | None => 
            let (acc,pi) := 
              stateset_fold (f i) (fun j accp Hj =>
                let '(acc,p) := accp in
                  let (acc,pj) := rt_closure_aux j Hj acc in
                    (acc,StateSet.union pj p)
              ) (acc,StateSet.singleton i) in
              (StateMap.add i pi acc, pi)
        end).

  Definition rt_closure_aux' i acc := fst (rt_closure_aux i acc).

  Definition rt_closure size: state -> stateset := 
    statemap_set_to_fun (fold_states rt_closure_aux' size (StateMap.empty _)).

End map_transitive_closure.

Definition set_closure (c: state -> stateset) (p: stateset): stateset :=
  StateSet.fold (fun i => StateSet.union (c i)) p StateSet.empty.

Definition statelabelmap_set_to_fun d := fun a i => optionset_to_set (StateLabelMap.find (i,a) d).

Definition eNFA_to_NFA A (Hwf: eNFA.well_founded A) := 
  let (size,_,delta,initial,final,max_label) := A in
  let eps := rt_closure (guard 100 Hwf) size in
    NFA.build 
    size
    (statelabelmap_set_to_fun (StateLabelMap.map (set_closure eps) delta))
    (eps initial)
    (StateSet.singleton final)
    max_label.
Implicit Arguments eNFA_to_NFA [].





(** specifiaction the generic transitive closure algorithm *)


Definition step f: relation state := fun i j => StateSet.mem j (f i) = true.
Definition steps f: relation state := clos_refl_trans_1n _ (step f).

Definition valid f i p := forall j, StateSet.In j p <-> steps f i j.
Definition approx f acc := forall i p, StateMap.MapsTo i p acc -> valid f i p.

Lemma add_valid: forall acc f i p B, valid f i p /\ approx f acc /\ B -> 
  StateMap.MapsTo i p (StateMap.add i p acc) /\ approx f (StateMap.add i p acc) /\ B.
Proof.
  intros. unfold approx. 
   StateMapProps.map_iff. intuition. 
   revert H1. StateMapProps.map_iff. intuition; subst; trivial. 
Qed.

Ltac destruct_fold_pair H :=
  match type of H with 
    context [stateset_fold ?x ?f ?acc] => 
    case_eq (stateset_fold x f acc); 
    let acc' := fresh "acc" in
    let p' := fresh "p" in
    let H' := fresh "H" in
      intros acc' p' H'; 
      rewrite H' in H; simpl in H;
      injection H; intros; subst; clear H
  end.

Import Common.                  (* to get Common.apply *)

Lemma rt_closure_aux_spec: forall f (Hwf: terminates f) i acc acc' p,
  approx f acc -> rt_closure_aux Hwf i acc = (acc',p) -> 
  StateMap.MapsTo i p acc' /\ approx f acc' /\ (forall j, StateMap.In j acc -> StateMap.In j acc').
Proof.
  intros f Hwf.
  refine (Fix_induction Hwf (P:=fun i (g: statemap stateset -> _) => 
    forall acc acc' p, approx f acc -> g acc = (acc',p) -> 
      StateMap.MapsTo i p acc' /\ approx f acc' /\ (forall j, StateMap.In j acc -> StateMap.In j acc')) _).

  (** interesting part *)
  intros i G IH acc acc' p Hacc Hcall.

  StateMapProps.find_analyse. 
   (* 1 memoised case *)
   auto.

   (* 2 non memoised case *)
   clear H. simpl in Hcall. destruct_fold_pair Hcall. apply add_valid.
 
   match type of H with stateset_fold _ ?f _ = _ => set (g:=f) in * end.
   pose (stateset_fold_rec_bis 
     (f:=g)
     (P:=fun x' accy => 
       let '(acc',y) := accy in
         approx f acc' /\
         (forall j, StateSet.In j y -> steps f i j) /\
         (forall j, steps f i j -> StateSet.In j y 
           \/ exists2 k, StateSet.In k (StateSet.diff (f i) x') & steps f k j) /\
         (forall j, StateMap.In j acc -> StateMap.In j acc')
     )
     (i:=(acc,StateSet.singleton i))
     (p:=f i)
   ) as H'.
   rewrite H in H'. clear H. 
   apply apply in H'. apply apply in H'. apply apply in H'. 

    intuition. intro j. intuition. destruct (H0 _ H2) as [? | [k ? ?]];  trivial.
    clear - H4. revert H4. StateSetProps.set_iff. tauto.
    StateMapProps.map_iff. auto.

    (* 2.1 internal inductive case *)
    clear - IH. 
    intros j [acc' p] y Hij Hnjy IHx. simpl. intuition.
    unfold g in *; clear g.
    case_eq (G j Hij acc'). intros acc'' pj Heq. apply IH in Heq; trivial; clear IH.
    intuition. 
     revert H4. StateSetProps.set_iff. intros [H4|H4].
      apply H5 in H2. apply H2 in H4. clear - Hij H4. econstructor 2; eassumption.
      apply H1 in H4. trivial.
     destruct (H0 _ H4) as [H8 | [k H9 H10]].
      left. clear - H8. StateSetProps.set_iff. auto.
      destruct (eq_num_dec k j).
       subst. left. apply H5 in H2. apply H2 in H10. revert H10. clear. StateSetProps.set_iff. auto. 
       right. exists k; trivial. revert H9. clear -n. StateSetProps.set_iff. intuition.

    (* 2.2 external base case *)
    clear - Hacc.
    intuition.
     revert H. StateSetProps.set_iff. intro H. subst. constructor 1.
     inversion_clear H. 
      left. auto with set.
      right. exists y; trivial. StateSetProps.set_iff; auto with set. 

    (* remaining compatibility lemma *)
    clear. intros u v [acc' y] Hu H. intuition.
    destruct (H1 j H2) as [?|[k ? ?]]; auto.
    right. exists k; auto. rewrite <- Hu. trivial.
Qed.


Lemma rt_closure_aux'_spec: forall f Hwf n acc, 
  approx f acc -> 
  approx f (@rt_closure_aux' f Hwf n acc) 
  /\ forall i, StateMap.In i acc \/ i=n -> StateMap.In i (@rt_closure_aux' f Hwf n acc).
Proof.
  intros. unfold rt_closure_aux'. 
  case_eq (rt_closure_aux Hwf n acc); intros acc' p H'. 
  apply rt_closure_aux_spec in H'; auto.
  split.
   apply H'.
   intros i [Hi| ->]; simpl.
    apply H', Hi.
    exists p. apply H'.
Qed.
   
Lemma rt_closure_prespec: forall f Hwf size acc,
  approx f acc ->
  approx f (fold_states (@rt_closure_aux' f Hwf) size acc) 
  /\ forall i, below i size \/ StateMap.In i acc -> 
    StateMap.In i (fold_states (rt_closure_aux' Hwf) size acc).
Proof.
  induction size using Pind; intros acc H.
   split. apply H. intros i [Hi|H']. destruct i; discriminate Hi. apply H'.
   specialize (IHsize (rt_closure_aux' Hwf size acc)).
   pose proof (rt_closure_aux'_spec Hwf size H) as [Happrox Hin].
   apply apply in IHsize as [IHapprox IHin]; auto. 
   unfold fold_states. rewrite Prect_succ. split; trivial.
   intros i Hi. destruct (eq_num_dec i size).
    subst. auto. 
    apply IHin. destruct Hi as [Hi|Hi]; auto.
    left. clear -Hi n. num_omega.
Qed.


Theorem rt_closure_spec: forall f Hwf size i, below i size ->
  forall j, steps f i j <-> StateSet.In j (@rt_closure f Hwf size i).
Proof.
  intros f Hwf size i Hi j.
  pose proof (rt_closure_prespec Hwf size (acc:=StateMap.empty _)) as H.
  apply apply in H. destruct H as [Happrox Hin].
  eapply apply in Hin; eauto. destruct Hin as [p Hip].
  specialize (Happrox _ _ Hip). unfold valid in Happrox. rewrite <- Happrox.
  apply -> StateMapProps.find_mapsto_iff in Hip.
  unfold rt_closure, statemap_set_to_fun. rewrite Hip.
  reflexivity.
  clear. intros j acc. StateMapProps.map_iff. tauto.
Qed.



Section algebraic_lemmas.

  Context `{KA: KleeneAlgebra}.

  Lemma algebraic_correctness: forall A B C (j' j n m': X B B) (u u': X A B) (v v': X B C),
    j'==j# -> m'==n*j' -> u'==u*j' -> v'==v -> u*(j+n)#*v == u'*m'#*v'.
  Proof.
    intros.
    rewrite H0, H1, H2, H.
    rewrite star_distr. monoid_reflexivity.
  Qed.
  
  Lemma algebraic_rt_closure: forall A (j' j : X A A), 1 <== j' -> j' * j' <== j' -> j<==j' -> j# <== j'.
  Proof.
    intros A j' j Hr Ht H.
    transitivity (j'#); auto with algebra.
     apply star_destruct_left_one. semiring_normalize. rewrite Ht, Hr. auto with algebra.
  Qed.

  Lemma xif_bool_incr: forall A B b c (x : X A B), (b=true -> c=true) -> xif b x 0 <== xif c x 0.
  Proof.
    intros. destruct b.
     rewrite H; auto.
     simpl. trivial with algebra.
  Qed.

End algebraic_lemmas.

Notation ns := nat_of_state.
Notation sn := state_of_nat.

Lemma rt_closure_star: forall f Hwf size, (forall i, below i size -> setbelow (f i) size) -> 
  (mx_bool tt (ns size) (ns size) (fun i j => StateSet.mem (sn j) (f (sn i)))) #
  ==
  (mx_bool tt (ns size) (ns size) (fun i j => StateSet.mem (sn j) (@rt_closure f Hwf size (sn i)))).
Proof.
  intros f Hwf size Hbounded.
  apply leq_antisym. 
   apply algebraic_rt_closure; simpl; fold_regex; intros i j Hi Hj; fold_leq. 
    nat_analyse; fold_regex; auto with algebra.
    subst. type_view StateSet.mem; auto with algebra. 
    elim n. rewrite <- rt_closure_spec by num_omega. constructor 1.

    apply sum_leq. intros k _ Hk.
    type_view StateSet.mem. 2: simpl; fold_regex; semiring_reflexivity.
    type_view StateSet.mem. 2: simpl; fold_regex; semiring_reflexivity.
    type_view StateSet.mem. simpl; fold_regex; semiring_reflexivity.
    elim n.
     rewrite <- rt_closure_spec by num_omega. 
     apply trans_rt1n. constructor 3 with (sn k); 
      apply rt1n_trans; apply <- rt_closure_spec; eauto; instantiate; num_omega. 
     
    type_view StateSet.mem. 2: simpl; fold_regex; aci_reflexivity.
    type_view StateSet.mem. simpl; fold_regex; aci_reflexivity.
    elim n.
     rewrite <- rt_closure_spec by num_omega.
     constructor 2 with (sn j). apply StateSet.mem_1 in i0. assumption. constructor 1.

   mx_intros i j Hi Hj. simpl. fold_regex; fold_leq.
   set (m := mx_bool Datatypes.tt (ns size) (ns size) (fun i j => StateSet.mem (sn j) (f (sn i)))).
   type_view StateSet.mem; auto with algebra. rename i0 into Hij.
   rewrite <- rt_closure_spec in Hij by num_omega.
   revert Hi Hj. rewrite <- (id_nat i), <- (id_nat j). revert Hij.  
   generalize (sn j) as j'. generalize (sn i) as i'. clear - Hbounded.
   intros i j ij. induction ij; intros Hi Hj.
    transitivity (!(1+m*m#) (ns x) (ns x)). 
    simpl; fold_regex; fold_leq. nat_analyse. auto with algebra.
    apply equal_leq. refine (star_make_right m _ _ Hi Hj).

    transitivity (!(1+m*m#) (ns x) (ns z)). 
    simpl; fold_regex; fold_leq. rewrite <- plus_make_right.
    assert (ns y < ns size). 
     rewrite <- lt_nat_spec in Hi. apply Hbounded in Hi. 
     rewrite <- lt_nat_spec. apply Hi. apply StateSet.mem_2, H. 
    apply leq_sum. exists (ns y); repeat split; auto with arith.
    rewrite 2id_num. rewrite H. rewrite <- IHij by assumption. unfold xif. monoid_reflexivity.
    apply equal_leq. refine (star_make_right m _ _ Hi Hj).
Qed.

Local Opaque star dot plus zero one equal leq guard .

Lemma mem_set_closure: forall f i p,
  StateSet.mem i (set_closure f p) = StateSet.exists_ (fun j => StateSet.mem i (f j)) p.
Proof.
  intros f i p. unfold set_closure.
  rewrite StateSetProps.exists_fold by (repeat intro; psubst; reflexivity).
  
  (* Generalisation preinduction *)
  assert (StateSet.mem i StateSet.empty = false) by auto with set. 
  revert H;  generalize StateSet.empty;  generalize false.

  change stateset with NumSet.t in *. (* BUG d'induction *)
  induction p using StateSetProps.set_induction_below; intros b acc Hbacc. 
  
     rewrite 2 StateSetProps.fold_empty; (repeat intro; num_prop; psubst; try reflexivity || ti_auto). 
     rewrite H1; reflexivity.

     (* asserts used to avoid non instantiated variables *)
     assert (SetoidList.compat_op eq StateSet.Equal (fun i => StateSet.union (f i))).
        repeat intro. rewrite H3. psubst. reflexivity.
     assert (SetoidList.compat_op eq (@eq bool) (fun x acc => StateSet.mem i (f x) || acc)).
        repeat intro. psubst. reflexivity.
        
     rewrite (StateSetProps.fold_equal _ H2 _ H1).
     rewrite (StateSetProps.fold_equal _ H3 _ H1). 

     setoid_rewrite StateSetProps.fold_add_below;  
       try solve [(repeat intro; num_prop;  subst; try reflexivity || ti_auto)].
     rewrite (IHp1 (StateSet.mem i (f x) || b)); [reflexivity|].
     rewrite <- Hbacc.
     rewrite bool_prop_iff. bool_connectors. rewrite <- 3NumSetProps.mem_iff. StateSetProps.setdec. 
     repeat intro; num_prop; psubst; rewrite H5; reflexivity.
Qed.

Lemma delta_bounded: forall A, eNFA.bounded A -> 
  forall i a n x, StateLabelMap.MapsTo (i, a) x (eNFA.deltamap A) -> StateSet.In n x -> below n (eNFA.size A).
Proof.
  intros [size eps delta initial final max_label] Hb i a n x Hx Hnx.
  simpl. apply (@eNFA.bounded_delta _ Hb a i). 
  unfold eNFA.delta in *. simpl in *. apply StateLabelMapProps.find_mapsto_iff in Hx. rewrite Hx. apply Hnx.
Qed.
  

Theorem correct: forall A HA, eNFA.bounded A -> NFA.eval (eNFA_to_NFA A HA) == eNFA.eval A.
Proof.
  intros [size eps delta initial final max_label] Hwf Hb.
  apply mx_to_scal_compat. simpl. symmetry.
  apply algebraic_correctness with
    (mx_bool tt (ns size) (ns size) (fun i j => StateSet.mem (sn j) 
      (rt_closure (guard 100 Hwf) size (sn i)))).

  (* j' = j# *)
  symmetry. apply rt_closure_star. 
  intros. apply Hb.

  Local Transparent dot plus zero one equal. 

  (* m' = n*j' *)
  simpl; fold_regex. intros i j Hi Hj. unfold labelling.
  setoid_rewrite sum_distr_left.
  rewrite sum_inversion.
  apply sum_compat. intros a Ha. simpl; fold_regex.
  unfold eNFA.delta, eNFA.deltamap, statelabelmap_set_to_fun.
  setoid_rewrite dot_xif_zero. 
  setoid_rewrite dot_neutral_right.
  rewrite StateLabelMapProps.map_o.
  unfold numota_of_nat.
  StateLabelMapProps.find_analyse; simpl; fold_regex. 
  rewrite mem_set_closure.
  match goal with |- context [StateSet.exists_ ?f ?p] => set (e:=StateSet.exists_ f p) end.
  apply leq_antisym.
   case_eq e; intros Hj'; trivial with algebra.
   apply leq_sum.
    subst e; apply <- StateSetProps.exists_iff in Hj'. destruct Hj' as [n [Hnx Hjn]].
    exists (ns n); repeat split; auto with arith.
    simpl. rewrite <- lt_nat_spec. apply (delta_bounded Hb H Hnx).
    apply StateSet.mem_1 in Hnx. rewrite 2id_num. rewrite Hnx.
    unfold statesetelt_of_nat in Hjn. rewrite Hjn. reflexivity. 
    repeat intro. psubst. reflexivity.
   apply sum_leq. intros n _ Hn.
    apply xif_bool_incr. bool_connectors. intros [Hnx Hjn].
    apply -> StateSetProps.exists_iff. 2: repeat intro;  psubst; reflexivity.
    exists (sn n); split; assumption.
  setoid_rewrite StateSetProps.empty_b. symmetry. rapply sum_fun_zero. 

  (* u' = u*j' *)
  mx_intros i j Hi Hj. simpl; fold_regex.
  rewrite (sum_collapse (n:=ns initial)). simpl. bool_simpl. simpl. fold_regex. unfold statesetelt_of_nat. 
  monoid_reflexivity. 
  apply -> lt_nat_spec. apply Hb.
  simpl. intros k Hk. nat_analyse. simpl. fold_regex. auto with algebra.

  (* v' = v *)
  mx_intros i j Hi Hj. simpl. fold_regex. apply xif_compat; trivial.
  bool_simpl. rewrite bool_prop_iff. num_prop. nat_prop. num_omega. 
Qed. 



Lemma rt_closure_bounded: forall f Hwf size, 
  (forall i, below i size -> setbelow (f i) size) -> 
   forall i, below i size -> setbelow (@rt_closure f Hwf size i) size.
Proof.
  intros f Hwf size H i Hi j Hj.
  rewrite <- rt_closure_spec in Hj by trivial.
  revert Hi. induction Hj; intro Hi; trivial.
  apply IHHj.
  apply (H x Hi). apply StateSet.mem_2, H0.
Qed. 

Lemma bounded: forall A HA, eNFA.bounded A -> NFA.bounded (eNFA_to_NFA A HA).
Proof.
  intros [size eps delta initial final max_label] Hwf Hb. unfold eNFA_to_NFA. constructor; simpl.
   (* delta *)
   intros a i j Hj. unfold statelabelmap_set_to_fun in Hj. 
   rewrite StateLabelMapProps.map_o in Hj.
   StateLabelMapProps.find_analyse; simpl in Hj. 2: StateSetProps.setdec.
    apply StateSet.mem_1 in Hj. rewrite mem_set_closure in Hj. 
    rewrite <- StateSetProps.exists_iff in Hj by (repeat intro; psubst; reflexivity). 
    destruct Hj as [n [Hnx Hjn]].
    eapply rt_closure_bounded. 3: apply StateSet.mem_2, Hjn. intros. apply Hb.
    apply (delta_bounded Hb H Hnx).
   (* initiaux *)
   intros i Hi. eapply rt_closure_bounded. 3: apply Hi. 2: apply Hb. 
   clear i Hi. intros i Hi. apply Hb.
   (* finaux *)
   intros i. StateSetProps.set_iff. intro Hi. psubst. apply Hb.
Qed.

Lemma preserve_max_label: forall A HA, NFA.max_label (@eNFA_to_NFA A HA) = eNFA.max_label A.
Proof.
  intros A HA. destruct A. reflexivity.
Qed.

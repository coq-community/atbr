(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Conversion from NFAs to DFAs.

    The algorithm basically constructs a [Store], i.e.,
    - a bijection from reachable set of states to a new set of states,
    represented as a [Table] together with a bound (the next fresh state, 
    or, equivalently, the size of the [Table])
    - a transition relation over these new states, represented by a
      map ([Delta])
    *)

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
Require Import DKA_StateSetSets.
Require Import Numbers.
Require Import Utils_WF.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import Numbers.Positive.
Open Scope num_scope.




Notation Table := (statesetmap state).
Notation Delta := (statelabelmap state).
Notation Store := (Table * Delta * state)%type.

Section S.

  Open Scope num_scope.
  Variable A : NFA.t.
  
  Notation delta := (NFA.delta A).
  Notation initiaux := (NFA.initiaux A).
  Notation finaux := (NFA.finaux A).
  Notation max_label := (NFA.max_label A).
  Notation size := (NFA.size A).

  (** extension of the transition function to sets *)
  Definition delta_set :=
    let delta := delta in
      fun (a: label) (q: stateset) => StateSet.fold (fun x => StateSet.union (delta a x)) q StateSet.empty.

  (** we start with the store mapping the set of initial states to one *)
  Definition initial_store: Store := 
    (StateSetMap.add initiaux (state_of_nat 0) (StateSetMap.empty _),StateLabelMap.empty _,(state_of_nat 1)).

  (** the algorithm (function [build_store] below) consists in iterating the following function [step], 
     defined by open recursion through the [loop] argument.
     intuitively, [step loop p np a s] assumes that [p] points to [np] in the store [s] ;
     it returns the store where all descendants of [p] along [a] have been added.
     *)
  Definition step (delta_set: label -> stateset -> stateset) loop p np := 
    (fun a s => 
      let q := delta_set a p in
        let '(table,d,next) := s in
          match StateSetMap.find q table with 
            | None => loop (StateSetMap.add q next table, StateLabelMap.add (np,a) next d, S next) q next
            | Some nq => (table, StateLabelMap.add (np,a) nq d, next)
          end
    ).

  (** powerfix does (2^size) iterations, which is sufficient since the set of 
     reachable sets of states cannot have a larger size. 
     at each stage, one folds over the set of labels to add all the descendence of [p] 
     *)
  Definition build_store :=
    let step := step delta_set in
    let max_label := max_label in
    powerfix size
    (fun loop (s: Store) (p: stateset) (np: state) => 
      fold_labels (step loop p np) max_label s
    ) (fun s _ _ => s) initial_store initiaux 0.

  (** once we obtained the store, it suffices to convert it into a DFA *)
  Definition table_finals (table: Table) :=
    let finaux := finaux in
    StateSetMap.fold 
      (fun p np acc => 
        if StateSet.exists_ (fun s => StateSet.mem s finaux) p 
          then StateSet.add np acc else acc
      ) table StateSet.empty.

  Definition delta' (d: Delta) := 
    fun a x => match StateLabelMap.find (x,a) d with Some y => y | None => 0 end.

  Definition NFA_to_DFA :=
    let '(t,d,n) := build_store in
      DFA.mk n (delta' d) 0 (table_finals t) max_label.


  (** Now starts the correctness proof ; we need to know that the NFA [A] is bounded. *)
  Hypothesis HA: NFA.bounded A.


  (** We start the correctness proof by characterising [build_store] with the 
     following simpler fixpoint (which is problematic from the computational point of 
     view: one has to compute the worst case exponential bound, even if it is not 
     reached) *)
  Definition step' := step delta_set.

  Fixpoint steps n s p np :=
    match n with 
      | O => s
      | Datatypes.S n => fold_labels (step' (steps n) p np) max_label s
    end.

  Instance step_compat: Proper 
    (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (@eq _)))
      ==>
     pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (@eq _))))) step'.
  Proof.
    intros f g H p np a s. unfold step', step. 
    destruct s as [[table d]next].
    StateSetMapProps.find_analyse; trivial. apply H. 
  Qed.

  (** characterisation of [build_store] with [steps], as explained above *)
  
  Lemma build_store_spec: build_store = steps (power size) initial_store initiaux (state_of_nat 0).
  Proof.
    unfold build_store.
    pose (Heq:=powerfix_linearfix (A:=Store) (B:=stateset -> num -> Store) (R:=pointwise_relation _ (pointwise_relation _ (@eq _)))).
    unfold pointwise_relation at -1 -2 -3 in Heq.
    rewrite Heq. 
    generalize (state_of_nat 0) initiaux initial_store. generalize (power size) as n. 
    induction n; intros s p np; simpl.
     reflexivity.
     apply fold_num_compat, step_compat. repeat intro. apply IHn.
     intros f g H s ? <- p np. apply fold_num_compat, step_compat, H.  
  Qed.


  Notation "s %t" := (fst (fst s)) (at level 1).
  Notation "s %d" := (snd (fst s)) (at level 1).
  Notation "s %s" := (snd s) (at level 1).

  (** preliminary lemma: [delta_set] builds bounded sets *)
  Lemma bounded_delta_set: forall a p, setbelow (delta_set a p) size.
  Proof.
    intros. unfold delta_set.
    apply StateSetProps.Props.fold_rec_nodep.
    intros x Hx. StateSetProps.setdec.
    intros x i Hx IH y Hy. apply StateSet.union_1 in Hy as [Hy|Hy]; auto.
    apply HA in Hy. exact Hy.
  Qed.


  (** Invariant of the construction *)
  Record invariant s: Prop := {
    (** all states in the table are bounded *)
    i_table_wf: forall p i, StateSetMap.MapsTo p i s%t -> setbelow p size /\ below i s%s;
    (** the table is injective *)
    i_table_inj: forall p q i, StateSetMap.MapsTo p i s%t -> StateSetMap.MapsTo q i s%t -> StateSet.Equal p q;
    (** the table is surjective *)
    i_table_surj: forall i, below i s%s -> exists p, StateSetMap.MapsTo p i s%t;
    (** the table contains [s%n] elements (derivable from the two previous points, but easier to require here) *)
    i_table_size: StateSetMap.cardinal s%t = nat_of_num s%s;
    (** any transition in [s%d] corresponds to a [delta_set] transition in the NFA *)
    i_delta: forall np a nq, StateLabelMap.MapsTo (np,a) nq s%d -> 
      exists2 p, StateSetMap.MapsTo p np s%t & StateSetMap.MapsTo (delta_set a p) nq s%t
  }.

  (** Dynamics of the construction : we basically prove that [invariant s] 
     entails [extends s (steps i s) /\ defined (steps i s)] *)
  Record extends (s s': Store): Prop := {
    (** the resulting store satisfies the invariant *)
    e_invariant :> invariant s';
    (** the table was extended *)
    e_table: forall p i, StateSetMap.MapsTo p i s%t -> StateSetMap.MapsTo p i s'%t;
    e_next: s%s <= s'%s
  }.

  (** Last definition: a store is `defined up to P' if there are transitions for all state [n] and label [a], 
     except for those specified in P *)
  Definition defined (s: Store) P := forall n a, n<s%s -> a < max_label -> StateLabelMap.In (n,a) s%d \/ P n a.
  
  Instance transitive_extends: Transitive extends.
  Proof.
    intros s s' s'' Hs Hs'. destruct Hs. destruct Hs'. constructor; simpl; auto. 
    rewrite <- e_next1. assumption.
  Qed.
  Lemma reflexive_extends: forall s, invariant s -> extends s s.
  Proof.
    intros s Hs. constructor; auto. reflexivity.
  Qed.

  (** the following lemma corresponds to the termination of the
     algorithm: iterating 2^n times is enough to reach all possible
     subsets *)
  Lemma store_size_bound: forall s, invariant s -> (nat_of_state s%s <= power size)%nat.
  Proof.
    intros s Hs. 
    rewrite <- (i_table_size Hs).
    rewrite <- cardinal_domain.
    apply card_pset.
    intros p Hp. 
     rewrite domain_spec in Hp. rewrite id_num. 
     destruct Hp. eapply Hs. eassumption.
  Qed.

  (** heart of the proof : specification of [steps] *)
  Lemma steps_correct: forall i (s: Store) p np, 
    (power size - s%s < i)%nat ->
    invariant s -> 
    StateSetMap.MapsTo p np s%t ->
    extends s (steps i s p np) /\
    forall P, defined s (fun n a => P n a \/ n=np) -> defined (steps i s p np) P.
  Proof. 
    induction i; intros s p np Hsize H Hp; simpl.
     omega_false.
     cut (forall a: num, extends s (fold_labels (step' (steps i) p np) a s) /\
       forall P, defined s (fun n b => P n b \/ n = np /\ b < a) ->
         defined (fold_labels (step' (steps i) p np) a s) P).
     intro G. split. eapply G. 
     intros P HP. eapply G. intros n b Hn Hb. specialize (HP _ _ Hn Hb). tauto.

     intro a. revert s Hsize H Hp. induction a using num_peano_rec; intros [[t d] n] Hsize H Hp.
      rewrite fold_num_O. split.
       apply reflexive_extends. assumption.
       intros P HP m b Hm Hb. specialize (HP m b Hm Hb). intuition auto. num_omega_false.
      rewrite fold_num_S. simpl. StateSetMapProps.find_analyse.
       (* existing state *)
       assert (H': invariant (t, StateLabelMap.add (np, a) x d, n)).
         constructor; try apply H. 
          intros nq b nq'. simpl. StateLabelMapProps.map_iff. intuition subst.
           apply StateLabel.P.reflect in H1. injection H1; intros; subst; clear H1.
           exists p; auto with map.
          destruct (i_delta H H3) as [q ?]. exists q; auto with map.
       split.
       rewrite <- (fun s Hsize Hs Hn => proj1 (IHa s Hsize Hs Hn)); simpl; auto with map. 
        constructor; auto with map. reflexivity.
        intros P HP. eapply IHa; simpl; auto with map. 
        intros m' b Hm Hb. specialize (HP _ b Hm Hb). simpl in *.
        intuition subst; auto with map. destruct (eq_spec a b). subst. auto with map. num_omega. 

       (* new state *)
       set (s' := (StateSetMap.add (delta_set a p) n t, StateLabelMap.add (np: NumOTA.t, a) n d, S n)).
       assert (H': invariant s').
         constructor; simpl.
          intros q nq. StateSetMapProps.map_iff. intuition subst.
           intros x Hx. rewrite <- H1 in Hx. eapply bounded_delta_set, Hx.  
           num_omega.
           apply (i_table_wf H H3).
           specialize (i_table_wf H H3). simpl. num_omega.
          intros q q' nq. StateSetMapProps.map_iff. intuition subst. 
           StateSetProps.setdec.
           exfalso. specialize (i_table_wf H H5). simpl. num_omega.
           exfalso. specialize (i_table_wf H H4). simpl. num_omega.
           apply (i_table_inj H H4 H5).
          intros m Hm. destruct (eq_num_dec m n). subst.
           eauto with map.
           destruct (@i_table_surj _ H m) as [q ?]. simpl. num_omega. exists q.
            apply StateSetMap.add_2; trivial. intro F. rewrite <- F in H1. elim H0. exists m; assumption.
          erewrite StateSetMapProps.cardinal_2; eauto. 
           apply i_table_size in H. simpl in H. rewrite H. num_omega.
           intro; reflexivity.
          intros nq b nq'. StateLabelMapProps.map_iff. intuition subst.
           apply StateLabel.P.reflect in H1. injection H1; intros; subst; clear H1.
            exists p; auto with map.
            apply StateSetMap.add_2; trivial. intro F. rewrite F in H0. elim H0. exists nq; assumption.
           destruct (i_delta H H3) as [q ?]. exists q.
            apply StateSetMap.add_2; trivial. intro F. rewrite F in H0. elim H0. exists nq; assumption.
            apply StateSetMap.add_2; trivial. intro F. rewrite F in H0. elim H0. exists nq'; assumption.

       specialize (IHi s' (delta_set a p) n). 
       simpl in IHi. destruct IHi as [IHi1 IHi2]; auto with map.
        clear - Hsize H Hp H0 H'. subst s'. simpl in *.
        apply store_size_bound in H'. simpl in *. pose proof (power_positive size). num_omega.

       specialize (IHa (steps i s' (delta_set a p) n)). 
       simpl in IHa. destruct IHa as [IHa1 IHa2].
        clear IHi2. subst s'. apply e_next in IHi1. simpl in *. num_omega.
        apply IHi1.
        apply IHi1. simpl.
         apply StateSetMap.add_2; trivial. intro F. rewrite F in H0. elim H0. exists np. assumption.
         
       split.
        subst s'.
        rewrite <- IHa1. rewrite <- IHi1. 
        constructor; simpl; auto.  
         intros q nq Hq. 
          apply StateSetMap.add_2; trivial. intro F. rewrite <- F in Hq. elim H0. exists nq. assumption.
         num_omega.

        intros P HP. apply IHa2. apply IHi2. unfold s' in *. clear - Hp HP. 
        intros m b Hm Hb. simpl in *.
        destruct (eq_num_dec m n). subst. auto.
        destruct (HP m b) as [[y ?]|[ ?|[? ?]]]; subst; simpl in *; auto with map. num_omega. 
         clear - H. eauto with map.
         destruct (eq_spec a b). subst. auto with map. num_omega. 
  Qed. 

  (** the initial store satisfies the invariant *)
  Lemma invariant_initial_store: invariant initial_store.
  Proof.
    unfold initial_store. constructor; simpl; intros.
     revert H. StateSetMapProps.map_iff. intuition subst; try reflexivity.
      intros x Hx. rewrite <- H in Hx. apply (NFA.bounded_initiaux HA Hx).
     StateSetMapProps.find_tac; StateSetProps.setdec.
     exists initiaux. replace i with (state_of_nat O). auto with map. 
      change 2%positive with (state_of_nat 1) in H. num_omega.
     reflexivity.
     revert H. StateLabelMapProps.map_iff. tauto. 
  Qed.

  (** therefore, the constructed store extends the initial one, and is completely defined *)
  Lemma build_store_correct: 
    extends initial_store build_store 
    /\ forall n a, n<build_store%s -> a < max_label -> StateLabelMap.In (n,a) build_store%d.
  Proof.
    rewrite build_store_spec.
    destruct (@steps_correct (power size) initial_store initiaux 0) as [H H'].
     simpl. pose proof (power_positive size). change 2%positive with (state_of_nat 1). num_omega. 
     apply invariant_initial_store.
     simpl. auto with map.
    split. apply H.
    intros n a Hn Ha. destruct (fun H => H' (fun _ _ => False) H n a Hn Ha); try tauto.
    intros m b Hm _. simpl in Hm. right. right. change 2%positive with (state_of_nat 1) in Hm. num_omega. 
  Qed.

  (** in particular, the constructed store satisfies the invariant *)
  Lemma invariant_build_store: invariant build_store.
  Proof. apply build_store_correct. Qed.


  (** we define notations for the three projections *)
  Notation table := (build_store%t).
  Notation size' := (build_store%s).
  Notation d := (build_store%d).

  (** rho is the predicate that associates states of the DFA to the sets of reachable states from the NFA *)
  Notation rho p i := (StateSetMap.MapsTo p i table).

  (** theta is the converse function: it associates a set of states to each state of the DFA *)
  Definition theta i := 
    StateSetMap.fold (fun p np acc => if eq_state_bool i np then p else acc) table StateSet.empty.

  (** specification of theta, for valid states *)
  Lemma rho_theta i: i<size' -> rho (theta i) i.
  Proof.
    intro Hi. unfold theta. generalize (i_table_surj invariant_build_store Hi). clear. 
    generalize table. intro t. 
    refine (StateSetMapProps.fold_rec_bis 
      (P := fun t acc => (exists p : StateSetMap.key, StateSetMap.MapsTo p i t) -> StateSetMap.MapsTo acc i t)
    _ _ _). intros ? ? ? H. setoid_rewrite H. tauto.
    intros [? ?]. apply StateSetMap.empty_1 in H. elim H.
    intros p j q t' Hp Hp' IH [r Hr].
    num_analyse. subst. auto with map.
    StateSetMapProps.find_tac. right. apply apply in IH.
    split; auto. intro F. elim Hp'. rewrite F. eauto with map. eauto. 
  Qed.

  (** rho is injective (it admits theta as an inverse function) *)
  Lemma theta_rho: forall p i, rho p i -> StateSet.Equal (theta i) p.
  Proof.
    intros p i Hpi. assert (Hi := i_table_wf invariant_build_store Hpi).
    apply proj2, rho_theta in Hi. eapply i_table_inj; eauto. apply invariant_build_store. 
  Qed.

  (** sets build via theta are bounded, and theta is empty out of the bounds *)
  Lemma theta_below: forall u i, StateSet.In u (theta i) -> i < size' /\ u < size.
  Proof.
    intros u i. unfold theta.
    apply StateSetMapProps.fold_rec_nodep.
     StateSetProps.setdec.
     intros p j q Hpj IH.
     num_analyse; auto. 
     subst. split.
      eapply invariant_build_store, Hpj.
      apply invariant_build_store in Hpj. apply Hpj. assumption. 
  Qed.

  (** specification of the [delta_set] function *)
  Lemma in_delta_set: forall j p b, 
    StateSet.In j (delta_set b p) <-> 
    exists k, StateSet.In k p /\ StateSet.In j (delta b k).
  Proof.
    unfold delta_set; split.
     apply StateSetProps.Props.fold_rec_nodep. StateSetProps.setdec.
     intros i a Hip IH.
     StateSetProps.set_iff. intros [Hi|Hi]; eauto.
   
     intros [i [Hip Hj]]. revert Hip.
     apply (StateSetProps.Props.fold_rec_bis (P:=fun p a => StateSet.In i p -> StateSet.In j a)); 
     StateSetProps.setdec.
  Qed.

  (** [theta] and [delta'] commute *)
  Lemma theta_delta': forall a i, a < max_label -> i < size' -> 
    StateSet.eq (theta (delta' d a i)) (delta_set a (theta i)).
  Proof.
    intros a i Ha Hi x. rewrite in_delta_set. 
    unfold delta'. StateLabelMapProps.find_analyse. rename H into Hx.
     apply invariant_build_store in Hx as [pi Hpi Hix].
     rewrite (theta_rho Hix). 
     rewrite in_delta_set.
     setoid_rewrite <- (theta_rho Hpi).
     reflexivity.

     elim H. destruct (proj2 build_store_correct i a) as [di Hdi]; auto. eauto with map.
  Qed.


  (** we need this lemma to use the [StateSetProps.exists_iff] from the FSet library *)
  Lemma final_compat: SetoidList.compat_bool NumSet.E.eq (fun s => StateSet.mem s finaux).
  Proof.  intros x y H. rewrite H. reflexivity. Qed.
  Local Hint Resolve final_compat : core.

      
  (** two auxiliary lemmas about [table_finals], to obtain the characterisation [mem_table_finals] below *)
  Lemma table_finals_correct: 
    forall i, StateSet.In i (table_finals table) -> 
      exists2 u, StateSet.In u (theta i) & StateSet.In u finaux.
  Proof.
    intros i. unfold table_finals.
    apply StateSetMapProps.fold_rec_nodep. StateSetProps.setdec.
    intros p j a Hpj IH H.
    case_eq (StateSet.exists_ (fun s => StateSet.mem s finaux) p); intro He; rewrite He in H. 2: auto.
    revert H. StateSetProps.set_iff. intros [H|H]; auto.
     psubst. clear IH. 
     rewrite <- StateSetProps.exists_iff in He by trivial. destruct He as [k [Hk Hk']].
     exists k; auto. rewrite (theta_rho Hpj). trivial.
  Qed.

  Lemma table_finals_complete:
    forall u p i, StateSet.In u finaux -> rho p i -> StateSet.In u p -> StateSet.In i (table_finals table).
  Proof.
    intros u p i Hu Hpi Hi. revert Hpi. 
    refine (StateSetMapProps.fold_rec_bis (P:=fun t acc => StateSetMap.MapsTo p i t -> StateSet.In i acc) _ _ _).
     intros ? ? ? H. setoid_rewrite H. tauto.

     StateSetMapProps.map_iff. tauto.

     intros q j q' t Hqj Hq IH. 
     StateSetMapProps.map_iff. intros [[Hqp ->]|[Hqp Hpi]].
      replace (StateSet.exists_ (fun s : StateSet.elt => StateSet.mem s finaux) q) with true. auto with set.
      symmetry. rewrite <- StateSetProps.exists_iff by trivial. exists u.
       rewrite Hqp. StateSetProps.mem_prop. auto. 
      apply IH in Hpi. clear IH.
      case StateSet.exists_; auto with set.
  Qed.

  (** specification of [table_finals] *)
  Lemma mem_table_finals: forall i, 
    StateSet.mem i (table_finals table) = StateSet.exists_ (fun x => StateSet.mem x finaux) (theta i).
  Proof.
    intros i. rewrite bool_prop_iff. 
    rewrite <- StateSetProps.exists_iff by trivial. StateSetProps.mem_prop.
    split; intro H. 
     apply table_finals_correct in H as [u Hu Hu']. exists u. split; auto. StateSetProps.mem_prop. trivial.
     destruct H as [u [H H']]. StateSetProps.mem_prop. eapply table_finals_complete.
      eassumption.
      apply rho_theta; trivial. eapply theta_below, H. 
      assumption.
  Qed.

  (** the construted DFA has at least one state *)
  Lemma positive_size: 0 < size'.
  Proof.
    assert (H:=build_store_correct). eapply proj1, e_next in H. simpl in H.
    change 2%positive with (state_of_nat 1) in H. num_omega.
  Qed.

  (** its transitions are bounded *)
  Lemma delta'_below: forall a i, delta' d a i < size'.
  Proof.
    intros a i. unfold delta'. StateLabelMapProps.find_analyse. 
     apply (i_delta invariant_build_store) in H as [px _ Hx]. apply (i_table_wf invariant_build_store Hx).
     exact positive_size.
  Qed.
    

  (** the constructed DFA is bounded (requirement of DFA_Merge / DFA_Equiv) *)
  Lemma bounded: DFA.bounded NFA_to_DFA.
  Proof.
    pose proof delta'_below.
    pose proof positive_size.
    assert (Ht:= table_finals_correct).
    assert (Ht':= theta_below).
    unfold NFA_to_DFA. destruct build_store as [[t d] n]; simpl in *.
    constructor; simpl; auto.
     intros i Hi. apply Ht in Hi as [? Hi _]. eapply Ht', Hi. 
  Qed.

  (** the state 1 points to the set of initial states *)
  Lemma theta_0: StateSet.eq (theta (state_of_nat 0)) (initiaux).
  Proof.
    apply theta_rho. apply build_store_correct. simpl; auto with map.
  Qed.

  (** Final theorem : correctness of the algorithm, the constructed DFA evaluates as the original NFA *)
  Theorem correct: DFA.eval NFA_to_DFA == NFA.eval A.
  Proof. 
    pose proof positive_size as Hpositive_size.
    pose proof theta_below as Htheta_below.
    pose proof delta'_below as Hdelta'_below.
    pose proof theta_delta' as Htheta_delta'.
    pose proof mem_table_finals as Hmem_table_finals.
    unfold NFA_to_DFA. destruct build_store as [[t d] n]. Opaque equal. simpl in *. Transparent equal.

    apply mx_to_scal_compat. apply right_filter with
    (mx_bool tt (nat_of_state n) size (fun s j => StateSet.mem j (theta (state_of_nat s))): KMX _ _).

    (** u *)
    Opaque dot one zero equal. simpl. Transparent dot one zero equal.
    rewrite mx_point_one_left by num_omega. 
    mx_intros i j Hi Hj. Opaque eq_nat_bool. simpl. bool_simpl. simpl. fold_regex. Transparent eq_nat_bool. 
    rewrite theta_0. reflexivity. 

    (** m *)
    mx_intros i j Hi Hj; simpl. fold_regex. 
    unfold labelling. 
    setoid_rewrite sum_distr_left. rewrite sum_inversion. 
    setoid_rewrite sum_distr_right. rewrite sum_inversion. 
    apply sum_compat. intros a Ha.
    setoid_rewrite dot_xif_zero. simpl; fold_regex.
    setoid_rewrite dot_neutral_left.
    setoid_rewrite dot_neutral_right.
    apply leq_antisym; apply compare_sum_xif_zero; intros u Hu; bool_connectors; intros [Hu' Hu'']; simpl in *.
     exists (nat_of_state (delta' d a i)); auto. specialize (Hdelta'_below a i). num_omega. 
     bool_connectors. num_prop. rewrite id_num. split; trivial.
     rewrite Htheta_delta' by num_omega.
     StateSetProps.mem_prop. apply <- in_delta_set. exists (state_of_nat u); auto.

     num_prop. rewrite Hu' in Hu''. clear u Hu Hu'. simpl in Hi. 
     rewrite Htheta_delta', <- StateSetProps.mem_iff in Hu'' by num_omega.
     apply -> in_delta_set in Hu''. destruct Hu'' as [k [? ?]].
     exists (nat_of_state k). 
      apply Htheta_below, proj2 in H. clear - H. num_omega.
      rewrite id_num. bool_connectors. StateSetProps.mem_prop. rewrite id_num. auto. 

    (** v *)
    mx_intros i j Hi Hj; simpl in *. fold_regex.  
    setoid_rewrite dot_xif_zero.
    rewrite Hmem_table_finals.
    case_eq (StateSet.exists_ (fun x => StateSet.mem x finaux) (theta (statesetelt_of_nat i))); 
     intro H; simpl; fold_regex.

     rewrite <- StateSetProps.exists_iff in H by trivial. destruct H as [u [Hu Hu']].
     rewrite (sum_fixed_xif_zero (v:=nat_of_state u)). auto with algebra. 
      StateSetProps.mem_prop. apply HA in Hu'. apply Htheta_below, proj2 in Hu. num_omega.
     rewrite id_num. bool_connectors. StateSetProps.mem_prop. auto.  

     apply sum_zero. intros m Hm. apply xif_false. simpl.
     rewrite <- H. rewrite bool_prop_iff. bool_connectors. 
     rewrite H. StateSetProps.mem_prop. intuition; try discriminate.
     rewrite <- H. rewrite <- StateSetProps.exists_iff by trivial. eexists; StateSetProps.mem_prop; eauto. 
  Qed.

End S.

(** We finally prove that the algorithm preserves the max_label field *)
Lemma preserve_max_label: forall A, DFA.max_label (NFA_to_DFA A) = NFA.max_label A.
Proof.
  intros. unfold NFA_to_DFA. destruct (build_store A) as [[? ?] ?]. reflexivity.
Qed.

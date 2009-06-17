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
Require Import Monoid.
Require Import SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.
Require Import BoolAlg.
Require Import FreeKleeneAlg.

Require Import DKA_Annexe.

Set Implicit Arguments.
Unset Printing Implicit Defensive.


Lemma alg_eval `{KleeneAlgebra} B B' A C: forall (x: X B' B) (u: X A B) m v u' m' (v': X B' C),
  u'*x == u ->
  m'*x == x*m ->
  v' == x*v ->
  u'*m'#*v' == u*m#*v.
Proof.
  intros.
  rewrite H2. 
  rewrite <- H0.
  monoid_rewrite <- (comm_iter_left H1).
  monoid_reflexivity.
Qed.


Section Protect.

Opaque equal dot plus one zero star.

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

Import Det.

Section Termination.

  Variable A: NFA.
  Notation size := (N_size A).

  Fixpoint power n := (match n with O => 1 | S n => 2*power n end)%nat.

  Lemma below0_empty p: below p 0 -> StateSet.Empty p.
  Proof.
    intros p H.
    rewrite StateSetProp.elements_Empty.
    remember (StateSet.elements p) as l. destruct l as [|i l]. trivial.
    lpose (H i) as H'. 
    rewrite StateSetFact.elements_iff. rewrite <- Heql. auto.  
    inversion H'.
  Qed.

  Definition statesetset_map f t :=
    StateSetSet.fold (fun x acc => StateSetSet.add (f x) acc) t StateSetSet.empty.

  Section sssm.
    Variable t0: StateSetSet.t.
    Variable f: stateset -> stateset.

    Lemma statesetset_map_in p:
      StateSetSet.In p (statesetset_map f t0) -> exists2 q, StateSetSet.In q t0 & StateSet.Equal (f q) p.
    Proof.
      intro p. unfold statesetset_map.
      apply StateSetSetProp.fold_rec_nodep.  statesetset_dec.
      intros q a Hq IH.  StateSetSetFact.set_iff. intros [Hp|Hp]; eauto. 
    Qed.

    Hypothesis Hf: forall p q, StateSetSet.In p t0 -> StateSetSet.In q t0 -> 
      (StateSet.Equal (f p) (f q) <-> StateSet.Equal p q).

    Lemma statesetset_map_cardinal:
      StateSetSet.cardinal (statesetset_map f t0) = StateSetSet.cardinal t0.
    Proof.
      refine (proj2 (StateSetSetProp.fold_rec_bis 
        (P:=fun t a => (forall p, StateSetSet.In p t0 -> (StateSetSet.In (f p) a <-> StateSetSet.In p t)) /\  
          ((forall p, StateSetSet.In p t -> StateSetSet.In p t0) -> StateSetSet.cardinal a = StateSetSet.cardinal t)) _ _ _) _); trivial. 
      intros. setoid_rewrite <- H. trivial. 
      split; trivial. statesetset_dec. 
      intros p a t' Hp Hp' [IH IHc]. split.
      intros q Hq. StateSetSetFact.set_iff. specialize (IH q Hq). rewrite Hf by auto. tauto.  
      intros Ht'.
      rewrite (StateSetSetProp.cardinal_2 (s:=a) (x:=f p)); auto with map. 
      symmetry. rewrite (StateSetSetProp.cardinal_2 (s:=t') (x:=p)); auto with map. 
      symmetry. rewrite IHc; auto. intros q Hq. apply Ht'. statesetset_dec.
      rewrite IH; auto.
    Qed.

  End sssm.

  Lemma card_pset s t: (forall p, StateSetSet.In p t -> below p s) -> StateSetSet.cardinal t <= power s.
  Proof. 
    induction s; intros t H; simpl.
    (* il ne peut y avoir que l'ensemble vide dans la table *)
     destruct (StateSetSetProp.cardinal_0 t) as (l&Hl&Hlt&->).
     setoid_rewrite Hlt in H. clear Hlt.
     destruct l as [|x [| y q]]; simpl; auto with arith. elimtype False.
     inversion_clear Hl. apply H0. left. clear H0 H1.
     lpose (@below0_empty x) as Hx. apply H. left. reflexivity.
     lpose (@below0_empty y) as Hy. apply H. right. left. reflexivity.
     stateset_dec.

    (* il faut partitionner: ceux qui contiennent s et les autres *)
    remember (StateSetSet.partition (fun p => StateSet.mem s p) t) as tt. 
    pose (t0' := statesetset_map (StateSet.remove s) (fst tt)).
    setoid_replace t with (StateSetSet.union (fst tt) (snd tt)).
    rewrite StateSetSetProp'.union_cardinal.
    replace (StateSetSet.cardinal (fst tt)) with (StateSetSet.cardinal t0').
    lpose (IHs (snd tt)) as Ht0'. 2:lpose (IHs t0') as H1. 3: omega.

     rewrite Heqtt. intro p. 
     rewrite (fun f H t => StateSetSet.equal_2 (StateSetSetProp'.partition_filter_2 f H t)).
     rewrite StateSetSetFact.mem_iff.
     rewrite StateSetSetProp'.filter_mem.
     case_eq (StateSetSet.mem p t). 2:(intros; discriminate). simpl. intros Hp Hp'. 
     intros x Hx. destruct (eq_nat_dec x s). rewrite e in Hx. revert Hp'. 
     case_eq (StateSet.mem s p). intros; try discriminate. rewrite <- StateSetFact.not_mem_iff. tauto. 
     rewrite <- StateSetSetFact.mem_iff in Hp. pose (H' := H p Hp x Hx). simpl in H'. omega.
     repeat intro. rewrite H0. trivial.
     repeat intro. rewrite H0. trivial.

     intros p Hp. destruct (statesetset_map_in _ _ Hp) as [q Hq Hq']. revert Hq.
     rewrite Heqtt. 
     rewrite (fun f H t => StateSetSet.equal_2 (StateSetSetProp'.partition_filter_1 f H t)).
     rewrite StateSetSetFact.mem_iff.
     rewrite StateSetSetProp'.filter_mem.
     case_eq (StateSetSet.mem q t). 2:(intros; discriminate). simpl. intros Hq Hq''. 
     intros x Hx. destruct (eq_nat_dec x s). rewrite e in Hx. stateset_dec. 
     rewrite <- StateSetSetFact.mem_iff in Hq. 
     rewrite <- StateSetFact.mem_iff in Hq''. 
     specialize (H q Hq). lpose (H x) as H'. stateset_dec. omega.
     repeat intro. rewrite H0. trivial.
     repeat intro. rewrite H0. trivial.

     apply statesetset_map_cardinal. 
     rewrite Heqtt. intros p q.
     rewrite (fun f H t => StateSetSet.equal_2 (StateSetSetProp'.partition_filter_1 f H t)).
     setoid_rewrite StateSetSetFact.mem_iff.
     setoid_rewrite StateSetSetProp'.filter_mem. 
     case (StateSetSet.mem p t). 2: (intros; discriminate).
     case (StateSetSet.mem q t). 2: (intros; discriminate). simpl.
     setoid_rewrite <- StateSetFact.mem_iff. 
     (* BUG de fsetdec ? devrait passer, non ? *)
     (*      stateset_dec. *)
     split; intro; stateset_dec. (* long... *)
     repeat intro. rewrite H0. trivial.
     repeat intro. rewrite H0. trivial.
     repeat intro. rewrite H0. trivial.

    intro x. rewrite Heqtt. 
    rewrite (fun f H t => StateSetSet.equal_2 (StateSetSetProp'.partition_filter_1 f H t)).
    rewrite (fun f H t => StateSetSet.equal_2 (StateSetSetProp'.partition_filter_2 f H t)).
    setoid_rewrite StateSetSetProp'.filter_mem. case (StateSet.mem s x); case (StateSetSet.mem x t); trivial. 
    repeat intro. rewrite H0. trivial.
    repeat intro. rewrite H0. trivial.
    repeat intro. rewrite H0. trivial.
    repeat intro. rewrite H0. trivial.
    
    rewrite Heqtt.
    rewrite (fun f H t => StateSetSet.equal_2 (StateSetSetProp'.partition_filter_1 f H t)).
    rewrite (fun f H t => StateSetSet.equal_2 (StateSetSetProp'.partition_filter_2 f H t)).
    rewrite StateSetSetProp'.union_filter.
    intro u. setoid_rewrite StateSetSetFact.mem_iff.
    rewrite StateSetSetProp'.filter_mem.
    rewrite andb_comm. case (StateSet.mem s u); simpl; tauto.
    repeat intro. rewrite H0. trivial.
    repeat intro. rewrite H0. trivial.
    repeat intro. rewrite H0. trivial.
    repeat intro. rewrite H0. trivial.
    repeat intro. rewrite H0. trivial.
  Qed.
  
  Definition domain t := StateSetMap.fold (fun p (np: nat) a => StateSetSet.add p a) t StateSetSet.empty.
  
  Lemma cardinal_domain t: StateSetSet.cardinal (domain t) = StateSetMap.cardinal t.
  Proof.
    intro t.
    refine (proj2 (StateSetMapProp.fold_rec_bis 
      (P:=fun t a => (forall p, StateSetSet.In p a <-> StateSetMap.In p t) /\  
                     StateSetSet.cardinal a = StateSetMap.cardinal t) _ _ _)). 
    intros. setoid_rewrite <- H. trivial. 
    split; trivial. split. statesetset_dec. StateSetMapFact.map_iff. tauto. 
    intros p np a t' Hp Hp' [IH IHc]. split.
    intro q. StateSetSetFact.set_iff. StateSetMapFact.map_iff. specialize (IH q). tauto.
    rewrite (StateSetMapProp.cardinal_2 Hp') by (intro; reflexivity). 
    rewrite (StateSetSetProp.cardinal_2 (s:=a) (x:=p)). congruence. rewrite IH; trivial.
    auto with map.
  Qed.  

  Definition valid_elts s t := 
    StateSetMap.cardinal 
      (@StateSetMapProp.filter_dom nat
        (fun p => StateSet.for_all (fun i => negb (le_lt_dec s i) (* i<s *)) p)
        t).

  Lemma bbool_view b1 b2: (b1=true <-> b2=true) -> b1=b2.
  Proof. intros [|] [|]; intuition. Qed.

  Lemma for_all_compat f: Proper (StateSet.Equal ==> @eq bool) (StateSet.for_all f).
  Proof. 
    intros f x y H.
    apply bbool_view.
    rewrite <- 2StateSetFact.for_all_iff by (repeat intro; subst; trivial). 
    (split; intros Ht i); [rewrite <- H| rewrite H]; auto.  
  Qed.

  Lemma valid_add s: forall p np table, 
    StateSetMap.find p table = None -> 
    below p s ->
    valid_elts s (StateSetMap.add p np table) = S (valid_elts s table).
  Proof.
    intros. unfold valid_elts. unfold StateSetMapProp.filter_dom.
    apply StateSetMapProp.cardinal_2 with p np.
     apply <- StateSetMapFact.not_find_in_iff.
     match goal with |- ?x = None => case_eq x end; trivial. intros n Hn. 
     rewrite <- StateSetMapFact.find_mapsto_iff in Hn.
     rewrite -> StateSetMapProp.filter_iff in Hn. apply proj1 in Hn.
     rewrite -> StateSetMapFact.find_mapsto_iff, H in Hn. discriminate.
     repeat intro. subst. apply for_all_compat. assumption.

     intro q.
     match goal with |- ?x = _ => case_eq x; [intros r Hr|intro Hr]; symmetry end. 
      rewrite <- StateSetMapFact.find_mapsto_iff in Hr.
      rewrite <- StateSetMapFact.find_mapsto_iff. 
      rewrite StateSetMapProp.filter_iff in Hr. destruct Hr as [Hr Hr'].
      rewrite StateSetMapFact.add_mapsto_iff in Hr. intuition. 
      subst. auto with map.
      apply StateSetMap.add_2; trivial.
      rewrite StateSetMapProp.filter_iff. auto. 
      repeat intro. subst. apply for_all_compat. assumption. 
      repeat intro. subst. apply for_all_compat. assumption. 
      
      rewrite <- StateSetMapFact.not_find_in_iff in Hr.
      rewrite <- StateSetMapFact.not_find_in_iff.
      StateSetMapFact.map_iff. intros [Hr'|[nq Hr']]; apply Hr; clear Hr.
       rewrite <- Hr'. clear Hr' q. exists np. rewrite StateSetMapProp.filter_iff.
       split. apply StateSetMap.add_1; trivial. 
       rewrite <- StateSetFact.for_all_iff by (repeat intro; subst; trivial). 
       intros x Hx. destruct (le_lt_dec s x); trivial. simpl. pose (H':= H0 x Hx). omega_false.
       repeat intro. subst. apply for_all_compat. assumption. 

       exists nq.
       rewrite StateSetMapProp.filter_iff in Hr'. destruct Hr' as [Hq Hr'].
       rewrite StateSetMapProp.filter_iff. split; auto.
       apply StateSetMap.add_2; trivial. 
       intro Hpq. rewrite <- Hpq in Hq. 
       rewrite StateSetMapFact.find_mapsto_iff, H in Hq. discriminate.
       repeat intro. subst. apply for_all_compat. assumption. 
       repeat intro. subst. apply for_all_compat. assumption. 
  Qed. 


  Lemma valid_size: forall s table, valid_elts s table <= power s.
  Proof.
    intros. unfold valid_elts.
    rewrite <- cardinal_domain.
    apply card_pset. intro p. 
    unfold domain.
    apply StateSetMapProp.fold_rec_nodep. statesetset_dec. 
    intros q nq a Hq IH.
    StateSetSetFact.set_iff. intros [H|H]. 2: auto.
    clear IH. unfold StateSetMapProp.filter_dom in Hq. rewrite StateSetMapProp.filter_iff in Hq.
    apply proj2 in Hq. rewrite <- StateSetFact.for_all_iff in Hq.
    intros x Hx. rewrite <- H in Hx. generalize (Hq x Hx). destruct (le_lt_dec s x); trivial. intro. discriminate. 
    repeat intro. subst. trivial.
    repeat intro. subst. apply for_all_compat. assumption. 
  Qed.

  Lemma delta_set_below: NFA_wf A -> forall p b,(* below p size ->*) b<N_max_label A -> below (delta_set A p b) size.
  Proof.
    intros.
    unfold delta_set.
    apply StateSetProp.fold_rec_nodep.
    intros x Hx. stateset_dec.
    intros x a Hx IH y Hy. apply StateSet.union_1 in Hy as [Hy|Hy].
    eapply (proj2 (proj2 H)); eauto.
    apply IH. assumption.
  Qed.

  (* l'énoncé ne doit pas bouger : requis par DecideKleeneAlgebra *)
  Theorem Termination: Det.Termination A.
  Proof.
    intros HA.
    eapply (lexico_incl_wf 
      (fun nttd: NTTD => 
        let '(_,table,todo,_) := nttd in 
          (power size - valid_elts size table, List.length todo))); try apply lt_wf.
    intros nttd' nttd H. inversion_clear H. clear nttd nttd'.
    destruct ntt as [[next' table'] todo']. simpl.
    revert next table todo H0. rename dp into dp'. generalize (StateMap.empty nat) as dp.
    unfold explore_labels. 
    generalize (lt_n_Sn (N_max_label A)). pattern (N_max_label A) at -2.
    induction (N_max_label A) as [| b IHb]; intros Hb dp next table todo H.
     inversion_clear H.
     right. simpl. trivial with arith. 
     
     simpl in H.
     case_eq (StateSetMap.find (delta_set A p b) table).
      intros nq Hnq. rewrite Hnq in H. apply IHb in H; auto with arith. 
      intro Ht. rewrite Ht in H. apply IHb in H; auto with arith. clear IHb.
      left.
      lpose (@valid_add size _ next _ Ht) as Hs. apply delta_set_below; auto with arith.
      inversion H; subst; clear H.
       omega.
       pose proof (valid_size size (StateSetMap.add (delta_set A p b) next table)). omega.
  Qed.

End Termination.

Section Correction.

  Variable A: NFA.
  Hypothesis HA: NFA_wf A.

  Notation explore := (explore (@Termination _) HA).

  Notation size := (N_size A).
  Notation delta := (N_delta A).
  Notation initiaux := (N_initiaux A).
  Notation finaux := (N_finaux A).
  Notation max_label := (N_max_label A).


  (* d contient la transition np -a-> nq *)
  Definition MapsTo2 (np: state) (a: label) (nq: state) (d: Delta) := 
    (exists2 dp, StateMap.MapsTo np dp d & LabelMap.MapsTo a nq dp).
  
  (* égalité sur les listes (SetoiList.InA inliné) *)
  Inductive In_list: Todo -> list Todo -> Prop :=
  | In_head: forall p p' np q, StateSet.Equal p p' -> In_list (p,np) ((p',np)::q)
  | In_tail: forall pnp x q, In_list pnp q -> In_list pnp (x::q).


  (* invariant de la fonction explore *)
  Record invariant_explore next table todo d := {
    (* la table ne pointe que vers des etats valides *)
    ie_table_wf: forall s i, StateSetMap.MapsTo s i table -> i < next;
    (* la table ne part que d'états valides *)
    ie_table_wf': forall s i, StateSetMap.MapsTo s i table -> below s size;
    (* la table est injective *)
    ie_table_inj: forall s t i, StateSetMap.MapsTo s i table -> StateSetMap.MapsTo t i table -> StateSet.Equal s t;
    (* la table est surjective (up to next) *)
    ie_table_surj: forall i, i<next -> { s | StateSetMap.MapsTo s i table };
    (* la liste todo est contenue dans la table *)
    ie_todo_table: forall p np, In_list (p,np) todo -> StateSetMap.MapsTo p np table;
    (* tout etat de la table, mais pas dans todo, admet ses successeurs dans delta *)
    ie_table_delta_set: forall p a np, a < max_label -> 
      StateSetMap.MapsTo p np table -> 
         In_list (p,np) todo 
      \/ exists2 nq, MapsTo2 np a nq d & StateSetMap.MapsTo (delta_set A p a) nq table;
    (* toute transition de d correspond a une transition de delta_set
       (et en particulier, tous les points de delta sont dans la table) *)
    ie_delta: forall np a nq, MapsTo2 np a nq d -> 
      exists2 p, StateSetMap.MapsTo p np table & StateSetMap.MapsTo (delta_set A p a) nq table
  }.

  Definition invariant_explore' nttd :=
    let '(next,table,todo,d) := nttd in invariant_explore next table todo d.

  (* invariant de la fonction explore_labels *)
  Record invariant_explore_labels p np dp next table todo d b := {
    (* l'invariant externe est satisfait *)
    iel_ie: invariant_explore next table ((p,np)::todo) d;
    (* p admet tous ses successeurs par des labels >= b dans dp *)
    iel_dp_delta_set_table: forall a, b <= a -> a < max_label -> 
      exists2 nq, LabelMap.MapsTo a nq dp & StateSetMap.MapsTo (delta_set A p a) nq table;
    (* toute transition de dp correspond a une transition de delta_set 
       (et en particulier, tous les points de dp sont dans la table) *)
    iel_dp: forall a nq, LabelMap.MapsTo a nq dp -> StateSetMap.MapsTo (delta_set A p a) nq table
  }.

  Definition invariant_explore_labels' p np nttdp d :=
    let '(next,table,todo,dp) := nttdp in invariant_explore_labels p np dp next table todo d.

  Definition delta_set' a q := delta_set A q a.

  Instance delta_set_compat a: Proper (StateSet.Equal ==> StateSet.Equal) (delta_set' a).
  Proof.
    intros a s t H. unfold delta_set', delta_set.
    rewrite StateSetOrdProp.fold_equal. reflexivity. 3: assumption. 
    constructor; repeat intro; stateset_dec.
    intros x x' y y' <- Hy. rewrite Hy. reflexivity. 
  Qed.  


  Lemma In_list_2cons: forall p np x p' np' q,
    In_list (p,np) (x::(p',np')::q) <-> StateSet.Equal p p' /\ np=np' \/ In_list (p,np) (x::q).
  Proof.
    intros p np [x nx] p' np' q; split; intro H.
    inversion_clear H.
     right. left. trivial.
     inversion_clear H0; auto. 
     right. right. trivial.
    destruct H as [[H ->] | H].
     right. left. trivial.
    inversion_clear H.
     left. trivial.
     right. right. trivial.
  Qed.

  Lemma delta_set_wf: forall p a, below p size -> a<max_label -> below (delta_set A p a) size.
  Proof.
    intros p a Hp Ha i.
    unfold delta_set.
    apply StateSetProp.fold_rec_nodep.
    stateset_dec.
    intros j q Hjq Hq.
    StateSetFact.set_iff. intros [H | H]; auto.
    eapply (proj2 (proj2 HA)); eauto. 
  Qed.

  Lemma explore_labels_invariant: forall p np nttdp d,
    invariant_explore_labels' p np nttdp d max_label ->
    invariant_explore_labels' p np (explore_labels A p np nttdp) d O.
  Proof.
    unfold explore_labels. fold max_label. intros p np. generalize (lt_n_Sn max_label).
    pattern max_label at -2. induction max_label as [|b IHb]; simpl; intros Hb [[[next table] todo] dp] d IH. 
     assumption.

     (* cas inductif de explore_labels *)
     remember (insert_table (next,table,todo) (delta_set A p b)) as it.
     destruct it as [nq [[next' table'] todo']].
     apply IHb. omega.
     unfold insert_table in Heqit.
     remember (StateSetMap.find (delta_set A p b) table) as snq. destruct snq as [nq'|].
      (* l'etat existait *)
      inversion Heqit. subst. clear Heqit.
      symmetry in Heqsnq. rewrite <- StateSetMapFact.find_mapsto_iff in Heqsnq.
      destruct IH. destruct iel_ie0. constructor. constructor; intuition.
       intros a Ha Ha'.
       destruct (eq_nat_dec a b). subst.
       exists nq'; auto. apply StateMap.add_1; trivial.
       destruct (iel_dp_delta_set_table0 a) as [nq Hnq Hnq']; trivial. omega.
       exists nq; auto. apply StateMap.add_2; trivial. compute; intro; subst; tauto_false.

       intros a nq Ha.
       rewrite StateMapFact.add_mapsto_iff in Ha. intuition. subst. assumption.

      (* on ajoute un nouvel etat *)
      inversion Heqit. subst. clear Heqit.
      destruct IH. destruct iel_ie0. constructor. constructor.  
       (* table_wf *)
       intros s i H. rewrite StateSetMapFact.add_mapsto_iff in H. intuition. 
       apply ie_table_wf0 in H1. auto with arith. 

       (* table_wf' *)
       intros s i H. rewrite StateSetMapFact.add_mapsto_iff in H. intuition. 
       intros x Hx. rewrite <- H in Hx. revert x Hx. apply delta_set_wf. 
        eapply ie_table_wf'0. apply ie_todo_table0. left. reflexivity.  omega. 
       apply ie_table_wf'0 in H1. trivial.

       (* table_inj *)
       intros s t i Hs Ht. 
       rewrite StateSetMapFact.add_mapsto_iff in Hs. 
       rewrite StateSetMapFact.add_mapsto_iff in Ht. 
       intuition.
        rewrite <- H0. trivial. 
        subst. apply ie_table_wf0 in H3. omega_false.
        subst. apply ie_table_wf0 in H1. omega_false.
        apply ie_table_inj0 with i; trivial.

       (* table_surj *)
       intros i Hi.
       destruct (eq_nat_dec i next). subst.
       exists (delta_set A p b). auto with map.
       destruct (ie_table_surj0 i) as [s Hs]. omega. exists s. apply StateSetMap.add_2; trivial.
       intro H. rewrite H in Heqsnq.
       rewrite StateSetMapFact.find_mapsto_iff, <- Heqsnq in Hs. discriminate.

       (* todo_table *)
       intros q nq Hq. destruct (eq_nat_dec nq next). subst.
        destruct (proj1 (In_list_2cons _ _ _ _ _ _) Hq) as [[H _]|H]; clear Hq. 
        apply StateSetMap.add_1. symmetry in H; trivial.
        apply ie_todo_table0, ie_table_wf0 in H. omega_false.
        destruct (proj1 (In_list_2cons _ _ _ _ _ _) Hq) as [[H Hn]|H]; clear Hq. tauto.
        apply StateSetMap.add_2; auto. 
        intro H'. rewrite H' in Heqsnq. clear H'.
        apply ie_todo_table0 in H. rewrite StateSetMapFact.find_mapsto_iff, <- Heqsnq in H. discriminate.

       (* table_delta_set *)
       intros q a nq Ha Hq.
       rewrite StateSetMapFact.add_mapsto_iff in Hq. intuition. subst.
        left. right. left. symmetry; trivial.
        destruct (ie_table_delta_set0 q a nq Ha H1) as [H|[nq' Hnq' Hnq'']].
        left. apply <- In_list_2cons. auto. 
        right. exists nq'; auto. 
        apply StateSetMap.add_2; auto. 
        intro H'. rewrite H' in Heqsnq. clear H'.
        rewrite StateSetMapFact.find_mapsto_iff, <- Heqsnq in Hnq''. discriminate.

       (* delta *)
       intros nq a nq' Hq.
       destruct (ie_delta0 _ _ _ Hq) as [q Hq' Hq''].
       exists q. 
        apply StateSetMap.add_2; auto. intro H'. rewrite H' in Heqsnq. clear H'.
        rewrite StateSetMapFact.find_mapsto_iff, <- Heqsnq in Hq'. discriminate.
        apply StateSetMap.add_2; auto. intro H'. rewrite H' in Heqsnq. clear H'.
        rewrite StateSetMapFact.find_mapsto_iff, <- Heqsnq in Hq''. discriminate.

       (* dp_delta_set_table *)
       intros a Ha Ha'. destruct (eq_nat_dec b a). subst.
        exists next. apply StateMap.add_1. reflexivity. apply StateSetMap.add_1. reflexivity.
        destruct (iel_dp_delta_set_table0 a) as [nq Hq Hq']; auto with omega.
        exists nq. apply StateMap.add_2; trivial. apply StateSetMap.add_2; trivial. 
        intro H'. rewrite H' in Heqsnq. clear H'.
        rewrite StateSetMapFact.find_mapsto_iff, <- Heqsnq in Hq'. discriminate.

       (* dp *)
       intros a nq Hq.
       rewrite StateMapFact.add_mapsto_iff in Hq. intuition. subst.
        apply StateSetMap.add_1. reflexivity.
        apply iel_dp0 in H1.
        apply StateSetMap.add_2; trivial. 
        intro H'. rewrite H' in Heqsnq. clear H'.
        rewrite StateSetMapFact.find_mapsto_iff, <- Heqsnq in H1. discriminate.
  Qed.


  

  Lemma explore_labels_correct: forall p np dp next table todo delta' ntt',
    explore_labels A p np (next, table, todo, StateMap.empty nat) = (ntt', dp) ->
    invariant_explore  next table ((p,np)::todo) delta' ->
    invariant_explore' (ntt', StateMap.add np dp delta').
  Proof.
    intros until 0; intros H IH.
    pose proof (explore_labels_invariant p np (next,table,todo,StateMap.empty nat) delta') as Hl.
    rewrite H in Hl. clear H. destruct ntt' as [[next' table'] todo']. destruct Hl.

     constructor; trivial.
     intros. omega_false.
     intros a nq H. elim (StateMap.empty_1 H).

     clear IH next table todo. destruct iel_ie0. constructor.
      assumption.
      assumption.
      assumption.
      assumption.
      intros q nq Hq. eapply In_tail in Hq. eauto. 

      (* tout etat admet ses successeurs dans d (a moins d'etre dans todo) *)
      intros r a nr Ha Hr. destruct (eq_nat_dec nr np). subst.
       (* le cas interessant : l'etat considere vient de passer de todo a delta  *)
       destruct (iel_dp_delta_set_table0 a) as [nq Hnq Hnq']; trivial with arith.
       right. exists nq. exists dp; auto with map.
       fold (delta_set' a r). setoid_replace r with p. assumption. 
       eapply ie_table_inj0; eauto. apply ie_todo_table0. left; reflexivity.
       (* les deux autres cas que l'on doit transferer *)
       destruct (ie_table_delta_set0 r a nr Ha Hr) as [H|H].
       inversion_clear H; auto. 
        elim n. eapply StateSetMapFact.MapsTo_fun. apply Hr. 
        rewrite H0. apply ie_todo_table0. left; reflexivity.
       right.
        destruct H as [nr' [dr Hnr1 Hnr2] Hnr3]. exists nr'; trivial.
        exists dr; trivial. apply StateMap.add_2; trivial. compute; intro; subst; tauto_false.

      (* les transitions de d correspondent a des transitions de delta_set *)
      intros nr a nq [dp' Hpq Hpq'].
      rewrite StateMapFact.add_mapsto_iff in Hpq. intuition. subst.
       (* transition de l'etat qu'on vient d'ajouter *)
       exists p; intuition. apply ie_todo_table0. left; reflexivity.
       (* transition d'un autre etat *)
       apply ie_delta0. exists dp'; assumption.
  Qed.

  Lemma explore_invariant: forall nttd,
    invariant_explore' nttd -> 
    invariant_explore' (explore nttd).
  Proof.
    intros.
    functional induction (explore nttd); trivial.
    apply IHn1; clear IHn1.
    eapply explore_labels_correct; eassumption. 
  Qed.
  
  Definition get_table U (nttd: NTT*U) := let '(_,t,_,_) := nttd in t.

  Lemma explore_labels_increase_table p np nttdp: forall q nq, 
    StateSetMap.MapsTo q nq (get_table nttdp) -> StateSetMap.MapsTo q nq (get_table (explore_labels A p np nttdp)).
  Proof.
    intros p np. unfold explore_labels. 
    induction (N_max_label A) as [| b IHb]; simpl; trivial. 
    intros [[[next table] todo] dp] q nq H; simpl.
    apply IHb. clear IHb. 
     case_eq (StateSetMap.find (delta_set A p b) table); simpl in *; trivial.
     intro Hn.
     apply StateSetMap.add_2; trivial.
     intros D. rewrite D in Hn. clear D.
     rewrite StateSetMapFact.find_mapsto_iff, Hn in H. discriminate.
  Qed.

  Lemma explore_increase_table nttd: forall q nq, 
    StateSetMap.MapsTo q nq (get_table nttd) -> StateSetMap.MapsTo q nq (get_table (explore nttd)).
  Proof.
    intros nttd.
    functional induction (explore nttd); trivial.
    intros q nq H. apply IHn1. clear IHn1. simpl in H.
    destruct ntt as [[next' table'] todo']. simpl.
    change table' with (get_table (next',table',todo',dp)).
    unfold NTT in e1. rewrite <- e1. clear e1.
    apply explore_labels_increase_table. assumption.    
  Qed.

  Definition nttd := explore (1%nat, 
    StateSetMap.add initiaux O (StateSetMap.empty _), 
    (initiaux,O)::nil, 
    StateMap.empty _).
  
  Let size' := let '(next,_,_,_) := nttd in next.
  Let table := let '(_,table,_,_) := nttd in table.
  Let deltam := let (_,delta') := nttd in delta'.
  Let delta' := Delta_to_fun deltam.
  Let initial' := 0%nat.
  Let finaux' := finals A table.


  Global Strategy 1010 [Det.explore].
  Lemma nttd_split: nttd = (size',table,nil,deltam).
  Proof.
    remember nttd. destruct n as [[[next t] todo] d].
    replace todo with (@nil Todo). reflexivity.
    revert Heqn. clear. 
    unfold nttd.
    functional induction 
      (explore
        (1%nat, StateSetMap.add initiaux O (StateSetMap.empty nat),
          (initiaux, O) :: nil, StateMap.empty (StateMap.t nat))); trivial. 
    intro H. inversion_clear H. trivial.
  Qed.

  Lemma invariant_nttd: invariant_explore size' table nil deltam.
  Proof.
    fold (invariant_explore' (size',table,nil,deltam)). rewrite <- nttd_split. 
    apply explore_invariant.
    constructor.
     intros s i H. rewrite StateSetMapFact.add_mapsto_iff in H. intuition.
     rewrite StateSetMapFact.empty_mapsto_iff in H1. elim H1.
     
     intros s i H. rewrite StateSetMapFact.add_mapsto_iff in H. intuition.
     intro x. rewrite <- H. apply (proj1 HA). 
     rewrite StateSetMapFact.empty_mapsto_iff in H1. elim H1.

     intros s t i Hs Ht.
     rewrite StateSetMapFact.add_mapsto_iff in Hs. intuition.
     rewrite StateSetMapFact.add_mapsto_iff in Ht. intuition.
      rewrite <- H0; trivial.
      rewrite StateSetMapFact.empty_mapsto_iff in H4. elim H4.
      rewrite StateSetMapFact.empty_mapsto_iff in H1. elim H1.

     intros [|i] Hi. 2:omega_false. eauto with map.

     intros p np H. inversion_clear H.
      apply StateSetMap.add_1. symmetry; trivial.  
      inversion H0.

     intros p a np Ha H.
      rewrite StateSetMapFact.add_mapsto_iff in H. intuition. subst.
      left. left. symmetry; trivial. 
      rewrite StateSetMapFact.empty_mapsto_iff in H1. elim H1.

     intros np a nq [dp H H']. 
      rewrite StateMapFact.empty_mapsto_iff in H. elim H.
  Qed.

  Let rho p i := StateSetMap.MapsTo p i table.

  Definition theta i := 
    match le_lt_dec size' i with
      | left _ => StateSet.empty
      | right H => let (p,_) := ie_table_surj invariant_nttd H in p
    end.

  Definition bX: BMX(size',size) := 
    box (G:=bool_Graph) _ _ (fun s j => StateSet.mem j (theta s)). 
  Notation X := (convert bX).


  Lemma rho_theta i: i<size' -> rho (theta i) i. 
  Proof. 
    intros i Hi. unfold theta. destruct (le_lt_dec size' i). omega_false.
    destruct (ie_table_surj invariant_nttd l). assumption.
  Qed.

  Lemma theta_rho i: i<size' -> forall p, rho p i -> StateSet.Equal p (theta i). 
  Proof. 
    intros i Hi p Hp.
    eapply (ie_table_inj (invariant_nttd)). eassumption.
    apply rho_theta. assumption.
  Qed.

  Lemma rho_wf: forall p i, rho p i -> i<size'.
  Proof.
    intros. destruct invariant_nttd; eauto.
  Qed.

  Lemma initiaux_initial: rho initiaux initial'.
  Proof.
    apply explore_increase_table. 
    simpl. auto with map.
  Qed.

  Lemma finaux_finaux': 
    forall i, StateSet.In i finaux' -> exists2 p, rho p i & exists2 u, StateSet.In u p & StateSet.In u finaux.
  Proof.
    intro i. unfold finaux', finals. destruct invariant_nttd. 

    apply StateSetMapProp.fold_rec_nodep. stateset_dec.
    intros p j a Hpj IH H.
    case_eq (StateSet.exists_ (fun s => StateSet.mem s finaux) p); intro He; rewrite He in H. 2: auto.
    revert H. StateSetFact.set_iff. intros [H|H]; auto. subst. clear IH. 
    rewrite <- StateSetFact.exists_iff in He. destruct He as [k [Hk Hk']].
    exists p; auto. exists k; auto. rewrite StateSetFact.mem_iff. trivial.
    repeat intro. subst. trivial.
  Qed.
  
  Lemma delta_delta': 
    forall i a, i<size' -> a<max_label -> exists2 p, rho p i & rho (delta_set A p a) (delta' i a).
  Proof.
    intros i a Hi Ha. unfold delta', Delta_to_fun.
    destruct invariant_nttd.
    cut (exists p, rho p i). intros [p Hp]. 
    exists p; trivial.
    destruct (ie_table_delta_set0 _ _ _ Ha Hp) as [H|[j [dp Hdp Hdp'] Hj']]. 
     inversion H.
     rewrite StateMapFact.find_mapsto_iff in Hdp. rewrite Hdp.
     rewrite StateMapFact.find_mapsto_iff in Hdp'. rewrite Hdp'.
     assumption.
    edestruct ie_table_surj0; eauto. 
  Qed.

  Lemma initial'_wf: initial' < size'.
  Proof. 
    eauto using rho_wf, initiaux_initial. 
  Qed.

  Lemma delta'_wf: forall i a, i < size' -> a < max_label -> delta' i a < size'.
  Proof.
    intros i a Hi Ha. destruct (delta_delta' Hi Ha) as [p _ Hp]. eapply rho_wf. eassumption. 
  Qed.

  (* second requirement de DecideKleeneAlgebra *)
  Lemma well_formed: DFA_wf (NFA_to_DFA Termination A HA).  
  Proof.
    unfold NFA_to_DFA, build. fold nttd. rewrite nttd_split. fold delta' initial' finaux'.
    repeat split.
    apply initial'_wf.
    intros i Hi. apply finaux_finaux' in Hi. 
     destruct Hi as [p Hp _]. eapply rho_wf. eassumption.
    auto using delta'_wf.
  Qed.

  Lemma theta_initiaux: StateSet.Equal initiaux (theta O).
  Proof.
    apply theta_rho; eauto using rho_wf, initiaux_initial. 
  Qed.

  Lemma eq_nat_dec_eq i j: is_true (eq_nat_dec i j) <-> i=j. 
  Proof.
    intros i j. destruct_nat_dec; simpl; firstorder. discriminate.
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

  Lemma mem_spec i s: is_true (StateSet.mem i s) <-> StateSet.In i s.
  Transparent equal one. 
  Proof.
    intros. simpl. setoid_replace (true = StateSet.mem i s) with (StateSet.mem i s = true) by firstorder.
    symmetry. apply StateSetFact.mem_iff.
  Qed.
  Opaque equal one. 

  Lemma eq_symm: forall (i j: bool), i = j <-> j = i.
  Proof. firstorder. Qed.

  Lemma map_filter i (P: stateset -> bool) (HP: Proper (StateSet.Equal ==> @eq bool) P):
   StateSet.In i
     (StateSetMap.fold
        (fun p np acc =>
         if P p then StateSet.add np acc
         else acc) table StateSet.empty)
     <-> exists p, rho p i /\ P p = true.
  Proof.
    split. 
     apply StateSetMapProp.fold_rec_nodep.
     intro. stateset_dec.
     intros p j acc Hpj IH Hi'.
     case_eq (P p); intro He; rewrite He in Hi'.
      revert Hi'. StateSetFact.set_iff. intros [Hi'|Hi'].
       subst. clear IH. exists p; auto. 
       auto.
      auto.

     intros (p&Hpi&Hp). revert Hpi.
     apply (StateSetMapProp.fold_rec_bis 
       (P:=fun table a => StateSetMap.MapsTo p i table -> StateSet.In i a)).
     intros m m' a H. rewrite H. trivial.
     rewrite StateSetMapFact.empty_mapsto_iff. tauto. 
     intros q j a table' Hqj Hq IH H.
     rewrite StateSetMapFact.add_mapsto_iff in H. destruct H as [[Hqp Hij]|[Hqp Hpi]]. subst.
     rewrite <- (HP _ _ Hqp) in Hp. rewrite Hp. stateset_dec.
     cut (StateSet.In i a); auto. case (P q); trivial; stateset_dec.
  Qed.

  Lemma in_deltaset: forall j p b, 
    StateSet.In j (delta_set A p b) <-> 
    exists k, StateSet.In k p /\ StateSet.In j (delta k b).
  Proof.
    unfold delta_set; split.
     apply StateSetProp.fold_rec_nodep. stateset_dec.
     intros i a Hip IH.
     StateSetFact.set_iff. intros [Hi|Hi]; eauto.
   
     intros [i [Hip Hj]]. revert Hip.
     apply (StateSetProp.fold_rec_bis (P:=fun p a => StateSet.In i p -> StateSet.In j a)); stateset_dec.
  Qed.


  (* third requirement de DecideKleeneAlgebra *)
  Theorem eval: eval_D (NFA_to_DFA Termination A HA) == eval_N A.
  Proof.
    unfold NFA_to_DFA, build. fold nttd. rewrite nttd_split. fold delta'.
    apply alg_eval with X; simpl.

    rewrite <- convert_dot. apply convert_compat. 
    mx_intros i j Hi Hj. simpl.
    rewrite theta_initiaux.
    apply bool_view. rewrite mxbool_dot_spec. simpl.  
    setoid_rewrite eq_nat_dec_eq. 
    split.
     intros [k [_ [-> H]]]. assumption. 
     intro H. exists O. eauto using initial'_wf.


    setoid_rewrite convert_zero. setoid_rewrite plus_neutral_left.
    apply convert_sum_commute. intros b Hb. mx_intros i j Hi Hj. simpl.
    apply bool_view. rewrite 2 mxbool_dot_spec. simpl. 
    setoid_rewrite eq_nat_dec_eq.
    setoid_rewrite and_com. setoid_rewrite <- and_assoc. 
    rewrite exists_eq. rewrite and_neutral_right. 2:auto using delta'_wf.
    setoid_rewrite mem_spec.
    destruct (delta_delta' Hi Hb) as [p Hpi Hp].
    setoid_rewrite <- (theta_rho Hi Hpi).
    rewrite <- (theta_rho (delta'_wf Hi Hb) Hp). 
    setoid_rewrite and_assoc. setoid_rewrite and_impl'.
    apply in_deltaset.
    intros x [H _]. eapply (ie_table_wf' invariant_nttd). apply Hpi. trivial.

    
    rewrite <- convert_dot. apply convert_compat. 
    mx_intros i j Hi Hj. simpl. 
    apply bool_view. rewrite mxbool_dot_spec. simpl.    
    setoid_rewrite mem_spec. unfold finals.
    rewrite map_filter. 
    split.
    
     intros (p&Hpi&Hp).
     setoid_rewrite <- StateSetFact.exists_iff in Hp. 2:(unfold compat_bool; intuition stateset_dec).
     destruct Hp as (j&Hj&Hj').
     rewrite <- StateSetFact.mem_iff in Hj'. 
     exists j. repeat split; trivial.
     apply (proj1 (proj2 HA)); trivial.
     rewrite <- (theta_rho Hi Hpi). assumption.

     intros (j&Hj&Hji&Hjf).
     exists (theta i). split.
      apply rho_theta. trivial.
      rewrite <- StateSetFact.exists_iff. 2:(unfold compat_bool; intuition stateset_dec).
      exists j. split; trivial.
      rewrite <- StateSetFact.mem_iff. trivial.

    intros s t H. apply bbool_view. 
    rewrite <- 2StateSetFact.exists_iff by (unfold compat_bool; intuition stateset_dec).
    (split; intros [x Hx]; exists x); [rewrite <- H| rewrite H]; auto.  
  Qed.
  
End Correction.

End Protect.

(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Hopcroft and Karp algorithm for checking the equivalence of two DFAs. *)

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
Require        DKA_DFA_Language.

Require Import Utils_WF.
Require Import Relations. 
Require Import List. 


Import DSUtils.Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section e.
  Import Numbers.Positive.

  Variable A : DFA.t.
  Let f := DFA.finaux A.
  Let d := DFA.delta A.

  (* TOTHINK: m := peanoView (DFA.max_label A) ? *)
  Let m := DFA.max_label A.
  Let final s := StateSet.mem s f.
  
  Fixpoint loop n (w: list label) tarjan (x y: state) : DS.UF + bool * list num := 
    match n with 
      | Datatypes.S n => 
        let '(b,tarjan) := DS.test_and_unify tarjan x y in 
        if b then inl tarjan else
        let fx := final x in
        let fy := final y in 
        if eq_bool_bool fx fy
        then fold_num_sum (fun a tarjan => loop n (a::w) tarjan (d a x) (d a y)) m tarjan
        else inr (fx, rev w)
      (* this last case is never reached *)
      | O => inl tarjan 
    end.

End e.

Import DFA.

Definition equiv A x y :=
  match loop A (Datatypes.S (size A)) nil DS.empty x y with 
    | inl _ => None
    | inr e => Some e
  end.

Lemma bounded_change_initial: forall A i, bounded A -> belong i A -> bounded (change_initial A i).
Proof.
  intros A i HA Hi. constructor; trivial; apply HA.
Qed.

Section comb.

  Local Hint Resolve DS.union_WF DS.empty_WF: typeclass_instances.

  Inductive combine_no_length X Y : list X -> list Y -> Type :=
  |cnl_nil : combine_no_length nil nil
  |cnl_cons : forall lx ly x y, combine_no_length lx ly -> combine_no_length (x::lx) (y::ly).
  
  Program Definition build_combine X Y : forall lx ly (H : List.length lx = List.length ly),
                                           @combine_no_length X Y lx ly.
  Proof. 
    induction lx. 
    intros [|y ly] Hl; (constructor || discriminate).
    intros[|y ly] Hl ; (constructor || discriminate).
    apply IHlx. simpl in Hl. injection Hl.
    tauto.
  Qed.

  Fixpoint complete (tarjan : DS.T) (l : list (state * state)) : DS.T :=
    match l with 
      | nil => tarjan
      | (x,y)::l => complete (DS.union tarjan x y) l
    end.
  Notation "t +++ l" := (complete t l) (at level 60).

  Fixpoint comb_aux l r acc : list (state * state):= match l,r with |x::l,y::r => comb_aux l r ((x,y)::acc) | _,_ => acc end.
  Definition comb l r := comb_aux l r nil.

  Lemma add_incr : forall {tar} `{DS.WF tar} l, tar <T= (tar +++ l).
  Proof.
    intros tar Hwf l; revert tar Hwf.
    induction l as [ | [x y] l IH].  intros; reflexivity. intros; simpl.  
    transitivity (DS.union tar x y).  apply DSUtils.le_union.  apply IH. ti_auto. 
  Qed.

  Lemma le_proxy : forall t t' x y,  {{t}} x y -> t <T= t' -> {{t'}} x y. 
  Proof. intuition. Qed.
  

  Lemma complete_incr : forall {tar} `{DS.WF tar} l x y, {{tar}} x y -> {{tar +++ l}} x y.
  Proof.
    intros; eauto using le_proxy, add_incr. 
  Qed.

  Lemma complete_incr_left : forall {tar} `{DS.WF tar} {tar'} `{DS.WF tar'} l,
    tar <T= tar' -> 
    tar +++l <T= tar' +++ l. 
  Proof.
    intros tar Hwf tar' Hwf' l; revert tar Hwf tar' Hwf'.
    induction l as [|[x y] l  IHl]; intros tar Hwf tar' Hwf' Hle; [ apply Hle|]. 
    simpl. apply IHl; ti_auto. apply DSUtils.le_incr, Hle. 
  Qed. 

  Lemma complete_compat_left : forall {tar} `{DS.WF tar} {tar'} `{DS.WF tar'} l,
    tar [=T=] tar' -> 
    tar +++l [=T=] tar' +++ l. 
  Proof.
    intros ? ? ? ? ? H. split; apply complete_incr_left; apply H.
  Qed.

  Instance complete_WF : forall {tar} `{DS.WF tar} l, DS.WF (tar +++ l).  
  Proof. 
    intros tar Hwf l; revert tar Hwf.
    induction l; simpl; intuition auto with typeclass_instances.
  Qed.

End comb.
Notation "t +++ l" := (complete t l) (at level 60).


Section correctness.

  Variable A: DFA.t.
  Hypothesis Hbounds: bounded A.

  Notation delta := (delta A).
  Notation size := (size A).
  Notation ml := (max_label A).
  Notation final x := (StateSet.mem x (finaux A)).
  Notation kt := (list label -> DS.UF -> state -> state -> DS.UF + bool*list label)%type.
  Notation measure := (measure size).

  Definition diag (R S : relation state) := 
    forall a x y, below x size -> below y size -> a < ml ->
      R x y -> S (delta a x) (delta a y).


  Definition prog (t t' : DS.T) := forall R, diag {{t}} {{t +++ R}} -> diag {{t'}} {{t' +++ R}}.

  Local Hint Resolve DS.union_WF DS.empty_WF: typeclass_instances.
  Existing Instance complete_WF.
  
  Instance preorder_prog : PreOrder prog.
  Proof. 
    unfold prog.
    constructor. intros tar l. tauto.
    intros x y z Hxy Hyz.
    intuition.
  Qed.

  Instance diag_compat: Proper (same_relation _ ==> same_relation _ ==> iff) diag.
  Proof.
    intros R R' HR T T' HT. unfold diag. split; intros H a x y Hx Hy Ha Hxy;
     apply HT, H; auto; apply HR; assumption. 
  Qed.

  Class invariant tarjan : Prop := 
    {
      i_wf_tarjan :> DS.WF tarjan ; 
      i_final : forall x y, {{tarjan}} x y -> final x = final y 
    }.

  Record correct_ind tarjan tarjan' (x y : state) : Prop :=
    {
      ci_prog : prog tarjan tarjan'; 
      ci_le : tarjan <T= tarjan';
      ci_measure : measure tarjan' <= measure tarjan;
      ci_sameclass : {{tarjan'}} x y
    }.

  Fixpoint add_lists x y a l := 
    match a with O => l | Datatypes.S a => (delta a x, delta a y)::add_lists x y a l end.

  Record correct_fold_ind tarjan tarjan' x y ml :=
    {
      cfi_prog : forall l, diag {{tarjan}} {{tarjan +++ add_lists x y ml l}} -> diag {{tarjan'}} {{tarjan' +++ l}};
      cfi_le : tarjan <T= tarjan';
      cfi_measure : measure tarjan' <= measure tarjan
    }.

  Lemma diag_compat_left : forall {tar} `{DS.WF tar} {tar'} `{DS.WF tar'},
    tar [=T=] tar' -> 
    forall l,
      diag {{tar}} {{tar +++ l}} -> 
      diag {{tar' }} {{tar'+++l}}.
  Proof.
    intros tar Hwf tar' Hwf' Heq l H a x y Hx Hy Ha Htar.
    rewrite <- Heq in Htar. 
    specialize (H a x y Hx Hy Ha Htar).
    refine (complete_incr_left _ H). apply Heq.  
  Qed.

  Lemma correct_ind_idem : forall x y tarjan, 
     {{tarjan}} x y -> 
     invariant tarjan -> 
     correct_ind tarjan ( DS.union tarjan x y ) x y.
  Proof.
    intros x y tarjan Hxy Hstat.
    constructor.
    
     assert (heq : tarjan [=T=] DS.union tarjan x y). 
       apply DSUtils.eq_union, Hxy. 
     unfold prog. intros. exact (diag_compat_left heq H). 
     
     apply DSUtils.le_union.
     rewrite measure_union_idem; trivial. 
     rewrite DS.sameclass_union. auto. 
  Qed.

  Lemma invariant_idem : forall tarjan x y, 
    invariant tarjan -> 
    {{tarjan}} x y ->
    invariant (DS.union tarjan x y).
  Proof.
    intros tarjan x y H Hxy.
    assert (Hprog : forall np nq, {{DS.union tarjan x y}} np nq -> {{tarjan}} np nq).
      intros np nq H'.
      rewrite DS.sameclass_union in H'. intuition; symmetry. 
      rewrite H0, Hxy. assumption. 
      rewrite H2, <- Hxy. assumption. 

    constructor.
     ti_auto. 
     intros np nq H'. apply Hprog in H'. apply H; auto.
  Qed.

  Lemma tarjan_equiv_true : forall {tarjan} `{DS.WF tarjan} x y u, 
    DS.equiv tarjan x y = (true, u) -> {{tarjan}} x y. 
  Proof.
    intros T Hwf x y u H .
    rewrite <- DS.sameclass_equiv.  
    rewrite H; reflexivity.
  Qed.
  Hint Resolve tarjan_equiv_true : core.

  Lemma invariant_prog : forall tarjan x y,
    invariant tarjan ->
    final x = final y ->
    invariant (DS.union tarjan x y).
  Proof.
    intros tarjan x y H Hxy.
    constructor. ti_auto. 
    intros np nq H'.
    rewrite DS.sameclass_union in H'.  
    assert (wlog : forall P Q : relation state, 
      (forall x y, Q x y <-> Q y x) -> (forall x y, P x y -> Q x y) -> forall u v, (P u v \/ P v u) -> Q u v).
    clear.
    intros.
    destruct H1.
    apply H0. auto.
    rewrite H. apply H0. auto.
    
    destruct H' as [H' | H'].
    apply H. auto.
    revert H'.
    generalize np nq.  clear np nq. apply wlog.
    intros. intuition.
    intros. destruct H0. apply H in H0. apply H in H1. eauto. 
  Qed.

  Lemma in_union: forall {tar} `{DS.WF tar} x y, {{DS.union tar x y}} x y.
  Proof.
    intros. rewrite DS.sameclass_union.
    right. left. split; reflexivity.
  Qed.


  Lemma add_lists_S: forall {tar} `{DS.WF tar} x y a l,
    {{tar}} (delta a x) (delta a y) -> tar+++add_lists x y (Datatypes.S a) l [=T=] tar+++add_lists x y a l.
  Proof.
    intros tarjan Hwf x y a l H.
    simpl complete at 1.  
    apply complete_compat_left. 
    split; intros u v Huv.
    rewrite DS.sameclass_union in Huv.
    num_simpl.
    destruct Huv as [Huv | [[Hu Hv]|[Hu Hv]]]; auto.
    rewrite Hu, Hv; assumption.
    rewrite Hu, Hv; symmetry; assumption.
    apply DSUtils.le_union, Huv.
  Qed.
 

  Lemma add_lists_sameclass: forall {tar} `{DS.WF tar} ml a x y l, a < ml ->
    {{tar +++ add_lists x y ml l}} (delta a x) (delta a y).
  Proof.
    intros tar Hwf ml; revert tar Hwf.
    induction ml; intros.
     lia_false.
     simpl.
      destruct (eq_nat_dec a ml). subst. apply complete_incr. apply in_union.
      apply IHml; ti_auto. lia.
  Qed.



  Lemma diag_ok : forall {tarjan} `{DS.WF tarjan} x y l, 
      below x size ->
      below y size ->
      diag {{tarjan}} {{tarjan +++ l}} ->
      diag  {{DS.union tarjan x y}} {{DS.union tarjan x y +++ add_lists x y ml l}}.
  Proof.
    intros tar Hwf x y l Hx Hy Hl.
    intros a v w Hv Hw Ha H.
    rewrite DS.sameclass_union in H. 
    assert (Hle : tar+++l <T= DS.union tar x y +++ add_lists x y ml l).  
     clear - Hwf. induction ml using num_peano_rec; simpl. 
     apply complete_incr_left. auto using DSUtils.le_union. 
      num_simpl. simpl.  
      rewrite IHn. apply complete_incr_left. apply DSUtils.le_union. 
       
       destruct H as [H | [[Hv' Hw' ] | [Hw' Hv']]].
       eapply (Hl a) in H; auto.
              
       eapply (Hl a) in Hv'; auto.
       eapply (Hl a) in Hw'; auto.
         apply Hle in Hv'. 
         apply Hle in Hw'. 
         rewrite Hv', Hw'.
         apply add_lists_sameclass, Ha.

       eapply (Hl a) in Hv'; auto.
       eapply (Hl a) in Hw'; auto.
         apply Hle in Hv'. 
         apply Hle in Hw'. 
         rewrite Hv', Hw'.  
         symmetry.
         apply add_lists_sameclass, Ha.
  Qed.

  Import Numbers.Positive.
  Lemma loop_correct : forall n w t t' x y,
    measure t < n -> 
    invariant t -> below x size -> below y size -> loop A n w t x y = inl t' ->  
    correct_ind t t' x y /\ invariant t'.
  Proof.
    induction n. intros. lia_false.
    intros w tarjan tar' x y Hsize Hstat Hx Hy. simpl loop.
    rewrite DS.test_and_unify_eq.
    case_eq (DS.equiv tarjan x y). intros [|] u Hn; simpl. 
    
    (** first case, nothing is done*)
    intro H'; injection H'; intros; subst; clear H'.
    split. apply correct_ind_idem; trivial. rewrite <- DS.sameclass_equiv, Hn. reflexivity.
    apply invariant_idem; trivial. rewrite <- DS.sameclass_equiv, Hn. reflexivity.    

    (** second case, we make a fold_labels*)
    bool_analyse. 2: discriminate.
    assert (IH: forall tar, 
      fold_num_sum (fun a tar => loop A n (a :: w) tar (delta a x) (delta a y)) ml tar = inl tar' ->
      {{tar}} x y ->
      measure tar < n -> 
      invariant tar -> correct_fold_ind tar tar' x y ml /\ invariant tar').
    clear u Hn tarjan Hstat Hsize.
    induction ml as [|a IHa] using num_peano_rec; [setoid_rewrite fold_num_sum_O|setoid_rewrite fold_num_sum_S];
      simpl; intros tar Htar Hxy Hsize Htar'.
     dependent destruction Htar. split; auto. constructor; auto. reflexivity.
     revert Htar. num_simpl. simpl. num_simpl.
     case_eq (loop A n (a :: w) tar (delta a x) (delta a y)); intros tar'' Htar'' Htar. 2: discriminate.
     apply IHn in Htar''; auto using bounded_delta. destruct Htar'' as [Htar'' Htar''i]. clear IHn.
     apply IHa in Htar; auto. clear IHa.
      split.
       constructor.
        intros l Hl. apply Htar. rewrite <- add_lists_S. apply Htar''. assumption. 
        apply (ci_sameclass Htar'').
        transitivity tar''. apply Htar''. apply Htar.   
        apply le_trans with (measure tar''). apply Htar. apply Htar''.
       apply Htar.
      apply Htar'', Hxy.
      eapply le_lt_trans. apply Htar''. apply Hsize. 

    clear IHn. intro Hr.
    destruct (IH _ Hr) as [IH1 IH2]; clear Hr IH. 
     apply in_union. 
     apply (measure_union_strict (size:=size)) in Hn; auto; num_lia. 
     apply invariant_prog; assumption.
    split; auto. constructor. 
     intros l Hl. simpl; simpl in Hl. 
     apply IH1. apply diag_ok; ti_auto. 

     transitivity (DS.union tarjan x y). apply DSUtils.le_union. apply IH1.
     apply le_trans with (measure (DS.union tarjan x y)). 
     apply IH1. apply (measure_union_strict (size:=size)) in Hn; auto using lt_le_weak; num_lia.
     apply IH1. apply in_union.
  Qed.


  Section Correction.

    Variables i' j' : state.
    Hypothesis Hi' : below i' size.
    Hypothesis Hj' : below j' size.
    Variable tarjan : DS.T.
    Hypothesis _H : (loop A (Datatypes.S size) nil DS.empty i' j') = inl tarjan.  

    Lemma invariant_empty : invariant DS.empty.
    Proof.
      constructor. ti_auto. intros x y Hxy.
      apply DS.sameclass_empty in Hxy; subst. reflexivity.
    Qed.
    
    Lemma tarjan_correct : correct_ind DS.empty tarjan i' j' /\ invariant tarjan.
    Proof.
      apply loop_correct in _H; auto.
      rewrite measure_empty. auto with arith.
      apply invariant_empty.
    Qed.

    Instance tarjan_wf : DS.WF tarjan.
    Proof. apply tarjan_correct. Qed.

    Definition equivalent x y := (fst (DS.equiv tarjan x y)).

    Notation "A =&&= B" := (eq_state_bool A B) (at level 75).
    Notation "A =T= B" := (equivalent A B) (at level 75).
 
    Ltac xif_simpl :=
      repeat match goal with
               | |- context [xif true ?x ?y] => change (xif true x y) with x
               | |- context [xif false ?x ?y] => change (xif false x y) with y
             end.

    Ltac xif_destruct :=
      match goal with
        | |- context [xif ?b ?x ?y] => case_eq b; intros; xif_simpl
      end.

    Lemma T_true : forall a b, (a =T= b) = true <-> {{tarjan}} a b.
    Proof. intros. rewrite <- DS.sameclass_equiv. reflexivity. Qed.

    Lemma T_finaux : forall x y, (x =T= y) = true -> StateSet.mem x (finaux A) = StateSet.mem y (finaux A). 
    Proof. 
      intros.
      rewrite T_true in H.
      destruct tarjan_correct as [_ H']. apply i_final, H.
    Qed.
            
    Lemma T_refl : forall x, (x =T= x) = true.
    Proof.
      intros.
      rewrite T_true. 
      reflexivity.
    Qed.
    Hint Rewrite T_refl : bool_simpl.
    
    Lemma zero_leq : forall x, 0 <= x. Proof. trivial with arith. Qed.
    Lemma leq_zero_plus : forall a b, a < b -> a < 0 + b. Proof. auto with arith. Qed.
    Hint Resolve zero_leq leq_zero_plus: size. 
      
    Ltac leq_sum n := apply leq_sum; exists n; split ; [ auto with size | split; [ auto with size |]].
    
    Lemma diag_empty :  diag {{DS.empty}} {{DS.empty +++ nil}}.
    Proof.
      intros l ? ? ? ? ? Hxy. apply DS.sameclass_empty in Hxy. subst. reflexivity.
    Qed.
    
    Lemma simulation: forall i j, (i =T= j) = true -> belong i A -> belong j A -> 
      forall a, a < max_label A -> (delta a i =T= delta a j) = true.
    Proof.
      intros. rewrite T_true in *.
      destruct tarjan_correct as [[H' _ _ _] _].
      eapply (H' nil diag_empty); trivial.
    Qed.
    
    Lemma eval_change_initial : eval (change_initial A i') == eval (change_initial A j').
    Proof.
      apply mx_to_scal_compat.

      pose (y := box _ _ 
        (fun np rp => xif (state_of_nat np =T= state_of_nat rp) 1 0): KMX (nat_of_num size) (nat_of_num size)).
      pose (m := MAUT.delta (to_MAUT (change_initial A j'))). 
      pose (v :=  MAUT.final (to_MAUT (change_initial A j'))).
      apply (equiv_filter (y := y) (m := m) (v := v)).

      (* ia * y == ib * y *)
      simpl MAUT.initial. fold_regex.
      setoid_rewrite (mx_point_one_left (n:=1) (m:=size) (p:=size)).
      mx_intros a b Ha Hb. simpl. fold_regex.
      apply xif_compat; auto.
      rewrite 2 id_num. apply <- bool_prop_iff. rewrite 2 T_true. 
      destruct tarjan_correct as [[ _ _ _ H] _]. rewrite H. tauto.  
      num_lia.
      num_lia.
       
      (* y * m <== m * y *)
      mx_intros i k Hi Hk. simpl; fold_regex.
       apply sum_leq; intros j _ Hj. 
       xif_destruct; [semiring_normalize|semiring_reflexivity].
       unfold labelling. 
       setoid_rewrite sum_distr_left. rewrite sum_inversion. (* BUG setoid_rewrite/rewrite: très long... *)
       apply sum_incr; intros a Ha. simpl; fold_regex. fold_leq.
       xif_destruct; unfold xif at 1; trivial with algebra.
       leq_sum (delta a i). pose proof (bounded_delta Hbounds a i). num_lia.
       bool_simpl. num_prop. rewrite H0.
       rewrite (simulation H); trivial. 
        unfold xif. semiring_reflexivity.
        num_lia. 
        num_lia. 
            
      (* y * v == v *)
      mx_intros i j Hi Hj. clear - Hi Hbounds i' Hi' Hj' _H. simpl; fold_regex.
      apply leq_antisym. 
       apply sum_leq.
       intros n Hn Hn'. 
       xif_destruct; [semiring_normalize|semiring_reflexivity]. 
       apply T_finaux in H. unfold statesetelt_of_nat, statemapelt_of_nat in *.
       rewrite H. reflexivity.
        
       xif_destruct; trivial with algebra.
       leq_sum i. rewrite T_refl, H. xif_simpl. semiring_reflexivity.

      (* 1 <== y *)
      mx_intros i j Hi Hj. simpl; fold_regex.
       nat_analyse; auto with algebra.
       rewrite T_refl. xif_simpl. trivial with algebra.

      (* y * y <== y*)
      mx_intros i j Hi Hj. simpl; fold_regex.
       apply sum_leq. intros k Hk Hk'. 
       xif_destruct; [semiring_normalize|semiring_reflexivity].
       xif_destruct; [semiring_normalize|semiring_reflexivity].
       rewrite T_true in *. rewrite H0 in H. rewrite <- T_true in H. 
       rewrite H. reflexivity. 
    Qed.
  End Correction.


  Theorem valid i j: belong i A -> belong j A -> equiv A i j = None -> 
    eval (change_initial A i) == eval (change_initial A j).
  Proof.
    intros Hi Hj H'.
    unfold equiv in H'.
    case_eq (loop A (Datatypes.S size) nil DS.empty i j); intros R HR; rewrite HR in H'.
    apply (eval_change_initial Hi Hj HR).
    discriminate.
  Qed.

End correctness.
          

Import DKA_DFA_Language.

Section completeness.

  Variable A: DFA.t.
  Hypothesis HA: bounded A.
  Variables i j: state.
  Hypothesis Hi: belong i A.
  Hypothesis Hj: belong j A.

  Definition select (b: bool) (i j: state) := if b then i else j.

  Lemma counter_exemple_loop: forall b w n v t, 
    bounded_word A v ->
    loop A n v t (read A (rev v) i) (read A (rev v) j) = inr (b,w) -> 
    DFA_language (change_initial A (select b i j)) w  
    /\ ~ DFA_language (change_initial A (select b j i)) w.
  Proof.
    induction n; intros v tar Hv.
     intro. discriminate.
     simpl. case DS.test_and_unify. intros [|] tar'.
      intro. discriminate.
      bool_analyse. 
       clear e tar. revert v Hv tar'. generalize (le_n (max_label A)). 
       generalize (max_label A) at 1 3 as a. 
       induction a using num_peano_rec; [setoid_rewrite fold_num_sum_O|setoid_rewrite fold_num_sum_S];
         intros Ha v Hv tar; simpl.
        intro. discriminate.
        num_simpl. simpl. num_simpl.
        generalize (IHn (a::v) tar). simpl. rewrite 2 read_app. simpl.
        case loop. 
         intros tar' _ H. apply IHa in H; auto with arith. 
         intros p H H'. dependent destruction H'. apply H; auto.
          intros c [->|Hc]; auto with arith. num_lia. 

       clear IHn. intro H'; injection H'; intros; subst; clear H'.
       StateSetProps.mem_analyse; StateSetProps.mem_analyse; 
        (elim H; reflexivity) || (unfold DFA_language, bounded_word; setoid_rewrite <- In_rev; tauto).
  Qed.

  Lemma counter_exemple_equiv: forall b w, 
    equiv A i j = Some (b,w) -> 
    DFA_language (change_initial A (select b i j)) w  
    /\ ~ DFA_language (change_initial A (select b j i)) w.
  Proof.
    intros b w. unfold equiv. 
    case_eq (loop A (Datatypes.S (size A)) nil DS.empty i j). intros; discriminate. 
    intros [b' w'] H H'. injection H'; intros; subst.   clear H'. 
    apply (@counter_exemple_loop b w _ nil) in H. assumption.
    intro. simpl. tauto.
  Qed.

Opaque equal.
  Theorem completeness: equiv A i j <> None -> ~ eval (change_initial A i) == eval (change_initial A j).
  Proof.
    remember (equiv A i j) as r. destruct r as [[b w]|]. 2: rewrite Heqr; firstorder. 
    intros _ H. symmetry in Heqr. apply counter_exemple_equiv in Heqr; auto. 
    apply regex_language_graph_functor in H. simpl in H.
    rewrite 2 language_DFA_eval in H by auto using bounded_change_initial.
    specialize (H w). destruct b; simpl in Heqr; tauto.
  Qed.
Transparent equal.

End completeness.

Theorem correct: forall A i j, bounded A -> belong i A -> belong j A ->
  (equiv A i j = None <-> eval (change_initial A i) == eval (change_initial A j)).
Proof.
  intros A i j HA Hi Hj. split.
   apply valid; assumption.
   case_eq (equiv A i j); auto.
   intros c Hc H. exfalso. apply (completeness HA Hi Hj). rewrite Hc. intro. discriminate. assumption.
Qed.

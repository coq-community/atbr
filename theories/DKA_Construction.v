(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Construction of automata ([eNFA]) from regular expressions.
   
    We define a high-level algorithm first, which we prove correct.
    The efficient algorithm is then defined, and proved equivalent to
    the high-level one.

    We also prove that is the given expression was in strict star
    form, then the resulting automata has well-founded epsilon
    transitions.
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
Require Import DKA_CheckLabels.
Require Import StrictStarForm.

Require Import Utils_WF.
Require Import Relations.      


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** Algebraic, not really efficient, presentation of the construction algorithm *)
Module Algebraic.

  #[universes(template)]
  Record pre_MAUT := mk {
    size: nat;
    delta: KMX size size 
  }.

  Definition add (a : regex) (i f : nat) (A : pre_MAUT) : pre_MAUT := mk (delta A + mx_point _ _ i f a).

  Definition add_one i f A := add 1 i f A.

  Definition add_var i f c A := add (RegExp.var c) i f A.
    
  Definition empty := mk (0: KMX 2 2).

  Definition incr (A : pre_MAUT) : pre_MAUT := @mk (size A+1) (mx_blocks (delta A) 0 0 0).
    
  Fixpoint build e i f (A : pre_MAUT) : pre_MAUT :=
    match e with 
      | RegExp.zero => A
      | RegExp.one => add_one i f A 
      | RegExp.var c => add_var i f c A
      | RegExp.plus a b => build a i f (build b i f A)
      | RegExp.dot a b =>
        let p := size A in
          build a i p (build b p f (incr A))
      | RegExp.star a =>
        let p := size A in 
          add_one i p (build a p p (add_one p f (incr A)))
    end.

  Definition to_MAUT i f A :=
    MAUT.mk (mx_point _ _ 0 i 1) (delta A) (mx_point _ _ f 0 1).

  Definition X_to_MAUT e := to_MAUT 0 1 (build e 0 1 empty).


  (** below : proof of correctness *)

  Definition eval i f := to_MAUT i f >> MAUT.eval.

  Inductive equal : pre_MAUT -> pre_MAUT -> Prop :=
  | equal_refl: forall n (M N : KMX n n), M == N -> equal (mk M) (mk N).

  Infix " [=0=] " := equal (at level 80).
  
  Section protect.

  Local Instance equal_equiv : Equivalence equal. 
  Proof.
    constructor.
     intros [x X]. constructor. reflexivity.
     intros [x X][y Y] H. destruct H. constructor. symmetry; auto.
     intros x y z Hxy Hyz. 
     assert (Sxy: size x = size y /\ mx_equal_at (size x) (size x) (delta x) (delta y)). destruct Hxy. auto.
     clear Hxy. destruct Hyz. destruct x. simpl in Sxy. intuition. subst.
     constructor. transitivity M; assumption.
  Qed.

  Local Instance to_MAUT_compat i f : Proper (equal ==> MAUT.equal) (to_MAUT i f).
  Proof.
    intros [m M] [n N] H.
    destruct H. 
    constructor; auto with compat. 
  Qed.

  Local Instance eval_compat i f : Proper (equal ==> Classes.equal tt tt) (eval i f).
  Proof.
    intros M N H. apply MAUT.eval_compat, to_MAUT_compat, H.
  Qed.

  Local Instance add_compat' : Proper (Classes.equal tt tt ==> (@eq nat) ==> @eq nat ==> equal ==> equal) add.
  Proof.
    intros a b Hab i i' Hi j j' Hj M N H. destruct H. constructor. subst. auto with compat. 
  Qed.
  Local Instance add_compat a i j : Proper (equal ==> equal) (add a i j).
  Proof.
    intros M N H. destruct H. constructor. auto with compat. 
  Qed.

  Local Instance incr_compat : Proper (equal ==> equal) incr.
  Proof.
    intros M N H. destruct H. constructor. auto with compat.
  Qed.

  Local Instance build_compat a i f : Proper (equal ==> equal) (build a i f).
  Proof.
    unfold Proper, respectful. revert i f.
    induction a; intros i f M N H; simpl; unfold add_one, add_var; auto with compat.

    apply add_compat; trivial.

    inversion_clear H.
    apply IHa1, IHa2, incr_compat. constructor; trivial. 

    inversion_clear H.
    apply add_compat, IHa, add_compat, incr_compat. constructor; trivial. 
    
    apply add_compat; trivial.
  Qed.

  Arguments star : simpl never.
  Arguments plus : simpl never.
  Arguments dot : simpl never.
  Arguments one : simpl never.
  Arguments zero : simpl never.
  Arguments Classes.equal : simpl never.

  Notation belong s A := (s < size A)%nat.

  Lemma belong_incr: forall A s, belong s A -> belong s (incr A).
  Proof. intros. destruct A. simpl in *. auto with arith. Qed.
  Lemma belong_incr': forall A, belong (size A) (incr A).
  Proof. intros. simpl. omega. Qed.
  Lemma belong_add: forall i j b A s, belong s A -> belong s (add i j b A).
  Proof. intros. destruct A. assumption. Qed.
  Lemma belong_add_one: forall i j A s, belong s A -> belong s (add_one i j A).
  Proof. intros. apply belong_add. trivial. Qed.
  Lemma belong_add_var: forall i j n A s, belong s A -> belong s (add_var i j n A).
  Proof. intros. apply belong_add. trivial. Qed.
  Local Hint Resolve belong_incr belong_incr' belong_add belong_add_one belong_add_var : core.

  Lemma belong_build: forall a i j A s, belong s A -> belong s (build a i j A).
  Proof. induction a; simpl; intros; auto. Qed.
  Local Hint Resolve belong_build : core.

  Lemma add_comm : forall a b i f s t M, add a i f (add b s t M) [=0=] add b s t (add a i f M).
  Proof.
    intros a b i f s t [m M].
    constructor. cbn. semiring_reflexivity.
  Qed.

  Lemma add_plus : forall a b i f M, add (a+b) i f M [=0=] add a i f (add b i f M).
  Proof.
    intros a b i f [m M].
    constructor. cbn. rewrite <- mx_point_plus. semiring_reflexivity.
  Qed.

  Lemma add_zero : forall i f M, add 0 i f M [=0=] M.
  Proof.
    intros i f [m M].
    constructor. cbn. rewrite <- mx_point_zero. semiring_reflexivity.
  Qed.


  Lemma incr_add : forall a s t M, belong s M -> belong t M ->
    incr (add a s t M) [=0=] add a s t (incr M).
  Proof.
    intros a s t [n M] Hs Ht. constructor. cbn in *. 
    rewrite mx_point_blocks00 by assumption.
    rewrite mx_blocks_plus. auto with algebra. 
  Qed.

  Lemma build_add: forall b i j s t M a, belong s M -> belong t M -> 
    build b i j (add a s t M) [=0=] add a s t (build b i j M).
  Proof. 
    induction b;  intros i j s t M a Hs Ht ; cbn. 
   
     apply add_comm.
    
     reflexivity.
  
     rewrite <- IHb1; auto. apply build_compat.
     rewrite <- IHb2; auto. apply build_compat.
     apply incr_add; trivial.

     rewrite <- IHb1; auto. apply build_compat.
     apply IHb2; trivial.

     unfold add_one. 
     rewrite add_comm. apply add_compat. 
     rewrite <- IHb; auto. apply build_compat.
     rewrite add_comm. apply add_compat.
     apply incr_add; trivial.
     
     apply add_comm.
  Qed.

  Lemma eval_select_block m x y z: forall (U: KMX x m) (A M: KMX m m) B C (D: KMX y y) (V: KMX m z),
    A+B*D#*C == M ->
     mx_blocks (x:=0) 0 0 U 0 * (mx_blocks A B C D)# * mx_blocks (y:=0) 0 V 0 0 
     == U * M# * V.
  Proof.
    intros.
    rewrite mx_blocks_star.  
    rewrite 2 mx_blocks_dot.  
    rewrite mx_blocks_degenerate_11.
    rewrite H.
    semiring_reflexivity.
  Qed.

  Lemma eval_master_theorem i f s t a b c: forall A,
    belong i A -> belong f A -> belong s A -> belong t A ->
    eval i f (add c (size A) (size A) (add a s (size A) (add b (size A) t (incr A))))
    == eval i f (add (a*c#*b) s t A).
  Proof.   
    intros [n M]; cbn; intros Hi Hf Hs Ht. 
    apply mx_to_scal_compat; cbn.
    change 1%nat with (0+1)%nat.
    rewrite mx_point_blocks10 by trivial. 
    rewrite mx_point_blocks10 by trivial.    
    rewrite mx_point_blocks01 by trivial.
    rewrite mx_point_blocks11 by trivial.
    setoid_rewrite mx_point_blocks01 at 2; trivial.
    cbn.
    rewrite 2minus_diag.
    set (U := mx_point 1 n 0 i (1: regex)).
    set (V := mx_point n 1 f 0 (1: regex)).
    set (Y := mx_point n 1 s 0 (a: regex)).
    set (Z := mx_point 1 n 0 t (b: regex)).
    set (A := mx_point 1 1 0 0 c).
    set (AS := M + mx_point n n s t (a*c#*b)).
    rewrite 3 mx_blocks_plus.
    apply eval_select_block. 
    rewrite !plus_neutral_right, !plus_neutral_left. apply plus_compat; trivial.
    unfold A, Y, Z.
    rewrite mx_point_scal. rewrite <- mx_of_scal_star. rewrite <- mx_point_scal. 
    rewrite mx_point_dot by trivial with arith.  
    rewrite mx_point_dot by trivial with arith.
    apply mx_point_compat.
    semiring_reflexivity.
  Qed.
  
  Lemma eval_dot i f s t a b: forall A, 
    belong i A -> belong f A -> belong s A -> belong t A ->
    eval i f (add b (size A) t (add a s (size A) (incr A)))
    == eval i f (add (a*b) s t A).
  Proof.
    intros [n M]. cbn - [eval]. intros Hi Hf Hs Ht.
    setoid_replace (a*b: regex) with (a*0#*b)%A using relation RegExp.equal. 
    rewrite add_comm; rewrite <- eval_master_theorem;auto. apply eval_compat. rewrite add_zero. reflexivity.
    fold_regex. rewrite star_zero. semiring_reflexivity.
  Qed.

  Lemma eval_star i f s t a A:
    belong i A -> belong f A -> belong s A -> belong t A ->
    eval i f (add a (size A) (size A) (add 1 s (size A) (add 1 (size A) t (incr A)))) 
    == eval i f (add (a#) s t A).
  Proof.
    cbn - [eval]; intros Hi Hf Hs Ht. 
    rewrite eval_master_theorem;auto.
    apply eval_compat, add_compat'; auto.
    semiring_reflexivity.
    reflexivity.
  Qed.
    
  Lemma build_correct: forall a A i f s t,
    belong i A -> belong f A -> belong s A -> belong t A -> 
    eval i f (build a s t A) == eval i f (add a s t A).
  Proof.
    induction a; intros A i f s t Hi Hf Hs Ht; cbn - [eval]; trivial.
     rewrite add_zero; trivial.

     rewrite IHa1; auto.
     rewrite <- build_add; auto.
     rewrite IHa2; auto.
     apply eval_dot; trivial.

     rewrite IHa1; auto.
     rewrite <- build_add; auto.
     rewrite IHa2; auto.
     rewrite add_plus, add_comm. reflexivity.

     unfold add_one.
     rewrite <- build_add; auto.
     rewrite IHa; auto.
     apply eval_star; trivial.
  Qed.

  (** Correctness of the high-level construction algorithm *)

  Theorem construction_correct: forall (e: regex), MAUT.eval (X_to_MAUT e) == e.
  Proof.
    intro e. eapply equal_trans.
    apply build_correct; auto with arith.
    Transparent dot star plus one zero Peano.minus.
    compute; fold_regex.
    kleene_clean_zeros. semiring_reflexivity.
  Qed.

  End protect.
End Algebraic.


Infix " [=0=] " := Algebraic.equal (at level 80).

Definition statelabelmap_set_to_fun d := fun ia => optionset_to_set (StateLabelMap.find ia d).

Module Concrete.

  #[universes(template)]
  Record pre_eNFA := mk {
    size:       state;                  (** next fresh state (= size) *)
    epsilonmap: statemap stateset;      (** epsilon-transitions *)
    deltamap:   statelabelmap stateset; (** visible transitions *)
    max_label:  label                   (** maximal label + 1 *)
  }. 

  Definition augment (i: state) f eps :=
    StateMap.add i (StateSet.add f (statemap_set_to_fun eps i)) eps. 

  Definition add_one i f (A: pre_eNFA) :=
    let '(mk s e d m) := A in 
      mk s (augment i f e) d m.

  Definition augment_var ia j delt :=
    StateLabelMap.add ia (StateSet.add j (statelabelmap_set_to_fun delt ia)) delt. 

  Definition add_var i f a (A: pre_eNFA) :=
    let '(mk s e d m) := A in 
      mk s e (augment_var (i,a) f d) (max (S a) m).
      
  Definition incr (A: pre_eNFA): pre_eNFA:=
    let '(mk s e d m) := A in 
      mk (S s) e d m.
    
  Fixpoint build e (i : state) (f: state) (A : pre_eNFA) : pre_eNFA :=
    match e with 
      | RegExp.zero => A
      | RegExp.one => add_one i f A
      | RegExp.var c => add_var i f c A 
      | RegExp.plus a b => build a i f (build b i f A)
      | RegExp.dot a b => 
        let p := size A in 
          let A := incr A in 
            build a i p (build b p f A)
      | RegExp.star a =>
        let p := size A in 
          let A := incr A in 
            add_one i p (build a p p (add_one p f A))
    end.
      
  Definition empty := mk 2 (StateMap.empty _) (StateLabelMap.empty _) O.

  Definition X_to_eNFA e := 
    let '(mk s e d m) := build e 0 1 empty in
      eNFA.mk s (statemap_set_to_fun e) d 0 1 m.
    
End Concrete.

Definition X_to_eNFA := Concrete.X_to_eNFA.


Module Correctness.

  Import Concrete.

  Notation belong s A := (below s (size A)).

  Definition epsilonfun A := statemap_set_to_fun (epsilonmap A).
  Definition epsilonbrel A := fun i j => StateSet.mem j (epsilonfun A i).
  Definition epsilon A: relation state := fun i j => epsilonbrel A i j = true.
  Notation epsilon_t A := (clos_trans state (epsilon A)).
  Notation epsilon_rt A := (clos_refl_trans state (epsilon A)).

  Definition wf A := well_founded (transp _ (epsilon A)).


  Definition deltafun A := statelabelmap_set_to_fun (deltamap A).
  Definition deltabrel A i a j := StateSet.mem j (deltafun A (i,a)).
  Definition delta A i a j := deltabrel A i a j = true.

  Ltac unfold_defs H :=
    unfold delta, deltabrel, deltafun, statelabelmap_set_to_fun,
      epsilon, epsilonbrel, epsilonfun, statemap_set_to_fun in H; simpl in H.

  Record bounded A : Prop := {
      bounded_delta: forall i a j, delta A i a j -> lt a (max_label A) /\ belong i A /\ belong j A;
      bounded_eps : forall i j, epsilon A i j -> belong i A /\ belong j A
  }.

  Definition preNFA_to_preMAUT (A: pre_eNFA): Algebraic.pre_MAUT := 
    let n := nat_of_state (size A) in
      Algebraic.mk
      (mx_bool _ n n (fun i j => epsilonbrel A (state_of_nat i) (state_of_nat j))
        + box n n (fun i j => labelling (max_label A) 
                      (fun a => deltabrel A (state_of_nat i) a (state_of_nat j)))).   

  Section protect.


  Transparent zero one plus dot star.

  Lemma belong_incr: forall A s, belong s A -> belong s (incr A).
  Proof. intros. destruct A; simpl in *. num_omega. Qed.
  Lemma belong_incr': forall A, belong (size A) (incr A).
  Proof. intros. destruct A. simpl. num_omega. Qed.
  Lemma belong_add_one: forall i j A s, belong s A -> belong s (add_one i j A).
  Proof. intros. destruct A. assumption. Qed.
  Lemma belong_add_var: forall i j n A s, belong s A -> belong s (add_var i j n A).
  Proof. intros. destruct A. assumption. Qed.
  Local Hint Resolve belong_incr belong_incr' belong_add_one belong_add_var : core.

  Lemma belong_build: forall a i j A s, belong s A -> belong s (build a i j A).
  Proof. induction a; simpl; intros; auto. Qed.
  Local Hint Resolve belong_build : core.
  
  Lemma epsilonbrel_add_one: forall i j A s t, 
    epsilonbrel (add_one i j A) s t = epsilonbrel A s t || eq_state_bool i s && eq_state_bool j t.
  Proof.
    intros. destruct A. unfold epsilonbrel, epsilonfun, add_one, augment, statemap_set_to_fun. simpl.

    
    repeat StateMapProps.find_analyse; simpl; StateMapProps.find_tac; bool_simpl; simpl; trivial.
     rewrite eqb_eq_nat_bool. apply orb_comm. 
     num_analyse; bool_simpl; trivial; subst; auto.
     num_analyse; bool_simpl; trivial; subst; auto.
     rewrite eqb_eq_nat_bool. trivial. 
     apply <- bool_prop_iff; bool_connectors; intuition. num_prop. subst. auto.
     apply <- bool_prop_iff; bool_connectors; intuition. num_prop. subst. auto.
  Qed.

  Lemma epsilon_add_one: forall i j A s t, epsilon (add_one i j A) s t <-> epsilon A s t \/ i=s /\ j=t.
  Proof.
    intros. unfold epsilon. rewrite epsilonbrel_add_one. bool_connectors. num_prop. reflexivity.
  Qed.


  Lemma epsilon_add_var: forall i j n A s t, epsilon (add_var i j n A) s t <-> epsilon A s t.
  Proof. intros i j n [ ] s t. reflexivity. Qed.

  Lemma epsilon_incr: forall A s t, epsilon (incr A) s t <-> epsilon A s t.
  Proof. intros [ ] s t. reflexivity. Qed.

  Lemma epsilon_empty: forall i j, ~ epsilon empty i j.
  Proof.
    intros i j F.
    apply StateSet.mem_2 in F.
    unfold_defs F. StateMapProps.find_analyse.  simpl in *.
     revert H. StateMapProps.map_iff. tauto.
     apply StateSet.empty_1 in F. auto.
  Qed.

  Ltac sl_inject := repeat
    match goal with 
      | H: StateLabel.P.compare _ _ = Eq |- _ => 
        apply StateLabel.P.reflect in H; injection H; intros; subst
      | H: StateLabel.P.compare ?x ?x = Eq -> False |- _ => elim H; apply StateLabel.eq_refl
    end.

  Lemma deltabrel_add_var: forall i j n A s t m, 
    deltabrel (add_var i j n A) s m t = 
    deltabrel A s m t || eq_label_bool n m && (eq_state_bool i s && eq_state_bool j t).
  Proof.
    intros. destruct A. unfold deltabrel, deltafun, add_var, augment_var, statelabelmap_set_to_fun. simpl. 
    repeat StateLabelMapProps.find_analyse; simpl; 
    repeat (StateLabelMapProps.find_tac;  sl_inject); bool_simpl; simpl; trivial.
     rewrite eqb_eq_nat_bool. apply orb_comm. 
     num_analyse; nat_analyse; bool_simpl; trivial; subst; auto. elim H. apply StateLabel.eq_refl. 
     num_analyse; nat_analyse; bool_simpl; trivial; subst; auto. elim H. apply StateLabel.eq_refl.
     rewrite eqb_eq_nat_bool. trivial. 
     apply <-bool_prop_iff; bool_connectors; intuition. 
       num_prop. nat_prop. subst. elim H2. apply StateLabel.eq_refl. 
     apply <-bool_prop_iff; bool_connectors; intuition. 
       num_prop. nat_prop. subst. elim H2. apply StateLabel.eq_refl. 
  Qed.

  Lemma delta_add_var: forall i j n A s t m, 
    delta (add_var i j n A) s m t <-> delta A s m t \/ n=m /\ i=s /\ j=t.
  Proof.
    intros. unfold delta. rewrite deltabrel_add_var. bool_connectors. nat_prop; num_prop. reflexivity.
  Qed.


  Lemma bounded_incr: forall A, bounded A -> bounded (incr A).
  Proof.
    intros A [Hd He]. destruct A. split.
     intros i a j H. destruct (Hd i a j H) as (?&?&?). auto.
     intros i j H. destruct (He i j H) as (?&?). auto.
  Qed.
  Lemma bounded_add_one: forall i j A, belong i A -> belong j A -> bounded A -> bounded (add_one i j A).
  Proof.
    destruct A. intros Hi Hj [Hd He]. split; auto.
    intros s t Hst. apply epsilon_add_one in Hst as [Hst|[-> ->]]; auto.
  Qed.
  Lemma bounded_add_var: forall i j n A, belong i A -> belong j A -> bounded A -> bounded (add_var i j n A).
  Proof.
    intros i j n A Hi Hj [Hd He]. split; auto.
    intros s a t Hst. apply delta_add_var in Hst as [Hst|[-> [-> ->]]]; split; auto; simpl.
     specialize (Hd _ _ _ Hst). destruct A. simpl. num_simpl. eapply lt_le_trans. apply Hd. apply Max.le_max_r.
     specialize (Hd _ _ _ Hst). intuition.
     destruct A. simpl. num_simpl. apply Max.le_max_l.
     destruct A. simpl. auto.
  Qed.
  Local Hint Resolve bounded_incr bounded_add_one bounded_add_var : core.

  Lemma bounded_build: forall a i j A, belong i A -> belong j A -> bounded A -> bounded (build a i j A).
  Proof. induction a; simpl; intros; auto. Qed.
  Local Hint Resolve bounded_build : core.

  Lemma bounded_empty: bounded empty.
  Proof.
    split.
     intros i a j Hij. apply StateSet.mem_2, StateSet.empty_1 in Hij. elim Hij.
     intros i j Hij. elim (epsilon_empty Hij).
  Qed.

  Lemma commute_add_one: forall i f A, 
    bounded A -> belong i A -> belong f A ->
    Algebraic.add_one (nat_of_state i) (nat_of_state f) (preNFA_to_preMAUT A) 
    [=0=] preNFA_to_preMAUT (add_one i f A).
  Proof.
    Opaque add_one.
    intros i f [sA epsA deltaA mlA]. constructor. mx_intros s t Hs Ht. simpl in *. fold_regex.
    rewrite plus_com, plus_assoc. apply plus_compat; trivial.
    rewrite epsilonbrel_add_one. 
    
    case (epsilonbrel (mk sA epsA deltaA mlA) (state_of_nat s) (state_of_nat t)); simpl; 
      nat_analyse; simpl; fold_regex; auto with algebra;
      num_analyse; simpl; fold_regex; auto with algebra; num_omega_false.
    Transparent add_one.
  Qed.

  Lemma labelling_S: forall f n, 
    labelling (Datatypes.S n) f == labelling n f + xif (f n) (RegExp.var (num_of_nat n): regex) 0.
  Proof.
    intros. apply sum_enter_right.
  Qed.
  
  Lemma labelling_empty: forall f, (forall a, f a = false) -> forall n, labelling n f == 0.
  Proof.
    intros. apply sum_zero. intros m _. rewrite H. reflexivity.
  Qed.
  
  Lemma labelling_crop : forall n A i j, 
    bounded A -> max_label A <= n -> 
    labelling (max_label A) (fun a => deltabrel A i a j) == labelling n (fun a => deltabrel A i a j).
  Proof.
    intros n A i j HA H.
    induction H. 
     reflexivity.
     rewrite IHle. rewrite labelling_S.
     case_eq (deltabrel A i (num_of_nat m) j); intro Hij.
      apply HA in Hij. num_omega_false. 
      unfold xif. semiring_reflexivity.
  Qed.

  Lemma leb_S: forall n, leb (S n) xH = false.
  Proof. intros. case le_spec; intro H; trivial. num_simpl. elim (lt_n_O _ H). Qed.
  Hint Rewrite leb_S : bool_simpl.

  Lemma labelling_add_var : forall n A i j s t c, 
    labelling n (fun a => deltabrel (add_var s t c A) i a j) 
    == 
    labelling n (fun a => deltabrel A i a j) + 
    xif (eq_state_bool s i && eq_state_bool t j && leb (S c) n) (RegExp.var c: regex) 0.
  Proof.
    intros. induction n.
     unfold labelling. bool_simpl. simpl. fold_regex. semiring_reflexivity.
     rewrite 2 labelling_S. rewrite IHn. clear IHn.
     rewrite deltabrel_add_var. bool_simpl.
     unfold labelling; simpl. 
     num_analyse; try num_omega_false; subst; simpl; bool_simpl; simpl; fold_regex; try semiring_reflexivity.
     case (deltabrel A i (num_of_nat n) j); simpl; fold_regex; semiring_reflexivity.
  Qed.

  Lemma psurj A: A = mk (size A) (epsilonmap A) (deltamap A) (max_label A).
  Proof. destruct A. reflexivity. Qed.

  Opaque Max.max.
  Lemma commute_add_var: forall n i f A, 
    bounded A -> belong i A -> belong f A ->
    Algebraic.add_var (nat_of_state i) (nat_of_state f) n (preNFA_to_preMAUT A)
    [=0=] preNFA_to_preMAUT (add_var i f n A).
  Proof.
    intros n i f A HA Hi Hf. rewrite (psurj A) at 2. simpl. constructor. mx_intros s t Hs Ht. simpl in *. fold_regex.
    rewrite <- plus_assoc. apply plus_compat; trivial.
    fold (add_var i f n (mk (size A) (epsilonmap A) (deltamap A) (max_label A))).
    rewrite labelling_add_var.
    rewrite (@labelling_crop (Max.max (Datatypes.S (nat_of_num n)) (max_label A))); auto with arith.
    setoid_rewrite eqb_eq_nat_bool. setoid_rewrite id_nat.
    unfold labelling. num_simpl.
    nat_analyse; simpl; fold_regex; try semiring_reflexivity. 
    num_analyse; simpl; fold_regex; try semiring_reflexivity. 
    elim n0. clear. num_simpl. apply Max.le_max_l. 
  Qed.
  Transparent Max.max.

  Lemma not_true_eq_false: forall b, ~ b = true -> b = false.
  Proof. intros [ ]; tauto. Qed.

Opaque equal.
  Lemma commute_incr: forall A, bounded A ->
    Algebraic.incr (preNFA_to_preMAUT A) [=0=] preNFA_to_preMAUT (incr A).
  Proof.
    intros [s ? ? ?] HA. unfold incr, preNFA_to_preMAUT. simpl.  
    replace (nat_of_num(S s)) with (nat_of_state  s +1)%nat by (clear;num_omega).
    constructor. mx_intros i j Hi Hj. simpl. 
    destruct_blocks; trivial; fold_regex;
      (case_eq (epsilonbrel (mk (S s) epsilonmap0 deltamap0 max_label0) (state_of_nat i) (state_of_nat j)); 
        intro Hij; [apply HA in Hij; cbn in *; exfalso; num_omega | 
          symmetry; rewrite labelling_empty; 
            [ auto with algebra | 
              intros a; apply not_true_eq_false; intro F; 
                apply HA in F; simpl in *; exfalso; num_omega ]]).
  Qed.
Transparent equal.

  Local Hint Resolve 
    Algebraic.equal_equiv Algebraic.eval_compat Algebraic.to_MAUT_compat
    Algebraic.add_compat Algebraic.build_compat Algebraic.incr_compat
    : typeclass_instances.

  Lemma commute_build: forall a i f A, 
    bounded A -> belong i A -> belong f A ->
    Algebraic.build a (nat_of_state i) (nat_of_state f) (preNFA_to_preMAUT A)
    [=0=] preNFA_to_preMAUT (build a i f A).
  Proof.
    induction a; intros s t A HA Hs Ht; simpl.    
     apply commute_add_one; auto.
     reflexivity.
     rewrite <- IHa1 by auto. rewrite <- IHa2 by auto. rewrite <- commute_incr by auto. reflexivity.
     rewrite <- IHa1 by auto. rewrite <- IHa2 by auto. reflexivity.
     rewrite <- commute_add_one by auto. rewrite <- IHa by auto. 
      rewrite <- commute_add_one by auto. rewrite <- commute_incr by auto. reflexivity.
     apply commute_add_var; auto.
  Qed.

  Lemma commute_empty: Algebraic.empty [=0=] preNFA_to_preMAUT empty.
  Proof.
    constructor. mx_intros i j Hi Hj. simpl. fold_regex. 
    case_eq (epsilonbrel empty (state_of_nat i) (state_of_nat j)); intro H.
     elim (epsilon_empty H).
     unfold labelling; simpl. fold_regex; semiring_reflexivity.
  Qed.

  Lemma commute_build_empty: forall e, 
    Algebraic.build e 0 1 Algebraic.empty [=0=] preNFA_to_preMAUT (build e 0 1 empty).
  Proof. 
    intros. rewrite <- commute_build, <- commute_empty. reflexivity. 
    apply bounded_empty. 
    reflexivity.
    reflexivity.
  Qed.

  (** The two construction algorithms (high-level / efficient) are equivalent  *)

  Theorem constructions_equiv: forall a, 
    MAUT.equal (eNFA.to_MAUT (X_to_eNFA a)) (Algebraic.X_to_MAUT a).
  Proof.
    intros a. 
    unfold Algebraic.X_to_MAUT.
    rewrite commute_build_empty.
    unfold X_to_eNFA. destruct (build a 0 1 empty). reflexivity.
  Qed.



  Lemma t_rt: forall T R i j, clos_trans T R i j -> clos_refl_trans T R i j.
  Proof. induction 1; eauto using rt_step, rt_trans. Qed.

  Lemma rt_t: forall T R i j, clos_refl_trans T R i j -> i=j \/ clos_trans T R i j.
  Proof. 
    induction 1; auto using t_step.
    intuition subst; eauto using t_trans.
  Qed.


  Lemma epsilon_t_add_one: forall i j A s t, epsilon_t (add_one i j A) s t -> 
    epsilon_t A s t \/ epsilon_rt A s i /\ epsilon_rt A j t.
  Proof.
    induction 1.
     apply epsilon_add_one in H as [H | [-> ->]].
      left. constructor 1. assumption.
      right. split; constructor 2.
     intuition.
      left. econstructor 2; eassumption.
      right; intuition. eauto using rt_trans, t_rt.
      right; intuition. eauto using rt_trans, t_rt.
  Qed.  

  Lemma epsilon_rt_add_one: forall i j A s t, epsilon_rt (add_one i j A) s t -> 
    epsilon_rt A s t \/ epsilon_rt A s i /\ epsilon_rt A j t.
  Proof.
    intros.
    destruct (rt_t H) as [?|H'].
     subst. left. constructor 2.
     destruct (epsilon_t_add_one H'); auto using t_rt.
  Qed.          

  Lemma epsilon_rt_incr: forall A s t, epsilon_rt (incr A) s t -> epsilon_rt A s t.
  Proof. intros A. destruct A. auto. Qed.

  Lemma not_epsilon_rt_incr_left: forall A s, epsilon_rt (incr A) s (size A) -> bounded A -> belong s A -> False.
  Proof.
    intros A s H HA Hs.
    apply epsilon_rt_incr, rt_t in H as [->|H].
     num_omega.
     apply trans_tn1 in H. inversion_clear H.
     apply HA in H0. num_omega.
     apply HA in H0. num_omega.
  Qed.
  Lemma not_epsilon_rt_incr_right: forall A s, epsilon_rt (incr A) (size A) s -> bounded A -> belong s A -> False.
  Proof.
    intros A s H HA Hs.
    apply epsilon_rt_incr, rt_t in H as [<-|H].
     num_omega.
     apply trans_t1n in H. inversion_clear H.
     apply HA in H0. num_omega.
     apply HA in H0. num_omega.
  Qed.
  Ltac not_epsilon := 
    match goal with 
      | H: epsilon_rt (incr _) _ _ |- _ =>
        (elim (not_epsilon_rt_incr_left H) || elim (not_epsilon_rt_incr_right H)); solve [auto]
    end.
     

  Local Hint Constructors non_strict : core.
  Lemma epsilon_rt_build: forall a i j A s t, 
    bounded A ->
    belong i A -> belong j A ->
    belong s A -> belong t A ->
    epsilon_rt (build a i j A) s t -> 
    epsilon_rt A s t \/ (epsilon_rt A s i /\ epsilon_rt A j t /\ non_strict a).
  Proof.
    induction a; simpl; intros u v A s t HA Hu Hv Hs Ht H; auto.

     apply epsilon_rt_add_one in H. intuition auto. 

     apply IHa1 in H; auto. destruct H as [H|[H1 [H2 ?]]].
      apply IHa2 in H; auto. destruct H as [H|[H1 [? ?]]].
       auto using epsilon_rt_incr.
       not_epsilon.
      apply IHa2 in H1; auto. destruct H1 as [H1|[H3 [? ?]]].
       apply IHa2 in H2; auto. destruct H2 as [H2|[? [? ?]]].
        not_epsilon.
        auto using epsilon_rt_incr.
       not_epsilon.

     apply IHa1 in H; auto. destruct H as [H|[H1 [H2 ?]]].
      apply IHa2 in H; intuition auto. 
      apply IHa2 in H1; auto. apply IHa2 in H2; auto. intuition.

     apply epsilon_rt_add_one in H as [H|[H1 H2]].
      apply IHa in H; auto. destruct H as [H|[H1 [H2 ?]]].
       apply epsilon_rt_add_one in H as [H|[H1 H2]].
        auto using epsilon_rt_incr.
        not_epsilon.
       apply epsilon_rt_add_one in H1. intuition (idtac; not_epsilon).
      apply IHa in H1; auto. apply IHa in H2; auto. 
       destruct H1 as [H1|[H3 [H4 ?]]].
        apply epsilon_rt_add_one in H1 as [H1|[H3 H4]]. 2: not_epsilon.
        destruct H2 as [H2|[H3 [H4 ?]]].
         apply epsilon_rt_add_one in H2 as [H2|[H3 H4]]. 
          not_epsilon.
          destruct A. auto.
         apply epsilon_rt_add_one in H4 as [H4|[H5 H6]].
          not_epsilon.
          destruct A. auto.
       apply epsilon_rt_add_one in H3. intuition (idtac; not_epsilon).
       destruct A. auto.
  Qed.
      
  Lemma wf_add_one: forall A i j, wf A -> ~ epsilon_rt A j i -> wf (add_one i j A).
  Proof.
    intros A i j HA Hij.

    assert (Hj: forall v, epsilon_rt A j v -> Acc (transp _ (epsilon (add_one i j A))) v).
     induction v as [v IH] using (well_founded_induction HA); intros Hiv.
     constructor. intros u Hvu. 
      apply epsilon_add_one in Hvu as [Hvu|[-> ->]].
       apply IH. assumption. 
       eauto using rt_trans, rt_step.
      elim Hij. assumption.

    intro v. induction v as [v IH] using (well_founded_induction HA).
    constructor. intros u Hvu.
     apply epsilon_add_one in Hvu as [Hvu|[-> ->]].     
      apply IH. assumption.
      apply Hj. constructor 2.
  Qed.
    
  Theorem wf_build: forall a, strict_star_form a -> 
    forall i j A, bounded A -> belong i A -> belong j A -> wf A -> 
      (epsilon_rt A j i -> strict a) -> wf (build a i j A).
  Proof.
    intros a' a. induction a; simpl; intros u v A HAb Hu Hv HA Ha; auto.

      apply wf_add_one; auto. intro F. apply Ha in F. inversion F.

      destruct A. auto.

      apply wf_add_one; auto. 
       apply IHa; auto.
        apply wf_add_one; auto. 
         destruct A. auto. 
         intro. not_epsilon.
        intro Hnu. apply epsilon_rt_build in Hnu; auto.
        assert (Hnu': epsilon_rt (add_one (size A) v (incr A)) (size A) u). intuition. clear Hnu.
        apply epsilon_rt_add_one in Hnu' as [Hnu|[_ Hvu]].
         not_epsilon.
         apply epsilon_rt_incr in Hvu. apply Ha in Hvu. inversion Hvu.

      apply IHa1; auto. apply IHa2; auto.
       intro F. apply Ha in F. inversion_clear F. assumption.
       intro Hvu. apply epsilon_rt_build in Hvu; auto.
       apply Common.apply in Ha. inversion_clear Ha; auto. intuition.
       
      apply IHa1; auto. apply IHa2; auto.
       destruct A. auto.
       intro F. not_epsilon.
       intro Hnu. apply epsilon_rt_build in Hnu; auto. intuition.
        not_epsilon.
        apply non_strict_not_strict in H2. 
        destruct A. apply Ha in H. inversion_clear H; tauto.
  Qed.


  Lemma wf_empty: wf empty.
  Proof.
    intros x. constructor. intros y Hy. elim (epsilon_empty Hy).
  Qed.

  End protect.
End Correctness.


Import Correctness  Concrete.


(** Correctness of the construction algorithm *)

Theorem correct: forall (a: regex), eNFA.eval (X_to_eNFA a) == a.
Proof.
  intros a. unfold eNFA.eval, comp.
  rewrite constructions_equiv.
  apply Algebraic.construction_correct.
Qed.


Lemma bounded: forall (a: regex), eNFA.bounded (X_to_eNFA a).
Proof.
  intro.
  destruct (@bounded_build a 1 2 empty refl_equal refl_equal bounded_empty) as [Hd He].
  unfold X_to_eNFA.
  rewrite (psurj (build a 0 1 empty)).
  split; simpl.
   intros i b j Hj. apply (Hd b i j). apply StateSet.mem_1, Hj.
   intros i j Hj. apply (He i j). apply StateSet.mem_1, Hj.
   apply belong_build. reflexivity.
   apply belong_build. reflexivity.
Qed.

(** The algorithm produces well-founded eNFAs when starting with expressions in strict star form *)

Theorem well_founded: forall (a: regex), strict_star_form a -> eNFA.well_founded (X_to_eNFA a).
Proof.
  intros a Ha.
  apply incl_wf with (transp _ (epsilon (build a 0 1 empty))).
   apply wf_build.
    exact Ha.
    apply bounded_empty.
    reflexivity.
    reflexivity.
    apply wf_empty.
    intro H. apply trans_rt1n in H. inversion_clear H. elim (epsilon_empty H0).
   intros i j Hij. unfold X_to_eNFA in Hij. destruct (build a 0 1 empty). apply Hij.
Qed.



(** We finally show that expressions sharing the same set of labels
   yield eNFAs with the same max_label (theorem
   [same_labels_max_label] below). We test the equality of the sets of
   labels at the very beginning of [decide_kleene] (for efficiency
   reasons, in case of failure). Having the theorem below allows us to
   remove the need for a test on max_labels later on, in DKA_Merge, so
   that obtaining the completness of the procedure is easier.
*)

Lemma max_label_add_one: forall i j A, max_label (add_one i j A) = max_label A.
Proof. destruct A. reflexivity. Qed.

Lemma max_label_add_var: forall i j a A, max_label (add_var i j a A) = max (S a) (max_label A).
Proof. destruct A. reflexivity. Qed.

Lemma max_label_incr: forall A, max_label (incr A) = max_label A.
Proof. destruct A. reflexivity. Qed.

Lemma build_max_label: forall a i e f A, i < max_label A -> i < max_label (build a e f A).
Proof.
  induction a; intros i e f A Hi; rewrite (psurj A); simpl; auto.
   rewrite max_label_add_one. auto.
   num_simpl. eauto 2 using Max.le_max_r with arith.
Qed.

Lemma collect_max_label: 
  forall a i acc, NumSet.In i (collect a acc) -> 
    forall e f A, nat_of_num i < max_label (build a e f A) \/ NumSet.In i acc.
Proof.
  induction a; simpl; intros i acc Hi e f A; auto.
   eapply IHa1 in Hi as [Hi|Hi]. left. apply Hi. 
   eapply IHa2 in Hi as [Hi|Hi]. left. apply build_max_label, Hi. auto. 
   eapply IHa1 in Hi as [Hi|Hi]. left. apply Hi. 
   eapply IHa2 in Hi as [Hi|Hi]. left. apply build_max_label, Hi. auto. 
   rewrite max_label_add_one. auto. 
   revert Hi. NumSetProps.set_iff. intuition.
   subst. left. destruct A; simpl. num_simpl. eauto using Max.le_max_l with arith.
Qed.

Lemma max_label_collect: 
  forall a i e f A, i < max_label (build a e f A) -> 
    (exists2 j, i<=j & NumSet.In (state_of_nat j) (collect a NumSet.empty)) \/ i < max_label A.
Proof.
  induction a; simpl; intros i e f A Hi; rewrite ?max_label_add_one, ?max_label_incr in *; auto.
   eapply IHa1 in Hi as [[j ? Hj]|Hi]. left. exists j; auto.
    eapply collect_incr_1 in Hj as [?|?]. eassumption. NumSetProps.setdec. 
   eapply IHa2 in Hi as [[j ? ?]|Hi]. left. exists j; auto using collect_incr_2. 
    right. destruct A. assumption. 
   eapply IHa1 in Hi as [[j ? Hj]|Hi]. left. exists j; auto. 
    eapply collect_incr_1 in Hj as [?|?]. eassumption. NumSetProps.setdec. 
   eapply IHa2 in Hi as [[j ? ?]|Hi]. left. exists j; auto using collect_incr_2. right. assumption. 
   eapply IHa in Hi as [Hi|Hi]; auto.
   revert Hi. rewrite max_label_add_one, max_label_incr. auto. 
   revert Hi. rewrite max_label_add_var. num_simpl. apply Max.max_case; auto.
   intro Hi. left. exists (nat_of_num p). auto with arith. num_simpl. auto with set.
Qed.

Lemma inf_leq: forall n m, (forall k, k<n -> k<m) -> n <= m.
Proof. intros [|n] m H. trivial with arith. elim (H n); auto. Qed.

Lemma le_antisym: forall n m: num, n <= m -> m <= n -> n = m.
Proof. intros. num_omega. Qed. 

Lemma max_label_X_to_eNFA a: eNFA.max_label (X_to_eNFA a) = max_label (build a 0 1 empty).
Proof. unfold X_to_eNFA. destruct (build a 0 1 empty). reflexivity. Qed.

Theorem same_labels_max_label: forall a b, same_labels a b = true -> 
  eNFA.max_label (X_to_eNFA a) = eNFA.max_label (X_to_eNFA b).
Proof.
  intros. rewrite 2 max_label_X_to_eNFA.
  cut (forall a b, collect a NumSet.empty [=] collect b NumSet.empty -> 
    max_label (build a 0 1 empty) <= max_label (build b 0 1 empty)). 
  intros H'. apply NumSet.equal_2 in H. apply le_antisym; auto. symmetry in H. auto.

  clear. intros a b H. apply inf_leq. intros c Hc.
  apply max_label_collect in Hc as [[d ? Hd]|?]. 
   rewrite H in Hd. eapply collect_max_label in Hd as [Hd|?].
    eapply le_lt_trans. eassumption. unfold statesetelt_of_nat in Hd. rewrite id_nat in Hd. eassumption.
    NumSetProps.setdec.
    simpl in *. compute in H0. omega_false.
Qed.

(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Properties, definitions, hints and tactics for monoids :
   - [monoid_reflexivity] solves the equational theory
   - [monoid_normalize] normalizes the goal modulo associativity (and neutral elements)
   - [monoid_rewrite] does closed rewrites modulo associativity
   *)

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import BoolView.
Require        Reification.
Set Implicit Arguments.
Unset Strict Implicit.

(* see Structure.txt for the hints policy *)
Hint Extern 0 (equal _ _ _ _) => first [ 
    apply dot_assoc
  | apply dot_neutral_left
  | apply dot_neutral_right
]: algebra.
Hint Extern 2 (equal _ _ _ _) => first [ 
    apply dot_compat; instantiate
]: compat algebra.

(* Hint Resolve @dot_assoc @dot_neutral_left @dot_neutral_right: algebra. *)
(* Hint Resolve @dot_compat: compat algebra. *)
Hint Rewrite @dot_neutral_left @dot_neutral_right using ti_auto: simpl.  


(** Syntactic model to obtain write reflexive tactics 
    this module is "untyped", and uses an untyping theorem
    module T below uses a typed normalisation function.
  *)
Module U.

  (** untyped syntax and equality *)
  Inductive X :=
  | dot: X -> X -> X
  | one: X
  | var: positive -> X.

  Inductive equal: relation X :=
  | refl_one: equal one one
  | refl_var: forall i, equal (var i) (var i)

  | dot_assoc: forall x y z, equal (dot x (dot y z)) (dot (dot x y) z)
  | dot_neutral_left: forall x, equal (dot one x) x
  | dot_neutral_right: forall x, equal (dot x one) x

  | dot_compat: forall x x', equal x x' -> forall y y', equal y y' -> equal (dot x y) (dot x' y')
  | equal_trans: forall x y z, equal x y -> equal y z -> equal x z
  | equal_sym: forall x y, equal x y -> equal y x.

  (** normalisation function *)
  Fixpoint norm_aux acc x :=
    match x with
      | dot y z => norm_aux (norm_aux acc y) z
      | one => acc
      | var _ => match acc with one => x | _ => dot acc x end 
    end.

  Definition norm := norm_aux one.

  (** term comparison *)
  Fixpoint eqb (x y: X): bool := 
    match x,y with
      | dot x1 x2, dot y1 y2 => if eqb x1 y1 then eqb x2 y2 else false
      | one, one => true
      | var i, var j => eq_pos_bool i j 
      | _,_ => false
    end.

  (** decision function *)
  Definition decide x y := eqb (norm x) (norm y).


  (** correctness of the untyped normalisation and decision functions *)
  Section correctness.         (* section used to protect instances *)

    Instance E: Equivalence equal.
    Proof.
      constructor.
      intro x; induction x; constructor; assumption.
      exact equal_sym.
      exact equal_trans.
    Qed.
    Instance dot_compat': Proper (equal ==> equal ==> equal) dot := dot_compat.
  
    Lemma insert q x: equal (dot q x) (norm_aux q x).
    Proof.
      revert q; induction x; intro q; simpl.
      rewrite dot_assoc, IHx1; apply IHx2.
      apply dot_neutral_right.
      destruct q; try reflexivity. 
      apply dot_neutral_left.
    Qed.
  
    Lemma norm_correct: forall x, equal x (norm x).
    Proof.
      intro x; rewrite <- (dot_neutral_left x) at 1.  
      apply insert.
    Qed.
  
    Lemma eqb_spec: forall x y, reflect (x=y) (eqb x y).
    Proof.
      induction x; intros [u v| |j]; simpl; try (constructor; congruence).
      case (IHx1 u); intro; subst; try (constructor; congruence).
      case (IHx2 v); intro; subst; constructor; congruence.
      case eq_pos_spec; intro; subst; constructor; congruence.
    Qed.    
  
    Theorem decide_correct: forall x y, decide x y = true -> equal x y.
    Proof.
      unfold decide. intros x y. case eqb_spec. 
       intros H _. rewrite (norm_correct x), H. symmetry. apply norm_correct. 
       congruence.
    Qed.

  End correctness.


  Definition obind A B: option A -> (A -> option B) -> option B :=
    fun a f => match a with None => None | Some a => f a end.

  Definition pos_eq_dec: forall n m: positive, {n=m}+{n<>m}.
  Proof.
    induction n; destruct m; try (right; intro; discriminate). 
     case (IHn m); [left|right; congruence]. rewrite e; reflexivity.
     case (IHn m); [left|right; congruence]. rewrite e; reflexivity.
     left. reflexivity. 
  Defined.


  (** Erasure function, from typed syntax to untyped syntax *)
  Section erase.

    Import Reification Monoid.
    Context `{env: Env}.

    Fixpoint erase n m (x: X n m): U.X :=
      match x with 
        | dot _ _ _ x y => U.dot (erase x) (erase y)
        | one _ => U.one
        | var i => U.var i
      end.

    Record Pack' := pack' { src': positive; tgt': positive; unpack': X src' tgt' }.    
    Definition cast' p n m (H: n=m) (x: X p n): X p m := eq_rect n (X p) x m H.

    Fixpoint rebuild' l x: option Pack' :=
      match x with
        | U.dot x y => 
          obind (rebuild' l x) (fun x => 
            obind (rebuild' (tgt' x) y) (fun y => 
              match U.pos_eq_dec (tgt' x) (src' y) with
                | left H => Some (pack' (dot (cast' H (unpack' x)) (unpack' y)))
                | right _ => None
              end
            ))
        | U.one => Some (pack' (one l))
        | U.var i => Some (pack' (var i))
      end.


    Definition cast p n m (H: n=m) (x: Classes.X p (typ n)): Classes.X p (typ m) := 
      eq_rect n (fun n => Classes.X p (typ n)) x m H.

    Context {Mo: Monoid_Ops}.
    Fixpoint rebuild l x: option (Pack typ) :=
      match x with
        | U.dot x y => 
          obind (rebuild l x) (fun x => 
            obind (rebuild (tgt_p x) y) (fun y => 
              match U.pos_eq_dec (tgt_p x) (src_p y) with
                | left H => Some (pack (cast H (unpack x) * unpack y))
                | right _ => None
              end
            ))
        | U.one => Some (pack (Classes.one (typ l)))
        | U.var i => Some (val i)
      end.

  End erase.



  (** Untyping theorem for monoids *)
  Section faithful.

    Import Reification Classes.
    Context `{M: Monoid} {env: Env}.
    Notation feval := Monoid.eval.

    (** evaluation predicate *)
    Inductive eval: forall n m, U.X -> X (typ n) (typ m) -> Prop :=
    | e_dot: forall n m p u a v b, @eval n m u a -> @eval m p v b -> eval (U.dot u v) (a*b)
    | e_one: forall n, @eval n n U.one 1
    | e_var: forall i, eval (U.var i) (unpack (val i)).
    Implicit Arguments eval [].
    Local Hint Constructors eval.

    (** evaluation of erased terms *)
    Lemma eval_erase_feval: forall n m a, eval n m (erase a) (feval a).
    Proof. induction a; constructor; trivial. Qed.

    Lemma eval_rebuild: forall n m a a', eval n m a a' -> rebuild n a = Some (pack a').
    Proof.
      induction 1; simpl; auto.
       rewrite IHeval1. simpl. rewrite IHeval2. simpl. case U.pos_eq_dec; intro J.
        unfold cast. rewrite <- (Eqdep_dec.eq_rect_eq_dec pos_eq_dec). reflexivity.
        elim J. reflexivity.
       case (val i). reflexivity.
    Qed. 

    (* inversion lemmas for the eval predicate *)
    Lemma eval_dot_inv: forall n p u v c, eval n p (U.dot u v) c -> 
      exists m, exists a, exists b, c = a*b /\ eval n m u a /\ eval m p v b.
    Proof. intros. dependent destruction H. eauto 6. Qed.
  
    Lemma eval_one_inv: forall n m c, eval n m U.one c -> c [=] one (typ n) /\ n=m.
    Proof. intros. dependent destruction H. split; reflexivity. Qed.
  
    Lemma eval_var_inv: forall n m i c, eval n m (U.var i) c -> c [=] unpack (val i) /\ n=src_p (val i) /\ m=tgt_p (val i).
    Proof. intros. dependent destruction H. intuition reflexivity. Qed.

    (* corresponding inversion tactic *)
    Ltac eval_inversion :=
      repeat match goal with 
               | H : eval _ _ ?u _ |- _ => eval_inversion_aux H u 
             end
      with eval_inversion_aux H u :=
        let H1 := fresh in 
          match u with 
            | U.dot _ _ => destruct (eval_dot_inv H) as (?&?&?&H1&?&?); subst; try rewrite H1
            | U.one => destruct (eval_one_inv H) as [H1 ?]; auto; subst; apply eqd_inj in H1; subst
            | U.var _ => destruct (eval_var_inv H) as (H1&?&?); auto; subst; apply eqd_inj in H1; subst
          end; clear H.
  
    (* injectivity of types, on the left *)
    Lemma eval_type_inj_left: forall n n' m u a b, eval n m u a -> eval n' m u b -> n=n'.
    Proof.
      intros n n' m u a b H; revert n' b; induction H; intros n' c H'; eval_inversion.
      idestruct (IHeval2 _ _ H3).
      apply (IHeval1 _ _ H2).
    Qed.

    (* injectivity of the evaluation predicate (once types are fixed) *)
    Lemma eval_inj: forall n m u a b, eval n m u a -> eval n m u b -> a=b.
    Proof.
      intros n m u a b H; revert b; induction H; intros; eval_inversion; trivial.
      idestruct (eval_type_inj_left H0 H4).
      rewrite (IHeval1 _ H3).
      rewrite (IHeval2 _ H4).
      reflexivity.
    Qed.

    Lemma and_idem: forall (A: Prop), A -> A/\A. Proof. auto. Qed.

    Ltac split_IHeval :=
      repeat match goal with 
               | H: (forall n m x', eval n m ?x x' -> _) /\ _ ,
                 Hx: eval ?n ?m ?x ?x' |- _ => destruct (proj1 H _ _ _ Hx); clear H
               | H: _ /\ forall n m x', eval n m ?x x' -> _  ,
                 Hx: eval ?n ?m ?x ?x' |- _ => destruct (proj2 H _ _ _ Hx); clear H
             end;
      repeat match goal with 
               | H: (forall n m x', eval n m ?x x' -> _) 
                 /\ (forall n m y', eval n m ?y y' -> _) |- _ => destruct H
             end.

    Lemma equal_eval_aux: forall x y, U.equal x y -> 
      forall n m x', eval n m x x' -> exists2 y', eval n m y y' & x' == y'.
    Proof.
      intros x y H.
      cut ((forall n m x', eval n m x x' -> exists2 y', eval n m y y' & x' == y')
              /\ (forall n m y', eval n m y y' -> exists2 x', eval n m x x' & y' == x')); [tauto| ].
      induction H; (apply and_idem || split); intros n m xe Hx; 
        eval_inversion; split_IHeval;
          eauto with algebra;
            eauto using Graph.equal_trans;
              eauto 6 using Graph.equal_sym with algebra.
    Qed.

    (* "untyping" theorem: equal untyped terms evaluate to equal morphisms *)
    Lemma equal_eval: forall u v, U.equal u v -> 
      forall n m a b, eval n m u a -> eval n m v b -> a == b.
    Proof.
      intros u v H n m a b Ha Hb.
      destruct (equal_eval_aux H Ha) as [b'' Hb' Hab].
      idestruct (eval_inj Hb Hb').
      assumption.
    Qed.

    (* other formulation, using the intermediate reification syntax *)
    Theorem erase_faithful: forall n m (a b: Monoid.X n m), 
      U.equal (erase a) (erase b) -> feval a == feval b.
    Proof. intros. eapply equal_eval; eauto using eval_erase_feval. Qed.

    (* combination with the untyped decision procedure, to get the reflexive tactic *)
    Lemma decide_typed: forall n m (a b: Monoid.X n m), 
      decide (erase a) (erase b) = true -> feval a == feval b.
    Proof. intros. apply erase_faithful, decide_correct. assumption. Qed.

    (* for the monoid_normalize tactic *)
    Lemma normalizer {n} {m} {R} `{T: Transitive (Classes.X (typ n) (typ m)) R} `{H: subrelation _ (equal _ _) R} :
      forall (a b: Monoid.X n m) a' b',
        (* utiliser le prédicat d'évaluation permet d'éviter de repasser en OCaml 
           pour inventer le témoin typé... par contre, le terme de preuve grossit un peu. *)
        (let na := norm (erase a) in eval n m na a') ->
        (let nb := norm (erase b) in eval n m nb b') ->
        R a' b' -> R (feval a) (feval b).
    Proof.
      intros until b'; intros Ha Hb Hab.
      transitivity a'.
       apply H. eapply equal_eval; eauto using eval_erase_feval, norm_correct. 
       rewrite Hab.
       apply H. symmetry. eapply equal_eval; eauto using eval_erase_feval, norm_correct. 
    Qed.

  End faithful.
  Implicit Arguments normalizer [[G] [Mo] [M] [env] [n] [m] [R] [T] [H] a b].
End U.

(** the two reflexive tactics for monoids  *)
Ltac monoid_reflexivity := 
  (try apply equal_leq);       (* only sensible way of handling <== *)
  monoid_reify; intros;
    apply U.decide_typed; 
      vm_compute; (reflexivity || fail "Not a Monoid theorem").

Ltac monoid_normalize :=
  let t := fresh "t" in
  let e := fresh "e" in
  let l := fresh "l" in
  let r := fresh "r" in
  let x := fresh "x" in
  let solve_eval :=
    intro x; vm_compute in x; subst x;
      repeat econstructor;
        match goal with |- U.eval (U.var ?i) _ => eapply (U.e_var (env:=e) i) end
  in
    monoid_reify; intros t e l r;
      eapply U.normalizer;
        [ solve_eval | 
          solve_eval |
            compute [t e Reification.unpack Reification.val Reification.typ 
              Reification.tgt Reification.src Reification.tgt_p Reification.src_p
              Reification.sigma_get Reification.sigma_add Reification.sigma_empty
              FMapPositive.PositiveMap.find FMapPositive.PositiveMap.add
              FMapPositive.PositiveMap.empty ] ];
        try clear t e l r.

(*begintests

Import Reification Classes.
(* Set Printing All. *)

Lemma test_idx: forall `{Monoid} n m (a: Classes.X n m), a*1 == a.
Proof.
  intros.
  monoid_normalize.           (* bugue avec '' *)
  reflexivity.
Qed.
Print Assumptions test_idx.

Lemma test0: forall `{Monoid} n, 1*1*(1*1*1)*1 == 1*(1*(1*1)*(1*one n)).
  intros.
  monoid_reflexivity.
Qed.

Lemma test1: forall `{Monoid} A B (a: X A B) (b: X B A) (c: X A A), c*a*(b*c*1)*a == c*(a*(1*b)*(c*a)).
  intros.
  Time monoid_reflexivity.
Qed.
Print test1.

Lemma test2: forall `{Monoid} A B (a: X A B) (b: X B A) (c: X A A), c*a*(b*c*1)*a == c*(a*(1*b)*(c*a)).
  intros.
  Time monoid_normalize.
  reflexivity.
Qed.
Print test2.

Lemma test3: forall `{Monoid} A B (a: X A B) (b: X B A) (c: X A A), 1*1*(1*1*1)*1 == c*(a*(1*b)*(c*a))*b.
  intros.
  Time monoid_normalize. 
  admit.
Qed.
Print test3.

Lemma test1': forall `{KleeneAlgebra} A B (a: X A B) (b: X B A) (c: X A A), c*a*(b*c#*1)*a <== c*(a*(1*b)*(c#*a)).
  intros.
  Time monoid_reflexivity.
Qed.
Print test1'.

Lemma test2': forall `{KleeneAlgebra} A B (a: X A B) (b: X B A) (c: X A A), c*a*(b*c# *1)*a <== c*(a*(1*b)*(c#*a+a)).
  intros.
  Time monoid_normalize. 
  admit.
Time Qed.
Print test2'.

endtests*)




(** simple ad-hoc tactic for closed rewrites modulo associativity *) 

Section monoid_rewrite_equal.
  Context `{M: Monoid}.

  Lemma add_continuation A B (r: X A B) (p: forall Q, X Q A -> X Q B) (P: Prop):
    ((forall Q (q: X Q A), p _ q == q*r) -> P) -> (forall Q (q: X Q A), p _ q == q*r) -> P.
  Proof. tauto. Qed.

  Lemma add_continuation_1 A0 A1 A2 
    (l1: X A0 A1) (l2: X A1 A2)
    (r: X A0 A2):
    l1*l2 == r -> forall B (q: X B A0), q*l1*l2 == q*r.
  Proof. intros; rewrite <- H; auto with algebra. Qed.

  Lemma add_continuation_2 A0 A1 A2 A3
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3)
    (r: X A0 A3):
    l1*l2*l3 == r -> forall B (q: X B A0), q*l1*l2*l3 == q*r.
  Proof. intros; rewrite <- H; monoid_reflexivity. Qed.

  Lemma add_continuation_3 A0 A1 A2 A3 A4
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4)
    (r: X A0 A4):
    l1*l2*l3*l4 == r -> forall B (q: X B A0), q*l1*l2*l3*l4 == q*r.
  Proof. intros; rewrite <- H; monoid_reflexivity. Qed.

  Lemma add_continuation_4 A0 A1 A2 A3 A4 A5
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4) (l5: X A4 A5)
    (r: X A0 A5):
    l1*l2*l3*l4*l5 == r -> forall B (q: X B A0), q*l1*l2*l3*l4*l5 == q*r.
  Proof. intros; rewrite <- H; monoid_reflexivity. Qed.
End monoid_rewrite_equal.



Section monoid_rewrite_leq.
  Context `{M: IdemSemiRing}.

  (* This lemma cannot be in SemiRing only .. *)
  Instance dot_incr_temp A B C: 
  Proper ((leq A B) ==> (leq B C) ==> (leq A C)) (dot A B C).
  Proof.
    unfold leq; intros x y E x' y' E'.
    rewrite <- E, <- E'.
    rewrite dot_distr_left, 2 dot_distr_right. 
    rewrite <- (plus_assoc (x*x')) at 1.
    rewrite plus_assoc, plus_idem, plus_assoc. 
    reflexivity.
  Qed.

  Lemma add_continuationl A B (r: X A B) (p: forall Q, X Q A -> X Q B) (P: Prop):
    ((forall Q (q: X Q A), p _ q <== q*r) -> P) -> (forall Q (q: X Q A), p _ q <== q*r) -> P.
  Proof. tauto. Qed.

  Lemma add_continuation_1l A0 A1 A2 
    (l1: X A0 A1) (l2: X A1 A2)
    (r: X A0 A2):
    l1*l2 <== r -> forall B (q: X B A0), q*l1*l2 <== q*r.
  Proof. intros; rewrite <- H; monoid_reflexivity. Qed.

  Lemma add_continuation_2l A0 A1 A2 A3
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3)
    (r: X A0 A3):
    l1*l2*l3 <== r -> forall B (q: X B A0), q*l1*l2*l3 <== q*r.
  Proof. intros; rewrite <- H; monoid_reflexivity. Qed.

  Lemma add_continuation_3l A0 A1 A2 A3 A4
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4)
    (r: X A0 A4):
    l1*l2*l3*l4 <== r -> forall B (q: X B A0), q*l1*l2*l3*l4 <== q*r.
  Proof. intros; rewrite <- H; monoid_reflexivity. Qed.

  Lemma add_continuation_4l A0 A1 A2 A3 A4 A5
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4) (l5: X A4 A5)
    (r: X A0 A5):
    l1*l2*l3*l4*l5 <== r -> forall B (q: X B A0), q*l1*l2*l3*l4*l5 <== q*r.
  Proof. intros; rewrite <- H; monoid_reflexivity. Qed.

  Lemma add_continuation_1r A0 A1 A2 
    (l1: X A0 A1) (l2: X A1 A2)
    (r: X A0 A2):
    r <== l1*l2 -> forall B (q: X B A0), q*r <== q*l1*l2.
  Proof. intros; rewrite H; monoid_reflexivity. Qed.

  Lemma add_continuation_2r A0 A1 A2 A3
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3)
    (r: X A0 A3):
    r <== l1*l2*l3 -> forall B (q: X B A0), q*r <== q*l1*l2*l3.
  Proof. intros; rewrite H; monoid_reflexivity. Qed.

  Lemma add_continuation_3r A0 A1 A2 A3 A4
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4)
    (r: X A0 A4):
    r <== l1*l2*l3*l4 -> forall B (q: X B A0), q*r <== q*l1*l2*l3*l4.
  Proof. intros; rewrite H; monoid_reflexivity. Qed.

  Lemma add_continuation_4r A0 A1 A2 A3 A4 A5
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4) (l5: X A4 A5)
    (r: X A0 A5):
    r <== l1*l2*l3*l4*l5 -> forall B (q: X B A0), q*r <== q*l1*l2*l3*l4*l5.
  Proof. intros; rewrite H; monoid_reflexivity. Qed.
End monoid_rewrite_leq.


Ltac add_continuation H H' := fail "todo: generic add_continuation";
  let Q := fresh "Q" in
  let q := fresh "q" in
  let r' := fresh "r" in
    match type of H with
      | equal ?A ?B ?l ?r =>
        (eapply (@add_continuation _ _ r); 
          [ | 
            intros Q q;
            eapply equal_trans; [ | apply (dot_compat (equal_refl q) H)]; instantiate; (* rewrite <- H *)
(*             MonoidQuote.simpl_term_by (q;l) Free.normalize; *)
            instantiate;
            match goal with |- equal _ _ _ ?body => 
              set (r':=body);
              pattern Q, q in r'; cbv delta [r']; 
              reflexivity
            end
          ]; cbv beta; intro H'
        ) || fail 1 "Bug in [Monoid.add_continuation]"
      | _ => fail 1 "Not an equality"
    end.



Ltac _monoid_rewrite_equal H :=
  first [
    setoid_rewrite (add_continuation_1 H) |
    setoid_rewrite (add_continuation_2 H) |
    setoid_rewrite (add_continuation_3 H) |
    setoid_rewrite (add_continuation_4 H) |
    setoid_rewrite H |
    let H' := fresh in
      add_continuation H H'; 
      setoid_rewrite H'; clear H'
  ].

Ltac monoid_rewrite H :=
  lazymatch type of H with
    | _ == _ => _monoid_rewrite_equal H
    | _ <== _ =>
      first [
        setoid_rewrite (add_continuation_1l H) |
        setoid_rewrite (add_continuation_2l H) |
        setoid_rewrite (add_continuation_3l H) |
        setoid_rewrite (add_continuation_4l H) |
        setoid_rewrite H |
          let H' := fresh in
            add_continuation H H'; 
            setoid_rewrite <- H'; clear H'
      ]
    | _ => fail 1 "Not an (in)equality"
  end.

Tactic Notation "monoid_rewrite" "<-" constr(H) :=
  lazymatch type of H with
    | _ == _ => _monoid_rewrite_equal (equal_sym H)
    | _ <== _ =>
      first [
        setoid_rewrite <- (add_continuation_1r H) |
        setoid_rewrite <- (add_continuation_2r H) |
        setoid_rewrite <- (add_continuation_3r H) |
        setoid_rewrite <- (add_continuation_4r H) |
        setoid_rewrite <- H |
          let H' := fresh in
            add_continuation H H'; 
            setoid_rewrite <- H'; clear H'
      ]
    | _ => fail 1 "Not an (in)equality"
  end.
  

(*begintests
Section monoid_rewrite_tests.

  Require Import SemiLattice.
  Context `{ISR: IdemSemiRing}.

  Variable A: T.
  Variables a b c d e: X A A.

  Hypothesis H1:  a*b*c == a.
  Hypothesis H1': a*b*c <== a.
  Hypothesis H3:  a == e*c.
  Hypothesis H3': a <== e*c.
  Hypothesis H4:  a*(b+e)*c <== c.

  Instance dot_incr_temp' A B C: 
  Proper ((leq A B) ==> (leq B C) ==> (leq A C)) (dot A B C).
  Proof.
    unfold leq; intros x y E x' y' E'.
    rewrite <- E, <- E'.
    rewrite dot_distr_left, 2 dot_distr_right; aci_reflexivity.
  Qed.

  Goal a+d*a*b*c*d == a+d*e*c*d.
    monoid_rewrite H1.
    monoid_rewrite <- H3.
    reflexivity.
  Qed.

  Goal e*a*b*c+d*a*b*c == e*a+d*a.
    monoid_rewrite H1.
    reflexivity.
  Qed.

  Goal a+d*a*b*c*d <== a+d*e*c*d.
    monoid_rewrite H1'.
    monoid_rewrite <- H3'.
    reflexivity.
  Qed.

  Goal a+d*a*(b+e)*c*d <== a+d*c*d.
    monoid_rewrite H4.
    set (x:=c) at 1; monoid_rewrite <- H4.
  Abort.
  
End monoid_rewrite_tests.
endtests*)


(** Various properties about monoids and finite iterations *)
Section Props1.
  
  Context `{M: Monoid}.

  Fixpoint iter A (a: X A A) n := 
    match n with
      | 0 => 1
      | S n => a * iter a n
    end.

  Variables A B C: T.
     
  Lemma iter_once (a: X A A): iter a 1 == a.
  Proof. intros; simpl; apply dot_neutral_right. Qed.
        
  Lemma iter_split (a: X A A): forall m n, iter a (m+n) == iter a m * iter a n.
  Proof.
    induction m; intro n; simpl.
    monoid_reflexivity.
    rewrite IHm; monoid_reflexivity.
  Qed.
      
  Lemma iter_swap (a: X A A): forall n, a * iter a n == iter a n * a.
  Proof.
    intros until n.
    rewrite <- (iter_once a) at 4.
    rewrite <- iter_split.
    rewrite plus_comm.
    reflexivity.
  Qed.
  
  Lemma iter_swap2 (a: X A B) b: forall n, a * iter (b*a) n == iter (a*b) n * a.
  Proof.
    induction n; simpl.
    monoid_reflexivity.
    monoid_rewrite IHn.
    monoid_reflexivity.
  Qed.
  
  Lemma iter_compat n (a b: X A A): a==b -> iter a n == iter b n.
  Proof.
    intros E; induction n; simpl.
    reflexivity.
    rewrite IHn, E; reflexivity.
  Qed.
  
  Lemma xif_dot: forall b (x y: X A B) (z: X B C), xif b x y * z == xif b (x*z) (y*z).
  Proof. intros. destruct b; trivial. Qed.

  Lemma dot_xif: forall b (x y: X B A) (z: X C B), z * xif b x y == xif b (z*x) (z*y).
  Proof. intros. destruct b; trivial. Qed.
  
End Props1.


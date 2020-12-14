(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Properties, definitions, hints and tactics for monoids.
   In particular, [monoid_rewrite] does closed rewriting modulo
   associativity *)

Require Import Common.
Require Import Classes.
Require Import Graph.
Require Import BoolView.

Set Implicit Arguments.
Unset Strict Implicit.

Global Hint Extern 0 (equal _ _ _ _) => first [ 
    apply dot_assoc
  | apply dot_neutral_left
  | apply dot_neutral_right
]: algebra.
Global Hint Extern 2 (equal _ _ _ _) => first [ 
    apply dot_compat; instantiate
]: compat algebra.

(* Hint Resolve @dot_assoc @dot_neutral_left @dot_neutral_right: algebra. *)
(* Hint Resolve @dot_compat: compat algebra. *)
Hint Rewrite @dot_neutral_left @dot_neutral_right using ti_auto: simpl.  


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
  Proof. intros. rewrite <- H, 2dot_assoc. reflexivity. Qed.

  Lemma add_continuation_3 A0 A1 A2 A3 A4
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4)
    (r: X A0 A4):
    l1*l2*l3*l4 == r -> forall B (q: X B A0), q*l1*l2*l3*l4 == q*r.
  Proof. intros; rewrite <- H, 3dot_assoc. reflexivity. Qed.

  Lemma add_continuation_4 A0 A1 A2 A3 A4 A5
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4) (l5: X A4 A5)
    (r: X A0 A5):
    l1*l2*l3*l4*l5 == r -> forall B (q: X B A0), q*l1*l2*l3*l4*l5 == q*r.
  Proof. intros; rewrite <- H, 4dot_assoc. reflexivity. Qed.
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
  Proof. intros; rewrite <- H, dot_assoc. reflexivity. Qed.

  Lemma add_continuation_2l A0 A1 A2 A3
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3)
    (r: X A0 A3):
    l1*l2*l3 <== r -> forall B (q: X B A0), q*l1*l2*l3 <== q*r.
  Proof. intros; rewrite <- H, 2dot_assoc. reflexivity. Qed.

  Lemma add_continuation_3l A0 A1 A2 A3 A4
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4)
    (r: X A0 A4):
    l1*l2*l3*l4 <== r -> forall B (q: X B A0), q*l1*l2*l3*l4 <== q*r.
  Proof. intros; rewrite <- H, 3dot_assoc. reflexivity. Qed.

  Lemma add_continuation_4l A0 A1 A2 A3 A4 A5
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4) (l5: X A4 A5)
    (r: X A0 A5):
    l1*l2*l3*l4*l5 <== r -> forall B (q: X B A0), q*l1*l2*l3*l4*l5 <== q*r.
  Proof. intros; rewrite <- H, 4dot_assoc. reflexivity. Qed.

  Lemma add_continuation_1r A0 A1 A2 
    (l1: X A0 A1) (l2: X A1 A2)
    (r: X A0 A2):
    r <== l1*l2 -> forall B (q: X B A0), q*r <== q*l1*l2.
  Proof. intros; rewrite H, dot_assoc. reflexivity. Qed.

  Lemma add_continuation_2r A0 A1 A2 A3
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3)
    (r: X A0 A3):
    r <== l1*l2*l3 -> forall B (q: X B A0), q*r <== q*l1*l2*l3.
  Proof. intros; rewrite H, 2dot_assoc. reflexivity. Qed.

  Lemma add_continuation_3r A0 A1 A2 A3 A4
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4)
    (r: X A0 A4):
    r <== l1*l2*l3*l4 -> forall B (q: X B A0), q*r <== q*l1*l2*l3*l4.
  Proof. intros; rewrite H, 3dot_assoc. reflexivity. Qed.

  Lemma add_continuation_4r A0 A1 A2 A3 A4 A5
    (l1: X A0 A1) (l2: X A1 A2) (l3: X A2 A3) (l4: X A3 A4) (l5: X A4 A5)
    (r: X A0 A5):
    r <== l1*l2*l3*l4*l5 -> forall B (q: X B A0), q*r <== q*l1*l2*l3*l4*l5.
  Proof. intros; rewrite H, 4dot_assoc. reflexivity. Qed.
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
    rewrite dot_distr_left, 2 dot_distr_right. 
    (* Fail aac_reflexivity.       (* BUG *) *)
    rewrite !plus_assoc, plus_idem. reflexivity.
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
    auto with algebra. 
    rewrite IHm. auto with algebra.
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
     rewrite dot_neutral_left. trivial with algebra.
     monoid_rewrite IHn. rewrite 2 dot_assoc. reflexivity.
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


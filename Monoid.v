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
Require Import Graph.
Require Import SemiLattice.
Require        Quote. 
Set Implicit Arguments.
Unset Strict Implicit.

(* cf. Structure.txt pour la politique des hints *)
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


(* monoide libre non type, genere par nat *)
Module Free.
  Inductive X :=
  | dot: X -> X -> X
  | one: X
  | var: nat -> X
    .

  Inductive equal: X -> X -> Prop :=
  | refl_one: equal one one
  | refl_var: forall i, equal (var i) (var i)

  | dot_assoc: forall x y z, equal (dot x (dot y z)) (dot (dot x y) z)
  | dot_neutral_left: forall x, equal (dot one x) x
  | dot_neutral_right: forall x, equal (dot x one) x

  | dot_compat: forall x x', equal x x' -> forall y y', equal y y' -> equal (dot x y) (dot x' y')
  | equal_trans: forall x y z, equal x y -> equal y z -> equal x z
  | equal_sym: forall x y, equal x y -> equal y x  
    .

  Lemma equal_refl: forall x, equal x x.
  Proof. induction x; constructor; assumption. Qed.

  Add Relation X equal
    reflexivity proved by equal_refl
    symmetry proved by equal_sym
      transitivity proved by equal_trans
        as free_equal_setoid_relation.

  Fixpoint norm_aux acc x :=
    match x with
      | dot y z => norm_aux (norm_aux acc y) z
      | one => acc
      | var _ => match acc with one => x | _ => dot acc x end 
    end.
  Definition norm := norm_aux one.

  Section Protect.
  Instance dot_compat': Proper (equal ==> equal ==> equal) dot := dot_compat.

  Lemma insert q: forall x, equal (dot q x) (norm_aux q x).
  Proof.
    intros q x; revert q; induction x; intro q; simpl.
    rewrite dot_assoc, IHx1; apply IHx2.
    apply dot_neutral_right.
    destruct q; try reflexivity. 
    apply dot_neutral_left.
  Qed.

  Lemma normalize: forall x, equal x (norm x).
  Proof.
    intro x; rewrite <- (dot_neutral_left x) at 1.  
    apply insert.
  Qed.

  Lemma reflect: forall x y, norm x = norm y -> equal x y.
  Proof.
    intros x y H.
    eapply equal_trans; [apply normalize|].
    eapply equal_trans; [|symmetry; apply normalize].
    rewrite H; reflexivity.
  Qed.
  End Protect.



End Free.

(* module d'evaluation depuis le monoid libre, pour Quote *)
Module FreeEval. 
Section Params.

  Context `{M: Monoid}.

  Section Env.
    Variables s t: nat -> T.
    Variable f: forall i, X (s i) (t i).
  
    Inductive eval: forall A B, Free.X -> X A B -> Prop :=
    | e_one: forall A, @eval A A Free.one 1
    | e_dot: forall A B C x y x' y', 
                 @eval A B x x' -> @eval B C y y' -> @eval A C (Free.dot x y) (x'*y')
    | e_var: forall i, @eval (s i) (t i) (Free.var i) (f i).
    Implicit Arguments eval [].
    Hint Local Constructors eval.
    
    Lemma eval_dot_inv: forall A C x y z, eval A C (Free.dot x y) z -> 
      exists B, exists x', exists y', JMeq z (x'*y') /\ eval A B x x' /\ eval B C y y'.
    Proof. intros. dependent destruction H. eauto 6. Qed.
  
    Lemma eval_one_inv: forall A B z, eval A B Free.one z -> JMeq z (one A) /\ A=B. 
    Proof. intros. dependent destruction H. auto. Qed.
  
    Lemma eval_var_inv: forall A B i z, eval A B (Free.var i) z -> JMeq z (f i) /\ A=s i /\ B=t i.
    Proof. intros. dependent destruction H. auto. Qed.
 
(*     Ltac destruct_or_rewrite H :=  *)
(*     (* c'est pas tres satisfaisant, mais un coup il faut faire destruct, un coup case,  *)
(*        un coup rewrite, et parfois subst...  *) *)
(*       subst; try ((rewrite H || case H); clear H). *)

    (* inversion récursive d'hypothèses d'évaluation *)
    Ltac eval_inversion :=
      repeat match goal with 
               | H : eval _ _ ?x _ |- _ => eval_inversion_aux H x 
             end
      with eval_inversion_aux hyp t :=
        let H1 := fresh in 
          match t with 
            | Free.one => destruct (eval_one_inv hyp) as [H1 ?H]; subst; 
              try (apply JMeq_eq in H1; rewrite H1)
            | Free.dot _ _ => destruct (eval_dot_inv hyp) as (?B & ?x & ?y & H1 & ?H & ?H); subst; 
              try (apply JMeq_eq in H1; rewrite H1)
            | Free.var _ => destruct (eval_var_inv hyp) as (H1 & ?H & ?H); subst; try 
              (apply JMeq_eq in H1; rewrite H1)
          end; clear hyp.

  
    (* semi-injectivité du typage de l'evalutation (ça ne marche que grâce à l'absence de zero) *)
    Lemma eval_type_inj_left: forall A A' B x z z', eval A B x z -> eval A' B x z' -> A=A'.
    Proof.
      intros A A' B x z z' H; revert A' z'; induction H; intros A' z' H';
        eval_inversion; trivial.
      idestruct (IHeval2 _ _ H3).
      apply (IHeval1 _ _ H2).
    Qed.
  
    (* injectivité de l'évaluation *)
    Lemma eval_inj: forall A B x y z, eval A B x y -> eval A B x z -> y=z.
    Proof.
      intros A B x y z H; revert z; induction H; intros; eval_inversion; trivial.
      idestruct (eval_type_inj_left H0 H4).
      rewrite (IHeval1 _ H3).
      rewrite (IHeval2 _ H4).
      reflexivity.
    Qed.

    Lemma and_idem: forall (A: Prop), A -> A/\A.
    Proof. auto. Qed.
  
    (* decomposition et utilisation automatique des hypotheses de recurrence, 
       pour la preuve suivante *)
    Ltac split_IHeval :=
      repeat match goal with 
               | H: (forall A B x', eval A B ?x x' -> _) /\ _ ,
                 Hx: eval ?A ?B ?x ?x' |- _ => destruct (proj1 H _ _ _ Hx); clear H
               | H: _ /\ forall A B x', eval A B ?x x' -> _  ,
                 Hx: eval ?A ?B ?x ?x' |- _ => destruct (proj2 H _ _ _ Hx); clear H
             end;
      repeat match goal with 
               | H: (forall A B x', eval A B ?x x' -> _) 
                 /\ (forall A B y', eval A B ?y y' -> _) |- _ => destruct H
             end.

    (* lemme préliminaire pour le théorème eval_equal *)
    Lemma eval_equal_aux: forall x y, Free.equal x y -> forall A B x', eval A B x x' -> exists2 y', eval A B y y' & x' == y'.
    Proof.
      intros x y H.
      cut ((forall A B x', eval A B x x' -> exists2 y', eval A B y y' & x' == y')
              /\ (forall A B y', eval A B y y' -> exists2 x', eval A B x x' & y' == x')); [tauto| ].
      induction H; (apply and_idem || split); intros A B xe Hx; 
        eval_inversion; split_IHeval;
          eauto with algebra;
            eauto using equal_trans;
              eauto 6 using equal_sym with algebra.
    Qed.
    
    (* on conclut par injectivité de l'évaluation *)
    Theorem eval_equal: forall A B x' y' x y, eval A B x' x -> eval A B y' y -> Free.equal x' y' -> x == y.
    Proof.
      intros A B x' y' x y Hx Hy H.
      destruct (eval_equal_aux H Hx) as [y'' Hy' Hxy].
      idestruct (eval_inj Hy Hy').
      assumption.
    Qed.
(* Axiom Ici, on découvre qu'on a l'axiome JMeq    Print Assumptions eval_equal. *)

  End Env.

  Instance Quote: Quote.EVAL G := {
    X' := Free.X;
    var := Free.var;
    eval := eval
  }.
  Proof.
    intros; split; intro.
    apply eval_var_inv; assumption. 
    intuition; subst; rewrite H0; constructor.
  Defined.
End Params.
End FreeEval.

Ltac monoid_reflexivity := abstract
  lazymatch goal with 
    | |- @equal ?G _ _ _ _ => 
      Quote.quote (FreeEval.Quote (G:=G)) (FreeEval.eval_equal (G:=G));
        apply Free.reflect; vm_compute; (reflexivity || fail "Not a Monoid theorem")
    | |- @leq ?G _ _ _ _ _ => apply equal_leq; (* il ne faut pas dérouler leq, puisque l'on ne gère pas la somme *)
      Quote.quote (FreeEval.Quote (G:=G)) (FreeEval.eval_equal (G:=G));
        apply Free.reflect; vm_compute; (reflexivity || fail "Not a Monoid theorem")
    | _ => fail "Not an (in)equality"
  end.

Ltac monoid_normalize :=
  lazymatch goal with 
    | |- @equal ?G ?A ?B _ _ =>
        Quote.reduce
        (FreeEval.Quote (G:=G))
        (equal_normalizer 
          (E:=FreeEval.Quote (G:=G))
          (FreeEval.eval_equal (G:=G))
           Free.normalize)
    | |- @leq ?G ?SLo ?A ?B _ _ => 
        Quote.reduce
        (FreeEval.Quote (G:=G))
        (leq_normalizer (SLo := SLo)
          (E:=FreeEval.Quote (G:=G))
          (FreeEval.eval_equal (G:=G))
           Free.normalize)
    | _ => fail "Not an (in)equality"
  end.

(*begintests
(* tests pour les tactiques précédentes *)
Goal forall `{Monoid} A B (a: X A B) (b: X B A) (c: X A A), c*a*(b*c*1)*a == c*(a*(1*b)*(c*a)).
  intros.
  monoid_reflexivity.
Qed.

Goal forall `{Monoid} A B (a: X A B) (b: X B A) (c: X A A), c*a*(b*c*1)*a == c*(a*(1*b)*(c*a)).
  intros.
  monoid_normalize.
  reflexivity.
Qed.

Goal forall `{KleeneAlgebra} A B (a: X A B) (b: X B A) (c: X A A), c*a*(b*c#*1)*a <== c*(a*(1*b)*(c#*a)).
  intros.
  (* TODO: repair *)
  monoid_normalize.
  reflexivity.
Qed.
endtests*)



(* rewrite modulo A *) 
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

  (* Damien: je mets ce morphisme ici, bien qu'il soit dans [SemiRing] : 
     il le faut pour prouver les continuations sur leq *)
  Instance dot_incr_temp A B C: 
  Proper ((leq A B) ==> (leq B C) ==> (leq A C)) (dot A B C).
  Proof.
    intros until C; unfold leq; intros x y E x' y' E'.
    rewrite <- E, <- E'.
    rewrite dot_distr_left, 2 dot_distr_right; aci_reflexivity.
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


Ltac add_continuation H H' := fail "TODO: generic add_continuation";
  let Q := fresh "Q" in
  let q := fresh "q" in
  let r' := fresh "r" in
  (* pour optimiser, on pourrait faire a la main les cas ou l est un produit de deux, trois ou quatre termes..., 
     et retomber sur la tactique generique pour les autres *)
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

(*
Goal forall `{M: Monoid} A B (a: X A B) (b: X B A) (c: X A A), a*b*c == c*c -> False.
  intros.
  add_continuation H H'.
Abort.
*)


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
    intros until C; unfold leq; intros x y E x' y' E'.
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

(* finite iterations *)
Fixpoint iter `{Monoid} A (a: X A A) n := 
  match n with
    | 0 => 1
    | S n => a * iter a n
  end.
    
Lemma iter_once `{Monoid} A (a: X A A): iter a 1 == a.
Proof. intros; simpl; apply dot_neutral_right. Qed.
      
Lemma iter_split `{Monoid} A (a: X A A): forall m n, iter a (m+n) == iter a m * iter a n.
Proof.
  induction m; intro n; simpl.
  monoid_reflexivity.
  rewrite IHm; monoid_reflexivity.
Qed.
    
Lemma iter_swap `{Monoid} A (a: X A A): forall n, a * iter a n == iter a n * a.
Proof.
  intros until n.
  rewrite <- (iter_once a) at 4.
  rewrite <- iter_split.
  rewrite plus_comm.
  reflexivity.
Qed.

Lemma iter_swap2 `{Monoid} A B (a: X A B) b: forall n, a * iter (b*a) n == iter (a*b) n * a.
Proof.
  induction n; simpl.
  monoid_reflexivity.
  monoid_rewrite IHn.
  monoid_reflexivity.
Qed.

Lemma iter_compat `{Monoid} n A (a b: X A A): a==b -> iter a n == iter b n.
Proof.
  intros until n; intros A a b E; induction n; simpl.
  reflexivity.
  rewrite IHn, E; reflexivity.
Qed.



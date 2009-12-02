(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id$ i*)

Require        FSets.

Require Import Common.
Require Import Classes.
Require        Quote.
Require Import Graph.

Set Implicit Arguments.
Unset Strict Implicit.


Section leq.
  Context `{SL: SemiLattice}.
  Variables A B: T.

  Global Instance leq_refl: Reflexive (leq A B).
  Proof. intro. apply plus_idem. Qed.

  Global Instance leq_trans: Transitive (leq A B).
  Proof. 
    intros x y z E E'; unfold leq in *.
    rewrite <- E', plus_assoc, E; reflexivity. 
  Qed.

  Global Instance equal_leq: subrelation (equal A B) (leq A B).
  Proof.
    intros x y E; unfold leq; rewrite E; apply plus_idem.
  Qed.

  Global Instance equal_geq: subrelation (equal A B) (inverse (leq A B)).
  Proof. repeat intro; apply equal_leq; auto. Qed.

  Definition leq_antisym: Antisymmetric _ _ (leq A B).
    intros x y H1 H2; unfold leq in *; rewrite <- H2, plus_com, H1; reflexivity. 
  Qed.
End leq.

Hint Extern 0 (leq _ _ _ _) => apply leq_refl.



(* cf. Structure.txt pour la politique des hints *)
Hint Extern 0 (equal _ _ _ _) => first [ 
    apply plus_assoc
  | apply plus_com
  | apply plus_idem
  | apply plus_neutral_left
]: algebra.
Hint Extern 2 (equal _ _ _ _) => first [ 
    apply plus_compat; instantiate
]: compat algebra.

(* Hint Resolve @plus_assoc @plus_idem @plus_com @plus_neutral_left: algebra. *)
(* Hint Resolve @plus_compat: compat algebra. *)
Hint Rewrite @plus_neutral_left @plus_idem using ti_auto: simpl.  



(* monoide libre non type, genere par nat *)
Module Free.
  Inductive X :=
  | zero: X
  | plus: X -> X -> X
  | var: nat -> X
    .

  Inductive equal: X -> X -> Prop :=
  | refl_zero: equal zero zero
  | refl_var: forall i, equal (var i) (var i)

  | plus_neutral_left: forall x, equal (plus zero x) x
  | plus_idem: forall x, equal (plus x x) x
  | plus_assoc: forall x y z, equal (plus x (plus y z)) (plus (plus x y) z)
  | plus_com: forall x y, equal (plus x y) (plus y x)

  | plus_compat: forall x x', equal x x' -> forall y y', equal y y' -> equal (plus x y) (plus x' y')
  | equal_trans: forall x y z, equal x y -> equal y z -> equal x z
  | equal_sym: forall x y, equal x y -> equal y x  
    .

  Lemma equal_refl: forall x, equal x x.
  Proof. induction x; constructor; assumption. Qed.

  Local Hint Resolve equal_refl plus_neutral_left plus_idem plus_assoc plus_com plus_compat equal_trans: algebra.
  Local Hint Immediate equal_sym: algebra.

  Add Relation X equal
    reflexivity proved by equal_refl
    symmetry proved by equal_sym
      transitivity proved by equal_trans
        as free_equal_setoid_relation.

  Module VSet' := FSetList.Make(OrderedTypeEx.Nat_as_OT). (* FSetAVL. *)
  Module FSetHide (X : FSetInterface.S).
    Include X.
  End FSetHide.
  Module VSet := FSetHide VSet'.

  Module VSetProps := FSetProperties.OrdProperties VSet.
  Module VSetDec := FSetDecide.Decide VSet.
  Ltac fsetdec := VSetDec.fsetdec.

  Fixpoint X_to_VSet_aux acc x :=
    match x with
      | plus y z => X_to_VSet_aux (X_to_VSet_aux acc y) z
      | zero => acc
      | var i => VSet.add i acc
    end.

  Definition X_to_VSet := X_to_VSet_aux VSet.empty.

  Definition is_zero x := 
    match x with zero => true | _ => false end.

  Let f := (fun i acc => if is_zero acc then var i else plus acc (var i)).
  Definition VSet_to_X s := VSet.fold f s zero.

  Definition norm p := VSet_to_X (X_to_VSet p).


  Section Protect.

  Instance plus_compat_free: Proper (equal ==> equal ==> equal) plus := plus_compat.
  Typeclasses Opaque plus_compat_free.

  Lemma Is_zero x: is_zero x = true <-> x = zero.
  Proof.
    intro x; destruct x; simpl; intuition discriminate.
  Qed.


  Let Hc: SetoidList.compat_op (@eq nat) equal f.
  Proof.
    intros i j H x y H'; subst; unfold f. 
    case_eq (is_zero x); intro Hx; 
    case_eq (is_zero y); intro Hy. 
    constructor.
    rewrite (proj1 (Is_zero _) Hx) in H'; rewrite <- H'; do 2 constructor.
    rewrite (proj1 (Is_zero _) Hy) in H'; rewrite H'; constructor.
    constructor; trivial; constructor.
  Qed.
    
  Let Ht: SetoidList.transpose equal f.
  Proof. 
    intros i j z; unfold f.
    case_eq (is_zero z); intro Hz; simpl. 
    constructor.
    rewrite <- plus_assoc, (plus_com (var j)); constructor.
  Qed.

  Lemma normalize: forall x, equal x (norm x).
  Proof.
    intro x; rewrite <- (plus_neutral_left x) at 1.  
    unfold norm, X_to_VSet.
    change zero with (VSet_to_X VSet.empty).
    generalize VSet.empty.

    induction x; intro q; simpl.
    rewrite plus_com; apply plus_neutral_left.
    rewrite plus_assoc, IHx1; apply IHx2.

    induction q as [|q1 q2 IH z Hz Hq] using VSetProps.P.set_induction; unfold VSet_to_X.
     rewrite (VSetProps.P.fold_add _ Hc Ht) by fsetdec.
     rewrite VSetProps.P.fold_1b by assumption.
     constructor.

     destruct (VSetProps.P.In_dec n q2) as [Hn|Hn].
      rewrite (VSetProps.add_fold _ Hc _ Hn).
      rewrite <- (VSetProps.P.fold_equal _ Hc Ht _ (VSetProps.P.add_remove Hn)).
      rewrite (VSetProps.P.fold_add _ Hc Ht) by fsetdec.
      unfold f; match goal with |- context[is_zero ?x] => case_eq (is_zero x) end; intro Hx.
      constructor.
      rewrite <- plus_assoc, plus_idem; reflexivity.

      rewrite (VSetProps.P.fold_add _ Hc Ht _ Hn).
      unfold f; match goal with |- context[is_zero ?x] => case_eq (is_zero x) end; intro Hx.
      rewrite (proj1 (Is_zero _) Hx); constructor.
      reflexivity.
  Qed.

  Lemma reflect: forall x y, VSet.equal (X_to_VSet x) (X_to_VSet y) = true -> equal x y.
  Proof.
    intros x y H.
    transitivity (norm x); [ apply normalize | ].
    transitivity (norm y); [ | symmetry; apply normalize ].
    apply VSet.equal_2 in H; unfold norm, VSet_to_X.

    rewrite <- (@VSetProps.P.fold_equal X equal _ _ Hc Ht _ _ _ H).
    reflexivity.
  Qed.

  End Protect.

  (* [clean x] retire tous les zéros du terme [x] (sauf, éventuellement, le dernier...) *)
  Fixpoint clean (x: X): X := 
    match x with
      | plus x y => 
        let x := clean x in
          let y := clean y in
            if is_zero x then y
              else if is_zero y then x
                else plus x y
      | x => x
    end.

  Ltac destruct_if_zero := 
    repeat (
      repeat match goal with
               | H: is_zero ?x = _ |- _ => rewrite H
               | H: is_zero ?x = _, H': context[is_zero ?x] |- _ => rewrite H in H'
             end;
      repeat match goal with 
               | |- context[is_zero ?x] => 
                 match x with 
                   | context[is_zero ?y] => fail 1
                   |  _ => case_eq (is_zero x); let Z := fresh "Z" in intro Z
                 end
             end).

  Ltac replace_zeros :=
    repeat match goal with
             | H: is_zero ?x = true |- _ => rewrite (proj1 (Is_zero x) H) in *; clear H
           end.



  (* idempotence de [clean] *)
  Lemma clean_idem: forall x, clean (clean x) = clean x.
  Proof.
    intro x; induction x; trivial; simpl.
    destruct_if_zero; trivial; simpl.
    rewrite IHx1, IHx2; destruct_if_zero; trivial.
  Qed. 

  (* deux termes égaux se nettoient en [zero] en même temps *)
  Lemma equal_clean_zero_equiv : forall x y, equal x y -> is_zero (clean x) = is_zero (clean y).
  Proof.
    intros; induction H; trivial; simpl;
      destruct_if_zero; trivial; discriminate.
  Qed.

  (* conséquence de [equal_clean_zero_equiv], utile pour les analyses de cas ci-dessous*)
  Lemma sequal_clean_zero_equiv x y : equal (clean x) (clean y) -> is_zero (clean x) = is_zero (clean y).
  Proof.
    intros; rewrite <- (clean_idem x), <- (clean_idem y).
    apply equal_clean_zero_equiv; assumption.
  Qed.

  (* lemme de factorisation: toute preuve d'égalité se réduit par nettoyage en une preuve d'égalité des nettoyés *)
  Theorem equal_to_sequal : forall x y, equal x y -> equal (clean x) (clean y).
  Proof.
    intros; induction H; try apply equal_refl; simpl; 
      destruct_if_zero; auto with algebra; 
        solve [
          replace_zeros; auto with algebra 
          |
          repeat match goal with 
                   H: equal (clean ?x) (clean ?y) |- _ => apply sequal_clean_zero_equiv in H
                 end; destruct_if_zero; discriminate 
          |
          eauto 2 with algebra 
        ].
  Qed.

End Free.

(* module d'evaluation depuis le monoid libre, pour Quote *)
Module FreeEval. 
Section Params.

  Context `{SL: SemiLattice}.

  Section Env.
    (* le typage est trivial pour les semilattices, mais ça permet d'utiliser quote...  *)
    Variables s t: nat -> T.
    Variable f: forall i, X (s i) (t i).
  
    Inductive eval: forall A B, Free.X -> X A B -> Prop :=
    | e_zero: forall A B, @eval A B Free.zero 0
    | e_plus: forall A B x y x' y', 
                 @eval A B x x' -> @eval A B y y' -> @eval A B (Free.plus x y) (x'+y')
    | e_var: forall i, @eval (s i) (t i) (Free.var i) (f i).
    Implicit Arguments eval [].
    Local Hint Constructors eval.
    
    Lemma eval_plus_inv: forall A B x y z, eval A B (Free.plus x y) z -> 
      exists x', exists y', z=x'+y' /\ eval A B x x' /\ eval A B y y'.
    Proof. intros. dependent destruction H. eauto. Qed.

    Lemma eval_zero_inv: forall A B z, eval A B Free.zero z -> z=0. 
    Proof. intros. dependent destruction H. auto. Qed.
  
    Lemma eval_var_inv: forall A B i z, eval A B (Free.var i) z -> JMeq z (f i) /\ A=s i /\ B=t i.
    Proof. intros. dependent destruction H. auto. Qed.
 
    (* inversion récursive d'hypothèses d'évaluation *)
    Ltac eval_inversion :=
      repeat match goal with 
               | H : eval _ _ ?x _ |- _ => eval_inversion_aux H x 
             end
      with eval_inversion_aux hyp t :=
        let H1 := fresh in 
          match t with 
            | Free.zero => pose proof (eval_zero_inv hyp); subst
            | Free.plus _ _ => destruct (eval_plus_inv hyp) as (?x & ?y & H1 & ?H & ?H); try rewrite H1
            | Free.var _ => destruct (eval_var_inv hyp) as (H1 & ?H & ?H); subst; try apply JMeq_eq in H1; 
              try rewrite H1
          end; clear hyp.

    (* semi-injectivité du typage de l'evalutation : pour les nettoyés seulement *)
    Lemma eval_type_inj_left: forall A A' B x z z', eval A B x z -> eval A' B x z' -> A=A' \/ Free.is_zero (Free.clean x) = true.
    Proof.
      intros A A' B x z z' H; revert A' z'; induction H; intros A' z' H';
        eval_inversion; auto.
      destruct (IHeval2 _ _ H3) as [|Hx]; auto.
      destruct (IHeval1 _ _ H2) as [|Hy]; auto.
      right; simpl. rewrite Hy. assumption.
    Qed.
    
    (* qui se nettoie en zero s'evalue en zero *)
    Lemma eval_clean_zero: forall x, Free.is_zero (Free.clean x) = true -> forall A B z, eval A B x z -> z==0.
    Proof.
      induction x; simpl; intros H A B z Hz; try discriminate; eval_inversion.
      reflexivity.

      (* TODO: preuve bof, il faudrait que destruct_if_zero gère mieux ça *)
      case_eq (Free.is_zero (Free.clean x1)); intro Z1; rewrite Z1 in H.
      rewrite (IHx2 H _ _ _ H2), (IHx1 Z1 _ _ _ H1); apply plus_idem.

      case_eq (Free.is_zero (Free.clean x2)); intro Z2; rewrite Z2 in H.
      rewrite H in Z1; discriminate.
      discriminate.
(*      
      Free.destruct_if_zero.
      rewrite (IHx1 e _ _ _ H1), (IHx2 H _ _ _ H2); apply plus_idem.
*)
    Qed.


    (* le nettoyage préserve l'évaluation *)
    Lemma eval_clean: forall A B x y, eval A B x y -> exists2 z, eval A B (Free.clean x) z & y==z.
    Proof.
      intros A B x y H; induction H; simpl.

      exists 0; auto.

      Free.destruct_if_zero.
       destruct IHeval2 as [y'' Hy'' Hy]; exists y''; auto.
       rewrite (eval_clean_zero Z H), Hy; apply plus_neutral_left.

       destruct IHeval1 as [x'' Hx'' Hx]; exists x''; auto.
       rewrite (eval_clean_zero Z0 H0), Hx; rewrite plus_com; auto with algebra.

       destruct IHeval1; destruct IHeval2; eauto with compat.
             
      exists (f i); auto.
    Qed.


    (* injectivité de l'évaluation *)
    Lemma eval_inj: forall A B x y z, eval A B x y -> eval A B x z -> y=z.
    Proof. intros. dependent induction H; depelim H0; auto. 
      rewrite (IHeval1 x'0), (IHeval2 y'0); auto.
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
  
    (* lemme préliminaire pour le théorème eval_equal: validité de l'égalité forte *)
    Lemma eval_equal_aux: forall x y, Free.equal x y -> forall A B x', eval A B x x' -> exists2 y', eval A B y y' & x'==y'.
    Proof.
      intros x y H.
      cut ((forall A B x', eval A B x x' -> exists2 y', eval A B y y' & x'==y')
              /\ (forall A B y', eval A B y y' -> exists2 x', eval A B x x' & y'==x')); [tauto| ].
      induction H; (apply and_idem || split); intros A B xe Hx;
        eval_inversion; split_IHeval;
        eauto with algebra; eauto 3 using equal_trans.
      
      (* plus idem *)
      eexists; eauto.
      rewrite (eval_inj H0 H1); apply plus_idem.
    Qed.
    
        
    (* on conclut par injectivité de l'évaluation *)
    Theorem eval_equal: forall A B x' y' x y, eval A B x' x -> eval A B y' y -> Free.equal x' y' -> x==y.
    Proof.
      intros A B x' y' x y Hx Hy H.
      destruct (eval_clean Hx) as [x1 Hx1 Hx1'].
      destruct (eval_clean Hy) as [y1 Hy1 Hy1'].
      destruct (eval_equal_aux (Free.equal_to_sequal H) Hx1) as [y2 Hy2 Hy2'].
      rewrite Hx1', Hy1', Hy2'.
      rewrite (eval_inj Hy2 Hy1).
      reflexivity.
    Qed.
  
  End Env.

  Instance Quote: Quote.EVAL G := {
    X' := Free.X;
    var := Free.var;
    eval := eval
  }.
  Proof.
    intros; split; intro.
    apply eval_var_inv; assumption.
    intuition; subst. apply JMeq_eq in H0. rewrite H0; constructor.
  Defined.
End Params.
End FreeEval.

Section normalizers.
  Context {G: Graph} (E: Quote.EVAL G).

  Variable equal': relation Quote.X'.
  Hypothesis eval_equal: forall s t f A B x' y' x y,
    Quote.eval s t f A B x' x ->
    Quote.eval s t f A B y' y ->
    equal' x' y' -> x == y.

  Variable norm: Quote.X' -> Quote.X'.
  Hypothesis normalize: forall x, equal' x (norm x).

  Lemma equal_normalizer: 
    forall s t f A B x' y' x y nx ny,
      Quote.eval s t f A B x' x ->
      Quote.eval s t f A B y' y ->
      Quote.eval s t f A B (norm x') nx ->
      Quote.eval s t f A B (norm y') ny ->
      nx==ny -> x==y.
  Proof.
    intros until ny; intros Hx Hy Hnx Hny H.
    rewrite (eval_equal Hx Hnx) by apply normalize.
    rewrite (eval_equal Hy Hny) by apply normalize.
    assumption.
  Qed.

  Context {SLo} {SL: @SemiLattice G SLo}.

  Lemma leq_normalizer:
    forall s t f A B x' y' (x y nx ny: X A B),
      Quote.eval s t f A B x' x ->
      Quote.eval s t f A B y' y ->
      Quote.eval s t f A B (norm x') nx ->
      Quote.eval s t f A B (norm y') ny ->
      nx<==ny -> x<==y.
  Proof.
    intros until ny; intros Hx Hy Hnx Hny H.
    rewrite (eval_equal Hx Hnx) by apply normalize.
    rewrite (eval_equal Hy Hny) by apply normalize.
    assumption.
  Qed.
End normalizers.

Ltac get_Graph := 
  lazymatch goal with 
    | |- @equal ?G _ _ _ _ => G
    | |- @leq ?G _ _ _ _ _ => G
    | _ => fail 1 "Not an (in)equality"
  end.

Ltac aci_reflexivity := abstract
  let G := get_Graph in
    Quote.quote (FreeEval.Quote (G:=G)) (FreeEval.eval_equal (G:=G));
      apply Free.reflect; vm_compute; (reflexivity || fail "Not an ACI theorem").

Ltac aci_normalize :=
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
Section tests
  (* tests pour les tactiques précédentes *)
  Goal forall `{SemiLattice} A B (a b c: X A B), c+a+(b+c+0)+a == c+(a+0+(0+b)+(c+a)).
    intros.
    aci_reflexivity.
  Qed.
  
  Goal forall `{SemiLattice} A B (a b c: X A B), c+a+0+a <== c+(a+0+(0+b)+(c+a)).
    intros.
    try aci_reflexivity.
    unfold leq; aci_reflexivity.
  Qed.
  
  Goal forall `{SemiLattice} A B (a b c: X A B), c+a+(b+c+0)+a == c+(a+0+(0+b)+(c+a)).
    intros.
    aci_normalize.
    reflexivity.
  Qed.
  
  Goal forall `{IdemSemiRing} A (a b c: X A A), c+a*b+(b+c+0)+a <== c+(a+0+(0+b)+(c+a*b)).
    intros.
    aci_normalize.
    reflexivity.
  Qed.
  
  Goal forall `{KleeneAlgebra} A (a b c: X A A), c+a*b+(b#+c+0)+a <== c+(a+0+(0+b#)+(c+a*b)).
    intros.
    aci_reflexivity.
  Qed.
  
  Goal forall `{KleeneAlgebra} A (a b c: X A A), c+a*b+(b#+c+0)+a == c+(a+0+(0+b#)+(c+a*b)).
    intros.
    aci_normalize.
    reflexivity.
  Qed.
End tests
endtests*)



(****** rewrite AC **********)
(* peigne prend deux termes qui apparaissent dans le but, et les
   essaie de les agglomerer : on fait une disjonction de cas, suivant
   l'ordre dans lequel ils apparaissent, puis, on parcours le but,
   pour les mettre cote a cote
   plus_assoc :  x + (y + z) == x + y + z 
   un terme a pour structure (q + a) + b 
   *)      

Lemma switch `{SemiLattice} A B (a b c : X A B) : (a+b)+c == (a+c)+b.
Proof. intros. aci_reflexivity. Qed.
    
Ltac peigne a b n :=
  match goal with 
    | |- context [?q + b] => 
      match q with 
        | context [a] => ( peigne_aux (q+b) a b  (* || idtac "fail 1" q b a b *) ) ; (try set (n := a+b))
      end
    | |- context [?q + a] =>
      match q with 
        | context [b] => ( peigne_aux (q+a) b a  (* || idtac "fail 2" *) ) ; try (rewrite (plus_com b a); set (n := a+b))
      end
    | _ => fail 0 "failed to find " a " and " b " in the goal"
  end
with 
  (* [peigne_aux q a b] parcourt q dans lequel apparait a et le met à coté de b sachant que q finit par b*)
  peigne_aux q a b :=
  match q with 
    | (?q'+a)+b => rewrite <- (plus_assoc q' a b)
    | (?q'+?x)+b => rewrite (switch q' x b); peigne_aux (q' +b) a b   
    | a+b => idtac (* on a trouve *)
    | ?q' + ?x => peigne_aux q' a b (* appel recursif : on n'a pas encore vu de b *)
    | ?x => fail x (* ici, on termine par un terme atomique sans avoir vu de a ou de b... *)
  end.

Ltac atomic a :=
  match a with | _ + _ => fail 1 | _ => idtac  end.

(*
   on detruit un motif, jusqu a ce qu'il soit agglomere 
   [agglomere pat n] aggrege les elements du buts qui matchent exactement le terme [pat] sous le nom [n]
   *)
Ltac agglomere_motif pat n :=
  match pat with 
    | ?pat' + ?a => atomic a; 
      let x := fresh "pat" in 
        let x' := fresh "pat_plus_a" in 
          (agglomere_motif pat' x;
            peigne x a x';
            subst x; set (n := x'); subst x')
    | ?a => atomic a; set (n := a)
    | _ => fail 0 "failed to find the term: " pat 
  end.

Ltac ac_rewrite Li := 
(* Damien: je préfère laisser la possibilité de normaliser soit même *)
(* repeat rewrite plus_assoc; repeat rewrite dot_assoc; *)
(*  aci_normalize;  *)
  lazymatch type of Li with 
    | ?pat == _ => 
      (let n := fresh "ac_rewrite" in agglomere_motif pat n; 
        subst n; rewrite Li
      ) || fail "failed to gather the pattern."
    | ?pat <== _ => 
      (let n := fresh "ac_rewrite" in agglomere_motif pat n; 
        subst n; rewrite Li
      ) || fail "failed to gather the pattern."
    | ?x => fail "Not an (in)equality: " Li ": " x
  end.


(*begintests
Section test_ac_rewrite.
  Context `{ISR: IdemSemiRing}.
  Variable A B : T.
  Variable a b c d e f g: X A B.

  Hypothesis H  : a + b + c+d+e == d.
  Hypothesis H'  : a + b + c+d+e == d.

  Goal a + b + c + d == d.
    peigne a c toto.
    rewrite switch.
  Abort.
  
  Goal a + b + c + d == d. 
    agglomere_motif (a+c+d) toto.
  Abort. 
  
  Goal e + d + a + b  +c <== d.
    ac_rewrite H.
    reflexivity.
  Qed.

  Goal e + d + a + b + e +c <== e+d.
    ac_rewrite H'.
    reflexivity.
  Qed.

  Hypothesis J :  f + g == c.
  Goal e + d + a + b + e + f + g == d.
    aci_normalize.
    ac_rewrite J.
    aci_normalize.
    ac_rewrite H.
    aci_reflexivity.
  Qed.

  Variable C : T.
  Variable h : X B C.
  Goal (f+g)*h + 1*f*h == 1*c*h +1*f*1*h*1.
    ac_rewrite J.
    rewrite !dot_neutral_left, !dot_neutral_right.
    aci_reflexivity.
  Qed.

  Variable i j : X C C.
  Goal (f+g)*h*i*j + (a+b+f+d+g+e)* h *i == c*h*i*j + d*h*i.
    ac_rewrite J.
    ac_rewrite J.
    ac_rewrite H.
    reflexivity.
  Qed.
End test_ac_rewrite.  
endtests*)



(*
  (* tests grippaux pour rewrite ac non clot *)
  Lemma ac_head0: forall p q r, 
    equal (plus p q) r -> 
    forall i, equal (plus (plus i p) q) (plus i r).
  Proof.
    intros p q r H i.
    rewrite <- plus_assoc, H.
    reflexivity.
  Qed.
  Lemma ac_insert0: forall p q r, 
    equal (plus p q) r -> 
    forall i, equal (plus (plus p i) q) (plus r i).
  Proof.
    intros p q r H i.
    rewrite 2 (fun x => plus_com x i).
    apply ac_head0, H.
  Qed.
  Lemma ac_head1: forall p q r, 
    (forall (x: X), equal (plus (p x) (q x)) (r x)) -> 
    forall i x, equal (plus (plus i (p x)) (q x)) (plus i (r x)).
  Proof.
    intros; apply ac_head0; trivial.
  Qed.
  Lemma ac_insert1: forall p q r, 
    (forall (x: X), equal (plus (p x) (q x)) (r x)) -> 
    forall i x, equal (plus (plus (p x) i) (q x)) (plus (r x) i).
  Proof.
    intros; apply ac_insert0; trivial.
  Qed.
  Lemma ac_head2: forall p q r, 
    (forall (x y: X), equal (plus (p x y) (q x y)) (r x y)) -> 
    forall i x y, equal (plus (plus i (p x y)) (q x y)) (plus i (r x y)).
  Proof.
    intros; apply ac_head0; trivial.
  Qed.
  Lemma ac_insert2: forall p q r,
    (forall (x y: X), equal (plus (p x y) (q x y)) (r x y)) -> 
    forall i x y, equal (plus (plus (p x y) i) (q x y)) (plus (r x y) i).
  Proof.
    intros; apply ac_insert0; trivial.
  Qed.
  Lemma ac_head3: forall p q r, 
    (forall (x y z: X), equal (plus (p x y z) (q x y z)) (r x y z)) -> 
    forall i x y z, equal (plus (plus i (p x y z)) (q x y z)) (plus i (r x y z)).
  Proof.
    intros; apply ac_head0; trivial.
  Qed.
  Lemma ac_insert3: forall p q r,
    (forall (x y z: X), equal (plus (p x y z) (q x y z)) (r x y z)) -> 
    forall i x y z, equal (plus (plus (p x y z) i) (q x y z)) (plus (r x y z) i).
  Proof.
    intros; apply ac_insert0; trivial.
  Qed.

  Ltac ac_rewrite4' H := 
    rewrite H || fail "ac_rewrite5' not implemented" .
  Ltac ac_rewrite3' H :=
    rewrite H || ac_rewrite4' (ac_insert3 H).
  Ltac ac_rewrite2' H :=
    rewrite H || ac_rewrite3' (ac_insert2 H).
  Ltac ac_rewrite1' H :=
    rewrite H || ac_rewrite2' (ac_insert1 H).
  Ltac ac_rewrite0' H :=
    rewrite H || ac_rewrite1' (ac_insert0 H).

  Ltac ac_rewrite H :=
    match type of H with
      | equal _ _ => ac_rewrite0' H || ac_rewrite1' (ac_head0 H)
      | forall x, equal _ _ => ac_rewrite1' H || ac_rewrite2' (ac_head1 H)
      | forall x y, equal _ _ => ac_rewrite2' H || ac_rewrite3' (ac_head2 H)
      | forall x y z, equal _ _ => ac_rewrite3' H || ac_rewrite4' (ac_head3 H)
    end.

(*begintests
  Goal forall x y z, equal (plus (plus (plus (plus z x) y) x) y) (plus (plus z x) y).
    intros.
    ac_rewrite plus_idem.
    ac_rewrite plus_idem.
    reflexivity.
  Qed.

  Goal forall x y z, equal (plus (plus (dot x y) x) (dot z y)) (plus (dot (plus x z) y) x).
    intros.
    pose (dot_distr_left' x y z := equal_sym (dot_distr_left x y z)).
    ac_rewrite dot_distr_left'.
    reflexivity.
  Qed.
endtests*)
*)



Section FSumDef.

  Context `{SLo: SemiLattice_Ops}.

  Section Vars.
    Variables A B: T.
  
    (* sum i..i+k-1 *)
    Fixpoint sum i k (f: nat -> X A B): X A B :=
      match k in nat return X A B with
        | 0 => 0
        | S k => f i + sum (S i) k f
      end.
  End Vars.

  Context {SL: SemiLattice}.
  Variables A B: T.

  Lemma sum_empty i (f: nat -> X A B): sum i 0 f == 0.
  Proof. reflexivity. Qed.

  Lemma sum_enter_left i k (f: nat -> X A B):
    sum i (S k) f == f i + sum (S i) k f.
  Proof. reflexivity. Qed.

  Lemma sum_enter_right i k (f: nat -> X A B):
    sum i (S k) f == sum i k f + f (i+k)%nat.
  Proof. 
    intros i k f; revert i; induction k; intro i.
    simpl. rewrite plus_0_r; apply plus_com.
    change (sum i (S (S k)) f) with (f i + sum (S i) (S k) f).
    rewrite IHk, plus_assoc. simpl. auto with compat.
  Qed.

End FSumDef.
Opaque sum.
Ltac simpl_sum_r := simpl; repeat setoid_rewrite sum_empty; repeat setoid_rewrite sum_enter_right.
Ltac simpl_sum_l := simpl; repeat setoid_rewrite sum_empty; repeat setoid_rewrite sum_enter_left.


Section Props1.

  Context `{SL: SemiLattice}.
  Variables A B: T.

  Lemma plus_neutral_right: forall (x: X A B), x+0 == x.
  Proof. intros; aci_reflexivity. (* rewrite plus_com; apply plus_neutral_left. *) Qed.
  
  Lemma zero_inf: forall (x: X A B), 0 <== x.
  Proof (@plus_neutral_left _ _ _ A B).  
  
  Lemma plus_make_left: forall (x y: X A B), x <== x+y.
  Proof. intros; aci_reflexivity. (* unfold leq; rewrite plus_assoc, plus_idem; reflexivity. *) Qed.
  
  Lemma plus_make_right: forall (x y: X A B), x <== y+x.
  Proof. intros; aci_reflexivity. (* unfold leq; rewrite (plus_com y); apply plus_make_left. *) Qed.
  
  Lemma plus_destruct_leq: forall (x y z : X A B), x<==z -> y<==z -> x+y<==z.
  Proof. unfold leq; intros x y z H H'; ac_rewrite H'; trivial. Qed. 

  Lemma leq_destruct_plus: forall (x y z: X A B), x+y <== z -> x<==z /\ y<==z.
  Proof. intros x y z H; rewrite <- H; split; aci_reflexivity. Qed.
    

  Global Instance plus_incr:
  Proper ((leq A B) ==> (leq A B) ==> (leq A B)) (plus A B).
  Proof. 
    unfold leq; intros x x' Hx y y' Hy.
    rewrite <- Hy at 2; rewrite <- Hx at 2.
    aci_reflexivity.
(*
    rewrite (plus_com x'), <- plus_assoc, (plus_assoc y), Hy.
    rewrite plus_com, <- plus_assoc, (plus_com x'), Hx.
    reflexivity.
*)
  Qed.

  Lemma sup_def: forall (x y: X A B), (forall z, x <== z <-> y <== z) -> x==y.
  Proof.
    intros x y H. apply leq_antisym.
    apply <- H; reflexivity.
    apply -> H; reflexivity.
  Qed.

  Lemma inf_def: forall (x y: X A B), (forall z, z <== x <-> z <== y) -> x==y.
  Proof.
    intros x y H. apply leq_antisym.
    apply -> H; reflexivity.
    apply <- H; reflexivity.
  Qed.

  Lemma sum_compat (f f':nat -> X A B) i k:
    (forall n, n<k -> f (i+n)%nat == f' (i+n)%nat) -> sum i k f == sum i k f'.
  Proof.
    induction k; intro E; simpl_sum_r.
    reflexivity.
    rewrite IHk, E by auto with arith.
    reflexivity.
  Qed.

  Global Instance sum_compat' i k: 
  Proper ((pointwise_relation nat (equal A B)) ==> (equal A B)) (sum i k).
  Proof. repeat intro; auto using sum_compat. Qed.
   
  Lemma sum_zero i k (f: nat -> X A B):
    (forall n, n<k -> f (i+n)%nat == 0) -> sum i k f == 0.
  Proof.
    intros until f; induction k; intro E; simpl_sum_r.
    reflexivity.
    rewrite IHk, E by auto with arith.  
    apply plus_idem.
  Qed.
  
  (* ce lemme est utile quand on veut matcher des (fun x => 0). le lemme précédant peut s'appliquer à trop d'endroits *)
  Lemma sum_fun_zero i k : 
    sum i k (fun _ =>(0 : X A B)) == 0.
  Proof.
    intros. rewrite sum_zero; auto. 
  Qed.
  
  Lemma sum_cut k' i k (f: nat -> X A B):
    sum i (k'+k) f == sum i k f + sum (k+i) k' f.
  Proof.
    intros; induction k'; simpl_sum_r.
    aci_reflexivity.
    rewrite IHk', plus_assoc.
    auto with compat omega.
  Qed.
  
  Lemma sum_cut_fun i k (f g: nat -> X A B):
    sum i k (fun u => f u + g u) == sum i k f + sum i k g.
  Proof.
    intros; induction k; simpl_sum_r.
    aci_reflexivity.
    rewrite IHk.
    aci_reflexivity.  
  Qed.
    
  Lemma sum_cut_nth n (f: nat -> X A B) i k:
    n<k -> sum i k f == sum i n f + f (i+n)%nat + sum (i+S n) (k-n-1) f.
  Proof.
    intros. 
    pattern k at 1; replace k with (S(k-n-1)+n)%nat by omega. 
    rewrite sum_cut.
    rewrite sum_enter_left, plus_assoc.
    auto with compat omega.
  Qed.
  Implicit Arguments sum_cut_nth [].
  
  Lemma sum_shift d (f: nat -> X A B) i k:
    sum (i+d) k f == sum i k (fun u => f (u+d)%nat).
  Proof.
    induction k; simpl_sum_r; auto with compat omega.
  Qed.
    
  Theorem sum_inversion (f: nat -> nat -> X A B) i i' k k':
       sum i k (fun u => (sum i' k' (f u)))
    == sum i' k' (fun u'=> (sum i k (fun u => f u u'))).
  Proof.
    induction k'; simpl_sum_r.
    apply sum_zero; reflexivity. 
    rewrite sum_cut_fun.
    rewrite IHk'; reflexivity.
  Qed.
  
  Lemma leq_sum (f: nat -> X A B) i k x:
    (exists n, i<=n /\ n<i+k /\ x == f n) -> x <== sum i k f.
  Proof. 
    intros f i k x [n [? [? E]]].
    rewrite E, (sum_cut_nth (n-i))  by omega. 
    replace (i+(n-i))%nat with n by auto with arith. 
    aci_reflexivity. 
  Qed.  
  
  Lemma sum_incr (f f': nat -> X A B) i k:
    (forall n, n<k -> f (i+n)%nat <== f' (i+n)%nat) -> sum i k f <== sum i k f'.
  Proof.
    induction k; intro E; simpl_sum_r.
    reflexivity.
    rewrite 2 sum_enter_right.
    rewrite IHk, E by auto with arith.
    reflexivity.
  Qed.
    
  Global Instance sum_incr' i k: 
  Proper ((pointwise_relation nat (leq A B)) ==> (leq A B)) (sum i k).
  Proof. repeat intro; auto using sum_incr. Qed.

End Props1.
Implicit Arguments sum_cut_nth [[G] [SLo] [SL] A B].

(*begintests
Section tests_rewrite.
  Goal forall `{KleeneAlgebra} A (x y z: X A A), x+y == y+x+x -> (x+y)+z <== x#.
    intros.
    rewrite H0.
  Abort.
  Goal forall `{KleeneAlgebra} A (x y z: X A A), x+y == y+x+x -> (x+y)+z <== x#+(x+y).
    intros.
    rewrite H0 at 1.
    rewrite H0.
  Abort.
  Goal forall `{KleeneAlgebra} A (x y z: X A A), x+y <== y+x+x -> (x+y)+z <== x#.
    intros.
    rewrite H0.
  Abort.
  
  Goal forall `{KleeneAlgebra} A (x y z: X A A), x+y==z# -> sum 6 8 (fun _ => (x+y)+z) == z.
    intros.
    setoid_rewrite H0.
  Abort.
  
  Goal forall `{KleeneAlgebra} A (x y z: X A A), x+y==z# -> sum 6 8 (fun _ => (x+y)+z) <== z.
    intros.
    setoid_rewrite H0.
  Abort.
  
  Goal forall `{IdemSemiRing} A (x y z: X A A), x+y<==z*z -> sum 6 8 (fun _ => (x+y)+z) <== z.
    intros.
    setoid_rewrite H0.
  Abort.
End tests_rewrite.
endtests*)


Hint Extern 0 (equal _ _ _ _) => first [ 
  apply plus_neutral_right 
]: algebra.
Hint Extern 1 (equal _ _ _ _) => first [ 
    apply sum_compat
]: compat algebra.

Hint Extern 0 (leq _ _ _ _) => first [ 
  apply plus_destruct_leq
  | apply plus_make_left
  | apply plus_make_right
  | apply zero_inf
]: algebra.
Hint Extern 1 (leq _ _ _ _) => first [ 
    apply sum_incr
]: compat algebra.
Hint Extern 2 (leq _ _ _ _) => first [ 
    apply plus_incr
]: compat algebra.

(* Hint Resolve @sum_compat @sum_incr @plus_incr: compat algebra. *)
(* Hint Resolve  *)
(*   @plus_destruct_leq @plus_make_left @plus_make_right  *)
(*   @zero_inf @plus_neutral_right *)
(*   : algebra. *)
Hint Rewrite @plus_neutral_right using ti_auto: simpl.  


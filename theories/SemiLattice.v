(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Properties, definitions, hints and tactics for semilattices.
   In particular, the tactic [ac_rewrite] allows to rewrite closed
   equations modulo associativity and commutativity *)

Require Import Common.
Require Import Classes.
Require Import Graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma plus_neutral_right `{SemiLattice} A B: forall (x: X A B), x+0 == x.
Proof. intros. rewrite plus_com; apply plus_neutral_left. Qed.

(** Hints  *)
Hint Extern 0 (leq _ _ _ _) => apply leq_refl : core.

Hint Extern 0 (equal _ _ _ _) => first [
    apply plus_assoc
  | apply plus_com
  | apply plus_idem
  | apply plus_neutral_left
  | apply plus_neutral_right
]: algebra.
Hint Extern 2 (equal _ _ _ _) => first [
    apply plus_compat; instantiate
]: compat algebra.

(* Hint Resolve @leq_refl. *)
(* Hint Resolve @plus_assoc @plus_idem @plus_com @plus_neutral_left: algebra. *)
(* Hint Resolve @plus_compat: compat algebra. *)
Hint Rewrite @plus_neutral_left @plus_neutral_right @plus_idem using ti_auto: simpl.  


Ltac fold_leq := match goal with |- equal ?A ?B (?a + ?b) ?b => change (leq A B a b) end.


(** simple tactic for closed rewriting modulo AC, in Ltac *)
Lemma switch `{SemiLattice} A B (a b c : X A B) : (a+b)+c == (a+c)+b.
Proof. intros. rewrite <- plus_assoc, (plus_com b). apply plus_assoc. Qed.
    
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
  peigne_aux q a b :=
  match q with 
    | (?q'+a)+b => rewrite <- (plus_assoc q' a b)
    | (?q'+?x)+b => rewrite (switch q' x b); peigne_aux (q' +b) a b   
    | a+b => idtac 
    | ?q' + ?x => peigne_aux q' a b 
    | ?x => fail x   end.

Ltac atomic a :=
  match a with | _ + _ => fail 1 | _ => idtac  end.
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
  rewrite ?plus_assoc;
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
  
  Goal e + d + a + b  +c <== d.
    ac_rewrite H.
    reflexivity.
  Qed.

  Goal e + d + a + b + e +c <== e+d.
    ac_rewrite H'.
    reflexivity.
  Qed.

  Hypothesis J :  f + g == c.
  Goal e + d + a + b + e + g + f == d.
    ac_rewrite J.
    Fail ac_rewrite (plus_idem e). (* BUG *)
    ac_rewrite H.
  Abort.

  Variable C : T.
  Variable h : X B C.
  Goal (f+g)*h + 1*f*h == 1*c*h +1*f*1*h*1.
    ac_rewrite J.
    rewrite !dot_neutral_left, !dot_neutral_right.
    reflexivity.
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


(** finite sums and their properties  *)
Section FSumDef.

  Context `{SL: SemiLattice}.

  Variables A B: T.
  
  (* sum i..i+k-1 *)
  Fixpoint sum i k (f: nat -> X A B): X A B :=
    match k in nat return X A B with
      | 0 => 0
      | S k => f i + sum (S i) k f
    end.

  Lemma sum_empty i (f: nat -> X A B): sum i 0 f == 0.
  Proof. reflexivity. Qed.

  Lemma sum_enter_left i k (f: nat -> X A B):
    sum i (S k) f == f i + sum (S i) k f.
  Proof. reflexivity. Qed.

  Lemma sum_enter_right i k (f: nat -> X A B):
    sum i (S k) f == sum i k f + f (i+k)%nat.
  Proof. 
    revert i; induction k; intro i.
    simpl. rewrite plus_0_r; apply plus_com.
    change (sum i (S (S k)) f) with (f i + sum (S i) (S k) f).
    rewrite IHk, plus_assoc. simpl. auto with compat.
  Qed.

End FSumDef.
Opaque sum.
Ltac simpl_sum_r := simpl; repeat setoid_rewrite sum_empty; repeat setoid_rewrite sum_enter_right.
Ltac simpl_sum_l := simpl; repeat setoid_rewrite sum_empty; repeat setoid_rewrite sum_enter_left.



(** various properties of semilattices and finite sums  *)
Section Props1.

  Context `{SL: SemiLattice}.
  Variables A B: T.
  
  Lemma zero_inf: forall (x: X A B), 0 <== x.
  Proof (@plus_neutral_left _ _ _ A B).  
  
  Lemma plus_make_left: forall (x y: X A B), x <== x+y.
  Proof. intros; unfold leq. rewrite plus_assoc, plus_idem. reflexivity. Qed.
  
  Lemma plus_make_right: forall (x y: X A B), x <== y+x.
  Proof. intros; unfold leq. rewrite (plus_com y), plus_assoc, plus_idem. reflexivity. Qed.
  
  Lemma plus_destruct_leq: forall (x y z : X A B), x<==z -> y<==z -> x+y<==z.
  Proof. unfold leq; intros x y z H H'. ac_rewrite H'; trivial. Qed. 

  Lemma leq_destruct_plus: forall (x y z: X A B), x+y <== z -> x<==z /\ y<==z.
  Proof. 
    intros x y z H; rewrite <- H; split; unfold leq. 
     rewrite plus_assoc, plus_idem. reflexivity. 
     rewrite (plus_com x), plus_assoc, plus_idem. reflexivity.
  Qed.
    

  Global Instance plus_incr:
  Proper ((leq A B) ==> (leq A B) ==> (leq A B)) (plus A B).
  Proof. 
    unfold leq; intros x x' Hx y y' Hy.
    ac_rewrite Hx. ac_rewrite Hy. reflexivity. 
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
    induction k; intro E; simpl_sum_r.
    reflexivity.
    rewrite IHk, E by auto with arith.  
    apply plus_idem.
  Qed.
  
  Lemma sum_fun_zero i k : 
    sum i k (fun _ =>(0 : X A B)) == 0.
  Proof.
    rewrite sum_zero; auto. 
  Qed.
  
  Lemma sum_cut k' i k (f: nat -> X A B):
    sum i (k'+k) f == sum i k f + sum (k+i) k' f.
  Proof.
    induction k'; simpl_sum_r.
     auto with algebra.
     rewrite IHk', plus_assoc.
     auto with compat omega.
  Qed.
  
  Lemma sum_cut_fun i k (f g: nat -> X A B):
    sum i k (fun u => f u + g u) == sum i k f + sum i k g.
  Proof.
    induction k; simpl_sum_r.
     auto with algebra.
     rewrite IHk. 
     (* aac_reflexivity. *)
     rewrite switch. setoid_rewrite plus_com at 6. 
     rewrite 2plus_assoc. reflexivity. 
  Qed.
    
  Lemma sum_cut_nth n (f: nat -> X A B) i k:
    n<k -> sum i k f == sum i n f + f (i+n)%nat + sum (i+S n) (k-n-1) f.
  Proof.
    intros; pattern k at 1; replace k with (S(k-n-1)+n)%nat by omega. 
    rewrite sum_cut.
    rewrite sum_enter_left, plus_assoc.
    auto with compat omega.
  Qed.
  Arguments sum_cut_nth : clear implicits.
  
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
    (exists n, i<=n /\ n<i+k /\ x <== f n) -> x <== sum i k f.
  Proof. 
    intros [n [? [? E]]].
    rewrite E, (sum_cut_nth (n-i))  by omega. 
    replace (i+(n-i))%nat with n by auto with arith. 
    rewrite <- plus_make_left. apply plus_make_right.
  Qed.

  Lemma sum_leq (f : nat -> X A B) i k x: 
    (forall n, i <= n -> n < i +k -> f n <== x) -> sum i k f <== x.
  Proof.
    revert x.
    induction k. 
    intros x H. simpl_sum_r. apply plus_neutral_left.
    intros x H. simpl_sum_r. rewrite (IHk x) , H. 
     auto using plus_destruct_leq.
     auto with arith.
     auto with arith.
     intros; apply H; omega.  
  Qed.
    
  Lemma sum_plus : forall (f : nat -> X A B) i k a, 0 < k -> sum i k f + a == sum i k (fun n => f n + a).
  Proof.
    induction k; intros.
      omega_false.
      simpl_sum_r.
      destruct (eq_nat_dec 0 k).
        subst. simpl_sum_r. auto with algebra.
        setoid_rewrite <- IHk. 
        setoid_rewrite switch at 2. rewrite <- !plus_assoc, plus_idem. reflexivity.
        omega.
  Qed.
    
  Lemma sum_constant : forall i k (a : X A B),  0 < k -> sum i k (fun _ => a) == a.
  Proof. 
    induction k; intros. 
      omega_false.
      simpl_sum_r.   
      destruct (eq_nat_dec 0 k).
        subst. simpl_sum_r. auto with algebra.
        setoid_rewrite IHk. trivial with algebra.
        omega.
  Qed.

  Lemma sum_collapse n (f: nat -> X A B) i k:
    n<k ->
    (forall x,  x <> (i+n)%nat -> f x == 0) ->
    sum i k f == f (i+n)%nat.
  Proof.
    intros Hn H.
    rewrite (sum_cut_nth n), 2 sum_zero by  ( auto || intros; apply H ; omega).
    rewrite plus_neutral_left. apply plus_neutral_right.
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


  Lemma xif_plus: forall b (x y z: X A B), xif b x y + z == xif b (x+z) (y+z).
  Proof. intros. destruct b; trivial. Qed.

  Lemma plus_xif: forall b (x y z: X A B), z + xif b x y == xif b (z+x) (z+y).
  Proof. intros. destruct b; trivial. Qed.


  (* rather specific lemmas, used in the proof of DKA *)
  Lemma xif_sum_zero: forall b i k (f: nat -> X A B), xif b (sum i k f) 0 == sum i k (fun j => xif b (f j) 0).
  Proof.
    intros. revert i. induction k; intro i; simpl_sum_l. 
     apply xif_idem.
     rewrite <- IHk. destruct b; auto with algebra.
  Qed.

  Lemma sum_fixed_xif_zero: forall v k b (x: X A B), v < k -> b v = true -> sum 0 k (fun u => xif (b u) x 0) == x.
  Proof.
    intros v k b x ? H. apply leq_antisym.
    apply sum_leq. intros. case b. apply leq_refl. apply zero_inf.
    apply leq_sum. exists v. rewrite H. auto with arith. 
  Qed.

  Lemma compare_sum_xif_zero: forall k k' b c (x: X A B), 
    (forall i, i < k -> b i = true -> exists2 j, j < k' & c j = true) ->
    sum 0 k (fun i => xif (b i) x 0) <== sum 0 k' (fun j => xif (c j) x 0).
  Proof.
    intros until x; intro H. apply sum_leq. intros n _ Hn.
    specialize (H _ Hn). destruct (b n). destruct (H refl_equal) as [j ? Hj].
    apply leq_sum. exists j. rewrite Hj. auto with arith.
    apply zero_inf.
  Qed.


End Props1.
Arguments sum_cut_nth [G] [SLo] [SL] [A] [B].



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


(** Hints  *)

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


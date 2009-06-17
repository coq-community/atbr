(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*           GNU Lesser General Public License version 3                  *)
(*                (see file LICENSE for more details)                     *)
(*                                                                        *)
(*          Copyright 2009: Thomas Braibant, Damien Pous.                 *)
(*                                                                        *)
(**************************************************************************)

(*i $Id$ i*)

(** Booleans form a Kleene Algebra, and we can define efficient
functions for computation on boolean matrices *)

Require Import Common.
Require Import Classes.
Require Import SemiLattice.
Require Import SemiRing.
Require Import KleeneAlgebra.
Require Import MxGraph.
Require Import MxSemiRing.
Require Import MxKleeneAlgebra.

Require Import Functors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Def.
  (** * Definition of the Kleene Algebra of booleans *)
  Instance bool_Graph: Graph := {
    T := unit;
    X A B := bool;
    equal A B := @eq bool;
    equal_equivalence A B := eq_equivalence
  }.

  Instance bool_SemiLattice_Ops: SemiLattice_Ops := {
    plus A B := orb;
    zero A B := false
  }.

  Instance bool_Monoid_Ops: Monoid_Ops := {
    dot A B C := andb;
    one A := true
  }.
  
  Instance bool_Star_Op: Star_Op := { 
    star A x := 1 
  }.

  Instance bool_Inf_Op: Inf_Op := { 
    inf A B := andb
  }.
  
  Instance bool_Residual_Ops: Residual_Ops := { 
    ldiv A B C x y := orb (negb x) y;
    rdiv A B C x y := orb (negb x) y
  }.

  Instance bool_Converse_Op: Converse_Op := { 
    conv A B x := x
  }.
  
  Instance bool_SemiLattice: SemiLattice.
  Proof.
    constructor; repeat intro; simpl in *;
    repeat match goal with x: bool |- _ => destruct x end; reflexivity || discriminate.
  Qed.

  Instance bool_Monoid: Monoid.
  Proof.
    constructor; repeat intro; simpl in *;
    repeat match goal with x: bool |- _ => destruct x end; reflexivity || discriminate.
  Qed.

  Instance bool_SemiRing: IdemSemiRing.
  Proof.
    apply (Build_IdemSemiRing bool_Monoid bool_SemiLattice);
    repeat intro; simpl in *;
    repeat match goal with x: bool |- _ => destruct x end; reflexivity.
  Qed.

  Instance bool_ResIdemSemiRing: ResIdemSemiRing.
  Proof.
    constructor; first [
      exact bool_Monoid |
        exact bool_SemiLattice |
          intros; split; intro; simpl in *; 
            repeat match goal with x: bool |- _ => destruct x end; reflexivity || discriminate ].
  Qed.

  Instance bool_ActionAlgebra: ActionAlgebra.
  Proof.
    constructor; 
    try exact bool_ResIdemSemiRing;
    repeat intro; simpl in *;
    repeat match goal with x: bool |- _ => destruct x end; reflexivity.
  Qed.

  Instance bool_KleeneAlgebra: KleeneAlgebra.
  Proof.
    constructor; 
    try exact bool_SemiRing;
    repeat intro; simpl in *;
    repeat match goal with x: bool |- _ => destruct x end; reflexivity.
  Qed.

  Section Injection.

    (** we can inject a boolean algebra in a more general one *)

    Context {G: Graph} {t: @T G} {Mo: @Monoid_Ops G} {SLo: @SemiLattice_Ops G}.
    
    Definition convert: functor bool_Graph G :=
      @Build_functor bool_Graph G 
      (fun _ => t) 
      (fun _ _ x => if x then 1 else 0).

    Global Instance graph_functor_convert: graph_functor convert.
    Proof.
      intros A B x y H. vm_compute in H. subst. destruct y; reflexivity.
    Qed.
  
    Global Instance semiring_functor_convert {ISR: IdemSemiRing (G:=G)}: semiring_functor convert.
    Proof.
      constructor; constructor; auto with typeclass_instances;
        intros; symmetry; destruct x; destruct y; simpl; trivial with algebra. 
    Qed.

    Global Instance kleene_functor_convert {Ko} {KA: @KleeneAlgebra G Mo SLo Ko}: kleene_functor convert.
    Proof.
      constructor.
      exact semiring_functor_convert.
      intros A a. symmetry; destruct a; simpl. apply star_one. apply star_zero. 
    Qed.

  End Injection.

  (** Some properties on boolean Kleene algebra *)

  Notation is_true := (@equal bool_Graph tt tt 1). 

(*   Global Instance is_true_compat: Proper (@equal bool_Graph tt tt ==> iff) is_true. *)
(*   Proof. *)
(*     vm_compute; intros; subst; split; trivial. *)
(*   Qed. *)

  Lemma bool_view: forall x y, (is_true x <-> is_true y) -> x == y.
  Proof.
    intros [|] [|]; vm_compute; firstorder.
  Qed.

  Lemma bool_plus_spec: forall x y, is_true (x+y) <-> is_true x \/ is_true y.
  Proof.
    intros [|] [|]; vm_compute; intuition.
  Qed.

  Lemma bool_dot_spec: forall x y, is_true (x*y) <-> is_true x /\ is_true y.
  Proof.
    intros [|] [|]; vm_compute; intuition.
  Qed.

  Section bool_sum.
    Variables A B: T.
    Fixpoint bool_sum i k (f: nat -> X A B): X A B :=
      match k with 
        | 0 => false
        | S k => if f i then true else bool_sum (S i) k f
      end.

    Lemma bool_sum_sum: forall i k (f: nat -> X A B), bool_sum i k f = sum i k f.
      intros i k f.

      revert i; induction k; intro i; simpl.
      reflexivity.
      destruct (f i); simpl; trivial.
    Qed.

    Lemma bool_sum_spec i k (f : nat -> @X bool_Graph tt tt): is_true (sum i k f) <-> exists j, (i <= j /\ j < i+k /\ is_true (f j)).
    Proof.
      intros i k f. revert i. induction k; intro i.
      split; intros. discriminate. destruct H; intuition. omega_false.

      rewrite sum_enter_right.
      rewrite bool_plus_spec.
      rewrite IHk.
      split. intros [(j&?&?&?)|H]. 
       exists j; auto with omega.
       exists (i+k)%nat; auto with omega.
       intros (j&?&?&?). destruct (eq_nat_dec j (i+k)).
        subst. auto.
        left. exists j; auto with omega.

(*       simpl. *)
(*       split; intros. *)
(*       induction k. discriminate. *)
  
(*       apply bool_plus_one in H. *)
(*       destruct H. *)
(*        intuition. destruct H0 as [j ?]. exists j; intuition omega. *)
(*        exists (i+k)%nat. auto with omega. *)
      
(*       apply leq_antisym. destruct (sum i k f); reflexivity.  *)
(*       apply leq_sum. destruct H. exists x. intuition. *)
    Qed.

  End bool_sum.

  
  Section mxbool_dot.
    (** Boolean matrices form a Kleene algebra *)
    Variables n m p: nat.
    Variables A B C: T.
    Variables (M: MX(n,A)(m,B)) (N: MX(m,B)(p,C)). 
    Definition mxbool_dot: MX(n,A)(p,C) :=
      box n p (fun i j => @bool_sum A C 0 m (fun k => if (!M i k) then (!N k j) else false)).

  
    Lemma mxbool_dot_dot: mxbool_dot == M * N.
    Proof.
      Transparent equal.
      simpl. intros. rewrite bool_sum_sum. reflexivity.
      Opaque equal.
    Qed.

  End mxbool_dot.

  Section mxbool_dot'.
    Variables n m p: nat.
    Notation tt := (tt: @T bool_Graph).
    Variables (M: MX(n,tt)(m,tt)) (N: MX(m,tt)(p,tt)). 

    Lemma mxbool_dot_spec: forall i j, is_true (@get bool_Graph tt tt n p (M * N) i j) <-> 
      exists k, k < m /\ is_true (@get bool_Graph tt tt n m M i k) /\ is_true (@get bool_Graph tt tt m p N k j). 
    Proof.
      intros.
      setoid_rewrite <- bool_dot_spec.
      Opaque one. simpl. Transparent one.
      rewrite bool_sum_spec.
      firstorder. 
    Qed.

  End mxbool_dot'.
  

  Section mxbool_plus.
    Variables n m: nat.
    Variables A B: T.
    Variables (M N: MX(n,A)(m,B)).
    Definition mxbool_plus: MX(n,A)(m,B) :=
      box n m (fun i j => if !M i j then true: X A B else !N i j).
    
    Lemma mxbool_plus_plus: mxbool_plus = M + N.
    Proof. reflexivity. Qed.
  End mxbool_plus.

  Infix "**" := mxbool_dot (at level 20, left associativity). 
  Infix "+++" := mxbool_plus (at level 50, left associativity). 

  Section mxbool_star.
    Fixpoint mxbool_star_rec n A: MX (n,A) (n,A) -> MX (n,A) (n,A) :=
      match n return MX (n,A) (n,A) -> MX (n,A) (n,A) with
        | 0 => fun M => M
        | S n => fun M =>
          let b := sub01 (x:=1) (y:=1) M in
          let c := sub10 (x:=1) (y:=1) M in
          let d := sub11 (x:=1) (y:=1) M in
          let ds:= mx_force(mxbool_star_rec d) in
          let bds:= mx_force(b**ds) in 
          let dsc:= mx_force(ds**c) in 
            makeMat_blocks 
            (scal_to_Mat 1)
            (bds) 
            (dsc)
            (ds +++ dsc**bds) 
      end.

    Definition mxbool_star n A (M: MX(n,A)(n,A)) := mxbool_star_rec (n:=n) (mx_force M).

    Lemma mxbool_star_star: forall n A (M: MX(n,A)(n,A)), mxbool_star M == M#.
    Proof.
      intros n A M'.
      rewrite <- (mx_force_id M') at 2.
      unfold mxbool_star, star, mx_Star_Op, fst, snd.
      generalize (mx_force M') as M; clear M'.
      induction n; intro M.
      reflexivity.
      simpl mxbool_star_rec.
      unfold star_rec; fold star_rec.
      unfold star, bool_Star_Op, star_build.
      change (S n) with (1+n)%nat.
      rewrite <- scal_to_Mat_one.
      apply makeMat_blocks_compat; unfold fst, snd.
       reflexivity.
       (* bizarre, les trois sous-buts se condensaient mieux avant *)
       rewrite dot_neutral_left. rewrite mx_force_id. rewrite mxbool_dot_dot, mx_force_id, IHn. reflexivity.      
       rewrite dot_neutral_right. rewrite mx_force_id. rewrite mxbool_dot_dot, mx_force_id, IHn. reflexivity.      
       rewrite dot_neutral_right, mxbool_plus_plus. rewrite mxbool_dot_dot. rewrite mx_force_id at 1.
       rewrite mx_force_id at 1. rewrite mxbool_dot_dot. rewrite mx_force_id at 1. rewrite IHn at 1 2. 
       rewrite mx_force_id at 1. rewrite mxbool_dot_dot. rewrite mx_force_id at 1. rewrite IHn. reflexivity.
    Qed.
  
  End mxbool_star.

(*begintests

  Require Import List.

  Let M := 
    let f := false in
    let t := true in
    let l :=                      (* 20 x 20 *)
      (f::f::f::f::f::f::t::f::f::f::f::f::f::f::f::f::t::f::f::f::f::nil)::
      (f::f::t::f::f::f::f::t::f::f::f::f::t::f::f::f::f::f::f::f::f::nil)::
      (f::f::f::t::f::f::f::f::f::f::f::f::f::f::t::f::f::f::f::t::f::nil)::
      (f::f::f::f::f::f::f::f::f::f::t::f::f::f::f::f::f::f::f::t::f::nil)::
      (f::f::f::f::t::f::t::f::f::f::f::f::t::f::f::f::f::t::f::f::f::nil)::
      (f::f::f::f::f::t::f::f::f::f::f::f::f::f::f::f::f::t::f::f::f::nil)::
      (f::f::f::f::f::t::f::f::f::f::f::t::f::f::f::f::t::f::f::f::f::nil)::
      (f::t::f::f::t::f::f::f::f::f::f::f::f::t::f::f::f::t::f::f::f::nil)::
      (f::f::f::t::f::f::f::f::t::f::t::f::f::f::f::f::f::f::f::f::f::nil)::
      (f::t::f::f::f::f::f::f::t::f::f::f::t::f::f::f::f::f::f::f::t::nil)::
      (f::f::f::f::f::t::f::f::f::f::f::f::f::f::f::f::f::t::f::t::f::nil)::
      (f::f::f::f::f::f::f::f::f::t::t::f::t::f::f::f::f::f::t::t::f::nil)::
      (t::f::f::f::f::f::t::f::f::t::f::f::f::f::f::f::t::f::f::t::f::nil)::
      (f::f::f::f::f::f::f::f::f::f::f::f::t::f::f::f::f::f::f::t::f::nil)::
      (f::f::f::f::t::f::f::f::f::f::f::f::f::t::f::f::f::f::f::f::f::nil)::
      (t::f::f::f::f::f::f::f::f::f::f::t::t::f::f::f::f::f::f::t::f::nil)::
      (f::f::f::f::f::f::f::f::f::t::f::t::f::f::t::f::t::f::f::f::f::nil)::
      (f::f::f::f::f::f::f::f::t::f::t::f::t::f::t::f::t::f::t::f::f::nil)::
      (f::f::f::t::f::f::f::f::f::f::f::t::f::f::f::f::f::f::f::f::f::nil)::
      (f::f::f::f::f::f::f::f::f::f::f::f::f::t::f::f::f::f::t::f::f::nil)::nil 
    in 
    @box bool_Graph tt tt 20 20 (fun i j => List.nth j (List.nth i l nil) false).

  Let n := 20.        

  Let N := M: @X (@mx_Graph bool_Graph) (n,tt) (n,tt).
  Let N2 := makeMat_blocks N 0 1 N.
  Let N3 := makeMat_blocks N 0 0 N2.

  Time Eval vm_compute in 
    let Ms := mxbool_star N3
      in mx_noprint Ms. 

(* 
   le 20 fevrier (r435), gallium
   7 :   0.4s
   8 :   2.4s
   9 :  23.8s

   le 20 fevrier (r440), gallium  (mx_print N)
   9 :   0.03s
   20:   0.14s                  

   le 20 fevrier (r443), gallium
   9 :   0.03s
   20:   0.08s                  (* mx_noprint N#  *)
   40:   1.13s                  (* mx_noprint N2# *)
   60:   6.80s                  (* mx_noprint N3# *)

*)

endtests*)

End Def.


Notation is_true := (@equal bool_Graph tt tt 1). 

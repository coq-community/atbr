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
Require        List.
Require        Force.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Defs.

  Context {G: Graph}.

(*   Definition X' A B := nat -> nat -> X A B. *)
  Inductive X' A B (n m: nat) := 
    box: (nat -> nat -> X A B) -> X' A B n m.

  Definition get A B n m (M: X' A B n m) := let (f) := M in f.

  Program Instance mx_Graph: Graph := {
    T := prod nat T;
    X nA mB := X' (snd nA) (snd mB) (fst nA) (fst mB);
    equal nA mB M N := forall i j, i<fst nA -> j<fst mB -> get M i j == get N i j
  }.
  Next Obligation.
    split; repeat intro; simpl in *.
    reflexivity.
    symmetry; auto.
    transitivity (get y i j); auto.
  Qed.

  (* lemme débile, à utiliser quand equal est déclaré opaque *)
  Definition mx_equal nA mB (M N: @X mx_Graph nA mB) (H: forall i j, i<fst nA -> j<fst mB -> get M i j == get N i j): M == N := H.

End Defs.


(* NB: ne surtout pas "définir Mequal", sinon les lemmes de 
   auto non spécifiques aux matrices ne s'appliquent plus... *)
Notation Mequal := (@equal mx_Graph) (only parsing).
Notation MX := (@X mx_Graph).
Notation MT := (@T mx_Graph).

Notation "! M" := (get M) (at level 0).
Notation "M == [ n , m ]  N" := (Mequal (n,_) (m,_) M N) (at level 80).

(* tactique pour analyser makeMat_blocks, remontée ici pour qu'elle reste exportée *)
Global Opaque Peano.minus. 
Lemma plus_minus : forall m n, S (m+n)-n = S m.
Proof. intros. omega. Qed.

Ltac destruct_blocks :=
  rewrite ? plus_minus; 
  repeat match goal with 
           | |- context[S ?i - ?n] => case_eq (S i - n); intros 
         end. 
  
Ltac mx_intros i j Hi Hj :=
  apply mx_equal; unfold fst; intros i j Hi Hj;
  match type of Hi with
    | i < 0%nat => inversion Hi
    | i < 1%nat => destruct i; [clear Hi|omega_false]
    | _ => idtac
  end;
  match type of Hj with
    | j < 0%nat => inversion Hj
    | j < 1%nat => destruct j; [clear Hj|omega_false]
    | _ => idtac
  end.

Transparent equal.

Section Props.

  Context {G: Graph}.

  Variables A B: T.


  (* égalité *)

  Lemma equal_compat n m: forall M N: MX (n,A) (m,B), 
    M == N -> 
    forall i j i' j', i<n -> j<m -> i=i' -> j=j' -> equal A B (!M i j) (!N i' j').
  Proof. intros; subst; auto. Qed.

(*
  Lemma sub_equal_compat n' m' n m: forall M N: X' A B, 
    n<=n' -> m<=m' -> M ==[n',m'] N -> M ==[n,m] N.
  Proof. repeat intro. auto with omega. Qed.
*)

  (* évaluation forcée, et affichage (sous forme de listes de listes) *)
    
  Definition mx_force n m (M: MX(n,A)(m,B)): MX(n,A)(m,B) := box n m (Force.id2 n m !M).
  Definition mx_print n m (M: MX(n,A)(m,B)) := Force.print2 n m !M.
  Definition mx_noprint n m (M: MX(n,A)(m,B)) := let _ := mx_force M in (n,m).

  Lemma mx_force_id n m (M: MX (n,A) (m,B)): mx_force M == M.
  Proof. repeat intro; unfold mx_force. simpl. rewrite Force.id2_id by assumption. reflexivity. Qed.

  Global Instance mx_force_compat n m: Proper (Mequal(n,A)(m,B) ==> Mequal(n,A)(m,B)) (@mx_force n m).
  Proof. unfold Proper, respectful. intros. rewrite 2 mx_force_id. assumption. Qed.


  (* sous-matrices *)
  
  Definition subMat n' m' x y n m (M: MX(n',A)(m',B)) : MX(n,A)(m,B) 
    := box n m (fun i j => !M (x+i)%nat (y+j)%nat).
(*
  Global Instance subMat_compat x y n m:
  Proper (Mequal(x+n,A)%nat(y+m,B)%nat ==> Mequal(n,A)(m,B))
  (subMat x y n m).
  Proof. repeat intro. simpl. auto with omega. Qed.
*)
  Section Subs.
    Variables x y n m: nat.
    Section Def.
      Variable M: MX(x+n,A)%nat(y+m,B)%nat.
      Definition sub00 := subMat 0 0 x y M.
      Definition sub01 := subMat 0 y x m M.
      Definition sub10 := subMat x 0 n y M.
      Definition sub11 := subMat x y n m M.
    End Def.
    Global Instance sub00_compat: Proper (Mequal(x+n,A)%nat(y+m,B)%nat ==> Mequal(x,A)(y,B)) sub00.
    Proof. repeat intro. simpl. apply H; auto with omega. Qed.
    Global Instance sub01_compat: Proper (Mequal(x+n,A)%nat(y+m,B)%nat ==> Mequal(x,A)(m,B)) sub01.
    Proof. repeat intro. simpl. apply H; auto with omega. Qed.
    Global Instance sub10_compat: Proper (Mequal(x+n,A)%nat(y+m,B)%nat ==> Mequal(n,A)(y,B)) sub10.
    Proof. repeat intro. simpl. apply H; auto with omega. Qed.
    Global Instance sub11_compat: Proper (Mequal(x+n,A)%nat(y+m,B)%nat ==> Mequal(n,A)(m,B)) sub11.
    Proof. repeat intro. simpl. apply H; auto with omega. Qed.
  End Subs.
(*    
  Lemma mx_column_equal: forall n m (M N: MX(n,A)(m,B)),
    (forall j, j < m -> subMat 0 j n 1%nat M == subMat 0 j n 1%nat N) <-> M == N. 
  Proof.
    split; repeat intro.
     replace j with (j+0)%nat by auto with arith. apply H; auto.
     apply H; auto with omega.
  Qed.

  Lemma mx_line_equal: forall n m (M N: MX(n,A)(m,B)),
    (forall i, i < n -> subMat i 0 1%nat m M == subMat i 0 1%nat m N) <-> M == N. 
  Proof.
    split; repeat intro.
     replace i with (i+0)%nat by auto with arith. apply H; auto.
     apply H; auto with omega.
  Qed.
*)


  (* matrices par blocs *)

  Section Blocks.
    
    Variables x y n m: nat.

    Definition makeMat_blocks 
      (M: MX(x,A)(y,B))
      (N: MX(x,A)(m,B))
      (P: MX(n,A)(y,B))
      (Q: MX(n,A)(m,B)): (MX(x+n,A)(y+m,B))%nat
      := box _ _ 
      (fun i j => 
        match S i-x, S j-y with
          | O,   O   => !M i j
          | S i, O   => !P i j
          | O,   S j => !N i j
          | S i, S j => !Q i j
        end). 

    Global Instance makeMat_blocks_compat:
    Proper (
      (Mequal (x,A) (y,B))   ==>
      (Mequal (x,A) (m,B))  ==>
      (Mequal (n,A) (y,B))  ==>
      (Mequal (n,A) (m,B)) ==>
      (Mequal ((x+n)%nat,A) ((y+m)%nat,B)))
    (makeMat_blocks).
    Proof. 
      repeat intro. simpl. destruct_blocks; auto with omega.
    Qed.

    Lemma decomposeMat_blocks :
      forall M: MX(x+n,A)%nat(y+m,B)%nat,
        M ==
          makeMat_blocks
          (sub00 M)
          (sub01 M)
          (sub10 M)
          (sub11 M).
    Proof.
      simpl. intros. destruct_blocks; auto with omega. 
    Qed.
  
    Section Proj.

      Variables (a: MX(x,A)(y,B)) (b: MX(x,A)(m,B)) (c: MX(n,A)(y,B)) (d: MX(n,A)(m,B)).
  
      Lemma mx_block_00: sub00 (makeMat_blocks a b c d) == a.
      Proof.
        simpl. intros. destruct_blocks; reflexivity || omega_false.
      Qed.
    
      Lemma mx_block_01: sub01 (makeMat_blocks a b c d) == b.
      Proof.
        simpl. intros. destruct_blocks; omega_false || auto with compat omega.
      Qed.
    
      Lemma mx_block_10: sub10 (makeMat_blocks a b c d) == c.
      Proof.
        simpl. intros. destruct_blocks; omega_false || auto with compat omega.
      Qed.
    
      Lemma mx_block_11: sub11 (makeMat_blocks a b c d) == d.
      Proof.
        simpl. intros. destruct_blocks; omega_false || auto with compat omega.
      Qed.

    End Proj.
  
    Lemma mx_blocks_equal: forall (a a': MX(x,A)(y,B)) b b' c c' (d d': MX(n,A)(m,B)), 
      makeMat_blocks a b c d == makeMat_blocks a' b' c' d' ->
      a==a' /\ b==b' /\ c==c' /\ d==d'.
    Proof.
      intros.
      rewrite <- (mx_block_11 a b c d) at 1.
      rewrite <- (mx_block_10 a b c d) at 1.
      rewrite <- (mx_block_01 a b c d) at 1.
      rewrite <- (mx_block_00 a b c d) at 1.
      rewrite H.
      rewrite mx_block_00, mx_block_01, mx_block_10, mx_block_11.
      repeat split; reflexivity. 
    Qed.

  End Blocks.


  Lemma makeMat_blocks_degenerate_00 (a: MX(S O,A)(S O,B)) b c (d: MX(O,A)(O,B)):
    makeMat_blocks a b c d == a.
  Proof.
    intros a b c d [|] [|] Hi Hj; try omega_false. reflexivity. 
  Qed.


  (* conversions éléments/matrices *)
  
  Definition scal_to_Mat (x: X A B): MX(1%nat,A)(1%nat,B) := box 1 1 (fun _ _ => x).
  Definition Mat_to_scal (M: MX(1%nat,A)(1%nat,B)): X A B := !M O O.
  
  Global Instance scal_to_Mat_compat: 
  Proper ((equal A B) ==> (Mequal (1%nat,A) (1%nat,B))) scal_to_Mat.
  Proof. repeat intro. simpl. trivial. Qed.
  
  Global Instance Mat_to_scal_compat: 
  Proper ((Mequal (1%nat,A) (1%nat,B)) ==> (equal A B)) Mat_to_scal.
  Proof. repeat intro. simpl. apply H; auto. Qed.

  Lemma scal_to_Mat_morph (M: MX(1%nat,A)(1%nat,B)):
    M == scal_to_Mat (Mat_to_scal M).
  Proof. simpl. unfold Mat_to_scal. auto with omega. Qed.

  Lemma Meq_to_eq: forall (a b: X A B), scal_to_Mat a == scal_to_Mat b -> a == b.
  Proof.
    intros a b H. apply (H O O); auto.
  Qed.

  Lemma eq_to_Meq: forall (a b: MX(1%nat,A)(1%nat,B)), Mat_to_scal a == Mat_to_scal b -> a == b.
  Proof.
    intros a b H. mx_intros i j Hi Hj. apply H.
  Qed.



  (* transposée *)

  Definition transpose n m (M : MX(n,A)(m,B)): MX(m,A)(n,B) := box m n (fun i j => !M j i).
  
  Global Instance transpose_compat n m: 
  Proper (Mequal (n,A)(m,B) ==> Mequal (m,A)(n,B)) (@transpose n m).
  Proof. repeat intro. simpl. apply H; trivial. Qed.

  Lemma transpose_blocks x y n m (a: MX(x,A)(y,B)) b c (d: MX(n,A)(m,B)):
    transpose (makeMat_blocks a b c d) == makeMat_blocks (transpose a) (transpose c) (transpose b) (transpose d).
  Proof.
    repeat intro. simpl. destruct_blocks;  reflexivity.
  Qed.

End Props.

(*
Section Protect.
  Lemma mx_rev_T {G: Graph}: @T (@mx_Graph (@Graph.Reversed G)) = @T (@Graph.Reversed (@mx_Graph G)).
  Proof (fun _ => refl_equal _).

  Lemma mx_rev_X {G: Graph}: @X (@mx_Graph (@Graph.Reversed G)) = @X (@Graph.Reversed (@mx_Graph G)).
  Proof (fun _ => refl_equal _).

  Definition mx_equal_dual {G: Graph} nA mB: relation (MX nA mB) := fun M N => forall i j, i<fst mB -> j<fst nA -> M i j == N i j.

  Lemma mx_rev_equal {G: Graph}: @equal (@Graph.Reversed (@mx_Graph G)) = @mx_equal_dual (@Graph.Reversed G).
  Proof (fun _ => refl_equal _).

  Lemma mx_rev_equal' {G: Graph}: @equal (@mx_Graph (@Graph.Reversed G)) = @mx_equal_dual (@Graph.Reversed G).
  Proof. intro. reflexivity.
    destruct G. 
    compute.
    Set Printing All.

(*
    refine (refl_equal _). reflexivity. . refl_equal _.

  Instance Reversed `{Graph}: Graph := {
    T := T;
    X A B := X B A;
    equal A B := equal B A;
    equal_equivalence A B := equal_equivalence B A
  }.
*)
End Protect.
*)

Ltac fold_MT :=
  repeat 
    match goal with 
      |- context[(?n:nat,?A:@T _)] => 
        let x := fresh "nA" in
          set (x:=(n,A):@T (@mx_Graph _)) in *
    end.

Ltac unfold_MT :=
  repeat
    match goal with 
      x := (_,_):@T (@mx_Graph _) |- _ => unfold x in *; clear x
    end. 

Tactic Notation "patched" tactic(tac) := fold_MT; tac; unfold_MT.

(* Hint Extern 2 (Mequal _ _ _ _) => eapply sub_equal_compat; [ | | eassumption] : compat algebra.  *)
(* Hint Extern 1 (Mequal _ _ _ _) => apply subMat_compat: compat algebra. *)
Hint Extern 1 (Mequal _ _ _ _) => apply sub00_compat: compat algebra.
Hint Extern 1 (Mequal _ _ _ _) => apply sub01_compat: compat algebra.
Hint Extern 1 (Mequal _ _ _ _) => apply sub10_compat: compat algebra.
Hint Extern 1 (Mequal _ _ _ _) => apply sub11_compat: compat algebra.
Hint Extern 1 (Mequal _ _ _ _) => apply transpose_compat: compat algebra.
Hint Extern 1 (Mequal _ _ _ _) => apply mx_force_compat: compat algebra.
Hint Extern 4 (Mequal _ _ _ _) => apply makeMat_blocks_compat: compat algebra.
Hint Extern 1 (Mequal _ _ _ _) => apply scal_to_Mat_compat: compat algebra.
Hint Extern 1 ( equal _ _ _ _) => apply Mat_to_scal_compat: compat algebra.
Hint Extern 5 ( equal _ _ _ _) => apply equal_compat : compat algebra.

(* Hint Resolve @equal_compat: compat algebra.  *)
  
(* Hint Resolve  *)
(*   @subMat_compat @makeMat_blocks_compat  *)
(*   @scal_to_Mat_compat @Mat_to_scal_compat *)
(*   : compat algebra. *)



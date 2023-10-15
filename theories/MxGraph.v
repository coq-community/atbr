(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Basic definitions for matrices: definition of their [Graph] *)

From ATBR Require Import Common.
From ATBR Require Import Classes.
From ATBR Require Import Graph.
From Coq Require List.
From ATBR Require Force.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Defs.

  Context {G: Graph}.
  Variable A: T.
  Notation X := (X A A).

  (** [n] and [m] are phantom types, a matrix is a function from two [nat] to X *)
  Inductive MX (n m: nat) := 
    box: (nat -> nat -> X) -> MX n m.

  Definition get n m (M: MX n m) := let (f) := M in f.

  (** matrix equality is bounded pointwise equality  *)

  Definition mx_equal n m: relation (MX n m) := 
    fun M N => forall i j, i<n -> j<m -> get M i j == get N i j.

  (** matrix Graph, equality is bounded pointwise equality  *)
  Program Instance mx_Graph: Graph := {
    T := nat;
    X := MX;
    equal := mx_equal }.
  Next Obligation.
    split; repeat intro; simpl in *.
    reflexivity.
    symmetry; auto.
    transitivity (get y i j); auto.
  Qed.

  Lemma mx_equal': forall n m (M N: @Classes.X mx_Graph n m) 
    (H: forall i j, i<n -> j<m -> get M i j == get N i j), M == N.
  Proof.
    exact (fun _ _ _ _ H => H).
  Qed.
  
  Definition mx_equal_at p q n m n' m' (M : MX n m) (N : MX n' m') := 
    forall i j, i < p -> j < q -> get M i j == get N i j.

  Lemma mx_equal_at_equal n m (M N: @Classes.X mx_Graph n m) : mx_equal_at n m M N <-> M == N.
  Proof. intros. unfold mx_equal_at. intuition. Qed.
End Defs.

Notation MX_ A n m := (@X (mx_Graph A) (n%nat:nat) (m%nat:nat)) (only parsing).
Notation mx_equal_ A n m := (@equal (mx_Graph A) (n%nat) (m%nat)) (only parsing).

Notation "! M" := (get M) (at level 0) : A_scope.
Notation "M == [ n , m ]  N" := (@equal (mx_Graph _) n m M N) (at level 80) : A_scope.

Lemma plus_minus : forall m n, S (m+n)-n = S m.
Proof. intros. lia. Qed.
#[global] Opaque minus. 

Lemma lt_n_1 n: ~ (S n<1)%nat.
Proof. lia. Qed.

(** case analysis on block matrix acesses *)
Ltac destruct_blocks :=
  unfold mx_equal; intros; simpl;
  rewrite ? plus_minus; 
  repeat match goal with 
           | |- context[S ?i - ?n] => case_eq (S i - n); intros 
         end. 

(** tactic to pointwise check matrix equality *)
Ltac mx_intros i j Hi Hj :=
  apply mx_equal'; intros i j Hi Hj;
  match type of Hi with
    | i < 0%nat => elim (Nat.nlt_0_r _ Hi)
    | i < 1%nat => destruct i; [clear Hi | elim (lt_n_1 Hi)]
    | _ => idtac
  end;
  match type of Hj with
    | j < 0%nat => elim (Nat.nlt_0_r _ Hj)
    | j < 1%nat => destruct j; [clear Hj | elim (lt_n_1 Hj)]
    | _ => idtac
  end.

Transparent equal.

Section Props.

  Context {G: Graph}.
  Variable A: T.
  Notation MX n m := (MX_ A n m).
  Notation mx_equal n m := (mx_equal_ A n m) (only parsing).

  Lemma mx_equal_compat n m: forall M N: MX n m, 
    M == N -> 
    forall i j i' j', i<n -> j<m -> i=i' -> j=j' -> !M i j == !N i' j'.
  Proof. intros; subst; auto. Qed.
    
  Definition mx_force n m (M: MX n m): MX n m := box n m (Force.id2 n m !M).
  Definition mx_print n m (M: MX n m) := Force.print2 n m !M.
  Definition mx_noprint n m (M: MX n m) := let _ := mx_force M in (n,m).

  Lemma mx_force_id n m (M: MX n m): mx_force M == M.
  Proof. repeat intro; unfold mx_force. simpl. rewrite Force.id2_id by assumption. reflexivity. Qed.

  #[global] Instance mx_force_compat n m: Proper (mx_equal n m ==> mx_equal n m) (@mx_force n m).
  Proof. intros M N H. rewrite 2 mx_force_id. assumption. Qed.

  #[global] Instance box_compat n m: 
  Proper (pointwise_relation nat (pointwise_relation nat (equal A A)) ==> mx_equal n m) (box n m).
  Proof. intros. intros f g H. mx_intros i j Hi Hj. apply H. Qed.


  (** sub-matrix  *)
  Definition mx_sub n' m' x y n m (M: MX n' m') : MX n m 
    := box n m (fun i j => !M (x+i) (y+j))%nat.

  (** special case of block matrices  *)
  Section Subs.
    Variables x y n m: nat.
    Section Def.
      Variable M: MX (x+n) (y+m).
      Definition mx_sub00 := mx_sub 0 0 x y M.
      Definition mx_sub01 := mx_sub 0 y x m M.
      Definition mx_sub10 := mx_sub x 0 n y M.
      Definition mx_sub11 := mx_sub x y n m M.
    End Def.
    #[global] Instance mx_sub00_compat: Proper (mx_equal (x+n) (y+m) ==> mx_equal x y) mx_sub00.
    Proof. repeat intro. simpl. apply H; auto with lia. Qed.
    #[global] Instance mx_sub01_compat: Proper (mx_equal (x+n) (y+m) ==> mx_equal x m) mx_sub01.
    Proof. repeat intro. simpl. apply H; auto with lia. Qed.
    #[global] Instance mx_sub10_compat: Proper (mx_equal (x+n) (y+m) ==> mx_equal n y) mx_sub10.
    Proof. repeat intro. simpl. apply H; auto with lia. Qed.
    #[global] Instance mx_sub11_compat: Proper (mx_equal (x+n) (y+m) ==> mx_equal n m) mx_sub11.
    Proof. repeat intro. simpl. apply H; auto with lia. Qed.
  End Subs.



  Section Blocks.
    
    Variables x y n m: nat.

    (** block matrix  *)
    Definition mx_blocks 
      (M: MX x y)
      (N: MX x m)
      (P: MX n y)
      (Q: MX n m): MX (x+n) (y+m)
      := box _ _ 
      (fun i j => 
        match S i-x, S j-y with
          | O,   O   => !M i j
          | S i, O   => !P i j
          | O,   S j => !N i j
          | S i, S j => !Q i j
        end). 

    #[global] Instance mx_blocks_compat:
    Proper (
      mx_equal x y ==>
      mx_equal x m ==>
      mx_equal n y ==>
      mx_equal n m ==>
      mx_equal (x+n) (y+m))
    mx_blocks.
    Proof. 
      repeat intro. destruct_blocks; auto with lia.
    Qed.

    Lemma mx_decompose_blocks :
      forall M: MX (x+n) (y+m),
        M ==
          mx_blocks
          (mx_sub00 M)
          (mx_sub01 M)
          (mx_sub10 M)
          (mx_sub11 M).
    Proof.
      simpl; intros. destruct_blocks; auto with lia. 
    Qed.
  
    Section Proj.

      Variables (a: MX x y) (b: MX x m) (c: MX n y) (d: MX n m).
  
      Lemma mx_block_00: mx_sub00 (mx_blocks a b c d) == a.
      Proof.
        simpl. intros. destruct_blocks; reflexivity || lia_false.
      Qed.
    
      Lemma mx_block_01: mx_sub01 (mx_blocks a b c d) == b.
      Proof.
        simpl. intros. destruct_blocks; lia_false || auto with compat lia.
      Qed.
    
      Lemma mx_block_10: mx_sub10 (mx_blocks a b c d) == c.
      Proof.
        simpl. intros. destruct_blocks; lia_false || auto with compat lia.
      Qed.
    
      Lemma mx_block_11: mx_sub11 (mx_blocks a b c d) == d.
      Proof.
        simpl. intros. destruct_blocks; lia_false || auto with compat lia.
      Qed.

    End Proj.
  
    Lemma mx_blocks_equal: forall (a a': MX x y) b b' c c' (d d': MX n m), 
      mx_blocks a b c d == mx_blocks a' b' c' d' ->
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


  Lemma mx_blocks_degenerate_00 (a: MX 1 1) b c (d: MX 0 0):
    (mx_blocks a b c d: MX 1 1) == a.
  Proof.
    intros [|] [|] Hi Hj; try lia_false. reflexivity. 
  Qed.

  Lemma mx_blocks_degenerate_11 n m (a: MX 0 0) b c (d: MX n m):
    (mx_blocks a b c d: MX n m) == d.
  Proof.
    mx_intros i j Hi Hj. reflexivity. 
  Qed.





  (** conversions from and to scalars  *)
  Definition mx_of_scal (x: X A A): MX 1 1 := box 1 1 (fun _ _ => x).
  Definition mx_to_scal (M: MX 1 1): X A A := !M O O.
  
  #[global] Instance mx_of_scal_compat: 
  Proper (equal A A ==> mx_equal 1 1) mx_of_scal.
  Proof. repeat intro. simpl. trivial. Qed.
  
  #[global] Instance mx_to_scal_compat: 
  Proper (mx_equal 1 1 ==> equal A A) mx_to_scal.
  Proof. repeat intro. simpl. apply H; auto. Qed.

  Lemma mx_to_scal_from_scal (M: MX 1 1):
    M == mx_of_scal (mx_to_scal M).
  Proof. mx_intros i j Hi Hj. reflexivity. Qed.

  Lemma Meq_to_eq: forall a b, mx_of_scal a == mx_of_scal b -> a == b.
  Proof.
    intros a b H. apply (H O O); auto.
  Qed.

  Lemma eq_to_Meq: forall a b, mx_to_scal a == mx_to_scal b -> a == b.
  Proof.
    intros a b H. mx_intros i j Hi Hj. apply H.
  Qed.



  (** transposition  *)
  Definition mx_transpose n m (M : MX n m): MX m n := box m n (fun i j => !M j i).
  
  #[global] Instance mx_transpose_compat n m: 
  Proper (mx_equal n m ==> mx_equal m n) (@mx_transpose n m).
  Proof. repeat intro. simpl. apply H; trivial. Qed.

  Lemma mx_transpose_blocks x y n m (a: MX x y) b c (d: MX n m):
    mx_transpose (mx_blocks a b c d) 
    == mx_blocks (mx_transpose a) (mx_transpose c) (mx_transpose b) (mx_transpose d).
  Proof.
    repeat intro. simpl. destruct_blocks;  reflexivity.
  Qed.

End Props.

#[global] Hint Extern 1 (mx_equal_ _ _ _ _ _) => apply mx_sub00_compat: compat algebra.
#[global] Hint Extern 1 (mx_equal_ _ _ _ _ _) => apply mx_sub01_compat: compat algebra.
#[global] Hint Extern 1 (mx_equal_ _ _ _ _ _) => apply mx_sub10_compat: compat algebra.
#[global] Hint Extern 1 (mx_equal_ _ _ _ _ _) => apply mx_sub11_compat: compat algebra.
#[global] Hint Extern 1 (mx_equal_ _ _ _ _ _) => apply mx_transpose_compat: compat algebra.
#[global] Hint Extern 1 (mx_equal_ _ _ _ _ _) => apply mx_force_compat: compat algebra.
#[global] Hint Extern 4 (mx_equal_ _ _ _ _ _) => apply mx_blocks_compat: compat algebra.
#[global] Hint Extern 1 (mx_equal_ _ _ _ _ _) => apply mx_of_scal_compat: compat algebra.
#[global] Hint Extern 1 (equal _ _ _ _) => apply mx_to_scal_compat: compat algebra.
#[global] Hint Extern 5 (equal _ _ _ _) => apply mx_equal_compat : compat algebra.

(* Hint Resolve @equal_compat: compat algebra.  *)
  
(* Hint Resolve  *)
(*   @mx_sub_compat @mx_blocks_compat  *)
(*   @scal_to_Mat_compat @Mat_to_scal_compat *)
(*   : compat algebra. *)

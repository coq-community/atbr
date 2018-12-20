(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Memoisation function for matrices: we define an identity function
   that enforces evaluation *)

Require Import List.
Require Import Arith.
Set Implicit Arguments.

Section force.
  Variable T: Type.
  Variable f: nat -> T.

  Fixpoint force_rec acc i :=
    match i with
      | O => acc
      | S i => force_rec (f i :: acc) i
      end.

  Fixpoint nth i l :=
    match l,i with
      | nil, _ => f O           	(* absurd *)
      | a::_, O => a
      |_::q, S i => nth i q
    end.
End force.

Definition print T n f := @force_rec T f nil n.

Definition id T n f := 
    let l := @print T n f in
      fun i => nth f i l. 

Section correction.
  Variable T: Type.

  Lemma force_rec_rec: forall (f: nat -> T) i a, force_rec f a (S i) = f 0 :: force_rec (fun k => f (S k)) a i.
  Proof.
    induction i; intros a; simpl.
    reflexivity.
    apply IHi.
  Qed.

  Lemma nth_force_rec: forall n (f g: nat -> T) i a, i<n -> nth g i (force_rec f a n) = f i.
  Proof.
    induction n; intros f g i a H.
     inversion H.
     rewrite force_rec_rec. destruct i. 
      reflexivity.
      refine (IHn _ _ _ _ _). auto with arith.
  Qed.

  Lemma nth_force_rec': forall n (f g: nat -> T) i, n<=i -> nth g i (force_rec f nil n) = g O.
  Proof.
    induction n; intros f g i H. case i; reflexivity.
     rewrite force_rec_rec. destruct i. inversion H.
     simpl. apply IHn. auto with arith.
  Qed.

  Lemma id_id: forall n (f: nat -> T) i, i<n -> id n f i = f i.
  Proof.
    intros. apply nth_force_rec. assumption.
  Qed.

  Lemma id_notid: forall n (f: nat -> T) i, n<=i -> id n f i = f O.
  Proof.
    intros. apply nth_force_rec'. assumption.
  Qed.

End correction.

Section force2.
  Variable T: Type.
  Variables n m: nat.
  Variable f: nat -> nat -> T.

  Definition id2 := id n (fun i => id m (f i)).
  Definition print2 := print n (fun i => print m (f i)).

  Lemma id2_id: forall i j, i<n -> j<m -> id2 i j = f i j.
  Proof.
    intros; unfold id2.
    rewrite id_id by assumption.
    apply id_id; assumption.
  Qed.
End force2.

(*begintests

   Let m i := mult i i - i.
   Eval compute in print 5 m. 
   Time   Eval vm_compute in let _ := print 100 (id 100 m) in true. 

   Let n i j := mult i (j+1).
   Eval compute in print2 3 5 n. 
   Eval compute in print2 3 5 (id2 3 5 n). 

endtests*)

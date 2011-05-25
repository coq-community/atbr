(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2011: Thomas Braibant, Damien Pous.                    *)
(**************************************************************************)

(** (min,+) Kleene algebra 

   By taking matrices over this model, we get weighted graphs. For
   example, given a matrix [R] coding for the cost for moving from one
   state to another one, [R# i j] gives the cost of the shortest path
   from i to j. *)

Require Import Common.
Require Import Classes.
Require Import MinMax.
Require        Converse.
Set Implicit Arguments.
Unset Strict Implicit.

Definition onat := option nat.
Notation infty := None.

Definition mp_union (x y: onat): onat := 
  match x,y with
    | infty,_ => y
    | _,infty => x
    | Some x, Some y => Some (MinMax.min x y)
  end.
Definition mp_comp  (x y: onat): onat :=
  match x,y with
    | infty,_ => infty
    | _,infty => infty
    | Some x, Some y => Some (Peano.plus x y)
  end.

Definition mp_conv  (x: onat): onat := x.
Definition mp_id: onat := Some O.
Definition mp_empty: onat := infty.
Definition mp_star (_: onat): onat := mp_id.

Section protect.

  Program Instance mp_Graph: Graph := {
    T := unit;
    X A B := onat;
    equal A B := eq
  }.
  
  Instance mp_SemiLattice_Ops: SemiLattice_Ops mp_Graph := {
    plus A B := mp_union;
    zero A B := mp_empty
  }.
  
  Instance mp_Monoid_Ops: Monoid_Ops mp_Graph := {
    dot A B C := mp_comp;
    one A := mp_id
  }.
  
  Instance mp_Star_Op: Star_Op mp_Graph := { 
    star A := mp_star
  }.
  
  Instance mp_Converse_Op: Converse_Op mp_Graph := { 
    conv A B := mp_conv
  }.
  
  Transparent equal.
  
  Instance mp_SemiLattice: SemiLattice mp_Graph.
  Proof.
    constructor; simpl.
     eauto with typeclass_instances.
     reflexivity.
     destruct x; simpl; trivial. rewrite min_id. reflexivity. 
     destruct x; trivial. destruct y; trivial. destruct z; trivial. simpl. rewrite min_assoc. reflexivity. 
     destruct x; trivial. destruct y; trivial. simpl. rewrite min_comm. reflexivity. 
     destruct y; reflexivity.
  Qed.
  
  Instance mp_ConverseSemiRing: ConverseIdemSemiRing mp_Graph.
  Proof.
    constructor; simpl; eauto with typeclass_instances. 
     destruct x; trivial. destruct y; trivial. destruct z; trivial. simpl. rewrite Plus.plus_assoc. reflexivity. 
     destruct x; reflexivity. 
     destruct x; trivial. destruct y; trivial. simpl. rewrite plus_comm. reflexivity. 
     destruct y; reflexivity.
     destruct x; trivial. destruct y; trivial. simpl. rewrite min_comm. reflexivity. 
     destruct y; reflexivity.
     destruct x; trivial. destruct y; trivial; destruct z; trivial. simpl. 
     rewrite plus_min_distr_r. reflexivity. 
  Qed.
  
  Definition mp_IdemSemiRing: IdemSemiRing mp_Graph := Converse.CISR_ISR.  
   
  Instance mp_ConverseKleeneAlgebra: ConverseKleeneAlgebra mp_Graph.
  Proof.
    constructor; simpl; unfold mp_star, mp_id; eauto with typeclass_instances.
    destruct a; trivial.
    destruct c; trivial. intros _. simpl. rewrite min_idempotent. reflexivity.
  Qed.
  
  Definition mp_KleeneAlgebra: KleeneAlgebra mp_Graph := Converse.CKA_KA.  

End protect.


(** Import this module to work in the (min,+) algebra *)
Module Load.

  Existing Instance mp_Graph.
  Existing Instance mp_SemiLattice_Ops.
  Existing Instance mp_Monoid_Ops.
  Existing Instance mp_Converse_Op.
  Existing Instance mp_SemiLattice.
  Existing Instance mp_Star_Op.
  Existing Instance mp_KleeneAlgebra.
  
  Canonical Structure mp_Graph.
  
  Transparent equal plus dot one zero star. 

  Ltac fold_mpAlg := 
    unfold mp_star;
    change (@eq onat) with (@equal mp_Graph tt tt); 
      change (Some O) with (@one mp_Graph mp_Monoid_Ops tt);
      change mp_id with (@one mp_Graph mp_Monoid_Ops tt);
        change mp_comp with (@dot mp_Graph mp_Monoid_Ops tt tt tt);
          change mp_union with (@plus mp_Graph mp_SemiLattice_Ops tt tt);
            change (@None nat) with (@zero mp_Graph mp_SemiLattice_Ops tt tt);
            change mp_empty with (@zero mp_Graph mp_SemiLattice_Ops tt tt).
    
End Load.


(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Generic reification, for the classes from [Classes.v] to the inductives from [Reification.v] *)

DECLARE PLUGIN "reification_plugin"

open Ltac_plugin
open Reify

(* tactic grammar entries *)
TACTIC EXTEND kleene_reify [ "kleene_reify" ] -> [ reify_goal Reify.Reification.KA.ops ] END
TACTIC EXTEND semiring_reify [ "semiring_reify" ] -> [ reify_goal Reify.Reification.Semiring.ops ] END

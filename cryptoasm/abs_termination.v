(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import ZArith_ext uniq_tac machine_int uniq_tac.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib mips_syntax.
Import expr_m.
Require Import abs_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma abs_termination st h a0 a1 : uniq(a0, a1, r0) ->
  { s' | Some (st, h) -- abs a0 a1 ---> s' }.
Proof.
move=> Hregs.
rewrite /abs.
apply constructive_indefinite_description.
by apply no_while_terminate.
Qed.

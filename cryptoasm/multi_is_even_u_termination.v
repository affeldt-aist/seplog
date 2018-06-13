(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib mips_syntax.
Import expr_m.
Require Import multi_is_even_u_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma multi_is_even_u_termination st h a0 a1 a2 : uniq(a0, a1, a2, r0) ->
  { s' | Some (st, h) -- multi_is_even_u a0 a1 a2 ---> s' }.
Proof.
move=> Hregs.
rewrite /multi_is_even_u.
apply constructive_indefinite_description.
by apply no_while_terminate.
Qed.



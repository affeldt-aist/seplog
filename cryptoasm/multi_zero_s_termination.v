(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import ZArith_ext.
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Import expr_m.
Require Import multi_zero_s_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.

Lemma multi_zero_s_termination st h ru :
  {s' | Some (st, h) -- multi_zero_s ru ---> s'}.
Proof. rewrite /multi_zero_s. by apply exists_sw. Qed.

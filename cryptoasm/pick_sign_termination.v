(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool seq.
Require Import ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Require Import pick_sign_prg.
Import expr_m.

Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope machine_int_scope.
Local Open Scope uniq_scope.

Lemma pick_sign_termination st h rx a0 a1 : uniq(rx, a0, a1, r0) ->
  { s' | Some (st, h) -- pick_sign rx a0 a1 ---> s' }.
Proof.
move=> Hregs.
have : {s' : option (store.t * heap.t) |
   Some (st, h) -- pick_sign rx a0 a1 ---> s' /\
   forall st, s' = Some st -> True }.
  rewrite /pick_sign.
  exists_lw l_m_ H_l_m_ z_m_ H_z_m_.
  apply exists_ifte_P.
    by apply exists_addiu_P.
  apply exists_srl_seq_P.
  apply exists_ifte_P.
    by apply exists_addiu_P.
  by apply exists_addiu_P.
case => s' [Hs' _].
by exists s'.
Qed.

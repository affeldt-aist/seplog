(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool seq.
Require Import ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Require Import multi_negate_prg.
Import expr_m.

Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope machine_int_scope.
Local Open Scope uniq_scope.

Lemma multi_negate_termination s h rx a0 : uniq(rx, a0, r0) ->
  { si | Some (s, h) -- multi_negate rx a0 ---> si }.
Proof.
move=> Hnodup.
have : { si | Some (s, h) -- multi_negate rx a0 ---> si /\ 
  (forall s, si = Some s -> True)}.
  rewrite /multi_negate.
  exists_lw l_idx H_l_idx z_idx H_z_idx.
  apply exists_subu_seq_P.
  repeat Reg_upd.
  rewrite add0i.
  repeat Reg_upd.
  apply exists_sw_P with l_idx => //.
  by repeat Reg_upd.
case=> si Hsi.
exists si; tauto.
Qed.

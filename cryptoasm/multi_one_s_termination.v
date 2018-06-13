(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext seq_ext machine_int uniq_tac.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import multi_one_s_prg multi_zero_s_prg multi_zero_u_termination.
Require Import multi_negate_termination.

Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope machine_int_scope.
Local Open Scope uniq_scope.

Lemma termination_zero_s' s h rx a0 a1 a2 a3 : uniq(rx, a0, a1, a2, a3, r0) ->
  { si | Some (s, h) -- multi_zero_s' rx a0 a1 a2 a3 ---> si}.
Proof.
move=> Hnodup.
rewrite /multi_zero_s'.
set code := (_ ; _)%mips_cmd.
have : { si | Some (s, h) -- code ---> si /\ (forall s, si = Some s -> True) }.
  rewrite /code.
  exists_lw l_idx H_l_idx z_idx H_z_idx.
  exists_lw l_idx2 H_l_idx2 z_idx2 H_z_idx2.
  set s_ := store.upd _ _ _.
  have Hset : uniq(a0, a1, a2, a3, r0) by Uniq_uniq r0.
  case: {Hset}(multi_zero_u_termination s_ h _ _ _ _ Hset) => si Hsi.
  by exists si.
case=> si Hsi.
exists si; tauto.
Qed.

Lemma multi_one_s_termination st h rx rk a0 a1 a2 a3 : uniq(rx, rk, a0, a1, a2, a3, r0) ->
  { si | Some (st, h) -- multi_one_s rx rk a0 a1 a2 a3 ---> si }.
Proof.
move=>Hset.
set code := multi_one_s _ _ _ _ _ _.
  have Htermi : {x0 | Some (st, h) -- code ---> x0 /\ (forall s, x0 = Some s -> True)}.
    rewrite /code /multi_one_s.
    exists_lw l_idx H_l_idx z_idx H_z_idx.
    apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
      apply exists_ifte_P.
        by exists_sw1 l2_idx H_l2_idx z2_idx H_z2_idx.
      apply exists_ifte_P.
        have : uniq(rx, a0, r0) by Uniq_uniq r0.
        move/(multi_negate_termination (store.upd a0 z_idx st) h) => [si hi].
        by exists si.
      eexists.
      split => //.
      by do 2 constructor.
    move=> [[sti hi]|] Hsi.
      have : uniq(rx, a0, a1, a2, a3, r0) by Uniq_uniq r0.
      move/(termination_zero_s' sti hi) => [si2 hi2].
      apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
        by exists si2.
      move=> [[st3 h3]|] Hsi3.
        exists_lw l3_idx H_l3_idx z3_idx H_z3_idx.
        apply exists_addiu_seq_P.
        repeat Reg_upd.
        rewrite add0i.
        by exists_sw1 l4_idx H_l4_idx z4_idx H_z4_idx.
      exists None.
      split=> //.
      by apply while.exec_none.
    exists None.
    split=> //.
    by apply while.exec_none.
  case: Htermi => x0 [Htermi _].
  by exists x0.
Qed.

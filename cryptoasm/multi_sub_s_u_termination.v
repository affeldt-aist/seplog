(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import multi_sub_s_u_prg multi_is_zero_u_termination pick_sign_prg.
Require Import pick_sign_termination copy_u_u_termination multi_add_u_u_termination.
Require Import multi_negate_termination multi_lt_termination multi_sub_u_u_termination.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma multi_sub_s_u0_termination st h rk rx ry a0 a1 a2 a3 a4 a5 rX :
  uniq(rk, rx, ry, a0, a1, a2, a3, a4, a5, rX, r0) ->
  { s' | Some (st, h) -- multi_sub_s_u0 rk rx ry a0 a1 a2 a3 a4 a5 rX ---> s' }.
Proof.
move=> Hregs.
set c := multi_sub_s_u0 _ _ _ _ _ _ _ _ _ _.
have : {s' | Some (st, h) -- c ---> s' /\ forall s, s' = Some s -> True}.
  rewrite /c {c} /multi_sub_s_u0.
  exists_lw l Hl z Hz.
  set s0 := store.upd _ _ _.
  have : uniq(rx,a0,a1,r0) by Uniq_uniq r0.
  case/(pick_sign_termination s0 h rx a0 a1) => s1 Hs1.
  apply exists_seq_P with (fun s' => forall st0, s' = Some st0 -> True).
    by exists s1.
  move=> [[s1' h1']|] Hs1'; last first.
    exists None; split => //; by apply while.exec_none.
  apply exists_ifte_P.
    apply exists_ifte_P.
      have : uniq(rk, rX, ry, a2, a3, a4, r0) by Uniq_uniq r0.
      case/(copy_u_u_termination s1' h1') => s2 Hs2.
      apply exists_seq_P with (fun s' => forall st0, s' = Some st0 -> True).
        by exists s2.
      move=> [[s2' h2']|] Hs2'; last first.
        exists None; split => //; by apply while.exec_none.
      apply exists_addiu_seq_P.
      exists_sw_P k Hk z' Hz'.
      set si := store.upd _ _ _.
      set hi := heap.upd _ _ _.
      have : uniq(rx, a0, r0) by Uniq_uniq r0.
      move/multi_negate_termination.
      case/(_ si hi) => x.
      by exists x.
  have : uniq(rk, rX, ry, a0, a1, a5, a2, a3, a4, r0) by Uniq_uniq r0.
  move/multi_lt_termination.
  case/(_ s1' h1').
  case; last first.
    move=> Hsi.
    exists None; split => //.
    apply while.exec_seq with None => //.
    by apply while.exec_none.
  case=> s2 h2 s2h2.
  apply exists_seq_P with (fun s' => forall s, s' = Some s -> True).
    by exists (Some (s2, h2)).
  case=> [[s2' h2']|] => //; last first.
    move=> _.
    exists None; split => //.
    by apply while.exec_none.
  move=> ?.
  apply exists_ifte_P.
    apply exists_ifte_P.
      apply exists_addiu_seq_P.
      by exists_sw1 a b c d.
    have : uniq(rk, ry, rX, a0, a1, a2, a3, a4, a5, r0) by Uniq_uniq r0.
    move/multi_sub_u_u_termination.
    move/(_ s2' h2' rX) => H2'.
    case: H2' => si H2'.
    by exists si.

    apply exists_seq_P with (fun s' => forall st0, s' = Some st0 -> True).
    have : uniq(rk, rX, ry, a0, a1, a2, a3, a4, a5, r0) by Uniq_uniq r0.
    case/(multi_sub_u_u_termination s2' h2' rX) => si H2'.
    by exists si.
    move=> [[si hi]|]; last first.
      move=> _.
      exists None; split => //.
      by apply while.exec_none.
    move=> _.
    have : uniq(rx, a0, r0) by Uniq_uniq r0.
    move/multi_negate_termination.
    case/(_ si hi) => x.
    by exists x.

    apply exists_addiu_seq_P.
    repeat Reg_upd.
    rewrite add0i.
    have : uniq(rk, a3, ry, rX, a0, a1, a2, r0) by Uniq_uniq r0.
    move/(multi_add_u_u_termination) => H.
    set s2 := store.upd _ _ _.
    case: {H}(H s2 h1' rX) => si Hsi.
    destruct si as [[si hi]|]; last first.
      exists None; split => //.
      apply while.exec_seq with None => //.
      by apply while.exec_none.
    apply exists_seq_P with (fun si => True).
    by exists (Some (si, hi)).
    case.
      case=> si0 hi0 _.  
      by apply exists_mflo_P.
    move=> _.
    exists None; split => //.
    by apply while.exec_none.
case=> x [] Hx _.
by exists x.
Qed.

Lemma multi_sub_s_u_termination st h rk rx ry a0 a1 a2 a3 a4 a5 rX :
  uniq(rk, rx, ry, a0, a1, a2, a3, a4, a5, rX, r0) ->
  { s' | Some (st, h) -- multi_sub_s_u rk rx ry a0 a1 a2 a3 a4 a5 rX ---> s' }.
Proof.
move=> Hregs.
set c := multi_sub_s_u _ _ _ _ _ _ _ _ _ _.
have : {s' | (Some (st, h) -- c ---> s') /\ (forall s, s' = Some s -> True)}.
  rewrite /multi_sub_s_u.
  apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
  have : uniq(rk, ry, a0, a1, a2, r0) by Uniq_uniq r0.
  case/(multi_is_zero_u_termination st h) => si Hsi.
  by exists si.
  move=> [[si hi]|] Hsi; last first.
    exists None; split => //.
    by apply while.exec_none.
  apply exists_ifte_P.
    by apply exists_addiu_P.
    have : uniq(rk,rx,ry,a0,a1,a2,a3,a4,a5,rX,r0) by Uniq_uniq r0.
    move/(multi_sub_s_u0_termination si hi).
    case=> si' Hsi'.
    exists si'; tauto.
case=> si Hsi.
exists si; tauto.
Qed.

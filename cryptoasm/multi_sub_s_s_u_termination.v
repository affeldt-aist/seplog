(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import multi_sub_s_s_u_prg.
Require Import multi_is_zero_u_termination copy_s_s_termination.
Require Import pick_sign_termination copy_s_u_termination.
Require Import multi_add_u_u_termination multi_lt_termination.
Require Import multi_zero_s_termination multi_sub_u_u_termination.
Require Import multi_is_zero_u_termination copy_s_s_termination.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma multi_sub_s_s_u0_termination st h rz rx rk ry a0 a1 a2 a3 a4 ret rX rY :
  uniq(rk, rz, rx, ry, a0, a1, a2, a3, a4, ret, rX, rY, r0) ->
  {s' | Some (st, h) -- multi_sub_s_s_u0 rk rz rx ry a0 a1 a2 a3 a4 ret rX rY ---> s'}.
Proof.
move=> Hregs.
set c := multi_sub_s_s_u0 _ _ _ _ _ _ _ _ _ _ _ _.
have : {s' | Some (st, h) -- c ---> s' /\ forall s, s' = Some s -> True}.
  rewrite /c {c} /multi_sub_s_s_u0.
  exists_lw ly Hly zy Hzy.
  set s0 := store.upd _ _ _.
  exists_lw lx Hlx zx Hzx.
  set s1 := store.upd _ _ _.
  apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
    have : uniq(rx, a0, a1, r0) by Uniq_uniq r0.
    case/(pick_sign_termination s1 h) => s1' h1'.
    by exists s1'.
  move=> [[s2 h2]|] H2; last first.
    exists None; split => //; by apply while.exec_none.
  apply exists_ifte_P.
    apply exists_ifte_P.
      apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
        have : uniq(rk, rz, ry, a0, a1, a2, a3, r0) by Uniq_uniq r0.
        case/(copy_s_u_termination s2 h2) => s2' h2'.
        by exists s2'.
      move=> [[s3 h3]|] H3; last first.
        exists None; split => //; by apply while.exec_none.
      apply exists_addiu_seq_P.
      rewrite sext_Z2u // addi0 store.get_r0.
      apply exists_subu_seq_P.
      Reg_upd.
      rewrite store.get_r0 add0i.
      by exists_sw1 lz Hlz zz Hzz.
    apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
      have : uniq(rk, ry, rX, a0, a1, ret, a2, a3, a4, r0) by Uniq_uniq r0.
      case/(multi_lt_termination s2 h2) => s2' H2'.
      by exists s2'.
  move=> [[s2' h2']|] H2'; last first.
    exists None; split => //; by apply while.exec_none.
  apply exists_ifte_P.
    apply exists_ifte_P.
      apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
        case: (multi_zero_s_termination s2' h2' rz) => s3 h3.
        by exists s3.
      move=> [[s3 h3]|] H3; last first.
        exists None; split => //; by apply while.exec_none.
      by apply exists_addiu_P.
    apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
      have : uniq(rk, rX, ry, a0, a1, a2, a3, a4, ret, r0) by Uniq_uniq r0.
      case/(multi_sub_u_u_termination s2' h2' rY) => s3 h3.
      by exists s3.
    move=> [[s3 h3]|] H3; last first.
      exists None; split => //; by apply while.exec_none.
    apply exists_subu_seq_P.
    by exists_sw1 lz Hlz zz Hzz.
  apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
    have : uniq(rk, ry, rX, a0, a1, a2, a3, a4, ret, r0) by Uniq_uniq r0.
    case/(multi_sub_u_u_termination s2' h2' rY) => s3 h3.
    by exists s3.
  move=> [[s3 h3]|] H3; last first.
    exists None; split => //; by apply while.exec_none.
    by exists_sw1 lz Hlz zz Hzz.
  apply exists_addiu_seq_P.
  rewrite store.get_r0 add0i.
  apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
    have : uniq(rk, a3, rX, ry, a0, a1, a2, r0) by Uniq_uniq r0.
    case/(multi_add_u_u_termination (store.upd a3 (sext 16 one16) s2) h2 rY) => s3 h3.
    by exists s3.
  move=> [[s3 h3]|] H3; last first.
    exists None; split => //; by apply while.exec_none.
  apply exists_mflo_seq_P.
  apply exists_subu_seq_P.
  by exists_sw1 lz Hlz zz Hzz.
case=> s' h'.
exists s'; tauto.
Qed.

Lemma multi_sub_s_s_u_termination st h rz rx rk ry a0 a1 a2 a3 a4 ret X Y :
  uniq(rk, rz, rx, ry, a0, a1, a2, a3, a4, ret, X, Y, r0) ->
  {s' | Some (st, h) -- multi_sub_s_s_u rk rz rx ry a0 a1 a2 a3 a4 ret X Y ---> s'}.
Proof.
move=> Hregs.
set c := multi_sub_s_s_u _ _ _ _ _ _ _ _ _ _ _ _.
have : {s' | (Some (st, h) -- c ---> s') /\ (forall s, s' = Some s -> True)}.
  rewrite /c /multi_sub_s_s_u.
  apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
  have : uniq(rk, ry, a0, a1, a2, r0) by Uniq_uniq r0.
  case/(multi_is_zero_u_termination st h) => si Hsi.
  by exists si.
  move=> [[si hi]|] Hsi; last first.
    exists None; split => //.
    by apply while.exec_none.
  apply exists_ifte_P.
    apply exists_addiu_seq_P.
    rewrite sext_Z2u // addi0 store.get_r0.
    have : uniq(rk,rz,rx,a0,a1,a2,ret,a4,r0) by Uniq_uniq r0.
    case/(copy_s_s_termination (store.upd a3 zero32 si) hi) => si' Hsi'.
    by exists si'.
  case/(multi_sub_s_s_u0_termination si hi) : Hregs => s2 H2.
  by exists s2.
case=> s2 H2.
exists s2; tauto.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import multi_halve_u_prg multi_halve_u_termination.
Require Import multi_is_zero_u_termination multi_halve_s_prg multi_zero_s_prg.
Require Import abs_termination multi_is_even_u_termination multi_incr_u_termination.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma multi_halve_s_termination st h rx a0 a1 a2 a3 a4 a5 :
  uniq(rx, a0, a1, a2, a3, a4, a5, r0) ->
  {x0 | Some (st, h) -- multi_halve_s rx a0 a1 a2 a3 a4 a5 --->x0}.
Proof.
move=> Hregs.
have : {x0 | Some (st, h) -- multi_halve_s rx a0 a1 a2 a3 a4 a5 --->x0 /\
  (forall s, x0 = Some s -> True)}.
  rewrite /multi_halve_s.
  exists_lw l_idx H_l_idx z_idx H_z_idx.
  apply exists_ifte_P.
    by apply exists_addiu_P.
  exists_lw l2_idx H_l2_idx z2_idx H_z2_idx.
  apply exists_ifte_P.
    set s0 := store.upd _ _ _.
    have : uniq(a5, a0, a1, a2, a3, a4, r0) by Uniq_uniq r0.
    case/(multi_halve_u_termination s0 h) => si Hsi.
    apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
      by exists si.
    move=> si' Hsi'.
    destruct si' as [[si' hi']|]; last first.
      exists None.
      split => //.
      apply while.exec_none.
    have : uniq(a5, a0, a1, a2, a4, r0) by Uniq_uniq r0.
    case/(multi_is_zero_u_termination si' hi') => si2 Hsi2.
    apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
      by exists si2.
    move=> si3 Hsi3.
    destruct si3 as [[si3 hi3]|]; last first.
      exists None.
      split => //; exact/while.exec_none.
    apply exists_ifte_P.
      rewrite /multi_zero_s.
      by exists_sw1 l3_idx H_l3_idx z3_idx H_z3_idx.
    exists (Some (si3, hi3)).
    split => //.
    by do 2 constructor.
    set s0 := store.upd _ _ _.
    have : uniq(a5, a1, r0) by Uniq_uniq r0.
    case/(abs_termination s0 h) => si Hsi.
    apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
      by exists si.
    move=> [[si2 hi2]|] Hsi2; last first.
      exists None; split => //.
      by apply while.exec_none.
      have : uniq(a5, a0, a2, r0) by Uniq_uniq r0.
      case/(multi_is_even_u_termination si2 hi2) => si3 Hsi3.
      apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
        by exists si3.
      move=> [[si3' hi3']|] Hsi3'; last first.
        exists None; split => //.
        by apply while.exec_none.
      apply exists_ifte_P.
        have : uniq(a5, a0, a1, a2, a3, a4, r0) by Uniq_uniq r0.
        move/(multi_halve_u_termination si3' hi3').
        case=> si4 Hsi4.
        by exists si4.
      have : uniq(a5, a0, a1, a2, a3, a4, r0) by Uniq_uniq r0.
      case/(multi_halve_u_termination si3' hi3') => si4 Hsi4.
      apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
        by exists si4.
      move=> [[si4' hi4']|] Hsi4'; last first.
        exists None; split => //; exact/while.exec_none.
      apply exists_addiu_seq_P.
      rewrite store.get_r0 add0i.
      set s1 := store.upd _ _ _.
  have : uniq(a5, a4, a0, a1, a2, a3, r0) by Uniq_uniq r0.
  case/(multi_incr_u_termination s1 hi4') => si5 Hsi5.
  apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
    by exists si5.
  move=> [[si5' hi5']|] Hsi5'; last first.
    exists None; split => //; exact/while.exec_none.
  by apply exists_sll_P.
case=> x H.
exists x; tauto.
Qed.

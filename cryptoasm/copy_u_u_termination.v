(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int uniq_tac.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import copy_u_u_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma copy_u_u_termination st h rk ru rx a0 a1 a2 :
  uniq(rk, ru, rx, a0, a1, a2, r0) ->
  {si | Some (st, h) -- copy_u_u rk ru rx a0 a1 a2 ---> si}%mips_cmd.
Proof.
move=> Hset.
rewrite /copy_u_u.
apply exists_addiu_seq.
rewrite sext_Z2u // addi0.
apply exists_addiu_seq.
rewrite sext_Z2u // addi0.
repeat Reg_upd.
set s0 := store.upd _ _ _.
have [na2 Ha2] : { na2 | u2Z [rk]_s0 - u2Z [a2]_s0 = Z_of_nat na2 }%mips_expr.
  have [va2 Hva2] : { va2 | u2Z [rk]_s0 - u2Z [a2]_s0 = va2}%mips_expr by eapply exist; reflexivity.
  have : 0 <= va2.
    move: Hva2.
    rewrite /s0.
    repeat Reg_upd.
    rewrite Z2uK // subZ0 => <-.
    by apply min_u2Z.
  case/Z_of_nat_complete_inf => na2 va2_na2.
  by exists na2; rewrite Hva2.
move: na2 s0 Ha2 h; elim.
- move=> s0 Ha2 h.
  exists (Some (s0, h)).
  apply while.exec_while_false => /=.
  rewrite negbK.
  rewrite /= in Ha2.
  apply/eqP.
  lia.
- move=> na2 IH s0 Hna2 h.
  apply exists_while.
  + rewrite /=.
    apply/eqP => abs.
    rewrite abs Z_S subZZ in Hna2;lia.
  + apply exists_seq_P2 with (fun st => u2Z [rk]_(fst st) - u2Z [a2]_(fst st) = Z_of_nat na2)%mips_expr.
    * exists_lwxs l_idx H_l_idx z_idx H_z_idx.
      exists_sw_P l_idx2 H_l_idx2 z_idx2 H_z_idx2.
      repeat Reg_upd.
      apply exists_addiu_seq_P.
      repeat Reg_upd.
      apply exists_addiu_P.
      rewrite /=.
      repeat Reg_upd.
      rewrite Z_S in Hna2.
      rewrite sext_Z2u // u2Z_add_Z2u //.
      lia.
      move: (min_u2Z ([rk ]_ s0)%mips_expr) => ?.
      move: (min_u2Z ([a2 ]_ s0)%mips_expr) => ?.
      move: (max_u2Z ([rk ]_ s0)%mips_expr) => ?.
      move: (max_u2Z ([a2 ]_ s0)%mips_expr) => ?.
      lia.
    * move=> [si hi] Hna2'.
      by apply IH.
Qed.

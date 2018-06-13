(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import multi_incr_u_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma multi_incr_u_termination st h a0 a1 a2 a3 a4 a5 :
  uniq(a0, a1, a2, a3, a4, a5, r0) ->
  { s' | Some (st, h) -- multi_incr_u a0 a1 a2 a3 a4 a5 ---> s' }.
Proof.
move=> Hregs.
have : {s' | (Some (st, h) -- multi_incr_u a0 a1 a2 a3 a4 a5 ---> s') /\
   (forall s, s' = Some s -> True)}.
  rewrite /multi_incr_u.
  apply exists_addiu_seq_P.
  rewrite store.get_r0 add0i.
  apply exists_addiu_seq_P.
  repeat Reg_upd.
  rewrite sext_Z2u // addi0.
  apply exists_multu_seq_P.
  repeat Reg_upd.
  rewrite umul_0.
  set s0 := store.multu_op _ _.
  have [j Hj] : { j | u2Z [a0]_s0 - u2Z [a4]_s0 = Z_of_nat j}%mips_expr.
    have [j Hj] : { j | u2Z [a0]_s0 - u2Z [a4]_s0 = j}%mips_expr by eapply exist; reflexivity.
    have : 0 <= j. rewrite -Hj /s0. repeat Reg_upd. rewrite Z2uK // subZ0; exact: min_u2Z.
    case/Z_of_nat_complete_inf => j' H.
    exists j'; by rewrite -H.
  elim: j s0 Hj h.
  - move=> s0 Hj h.
    eapply exist.
    split => //.
    apply while.exec_while_false.
    rewrite /= in Hj *.
    repeat Reg_upd.
    apply/negPn/eqP; omega.
  - move=> j IH s0 Hj h.
    apply exists_while_P.
    + rewrite /=.
      repeat Reg_upd.
      apply/eqP; omegaz. (* rewrite Z_S in Hj; omega. *)
    + apply exists_seq_P with (fun s => forall s', s = Some s' ->
        u2Z ([ a0 ]_(fst s')) - u2Z ([a4]_(fst s')) = Z_of_nat j)%mips_expr.
        exists_lwxs l_idx H_l_idx z_idx H_z_idx.
        apply exists_maddu_seq_P.
        repeat Reg_upd.
        apply exists_seq_P with (fun s => forall s', s = Some s' ->
          u2Z ([ a0 ]_(fst s')) - u2Z ([a4]_(fst s')) = Z_of_nat (S j))%mips_expr.
          apply exists_ifte_P.
          apply exists_addiu_P.
          simpl.
          by repeat Reg_upd.
        apply exists_addiu_P.
        simpl fst.
        by repeat Reg_upd.
      move=> [[si hi]|] Hsi; last first.
        exists None.
        split => //.
        exact/while.exec_none.
      apply exists_maddu_seq_P.
      apply exists_mflhxu_seq_P.
      exists_sw_P l2_idx H_l2_idx z2_idx H_z2_idx.
      repeat Reg_upd.
      apply exists_addiu_seq_P.
      repeat Reg_upd.
      apply exists_addiu_P.
      repeat Reg_upd.
      simpl fst.
      repeat Reg_upd.
      rewrite sext_Z2u // u2Z_add_Z2u //.
      move: (Hsi _ refl_equal).
      rewrite Z_S /= => H.
      omega.
      move: (Hsi _ refl_equal).
      rewrite Z_S => H.
      move: (min_u2Z ([a0]_si)%mips_expr) (min_u2Z ([a4]_si)%mips_expr) => ? ?.
      move: (max_u2Z ([a0]_si)%mips_expr) (max_u2Z ([a4]_si)%mips_expr) => ? ?.
      simpl fst in H.
      omega.
      move=> [[si hi]|] Hsi; last first.
        exists None; split => //.
        exact/while.exec_none.
      apply IH.
      by move: (Hsi _ Logic.eq_refl).
case=> si Hsi.
exists si; tauto.
Qed.

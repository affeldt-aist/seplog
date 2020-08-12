(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import multi_double_u_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma multi_double_u_termination s h a0 a1 a2 a3 rx rk :
  uniq(rk, rx, a0, a1, a2, a3, r0) ->
  {x0 | Some (s, h) -- multi_double_u rk rx a0 a1 a2 a3 --->x0}%mips_cmd.
Proof.
move=> Hregs.
have [sf [exec_mips _]] : {sf | Some (s, h) -- multi_double_u rk rx a0 a1 a2 a3 ---> sf /\
  (forall s, sf = Some s -> True) }%mips_cmd.
  rewrite /multi_double_u.
  apply exists_addiu_seq_P.
  rewrite sext_Z2u // addi0.
  apply exists_addiu_seq_P.
  rewrite sext_Z2u // addi0.
  repeat Reg_upd.
  move Hs0 : (store.upd _ _ _) => s0.
  have [na0 Ha0] : { na0 | u2Z ([ rk ]_s0) - u2Z ([ a0 ]_s0) = Z_of_nat na0 }.
    apply Z_of_nat_complete_inf.
    rewrite -Hs0.
    repeat Reg_upd.
    rewrite Z2uK // subZ0; exact: min_u2Z.
  clear Hs0.
  move: na0 s0 s h Hregs Ha0.
  elim.
  - move=> s0 s h Hregs Ha0.
    exists (Some (s0, h)); split; last by [].
    apply while.exec_while_false.
    + rewrite /= in Ha0 *.
      apply/negPn/eqP; lia.
    + move=> na0 IH s0 st h Hset Ha0.
      apply exists_while_P.
      * rewrite /=; rewrite Z_S in Ha0.
        apply/eqP; lia.
      * apply exists_seq_P with (fun s => forall s', s = Some s' ->
        u2Z ([ rk ]_(fst s')) - u2Z ([ a0 ]_(fst s')) = Z_of_nat na0).
        - exists_lwxs l_a0 H_l_a0 z_a0 H_z_a0.
          apply exists_srl_seq_P.
          repeat Reg_upd.
          apply exists_sll_seq_P.
          repeat Reg_upd.
          apply exists_or_seq_P.
          repeat Reg_upd.
          rewrite store.upd_upd_eq.
          apply exists_addiu_seq_P.
          repeat Reg_upd.
          apply exists_sll_seq_P.
          repeat Reg_upd.
          apply exists_addu_seq_P.
          repeat Reg_upd.
          rewrite store.upd_upd_eq.
          exists_sw_P l_idx H_l_idx z_idx H_z_idx.
          repeat Reg_upd.
          apply exists_addiu_P.
          rewrite /=.
          repeat Reg_upd.
          rewrite Z_S in Ha0.
          rewrite sext_Z2u // u2Z_add_Z2u //.
          lia.
          move: (min_u2Z ([a0]_s0)) (min_u2Z ([rk]_s0)) (max_u2Z ([rk]_s0)) => ? ? ?.
          lia.
        - move=> si Hsi.
          destruct si as [[sti hi] |].
          + apply IH => //.
            by move: {Hsi}(Hsi _ (refl_equal _)).
          + exists None; split; by [ apply while.exec_none | ].
by exists sf.
Qed.

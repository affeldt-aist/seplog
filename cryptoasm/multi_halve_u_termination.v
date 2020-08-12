(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int uniq_tac.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import multi_halve_u_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma multi_halve_u_termination st h a0 a1 a2 a3 rx rk :
  uniq(rk, rx, a0, a1, a2, a3, r0) ->
  {x0 | Some (st, h) -- multi_halve_u rk rx a0 a1 a2 a3 --->x0}.
Proof.
move=> Hset.
have Htmp : {x0 | Some (st, h) -- multi_halve_u rk rx a0 a1 a2 a3 ---> x0 /\ (forall s, x0 = Some s -> True)}%mips_cmd.
  rewrite /multi_halve_u.
  apply exists_addiu_seq_P.
  rewrite sext_Z2u // addi0.
  apply exists_addiu_seq_P.
  rewrite sext_Z2u // addi0.
  repeat Reg_upd.
  move Hs0 : (store.upd _ _ _) => s0.
  have [na0 Ha0] : { na0 | u2Z ([a0]_s0)%mips_expr = Z_of_nat na0 }.
    apply Z_of_nat_complete_inf; exact/min_u2Z.
  clear Hs0.
  elim: na0 s0 st h Hset Ha0.
  - move=> s0 st h Hset Ha0.
    exists (Some (s0, h)); split; last by [].
    apply while.exec_while_false.
    + rewrite /= in Ha0 *.
      rewrite store.get_r0 Z2uK //.
      exact/negPn/eqP.
    + move=> na0 IH s0 st h Hset Ha0.
      apply exists_while_P.
      * rewrite /= store.get_r0 Z2uK // Ha0 Z_S.
        apply/eqP; lia.
      * apply exists_seq_P with (fun s => forall s', s = Some s' ->
        u2Z ([ a0 ]_(fst s')) = Z_of_nat na0)%mips_expr.
        - apply exists_addiu_seq_P.
          exists_lwxs l_a0 H_l_a0 z_a0 H_z_a0.
          apply exists_andi_seq_P.
          repeat Reg_upd.
          apply exists_srl_seq_P.
          repeat Reg_upd.
          apply exists_or_seq_P.
          repeat Reg_upd.
          apply exists_addiu_seq_P.
          repeat Reg_upd.
          apply exists_sll_seq_P.
          repeat Reg_upd.
          apply exists_sll_seq_P.
          repeat Reg_upd.
          apply exists_addu_seq_P.
          repeat Reg_upd.
          exists_sw1 l_idx H_l_idx z_idx H_z_idx.
          rewrite /=.
          repeat Reg_upd.
          rewrite sext_Z2s // u2Z_add_Z2s // Ha0; omegaz (*Z_S; lia*).
        - move=> si Hsi.
          destruct si as [[sti hi]|].
          + apply IH => //.
            by move: {Hsi}(Hsi _ (refl_equal _)).
          + exists None.
            split => //.
            exact/while.exec_none.
case: Htmp => x0 [Htmp _]; by exists x0.
Qed.

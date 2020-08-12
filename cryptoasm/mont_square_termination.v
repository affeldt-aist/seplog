(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import mips_bipl.expr_m.
Require Import mont_mul_prg mont_mul_termination.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma termination_mont_square s h k alpha x z m one ext int_ X_ B2K_ Y_ M_ quot C_ t s_ :
  uniq(k, alpha, x, z, m, one, ext, int_, X_, B2K_, Y_, M_, quot, C_, t, s_, r0) ->
    { si | Some (s, h) -- montgomery k alpha x x z m one ext int_ X_ B2K_ Y_ M_ quot C_ t s_ ---> si }.
Proof.
move=> Hset.
rewrite /montgomery.
apply exists_addiu_seq.
rewrite store.get_r0 add0i sext_Z2u //.
apply exists_addiu_seq.
repeat Reg_upd.
rewrite sext_Z2u // addi0.
apply exists_addiu_seq.
repeat Reg_upd.
rewrite sext_Z2u // addi0.
set s0 := store.upd _ _ _.
have [kext Hkext] : { kext | u2Z [k]_s0 - u2Z [ext]_s0 = Z_of_nat kext }.
  have [zext Hkext] : { zext | u2Z [k]_s0 - u2Z [ext]_s0 = zext }.
    eapply exist; reflexivity.
  have : 0 <= zext.
    rewrite -Hkext {2}/s0.
    repeat Reg_upd.
    rewrite /zero32 Z2uK // subZ0; exact: min_u2Z.
  case/Z_of_nat_complete_inf => next Hzext.
  exists next; by rewrite -Hzext.
move: kext s0 Hkext h.
elim.
- move=> s0 Hkext h.
  eapply exist.
  apply while.exec_while_false.
  rewrite /= in Hkext *; apply/negPn/eqP; lia.
- move=> kext IH s0 Hkext h.
  apply exists_while.
  + rewrite /=; apply/negP/negPn/eqP; omegaz. (* rewrite Z_S in Hkext; lia. *)
  + apply exists_seq_P2 with (fun st => u2Z [k]_(fst st) - u2Z [ext]_(fst st) = Z_of_nat kext).
    * exists_lwxs l_x H_l_x z_x Hz_x.
      exists_lw l_y H_l_y z_y Hz_y.
      exists_lw l_z H_l_z z_z Hz_z.
      apply exists_multu_seq_P.
      exists_lw l_m_ H_l_m z_m_ Hz_m_.
      apply exists_maddu_seq_P.
      repeat Reg_upd.
      apply exists_mflo_seq_P.
      repeat Reg_upd.
      apply exists_mfhi_seq_P.
      repeat Reg_upd.
      apply exists_multu_seq_P.
      repeat Reg_upd.
      apply exists_addiu_seq_P.
      repeat Reg_upd.
      apply exists_mflo_seq_P.
      repeat Reg_upd.
      apply exists_mthi_seq_P.
      repeat Reg_upd.
      apply exists_mtlo_seq_P.
      repeat Reg_upd.
      apply exists_maddu_seq_P.
      repeat Reg_upd.
      apply exists_mflhxu_seq_P.
      repeat Reg_upd.
      apply exists_addiu_seq_P.
      repeat Reg_upd.
      match goal with
        | |- { s' | (Some (?s0, _) -- _ ---> _) /\ _ } =>
          apply exists_seq_P with (fun x0 => forall st, x0 = Some st ->
            u2Z [k]_(fst st) - u2Z [ext]_(fst st) = Z_of_nat kext.+1)
      end.
      - have : uniq(k, x, z, m, one, ext, int_, X_, B2K_, Y_, M_, quot, t, r0) by Uniq_uniq r0.
        set _s := store.upd _ _ _.
        move/(termination_montgomery_inner_loop _s h kext.+1).
        have X : 0 < u2Z [int_ ]_ _s.
          rewrite /_s.
          repeat Reg_upd.
          by rewrite add0i (@u2Z_sext 16) // Z2uK.
        move/(_ X) => {X}.
        have X : u2Z [int_ ]_ _s <= u2Z [k ]_ _s.
          rewrite /_s.
          repeat Reg_upd.
          rewrite Z_S in Hkext.
          rewrite add0i (@u2Z_sext 16) // Z2uK //.
          move: (min_u2Z [ext ]_ s0) => ?; lia.
        move/(_ X) => {X}.
        assert ( X : u2Z [k ]_ _s - u2Z [ext ]_ _s = Z_of_nat kext.+1).
          rewrite /_s.
          repeat Reg_upd.
          assumption.
        case/(_ X) => {X} si [Hsi1 Hsi2].
        exists si; split; first by [].
        move=> st Hst.
        destruct si as [[si hi]|]; last by [].
        case: Hst => ?; subst st.
        by move: (Hsi2 _ (refl_equal _)) => <-.
      - move=> [[si hi] | ] Hsi.
        + apply exists_maddu_seq_P.
          repeat Reg_upd.
          apply exists_mflhxu_seq_P.
          repeat Reg_upd.
          apply exists_addiu_seq_P.
          repeat Reg_upd.
          exists_sw_P l_t H_l_t z_t H_z_t.
          apply exists_mflhxu_P.
          simpl fst.
          repeat Reg_upd.
          move: {Hsi}(Hsi _ Logic.eq_refl) => //.
          rewrite Z_S.
          simpl fst.
          repeat Reg_upd.
          intuition.
          rewrite u2Z_add sext_Z2u // Z2uK //.
          lia.
          move: (max_u2Z ([k]_si)) => ?; lia.
        + exists None; split; by [apply while.exec_none | ].
    * move=> [ si hi ] Hsi.
      exact: IH.
Qed.

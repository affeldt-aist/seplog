(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext seq_ext machine_int uniq_tac.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Require Import mont_mul_strict_prg mont_square_termination multi_lt_termination.
Require Import multi_sub_u_u_termination multi_zero_u_termination.
Import expr_m.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma mont_square_strict_termination s h k alpha x z m one ext int_ X_ B2K_ Y_ M_ quot C_ t s_ :
  uniq(k, alpha, x, z, m, one, ext, int_, X_, B2K_, Y_, M_, quot, C_, t, s_, r0) ->
  {si | Some (s, h) --
    mont_mul_strict k alpha x x z m one ext int_ X_ B2K_ Y_ M_ quot C_ t s_ ---> si }.
Proof.
move=> Hset; rewrite /mont_mul_strict.
apply exists_seq_P2 with (fun si => True).
- case/(termination_mont_square s h) : (Hset) => si Hsi; by exists si.
- move=> [si hi] Psi.
  + apply exists_ifte.
    * apply exists_seq_P2 with (fun si => True).
      - have : uniq(k, z, m, X_, B2K_, int_, ext, M_, Y_, r0) by Uniq_uniq r0.
        case/(multi_lt_termination si hi) => sj Hsj.
        by exists sj.
      - move=> [sj  hj] Psj.
        + apply exists_ifte.
          * have : uniq(k, m, z, ext, int_, quot, C_, M_, B2K_, r0) by Uniq_uniq r0.
            move/multi_sub_u_u_termination. case/(_ sj hj z) => sk Hk; by exists sk.
          * apply exists_nop; by move: {Psj}(Psj _ (refl_equal _)).
    * apply exists_addiu_seq.
      exists_sw_new l Hl z0 Hz0.
      repeat Reg_upd.
      apply exists_addiu_seq.
      repeat Reg_upd.
      set s0 := store.upd _ _ _.
      set h0 := heap.upd _ _ _.
      have : uniq(ext, m, z, Y_, int_, quot, C_, M_, B2K_, r0) by Uniq_uniq r0.
      move/multi_sub_u_u_termination. case/(_ s0 h0 z) => sk Hk.
      eexists; by apply Hk.
Qed.

Lemma mont_square_strict_init_termination
  s h k alpha x  z m one ext int_ X_ B2K_ Y_ M_ quot C_ t s_ :
  uniq(k, alpha, x, z, m, one, ext, int_, X_, B2K_, Y_, M_, quot, C_, t, s_, r0) ->
  { si | Some (s, h) --
    mont_mul_strict_init k alpha x x z m one ext int_ X_ B2K_ Y_ M_ quot C_ t s_ ---> si }.
Proof.
move=> Hset; rewrite /mont_mul_strict_init.
apply exists_seq_P2 with (fun si => True).
- have : uniq(k, z, ext, M_, r0) by Uniq_uniq r0.
  case/(multi_zero_u_termination s h) => si Hsi.
  exists si; split; first by tauto.
  done.
- move=> [si hi] Psi.
  + apply exists_seq_P2 with (fun sj => True).
    * by apply exists_mflhxu_seq_P, exists_mthi_seq_P, exists_mtlo_P.
    * move=> [sj hj] Psj.
    - have : uniq(k, alpha, x, z, m, one, ext, int_, X_, B2K_, Y_, M_, quot, C_, t, s_, r0) by Uniq_uniq r0.
      case/(mont_square_strict_termination sj hj) => x0 Hx0; by exists x0.
Qed.

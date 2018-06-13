(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Require Import multi_sub_u_u_prg.
Import expr_m.

Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope machine_int_scope.
Local Open Scope uniq_scope.

(* NB: z2 can be whatever *)
Lemma multi_sub_u_u_termination s h z2 k m z ext int_ quot C_ M_ B2K_ :
  uniq(k, m, z, ext, int_, quot, C_, M_, B2K_, r0) ->
  { si | Some (s, h) -- multi_sub_u_u k z m z2 ext int_ quot C_ M_ B2K_ ---> si }.
Proof.
move=> Hset; rewrite /multi_sub_u_u.
apply exists_addiu_seq.
repeat Reg_upd.
rewrite add0i.
apply exists_addiu_seq.
repeat Reg_upd.
rewrite sext_Z2u // addi0.
apply exists_addiu_seq.
repeat Reg_upd.
rewrite sext_Z2u // addi0.
set s0 := store.upd _ _ _.
have [kint_ Hkint_] : { kint_ | u2Z [k]_s0 - u2Z [int_]_s0 = Z_of_nat kint_}.
  have [kint_ Hkint_] : { kint_ | u2Z [k]_s0 - u2Z [int_]_s0 = kint_} by eapply exist; reflexivity.
  have : 0 <= kint_. rewrite -Hkint_ /s0. repeat Reg_upd. rewrite Z2uK // subZ0; exact: min_u2Z.
  case/Z_of_nat_complete_inf => kint_' H.
  exists kint_'; by rewrite -H.
move: kint_ s0 Hkint_ h.
elim.
- move=> s0 Hkint_ h.
  eapply exist.
  apply while.exec_while_false.
  rewrite /= in Hkint_ *.
  apply/negPn/eqP; omega.
- move=> kint_ IH s0 Hkint_ h.
  apply exists_while.
  + rewrite /=; apply/eqP; omegaz. (*rewrite Z_S in Hkint_; omega.*)
  + apply exists_seq_P2 with (fun st => u2Z [k]_(fst st) - u2Z [int_]_(fst st) = Z_of_nat kint_).
    * exists_lwxs l_m_ H_l_m_ z_m_ H_z_m_.
      apply exists_addu_seq_P.
      repeat Reg_upd.
      eapply exists_sltu_seq_P.
      reflexivity.
      repeat Reg_upd.
      move Hss : (store.upd _ _ _) => ss.
      exists_lwxs l_z H_l_z z_z H_z_z.
      apply exists_seq_P with (fun s' => forall st, s' = Some st ->
        u2Z [k]_(fst st) - u2Z [int_]_(fst st) = Z_of_nat (S kint_)).
      - apply exists_ifte_P.
        + apply exists_addiu_seq_P.
          repeat Reg_upd.
          rewrite add0i sext_Z2u //.
          apply exists_multu_seq_P.
          repeat Reg_upd.
          apply exists_msubu_seq_P.
          repeat Reg_upd.
          eapply exists_sltu_seq_P.
          repeat Reg_upd.
          reflexivity.
          apply exists_mflhxu_P.
          rewrite Z_S /= in Hkint_ *.
          rewrite -Hss.
          by repeat Reg_upd.
        + apply exists_nop_P.
          rewrite Z_S /= in Hkint_ *.
          rewrite -Hss.
          by repeat Reg_upd.
    - move=> [[ si hi] | ] Hsi.
      rewrite Z_S in Hsi *.
      move: {Hsi}(Hsi _ refl_equal) => H1.
      rewrite /= in H1.
      exists_sw_P l_t H_l_t z_t H_z_t.
      apply exists_addiu_seq_P.
      repeat Reg_upd.
      apply exists_addiu_P.
      rewrite /=.
      repeat Reg_upd.
      rewrite sext_Z2u // u2Z_add_Z2u //.
      rewrite /= in H1; omega.
      move: (max_u2Z ([k]_si)) => ?; omega.
    * exists None; split; by [apply while.exec_none | ].
  + move=> [ si hi ] Hsi; exact: IH.
Qed.

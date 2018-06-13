(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
Require Import ssrZ ZArith_ext seq_ext.
Require Import machine_int uniq_tac (*NB: needed by Regs_upd*).
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import multi_lt_prg.

Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope machine_int_scope.

Lemma multi_lt_termination s h k z m X_ B2K_ int_ ext M_ Y_ :
  uniq (k :: z :: m :: X_ :: B2K_ :: int_ :: ext :: M_ :: Y_ :: r0 :: nil) ->
  { si | Some (s, h) -- multi_lt k z m X_ B2K_ int_ ext M_ Y_ ---> si }.
Proof.
move=> Hset.
rewrite /multi_lt.
apply exists_addiu_seq.
rewrite sext_0 addi0.
apply exists_addiu_seq.
rewrite store.get_r0 add0i sext_Z2u // -/one32.
apply exists_ifte.
(* taken branch *)
apply exists_addiu_seq.
rewrite sext_0 addi0.
exact/exists_addiu.
(* fall-through branch *)
set s0 := store.upd _ _ _.
have Hs0 : [B2K_]_s0 <> zero32  .
  rewrite /s0.
  repeat Reg_upd.
  exact/Z2u_dis.
have [x Hx] : { x | u2Z ([X_]_s0 `+ sext 16 mone16) = Z_of_nat x}.
  apply Z_of_nat_complete_inf; exact/min_u2Z.
elim: x s0 Hx Hs0 h => [s0 Hx Hs0 h | x IH s0 Hx Hs0 h].
- apply exists_while.
  + rewrite /= store.get_r0.
    apply/negP.
    move/eqP.
    contradict Hs0.
    exact/u2Z_inj.
  + apply exists_seq_P2 with (fun st => [B2K_]_(fst st) = zero32).
    * apply exists_addiu_seq_P.
      exists_lwxs l_z H_l_z z_z H_z_z.
      exists_lwxs l_m H_l_m z_m_ H_m_z_.
      eapply exists_sltu_seq_P; first by reflexivity.
      repeat Reg_upd.
      exists_movn Hint_.
      - apply exists_movn_false_seq_P => //.
        eapply exists_sltu_seq_P; first by reflexivity.
        repeat Reg_upd.
        exists_movn Hext.
        + apply exists_movn_false_seq_P => //.
          * apply exists_movz_true_P.
            - repeat Reg_upd.
              apply u2Z_inj; by rewrite Hx Z2uK.
            - rewrite /=; by repeat Reg_upd.
          * apply exists_movn_true_seq_P => //.
            apply exists_movz_true_P.
            - repeat Reg_upd.
              apply u2Z_inj; by rewrite Hx Z2uK.
              rewrite /=; by repeat Reg_upd.
      - apply exists_movn_true_seq_P => //.
        eapply exists_sltu_seq_P; first by reflexivity.
        repeat Reg_upd.
        exists_movn Hext.
        + apply exists_movn_false_seq_P => //.
          apply exists_movz_true_P.
          * repeat Reg_upd.
            apply u2Z_inj; by rewrite Hx Z2uK.
          * rewrite /=; by repeat Reg_upd.
        + apply exists_movn_true_seq_P => //.
          apply exists_movz_true_P.
          * repeat Reg_upd.
            apply u2Z_inj; by rewrite Hx Z2uK.
          * rewrite /=; by repeat Reg_upd.
    * move=> [[si mi] hi] H.
        apply exists_while_false => //.
        rewrite /= in H *.
        by rewrite H negbK.
- apply exists_while.
  + rewrite /= store.get_r0.
    apply/eqP.
    contradict Hs0.
    exact/u2Z_inj.
  + apply exists_seq_P2 with (fun st => u2Z ([X_]_(fst st) `+ sext 16 mone16) = Z_of_nat x).
    * apply exists_addiu_seq_P.
      exists_lwxs l_z H_l_z z_z H_z_z.
      exists_lwxs l_m_ H_l_m_ z_m_ H_z_m_.
      eapply exists_sltu_seq_P; first by reflexivity.
      repeat Reg_upd.
      exists_movn Hint_.
      - apply exists_movn_false_seq_P => //.
        eapply exists_sltu_seq_P; first by reflexivity.
        repeat Reg_upd.
        exists_movn Hext.
        + apply exists_movn_false_seq_P => //.
          exists_movz1 HX_.
          * apply exists_movz_true_P.
            - move: HX_; rewrite /=; by repeat Reg_upd.
            - move: HX_.
              rewrite /=.
              repeat Reg_upd.
              move=> HX_.
              by rewrite HX_ Z2uK // in Hx.
          * apply exists_movz_false_P.
            - move: HX_ => /=; by repeat Reg_upd.
            - move: HX_ => /=.
              repeat Reg_upd.
              move=> HX_.
              rewrite sext_Z2s // in Hx.
              rewrite sext_Z2s // u2Z_add_Z2s // Hx Z_S -addZA /= addZC //=; exact/Zle_0_nat.
        + apply exists_movn_true_seq_P => //.
          repeat Reg_upd.
          exists_movz1 HX_.
          * apply exists_movz_true_P.
            - move: HX_ => /=.
              by repeat Reg_upd.
            - rewrite /=.
              repeat Reg_upd.
              rewrite sext_Z2s // in Hx.
              rewrite sext_Z2s // u2Z_add_Z2s // Hx Z_S -addZA /= addZC //=; exact/Zle_0_nat.
          * apply exists_movz_false_P.
            - move: HX_ => /=.
              by repeat Reg_upd.
            - move: HX_ => /=.
              repeat Reg_upd.
              move=> HX_.
              rewrite sext_Z2s // in Hx.
              rewrite sext_Z2s // u2Z_add_Z2s // Hx Z_S -addZA /= addZC //=; exact/Zle_0_nat.
      - apply exists_movn_true_seq_P => //.
        eapply exists_sltu_seq_P; first by reflexivity.
          repeat Reg_upd.
          exists_movn Hext.
          + apply exists_movn_false_seq_P => //.
            exists_movz1 HX_.
            * apply exists_movz_true_P.
              - move: HX_ => /=; by repeat Reg_upd.
              - move: HX_.
                rewrite /=.
                repeat Reg_upd.
                move=> HX_.
                rewrite sext_Z2s // in Hx.
                rewrite sext_Z2s // u2Z_add_Z2s // Hx Z_S -addZA /= addZC //=; exact/Zle_0_nat.
            * apply exists_movz_false_P.
              - move: HX_ => /=.
                by repeat Reg_upd.
              - move: HX_ => /=.
                repeat Reg_upd.
                move=> HX_.
                rewrite sext_Z2s // in Hx.
                rewrite sext_Z2s // u2Z_add_Z2s // Hx Z_S -addZA /= addZC //=; exact/Zle_0_nat.
          + apply exists_movn_true_seq_P => //.
            repeat Reg_upd.
            exists_movz1 HX_.
            * apply exists_movz_true_P.
              - move: HX_ => /=.
                by repeat Reg_upd.
              - move: HX_ => /=.
                repeat Reg_upd.
                move=> HX_.
                rewrite sext_Z2s // in Hx.
                rewrite sext_Z2s // u2Z_add_Z2s // Hx Z_S -addZA /= addZC //=; exact/Zle_0_nat.
            * apply exists_movz_false_P.
              - move: HX_ => /=.
                by repeat Reg_upd.
              - move: HX_ => /=.
                repeat Reg_upd.
                move=> HX_.
                rewrite sext_Z2s // in Hx.
                rewrite sext_Z2s // u2Z_add_Z2s // Hx Z_S -addZA /= addZC //=; exact/Zle_0_nat.
    * move=> [si hi] H.
      - case: (dec_int [B2K_]_si zero32) => HB2K_.
        + apply exists_while_false.
          by rewrite /= HB2K_ store.get_r0 negbK.
        + exact: IH.
Qed.

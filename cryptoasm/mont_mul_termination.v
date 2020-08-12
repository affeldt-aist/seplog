(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext ssrnat_ext seq_ext machine_int uniq_tac.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Require Import mont_mul_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Import expr_m.

Lemma termination_montgomery_inner_loop s h kext k y z m one ext int_ X_ B2K_ Y_ M_ quot t :
  uniq(k, y, z, m, one, ext, int_, X_, B2K_, Y_, M_, quot, t, r0) ->
    0 < u2Z ([int_]_s) ->
    u2Z [int_]_s <= u2Z [k]_s ->
    u2Z [k]_s - u2Z [ext]_s = Z_of_nat kext ->
    { si | (Some (s, h) --
        while.while (bne int_ k)
        (lwxs B2K_ int_ y;
         lwxs M_ int_ z;
         maddu X_ B2K_;
         lwxs Y_ int_ m;
         maddu M_ one;
         maddu quot Y_;
         addiu int_ int_ one16; mflhxu M_; addiu t t four16; sw M_ mfour16 t)
        ---> si) /\
      forall st, si = Some st ->
          u2Z [k]_(fst st) - u2Z [ext]_(fst st) = Z_of_nat kext }.
Proof.
move=> Hset Hint_ Hkint_ Hkext.
have {Hkint_}[kint_ Hkint_' ] : { kint_ | u2Z [k]_s - u2Z [int_]_s = Z_of_nat kint_ }.
  have [zkint_ Hkint_' ] : { zkint_ | u2Z [k]_s - u2Z [int_]_s = zkint_ } by eapply exist; reflexivity.
  have : 0 <= zkint_ by rewrite -Hkint_'; lia.
  case/Z_of_nat_complete_inf => kint_ H.
  exists kint_; by rewrite -H.
move: kint_ s Hint_ Hkint_' Hkext h.
elim.
- move=> s Hint_ Hkint_' HKext h.
  eapply exist; split.
  + apply while.exec_while_false.
    rewrite /= in Hkint_' *.
    apply/negPn/eqP; lia.
  + move=> st; by case => <- /=.
- move=> kint_ IH s Hint_ Hkint_' HKext h.
  apply exists_while_P.
  + rewrite /=; apply/eqP; rewrite Z_S in Hkint_'; lia.
  + apply exists_seq_P with (fun x0 => forall st, x0 = Some st ->
      0 < u2Z [int_]_(fst st) /\
      u2Z [int_]_(fst st) <= u2Z [k]_(fst st) /\
      u2Z [int_]_(fst st) = u2Z [int_]_s + 1 /\
      u2Z [k]_(fst st) - u2Z [ext]_(fst st) = Z_of_nat kext /\
      [k]_(fst st) = [k]_s ).
    * exists_lwxs l_y Hl_y z_y Hz_y.
      exists_lwxs l_z Hl_z z_z Hz_z.
      apply exists_maddu_seq_P.
      repeat Reg_upd.
      exists_lwxs l_m_ Hl_m_ z_m_ Hz_m_.
      repeat Reg_upd.
      rewrite !store.maddu_upd.
      apply exists_maddu_seq_P.
      repeat Reg_upd.
      apply exists_maddu_seq_P.
      repeat Reg_upd.
      apply exists_addiu_seq_P.
      repeat Reg_upd.
      apply exists_mflhxu_seq_P.
      repeat Reg_upd.
      apply exists_addiu_seq_P.
      repeat Reg_upd.
      exists_sw1 l_t H_l_t z_t H_z_t.
      repeat Reg_upd.
      split.
        rewrite /=.
        repeat Reg_upd.
        rewrite sext_Z2u // u2Z_add_Z2u //.
        lia.
        rewrite Z_S in Hkint_'.
        move: (max_u2Z [k ]_ s) => ?; lia.
      split.
        rewrite /=.
        repeat Reg_upd.
        rewrite sext_Z2u // u2Z_add_Z2u //.
        rewrite Z_S in Hkint_'; lia.
        rewrite Z_S in Hkint_'. move: (max_u2Z [k ]_ s) => ?; lia.
      split.
        rewrite /=.
        repeat Reg_upd.
        rewrite sext_Z2u // u2Z_add_Z2u //.
        rewrite Z_S in Hkint_'. move: (max_u2Z [k ]_ s) => ?; lia.
      split.
        rewrite /=.
        repeat Reg_upd.
        assumption.
      rewrite /=.
      repeat Reg_upd.
      reflexivity.
    * move=> [ [ si hi ] | ] Hsi.
      - move : {Hsi}(Hsi _ (refl_equal _)).
        simpl fst.
        move=> [H1 [H2 [H3 [H4 H5]]]].
        have : {s' : option (store.t * heap.t) | Some (si, hi) --
          while.while (bne int_ k)
          (lwxs B2K_ int_ y;
            lwxs M_ int_ z;
            maddu X_ B2K_;
            lwxs Y_ int_ m;
            maddu M_ one;
            maddu quot Y_;
            addiu int_ int_ one16; mflhxu M_; addiu t t four16; sw M_ mfour16 t) ---> s' /\
          (forall st : store.t * heap.t,
            s' = Some st ->
            u2Z [k ]_ (fst st) - u2Z [ext ]_ (fst st) = Z_of_nat kext )}.
          move: {IH}(IH si H1).
          have X : u2Z [k ]_ si - u2Z [int_ ]_ si = Z_of_nat kint_.
            rewrite H3 H5; omegaz.
(*            rewrite Z_S in Hkint_'.
            rewrite H3 H5; lia.*)
          move/(_ X) => {X}.
          move/(_ H4 hi).
          case=> sj [Hsj1 Hsj2].
          exists sj; split; first by [].
          move=> st Hst.
          rewrite /=; by move: (Hsj2 _ Hst).
        case=> s' [Hs'1 Hs'2].
        exists s'; split; first by [].
        move=> st Hst.
        rewrite /=; by move: (Hs'2 _ Hst).
      - exists None; split; by [apply while.exec_none | ].
Qed.

Lemma termination_montgomery s h k alpha x y z m one ext int_ X_ B2K_ Y_ M_ quot C_ t s_ :
  uniq (k :: alpha :: x :: y :: z :: m :: one :: ext :: int_ :: X_ :: B2K_ :: Y_ :: M_ ::
  quot :: C_ :: t :: s_ :: r0 :: nil) ->
    { si | Some (s, h) -- montgomery k alpha x y z m one ext int_ X_ B2K_ Y_ M_ quot C_ t s_ ---> si }.
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
  have [zext Hkext] : { zext | u2Z [k]_s0 - u2Z [ext]_s0 = zext} by eapply exist; reflexivity.
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
  + rewrite /=; apply/eqP; rewrite Z_S in Hkext; lia.
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
          apply exists_seq_P with (fun x0 => forall st : state, x0 = Some st ->
            u2Z [k]_(fst st) - u2Z [ext]_(fst st) = Z_of_nat (S kext))
      end.
      - have : uniq (k :: y :: z :: m :: one :: ext :: int_ :: X_ :: B2K_ :: Y_ :: M_ :: quot :: t ::
          r0 :: nil) by Uniq_uniq r0.
        set _s := store.upd _ _ _.
        move/(termination_montgomery_inner_loop _s h (S kext)).
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
        assert (X : u2Z [k ]_ _s - u2Z [ext ]_ _s = Z_of_nat (S kext)).
          rewrite /_s.
          repeat Reg_upd.
          assumption.
        case/(_ X) => {X} si [Hsi1 Hsi2].
        exists si; split; first by [].
        move=> st Hst.
        destruct si as [[si hi]|]; last by [].
        case: Hst => ?; subst st.
        by move: (Hsi2 _ (refl_equal _)) => <-.
      - move=> [ [ si hi ] | ] Hsi.
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
          move: {Hsi}(Hsi _ (refl_equal _)) => //.
          rewrite Z_S.
          simpl fst.
          repeat Reg_upd.
          intuition.
          rewrite sext_Z2u // u2Z_add // Z2uK //.
          lia.
          move: (max_u2Z [k]_si) => ?; lia.
        + exists None; split; by [apply while.exec_none |].
    * move=> [si hi] Hsi; exact/IH.
Qed.

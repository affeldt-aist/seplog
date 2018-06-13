(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int multi_int uniq_tac.
Import MachineInt.
Require Import mips_seplog mips_tactics mips_contrib mapstos mips_frame.
Require Import copy_s_u_prg multi_is_zero_u_triple copy_u_u_triple.
Require Import multi_zero_s_triple.
Import expr_m.
Import assert_m.

Local Open Scope machine_int_scope.
Local Open Scope multi_int_scope.
Local Open Scope heap_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.

Lemma copy_s_u_triple rk rx ry xtmp ytmp i j : uniq(rk, rx, ry, xtmp, ytmp, i, j, r0) ->
  forall X Y nk, size X = nk -> size Y = nk ->
    forall slen,
      forall ptr, u2Z ptr + 4 * Z_of_nat nk < \B^1 ->
      forall vy, u2Z vy + 4 * Z_of_nat nk < \B^1 ->
  {{ fun s h => [ry]_s = vy /\
    u2Z [rk]_s = Z_of_nat nk /\
    ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X) **
     var_e ry |--> Y) s h }}
  copy_s_u rk rx ry xtmp ytmp i j
  {{ fun s h => [ry]_s = vy /\
    u2Z [rk]_s = Z_of_nat nk /\
    ((var_e rx |--> (if \S_{ nk } Y == 0 then zero32 else Z2u 32 (Z_of_nat nk)) :: ptr :: nil **
       int_e ptr |--> (if \S_{ nk } Y == 0 then X else Y)) **
      var_e ry |--> Y) s h }}.
Proof.
move=> Hnodup X Y nk X_nk Y_nk slen ptr ptr_fit vy vy_fit.
rewrite /copy_s_u.

apply while.hoare_seq with (fun s h => [ry]_s = vy /\
  u2Z ([rk ]_ s) = Z_of_nat nk /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X) ** var_e ry |--> Y) s h /\
  (0 = \S_{ nk } Y -> [i]_s = one32) /\
  (0 < \S_{ nk } Y -> [i]_s = zero32)).

have : uniq(rk, ry, xtmp, ytmp, i, r0) by Uniq_uniq r0.
move/multi_is_zero_u_triple/(_ _ _ _ Y_nk vy_fit) => Htmp.
eapply (before_frame (var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X)).
  apply frame_rule_R.
    by apply Htmp.
    rewrite [modified_regs _]/=; by Inde.
  by [].
  move=> s h [ry_vy [rk_nk]].
  case => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
  rewrite assert_m.conCE.
  by exists h1, h2; repeat (split => //).
move=> s h.
case => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
case: Hh1 => rk_nk [ry_vy [Hh1 HSum]].
repeat (split; first by []).
split; last by [].
rewrite assert_m.conCE.
by exists h1, h2.

apply hoare_ifte_bang.

apply (hoare_prop_m.hoare_stren (fun s h => 0 < \S_{ nk } Y /\ [ry ]_ s = vy /\
  u2Z ([rk ]_ s) = Z_of_nat nk /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X) ** var_e ry |--> Y) s h)).

move=> s h H.
apply assert_m.con_and_bang_inv_R in H.
case: H => [[ry_vy [rk_nk [H HSum]]] Htest].
repeat (split => //).
case/leZ_eqVlt : (min_lSum nk Y) => // Sum_Y.
case: HSum.
move/(_ Sum_Y) => Hi _.
rewrite /= Hi store.get_r0 in Htest.
move/eqP : Htest.
by rewrite !Z2uK.

apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => HSum.

apply hoare_lw_back_alt'' with (fun s h =>
  [ry ]_ s = vy /\
  u2Z ([rk ]_ s) = Z_of_nat nk /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X) ** var_e ry |--> Y) s h /\
  [xtmp]_s = ptr).

move=> s h [ry_vy [rk_nk Hmem]].
exists ptr; split.
- rewrite -assert_m.mapsto2_mapstos in Hmem.
  Rotate Hmem.
  move: Hmem; apply assert_m.monotony => // h'.
  apply assert_m.mapsto_ext => //.
  by rewrite sext_Z2u.
- rewrite /update_store_lw.
  repeat Reg_upd.
  repeat (split; first by []).
  split; last by [].
  by Assert_upd.

apply while.hoare_seq with (
  !(fun s => ([xtmp ]_ s) = ptr) **
  !(fun s => ([ry ]_ s) = vy) **
  !(fun s => u2Z ([rk ]_ s) = Z_of_nat nk) **
  (var_e ry |--> Y ** var_e xtmp |--> Y) **
  var_e rx |--> slen :: ptr :: nil).

have : uniq(rk, xtmp, ry, ytmp, i, j, r0) by Uniq_uniq r0.
move/copy_u_u_triple/(_ _ _ _ Y_nk X_nk _ ptr_fit) => Htmp.
eapply (before_frame (!(fun s => [ry ]_ s = vy) ** (var_e rx |--> slen :: ptr :: nil))).
apply frame_rule_R.
  by apply Htmp.
  rewrite [modified_regs _]/=; by Inde.
done.
move=> s h [ry_vy [rk_nk [Hmem xtmp_ptr]]].
rewrite assert_m.conAE in Hmem.
case: Hmem => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
rewrite assert_m.conCE.
exists h1, h2; repeat (split => //).
apply assert_m.con_and_bang_L => //.
rewrite assert_m.conCE.
move: Hh2.
apply assert_m.monotony => // h'.
by apply assert_m.mapstos_ext.
move=> s h H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [[xtmp_ptr [rk_nk Hh1]] Hh2]]]].
apply assert_m.con_and_bang_inv_L in Hh2.
case: Hh2 => ry_vy Hh2.
apply assert_m.con_and_bang_L => //.
apply assert_m.con_and_bang_L => //.
apply assert_m.con_and_bang_L => //.
by exists h1, h2.

apply hoare_sw_back' => s h H.
rewrite -assert_m.mapsto2_mapstos in H.
do 5 rewrite assert_m.conCE !assert_m.conAE in H.
exists (int_e slen).
move: H; apply assert_m.monotony => // h'.
- apply assert_m.mapsto_ext => //.
  by rewrite /= sext_Z2u // addi0.
- apply assert_m.currying => h'' Hh''.
  rewrite !assert_m.conAE in Hh''.
  do 2 rewrite assert_m.conCE !assert_m.conAE in Hh''.
  apply assert_m.con_and_bang_inv_L in Hh''.
  case: Hh'' => ry_vy Hh''.
  apply assert_m.con_and_bang_inv_L in Hh''.
  case: Hh'' => rk_nk Hh''.
  repeat (split; first by []).
  rewrite assert_m.conCE.
  do 4 rewrite assert_m.conCE !assert_m.conAE in Hh''.
  apply assert_m.con_and_bang_inv_L in Hh''.
  case: Hh'' => xtmp_ptr Hh''.
  move: Hh''; apply assert_m.monotony => // h3.
  have -> : \S_{ nk } Y == 0 = false.
    apply/eqP => abs; rewrite abs in HSum.
    by apply ltZZ in HSum.
  rewrite assert_m.conCE.
  apply assert_m.monotony => // h4; last first.
    by apply assert_m.mapstos_ext => /=.
  rewrite -assert_m.mapsto2_mapstos.
  apply assert_m.monotony => // h5.
  apply assert_m.mapsto_ext => //=.
  by rewrite sext_Z2u // addi0.
  by rewrite -rk_nk Z2u_u2Z.

have : uniq(rx, r0) by Uniq_uniq r0.
move/(multi_zero_s_triple)/(_ X ptr slen) => Htmp.
eapply (before_frame (fun s h => ([ry ]_ s) = vy /\ u2Z ([rk ]_ s) = Z_of_nat nk /\ (var_e ry |--> Y) s h /\ \S_{ nk } Y = 0)).
apply frame_rule_R.
by apply Htmp.
done.
done.
move=> s h H.
apply assert_m.con_and_bang_inv_R in H.
case: H => [[ry_vy [rk_nk [H HSum]]] Htest].
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
exists h1, h2; repeat (split => //).
rewrite /= store.get_r0 Z2uK // in Htest.
case: HSum => _ HSum.
case/leZ_eqVlt : (min_lSum nk Y) => // Sum_Y.
apply HSum in Sum_Y.
by rewrite Sum_Y Z2uK in Htest.

move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh2 => ry_vy [rk_nk [Hh2 HSum]].
repeat (split; first by []).
rewrite HSum eqxx.
by exists h1, h2; repeat (split => //).
Qed.

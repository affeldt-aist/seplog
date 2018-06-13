(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_tactics mips_contrib mapstos mips_frame.
Require Import copy_s_s_prg pick_sign_prg copy_s_u_prg multi_zero_s_prg.
Import expr_m.
Import assert_m.
Require Import pick_sign_triple copy_s_u_triple multi_zero_s_triple.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope multi_int_scope.

(** x <- y *)

Lemma copy_s_s_triple rk rx ry xtmp ytmp i j a0 : uniq(rk, rx, ry, xtmp, ytmp, i, j, a0, r0) ->
  forall X Y nk, size X = nk -> size Y = nk ->
    forall slenx ptrx, u2Z ptrx + 4 * Z_of_nat nk < \B^1 ->
    forall sleny ptry, u2Z ptry + 4 * Z_of_nat nk < \B^1 ->
    forall vy,
      s2Z sleny = sgZ (s2Z sleny) * Z_of_nat nk ->
      sgZ (s2Z sleny) = sgZ (sgZ (s2Z sleny) * \S_{ nk } Y) ->
  {{ fun s h =>
    [ry]_s = vy /\
    u2Z [rk]_s = Z_of_nat nk /\
    ((var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> X) **
     (var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y)) s h }}
  copy_s_s rk rx ry xtmp ytmp i j a0
  {{ fun s h =>
    [ry]_s = vy /\
    u2Z [rk]_s = Z_of_nat nk /\
    ((var_e rx |--> sleny :: ptrx :: nil ** int_e ptrx |--> (if sleny == zero32 then X else Y)) **
    (var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y)) s h }}.
Proof.
move=> Hregs X Y nk lenX lenY slenx ptrx ptrx_fit sleny ptry ptry_fit vy
  sleny_encoding Y_encoding.
rewrite /copy_s_s.
apply while.hoare_seq with (fun s h =>
  [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> X) **
    var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y) s h /\
  [xtmp ]_ s = sleny /\
  sgZ (s2Z [ytmp ]_ s) = sgZ (s2Z sleny) /\
  (s2Z [ ytmp ]_ s = 0 \/ s2Z [ ytmp ]_ s = 1 \/ s2Z [ ytmp ]_s = - 1)
).
have : uniq(ry, xtmp, ytmp, r0) by Uniq_uniq r0.
move/pick_sign_triple.
move/(_ (fun s h => u2Z [rk ]_ s = Z_of_nat nk)).
move/(_ ((var_e ry \+ int_e four32 |--> ptry :: nil ** int_e ptry |--> Y) **
   (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> X)) vy sleny).
set ind := inde _ _.
have Hind : ind.
  rewrite /ind.
  by Inde.
move/(_ Hind) => {Hind ind}.
set ind := inde _ _.
have Hind : ind by rewrite /ind; Inde.
move/(_ Hind) => {Hind ind} hoare_triple.
eapply while.hoare_conseq; last by apply hoare_triple.
- move=> s h [Hry [Hxtmp [Hytmp_sgn [Hytmp [Hmem]]]]] Hrk.
  repeat (split => //).
  rewrite conCE -mapsto2_mapstos 2!conAE.
  move: Hmem; apply monotony => // h1 Hh1.
  by rewrite conAE -mapsto1_mapstos in Hh1.
- move=> s h [Hry [Hrk Hmem]].
  repeat (split => //).
  rewrite conCE -mapsto2_mapstos 2!conAE in Hmem.
  move: Hmem; apply monotony => // h1 Hh1.
  by rewrite -mapsto1_mapstos conAE.

apply while.hoare_ifte.
have : uniq(rx, r0) by Uniq_uniq r0.
move/multi_zero_s_triple.
move/(_ X ptrx slenx) => hoare_triple.
eapply (before_frame (fun s h => ([ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  (var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y) s h /\
  [xtmp ]_ s = sleny /\
  sgZ (s2Z [ytmp ]_ s) = sgZ (s2Z sleny) /\
  s2Z [ytmp ]_ s = 0))).
apply frame_rule_R.
apply hoare_triple.
rewrite [modified_regs _]/=; by Inde.
done.
move=> s h [[Hry [Hrk [Hmem [Hxtmp [Hytmp_sgn Hytmp]]]]] Htest].
move: Hmem; apply monotony => // h1 Hh1.
repeat (split => //).
rewrite /= store.get_r0 in Htest.
move/eqP in Htest.
move/u2Z_inj : Htest => ->.
by rewrite s2Z_u2Z_pos' // Z2uK.
move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh2 => Hry [Hrk [Hh2 [Hxtmp [Hytmp_sgn Hytmp]]]].
repeat (split => //).
rewrite (_ : 0 = s2Z zero32) in Hytmp; last first.
  by rewrite s2Z_u2Z_pos' Z2uK.
move/s2Z_inj in Hytmp.
rewrite Hytmp s2Z_u2Z_pos' Z2uK //= in Hytmp_sgn.
symmetry in Hytmp_sgn.
rewrite -> Zsgn_null in Hytmp_sgn.
rewrite (_ : 0 = s2Z zero32) in Hytmp_sgn; last by rewrite s2Z_u2Z_pos' Z2uK.
move/s2Z_inj in Hytmp_sgn.
rewrite Hytmp_sgn eqxx.
rewrite Hytmp_sgn in Hh2.
by exists h1, h2.

apply hoare_lw_back_alt'' with (fun s h => sleny <> zero32 /\
  [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> X) **
    var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y) s h /\
  [xtmp ]_ s = sleny /\
  [ i ]_s = ptry).

move=> s h [[Hry [Hrk [Hmem [Hxtmp [sgn_ytmp Hytmp]]]]] Htest].
exists ptry; split.
  rewrite conCE -mapsto2_mapstos 2!conAE conCE 1!conAE in Hmem.
  move: Hmem; apply monotony => // h1.
  apply mapsto_ext => //=; by rewrite sext_Z2u.
case/orP : (orbN (sleny == zero32)) => sleny_zero32.
  move/eqP in sleny_zero32; subst sleny.
  rewrite sleny_zero32 (_ : sgZ (s2Z zero32) = 0) in sgn_ytmp; last first.
    by rewrite s2Z_u2Z_pos' // Z2uK.
  rewrite -> Zsgn_null in sgn_ytmp.
  rewrite /= in Htest.
  have : u2Z [ytmp ]_ s = 0 by rewrite -sgn_ytmp s2Z_u2Z_pos // sgn_ytmp.
  move=> abs; by rewrite abs store.get_r0 Z2uK in Htest.
rewrite /update_store_lw.
split; first by apply/eqP.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.

apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => sleny_neq0.

apply while.hoare_seq with  (fun s h => [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptrx :: nil ** int_e ptrx |--> Y) **
    var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y) s h).

have : uniq(rk, rx, i, xtmp, ytmp, j, a0, r0) by Uniq_uniq r0.
move/copy_s_u_triple/(_ X Y nk lenX lenY slenx _ ptrx_fit ptry ptry_fit) => hoare_triple.
eapply (before_frame (fun s h =>
  [ry ]_ s = vy /\
  (var_e ry |--> sleny :: ptry :: nil) s h)).
apply frame_rule_R.
apply hoare_triple.
rewrite [modified_regs _]/=; by Inde.
done.
move=> s h [Hry [Hrk [Hmem [Hxtmp Hi]]]].
rewrite conCE conAE conCE in Hmem.
move: Hmem; apply monotony => // h1 Hh1.
repeat (split => //).
rewrite conCE.
move: Hh1; apply monotony => // h1'.
by apply mapstos_ext.
move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh1 => Hi [Hrk Hh1].
case: Hh2 => Hry Hh2.
repeat (split => //).
have Sum_Y_neq0 : \S_{ nk } Y == 0 = false.
  apply/eqP => abs; rewrite abs mulZ0 /= in Y_encoding.
  rewrite -> Zsgn_null in Y_encoding.
  rewrite (_ : 0 = s2Z zero32) in Y_encoding; last by rewrite s2Z_u2Z_pos' // Z2uK.
  by move/s2Z_inj : Y_encoding.
rewrite Sum_Y_neq0 in Hh1.
rewrite -(conCE (int_e ptry |--> Y)) -conAE.
exists h1, h2; repeat (split => //).
move: Hh1; apply monotony => h1'.
apply monotony => h1'' //.
by apply mapstos_ext.

apply hoare_lw_back_alt'' with (fun s h => [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptrx :: nil ** int_e ptrx |--> Y) **
    var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y) s h /\
  [xtmp]_s = sleny).

move=> s h [Hry [Hrk Hmem]].
exists sleny; split.
  rewrite conCE in Hmem.
  rewrite -mapsto2_mapstos 2!conAE in Hmem.
  move: Hmem; apply monotony => // h1.
  apply mapsto_ext => //=; by rewrite sext_Z2u // addi0.
rewrite /update_store_lw.
repeat (Reg_upd).
repeat (split => //).
by Assert_upd.

apply hoare_sw_back'.

move/eqP/negbTE in sleny_neq0.
rewrite sleny_neq0.
move=> s h [Hry [Hrk [Hmem Hxtmp]]].
exists (int_e (Z2u 32 (Z_of_nat nk))).
rewrite -mapsto2_mapstos in Hmem.
rewrite 2!conAE in Hmem.
move: Hmem; apply monotony => h1.
apply mapsto_ext => //=.
by rewrite sext_Z2u // addi0.
apply currying => h1' Hh1'.
repeat (split => //).
rewrite -mapsto2_mapstos 2!conAE.
rewrite conCE in Hh1'.
move: Hh1'; apply monotony => // h1''.
apply mapsto_ext => //=.
by rewrite sext_Z2u // addi0.
Qed.
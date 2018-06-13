(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext machine_int uniq_tac multi_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_tactics mips_frame.
Import expr_m.
Import assert_m.
Require Import multi_sub_s_s_s_prg pick_sign_triple multi_add_s_s_u_triple.
Require Import multi_sub_s_s_u_triple pick_sign_triple copy_s_s_triple.

Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope machine_int_scope.
Local Open Scope multi_int_scope.

Lemma multi_sub_s_s_s_triple rk rz rx ry a0 a1 a2 a3 a4 a5 rX rY rZ :
  uniq(rk, rz, rx, ry, a0, a1, a2, a3, a4, a5, rX, rY, rZ, r0) ->
  forall nk vx vy vz ptrx ptry ptrz, 0 < Z_of_nat nk < 2 ^^ 31 ->
    u2Z ptrx + 4 * Z_of_nat nk < \B^1 ->
    u2Z ptry + 4 * Z_of_nat nk < \B^1 ->
    u2Z ptrz + 4 * Z_of_nat nk < \B^1 ->
  forall X Y Z, size X = nk -> size Y = nk -> size Z = nk ->
    forall slenx sleny slenz,
    s2Z slenx = sgZ (s2Z slenx) * Z_of_nat nk ->
    s2Z sleny = sgZ (s2Z sleny) * Z_of_nat nk ->
    s2Z slenz = sgZ (s2Z slenz) * Z_of_nat nk ->
    sgZ (s2Z slenx) = sgZ (sgZ (s2Z slenx) * \S_{ nk } X) ->
    sgZ (s2Z sleny) = sgZ (sgZ (s2Z sleny) * \S_{ nk } Y) ->
    sgZ (s2Z slenz) = sgZ (sgZ (s2Z slenz) * \S_{ nk } Z) ->
{{ fun s h => [rx]_s = vx /\ [ry]_s = vy /\ [rz]_s = vz /\ u2Z [rk]_s = Z_of_nat nk /\
    ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> Z) **
     (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> X) **
     (var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y)) s h }}
 multi_sub_s_s_s rk rz rx ry a0 a1 a2 a3 a4 a5 rX rY rZ
 {{ fun s h => exists Z' slenz', size Z' = nk /\
   s2Z slenz' = sgZ (s2Z slenz') * Z_of_nat nk /\
   sgZ (s2Z slenz') = sgZ (sgZ (s2Z slenx) * \S_{ nk } X - sgZ (s2Z sleny) * \S_{ nk } Y) /\
   ((var_e rz |--> slenz' :: ptrz :: nil ** int_e ptrz |--> Z') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> X) **
    (var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y)) s h /\
   u2Z ([a3]_ s) <= 1 /\
   sgZ (s2Z slenz') * (\S_{ nk } Z' + u2Z ([a3]_ s) * \B^nk) =
   sgZ (s2Z slenx) * \S_{ nk } X - sgZ (s2Z sleny) * \S_{ nk } Y }}.
Proof.
move=> Hregs nk vx vy vz ptrx ptry ptrz Hnk ptrx_fit ptry_fit ptrz_fit X Y Z lenX lenY lenZ
  slenx sleny slenz Hslenx Hsleny Hslenz sgn_slenx sgn_sleny sgn_slenz.
rewrite /multi_sub_s_s_s.
apply hoare_lw_back_alt'' with (fun s h =>
  [rx ]_ s = vx /\ [ry ]_ s = vy /\ [rz ]_ s = vz /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> Z) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> X) **
    var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y) s h /\
  [rY]_s = ptry).
move=> s h [Hrx [Hry [hrz [Hrk H]]]].
exists ptry; split.
  rewrite -conAE conCE conAE -mapsto2_mapstos conAE -conCE conAE in H.
  move: H; apply monotony => // h'; apply mapsto_ext => //=; by rewrite sext_Z2u.
rewrite /update_store_lw.
repeat Reg_upd.
repeat (split=> //).
by Assert_upd.
apply while.hoare_seq with (fun s h =>
  [rx ]_ s = vx /\ [ry ]_ s = vy /\ [ rz ]_s = vz /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> Z) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> X) **
    var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y) s h /\
  [rY]_s = ptry /\
  [a0 ]_ s = sleny /\
  sgZ (s2Z [a1 ]_ s) = sgZ (s2Z sleny) /\
  (s2Z [ a1 ]_ s = 0 \/ s2Z [ a1 ]_ s = 1 \/ s2Z [ a1 ]_s = - 1)).
eapply while.hoare_conseq; last first.
  apply (pick_sign_triple
    (fun s h => [rx ]_ s = vx /\ [ rz ]_s = vz /\ [rY ]_ s = ptry /\ u2Z [rk ]_ s = Z_of_nat nk)
    ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> Z) **
      (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> X) **
      var_e ry \+ int_e four32 |--> ptry :: nil ** int_e ptry |--> Y) vy sleny).
  by Uniq_uniq r0.
  by Inde.
  by Inde.
move=> s h [Hrx [Hry [Hrz [Hrk [H HrY]]]]].
repeat (split => //).
rewrite -conAE conCE -mapsto2_mapstos in H.
assoc_comm H.
by rewrite -mapsto1_mapstos.
move=> s h [Hry [Ha0 [sgn_a1 [Ha1 [H [Hrx [Hrz [HrY Hrk]]]]]]]].
repeat (split => //).
rewrite -conAE conCE -mapsto2_mapstos.
assoc_comm H.
by rewrite mapsto1_mapstos.
apply while.hoare_ifte.

apply while.hoare_ifte.

apply while.hoare_seq with (fun s h => s2Z sleny = 0 /\
  [rx ]_ s = vx /\ [ry ]_ s = vy /\ [rz ]_ s = vz /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenx :: ptrz :: nil ** int_e ptrz |--> (if slenx == zero32 then Z else X)) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> X) **
    var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y) s h /\
  [rY ]_ s = ptry).
have : uniq(rk, rz, rx, a0, a1, a2, a3, a4, r0) by Uniq_uniq r0.
move/copy_s_s_triple.
move/(_ Z X nk lenZ lenX slenz ptrz ptrz_fit slenx ptrx ptrx_fit vx Hslenx sgn_slenx) =>
  hoare_triple.
eapply (before_frame (fun s h =>
  s2Z sleny = 0 /\
  [ry ]_ s = vy /\
  [rz ]_ s = vz /\
  (var_e ry |--> sleny :: ptry :: nil ** int_e ptry |--> Y) s h /\
  [rY ]_ s = ptry)).
apply frame_rule_R.
by apply hoare_triple.
rewrite [modified_regs _]/=; by Inde.
done.
move=> s h [[[Hrx [Hry [Hrz [Hrk [H [HrY [Ha0 [sgn_a1 Ha1']]]]]]]] _] Ha1].
rewrite -conAE in H; case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
rewrite /= store.get_r0 in Ha1.
move/eqP/u2Z_inj in Ha1.
exists h1, h2; repeat (split => //).
rewrite Ha1 s2Z_u2Z_pos' // Z2uK //= in sgn_a1.
by apply/Zsgn_null/esym.
move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh1 => Hrx [Hrk Hh1].
case: Hh2 => sleny_0 [Hry [Hrz [Hh2 HrY]]].
repeat (split => //).
rewrite -conAE.
by exists h1, h2.

apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => sleny0.

apply hoare_addiu'.
move=> s h [Hrx [Hry [Hrz [Hrk [H HrY]]]]].
rewrite /wp_addiu.
exists (if slenx == zero32 then Z else X), slenx.
split; first by case: ifP.
split; first by [].
split; first by rewrite sleny0 /= subZ0.
split; first by Assert_upd.
repeat Reg_upd.
rewrite add0i sext_Z2u // Z2uK //.
split; first by [].
rewrite mul0Z addZ0 sleny0 /= subZ0.
case: ifP => // /eqP ->.
by rewrite s2Z_u2Z_pos' // Z2uK.

have : uniq(rk, rz, rx, rY, a0, a1, a2, a3, a4, a5, rX, rZ, r0) by Uniq_uniq r0.
move/multi_sub_s_s_u_triple/(_ nk vz vx ptry Hnk ptrz ptrx ptrz_fit ptrx_fit ptry_fit Z X Y lenZ lenX lenY slenx slenz Hslenx Hslenz sgn_slenx) => hoare_triple.
eapply (before_frame (fun s h => 0 < s2Z sleny /\ [ry ]_ s = vy /\
  (var_e ry |--> sleny :: ptry :: nil) s h )).
apply frame_rule_R.
  by apply hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
  done.
move=> s h [[[Hrx [hry [Hrz [Hrk [H [hrY [Ha0 [sgn_a1 Ha1'']]]]]]]] Ha1'] Ha1].
rewrite -conAE conCE 2!conAE in H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
rewrite conCE.
exists h1, h2; repeat (split => //).
have Ha1''' : s2Z [a1]_s = 1.
  case: Ha1'' => Ha1''.
    rewrite /= in Ha1.
    exfalso.
    move/eqP in Ha1; apply Ha1.
    by rewrite store.get_r0 Z2uK // -s2Z_u2Z_pos // Ha1''.
  case: Ha1'' => // Ha1''.
  rewrite /= in Ha1'.
  exfalso.
  move/leZP : Ha1'.
  by rewrite Ha1'' => /leZP.
rewrite Ha1''' /= in sgn_a1.
by apply Zsgn_pos.
rewrite -conAE conCE.
move: Hh2; apply monotony => // h2'.
by apply mapstos_ext.
move=> Hh2'; by assoc_comm Hh2'.

move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh1 => Z' [slenz' [lenZ' [HrY [Hslenz' [sgn_slenz' [Hh1 [Ha3 HSum]]]]]]].
case: Hh2 => sleny0 [Hry Hh2].
exists Z', slenz'; repeat (split => //).
rewrite sgn_slenz'.
apply Zsgn_pos in sleny0.
by rewrite sleny0 Zmult_1_l.
rewrite -2!conAE conCE -conAE.
exists h1, h2; repeat (split => //).
assoc_comm Hh1.
move: Hh1; apply mapstos_ext => /=.
done.
apply Zsgn_pos in sleny0.
by rewrite sleny0 Zmult_1_l.

have : uniq(rk, rz, rx, rY, a0, a1, a2, a3, a4, a5, rX, rZ, r0) by Uniq_uniq r0.
move/multi_add_s_s_u_triple/(_ nk vz vx ptry Hnk ptrz ptrx
ptrz_fit ptrx_fit ptry_fit Z X Y lenZ lenX lenY _ _ Hslenx Hslenz sgn_slenx) => hoare_triple.
eapply (before_frame (fun s h => s2Z sleny < 0 /\ (var_e ry |--> sleny :: ptry :: nil) s h)).
apply frame_rule_R.
  by apply hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
done.
move=> s h [ [Hrx [Hry [Hrz [Hrk [H [HrY [Ha0 [Ha1' Ha1'']]]]]]]] Ha1 ].
rewrite /= in Ha1.
move/leZP in Ha1.
rewrite -conAE conCE -mapsto2_mapstos conAE in H.
rewrite conCE.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
exists h1, h2; repeat (split => //).
suff : s2Z [a1 ]_ s = -1.
  move=> abs; rewrite abs /= in Ha1'.
  by apply Zsgn_neg.
case: Ha1'' => // Ha1''.
  exfalso.
  by move: Ha1; rewrite Ha1'' => /leZP.
case: Ha1'' => // Ha1''.
exfalso.
by move: Ha1; rewrite Ha1'' => /leZP.
by rewrite -mapsto2_mapstos.
rewrite -conAE conCE.
assoc_comm Hh2.
move: Hh2; by apply mapstos_ext.

move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh1 => Z' [slenz' [lenZ' [HrY [H_ [sgn_slenz' [Hh1 [Ha3 HSum]]]]]]].
case: Hh2 => sleny0 Hh2.
have Htmp : sgZ (s2Z sleny) = -1 by apply Zsgn_neg.
exists Z', slenz'; repeat (split => //).
rewrite sgn_slenz' Htmp.
by rewrite Z.sub_opp_r.
rewrite -conAE conCE conAE conCE.
exists h1, h2; repeat (split => //).
assoc_comm Hh1.
move: Hh1; by apply mapstos_ext => /=.
rewrite HSum Htmp; ring.
Qed.

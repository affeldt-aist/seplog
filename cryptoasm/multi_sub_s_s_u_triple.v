(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_frame mips_contrib mips_tactics mips_mint.
Import expr_m.
Import assert_m.
Require Import multi_sub_s_s_u_prg pick_sign_triple multi_add_u_u_triple.
Require Import multi_lt_triple multi_sub_u_u_R_triple.
Require Import multi_sub_u_u_L_triple multi_negate_triple.
Require Import multi_is_zero_u_triple copy_s_u_triple multi_add_u_u_u_triple.
Require Import multi_lt_triple multi_zero_s_triple multi_sub_u_u_u_triple.
Require Import copy_s_s_triple multi_zero_s_triple.

Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope uniq_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope multi_int_scope.

Lemma multi_sub_s_s_u0_triple rk rz rx ry a0 a1 a2 a3 a4 ret X Z :
  uniq(rk, rz, rx, ry, a0, a1, a2, a3, a4, ret, X, Z, r0) ->
  forall nk vz vx vy, 0 < Z_of_nat nk < 2 ^^ 31 ->
    forall ptrz ptrx,
      u2Z ptrz + 4 * Z_of_nat nk < \B^1 ->
      u2Z ptrx + 4 * Z_of_nat nk < \B^1 ->
      u2Z vy + 4 * Z_of_nat nk < \B^1 ->
      forall VZ VX VY,
        size VZ = nk -> size VX = nk -> size VY = nk -> 0 < \S_{ nk } VY ->
        forall slenx slenz,
          s2Z slenx = sgZ (s2Z slenx) * Z_of_nat nk ->
          s2Z slenz = sgZ (s2Z slenz) * Z_of_nat nk ->
  {{ fun s h =>
    [ rz ]_ s = vz /\ [ rx ]_ s = vx /\ [ ry ]_ s = vy /\ u2Z [ rk ]_s = Z_of_nat nk /\
    ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
      (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
      var_e ry |--> VY ) s h  }}
  multi_sub_s_s_u0 rk rz rx ry a0 a1 a2 a3 a4 ret X Z
  {{ fun s h => exists VZ' slenz', size VZ' = nk /\
    [ ry ]_ s = vy /\
    s2Z slenz' = sgZ (s2Z slenz') * Z_of_nat nk /\
    sgZ (s2Z slenz') = sgZ (sgZ (s2Z slenx) * \S_{ nk } VX - \S_{ nk } VY) /\
    ((var_e rz |--> slenz' :: ptrz :: nil ** int_e ptrz |--> VZ') **
      (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
      var_e ry |--> VY
    ) s h /\
    u2Z ([a3]_ s) <= 1 /\
    sgZ (s2Z slenz') * (\S_{ nk } VZ' + u2Z ([a3]_ s) * \B^nk) =
    sgZ (s2Z slenx) * \S_{ nk } VX - \S_{ nk } VY
  }}.
Proof.
move=> Hregs nk vz vx vy nk_231 ptrz ptrx ptrz_fit ptrx_fit vy_fit VZ VX VY VZ_nk VX_nk VY_nk VY_neq0 slenx slenz Hslenx Hslenz.
rewrite /multi_sub_s_s_u0.
apply hoare_lw_back_alt'' with (fun s h => [rz ]_ s = vz /\
  [rx ]_ s = vx /\ [ry ]_ s = vy /\ u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
   (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
  var_e ry |--> VY) s h /\
  [Z]_s = ptrz).
  move=> s h [Hrz [Hrx [Hry [Hrk H]]]].
  exists ptrz; split.
  rewrite -mapsto2_mapstos in H.
  rewrite 2!conAE conCE 2!conAE in H.
  move: H; apply monotony => // h1.
  apply mapsto_ext => //=; by rewrite sext_Z2u.
rewrite /update_store_lw.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.
apply hoare_lw_back_alt'' with (fun s h => [rz ]_ s = vz /\
  [rx ]_ s = vx /\ [ry ]_ s = vy /\ u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
   (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
  var_e ry |--> VY) s h /\ [Z]_s = ptrz /\ [X]_s = ptrx).
  move=> s h [Hrz [Hrx [Hry [Hrk [H HZ]]]]].
  exists ptrx; split.
  rewrite conCE -mapsto2_mapstos 3!conAE conCE 4!conAE in H.
  move: H; apply monotony => // h1.
  apply mapsto_ext => //=; by rewrite sext_Z2u.
rewrite /update_store_lw.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.
apply while.hoare_seq with (fun s h => [rz ]_ s = vz /\
  [rx ]_ s = vx /\ [ry ]_ s = vy /\ u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
   (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
  var_e ry |--> VY) s h /\ [Z]_s = ptrz /\ [X]_s = ptrx /\
  [a0 ]_ s = slenx /\ sgZ (s2Z [a1 ]_ s) = sgZ (s2Z slenx) /\
  (s2Z [ a1 ]_ s = 0 \/ s2Z [ a1 ]_ s = 1 \/ s2Z [ a1 ]_s = - 1)).
have : uniq(rx, a0, a1, r0) by Uniq_uniq r0.
move/pick_sign_triple.
move/(_ (fun s h => [rz ]_ s = vz /\ [ry ]_ s = vy /\ u2Z [rk ]_ s = Z_of_nat nk /\
     [Z ]_ s = ptrz /\ [X ]_ s = ptrx) ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
  (var_e rx \+ int_e four32 |--> ptrx :: nil ** int_e ptrx |--> VX) **
  var_e ry |--> VY) vx slenx) => Htmp.
lapply Htmp; last by Inde.
move=> {}Htmp; lapply Htmp; last by Inde.
move=> {}Htmp.
eapply while.hoare_conseq; last exact: Htmp.
move=> {Htmp} s h.
move=> [Hrx [Hra0 [Hra1 [Hra1' [H1 H2]]]]].
case: H2 => Hrz [Hry [Hrk [HZ HX]]].
repeat (split => //).
rewrite conCE 2!conAE -mapsto2_mapstos conAE.
rewrite -mapsto1_mapstos in H1.
by assoc_comm H1.
move=> s h [Hrz [Hrx [Hry [Hrk [H [HZ HX]]]]]].
repeat (split => //).
rewrite conCE -mapsto2_mapstos in H.
rewrite -mapsto1_mapstos.
by assoc_comm H.
apply while.hoare_ifte.
apply while.hoare_ifte.
apply while.hoare_seq with (fun s h => slenx = zero32 /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> Z2u 32 (Z_of_nat nk) :: ptrz :: nil ** int_e ptrz |--> VY) **
   (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\ [Z ]_ s = ptrz /\ [X ]_ s = ptrx).
have : uniq(rk, rz, ry, a0, a1, a2, a3, r0) by Uniq_uniq r0.
move/copy_s_u_triple/(_ VZ VY _ VZ_nk VY_nk slenz ptrz ptrz_fit vy vy_fit) => hoare_triple.
eapply (before_frame (fun s h => slenx = zero32 /\ [rz ]_ s = vz /\ [rx ]_ s = vx /\
  (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx)).
apply frame_rule_R.
  exact: hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
by [].
move=> s h [[[Hrz [Hrx [Hry [Hrk [H [HZ [HX [Ha0 [Ha1 Ha1']]]]]]]]] Htest2] Htest].
rewrite conCE conAE in H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
exists h2, h1; repeat (split => //).
exact: heap.disj_sym.
rewrite heap.unionC //. exact: heap.disj_sym.
by assoc_comm Hh2.
rewrite /= store.get_r0 in Htest.
move/eqP/u2Z_inj in Htest.
move: Ha1.
rewrite Htest s2Z_u2Z_pos' // Z2uK //=.
move/esym.
rewrite Zsgn_null (_ : 0 = s2Z zero32); last by rewrite s2Z_u2Z_pos' // Z2uK.
by move/s2Z_inj.

move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh1 => Hry [Hrk Hh1].
case: Hh2 => slenz0 [Hrz [Hrx [Hh2 [HZ HX]]]].
repeat (split => //).
have : \S_{ nk } VY == 0 = false by apply/eqP => abs; rewrite abs in VY_neq0.
move=> tmp; rewrite tmp in Hh1.
rewrite conCE conAE.
exists h2, h1; repeat (split => //).
exact: heap.disj_sym.
rewrite heap.unionC //. exact: heap.disj_sym.
by assoc_comm Hh1.

apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => slenx0.

apply hoare_addiu with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> Z2u 32 (Z_of_nat nk) :: ptrz :: nil ** int_e ptrz |--> VY) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\ [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  [ a3 ]_s = zero32).

move=> s h [Hrz [Hrx [Hry [Hrk [H [HZ HX]]]]]].
rewrite /wp_addiu.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.
by rewrite sext_Z2u // addi0.

apply hoare_subu with (fun s h => [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> Z2u 32 (Z_of_nat nk) :: ptrz :: nil ** int_e ptrz |--> VY) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\ [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  [ a3 ]_s = zero32 /\ s2Z [ a0 ]_s = - Z_of_nat nk).
move=> s h [Hrz [Hrx [Hry [Hrk [H [HZ [HX Ha3]]]]]]].
rewrite /wp_subu.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.
rewrite add0i s2Z_cplt2; last by rewrite weirdE Hrk; omega.
congr (- _); rewrite s2Z_u2Z_pos' // Hrk [predn _]/=; omega.

apply hoare_sw_back'.
move=> s h [Hrz [Hrx [Hry [Hrk [H [HZ [HX [Ha3 Ha0]]]]]]]].
exists (int_e (Z2u 32 (Z_of_nat nk))).
rewrite conAE -mapsto2_mapstos conAE in H.
move: H; apply monotony => // h1.
apply mapsto_ext => //=.
by rewrite sext_Z2u // addi0.
apply currying => h2 Hh2.
exists VY, ([ a0 ]_ s).
split => //.
split => //.
split.
  suff : sgZ (s2Z [a0]_s) = -1 by move=> ->.
  apply Zsgn_neg.
  rewrite Ha0; omega.
split.
  rewrite Ha0 slenx0 s2Z_u2Z_pos' // Z2uK //= 2!Zsgn_Zopp; congr (- _).
  transitivity 1.
    apply Zsgn_pos; by case: nk_231.
  exact/esym/Zsgn_pos.
split.
  rewrite -mapsto2_mapstos.
  rewrite 3!conAE conCE 4!conAE.
  rewrite 4!conAE in Hh2.
  move: Hh2; apply monotony => // h3.
  apply monotony => // h4.
  apply monotony => // h5.
  apply monotony => // h6.
  apply monotony => // h7.
  apply mapsto_ext => //=.
  by rewrite sext_Z2u // addi0.
split; first by rewrite Ha3 Z2uK.
rewrite Ha3 Z2uK // mul0Z addZ0 Ha0 Zsgn_Zopp slenx0 /=.
rewrite s2Z_u2Z_pos' // Z2uK //= (proj2 (Zsgn_pos (Z_of_nat nk))); last by case: nk_231.
ring.

apply while.hoare_seq with (fun s h => 0 < s2Z slenx /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\
  [X ]_ s = ptrx /\
  ((\S_{ nk } VY < \S_{ nk } VX /\ [ret]_s = one32 /\ [a2]_s = zero32) \/
   (\S_{ nk } VY > \S_{ nk } VX /\ [ret]_s = zero32 /\ [a2]_s = one32) \/
   (\S_{ nk } VY = \S_{ nk } VX /\ [ret]_s = zero32 /\ [a2]_s = zero32))).

have : uniq(rk, ry, X, a0, a1, ret, a2, a3, a4, r0) by Uniq_uniq r0.
move/multi_lt_triple/(_ nk VY VX vy ptrx VY_nk VX_nk) => hoare_triple.
eapply (before_frame (fun s h => 0 < s2Z slenx /\ [rz ]_ s = vz /\ [rx ]_ s = vx /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil)) s h /\ [Z ]_ s = ptrz)).
apply frame_rule_R.
  exact: hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
by [].

move=> s h [[[Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [Ha0 [Ha1'' Ha1''']]]]]]]]] Ha1] Ha1'].
rewrite -2!conAE conCE -2!conAE conCE 2!conAE -conAE in Hmem.
case: Hmem => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
exists h1, h2; repeat (split => //).
rewrite conCE.
move: Hh1; apply monotony => // h3.
exact: mapstos_ext.
rewrite /= in Ha1 Ha1'.
move/leZP in Ha1.
apply Zsgn_pos.
rewrite -Ha1''.
apply Zsgn_pos.
have {}Ha1' : 0 <> s2Z [a1]_s.
  move/eqP in Ha1'.
  contradict Ha1'.
  by rewrite store.get_r0 Z2uK // -s2Z_u2Z_pos.
omega.
by assoc_comm Hh2.

move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh1 => [Hrk [Hry [HX [HSum Hh1]]]].
case: Hh2 => slenx0 [Hrz [Hrx [Hh2 HZ]]].
repeat (split => //).
rewrite -2!conAE conCE -2!conAE conCE 2!conAE -conAE.
exists h1, h2; repeat (split => //).
rewrite conCE.
move: Hh1; apply monotony => // h3.
exact: mapstos_ext.
by assoc_comm Hh2.

apply while.hoare_ifte.
apply while.hoare_ifte.
apply while.hoare_seq with (fun s h =>
0 < s2Z slenx /\ \S_{ nk } VY = \S_{ nk } VX /\
[rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
u2Z [rk ]_ s = Z_of_nat nk /\
((var_e rz |--> zero32 :: ptrz :: nil ** int_e ptrz |--> VZ) **
  (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
  var_e ry |--> VY) s h /\
[Z ]_ s = ptrz /\ [X ]_ s = ptrx).
have : uniq(rz, r0) by Uniq_uniq r0.
move/multi_zero_s_triple.
move/(_ VZ ptrz slenz) => hoare_triple.
eapply (before_frame (fun s h => 0 < s2Z slenx /\ \S_{ nk } VY = \S_{ nk } VX /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
  var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx)).
apply frame_rule_R.
apply hoare_triple.
rewrite [modified_regs _]/=; by Inde.
by [].

move=> s h [[[slenx0 [Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX HSum]]]]]]]] Hret'] Hret].
case: Hmem => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
exists h1, h2; repeat (split => //).
rewrite /= in Hret' Hret.
move/eqP/u2Z_inj in Hret'; rewrite store.get_r0 in Hret'.
move/eqP/u2Z_inj in Hret; rewrite store.get_r0 in Hret.
case: HSum => HSum //.
  case: HSum => _ [] HSum _; rewrite HSum in Hret'.
  by apply Z2u_dis in Hret'.
case: HSum => HSum //.
  case: HSum => _ [] _ HSum; rewrite HSum in Hret.
  by apply Z2u_dis in Hret.
tauto.
move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh2 => slenx0 [VY_VX [Hrz [Hrx [Hry [Hrk [Hh2 [HZ HX]]]]]]].
repeat (split => //).
by exists h1, h2.

apply hoare_addiu'.
move=> s h [slenx0 [VY_VX [Hrz [Hrx [Hry [Hrk [Hmem [HZ HX]]]]]]]].
rewrite /wp_addiu.
exists VZ, zero32.
repeat Reg_upd.
repeat (split => //).
by rewrite s2Z_u2Z_pos' // Z2uK.
rewrite s2Z_u2Z_pos' // Z2uK //=.
by rewrite (proj2 (Zsgn_pos _) slenx0) VY_VX mul1Z subZZ.
by Assert_upd.
by rewrite sext_Z2u // addi0 Z2uK.
rewrite sext_Z2u // addi0 Z2uK // mul0Z addZ0.
rewrite s2Z_u2Z_pos' // Z2uK //=.
by rewrite (proj2 (Zsgn_pos _) slenx0) VY_VX mul1Z subZZ.

apply while.hoare_seq with (fun s h => exists VZ' : list (int 32),
  size VZ' = nk /\
  0 < s2Z slenx /\
  \S_{ nk } VY > \S_{ nk } VX /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\
  [X ]_ s = ptrx /\
  u2Z [a3]_s <= 1 /\
  \S_{ nk } VZ' = \S_{ nk } VY - \S_{ nk } VX + u2Z [a3]_s * \B^nk).

have : uniq(rk, ry, X, Z, a0, a1, a2, a3, a4, ret, r0) by Uniq_uniq r0.
move/multi_sub_u_u_u_triple.
move/(_ nk vy ptrx ptrz ptrz_fit VY VX VZ VY_nk VX_nk VZ_nk) => hoare_triple.
eapply (before_frame (fun s h =>
  0 < s2Z slenx /\ \S_{ nk } VY > \S_{ nk } VX /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\
  ((var_e rz |--> slenz :: ptrz :: nil) ** (var_e rx |--> slenx :: ptrx :: nil)) s h)).
apply frame_rule_R.
apply hoare_triple.
rewrite [modified_regs _]/=; by Inde.
by [].

move=> s h [[[slenx0 [Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX HSum]]]]]]]] Ha2'] Ha2].
rewrite /= in Ha2' Ha2.
move/eqP/u2Z_inj in Ha2'.
rewrite store.get_r0 in Ha2'.
rewrite -(conCE (_ |--> VZ)) -conAE conCE -2!conAE conCE 2!conAE -2!conAE in Hmem.
case: Hmem => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
exists h1, h2; repeat (split => //).
rewrite (conCE (_ |--> VX)) conAE in Hh1; move: Hh1; apply monotony => // h1'.
apply monotony => // h1''.
exact: mapstos_ext.
exact: mapstos_ext.
case: HSum.
  case=> _ [] HSum _.
  rewrite Ha2' in HSum.
  by apply Z2u_dis in HSum.
case.
  tauto.
case=> _ [] _ abs; by rewrite abs store.get_r0 !Z2uK in Ha2.

move=> s h.
case=> h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
case: Hh1 => VZ' [VZ'_nk [HX [Hry [HZ [Hrk [Hh1 [ha3 HSum]]]]]]].
case: Hh2 => slenx0 [HSum' [Hrz [Hrx Hh2]]].
exists VZ'.
repeat (split => //).
rewrite -(conCE (_ |--> VZ')) -conAE conCE -2!conAE conCE 2!conAE -2!conAE.
exists h1, h2; repeat (split => //).
rewrite -conAE (conCE (_ |--> VY)) in Hh1.
move: Hh1; apply monotony => // h1'.
apply monotony => // h1''; exact: mapstos_ext.
exact: mapstos_ext.

apply pull_out_exists => VZ'.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => VZ'_nk.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => slenx0.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => VY_VX.

apply hoare_subu with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  u2Z [a3 ]_ s <= 1 /\
  \S_{ nk } VZ' = \S_{ nk } VY - \S_{ nk } VX + u2Z [a3 ]_ s * \B^nk /\
  s2Z [ a0 ]_s = - Z_of_nat nk).

move=> s h [Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [Ha3 HSum]]]]]]]].
rewrite /wp_subu.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.
rewrite add0i s2Z_cplt2.
f_equal.
rewrite -Hrk s2Z_u2Z_pos' //.
rewrite Hrk. simpl Peano.pred. omega.
rewrite weirdE => abs; rewrite -Hrk abs in nk_231; omega.

apply hoare_sw_back' => s h.
case=> Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [Ha3 [HSum Ha0]]]]]]]].
exists (int_e slenz).
rewrite -mapsto2_mapstos 2!conAE in Hmem.
move: Hmem; apply monotony => // h1.
apply mapsto_ext => //=.
by rewrite sext_Z2u // addi0.
apply currying => h1' Hh1'.
exists VZ', (Z2s 32 (- Z_of_nat nk)).
repeat (split => //).
rewrite Z2sK //.
suff : sgZ (- Z_of_nat nk) = -1 by move=> ->.
apply Zsgn_neg.
omega.
omega.
rewrite Z2sK //.
rewrite (proj2 (Zsgn_pos _) slenx0) mul1Z.
transitivity (-1).
  apply Zsgn_neg.
  omega.
symmetry.
apply Zsgn_neg; omega.
omega.
rewrite -mapsto2_mapstos 2!conAE.
rewrite conCE in Hh1'.
move: Hh1'; apply monotony => // h1''.
apply mapsto_ext => //=.
by rewrite sext_Z2u // addi0.
apply s2Z_inj; rewrite Ha0.
rewrite Z2sK //; omega.
rewrite Z2sK; last by omega.
rewrite (proj2 (Zsgn_pos _) slenx0) mul1Z HSum.
rewrite (_ : sgZ (- Z_of_nat nk) = -1); last first.
  apply Zsgn_neg; omega.
have Ha30 : u2Z [a3 ]_ s = 0.
  have {Ha3}[Ha3|Ha3] : u2Z [a3 ]_ s = 0 \/ u2Z [a3 ]_ s = 1 by move: (min_u2Z [a3]_s) => ?; omega.
  by [].
  exfalso.
  rewrite Ha3{} mul1Z in HSum.
  move: (max_lSum nk VZ').
  rewrite HSum ZbetaE => abs.
  suff : 0 <= \S_{ nk } VY - \S_{ nk } VX by move=> ?; omega.
  omega.
rewrite Ha30; ring.

apply while.hoare_seq with (fun s h => exists VZ' : list (int 32),
  size VZ' = nk /\
  0 < s2Z slenx /\
  \S_{ nk } VY < \S_{ nk } VX /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\
  [X ]_ s = ptrx /\
  u2Z [a3]_s <= 1 /\
  \S_{ nk } VZ' = \S_{ nk } VX - \S_{ nk } VY + u2Z [a3]_s * \B^nk).

have : uniq(rk, X, ry, Z, a0, a1, a2, a3, a4, ret, r0) by Uniq_uniq r0.
move/multi_sub_u_u_u_triple.
move/(_ nk ptrx vy ptrz ptrz_fit VX VY VZ VX_nk VY_nk VZ_nk) => hoare_triple.
eapply (before_frame (fun s h =>
  0 < s2Z slenx /\ \S_{ nk } VY < \S_{ nk } VX /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\
  ((var_e rz |--> slenz :: ptrz :: nil) ** (var_e rx |--> slenx :: ptrx :: nil)) s h)).
apply frame_rule_R.
apply hoare_triple.
rewrite [modified_regs _]/=; by Inde.
by [].

move=> s h [[slenx0 [Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX HSum]]]]]]]] Ha2].
rewrite /= in Ha2.
rewrite -(conCE (_ |--> VZ)) -conAE conCE -2!conAE conCE 2!conAE -2!conAE in Hmem.
case: Hmem => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
exists h1, h2; repeat (split => //).
rewrite conAE in Hh1; move: Hh1; apply monotony => // h1'.
exact: mapstos_ext.
apply monotony => // h1''; exact: mapstos_ext.
case: HSum.
  tauto.
case;
  case=> _ [] HSum _ ;
  by rewrite HSum store.get_r0 Z2uK in Ha2.

move=> s h.
case=> h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
case: Hh1 => VZ' [VZ'_nk [HX [Hry [HZ [Hrk [Hh1 [ha3 HSum]]]]]]].
case: Hh2 => slenx0 [HSum' [Hrz [Hrx Hh2]]].
exists VZ'.
repeat (split => //).
rewrite -(conCE (_ |--> VZ')) -conAE conCE -2!conAE conCE 2!conAE -2!conAE.
exists h1, h2; repeat (split => //).
rewrite -conAE in Hh1.
move: Hh1; apply monotony => // h1'.
apply monotony => // h1''; exact: mapstos_ext.
exact: mapstos_ext.

apply pull_out_exists => VZ'.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => VZ'_nk.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => slenx0.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => VY_VX.

apply hoare_sw_back' => s h.
case=> Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [Ha3 HSum]]]]]]].
exists (int_e slenz).
rewrite -mapsto2_mapstos 2!conAE in Hmem.
move: Hmem; apply monotony => // h1.
apply mapsto_ext => //=.
by rewrite sext_Z2u // addi0.
apply currying => h1' Hh1'.
exists VZ', (Z2u 32 (Z_of_nat nk)).
have H1 : s2Z (Z2u 32 (Z_of_nat nk)) = Z_of_nat nk.
  rewrite s2Z_u2Z_pos'; last first.
    rewrite Z2uK //.
    rewrite [Peano.pred _]/=; omega.
    simpl expZ in nk_231. simpl. omega.
  rewrite Z2uK //.
  simpl expZ in nk_231. simpl. omega.
have H2 : sgZ (Z_of_nat nk) = 1 by apply Zsgn_pos; omega.
have H3 : u2Z (Z2u 32 (Z_of_nat nk)) = Z_of_nat nk.
  rewrite Z2uK //.
  simpl expZ in nk_231. simpl. omega.
repeat (split => //).
rewrite s2Z_u2Z_pos' //.
rewrite Z2uK //.
suff : sgZ (Z_of_nat nk) = 1 by move=> ->; rewrite mul1Z.
apply Zsgn_pos.
omega.
simpl in nk_231; simpl; omega.
rewrite Z2uK //.
simpl Peano.pred; omega.
simpl in nk_231; simpl; omega.
rewrite H1 (proj2 (Zsgn_pos _) slenx0) mul1Z H2.
symmetry.
apply Zsgn_pos; omega.
rewrite -mapsto2_mapstos 2!conAE.
rewrite conCE in Hh1'.
move: Hh1'; apply monotony => // h1''.
apply mapsto_ext => //=.
by rewrite sext_Z2u // addi0.
apply u2Z_inj; rewrite Hrk.
by rewrite H3.
rewrite H1 H2 (proj2 (Zsgn_pos _) slenx0) mul1Z HSum.
have Ha30 : u2Z [a3 ]_ s = 0.
  have {Ha3}[Ha3|Ha3] : u2Z [a3 ]_ s = 0 \/ u2Z [a3 ]_ s = 1 by move: (min_u2Z [a3]_s) => ?; omega.
  by [].
  exfalso.
  rewrite Ha3{} mul1Z in HSum.
  move: (max_lSum nk VZ').
  rewrite HSum ZbetaE => abs.
  suff : 0 <= \S_{ nk } VY - \S_{ nk } VX by move=> ?; omega.
  omega.
rewrite Ha30; ring.

apply hoare_addiu with (fun s h =>
  s2Z slenx < 0 /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  [a3]_s = one32).

move=> s h [[Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [Ha0 [Ha1 Ha1']]]]]]]]] Ha1''].
rewrite /wp_addiu.
repeat (Reg_upd).
repeat (split => //).
rewrite /= Z.leb_antisym negbK in Ha1''.
move/ltZP in Ha1''.
case: Ha1'.
  move=> abs; by rewrite abs in Ha1''.
case=> //.
move=> abs; by rewrite abs in Ha1''.
move=> {}Ha1''; rewrite Ha1'' /= in Ha1.
symmetry in Ha1.
by apply Zsgn_neg in Ha1.
by Assert_upd.
by rewrite sext_Z2u // add0i.

apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => slenx0.

apply while.hoare_seq with (fun s h =>
  exists VZ', size VZ' = nk /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  u2Z (store.lo s) <= 1 /\
  \S_{ nk } VZ' + u2Z (store.lo s) * \B^nk = \S_{ nk } VX + \S_{ nk } VY).

have : uniq(rk, a3, X, ry, Z, a0, a1, a2, r0) by Uniq_uniq r0.
move/multi_add_u_u_u_triple.
move/(_ nk ptrx vy ptrz ptrz_fit VX VY VX_nk VY_nk) => hoare_triple.
eapply (before_frame (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\
  ((var_e rz |--> slenz :: ptrz :: nil) **
   (var_e rx |--> slenx :: ptrx :: nil)) s h)).
apply frame_rule_R.
exact: hoare_triple.
rewrite [modified_regs _]/=; by Inde.
by [].
move=> s h [Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX Ha3]]]]]]].
rewrite -(conCE (_ |--> VZ)) conAE conCE 3!conAE -1!conAE in Hmem.
case: Hmem => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
rewrite conCE.
exists h1, h2; repeat (split => //).
exists VZ; repeat (split => //).
move: Hh2; apply monotony => // h2'.
exact: mapstos_ext.
apply monotony => // h2''; exact: mapstos_ext.

move=> s h; case=> h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
case: Hh1 => VZ' [lenVZ' [XH [Hry [HZ [Hrk [Hmem [Hlo HSum]]]]]]].
case: Hh2 => Hrz [Hrx Hh2].
exists VZ'; repeat (split => //).
rewrite -(conCE (_ |--> VZ')) conAE conCE 3!conAE -1!conAE.
rewrite conCE.
exists h1, h2; repeat (split => //).
move: Hmem; apply monotony => // h1'.
exact: mapstos_ext.
apply monotony => // h1''; exact: mapstos_ext.

apply pull_out_exists => VZ'.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => lenVZ'.

apply hoare_mflo with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\
  [X ]_ s = ptrx /\
  u2Z [a3]_s <= 1 /\
  \S_{ nk } VZ' + u2Z [a3]_s * \B^nk = \S_{ nk } VX + \S_{ nk } VY).

move=> s h [Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [Hlo HSum]]]]]]]].
rewrite /wp_mflo.
repeat (Reg_upd).
repeat (split => //).
by Assert_upd.

apply hoare_subu with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\
  [X ]_ s = ptrx /\
  u2Z ([a3]_ s) <= 1 /\
  \S_{ nk } VZ' + u2Z ([a3]_s) * \B^nk = \S_{ nk } VX + \S_{ nk } VY /\
  s2Z [ a0 ]_s = - Z_of_nat nk).

move=> s h [Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [Ha3 HSum]]]]]]]].
rewrite /wp_subu.
repeat (Reg_upd).
repeat (split => //).
by Assert_upd.
rewrite add0i s2Z_cplt2.
f_equal.
rewrite s2Z_u2Z_pos' //.
rewrite Hrk [Peano.pred _]/=; omega.
rewrite weirdE. move=> abs; rewrite -Hrk abs in nk_231; by case: nk_231.

apply hoare_sw_back'.
move=> s h [Hrz [Hrx [Hry [Hrk [H [HZ [HX [Hlo [HSum Ha0]]]]]]]]].
exists (int_e slenz).
rewrite conAE -mapsto2_mapstos conAE in H.
move: H; apply monotony => // h1.
apply mapsto_ext => //=.
by rewrite sext_Z2u // addi0.
apply currying => h2 Hh2.
exists VZ', ([ a0 ]_ s).
split => //.
have Htmp : sgZ (s2Z [a0 ]_ s) = -1 by apply Zsgn_neg; omega.
have Htmp' : sgZ (s2Z slenx) = -1 by apply Zsgn_neg.
split => //.
split.
  by rewrite Htmp mulN1Z.
split.
  rewrite Htmp.
  rewrite Htmp'.
  apply/esym/Zsgn_neg.
  move: (min_lSum nk VX) => ?; omega.
split.
  rewrite -mapsto2_mapstos.
  rewrite 3!conAE conCE conAE.
  rewrite 1!conAE in Hh2.
  move: Hh2; apply monotony => // h3.
  apply monotony => // h4.
  apply monotony => // h5.
  by rewrite -conAE.
  apply mapsto_ext => //=.
  by rewrite sext_Z2u // addi0.
split => //.
rewrite HSum Htmp Htmp'; ring.
Qed.

Lemma multi_sub_s_s_u_triple rk rz rx ry a0 a1 a2 a3 a4 ret X Z :
  uniq(rk, rz, rx, ry, a0, a1, a2, a3, a4, ret, X, Z, r0) ->
  forall nk vz vx vy, 0 < Z_of_nat nk < 2 ^^ 31 ->
    forall ptrz ptrx,
      u2Z ptrz + 4 * Z_of_nat nk < \B^1 ->
      u2Z ptrx + 4 * Z_of_nat nk < \B^1 ->
      u2Z vy + 4 * Z_of_nat nk < \B^1 ->
      forall VZ VX VY,
        size VZ = nk -> size VX = nk -> size VY = nk ->
        forall slenx slenz,
          s2Z slenx = sgZ (s2Z slenx) * Z_of_nat nk ->
          s2Z slenz = sgZ (s2Z slenz) * Z_of_nat nk ->
          sgZ (s2Z slenx) = sgZ (sgZ (s2Z slenx) * \S_{ nk } VX) ->
  {{ fun s h =>
    [ rz ]_ s = vz /\ [ rx ]_ s = vx /\ [ ry ]_ s = vy /\ u2Z [ rk ]_s = Z_of_nat nk /\
    ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
      (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
      var_e ry |--> VY ) s h  }}
  multi_sub_s_s_u rk rz rx ry a0 a1 a2 a3 a4 ret X Z
  {{ fun s h => exists VZ', exists slenz', size VZ' = nk /\
    [ ry ]_ s = vy /\
    s2Z slenz' = sgZ (s2Z slenz') * Z_of_nat nk /\
    sgZ (s2Z slenz') = sgZ (sgZ (s2Z slenx) * \S_{ nk } VX - \S_{ nk } VY) /\
    ((var_e rz |--> slenz' :: ptrz :: nil ** int_e ptrz |--> VZ') **
      (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
      var_e ry |--> VY
    ) s h /\
    u2Z ([a3]_ s) <= 1 /\
    sgZ (s2Z slenz') * (\S_{ nk } VZ' + u2Z ([a3]_ s) * \B^nk) =
    sgZ (s2Z slenx) * \S_{ nk } VX - \S_{ nk } VY
  }}.
Proof.
move=> Hregs nk vz vx vy Hnk ptrz ptrx ptrz_fit ptrx_fit vy_fit VZ VX VY
  lenVZ lenVX lenVY slenx slenz Hslenx Hslenz sgn_slenx.
rewrite /multi_sub_s_s_u.
apply while.hoare_seq with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  ((0 = \S_{ nk } VY -> [a2]_s = one32) /\ (0 < \S_{ nk } VY -> [a2]_s = zero32))).
have : uniq(rk, ry, a0, a1, a2, r0) by Uniq_uniq r0.
move/multi_is_zero_u_triple/(_ nk VY vy lenVY vy_fit) => hoare_triple.
eapply (before_frame (fun s h => [rz ]_ s = vz /\ [rx ]_ s = vx /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX)) s h)).
apply frame_rule_R.
  exact: hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
by [].
move=> s h [Hrz [Hrx [Hry [Hrk H]]]].
rewrite -conAE conCE in H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
by exists h1, h2.
move=> s h H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
case: Hh1 => Hrk [Hry [Hh1 HSum]].
case: Hh2 => Hrz [Hrx Hh2].
repeat (split => //).
rewrite -conAE conCE.
by exists h1, h2.

apply while.hoare_ifte.

apply hoare_addiu with (fun s h => 0 = \S_{ nk } VY /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\ [a3]_s =zero32).

move=> s h [[Hrz [Hrx [Hry [Hrk [H [HSum1 HSum2]]]]]] Ha2].
rewrite /wp_addiu.
split.
  rewrite /= in Ha2.
  case: (Z_le_lt_eq_dec _ _ (min_lSum nk VY)) => //.
  move/HSum2 => abs; by rewrite abs Z2uK // store.get_r0 Z2uK in Ha2.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.
by rewrite sext_Z2u // addi0.

apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => Sum_VY.

have : uniq(rk, rz, rx, a0, a1, a2, ret, a4, r0) by Uniq_uniq r0.
move/copy_s_s_triple.
move/(_ VZ VX nk lenVZ lenVX slenz ptrz ptrz_fit slenx ptrx ptrx_fit vx Hslenx sgn_slenx) => hoare_triple.
eapply (before_frame (fun s h => [rz ]_ s = vz /\ [ry ]_ s = vy /\ (var_e ry |--> VY) s h /\
  [a3]_s = zero32)).
apply frame_rule_R.
  exact: hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
by [].
move=> s h [Hrz [Hrx [Hry [Hrk [H Ha3]]]]].
rewrite -conAE in H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
exists h1, h2; repeat (split => //).
move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh1 => Hrx [Hrk Hh1].
case: Hh2 => Hrz [Hry [Hh2 Ha3]].
exists (if slenx == zero32 then VZ else VX), slenx.
split; first by case: ifP.
split; first by [].
split; first by [].
split; first by rewrite -Sum_VY subZ0.
split.
  rewrite -conAE.
  exists h1, h2; repeat (split => //).
split; first by rewrite Ha3 Z2uK.
rewrite -Sum_VY subZ0.
case: ifP => [/eqP -> | _].
  by rewrite s2Z_u2Z_pos' // Z2uK.
by rewrite Ha3 Z2uK // mul0Z addZ0.

apply hoare_prop_m.hoare_stren with (fun s h => 0 < \S_{ nk } VY /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h).

move=> s h [[Hrz [Hrx [Hry [Hrk [H [HSum1 HSum2]]]]]] Ha2].
split => //.
rewrite /= in Ha2.
case: (Z_le_lt_eq_dec _ _ (min_lSum nk VY)) => //.
move/HSum1 => abs; by rewrite abs Z2uK // store.get_r0 Z2uK in Ha2.

apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => Sum_VY.

exact: multi_sub_s_s_u0_triple.
Qed.

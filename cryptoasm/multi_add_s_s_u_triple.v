(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_frame mips_contrib mips_tactics.
Require Import mips_mint.
Import expr_m.
Import assert_m.
Require Import multi_add_s_s_u_prg pick_sign_triple multi_add_u_u_triple.
Require Import multi_lt_triple multi_sub_u_u_R_triple.
Require Import multi_sub_u_u_L_triple multi_negate_triple.
Require Import multi_is_zero_u_triple copy_s_u_triple multi_add_u_u_u_triple.
Require Import multi_lt_triple multi_zero_s_triple multi_sub_u_u_u_triple.
Require Import copy_s_s_triple.

Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope uniq_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope multi_int_scope.

(* TODO: clean *)

Lemma multi_add_s_s_u0_triple rk rz rx ry a0 a1 a2 a3 a4 ret X Z :
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
      var_e ry |--> VY ) s h }}
  multi_add_s_s_u0 rk rz rx ry a0 a1 a2 a3 a4 ret X Z
  {{ fun s h => exists VZ' slenz', size VZ' = nk /\
    [ry ]_ s = vy /\
    s2Z slenz' = sgZ (s2Z slenz') * Z_of_nat nk /\
    sgZ (s2Z slenz') = sgZ (sgZ (s2Z slenx) * \S_{ nk } VX + \S_{ nk } VY) /\
    ((var_e rz |--> slenz' :: ptrz :: nil ** int_e ptrz |--> VZ') **
      (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
      var_e ry |--> VY
    ) s h /\
    u2Z ([a3]_ s) <= 1 /\
    sgZ (s2Z slenz') * (\S_{ nk } VZ' + u2Z ([a3]_ s) * \B^nk) =
    sgZ (s2Z slenx) * \S_{ nk } VX + \S_{ nk } VY }}.
Proof.
move=> Hnodup nk vz vx vy Hnk ptrz ptrx Hptrz Hptrx Hvy VZ VX VY VZ_nk VX_nk VY_nk Sum_VY slenx slenz Hslenx Hslenz.
rewrite /multi_add_s_s_u.

(* lw Z four16 rz *)

apply hoare_lw_back_alt'' with (fun s h =>
  [ rz ]_ s = vz /\ [ rx ]_ s = vx /\ [ ry ]_ s = vy /\ u2Z [ rk ]_s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
   (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [ Z]_ s = ptrz).

move => s h [] Hrz [] Hrx [] Hry [] Hrk Hheap.
exists ptrz.
split.
- rewrite -assert_m.mapsto2_mapstos in Hheap.
  Rotate Hheap.
  move: Hheap; apply monotony => // h'; apply mapsto_ext => //; by rewrite sext_Z2u.
- rewrite /update_store_lw.
  repeat Reg_upd; repeat (split => //).
  by Assert_upd.

(* lw X four16 rx *)

apply hoare_lw_back_alt'' with (fun s h =>
  [ rz ]_ s = vz /\ [ rx ]_ s = vx /\ [ ry ]_ s = vy /\ u2Z [ rk ]_s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [ Z ]_ s = ptrz /\ [ X ]_ s = ptrx).

move => s h [] Hrz [] Hrx [] Hry [] Hrk [] Hheap HrZ.
exists ptrx.
split.
- do 2 Rotate Hheap.
  rewrite -assert_m.mapsto2_mapstos in Hheap.
  Rotate Hheap.
  move: Hheap; apply monotony => // h'; apply mapsto_ext => //; by rewrite sext_Z2u.
- rewrite /update_store_lw.
  repeat Reg_upd; repeat (split => //).
  by Assert_upd.

(* pick_sign rx a0 a1 *)

apply while.hoare_seq with (fun s h =>
  [ rz ]_ s = vz /\ [ rx ]_ s = vx /\ [ ry ]_ s = vy /\ u2Z [ rk ]_s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [ Z ]_ s = ptrz /\
  [ X ]_ s = ptrx /\
  (s2Z [a1]_s) = sgZ (s2Z slenx)).

eapply while.hoare_conseq; last first.

apply (pick_sign_triple (fun s h =>
    [ rz ]_ s = vz /\ [ ry ]_ s = vy /\ u2Z [ rk ]_s = Z_of_nat nk /\
    [ Z ]_ s = ptrz /\ [ X ]_ s = ptrx)
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
   (var_e rx \+ int_e four32 |~> int_e ptrx ** int_e ptrx |--> VX) **
   var_e ry |--> VY) vx slenx).

- by Uniq_uniq r0.
- by Inde.
- by Inde.
- move => s h [] Hrz [] Hrx [] Hry [] Hrk [] Hheap [] HZ HX.
  split; first by [].
  split.
  + do 2 Rotate Hheap.
    rewrite -assert_m.mapsto2_mapstos in Hheap.
    by assoc_comm Hheap.
  + tauto.

move => s h [] Hrx [] Ha0 [] Ha1 [] Ha1_2 [] Hheap [] Hrz [] Hry [] Hrk [] HZ HX.
repeat (split; first by tauto).
split.
- do 2 RotateGoal.
  rewrite -assert_m.mapsto2_mapstos.
  rewrite conAE.
  move: Hheap; apply monotony => // h' Hheap.
  do 2 Rotate Hheap.
  clear h.
  by move: Hheap; apply monotony => // h Hheap.
- repeat (split; first by tauto).
  case: Ha1_2 => H.
    by rewrite H; rewrite H in Ha1.
  case: H => H; by rewrite H; rewrite H in Ha1.

(* If_bgez a1 *)

apply while.hoare_ifte.

(* a1 >= 0 *)

(* If_beq a1 r0 *)

apply while.hoare_ifte.

(* a1 == 0 *)

apply (hoare_prop_m.hoare_stren (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
  (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  sgZ (s2Z slenx) = 0)).

- move => s h.
  case; case; case=> Hrz [] Hrx [] Hry [] Hrk [] Hheap [] HZ [] HX Ha1 Ha1_2 Ha1_3.
  repeat (split; first by tauto).
  rewrite /= in Ha1_3.
  rewrite -Ha1.
  move/eqP in Ha1_3.
  rewrite store.get_r0 /zero32 Z2uK in Ha1_3.
  rewrite s2Z_u2Z_pos'; by rewrite Ha1_3.
  by [].

(* copy_s_u rk rz ry a0 a1 a2 a3  *)

apply while.hoare_seq with (fun s h => [rz ]_ s = vz /\ [rx ]_ s = vx /\
    [ry ]_ s = vy /\ u2Z [rk ]_ s = Z_of_nat nk /\
    ((var_e rz |--> (Z2u 32 (Z_of_nat nk)) :: ptrz :: nil ** int_e ptrz |--> VY) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
    [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\ sgZ (s2Z slenx) = 0).

have : uniq( rk, rz, ry, a0, a1, a2, a3, r0) by Uniq_uniq r0.
move/copy_s_u_triple/(_ _ _ _ VZ_nk VY_nk slenz _ Hptrz _ Hvy) => hoare_triple.
eapply (before_frame  (fun s h => [rz ]_ s = vz /\ [rx ]_ s = vx /\
    ((var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX)) s h /\
    [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
    sgZ (s2Z slenx) = 0)).
apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.
by apply hoare_triple.
- move=> {hoare_triple} s h H.
  case: H => rz_vz [rx_vx [ry_vy [rk_nk [Hmem [Z_ptrz [X_ptrx sgn_slenx]]]]]].
  rewrite -conAE conCE -conAE in Hmem.
  move: Hmem; apply monotony => // h1 Hh1.
  repeat (split => //); by assoc_comm Hh1.
- move=> {hoare_triple} s h [h1 [h2 [ h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
  case: Hh1 => [Hry [Hrk Hh1]].
  case: Hh2 => Hrz [Hrx [Hh2 [HZ [HX sgn_slenx]]]].
  repeat (split => //).
  have HVY : \S_{ nk } VY != 0.
    apply/negP => /eqP abs.
    move: Sum_VY.
    rewrite abs; by move/ltZZ.
  rewrite (negbTE HVY){HVY} in Hh1.
  rewrite -conAE conCE -conAE.
  exists h1, h2; repeat (split => //).
  by assoc_comm Hh1.

(** addiu a3 r0 zero16 *)

apply (hoare_prop_m.hoare_weak (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> (Z2u 32 (Z_of_nat nk)) :: ptrz :: nil ** int_e ptrz |--> VY) **
   (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\ sgZ (s2Z slenx) = 0 /\ [ a3 ]_s = zero32)); last first.

apply hoare_addiu'.
move => s h [] Hrz [] Hrx [] Hry [] Hrk [] Hheap [] HZ [] HX Hslenx_2.
rewrite /wp_addiu.
repeat Reg_upd; repeat (split => //).
by Assert_upd.
by rewrite add0i sext_Z2u.

move => s h [] Hrz [] Hrx [] Hry [] Hrk [] Hheap [] HZ [] HX [] Hslenx_2 Ha3.
exists VY, (Z2u 32 (Z_of_nat nk)).
have Htmp : u2Z (Z2u 32 (Z_of_nat nk)) = Z_of_nat nk.
  rewrite Z2uK //.
  split; first by apply Zle_0_nat.
  case: Hnk => _ Hnk.
  by apply: ltZ_trans; eauto.
have Htmp2 : sgZ (s2Z (Z2u 32 (Z_of_nat nk))) = 1.
  rewrite s2Z_u2Z_pos'; last first.
    rewrite Htmp.
    split; first by apply Zle_0_nat.
    by case: Hnk.
  rewrite Htmp.
  apply Zsgn_pos; by case: Hnk.
split; first by tauto.
split; first by [].
split.
  rewrite Htmp2 mul1Z s2Z_u2Z_pos' // Htmp [Peano.pred _]/=; omega.
split.
  rewrite Htmp2 Hslenx_2 /= (_: sgZ (\S_{ nk } VY) = 1) //=.
  apply Zsgn_pos; tauto.
split => //.
split; first by rewrite Ha3 Z2uK.
by rewrite Hslenx_2 /= Htmp2 mul1Z Ha3 Z2uK // mul0Z addZ0.

(* a1 > 0 *)

Local Open Scope machine_int_scope.

apply (hoare_prop_m.hoare_stren (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
  (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  sgZ (s2Z slenx) = 1 /\ (* TODO: mettre en haut, faire un pull_out*)
  [ a1 ]_ s = one32)).

move => s h [[H Htest2] Htest1].
case: H => Hrz [] Hrx [] Hry [] Hrk [] Hheap [] HZ [] HX Ha1.
suff: ([a1]_ s = one32).
  repeat (split => //).
  rewrite -Ha1 x s2Z_u2Z_pos'; by rewrite Z2uK.
rewrite /= in Htest2.
move/leZP in Htest2.
rewrite /= store.get_r0 // Z2uK // in Htest1.
case: (Zsgn_spec (s2Z slenx)).
  case => H1 H2.
  rewrite H2 -(@Z2sK 1 31) in Ha1.
  move/s2Z_inj in Ha1.
  apply s2Z_inj.
  rewrite Ha1 Z2sK //= s2Z_u2Z_pos' //=; by rewrite Z2uK.
  omega.
move => [].
  case => H1 H2.
  rewrite -H1 /= in Ha1.
  exfalso.
  move/negP in Htest1.
  apply/Htest1/eqP.
  by rewrite -s2Z_u2Z_pos.
case => H1 H2.
apply Zsgn_pos0 in Htest2.
rewrite Ha1 H2 /= in Htest2.
exfalso.
omega.

(* multi_add_u_u rk a1 ry X Z a0 a3 a2 *)

apply while.hoare_seq with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  (exists VZ', size VZ' = nk /\
    ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
    u2Z (store.lo s) <= 1 /\
    \S_{ nk } VZ' + u2Z (store.lo s) * \B^nk = \S_{ nk } VX + \S_{ nk } VY) /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\ sgZ (s2Z slenx) = 1).

have : uniq(rk, a1, ry, X, Z, a2, a3, a4, r0) by Uniq_uniq r0.
move/multi_add_u_u_u_triple/(_ nk vy ptrx ptrz Hptrz VY VX VY_nk VX_nk) => hoare_triple.
eapply (before_frame  (fun s h => [rz ]_ s = vz /\
  [rx ]_ s = vx /\
  ((var_e rz |--> slenz :: ptrz :: nil) **
    (var_e rx |--> slenx :: ptrx :: nil)) s h /\
  sgZ (s2Z slenx) = 1 )).
apply frame_rule_R.
  by apply hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
by [].

- move=> s h [Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [sgn_slenz Ha1]]]]]]]].
  rewrite -(conCE (_ |--> VZ)) 2!conAE conCE in Hmem.
  rewrite 2!conAE -1!conAE conCE in Hmem.
  move: Hmem; apply monotony => // h1 Hh1.
  exists VZ; repeat (split => //).
  rewrite -conAE (conCE (_ |--> VY)).
  move: Hh1; apply monotony => // h2.
  apply monotony => // h3; by apply mapstos_ext.
  by apply mapstos_ext.
- move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
  case: Hh2 => Hrz [Hrx [Hh2 sgn_slenx]].
  case: Hh1 => VZ' [len_VZ' [Hry [HX [HZ [Hrk [Hh1 [Hlo HSum]]]]]]].
  repeat (split => //).
  exists VZ'; repeat (split => //).
  rewrite -(conCE (_ |--> VZ')).
  rewrite 2!conAE -2!conAE conCE 2!conAE -2!conAE.
  exists h1, h2; repeat (split => //).
  rewrite (conCE (_ |--> VX)) conAE.
  move: Hh1; apply monotony => // h1'.
  apply monotony => // h1''; by apply mapstos_ext.
  rewrite HSum; ring.

(** mflo a3 *)

apply hoare_mflo with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  (exists VZ', size VZ' = nk /\
    ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
      u2Z ([ a3 ]_ s) <= 1 /\
      \S_{ nk } VZ' + u2Z ([a3]_s) * \B^nk = \S_{ nk } VX + \S_{ nk } VY) /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\ sgZ (s2Z slenx) = 1 ).

rewrite /wp_mflo => s h [Hrz [Hrx [Hry [Hrk [HVZ' [HZ [HX sgn_slenx]]]]]]].
repeat Reg_upd.
repeat (split => //).
case: HVZ' => VZ' [lenVZ' [Hmem [Hlo HSum]]].
exists VZ'; repeat (split => //).
by Assert_upd.

(* sw rk zero16 rz *)

apply hoare_sw_back' => s h [Hrz [Hrx [Hry [Hrk [HVZ' [HZ [HX sgn_slenx]]]]]]].
case: HVZ' => VZ' [lenVZ' [Hmem [Ha3 HSum]]].
exists (int_e slenz).
rewrite -mapsto2_mapstos in Hmem.
rewrite 3!conAE in Hmem.
move: Hmem; apply monotony => h1.
apply mapsto_ext => //=; by rewrite sext_Z2u // addi0.
apply currying => h2 Hh2.
exists VZ'; exists (Z2u 32 (Z_of_nat nk)).
split => //.
have Htmp0 : u2Z (Z2u 32 (Z_of_nat nk)) = Z_of_nat nk.
  rewrite Z2uK //.
  split; first by apply Zle_0_nat.
  case: Hnk => _ Hnk; by apply: ltZ_trans; eauto.
have Htmp : s2Z (Z2u 32 (Z_of_nat nk)) = Z_of_nat nk.
  rewrite s2Z_u2Z_pos' // Htmp0.
  split; first by apply Zle_0_nat.
  by case: Hnk => _.
rewrite Htmp.
have Htmp2 : sgZ (Z_of_nat nk) = 1 by apply Zsgn_pos; case: Hnk.
rewrite Htmp2.
split; first by assumption.
split; first by rewrite mul1Z.
split.
  rewrite sgn_slenx mul1Z.
  apply/esym/Zsgn_pos.
  move: (min_lSum nk VX) => ?; omega.
split.
  rewrite conCE in Hh2.
  rewrite -mapsto2_mapstos 3!conAE.
  move: Hh2; apply monotony => h3.
  apply mapsto_ext => /=.
  by rewrite sext_Z2u // addi0.
  apply u2Z_inj; congruence.
  by apply monotony.
split => //.
by rewrite sgn_slenx 2!mul1Z.

(* a1 < 0 *)

(* multi_lt rk ry X a0 a1 ret a2 a3 a4 *)

apply while.hoare_seq with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
  (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\ sgZ (s2Z slenx) = -1 /\
  ((\S_{ nk } VY < \S_{ nk } VX /\ [ret]_s = one32 /\ [a2]_s = zero32) \/
    (\S_{ nk } VY > \S_{ nk } VX /\ [ret]_s = zero32 /\ [a2]_s = one32) \/
    (\S_{ nk } VY = \S_{ nk } VX /\ [ret]_s = zero32 /\ [a2]_s = zero32))).

have : uniq(rk, ry, X, a0, a1, ret, a2, a3, a4, r0) by Uniq_uniq r0.
move/multi_lt_triple/(_ nk VY VX vy ptrx VY_nk VX_nk) => hoare_triple.
eapply (before_frame (fun s h => [rz ]_ s = vz /\
  [rx ]_ s = vx /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil)) s h /\
  [Z ]_ s = ptrz /\ sgZ (s2Z slenx) = -1 )).
apply frame_rule_R.
  by apply hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
by [].
- move=> s h [[Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX Ha1]]]]]]] /= Htest].
  move/leZP in Htest.
  rewrite 2!conAE -2!conAE conCE in Hmem.
  move: Hmem; apply monotony => // h1 Hh1.
  repeat (split => //).
  rewrite conCE.
  move: Hh1; apply monotony => // h2.
  by apply mapstos_ext.
  repeat (split => //).
  rewrite Ha1 in Htest.
  apply Zsgn_neg.
  case: (Zsgn_spec (s2Z slenx)).
    case=> _ abs; rewrite abs in Htest; omega.
  case.
    case=> _ abs; rewrite abs in Htest; omega.
  by case; move/Zgt_lt.
- move=> s h.
  case=> h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
  case: Hh1 => Hrk [Hry [HX [HSum Hh1]]].
  case: Hh2 => Hrz [Hrx [Hh2 [HZ sgn_slenx]]].
  repeat (split => //).
  rewrite 2!conAE -2!conAE conCE.
  exists h1, h2; repeat (split => //).
  rewrite conCE; move: Hh1; apply monotony => // h1'.
  by apply mapstos_ext.

(* If_beq ret,r0 *)

apply while.hoare_ifte.

(* ret == 0 *)

(* If_beq a2,r0 *)

apply while.hoare_ifte.

(* a2 == 0 *)

(* multi_zero_s rk *)
apply while.hoare_seq with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> zero32 :: ptrz :: nil ** int_e ptrz |--> VZ) **
  (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  sgZ (s2Z slenx) = -1 /\
  \S_{ nk } VY = \S_{ nk } VX).

have : uniq(rz, r0) by Uniq_uniq r0.
move/multi_zero_s_triple/(_ VZ ptrz slenz) => hoare_triple.
eapply (before_frame (fun s h => (([rz ]_ s = vz /\
  [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  sgZ (s2Z slenx) = -1 /\
  (\S_{ nk } VY < \S_{ nk } VX /\ [ret ]_ s = one32 /\ [a2 ]_ s = zero32 \/
    \S_{ nk } VY > \S_{ nk } VX /\ [ret ]_ s = zero32 /\ [a2 ]_ s = one32 \/
    \S_{ nk } VY = \S_{ nk } VX /\ [ret ]_ s = zero32 /\ [a2 ]_ s = zero32)) /\
eval_b (beq ret r0) (fst (s, h))) /\ eval_b (beq a2 r0) (fst (s, h)))).
apply frame_rule_R.
  by apply hoare_triple.
  simpl modified_regs; by Inde.
by [].
- move=> s h
  [[ [Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [sgn_slenx Hsum]]]]]]]] Htest1] Htest2].
  by move: Hmem; apply monotony.
- move=> s h H.
  case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
  case: Hh2 => [[Hh2 Htest1] Htest2].
  case: Hh2 => [Hrz [Hrx [Hry [Hrk [Hh2 [HZ [HX [sgn_slenx Hsum]]]]]]]].
  repeat (split => //).
  exists h1, h2; repeat (split => //).
  rewrite /= store.get_r0 in Htest1.
  move/eqP in Htest1; apply u2Z_inj in Htest1.
  rewrite /= store.get_r0 in Htest2.
  move/eqP in Htest2; apply u2Z_inj in Htest2.
  rewrite Htest1 Htest2 in Hsum.
  case: Hsum.
    case=> _ [] abs _.
    exfalso.
    by apply: Z2u_dis abs.
  case.
    case=> _ [] _ abs.
    exfalso.
    by apply: Z2u_dis abs.
  by case.

(* addiu a3 r0 zero16 *)

apply hoare_addiu' => s h H.
case: H => Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [sgn_slenx HSum]]]]]]].
rewrite /wp_addiu.
exists VZ, zero32.
split; first by tauto.
have Htmp : s2Z zero32 = 0 by rewrite s2Z_u2Z_pos' Z2uK.
rewrite Htmp [sgZ 0]/= mul0Z.
repeat Reg_upd.
split; first by [].
split; first by reflexivity.
split.
  rewrite sgn_slenx.
  apply/esym/Zsgn_null.
  rewrite HSum; ring.
split; first by Assert_upd.
split.
  by rewrite add0i sext_Z2u // Z2uK.
rewrite sgn_slenx HSum; ring.

(* a2 != 0 *)

(* multi_sub_u_u rk ry X Z a0 a1 a2 a3 a4 ret *)

apply while.hoare_seq with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  (exists VZ', size VZ' = nk /\
    u2Z [a3]_s <= 1 /\
    ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
    \S_{ nk } VZ' = \S_{ nk } VY - \S_{ nk } VX + u2Z [a3]_s * \B^nk) /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  sgZ (s2Z slenx) = -1 /\
  \S_{ nk } VY > \S_{ nk } VX).

have : uniq(rk, ry, X, Z, a0, a1, a2, a3, a4, ret, r0) by Uniq_uniq r0.
move/multi_sub_u_u_u_triple/(_ nk vy ptrx ptrz Hptrz VY VX VZ VY_nk VX_nk VZ_nk) => hoare_triple.
eapply (before_frame (fun s h =>([rz ]_ s = vz /\
       [rx ]_ s = vx /\
       ((var_e rz |--> slenz :: ptrz :: nil) **
        (var_e rx |--> slenx :: ptrx :: nil)) s h /\
       sgZ (s2Z slenx) = -1 /\
       \S_{ nk } VY > \S_{ nk } VX))).
apply frame_rule_R.
  by apply hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
move=> _; by Inde_mult.
- move=> s h [[[Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [sgn_slenx HSum]]]]]]]] Htest1] Htest2].
  rewrite -(conCE (_ |--> VZ)) 2!conAE conCE in Hmem.
  rewrite 2!conAE -1!conAE conCE in Hmem.
  move: Hmem; apply monotony => // h1 Hh1.
  repeat (split => //).
  rewrite -conAE (conCE (_ |--> VY)).
  move: Hh1; apply monotony => // h2.
  apply monotony => // h3; by apply mapstos_ext.
  by apply mapstos_ext.
  repeat (split => //).
  rewrite /= store.get_r0 in Htest1.
  move/eqP in Htest1.
  apply u2Z_inj in Htest1.
  rewrite Htest1 in HSum.
  rewrite /= store.get_r0 in Htest2.
  case: HSum.
    case=> _ [] abs _.
    exfalso. exact: Z2u_dis abs.
  case; first by case.
  by case=> _ [] _ abs; rewrite abs eqxx in Htest2.
- move=> s h.
  case=> h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
  case: Hh1 => VZ' [lenVZ' [Hry [HX [HZ [Hrk [Hh1 [Ha3 HSum]]]]]]].
  case: Hh2 => Hrz [Hrx [Hh2 [sgn_slen VY_VX]]].
  repeat (split => //).
  exists VZ'; repeat (split => //).
  rewrite -(conCE (_ |--> VZ')).
  rewrite 2!conAE -2!conAE conCE.
  rewrite 2!conAE -2!conAE.
  exists h1, h2; repeat (split => //).
  rewrite (conCE (_ |--> VX)) conAE.
  move: Hh1; apply monotony => // h1'.
  apply monotony => // h1''; by apply mapstos_ext.

(* lw a0 zero16 rk *)

(* sw a0 zero16 rk *)

apply hoare_sw_back' => s h [Hrz [Hrx [Hry [Hrk [HVZ' [HZ [HX [sgn_slenx VY_VX]]]]]]]].

exists (int_e slenz).
case: HVZ' => VZ' [lenVZ' [Ha3 [Hmem HSum]]].
rewrite -mapsto2_mapstos in Hmem.
rewrite 2!conAE in Hmem.
move: Hmem; apply monotony => // h'.
apply mapsto_ext => //=; by rewrite sext_Z2u // addi0.
apply currying => h'' Hh''.
exists VZ', (Z2u 32 (Z_of_nat nk)).
split; first by [].
have Htmp0 : u2Z (Z2u 32 (Z_of_nat nk)) = Z_of_nat nk.
  rewrite Z2uK //.
  split; first by apply Zle_0_nat.
  case: Hnk => _ Hnk; by apply: ltZ_trans; eauto.
have Htmp : s2Z (Z2u 32 (Z_of_nat nk)) = Z_of_nat nk.
  rewrite s2Z_u2Z_pos' // Htmp0.
  split; first by apply Zle_0_nat.
  by case: Hnk => _.
rewrite Htmp.
have Htmp2 : sgZ (Z_of_nat nk) = 1 by apply Zsgn_pos; by case: Hnk.
rewrite Htmp2.
split; first by [].
split; first by rewrite mul1Z.
split.
  rewrite sgn_slenx.
  apply/esym/Zsgn_pos; omega.
split.
  rewrite conCE in Hh''.
  rewrite -mapsto2_mapstos.
  rewrite 2!conAE.
  move: Hh''; apply monotony => // h'''.
  apply mapsto_ext => //=.
  by rewrite sext_Z2u // addi0.
  apply u2Z_inj; by rewrite Htmp0.
split; first by [].
have {Ha3}[Ha3 | Ha3] : u2Z [a3 ]_ s = 0 \/ u2Z [a3 ]_ s = 1.
  move: (min_u2Z [a3]_s) => ?; omega.
- rewrite HSum Ha3 sgn_slenx; ring.
- rewrite Ha3 mul1Z in HSum.
  have abs : \B^nk <= \S_{ nk } VZ'.
    rewrite HSum.
    move: (Zbeta_gt0 nk) => ?; omega.
    move: (max_lSum nk VZ').
    by move/(leZ_ltZ_trans abs)/ltZZ.

(* multi_sub_u_u rk X ry Z a0 a1 ret a3 a2 a4 *)

apply while.hoare_seq with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  (exists VZ', size VZ' = nk /\
    u2Z [a3]_s <= 1 /\
    ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
    \S_{ nk } VZ' = \S_{ nk } VX - \S_{ nk } VY + u2Z [a3]_s * \B^nk) /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  sgZ (s2Z slenx) = -1 /\
  \S_{ nk } VY < \S_{ nk } VX).

have : uniq(rk, X, ry, Z, a0, a1, ret, a3, a2, a4, r0) by Uniq_uniq r0.
move/multi_sub_u_u_u_triple/(_ nk ptrx vy ptrz Hptrz VX VY VZ VX_nk VY_nk VZ_nk) => hoare_triple.
eapply (before_frame (fun s h => [rz ]_ s = vz /\ [rx ]_ s = vx /\
  ((var_e rz |--> slenz :: ptrz :: nil) ** (var_e rx |--> slenx :: ptrx :: nil)) s h /\
  sgZ (s2Z slenx) = -1 /\
  \S_{ nk } VY < \S_{ nk } VX)).
apply frame_rule_R.
  by apply hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
by [].
- move=> s h [[Hrz [Hrx [Hry [Hrk [Hmem [HZ [HX [sgn_slenx HSum]]]]]]]] Htest].
  rewrite -(conCE (_ |--> VZ)) 2!conAE -2!conAE conCE 2!conAE -2!conAE in Hmem.
  move: Hmem; apply monotony => // h1 Hh1.
  repeat (split => //).
  rewrite conAE in Hh1; move: Hh1; apply monotony => // h1''.
  by apply mapstos_ext.
  apply monotony => // h1'''.
  by apply mapstos_ext.
  repeat (split => //).
  rewrite /= in Htest.
  case: HSum.
    by case.
  case;
    case=> _ [] abs _; rewrite abs store.get_r0 in Htest ;
    by rewrite Z2uK // eqxx in Htest.
- move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
  case: Hh1 => VZ' [lenVZ' [HX [Hry [HZ [Hrk [Hh1 [Ha3 HSum]]]]]]].
  case: Hh2 => Hrz [Hrx [Hh2 [sgn_slenz VY_VX]]].
  repeat (split => //).
  exists VZ'; repeat (split => //).
  rewrite -(conCE (_ |--> VZ')).
  rewrite 2!conAE -2!conAE conCE 2!conAE -2!conAE.
  exists h1, h2; repeat (split => //).
  rewrite conAE.
  move: Hh1; apply monotony => h1' //.
  by apply mapstos_ext.
  apply monotony => h1'' //; by apply mapstos_ext.

(* subu a0 r0 rk *)

apply while.hoare_seq with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  (exists VZ', size VZ' = nk /\
    u2Z [a3]_s <= 1 /\
    ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) ** var_e ry |--> VY) s h /\
    \S_{ nk } VZ' = \S_{ nk } VX - \S_{ nk } VY + u2Z [a3]_s * \B^nk) /\
  [Z ]_ s = ptrz /\ [X ]_ s = ptrx /\
  sgZ (s2Z slenx) = -1 /\
  \S_{ nk } VY < \S_{ nk } VX /\
  s2Z [a0]_s = - Z_of_nat nk).

apply hoare_subu' => s h [Hrz [Hrx [Hry [Hrk [HVZ' [HZ [HX [sgn_slenx VY_VX]]]]]]]].
rewrite /wp_subu.
repeat Reg_upd.
case: HVZ' => VZ' [lenVZ' [Ha3 [Hmem HSum]]].
repeat (split => //).
exists VZ'; repeat (split => //).
by Assert_upd.
rewrite add0i s2Z_cplt2; last first.
  rewrite weirdE Hrk.
  move=> abs; rewrite abs in Hnk.
  case: Hnk => _; by move/ltZZ.
congr Zopp.
rewrite s2Z_u2Z_pos' // Hrk.
split; first by apply Zle_0_nat.
by case: Hnk.

(* sw a0 zero16 rk *)

apply hoare_sw_back' => s h [Hrz [Hrx [Hry [Hrk [HVZ' [HZ [HX [sgn_slenx [VY_VX Ha0]]]]]]]]].
case: HVZ' => VZ' [lenVZ' [Ha3 [Hmem HSum]]].
exists (int_e slenz).
rewrite -mapsto2_mapstos 2!conAE in Hmem.
move: Hmem; apply monotony => // h1.
apply mapsto_ext => //=; by rewrite sext_Z2u // addi0.
apply currying=> h1' Hh1'.
have Htmp : s2Z (Z2s 32 (- Z_of_nat nk)) = - Z_of_nat nk by rewrite Z2sK //; omega.
have Htmp2 : sgZ (- Z_of_nat nk) = -1 by apply Zsgn_neg; omega.
exists VZ', (Z2s 32 (- Z_of_nat nk)); repeat (split => //).

by rewrite Htmp Htmp2 mulN1Z.

rewrite sgn_slenx Htmp Htmp2.
symmetry.
apply Zsgn_neg; omega.

rewrite conCE in Hh1'.
rewrite -mapsto2_mapstos 2!conAE.
move: Hh1'; apply monotony => // h1''.
apply mapsto_ext => //=.
by rewrite sext_Z2u // addi0.
apply s2Z_inj.
by rewrite Htmp.

rewrite Htmp sgn_slenx Htmp2.
have {Ha3}[Ha3 | Ha3] : u2Z [a3 ]_ s = 0 \/ u2Z [a3 ]_ s = 1.
  move: (min_u2Z [a3]_s) => ?; omega.
- rewrite HSum Ha3; ring.
- rewrite Ha3 mul1Z in HSum.
  have abs : \B^nk <= \S_{ nk } VZ'.
    rewrite HSum.
    move: (Zbeta_gt0 nk) => ?; omega.
    move: (max_lSum nk VZ').
    by move/(leZ_ltZ_trans abs)/ltZZ.
Qed.

Lemma multi_add_s_s_u_triple rk rz rx ry a0 a1 a2 a3 a4 ret X Z :
  uniq(rk, rz, rx, ry, a0, a1, a2, a3, a4, ret, X, Z, r0) ->
  forall nk vz vx vy, 0 < Z_of_nat nk < 2 ^^ 31 ->
    forall ptrz ptrx,
      u2Z ptrz + 4 * Z_of_nat nk < \B^1 ->
      u2Z ptrx + 4 * Z_of_nat nk < \B^1 ->
      u2Z vy + 4 * Z_of_nat nk < \B^1 ->
      forall VZ VX VY, size VZ = nk -> size VX = nk -> size VY = nk ->
        forall slenx slenz,
          s2Z slenx = sgZ (s2Z slenx) * Z_of_nat nk ->
          s2Z slenz = sgZ (s2Z slenz) * Z_of_nat nk ->
          sgZ (s2Z slenx) = sgZ (sgZ (s2Z slenx) * \S_{ nk } VX) ->
  {{ fun s h =>
    [ rz ]_ s = vz /\ [ rx ]_ s = vx /\ [ ry ]_ s = vy /\ u2Z [ rk ]_s = Z_of_nat nk /\
    ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
      (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
      var_e ry |--> VY) s h }}
  multi_add_s_s_u rk rz rx ry a0 a1 a2 a3 a4 ret X Z
  {{ fun s h => exists VZ' slenz', size VZ' = nk /\
    [ry ]_ s = vy /\
    s2Z slenz' = sgZ (s2Z slenz') * Z_of_nat nk /\
    sgZ (s2Z slenz') = sgZ (sgZ (s2Z slenx) * \S_{ nk } VX + \S_{ nk } VY) /\
    ((var_e rz |--> slenz' :: ptrz :: nil ** int_e ptrz |--> VZ') **
      (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
      var_e ry |--> VY
    ) s h /\
    u2Z ([a3]_ s) <= 1 /\
    sgZ (s2Z slenz') * (\S_{ nk } VZ' + u2Z ([a3]_ s) * \B^nk) =
    sgZ (s2Z slenx) * \S_{ nk } VX + \S_{ nk } VY
  }}.
Proof.
move=> Hregs nk vz vx vy Hnk ptrz ptrx ptrz_fit ptrx_fit vy_fit VZ VX VY VZ_nk VX_nk VY_nk slenx slenz Hslenx Hslenz
  X_encoding.
rewrite /multi_add_s_s_u.

apply while.hoare_seq with (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
   (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  ((0 = \S_{ nk } VY -> [a2]_s = one32) /\
   (0 < \S_{ nk } VY -> [a2]_s = zero32))).

have : uniq(rk, ry, a0, a1, a2, r0) by Uniq_uniq r0.
move/(multi_is_zero_u_triple)/(_ nk VY _ VY_nk vy_fit) => hoare_triple.
eapply (before_frame  (fun s h =>
  [rz ]_ s = vz /\ [rx ]_ s = vx /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX)) s h)).
apply frame_rule_R.
  by apply hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
by [].
- move=> s h [Hrz [Hrx [Hry [Hrk Hmem]]]].
  rewrite -conAE conCE in Hmem.
  by move: Hmem; apply monotony => // h1.
- move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
  case: Hh1 => Hrk [Hry [Hh1 HSum]].
  case: Hh2 => [Hrz [Hrx Hh2]].
  repeat (split => //).
  rewrite -conAE conCE.
  by exists h1, h2.

apply while.hoare_ifte.

apply while.hoare_seq with (fun s h => exists VZ' slenz',
  size VZ' = nk /\
  s2Z slenz' = sgZ (s2Z slenz') * Z_of_nat nk /\
  sgZ (s2Z slenz') = sgZ (sgZ (s2Z slenx) * \S_{ nk } VX) /\
  (if slenx == zero32 then True else \S_{ nk } VZ' = \S_{ nk } VX) /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz' :: ptrz :: nil ** int_e ptrz |--> VZ') **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h /\
  0 = \S_{ nk } VY).

have : uniq(rk, rz, rx, a0, a1, a2, a3, a4, r0) by Uniq_uniq r0.
move/copy_s_s_triple/(_ VZ VX nk VZ_nk VX_nk slenz ptrz ptrz_fit slenx ptrx ptrx_fit vx
   Hslenx X_encoding) => hoare_triple.
eapply (before_frame (fun s h => [rz ]_ s = vz /\ [ry ]_ s = vy /\
    (var_e ry |--> VY) s h /\ 0 = \S_{ nk } VY)).
apply frame_rule_R.
  by apply hoare_triple.
  rewrite [modified_regs _]/=; by Inde.
by [].
move=> s h [[Hrz [Hrx [Hry [Hrk [Hmem [HSum1 HSum2]]]]]] Htest].
rewrite -conAE in Hmem.
move: Hmem; apply monotony => // h1 Hh1.
repeat (split => //).
case/leZ_eqVlt : (min_lSum nk VY) => //.
move/HSum2 => abs; by rewrite /= abs store.get_r0 Z2uK in Htest.

move=> s h [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
case: Hh1 => Hrx [Hrk Hh1].
case: Hh2 => Hrz [Hry [Hh2 HSum]].
case: (dec_int slenx zero32).
  move/eqP => slenx0.
  rewrite slenx0 in Hh1.
  exists VZ, slenx.
  repeat (split => //).
  by rewrite slenx0.
  rewrite -conAE; by exists h1, h2.
move/eqP/negbTE => abs; rewrite abs in Hh1.
exists VX, slenx.
repeat (split => //).
by rewrite abs.
rewrite -conAE.
by exists h1, h2.
apply pull_out_exists => VZ'.
apply pull_out_exists => slenz'.
apply hoare_addiu'.
move=> s h [lenVZ' [H_ [Hslenz' [VZ'_VX [Hrz [Hrx [Hry [Hrk [H HSum]]]]]]]]].
rewrite /wp_addiu.
exists VZ', slenz'.
Reg_upd.
rewrite sext_Z2u // addi0 store.get_r0 Z2uK //.
repeat Reg_upd.
repeat (split => //).
by rewrite -HSum addZ0.
by Assert_upd.
rewrite mul0Z addZ0 -HSum addZ0.
case: ifP VZ'_VX.
  move/eqP => ? _; subst slenx.
  have is0 : s2Z zero32 = 0.
    by rewrite s2Z_u2Z_pos' // Z2uK.
  rewrite is0 /= in Hslenz' *.
  rewrite Hslenz'; ring.
move=> slenx0 VZ'_VX.
rewrite VZ'_VX; congr (_ * _).
by rewrite Hslenz' -X_encoding.

apply (hoare_prop_m.hoare_stren (fun s h =>
  0 < \S_{ nk } VY /\
  [rz ]_ s = vz /\ [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rz |--> slenz :: ptrz :: nil ** int_e ptrz |--> VZ) **
    (var_e rx |--> slenx :: ptrx :: nil ** int_e ptrx |--> VX) **
    var_e ry |--> VY) s h)).

move=> s h [[Hrz [Hrx [Hry [Hrk [Hmem [HSum1 HSum2]]]]]] Htest].
repeat (split => //).
case/leZ_eqVlt :(min_lSum nk VY) => //.
move/HSum1 => abs.
by rewrite /= abs store.get_r0 !Z2uK in Htest.
apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => HSum.
apply multi_add_s_s_u0_triple => //; tauto.
Qed.

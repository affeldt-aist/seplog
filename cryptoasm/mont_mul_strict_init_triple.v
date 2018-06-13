(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext ssrnat_ext seq_ext machine_int multi_int uniq_tac.
Import MachineInt.
Require Import mips_seplog mips_frame mips_contrib mips_tactics mapstos.
Require Import multi_zero_u_prg mont_mul_strict_prg multi_zero_u_triple.
Require Import mont_mul_strict_triple.
Import expr_m.
Import assert_m.

Local Open Scope machine_int_scope.
Local Open Scope eqmod_scope.
Local Open Scope heap_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope multi_int_scope.
Local Open Scope zarith_ext_scope.

Section mont_mul_strict_init.

Variables k alpha x y z m one ext int_ X_ Y_ M_ Z_ quot C t s_ : reg.

Lemma mont_mul_strict_init_triple : uniq(k, alpha, x, y, z, m, one,
    ext, int_, X_, Y_, M_, Z_, quot, C, t, s_, r0) ->
  forall nk valpha vx vy vm vz X Y M,
  u2Z (M `32_ 0) * u2Z valpha =m -1 {{ \B^1 }} ->
  size X = nk -> size Y = nk -> size M = nk ->
  u2Z vz + 4 * Z_of_nat nk.+1 < \B^1 ->
  \S_{ nk } X < \S_{ nk } M -> \S_{ nk } Y < \S_{ nk } M ->
  {{fun s h => exists Z, size Z = nk /\
      [x]_s = vx /\ [y]_s = vy /\ [z]_s = vz /\ [m]_s = vm /\
      u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
      (var_e x |--> X ** var_e y |--> Y ** var_e z |--> Z ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h}}
  mont_mul_strict_init k alpha x y z m one ext int_ X_ Y_ M_ Z_ quot C t s_
  {{ fun s h => exists Z, size Z = nk /\
    [x]_s = vx /\ [y]_s = vy /\ [z]_s = vz /\ [m]_s = vm /\
    u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
    (var_e x |--> X ** var_e y |--> Y ** var_e z |--> Z ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
    \B^nk * \S_{ nk } Z =m \S_{ nk } X * \S_{ nk } Y {{ \S_{ nk } M }} /\ \S_{ nk } Z < \S_{ nk } M }}.
Proof.
move=> Hset nk valpha vx vy vm vz X Y M Halpha HlenX HlenY HlenM Hnz HXM HYM.
rewrite /mont_mul_strict_init.

(**  multi_zero ext k Z_ z ; *)

apply pull_out_exists => Z.

apply (hoare_prop_m.hoare_stren (!(fun s => size Z = nk) **
  (fun s h => [x]_s = vx /\ [y]_s = vy /\ [z]_s = vz /\ [m]_s = vm /\
    u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
    (((var_e x |--> X ** var_e y |--> Y) ** var_e z |--> Z ++ zero32 :: nil) ** var_e m |--> M ++ zero32 :: nil) s h))).

move=> s h [HlenZ [Hrx [Hry [Hrz [Hrm_ [Hrk [Hralpha Hmem]]]]]]].
exists heap.emp, h; repeat (split => //).
by map_tac_m.Disj.
by map_tac_m.Equal.
by rewrite !assert_m.conAE.

apply pull_out_bang => HlenZ.

apply (hoare_prop_m.hoare_stren 
  ((fun s h => [z]_s = vz /\ u2Z [k]_s = Z_of_nat nk /\ (var_e z |--> Z) s h) **
   (fun s h => [x]_s = vx /\ [y]_s = vy /\ [m]_s = vm /\ [alpha]_s = valpha /\
      (var_e x |--> X ** var_e y |--> Y ** var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 **
      var_e m |--> M ++ zero32 :: nil) s h))).

move=> s h [Hrx [Hry [Hrz [Hrm_ [Hrk [Hralpha Hmem]]]]]].
rewrite decompose_last_equiv HlenZ !assert_m.conAE assert_m.conCE !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
case: Hmem => [h1 [h2 [Hdisj [Hunion [Hmem1 Hmem2]]]]].
exists h1, h2; repeat (split; trivial).
by assoc_comm Hmem2.

apply while.hoare_seq with
  ((fun s h => [z]_s = vz /\ u2Z [k]_s = Z_of_nat nk /\ (var_e z |--> nseq nk zero32) s h) **
    (fun s h => [x]_s = vx /\ [y]_s = vy /\ [m]_s = vm /\ [alpha]_s = valpha /\
      (var_e x |--> X ** var_e y |--> Y ** var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 **
        var_e m |--> M ++ zero32 :: nil) s h)).

apply frame_rule_R.
- eapply multi_zero_u_triple; eauto.
  + by Uniq_uniq r0.
  + rewrite Z_S in Hnz; omega.
- by Inde_frame.
- move=> ?; by Inde_mult.

apply while.hoare_seq with (fun s h => [x]_s = vx /\ [y]_s = vy /\ [z]_s = vz /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e y |--> Y ** var_e z |--> nseq nk zero32 ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  store.multi_null s).

(* TODO: essayer de factoriser les operations suivantes en une fonction *)

(**  (mflhxu r0 ; *)

apply hoare_mflhxu with (fun s h => [x]_s = vx /\ [y]_s = vy /\ [z]_s = vz /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e y |--> Y ** var_e z |--> nseq nk zero32 ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  store.acx s = Z2u store.acx_size 0).

move=> s h [h1 [h2 [Hdisj [Hunion [[Hrz [Hrk Hmem1]] [Hrx [Hry [Hrm_ [Hralpha Hmem2]]]]]]]]].
rewrite /wp_mflhxu.
repeat Reg_upd; repeat (split; trivial).
move: {Hmem1 Hmem2}(assert_m.con_cons _ _ _ _ _ Hdisj Hmem1 Hmem2) => Hmem.
rewrite Hunion decompose_last_equiv size_nseq store.upd_r0.

Assert_upd; by assoc_comm Hmem.

by apply store.acx_mflhxu_op.

(**  mthi r0 ; *)

apply hoare_mthi with (fun s h => [x]_s = vx /\ [y]_s = vy /\ [z]_s = vz /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e y |--> Y ** var_e z |--> nseq nk zero32 ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  store.acx s = Z2u store.acx_size 0 /\ store.hi s = zero32).

move=> {Z HlenZ} s h [Hrx [Hry [Hrz [Hrm_ [Hrk [Hralpha [mem Hacx]]]]]]].
rewrite /wp_mthi.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.acx_mthi_op.
by rewrite store.hi_mthi_op.

(**  mtlo r0) ; *)

apply hoare_mtlo'.

move=> {Z HlenZ} s h [Hrx [Hry [Hrz [Hrm_ [Hrk [Hralpha [mem [Hacx Hhi]]]]]]]].
rewrite /wp_mtlo.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
apply store.utoZ_multi_null.
by rewrite store.utoZ_def store.hi_mtlo_op store.acx_mtlo_op store.lo_mtlo_op Hacx Hhi /zero32 !Z2uK.

(**  mont_mul_strict k alpha x y z m_ one ext int_ X_ Y_ M_ Z_ quot C t s_. *)

by eapply mont_mul_strict_triple; eauto.
Qed.

End mont_mul_strict_init.

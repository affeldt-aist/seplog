(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext uniq_tac machine_int.
Require Import multi_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_tactics mapstos.
Require Import mont_mul_prg.

Local Open Scope machine_int_scope.
Local Open Scope eqmod_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope heap_scope.
Import expr_m.
Local Open Scope mips_expr_scope.
Import assert_m.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope uniq_scope.
Local Open Scope multi_int_scope.

Lemma mont_square_triple (k alpha x z m one ext int_ X_ Y_ M_ Z_ quot C t s_ : reg) :
  uniq(k, alpha, x, z, m, one, ext, int_, X_, Y_, M_, Z_, quot, C, t, s_, r0) ->
  forall nk valpha vx vm vz X M,
    u2Z (M `32_ 0) * u2Z valpha =m -1 {{ \B^1 }} ->
    size X = nk -> size M = nk -> u2Z vz + 4 * Z_of_nat nk < \B^1 ->
    \S_{ nk } X < \S_{ nk } M ->
{{ fun s h => [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> nseq nk zero32 ** var_e m |--> M) s h /\ store.multi_null s }}
montgomery k alpha x x z m one ext int_ X_ Y_ M_ Z_ quot C t s_
{{ fun s h => exists Z, size Z = nk /\ [x]_s = vx /\ [z]_s = vz /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  \B^nk * \S_{ nk.+1 } (Z ++ [C]_s :: nil) =m \S_{ nk } X * \S_{ nk } X {{ \S_{ nk } M }} /\
  \S_{ nk.+1 } (Z ++ [C]_s :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk.-1 }}.
Proof.
move=> Hset nk valpha vx vm vz X M Halpha Hx Hm Hnz HX.
rewrite /montgomery.

(** addiu one r0 one16; *)

NextAddiu.
move=> s h [r_x [r_z [r_m [r_k [r_alpha [Hmem Hmu]]]]]].
rewrite /wp_addiu.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.multi_null_upd.

(** addiu C r0 zero16; *)

NextAddiu.
move=> s h [[r_x [r_z [r_m [r_k [r_alpha [Hmem Hmu]]]]]] r_one].
rewrite /wp_addiu.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.multi_null_upd.

(** addiu ext r0 zero16; *)

NextAddiu.
move=> s h [[[r_x [r_z [r_m [r_k [r_alpha [Hmem Hmu]]]]]] r_one] r_C].
rewrite /wp_addiu.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.multi_null_upd.

(** while (bne ext k) *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists Z next, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\ (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s <= u2Z [k]_s /\ [one]_s = one32 /\
  (next <> O -> u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk.-1) /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next)).

move=> s h [[[[r_x [r_z [r_m [r_k [r_alpha [Hmem Hmu]]]]]] r_one] r_C] r_ext].
exists (nseq nk zero32), O; repeat (split => //).
by rewrite size_nseq.
by rewrite r_ext sext_Z2u // addi0 store.get_r0 Z2uK.
rewrite r_ext sext_Z2u // addi0 store.get_r0 Z2uK //; exact/min_u2Z.
apply u2Z_inj; by rewrite r_one sext_Z2u // store.get_r0 addC addi0 Z2uK.

exists 0.
have -> : nseq nk zero32 ++ [C ]_ s :: nil = nseq nk.+1 zero32.
  suff -> : [ C ]_s = zero32 by rewrite nseqS.
  apply u2Z_inj; by rewrite r_C sext_Z2u // addi0 store.get_r0.
rewrite lSum_nseq_0.
split; first by [].
(* about X * Y < M *)
rewrite mulZ1 !mul0Z add0Z; apply mulZ_gt0 => //.
apply (@leZ_ltZ_trans (\S_{ nk } X)) => //; exact: min_lSum.

move=> s h [[Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [Hext [Hextk' [Hone [Ht Hinv]]]]]]]]]]]]] Hextk].
rewrite /= r_k Hext in Hextk; move/negPn/eqP/Z_of_nat_inj in Hextk; subst next.

exists Z; do 7 (split; trivial).
case: Hinv => K [Hinv1 Hinv2].
split; first by exists K.
split.
(* about X * Y < M *)
- apply/(@ltZ_pmul2r \B^nk).
  exact/Zbeta_gt0.
  by rewrite mulZC Hinv1.
apply Ht; by destruct nk.

(** lwxs X ext x; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists Z next, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next).

move=> s h [ [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Ht Hinv]]]]]]]]]]]]] Hextk].
rewrite /= r_ext r_k in Hextk, Hextk'.
move/eqP in Hextk; move/Nat2Z.inj_le/leP in Hextk'.
have {Hextk}Hextk : next <> nk by contradict Hextk; rewrite Hextk.
have {Hextk'}Hextk' : (next < nk)%nat by rewrite ltn_neqAle Hextk' andbT; apply/eqP.
exists (X `32_ next); split.
- Decompose_32 X next X1 X2 HlenX1 HX'; last by rewrite Hx.
  rewrite HX' (decompose_equiv _ _ _ _ _ HlenX1) !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u r_ext inj_mult mulZC.
- rewrite /update_store_lwxs.
  exists Z, next; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  rewrite r_ext r_k; exact/inj_lt_iff/leP.

(** lw Y zero16 y; *)

apply hoare_lw_back_alt'' with (fun s h => exists Z next, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\ [Y_]_s = X `32_ 0).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk r_X_]]]]]]]]]]]]]].

destruct X as [| hdx tlx]; first by destruct nk.
exists hdx; split.
rewrite [assert_m.mapstos _ _]/= !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // h'.
apply mapsto_ext => //=; by rewrite sext_0 addi0.

rewrite /update_store_lw.
exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** lw Z_ zero16 z; *)

apply hoare_lw_back_alt'' with (fun s h => exists Z next, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\
  [Y_]_s = X `32_ 0 /\ [Z_]_s = Z `32_ 0).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [r_X_ r_Y_]]]]]]]]]]]]]]].

destruct Z as [| hdz tlz]; first by destruct nk.
exists hdz; split.
rewrite assert_m.conAE assert_m.conCE /= !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // h'.
apply mapsto_ext => //=; by rewrite sext_0 addi0.
rewrite /update_store_lw.
exists (hdz :: tlz), next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** multu X Y; *)

apply hoare_multu with (fun s h => exists Z next, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\
  [Y_]_s = X `32_ 0 /\ [Z_]_s = Z `32_ 0 /\
  store.utoZ s <= (\B^1 - 1) * (\B^1 - 1) /\
  store.utoZ s = u2Z (X `32_ next) * u2Z (X `32_ 0)).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [r_X_ [r_Y_ r_Z_]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite store.utoZ_multu; exact: max_u2Z_umul.
by rewrite store.utoZ_multu (@u2Z_umul 32) r_X_ r_Y_.

(** lw M zero16 m; *)

apply hoare_lw_back_alt'' with (fun s h => exists Z next, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\ [Y_]_s = X `32_ 0 /\
  [Z_]_s = Z `32_ 0 /\ store.utoZ s <= (\B^1 - 1) * (\B^1 - 1) /\
  store.utoZ s = u2Z (X `32_ next) * u2Z (X `32_ 0) /\
  [M_]_s = M `32_ 0).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [r_X_ [r_Y_ [r_Z_ [Hm1 Hm2]]]]]]]]]]]]]]]]]].
destruct M as [| hdm tlm]; first by destruct nk.
exists hdm; split.
do 2 rewrite assert_m.conCE /= !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // h'.
apply mapsto_ext => //=; by rewrite sext_0 addi0.
exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** maddu Z_ one; *)

apply hoare_maddu with (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk}  M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\ [Y_]_s = X `32_ 0 /\
  [Z_]_s = Z `32_ 0 /\ store.utoZ s <= \B^1 * (\B^1 - 1) /\
  store.utoZ s = u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\
  [M_]_s = M `32_ 0).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [r_X_ [r_Y_ [r_Z_ [Hm1 [Hm2 r_M_]]]]]]]]]]]]]]]]]]].

exists Z, next.
have Htmp : store.utoZ s < \B^2 * (2 ^^ store.acx_size - 1).
  apply (@leZ_ltZ_trans ((\B^1 - 1) * (\B^1 - 1))); first by [].
  apply (@ltZ_leZ_trans (\B^2 * (2 ^^ 8 - 1))); first by [].
  exact/leZ_wpmul2r.
repeat Reg_upd.
do 7 (split; trivial).
by Assert_upd.
do 8 (split; trivial).
split.
  rewrite store.utoZ_maddu // Hone umul_1 (@u2Z_zext 32) r_Z_.
  apply (@leZ_trans ((\B^1 - 1) + (\B^1 - 1) * (\B^1 - 1))) => //.
  apply leZ_add.
  apply Zle_minus_1; exact: max_u2Z.
  rewrite Hm2 -u2Z_umul; exact: max_u2Z_umul.
by rewrite store.utoZ_maddu // Hone umul_1 (@u2Z_zext 32) r_Z_ Hm2 addZC.

(** mflo t; *)

apply hoare_mflo with (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\ [Y_]_s = X `32_ 0 /\
  [Z_]_s = Z `32_ 0 /\ store.utoZ s <= \B^1 * (\B^1 - 1) /\
  store.utoZ s = u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\
  [M_]_s = M `32_ 0 /\
  [t]_s = ((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [r_X_ [r_Y_ [r_Z_ [Hm1 [Hm2 r_M_]]]]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

apply store.lo_remainder.
by rewrite -addnA leq_addl.

rewrite Hm2 u2Z_add //.
by rewrite u2Z_umul u2Z_zext.
rewrite u2Z_zext ZpowerD -Zbeta1E -ZbetaD /=.
apply (@leZ_ltZ_trans ((\B^1 - 1) * (\B^1 - 1) + (\B^1 - 1))); last by [].
apply leZ_add; first exact: max_u2Z_umul.
apply Zle_minus_1; exact: max_u2Z.

(** mfhi s; *)

apply hoare_mfhi with (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\ [Y_]_s = X `32_ 0 /\
  [Z_]_s = Z `32_ 0 /\ store.utoZ s <= \B^1 * (\B^1 - 1) /\
  store.utoZ s = u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\
  [M_]_s = M `32_ 0 /\
  [t]_s = ((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32 /\
  u2Z ([s_]_s `|| [t]_s) = u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0)).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [ r_X_ [r_Y_ [r_Z_ [Hm1 [Hm2 [r_M_ r_t]]]]]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

have H : store.lo s = [t]_s.
  rewrite r_t; apply store.lo_remainder.
  + by rewrite -addnA leq_addl.
  + rewrite Hm2 -u2Z_umul u2Z_add.
    * by rewrite u2Z_zext.
    * rewrite u2Z_zext ZpowerD -Zbeta1E -ZbetaD /=.
      apply (@leZ_ltZ_trans ((\B^1 - 1) * (\B^1 - 1) + (\B^1 - 1))); last by [].
      apply leZ_add; [exact: (@max_u2Z_umul 32) | exact/Zle_minus_1/max_u2Z].

rewrite -H u2Z_concat -Zbeta1E.
rewrite store.utoZ_def store.utoZ_acx_beta2 in Hm2; last exact: (@leZ_ltZ_trans (\B^1 * (\B^1 - 1))).
rewrite Z2uK in Hm2; last by split; [exact: leZZ | exact: expZ_gt0].
rewrite -Hm2; ring.

(** multu t alpha; *)

apply hoare_multu with (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\ [Y_]_s = X `32_ 0 /\
  [Z_]_s = Z `32_ 0 /\ store.utoZ s <= (\B^1 - 1) * (\B^1 - 1) /\ [M_]_s = M `32_ 0 /\
  [t]_s = ((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32 /\
  u2Z ([s_]_s `|| [t]_s) = u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\
  store.utoZ s = u2Z [t]_s * u2Z [alpha]_s).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [r_X_ [r_Y_ [r_Z_ [Hm1 [Hm2 [r_M_  [r_t Hconcat]]]]]]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd.
do 6 (split; trivial).
split.
by Assert_upd.
do 8 (split; trivial).
split; first by rewrite store.utoZ_multu; exact: max_u2Z_umul.
do 3 (split; trivial).
by rewrite store.utoZ_multu -u2Z_umul.

(** addiu int_ r0 one16; *)

apply hoare_addiu with (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\ [Y_]_s = X `32_ 0 /\
  [Z_]_s = Z `32_ 0 /\ store.utoZ s <= (\B^1 - 1) * (\B^1 - 1) /\ [M_]_s = M `32_ 0 /\
  [t]_s = ((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32 /\
  u2Z ([s_]_s `|| [t]_s) = u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\
  store.utoZ s = u2Z [t]_s * u2Z [alpha]_s /\ [int_]_s = one32).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [ r_X_ [r_Y_ [r_Z_ [Hm1 [r_M_ [r_t [Hconcat Hm2]]]]]]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite add0i sext_Z2u.

(** mflo quot; *)

apply hoare_mflo with (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{next} X * \S_{nk} X + K * \S_{nk} M /\
    \S_{next} X * \S_{nk} X + K * \S_{nk} M < 2 * \S_{nk} M * \B^next) /\ (next < nk)%nat /\
  [X_]_s = X `32_ next /\ [Y_]_s = X `32_ 0 /\ [Z_]_s = Z `32_ 0 /\
  store.utoZ s <= (\B^1 - 1) * (\B^1 - 1) /\ [M_]_s = M `32_ 0 /\
  [t]_s = ((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32 /\
  u2Z ([s_]_s `|| [t]_s) = u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\
  store.utoZ s = u2Z [t]_s * u2Z [alpha]_s /\ [int_]_s = one32 /\
  [quot]_s = (((X `32_ next `* X `32_ 0) `+ (zext 32 (Z `32_ 0)) `% 32) `* [alpha]_s) `% 32).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [ r_X_ [r_Y_ [ r_Z_ [Hm1 [r_M_ [r_t [Hconcat [Hm2 Hgrpint_]]]]]]]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

apply store.lo_remainder.
- by rewrite -addnA leq_addl.
- by rewrite Hm2 r_t -u2Z_umul.

(** mthi s; *)

apply hoare_mthi with (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M  /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next) /\ (next < nk)%nat /\
  [X_]_s = X `32_ next /\ [Y_]_s = X `32_ 0 /\ [Z_]_s = Z `32_ 0 /\
  store.utoZ s < \B^2 /\ [M_]_s = M `32_ 0 /\
  [t]_s = ((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32 /\
  u2Z ([s_]_s `|| [t]_s) = u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\
  [int_]_s = one32 /\
  [quot]_s = ((((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32) `* [alpha]_s) `% 32 /\
  store.hi s = [s_]_s).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [r_X_ [r_Y_ [ r_Z_ [Hm1 [r_M_  [r_t [Hconcat [Hm2 [Hgrpint_ r_quot]]]]]]]]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite store.utoZ_def store.hi_mthi_op store.acx_mthi_op store.lo_mthi_op store.utoZ_acx_beta2; last first.
  rewrite Hm2.
  apply (@leZ_ltZ_trans ((\B^1 - 1) * (\B^1 - 1))); last by [].
  rewrite -u2Z_umul; exact: max_u2Z_umul.
rewrite Z2uK // addZ0.
apply (@leZ_ltZ_trans ((\B^1 - 1) + (\B^1 - 1) * \B^1)); last by [].
apply leZ_add.
apply Zle_minus_1; exact: max_u2Z.
apply leZ_wpmul2r => //.
apply Zle_minus_1; exact: max_u2Z.
exact: store.hi_mthi_op.

(** mtlo t; *)

apply hoare_mtlo with  (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\ [Y_]_s = X `32_ 0 /\
  [Z_]_s = Z `32_ 0 /\ store.utoZ s < \B^2 /\ [M_]_s = M `32_ 0 /\
  [t]_s = ((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32 /\
  u2Z ([s_]_s `|| [t]_s) = u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\
  [int_]_s = one32 /\
  [quot]_s = ((((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32) `* [alpha]_s) `% 32 /\
  store.hi s = [s_]_s /\ store.lo s = [t]_s).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [ r_X_ [r_Y_ [r_Z_ [Hm1 [r_M_  [r_t [ Hconcat [Hgrpint_ [r_quot Hm2]]]]]]]]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

rewrite store.utoZ_def store.acx_mtlo_op store.lo_mtlo_op store.hi_mtlo_op store.utoZ_acx_beta2 // Z2uK //= addZ0.
apply (@leZ_ltZ_trans ((\B^1 - 1) + (\B^1 - 1) * \B^1)); last by [].
apply leZ_add.
apply Zle_minus_1; exact: max_u2Z.
apply leZ_wpmul2r => //.
apply Zle_minus_1; exact: max_u2Z.
rewrite -Hm2.
exact: store.hi_mtlo_op.
exact: store.lo_mtlo_op.

(** maddu quot M; *)

apply hoare_maddu with (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ u2Z [ext]_s < u2Z [k]_s /\ [one]_s = one32 /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M  /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\
  [Y_]_s = X `32_ 0 /\ [Z_]_s = Z `32_ 0 /\
  [M_]_s = M `32_ 0 /\ [int_]_s = one32 /\
  [quot]_s = ((((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32) `* [alpha]_s) `% 32 /\
  store.utoZ s = u2Z [quot]_s * u2Z (M `32_ 0) +
  u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\ store.lo s = zero32).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [r_X_ [r_Y_ [r_Z_ [Hm1 [r_M_  [r_t [Hconcat [Hgrpint_ [r_quot [Hm2 Hm3]]]]]]]]]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite store.utoZ_maddu.
rewrite r_M_ -u2Z_umul store.utoZ_def store.utoZ_acx_beta2 // Z2uK.
by rewrite Hm2 Hm3 (addZC (u2Z [t]_s)) -u2Z_concat Hconcat mul0Z addZ0 addZA.
split; [exact: leZZ | exact: expZ_gt0].
exact: (@ltZ_leZ_trans (\B^2 * 1)).

rewrite r_quot; apply montgomery_lemma => //.
by rewrite r_M_ r_alpha.
rewrite store.utoZ_def store.utoZ_acx_beta2 // Z2uK.
rewrite mul0Z addZ0 addZC -u2Z_concat Hm2 Hm3 Hconcat -u2Z_umul u2Z_add.
rewrite (@u2Z_zext 32) // u2Z_zext.
apply (@leZ_ltZ_trans ((\B^1 - 1) * (\B^1 - 1) + (\B^1 - 1))); last by [].
apply leZ_add; first exact: (@max_u2Z_umul 32).
rewrite (@u2Z_zext 32) //; apply Zle_minus_1; exact: max_u2Z.
by split; [exact: leZZ | exact: expZ_gt0].

(** mflhxu Z_; *)

apply hoare_mflhxu with (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\ u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\ (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\
  [Y_]_s = X `32_ 0 /\ [M_]_s = M `32_ 0 /\ [int_]_s = one32 /\
  [quot]_s = ((((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32) `* [alpha]_s) `% 32 /\
  \B^1 * u2Z (store.hi s `|| store.lo s) =
  u2Z ([quot]_s) * u2Z (M `32_ 0) + u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\
  store.utoZ s < 2 * \B^1 - 2).

move=> s h [Z [next [HZ [r_x [r_z [r_m [r_k [r_alpha [Hmem [r_ext [Hextk' [Hone [Hinv [Hextk [ r_X_ [r_Y_ [r_Z_ [r_M_ [r_int_ [Hquot [Hm2 Hm3]]]]]]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

rewrite u2Z_concat store.hi_mflhxu_op store.lo_mflhxu_op -Hm2 store.utoZ_def.
have -> : \B^2 = \B^1 * \B^1 by rewrite -ZbetaD.
rewrite u2Z_zext Hm3 Z2uK // -Zbeta1E.
repeat Reg_upd; ring.

apply store.mflhxu_kbeta1_utoZ.
apply (@leZ_ltZ_trans ((\B^1 - 1) * (\B^1 - 1) + (\B^1 - 1) * (\B^1 - 1) + (\B^1 - 1))); last by [].
rewrite store.utoZ_upd Hm2; apply leZ_add.
apply leZ_add; rewrite -u2Z_umul; exact: max_u2Z_umul.
exact/Zle_minus_1/max_u2Z.

(** addiu t z zero16; *)

apply hoare_addiu with  (fun s h => exists Z next, size Z = nk /\ [x]_s = vx /\
  [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\ u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\ (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\
  (exists K, \B^next * \S_{nk.+1} (Z ++ [C]_s :: nil) = \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M  /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next) /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\
  [Y_]_s = X `32_ 0 /\ [M_]_s = M `32_ 0 /\ [int_]_s = one32 /\
  [quot]_s = ((((X `32_ next `* X `32_ 0) `+ zext 32 (Z `32_ 0)) `% 32) `* [alpha]_s) `% 32 /\
  \B^1 * u2Z (store.hi s `|| store.lo s) =
  u2Z [quot]_s * u2Z (M `32_ 0) + u2Z (X `32_ next) * u2Z (X `32_ 0) + u2Z (Z `32_ 0) /\
  store.utoZ s < 2 * \B^1 - 2 /\ [t]_s = vz).

move=> s h [Z [next [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hinv [Hextk [r_X_ [r_Y_ [r_M_  [r_int_ [Hquot [Hm2 Hm3]]]]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

by rewrite sext_Z2u // addi0.

(** while (bne int_ k) *)

apply (hoare_prop_m.hoare_stren (fun s h => exists Z next nint_, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (next < nk)%nat /\ [X_]_s = X `32_ next /\
  u2Z [int_]_s = Z_of_nat nint_ /\ (1 <= nint_)%nat /\ u2Z [int_]_s <= u2Z [k]_s /\
  store.utoZ s < 2 * \B^1 - 1 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nint_ - 1) /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-1 (Z ++ [C]_s :: nil) +
    u2Z (store.hi s `|| store.lo s) * \B^(next + nint_) =
    \S_{ next } X * \S_{ nk } X + \S_{ nint_ } X * u2Z (X `32_ next) * \B^next +
    \S_{ nint_ } M * u2Z [quot]_s * \B^next + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next))).

move=> s h [Z [next [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hinv [Hextk [r_X_ [r_Y_ [r_M_  [r_int_ [Hquot [Hm2 [Hm3 r_t]]]]]]]]]]]]]]]]]]]].

exists Z, next, 1%nat.
repeat (split; trivial).

by rewrite r_int_ Z2uK.
rewrite r_int_ r_k Z2uK // (_ : 1 = Z_of_nat 1) //.
by apply/inj_le/leP; apply: leq_ltn_trans Hextk.
exact: (@ltZ_leZ_trans (2 * \B^1 - 2)).
rewrite r_t; ring.

case: Hinv => K [Hinv1 Hinv2].
exists K; split; last by [].
rewrite Sum_hole_last'; last by rewrite size_cat /= HZ addnC.
rewrite addn1.
have -> : u2Z (store.hi s `|| store.lo s) * \B^next.+1 =
  \B^next * (\B^1 * u2Z (store.hi s `|| store.lo s)) by rewrite -(addn1 next) ZbetaD; ring.
rewrite subn1.
have -> : \B^next.+1 * \S_{ nk } (List.tail (Z ++ [C]_s :: nil)) =
  \B^next * (\B^1 * \S_{ nk } (List.tail (Z ++ [C]_s :: nil))) by rewrite Zbeta_S; ring.
rewrite lSum_Zpower_Zmult Hquot.
apply trans_eq with (\B^next *
  (\S_{nk.+1} (zero32 :: List.tail (Z ++ [C]_s :: nil)) + u2Z (Z `32_ 0)) +
  \B^next * (u2Z [quot]_s * u2Z (M `32_ 0) + u2Z (X `32_ next) * u2Z (X `32_ 0))).
- rewrite Hm2.
  set tmp := \S_{ _ } _.
  ring.
- rewrite lSum_head_swap0 tail_app; last by rewrite HZ; destruct nk => //; apply lt_O_Sn.
  rewrite List.app_comm_cons.
  move: (@list_tail _ zero32 Z) => ->; last by rewrite HZ; destruct nk => //; apply lt_O_Sn.
  rewrite Hquot Hinv1 2!lSum_1 /zero32 /nth'; ring.

apply while.hoare_seq with (fun s h => (exists Z next nint_, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (next < nk)%nat /\ [X_]_s = X `32_ next /\
  u2Z [int_]_s = Z_of_nat nint_ /\ (1 <= nint_)%nat /\ u2Z [int_]_s <= u2Z [k]_s /\
  store.utoZ s < 2 * \B^1 - 1 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nint_ - 1) /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-1 (Z ++ [C]_s :: nil) +
    u2Z (store.hi s `|| store.lo s) * \B^(next + nint_) =
    \S_{ next } X * \S_{ nk } X + \S_{ nint_ } X * u2Z (X `32_ next) * \B^next +
    \S_{ nint_ } M * u2Z [quot]_s * \B^next + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next))
/\ ~~ (eval_b (bne int_ k) s)).

apply while.hoare_while.

(**  lwxs Y int_ y; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists Z next nint_, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
  [one]_s = one32 /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\ u2Z [ext]_s = Z_of_nat next /\
  (next < nk)%nat /\ (nint_ < nk)%nat /\ [X_]_s = X `32_ next /\
  u2Z [int_]_s = Z_of_nat nint_ /\ (1 <= nint_)%nat /\
  store.utoZ s < 2 * \B^1 - 1 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nint_ - 1) /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-1 (Z ++ [C]_s :: nil) +
    u2Z (store.hi s `|| store.lo s) * \B^(next + nint_) =
    \S_{ next } X * \S_{ nk } X + \S_{ nint_ } X * u2Z (X `32_ next) * \B^next +
    \S_{ nint_ } M * u2Z [quot]_s * \B^next + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next) /\
  [Y_]_s = X `32_ nint_).

move=> s h [[Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk'  [r_X_ [r_int_ [Hint_ [r_int_' [Hm2 [r_t Hinv]]]]]]]]]]]]]]]]]]] Hint_k].
rewrite /= in Hint_k. move/eqP in Hint_k; rewrite r_int_ r_k in Hint_k.
have {Hint_k}Hint_k : nint_ <> nk by contradict Hint_k; rewrite Hint_k.
have {r_int_'}r_int_' : (nint_ < nk)%nat.
  rewrite r_int_ r_k in r_int_'; move/Nat2Z.inj_le/leP in r_int_'.
  rewrite ltn_neqAle r_int_' andbT; exact/eqP.

exists (X `32_ nint_); split.
- Decompose_32 X nint_ X1 X2 HlenX1 HX'; last by rewrite Hx.
  rewrite HX' (decompose_equiv _ _ _ _ _ HlenX1) !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u r_int_ inj_mult mulZC.
- rewrite /update_store_lwxs.
  exists Z, next, nint_; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** lwxs Z int_ z; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists Z next nint_, size Z = nk /\
  [x]_s = vx /\  [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (next < nk)%nat /\ (nint_ < nk)%nat /\
  [X_]_s = X `32_ next /\ u2Z [int_]_s = Z_of_nat nint_ /\ (1 <= nint_)%nat /\
  store.utoZ s < 2 * \B^1 - 1 /\ u2Z [t]_s = u2Z [z]_s + 4 * (Z_of_nat nint_ - 1) /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-1 (Z ++ [C]_s :: nil) +
    u2Z (store.hi s `|| store.lo s) * \B^(next + nint_) =
    \S_{ next } X * \S_{ nk } X + \S_{ nint_ } X * u2Z (X `32_ next) * \B^next +
    \S_{ nint_ } M * u2Z [quot]_s * \B^next + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next) /\
  [Y_]_s = X `32_ nint_ /\ [Z_]_s = Z `32_ nint_).

move=> s h [Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [Hint_' [r_X_ [r_int_' [Hint_ [Hm2 [r_t [Hinv r_Y_]]]]]]]]]]]]]]]]]]]].

exists (Z `32_ nint_); split.
- Decompose_32 Z nint_ Z1 Z2 HlenZ1 HZ'; last by rewrite HZ.
  rewrite HZ' (decompose_equiv _ _ _ _ _ HlenZ1) !assert_m.conAE assert_m.conCE !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u r_int_' inj_mult mulZC.
- exists Z, next, nint_; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  by rewrite r_t r_z.

(** maddu X Y; *)

apply hoare_maddu with (fun s h => exists Z next nint_, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (next < nk)%nat /\ (nint_ < nk)%nat /\
  [X_]_s = X `32_ next /\ u2Z [int_]_s = Z_of_nat nint_ /\ (1 <= nint_)%nat /\
  store.utoZ s < \B^2 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nint_ - 1) /\
  [Y_]_s = X `32_ nint_ /\ [Z_]_s = Z `32_ nint_ /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-1 (Z ++ [C]_s :: nil) +
    store.utoZ s * \B^(next + nint_) = \S_{ next } X * \S_{ nk } X +
    \S_{ nint_ } X * u2Z (X `32_ next) * \B^next +
    \S_{ nint_ } M * u2Z [quot]_s * \B^next +
    u2Z (X `32_ next) * u2Z (X `32_ nint_) * \B^(next + nint_) + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next)).

move=> s h [Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [Hint_' [ r_X_ [r_int_' [Hint_ [Hm2 [r_t [Hinv [r_Y_ r_Z_]]]]]]]]]]]]]]]]]]]]].

exists Z, next, nint_.

have Htmp : store.utoZ s < \B^2 * (2 ^^ store.acx_size - 1) by exact: (@ltZ_leZ_trans (2 * \B^1 - 1)).

repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite store.utoZ_maddu //.
apply (@ltZ_leZ_trans ((\B^1 - 1) * (\B^1 - 1) + (2 * \B^1 - 1))); last by [].
apply leZ_lt_add; by [exact: max_u2Z_umul | ].
by rewrite r_t r_z.

case: Hinv => K [Hinv1 Hinv2].
exists K; split; last by []. (* about X * Y < M *)
apply trans_eq with (\S_{ next } X * \S_{ nk } X +
 \S_{ nint_ } X * u2Z (X `32_ next) * \B^next + \S_{ nint_ } M * u2Z [quot]_s * \B^next +
 K * \S_{ nk } M + u2Z (X `32_ next) * u2Z (X `32_ nint_) * \B^(next + nint_)).
- rewrite store.utoZ_maddu // store.utoZ_def store.utoZ_acx_beta2 //; last first.
    exact: (@ltZ_leZ_trans (2 * \B^1 - 1)).
  rewrite Z2uK // -u2Z_umul -Hinv1 u2Z_concat addZ0 r_Y_ r_X_ // -addZA.
  f_equal.
  rewrite (addZC (u2Z (X `32_ next `* X `32_ nint_))) mulZDl mulZDl.
  f_equal.
  by rewrite mulZDl addZC.
- ring.

(** lwxs M int_ m; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists Z next nint_, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s =  Z_of_nat next /\ (next < nk)%nat /\ (nint_ < nk)%nat /\
  [X_]_s = X `32_ next /\ u2Z [int_]_s =  Z_of_nat nint_ /\ (1 <= nint_)%nat /\
  store.utoZ s < \B^2 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nint_ - 1) /\
  [Y_]_s = X `32_ nint_ /\ [Z_]_s = Z `32_ nint_ /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-1 (Z ++ [C]_s :: nil) +
    store.utoZ s * \B^(next + nint_) = \S_{ next } X * \S_{ nk } X +
    \S_{ nint_ } X * u2Z (X `32_ next) * \B^next +
    \S_{ nint_ } M * u2Z [quot]_s * \B^next +
    u2Z (X `32_ next) * u2Z (X `32_ nint_) * \B^(next + nint_) + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next)
  /\ [M_]_s = M `32_ nint_ ).

move=> s h [Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [Hint_' [r_X_ [r_int_' [Hint_ [Hm2 [r_t [r_Y_ [r_Z_ Hinv]]]]]]]]]]]]]]]]]]]]].

exists (M `32_ nint_); split.
- Decompose_32 M nint_ M1 M2 HlenM1 HM'; last by rewrite Hm.
  rewrite HM' (decompose_equiv _ _ _ _ _ HlenM1) in Hmem.
  do 3 rewrite assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u r_int_' inj_mult mulZC.
- exists Z, next, nint_; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** maddu Z_ one; *)

apply hoare_maddu with (fun s h => exists Z next nint_, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (next < nk)%nat /\ (nint_ < nk)%nat /\
  [X_]_s = X `32_ next /\ u2Z [int_]_s = Z_of_nat nint_ /\ (1 <= nint_)%nat /\
  store.utoZ s < \B^2 + \B^1 - 1 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nint_ - 1) /\
  [Y_]_s = X `32_ nint_ /\ [Z_]_s = Z `32_ nint_ /\ [M_]_s = M `32_ nint_ /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-1 (Z ++ [C]_s :: nil) +
    store.utoZ s * \B^(next + nint_) = \S_{ next } X * \S_{ nk } X +
    \S_{ nint_ } X * u2Z (X `32_ next) * \B^next +
    \S_{ nint_ } M * u2Z [quot]_s * \B^next +
    u2Z (X `32_ next) * u2Z (X `32_ nint_) * \B^(next + nint_) +
    u2Z (Z `32_ nint_) * \B^(next + nint_) + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next)).

move=> s h [Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [ Hint_' [r_X_ [r_int_' [Hint_ [Hm2 [r_t [r_Y_ [r_Z_ [Hinv r_M_]]]]]]]]]]]]]]]]]]]]]].

exists Z, next, nint_.

have Htmp : store.utoZ s < \B^2 * (2 ^^ store.acx_size - 1).
  exact: (@ltZ_leZ_trans (\B^2 * 1)).

repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite store.utoZ_maddu //.
apply (@ltZ_leZ_trans ((\B^1 - 1) + \B^2)); last by [].
apply leZ_lt_add; last by [].
rewrite Hone umul_1 (@u2Z_zext 32) //.
apply Zle_minus_1; exact/max_u2Z.

case: Hinv => K [Hinv1 Hinv2].
exists K; split; last by []. (* about X * Y < M *)
rewrite store.utoZ_maddu // Hone umul_1 (@u2Z_zext 32) //.
apply trans_eq with (\B^next.+1 * Sum_hole nk.+1 nint_.-1 (Z ++ [C]_s :: nil) +
     store.utoZ s * \B^(next + nint_) + u2Z (Z `32_ nint_) * \B^(next + nint_)).
by rewrite -r_Z_ {1}(addZC (u2Z [Z_]_s)) mulZDl addZA.
rewrite Hinv1; ring.

(** maddu quot M; *)

apply hoare_maddu with (fun s h => exists Z next nint_, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (next < nk)%nat /\ (nint_ < nk)%nat /\
  [X_]_s = X `32_ next /\ u2Z [int_]_s = Z_of_nat nint_ /\ (1 <= nint_)%nat /\
  store.utoZ s < 2 * \B^2 - \B^1 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nint_ - 1) /\
  [Y_]_s = X `32_ nint_ /\ [Z_]_s = Z `32_ nint_ /\ [M_]_s = M `32_ nint_ /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-1 (Z ++ [C]_s :: nil) +
    store.utoZ s * \B^(next + nint_) = \S_{ next } X * \S_{ nk } X +
    \S_{ nint_ } X * u2Z (X `32_ next) * \B^next +
    \S_{ nint_ } M * u2Z [quot]_s * \B^next +
    u2Z (X `32_ next) * u2Z (X `32_ nint_) * \B^(next + nint_) +
    u2Z (Z `32_ nint_) * \B^(next + nint_) +
    u2Z (M `32_ nint_) * u2Z [quot]_s * \B^(next + nint_) + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next)).

move=> s h [Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [Hint_' [r_X_ [r_int_' [Hint_ [Hm2 [r_t [r_Y_ [r_Z_ [r_M_ Hinv]]]]]]]]]]]]]]]]]]]]]].
exists Z, next, nint_.

have Htmp : store.utoZ s < \B^2 * (2 ^^ store.acx_size - 1) by exact: (@ltZ_leZ_trans (\B^2 + \B^1 - 1)).

repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
repeat (split; trivial).

rewrite store.utoZ_maddu //.
apply (@ltZ_leZ_trans ((\B^1 - 1) * (\B^1 - 1) + (\B^2 + \B^1 - 1))); last by [].
apply leZ_lt_add => //; exact: max_u2Z_umul.

case: Hinv => K [Hinv1 Hinv2].
exists K; split; last by []. (* about X * Y < M *)
rewrite store.utoZ_maddu // mulZDl.
apply trans_eq with (\B^next.+1 * Sum_hole nk.+1 nint_.-1 (Z ++ [C]_s :: nil) +
  store.utoZ s * \B^(next + nint_) + (u2Z ([quot]_s `* [M_]_s) * \B^(next + nint_))).
by rewrite (addZC (u2Z ([quot]_s `* [M_]_s) * \B^(next + nint_))) addZA.
rewrite Hinv1 u2Z_umul r_M_; ring.

(** addiu int_ int_ one16; *)

apply hoare_addiu with (fun s h => exists Z next nint_, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (next < nk)%nat /\ (nint_ <= nk)%nat /\
  [X_]_s = X `32_ next /\ u2Z [int_]_s = Z_of_nat nint_ /\ (2 <= nint_)%nat /\
  store.utoZ s < 2 * \B^2 - \B^1  /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nint_ - 2) /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-2 (Z ++ [C]_s :: nil) +
    store.utoZ s * \B^((next + nint_).-1) = \S_{ next } X * \S_{ nk } X +
    \S_{nint_.-1} X * u2Z (X `32_ next) * \B^next +
    \S_{nint_.-1} M * u2Z [quot]_s * \B^next +
    u2Z (X `32_ next) * u2Z (X `32_ nint_.-1)  * \B^((next + nint_).-1)+
    u2Z (Z `32_ nint_.-1) * \B^((next + nint_).-1) +
    u2Z (M `32_ nint_.-1) * u2Z [quot]_s * \B^((next + nint_).-1) + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next)).

move=> s h [Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk'  [Hint_' [r_X_ [r_int_' [Hint_ [Hm2 [r_t [r_Y_ [r_Z_ [r_M_ Hinv]]]]]]]]]]]]]]]]]]]]]].

exists Z, next, nint_.+1; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

rewrite sext_Z2u // u2Z_add_Z2u //.
- by rewrite r_int_' Z_S.
- rewrite r_int_'.
  apply (@leZ_ltZ_trans (Z_of_nat nk)).
  rewrite (_ : 1 = Z_of_nat 1) //. by omegaz' ssromega. (*-inj_plus plus_comm; exact/inj_le/leP.*)
  apply: leZ_ltZ_trans; last exact/Hnz.
  apply Zle_plus_trans; first exact: min_u2Z.
  rewrite mulZC; apply Zle_scale; last by [].
  exact/Zle_0_nat.

rewrite r_t Z_S; ring.

case: Hinv => K [Hinv1 Hinv2].
exists K; split; last by []. (* about X * Y < M *)
by rewrite addnS /= Hinv1.

(** mflhxu Z_; *)

apply hoare_mflhxu with (fun s h => exists Z next nint_, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
  [one]_s = one32 /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\ u2Z [ext]_s = Z_of_nat next /\
  (next < nk)%nat /\ (nint_ <= nk)%nat /\ [X_]_s = X `32_ next /\
  u2Z [int_]_s = Z_of_nat nint_ /\ (2 <= nint_)%nat /\
  store.utoZ s < 2 * \B^1 - 1 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nint_ - 2) /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-2 (Z ++ [C]_s :: nil) +
    u2Z (store.hi s `|| store.lo s) * \B^(next + nint_) +
    u2Z [Z_]_s * \B^((next + nint_).-1) = \S_{ next } X * \S_{ nk } X +
    \S_{nint_.-1} X * u2Z (X `32_ next) * \B^next +
    \S_{nint_.-1} M * u2Z [quot]_s * \B^next +
    u2Z (X `32_ next) * u2Z (X `32_ nint_.-1)  * \B^((next + nint_).-1) +
    u2Z (Z `32_ nint_.-1) * \B^((next + nint_).-1) +
    u2Z (M `32_ nint_.-1) * u2Z [quot]_s * \B^((next + nint_).-1) + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next)).

move=> s h [Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [Hint_' [r_X_ [r_int_' [Hint_ [Hm2 [r_t Hinv]]]]]]]]]]]]]]]]]]].

exists Z, next, nint_; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

apply store.mflhxu_kbeta1_utoZ.
apply (@ltZ_leZ_trans (2 * \B^2 - \B^1)); by [rewrite store.utoZ_upd | ].
case: Hinv => K [Hinv1 Hinv2].
exists K; split; last by [].  (* about X * Y < M *)

rewrite -Hinv1 u2Z_concat store.hi_mflhxu_op store.lo_mflhxu_op u2Z_zext store.utoZ_def -addZA.
f_equal.
rewrite -Zbeta1E /= 3!mulZDl -3!mulZA -3!ZbetaD.
rewrite 2!add1n add2n prednK; last by rewrite addn_gt0 (ltn_trans _ Hint_) // orbT.
repeat Reg_upd; ring.

(** addiu t t four16; *)

apply hoare_addiu with (fun s h => exists Z next nint_, size Z = nk /\
  [x]_s = vx /\  [z]_s = vz /\ [m]_s = vm /\
  [one]_s = one32 /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (next < nk)%nat /\ (nint_ <= nk)%nat /\
  [X_]_s = X `32_ next /\ u2Z [int_]_s = Z_of_nat nint_ /\ (2 <= nint_)%nat /\
  store.utoZ s < 2 * \B^1 - 1 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nint_-1) /\
  (exists K, \B^next.+1 * Sum_hole nk.+1 nint_.-2 (Z ++ [C]_s :: nil) +
    u2Z (store.hi s `|| store.lo s) * \B^(next + nint_) +
    u2Z [Z_]_s * \B^((next + nint_).-1) = \S_{ next } X * \S_{ nk } X +
    \S_{nint_.-1} X * u2Z (X `32_ next) * \B^next +
    \S_{nint_.-1} M * u2Z [quot]_s * \B^next +
    u2Z (X `32_ next) * u2Z (X `32_ nint_.-1)  * \B^((next + nint_).-1) +
    u2Z (Z `32_ nint_.-1) * \B^((next + nint_).-1) +
    u2Z (M `32_ nint_.-1) * u2Z [quot]_s * \B^((next + nint_).-1) + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next)).

move=> s h [Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [Hint_' [r_X_ [r_int_' [Hint_ [Hm2 [r_t Hinv]]]]]]]]]]]]]]]]]]].

exists Z, next, nint_; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite sext_Z2u // u2Z_add_Z2u //.
- rewrite r_t; ring.
- rewrite r_t -Zbeta1E.
  apply: (leZ_ltZ_trans _ Hnz).
  rewrite -addZA; apply leZ_add2l.
  rewrite -{2}(mulZ1 4) -mulZDr; apply leZ_wpmul2l => //.
  rewrite -addZA; apply Zle_plus_trans_L => //; exact/inj_le/leP.

(** sw Z_ mfour16 t *)

apply hoare_sw_back'.
move=> s h [Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [Hint_' [r_X_ [r_int_' [Hint_ [Hm2 [r_t Hinv]]]]]]]]]]]]]]]]]]].

exists (int_e (Z `32_ nint_.-2)).

have Htmp: [z]_s `+ Z2u 32 (Z_of_nat (4 * nint_.-2)) = [t]_s `+ sext 16 mfour16.
  rewrite /mfour16 sext_Z2s // r_z; apply u2Z_inj.
  rewrite u2Z_add_Z2s //.
  rewrite u2Z_add_Z_of_nat.
  rewrite r_t -subn2 inj_mult inj_minus1; last exact/leP.
  ring.
  rewrite inj_mult -subn2 inj_minus1 //; last exact/leP.
  rewrite -Zbeta1E [Z_of_nat _]/=.
  apply: (leZ_ltZ_trans _ Hnz).
  apply/leZ_add2l/leZ_wpmul2l; first by [].
  rewrite -inj_minus1 //; last exact/leP.
  rewrite minusE.
  apply/inj_le/leP.
  by rewrite subn2 (leq_trans (leq_pred _ )) // (leq_trans _ Hint_') // leq_pred.
  rewrite r_t -addZA (_ : -4 = 4 * ( -1 )) // -mulZDr.
  apply Zle_plus_trans; first exact: min_u2Z.
  rewrite mulZC; apply mulZ_ge0 => //.
  rewrite -addZA /= (_ : -2 = - Z_of_nat 2) //.
  exact/Zle_left/inj_le/leP.

Decompose_32 Z (nint_.-2) Z1 Z2 HlenZ1 HZ'; last first.
  rewrite HZ.
  ssromega.
rewrite HZ' (decompose_equiv _ _ _ _ _ HlenZ1) !assert_m.conAE assert_m.conCE !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // ht.
exact: mapsto_ext.

apply currying => h' H'; simpl app in H'.

exists (upd_nth Z nint_.-2 [Z_]_s), next, nint_; repeat (split; trivial).
exact: size_upd_nth.
rewrite HZ' upd_nth_cat HlenZ1 // subnn /= (decompose_equiv _ _ _ _ _ HlenZ1).
rewrite cat0s in H'.
assoc_comm H'.
move: H'; exact: mapsto_ext.
by rewrite (ltn_trans _ Hint_).
rewrite r_int_' r_k; exact/inj_le/leP.
case: Hinv => K [Hinv1 Hinv2].
exists K; split; last by []. (* about X * Y < M *)

(* technicalities:

   at this point, we have an hypothesis about K with
   ( z_0 ... z_{nint-2} ... z_{k-1} ++ C::nil )\{nint-2}

   whereas in the goal, we have
   ( z_0 ...     Z      ... z_{k-1} ++ C::nil )\{nint-1}

   we will:
   1. coax the hypothesis and the goal to have the same Sum_hole predicate
      1.a. add z_{nint-1} to the goal
      1.b. use the Sum_hole_shift property to change the Sum_hole predicate in the goal
   2. check that the goal can be obtained from the hypo by rewriting
 *)

(* 1. *)

(* 1.a. *)

apply (eqZ_add2l (\B^next.+1 * u2Z (Z `32_ nint_.-1) * \B^nint_.-2)).
rewrite addZA -mulZA -(mulZDr (\B^next.+1)).

(* 1.b. *)

rewrite (addZC (u2Z (Z `32_ nint_.-1) * \B^nint_.-2)).
have -> : Sum_hole nk.+1 nint_.-1 (upd_nth Z nint_.-2 [Z_]_s ++ [C]_s :: nil) +
    u2Z (Z `32_ nint_.-1) * \B^nint_.-2 =
    Sum_hole nk.+1 nint_.-2 (Z ++ [C]_s :: nil) + u2Z [Z_]_s * \B^nint_.-2.
  have H_ : size (upd_nth Z nint_.-2 [Z_]_s ++ [C]_s :: nil) = nk.+1.
    by rewrite size_cat (@size_upd_nth _ nk) // addn1.
  have H1__ : (nint_.-1 < nk)%nat by rewrite prednK // (ltn_trans _ Hint_).
  have H1_ : (nint_.-1 < nk.+1)%nat by apply ltnW.
  have H1___ : (nint_.-2 < nk)%nat by rewrite prednK // -ltnS // prednK // (ltn_trans _ Hint_).
  move/(Sum_hole_shift _ _ H_ _) : H1_ => {H_}H_.
  do 2 rewrite nth_cat (@size_upd_nth _ nk) // in H_.
  rewrite H1__ subn1 H1___ nth_upd_nth' in H_; last first.
    destruct nint_; first by [].
    destruct nint_; first by [].
    destruct nint_ as [|nint_]; first by [].
    apply/eqP; by rewrite neq_ltn /= ltnSn orbT.
  rewrite nth_upd_nth in H_; last by rewrite HZ.
  have -> : Sum_hole nk.+1 nint_.-2 (Z ++ [C]_s :: nil) =
                Sum_hole nk.+1 nint_.-2 (upd_nth Z nint_.-2 [Z_]_s ++ [C]_s :: nil).
  rewrite -upd_nth_cat'; last by rewrite HZ.
  rewrite -Sum_hole_upd_nth //.
  by rewrite size_cat addn1 /= HZ.
  by rewrite mulnC in H_.

(* 2. *)

have Htmp2 : (next.+1 + nint_.-2 = (next + nint_).-1)%nat.
  rewrite addSnnS prednK //; last by rewrite -ltnS // prednK // (ltn_trans _ Hint_).
  rewrite -[RHS]subn1 -addnBA //; last by rewrite (ltn_trans _ Hint_).
  by rewrite subn1.

apply trans_eq with (\B^next.+1 * Sum_hole nk.+1 nint_.-2 (Z ++ [C]_s :: nil) +
 u2Z (store.hi s `|| store.lo s) * \B^(next + nint_) +
  u2Z [Z_]_s * (\B^next.+1 * \B^nint_.-2)).
ring.

rewrite -ZbetaD Htmp2 {}Hinv1.

apply trans_eq with ((\S_{nint_.-1} X * u2Z (X `32_ next) * \B^next +
  u2Z (X `32_ next) * u2Z (X `32_ nint_.-1) * \B^((next + nint_).-1)) +
(\S_{nint_.-1} M * u2Z [quot]_s * \B^next +
  u2Z (M `32_ nint_.-1) * u2Z [quot]_s * \B^((next + nint_).-1))
+ K * \S_{ nk } M + \S_{ next } X * \S_{ nk } X
+ u2Z (Z `32_ nint_.-1) * \B^((next + nint_).-1)).
ring.

apply trans_eq with (\S_{ nint_ } X * u2Z (X `32_ next) * \B^next +
  \S_{ nint_ } M * u2Z [quot]_s * \B^next
  + K * \S_{ nk } M + \S_{ next } X * \S_{ nk } X
  + (u2Z (Z `32_ nint_.-1) * (\B^next.+1 * \B^nint_.-2)) ); last by ring.

f_equal; last by rewrite -ZbetaD Htmp2.

do 3 f_equal.
apply trans_eq with ((\S_{nint_.-1} X + u2Z (X `32_ nint_.-1) * \B^nint_.-1) * (u2Z (X `32_ next) * \B^next)).
- rewrite -(subn1 (next + nint_)) -addnBA; last exact: leq_trans Hint_.
  rewrite subn1 ZbetaD; ring.
- rewrite (mulZC _ (\B^nint_.-1)) {1}/Zbeta -lSum_remove_last.
- rewrite prednK //.
  by rewrite mulZA.
  exact: leq_trans Hint_.

apply trans_eq with ((\S_{nint_.-1} M + u2Z (M `32_ nint_.-1) * \B^nint_.-1) * (u2Z [quot]_s * \B^next)).
- rewrite -(subn1 (next + nint_)) -addnBA; last exact: leq_trans Hint_.
  rewrite subn1 ZbetaD; ring.
- rewrite (mulZC _ (\B^nint_.-1)) -lSum_remove_last prednK //.
  by rewrite mulZA.
  exact: leq_trans Hint_.

(** maddu C one; *)

apply hoare_maddu with (fun s h => exists Z next, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (next < nk)%nat /\
  [X_]_s = X `32_ next /\ u2Z [int_]_s = Z_of_nat nk /\
  store.utoZ s < 3 * \B^1 - 2 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nk - 1) /\
  (exists K, \B^next.+1 * \S_{nk.-1} Z + store.utoZ s * \B^(next + nk) =
    \S_{ next } X * \S_{ nk } X + \S_{ nk } X * u2Z (X `32_ next) * \B^next +
    \S_{ nk } M * u2Z [quot]_s * \B^next + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next)).

move=> s h [[Z [next [nint_ [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [Hint_' [r_int_' [r_X_ [Hint_ [Hm2 [r_t Hinv]]]]]]]]]]]]]]]]]]] Hint_k].
rewrite /= r_int_' r_k in Hint_k.
move/negPn/eqP/Z_of_nat_inj in Hint_k; subst nint_.

exists Z, next.

have Htmp : store.utoZ s < \B^2 * (2 ^^ store.acx_size - 1) by apply (@ltZ_leZ_trans (2 * \B^1 - 1)).

repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite store.utoZ_maddu // Hone umul_1 (@u2Z_zext 32) //.
apply (@ltZ_leZ_trans ((\B^1 - 1) + (2 * \B^1 - 1))); last by [].
apply leZ_lt_add => //; exact/Zle_minus_1/max_u2Z.

case : Hinv => K [Hinv1 Hinv2].
exists K; split; last by []. (* about X * Y < M *)
rewrite -Hinv1 store.utoZ_maddu // Hone umul_1 (@u2Z_zext 32).
rewrite mulZDl addZA /Sum_hole // store.utoZ_def store.utoZ_acx_beta2; last by exact: (@ltZ_leZ_trans (2 * \B^1 - 1)).
rewrite Z2uK; last by split; [exact: leZZ | exact: expZ_gt0].
rewrite mul0Z addZ0 u2Z_concat.
have [Z' [tl H ] ] : exists Z' tl, Z = Z' ++ tl :: nil.
  clear -HZ r_X_.
  case/lastP : Z HZ r_X_ => /=; first by move=> <-.
  move=> h t _ _; by exists h, t; rewrite -cats1.
rewrite {2}H -catA.
have H0 : size Z' = nk.-1 by rewrite H size_cat /= addn1 in HZ; rewrite -HZ.
rewrite (@idel_app _ _ Z' H0 _ tl ([C]_s :: nil)) //.
move: (lSum_remove_last _ (Z' ++ [C]_s :: nil) nk.-1) => H1.
rewrite -(@lSum_beyond _ nk.-1) in H1; last by [].
rewrite nth_cat H0 ltnn subnn [nth _ _ _]/= in H1.
rewrite prednK // in H1.
rewrite subn1.
rewrite H1 (mulZDr (\B^next.+1)).
have <- : \S_{nk.-1} Z = \S_{nk.-1} Z' by rewrite H -lSum_beyond.
rewrite -ZbetaE mulZA -ZbetaD.
rewrite addSnnS prednK //.
by rewrite (mulZC (\B^(next + nk))) (addZC (u2Z (store.lo s))).

(** mflhxu Z_; *)

apply hoare_mflhxu with (fun s h => exists Z next, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
  [one]_s = one32 /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\ u2Z [ext]_s = Z_of_nat next /\
  (next < nk)%nat /\ [X_]_s = X `32_ next /\ store.utoZ s < 3  /\
  u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nk - 1) /\
  (exists K, \B^next.+1 * \S_{nk.-1} Z + u2Z (store.lo s) * \B^((next + nk).+1) +
    u2Z [Z_]_s * \B^(next + nk) = \S_{ next } X * \S_{ nk } X +
    \S_{ nk } X * u2Z (X `32_ next) * \B^next +
    \S_{ nk } M * u2Z [quot]_s * \B^next + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M < 2 * \S_{ nk } M * \B^next)).

move=> s h [Z [next [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [r_X_ [r_int_ [Hm2 [r_t Hinv]]]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
apply store.mflhxu_kbeta1_utoZ.
apply (@ltZ_trans (3 * \B^1 - 2)); by [rewrite store.utoZ_upd | ].
case: Hinv => K [Hinv1 Hinv2].
exists K; split; last by []. (* about X * Y < M *)
rewrite -Hinv1 store.lo_mflhxu_op store.utoZ_def store.utoZ_acx_beta2; last exact: (@ltZ_leZ_trans (3 * \B^1 -2)).
rewrite Z2uK; last by split; [exact: leZZ | exact: expZ_gt0].
rewrite mul0Z addZ0 mulZDl -mulZA -ZbetaD (addnC 1%nat).
rewrite addn1 -addnS; repeat Reg_upd; ring.

(** addiu ext ext one16; *)

apply hoare_addiu with (fun s h => exists Z next, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\ [one]_s = one32 /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (1 <= next <= nk)%nat /\
  store.utoZ s < 3 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nk - 1) /\
  (exists K, \B^next * \S_{nk.-1} Z + u2Z (store.lo s) * \B^(next + nk) +
    u2Z [Z_]_s * \B^((next + nk).-1) = \S_{next.-1} X * \S_{ nk } X +
    \S_{ nk } X * u2Z (X `32_ next.-1) * \B^(next-1) +
    \S_{ nk } M * u2Z [quot]_s * \B^next.-1 + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M + (\B^1 - 1) * (\B^next.-1 * \S_{ nk } M)
    < 2 * \S_{ nk } M * \B^next)).

move=> s h [Z [next [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [r_X_ [Hm2 [r_t Hinv]]]]]]]]]]]]]]].

exists Z, next.+1; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite sext_Z2u // u2Z_add_Z2u // r_ext.
by rewrite Z_S.
apply (@leZ_ltZ_trans (Z_of_nat nk)).
rewrite (_ : 1 = Z_of_nat 1) // -inj_plus plusE addn1; exact/inj_le/leP.
rewrite -r_k; exact: max_u2Z.

case: Hinv => K [Hinv1 Hinv2].
exists K; split.
- by rewrite !subn1 -Hinv1 addSn.
- (* about X * Y < M *)
  rewrite lSum_remove_last mulZDl.
  apply (@ltZ_leZ_trans (2 * \S_{ nk } M * \B^next + u2Z (X `32_ next) * \B^next * \S_{ nk } X +
    (\B^1 - 1) * \B^next * \S_{ nk } M)).
  apply ltZ_le_add.
  rewrite -ZbetaE (mulZC (\B^next)) /zero32 addZC addZA;
    by apply ltZ_le_add; [rewrite addZC | apply leZZ].
  rewrite mulZA; exact/leZZ.
  apply (@leZ_trans (2 * \S_{ nk } M * \B^next + (\B^1 - 1) * \B^next * \S_{ nk } X +
    (\B^1 - 1) * \B^next * \S_{ nk } M)).
  apply leZ_add2r, leZ_add2l.
  rewrite -2!mulZA.
  apply leZ_wpmul2r.
  apply mulZ_ge0 => //; exact: min_lSum.
  apply Zle_minus_1; exact/max_u2Z.
  rewrite -addZA.
  apply (@leZ_trans (2 * \S_{ nk } M * \B^next +
    ((\B^1 - 1) * \B^next * \S_{ nk } M + (\B^1 - 1) * \B^next * \S_{ nk } M))).
    apply leZ_add2l, leZ_add2r, leZ_wpmul2l.
    apply mulZ_ge0; by [ | exact: Zbeta_0'].
  exact/ltZW.
  suff: 2 * \S_{ nk } M * \B^next + ((\B^1 - 1) * \B^next * \S_{ nk } M + (\B^1 - 1) * \B^next * \S_{ nk } M)
    = 2 * \S_{ nk } M * \B^next.+1 by move=> ->; apply leZZ.
  rewrite (Zbeta_S next); ring.

(** sw Z_ zero16 t; *)

apply hoare_sw_back'' with (fun s h => exists Z next, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
  [one]_s = one32 /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  u2Z [ext]_s = Z_of_nat next /\ (1 <= next <= nk)%nat /\
  store.utoZ s < 3 /\ u2Z [t]_s = u2Z vz + 4 * (Z_of_nat nk - 1) /\
  (exists K, \B^next * \S_{ nk } Z + u2Z (store.lo s) * \B^(next + nk) =
    \S_{next.-1} X * \S_{ nk } X + \S_{ nk } X * u2Z (X `32_ next.-1) * \B^(next-1) +
    \S_{ nk } M * u2Z [quot]_s * \B^(next-1) + K * \S_{ nk } M /\
    \S_{ next } X * \S_{ nk } X + K * \S_{ nk } M + (\B^1 - 1) * (\B^next.-1 * \S_{ nk } M) < 2 * \S_{ nk } M * \B^next)).

move=> s h [Z [next [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [Hm2 [r_t Hinv]]]]]]]]]]]]]].

have [lst1 [last H0 ] ] : exists Z' tl, Z = Z' ++ tl :: nil.
  clear -HZ Hextk'.
  case/lastP : Z HZ Hextk' => [<-|].
    rewrite leqn0; case/andP => H1 /eqP H2; by rewrite H2 in H1.
  move=> h t _ _; by exists h, t; rewrite cats1.
have Hlenlst1 : size lst1 = nk.-1 by rewrite -HZ H0 size_cat /= addn1.
have Htmp : [ var_e t \+ int_e (sext 16 zero16) ]e_ s = [ var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk.-1))) ]e_ s.
  rewrite /= sext_0 addi0; apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat.
  rewrite inj_mult -subn1 inj_minus1 //; last by destruct nk => //; exact/le_n_S/le_O_n.
  rewrite r_t r_z; simpl Z_of_nat; ring.
  rewrite inj_mult -subn1 inj_minus1 //; last by destruct nk => //; exact/le_n_S/le_O_n.
  rewrite r_z; simpl Z_of_nat.
  apply: leZ_ltZ_trans; last exact: Hnz.
  apply/leZ_add2l/leZ_wpmul2l; first by [].
  rewrite (_ : 1 = Z_of_nat 1) // -inj_minus1 //; last by ssromega.
  apply/inj_le/leP; by rewrite minusE subn1 leq_pred.

exists (int_e last).

rewrite H0 (decompose_equiv _ _ _ _ _ Hlenlst1) !assert_m.conAE assert_m.conCE !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // ht.
exact: mapsto_ext.
apply currying => h' H'; simpl assert_m.mapstos in H'.

exists (upd_nth Z nk.-1 [Z_]_s), next.

repeat (split; trivial).
exact: size_upd_nth.
rewrite H0 upd_nth_cat Hlenlst1 // subnn /= (decompose_equiv _ _ _ _ _ Hlenlst1).
simpl assert_m.mapstos.
assoc_comm H'.
exact: mapsto_ext H'.

case: Hinv => K [Hinv1 Hinv2].
exists K; split; last by []. (* about X * Y < M *)
rewrite (subn1 next).
rewrite (subn1 next) in Hinv1.
rewrite -Hinv1.
have -> : upd_nth Z nk.-1 [Z_]_s = lst1 ++ [Z_]_s :: nil.
  rewrite H0 upd_nth_cat /=.
  by rewrite Hlenlst1 subnn.
  by rewrite Hlenlst1.
rewrite (lSum_cut_last nk) //; last by rewrite size_cat /= -HZ H0 size_cat.
rewrite mulZDr mulZA -ZbetaD !subn1.
rewrite H0 -(lSum_beyond 32 nk.-1 lst1) //.
rewrite -(subn1 (next + nk)) -addnBA //.
rewrite subn1; ring.
rewrite (@leq_trans next) //.
by case/andP : Hextk'.
by case/andP : Hextk'.

(** mflhxu C *)

apply hoare_mflhxu'.

move=> s h [Z [next [HZ [r_x [r_z [r_m [Hone [r_k [r_alpha [Hmem [r_ext [Hextk' [Hm2 [r_t Hinv]]]]]]]]]]]]]].

exists Z, next; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

rewrite r_ext r_k.

apply/inj_le/leP; by case/andP: Hextk'.

rewrite -subn1 inj_minus1 //; destruct nk => //; exact/le_n_S/le_O_n.

case: Hinv => K [Hinv1 Hinv2].
exists (K + u2Z [quot]_s * \B^(next - 1)); split.
- rewrite lSum_cut_last; last by rewrite size_cat /= HZ addnC.
  rewrite !subn1 mulZDr mulZA -ZbetaD (mulZC (\B^(next + nk))) Hinv1.
  have <- : \S_{next.-1} X + u2Z (X `32_ next.-1) * \B^next.-1 = \S_{ next } X.
    rewrite -(mulZC (\B^next.-1)) /Zbeta -lSum_remove_last //.
    rewrite prednK //.
    by case/andP: Hextk'.
  rewrite subn1; ring.
(* about X * Y < M *)
- apply (@leZ_ltZ_trans(\S_{ next } X * \S_{ nk } X + K * \S_{ nk } M + ((\B^1 - 1) * \B^next.-1 * \S_{ nk } M))); last by rewrite -mulZA.
  rewrite mulZDl addZA.
  apply/leZ_add2l/leZ_wpmul2r; first exact: min_lSum.
  rewrite subn1; apply leZ_wpmul2r => //.
  apply Zle_minus_1; exact: max_u2Z.
Qed.

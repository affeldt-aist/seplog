(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext uniq_tac machine_int.
Require Import multi_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_tactics mapstos.
Require Import multi_mul_u_u_prg.
Import expr_m.
Import assert_m.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope heap_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope multi_int_scope.

Lemma multi_mul_u_u_triple k one a b c z t i j l atmp btmp ctmp :
 uniq(k, one, a, b, c, z, t, i, j, l, atmp, btmp, ctmp, r0) ->
forall nk va vb vc, u2Z vc + 8 * Z_of_nat nk < \B^1 ->
forall A B, size A = nk -> size B = nk ->
{{ fun s h => [one]_s = one32 /\ [a]_s = va /\ [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
   (var_e a |--> A ** var_e b |--> B ** var_e c |--> nseq (nk + nk)%nat zero32) s h /\
   store.multi_null s }}
multi_mul_u_u k one a b c z t i j l atmp btmp ctmp
{{ fun s h => exists C, size C = (nk + nk)%nat /\
   (var_e c |--> C ** TT) s h /\ \S_{ nk + nk } C = \S_{ nk } A * \S_{ nk } B }}.
Proof.
move=> Hset nk va vb vc Hnc A B Ha Hb; rewrite /multi_mul_u_u.

(**  addiu i r0 zero16; *)

NextAddiu.
move=> s h [Hone [Hra [Hrb [Hrc [Hrk [Hmem Hm]]]]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.multi_null_upd.

(**  addiu t c zero16; *)

NextAddiu.
move=> s h [[Hone [Hra [Hrb [Hrc [Hrk [Hmem Hm]]]]]] Hri].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.multi_null_upd.

(**  while (bne i k) ( *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists C ni,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ (ni <= nk)%nat /\
  store.multi_null s /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  \S_{ ni + nk } C = \S_{ ni } A * \S_{ nk } B).

move=> s h [[[Hone [Hra [Hrb [Hrc [Hrk [Hmem Hm]]]]]] Hri] Hrt].
exists (nseq (nk + nk) zero32), O; repeat (split; trivial).
exact: size_nseq.
by rewrite Hri sext_Z2u // addi0 store.get_r0 Z2uK.
rewrite Hrt sext_Z2u // addi0 Hrc; ring.
by rewrite /zero32 lSum_nseq_0.

move=> s h [[C [ni [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hik [Hm [Hrt Hinv]]]]]]]]]]]]] Hik'];
  rewrite /= in Hik'. move/negPn/eqP in Hik'.
exists C; repeat (split; trivial).
apply con_Q_con_TT with (var_e a |--> A ** var_e b |--> B).
by assoc_comm Hmem.
have ? : ni = nk by lia.
by subst ni.

(**    addiu z t zero16;*)

apply hoare_addiu with (fun s h => exists C ni,
  size C = (nk+nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\
  store.multi_null s /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  \S_{ ni + nk } C = \S_{ ni } A * \S_{ nk } B /\ u2Z [z]_s = u2Z [t]_s).

move=> s h [[C [ni [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hik [Hm [Hrt Hinv]]]]]]]]]]]]] Hik'];
  rewrite /= in Hik'. move/eqP in Hik'.

exists C, ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
ssromega.
by rewrite store.multi_null_upd.
by rewrite sext_Z2u // addi0.

(**    lwxs atmp i a;*)

apply hoare_lwxs_back_alt'' with (fun s h => exists C ni,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\
  store.multi_null s /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  \S_{ ni + nk } C = \S_{ ni } A * \S_{ nk } B /\ u2Z [z]_s = u2Z [t]_s /\ [atmp]_s = A `32_ ni).

move=> s h [C [ni [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hik [Hm [Hrt [Hinv Hrz]]]]]]]]]]]]]].

exists (A `32_ ni); split.

Decompose_32 A ni A1 A2 HlenA1 HA'; last by ssromega.

rewrite HA' (decompose_equiv _ _ _ _ _ HlenA1) !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // h'.
apply mapsto_ext => //.
by rewrite /= shl_Z2u Hri inj_mult mulZC.

rewrite /update_store_lwxs.
exists C, ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.multi_null_upd.

(**    addiu j r0 zero16;*)

apply hoare_addiu with (fun s h => exists C ni,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\
  store.multi_null s /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  \S_{ ni + nk } C = \S_{ ni } A * \S_{ nk } B /\ u2Z [z]_s = u2Z [t]_s /\
  [atmp]_s = A `32_ ni /\ [j]_s = zero32).

move=> s h [C [ni [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hik [Hm [Hrt [Hinv [Hrz Hratmp]]]]]]]]]]]]]]].

exists C, ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.multi_null_upd.
by rewrite sext_Z2u // addi0.

apply hoare_prop_m.hoare_stren with (fun s h => exists C ni nj,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ u2Z [j]_s = Z_of_nat nj /\
  (ni < nk)%nat /\ (nj <= nk)%nat /\ store.utoZ s < \B^1 /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nj /\
  [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + u2Z (store.lo s) * \B^(ni + nj) =
  \S_{ ni } A * \S_{ nk } B + \S_{ nj } B * u2Z (A `32_ ni) * \B^ni).

move=> s h [C [ni [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hik [Hm [Hrt [Hinv [Hrz [Hratmp Hrj]]]]]]]]]]]]]]]].

exists C, ni, O; repeat (split; trivial).
by rewrite Hrj /zero32 Z2uK.
by rewrite store.multi_null_utoZ.
rewrite Hrz; ring.
by rewrite store.multi_null_lo // Z2uK // Hinv.

(**    while (bne j k) ( *)

apply while.hoare_seq with (fun s h => (exists C ni nj,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ u2Z [j]_s = Z_of_nat nj /\
  (ni < nk)%nat /\ (nj <= nk)%nat /\ store.utoZ s < \B^1 /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nj /\
  [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + u2Z (store.lo s) * \B^(ni + nj) =
  \S_{ ni } A * \S_{ nk } B + \S_{ nj } B * u2Z (A `32_ ni) * \B^ni)
/\ ~~ (eval_b (bne j k) s)).

apply while.hoare_while.

(**      lwxs btmp j b;*)

apply hoare_lwxs_back_alt'' with (fun s h => exists C ni nj,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ u2Z [j]_s = Z_of_nat nj /\
  (ni < nk)%nat /\ (nj < nk)%nat /\ store.utoZ s < \B^1 /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nj /\
  [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + u2Z (store.lo s) * \B^(ni + nj) =
  \S_{ ni } A * \S_{ nk } B + \S_{ nj } B * u2Z (A `32_ ni) * \B^ni /\
  [btmp]_s = B `32_ nj).

move=> s h [ [C [ni [nj [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hrj [Hik [Hjk [Hm [Hrt [Hrz [Hratmp Hinv]]]]]]]]]]]]]]]]]] Hjk'];
  rewrite /= in Hjk'. move/eqP in Hjk'.

exists (B `32_ nj); split.
- Decompose_32 B nj B1 B2 HlenB1 HB'; last by ssromega.
  rewrite HB' (decompose_equiv _ _ _ _ _ HlenB1) !assert_m.conAE assert_m.conCE
  !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u Hrj inj_mult mulZC.
- rewrite /update_store_lwxs.
  exists C, ni, nj; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  ssromega.

(**      maddu atmp btmp;*)

apply hoare_maddu with (fun s h => exists C ni nj,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ u2Z [j]_s = Z_of_nat nj /\ (ni < nk)%nat /\
  (nj < nk)%nat /\ store.utoZ s < \B^2 - \B^1 + 1  /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nj /\ [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + store.utoZ s * \B^(ni + nj) =
  \S_{ ni } A * \S_{ nk } B + \S_{ nj } B * u2Z (A `32_ ni) * \B^ni +
  u2Z (A `32_ ni) * u2Z (B `32_ nj) * \B^(ni + nj) /\
  [btmp]_s = B `32_ nj).

move=> s h [C [ni [nj [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hrj [Hik [Hjk [Hm [Hrt [Hrz [Hratmp [Hinv Hrtmp]]]]]]]]]]]]]]]]]]].

exists C, ni, nj.

have Htmp : store.utoZ s < \B^2 * (2 ^^ store.acx_size - 1).
  exact: (@ltZ_leZ_trans \B^1).
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

rewrite store.utoZ_maddu //.
apply (@ltZ_leZ_trans ((\B^1 - 1) * (\B^1 - 1) + \B^1)) => //.
apply leZ_lt_add => //; exact: max_u2Z_umul.

rewrite store.utoZ_maddu // Hrtmp Hratmp (@u2Z_umul 32) -Hinv (proj2 (proj2 (store.utoZ_lo_beta1 _ Hm))); ring.

(**      addu l i j;*)

apply hoare_addu with (fun s h => exists C ni nj,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ u2Z [j]_s = Z_of_nat nj /\ (ni < nk)%nat /\
  (nj < nk)%nat /\ store.utoZ s < \B^2 - \B^1 + 1 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nj /\ [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + store.utoZ s * \B^(ni + nj) =
  \S_{ ni } A * \S_{ nk } B + \S_{ nj } B * u2Z (A `32_ ni) * \B^ni +
  u2Z (A `32_ ni) * u2Z (B `32_ nj) * \B^(ni + nj) /\
  [btmp]_s = B `32_ nj /\ [l]_s = [i]_s `+ [j]_s).

move=> s h [C [ni [nj [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hrj [Hik [Hjk [Hm [Hrt [Hrz [Hratmp [Hinv Hrtmp]]]]]]]]]]]]]]]]]]].

exists C, ni, nj; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(**      lwxs ctmp l c;*)

apply hoare_lwxs_back_alt'' with (fun s h => exists C ni nj,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ u2Z [j]_s = Z_of_nat nj /\ (ni < nk)%nat /\
  (nj < nk)%nat /\ store.utoZ s < \B^2 - \B^1 + 1 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nj /\ [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + store.utoZ s * \B^(ni + nj) =
  \S_{ ni } A * \S_{ nk } B + \S_{ nj } B * u2Z (A `32_ ni) * \B^ni +
  u2Z (A `32_ ni) * u2Z (B `32_ nj) * \B^(ni + nj) /\
  [btmp]_s = B `32_ nj /\ [l]_s = [i]_s `+ [j]_s /\ [ctmp]_s = C `32_ (ni + nj)).

move=> s h [C [ni [nj [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hrj [Hik [Hjk [Hm [Hrt [Hrz [Hratmp [Hinv [ Hrtmp Hrl]]]]]]]]]]]]]]]]]]]].

exists (C `32_ (ni + nj)); split.
Decompose_32 C (ni + nj)%nat C1 C2 HlenC1 HC'; last by ssromega.

rewrite HC' (decompose_equiv _ _ _ _ _ HlenC1) in Hmem.
(* TODO *)
rewrite assert_m.conCE !assert_m.conAE in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // ht.
apply mapsto_ext => //.
rewrite /=.
suff : shl 2 [l]_s = Z2u 32 (Z_of_nat (4 * (ni+nj))) by move=> ->.
rewrite shl_Z2u Hrl.
have -> : u2Z ([i]_s `+ [j]_s) = Z_of_nat (ni + nj).
  rewrite u2Z_add; first by rewrite Hri Hrj inj_plus.
  rewrite Hri Hrj -Zbeta1E.
  move: (min_u2Z vc) => ?; ssromega.
by rewrite inj_mult mulZC.

exists C, ni, nj; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(**      maddu ctmp one;*)

apply hoare_maddu with (fun s h => exists C ni nj,
  size C = (nk+nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ u2Z [j]_s = Z_of_nat nj /\ (ni < nk)%nat /\
  (nj < nk)%nat /\ store.utoZ s < \B^2 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nj /\
  [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + store.utoZ s * \B^(ni + nj) =
  \S_{ ni } A * \S_{ nk } B + \S_{ nj } B * u2Z (A `32_ ni) * \B^ni +
  u2Z (A `32_ ni) * u2Z (B `32_ nj) * \B^(ni + nj) +
  u2Z (C `32_ (ni + nj)) * \B^(ni + nj) /\ [btmp]_s = B `32_ nj /\
  [l]_s = [i]_s `+ [j]_s /\ [ctmp]_s = C `32_ (ni + nj)).

move=> s h [C [ni [nj [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hrj [Hik [Hjk [Hm [Hrt [Hrz [Hratmp [Hinv [Hrtmp [Hrl Hrctmp]]]]]]]]]]]]]]]]]]]]].

exists C, ni, nj.
have ? : store.utoZ s < \B^2 * (2 ^^ store.acx_size - 1).
  exact: (@ltZ_leZ_trans (\B^2 - \B^1 + 1)).
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

rewrite store.utoZ_maddu // Hone umul_1 (@u2Z_zext 32).
apply (@ltZ_leZ_trans ((\B^1 - 1) + (\B^2 - \B^1 + 1))) => //.
apply leZ_lt_add => //; exact/leZsub1/max_u2Z.

rewrite store.utoZ_maddu // Hone umul_1 (@u2Z_zext 32) Hrctmp.
apply trans_eq with (\S_{ ni + nk } C + store.utoZ s * \B^(ni + nj)
  + u2Z (C `32_ (ni + nj)) * \B^(ni + nj)).
rewrite /=; ring.

rewrite Hinv; ring.

(**      mflhxu ctmp;*)

apply hoare_mflhxu with (fun s h => exists C ni nj,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ u2Z [j]_s = Z_of_nat nj /\
  (ni < nk)%nat /\ (nj < nk)%nat /\ store.utoZ s < \B^1 /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nj /\ [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + store.utoZ s * \B^(ni + nj).+1 + u2Z [ctmp]_s * \B^(ni + nj) =
  \S_{ ni } A * \S_{ nk } B + \S_{ nj } B * u2Z (A `32_ ni) * \B^ni +
  u2Z (A `32_ ni) * u2Z (B `32_ nj) * \B^(ni + nj) +
  u2Z (C `32_ (ni + nj)) * \B^(ni + nj) /\
  [btmp]_s = B `32_ nj /\ [l]_s = [i]_s `+ [j]_s ).

move=> s h [C [ni [nj [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hrj [Hik [Hjk [Hm [Hrt [Hrz [Hratmp [Hinv [Hrtmp [Hrl Hrctmp]]]]]]]]]]]]]]]]]]]]].

exists C, ni, nj; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

by apply store.mflhxu_beta2_utoZ; rewrite store.utoZ_upd.

rewrite (store.mflhxu_utoZ s) in Hinv.
apply trans_eq with (\S_{ ni + nk } C + (store.utoZ (store.mflhxu_op s) * \B^1 + u2Z (store.lo s)) * \B^(ni + nj)).
rewrite Zbeta_S ZbetaD store.mflhxu_upd store.utoZ_upd; ring.
rewrite Hinv; ring.

(**      sw ctmp zero16 z;*)

apply hoare_sw_back'' with (fun s h => exists C ni nj,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ u2Z [j]_s = Z_of_nat nj /\
  (ni < nk)%nat /\ (nj < nk)%nat /\ store.utoZ s < \B^1 /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nj /\ [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + store.utoZ s * \B^(ni + nj).+1 =
  \S_{ ni } A * \S_{ nk } B + \S_{ nj } B * u2Z (A `32_ ni) * \B^ni +
  u2Z (A `32_ ni) * u2Z (B `32_ nj) * \B^(ni + nj)  /\
  [btmp]_s = B `32_ nj /\ [l]_s = [i]_s `+ [j]_s).

move=> s h [C [ni [nj [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hrj [Hik [Hjk [Hm [Hrt [Hrz [Hratmp [Hinv [Hrtmp Hrl]]]]]]]]]]]]]]]]]]]].

have Htmp : [ var_e z \+ int_e (sext 16 zero16) ]e_ s = [ var_e c \+ int_e (Z2u 32 (Z_of_nat (4 * (ni + nj)))) ]e_ s.
  rewrite /= sext_Z2u // addi0.
  apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat //.
  rewrite Hrz Hrt Hrc inj_mult inj_plus; simpl Z_of_nat; ring.
  rewrite Hrc inj_mult inj_plus -Zbeta1E; simpl Z_of_nat; ssromega.

exists (int_e (C `32_ (ni + nj))).

Decompose_32 C (ni + nj)%nat C1 C2 HlenC1 HC'; last by ssromega.
rewrite HC' (decompose_equiv _ _ _ _ _ HlenC1) in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // ht.
exact: mapsto_ext.

apply currying => h' H'; simpl app in H'.

exists (upd_nth C (ni + nj) [ctmp]_s), ni, nj.
repeat (split; trivial).
exact: size_upd_nth.
rewrite HC' upd_nth_cat HlenC1 // subnn /= (decompose_equiv _ _ _ _ _ HlenC1).
rewrite cat0s in H'.
assoc_comm H'.
by apply: mapsto_ext H'.

have [l1 [l2 [H3 H2]]] : exists l1 l2, size l1 = (ni + nk)%nat /\ C = l1 ++ l2.
  apply app_split.
  by rewrite HlenC leq_add2r ltnW.
rewrite H2 upd_nth_cat'; last by rewrite H3 ltn_add2l.
rewrite -lSum_beyond; last exact: size_upd_nth.
rewrite H2 -lSum_beyond // in Hinv.
rewrite -lSum_upd_nth2 //; last by ssromega.
rewrite -(ZbetaE (ni + nj)).
apply trans_eq with
  ((\S_{ ni + nk } l1 + store.utoZ s * \B^(ni + nj).+1 + u2Z [ctmp]_s * \B^(ni + nj)) -
    u2Z (l1 `32_ (ni + nj)) * \B^(ni + nj)).
rewrite /zero32 /nth'; ring.
rewrite Hinv.
rewrite /nth' nth_cat.
rewrite (_ : (_ < _)%nat = true); last apply/ltP; by ssromega.

(**      addiu z z four16;*)

apply hoare_addiu with (fun s h => exists C ni nj,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ u2Z [j]_s = Z_of_nat nj /\ (ni < nk)%nat /\
  (nj < nk)%nat /\ store.utoZ s < \B^1 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\
  u2Z [z]_s = u2Z [t]_s + 4 * (Z_of_nat nj + 1) /\ [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + store.utoZ s * \B^(ni + nj).+1 =
  \S_{ ni } A * \S_{ nk } B + \S_{ nj } B * u2Z (A `32_ ni) * \B^ni +
  u2Z (A `32_ ni) * u2Z (B `32_ nj) * \B^(ni + nj) /\
  [btmp]_s = B `32_ nj /\ [l]_s = [i]_s `+ [j]_s).

move=> s h [C [ni [nj [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hrj [Hik [Hjk [Hm [Hrt [Hrz [Hratmp [Hinv [Hrtmp Hrl]]]]]]]]]]]]]]]]]]]].

exists C, ni, nj; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite sext_Z2u // u2Z_add_Z2u //.
- rewrite Hrz; ring.
- rewrite -Zbeta1E; ssromega.

(**      addiu j j one16); *)

apply hoare_addiu'.
move=> s h [C [ni [nj [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hrj [Hik [Hjk [Hm [Hrt [Hrz [Hratmp [Hinv [Hrtmp Hrl]]]]]]]]]]]]]]]]]]]].

exists C, ni, nj.+1.
rewrite Z_S.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

rewrite u2Z_add sext_Z2u // Z2uK // Hrj //.
rewrite -Zbeta1E.
move: (min_u2Z vc) => ?; ssromega.

rewrite -(proj2 (proj2 (store.utoZ_lo_beta1 _ Hm))) -addSnnS.
rewrite Hinv ZbetaD lSum_remove_last -ZbetaE -/zero32 -/(B `32_ nj); ring.

(**    mflhxu ctmp;*)

apply hoare_mflhxu with (fun s h => exists C ni,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\ store.multi_null s /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\ u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nk /\
  [atmp]_s = A `32_ ni /\
  \S_{ ni + nk } C + u2Z [ctmp]_s * \B^(ni + nk) =
  \S_{ ni } A * \S_{ nk } B + \S_{ nk } B * u2Z (A `32_ ni) * \B^ni).

move=> s h [[C [ni [nj [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hrj [Hik [Hjk [Hm [Hrt [Hrz [Hratmp Hinv]]]]]]]]]]]]]]]]]] Hjk'];
  rewrite /= in Hjk'. move/negPn/eqP in Hjk'.

have ? : nj = nk by lia. subst nj.

exists C, ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

apply store.utoZ_multi_null.
rewrite store.mflhxu_upd store.utoZ_upd.
have H : store.utoZ (store.mflhxu_op s) < 1 by apply store.mflhxu_kbeta1_utoZ.
move: (store.utoZ_pos (store.mflhxu_op s)) => ?; lia.

(**    sw ctmp zero16 z; *)

apply hoare_sw_back'' with (fun s h => exists C ni,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\ store.multi_null s /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat ni /\ u2Z [z]_s = u2Z [t]_s + 4 * Z_of_nat nk /\
  [atmp]_s = A `32_ ni /\
  \S_{(ni + nk).+1} C = \S_{ ni } A * \S_{ nk } B + \S_{ nk } B * u2Z (A `32_ ni) * \B^ni).

move=> s h [C [ni [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hik [Hm [Hrt [Hrz [Hratmp Hinv]]]]]]]]]]]]]]].

have Htmp : [ var_e z \+ int_e (sext 16 zero16) ]e_ s = [ var_e c \+ int_e (Z2u 32 (Z_of_nat (4 * (ni + nk)))) ]e_ s.
  rewrite /= sext_Z2u // addi0.
  apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat //.
  rewrite Hrz Hrt Hrc inj_mult inj_plus; simpl Z_of_nat; ring.
  rewrite Hrc inj_mult inj_plus -Zbeta1E; simpl Z_of_nat; ssromega.

exists (int_e (C `32_ (ni + nk))).

Decompose_32 C (ni + nk)%nat C1 C2 HlenC1 HC'; last by rewrite HlenC ltn_add2r.

rewrite HC' (decompose_equiv _ _ _ _ _ HlenC1) in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // ht.
exact: mapsto_ext.

apply currying => h' H'; simpl app in H'.
exists (upd_nth C (ni + nk) [ctmp]_s), ni.
repeat (split; trivial).
exact: size_upd_nth.
rewrite HC' upd_nth_cat HlenC1 // subnn /= (decompose_equiv _ _ _ _ _ HlenC1).
rewrite cat0s in H'.
assoc_comm H'.
by move: H'; apply mapsto_ext.

rewrite -Hinv {1}HC' -cat1s catA upd_nth_cat'; last by rewrite size_cat /= -(addnC 1%nat) HlenC1.
rewrite upd_nth_cat; last by rewrite HlenC1.
rewrite -lSum_beyond; last by rewrite size_cat HlenC1 subnn //= addnC.
rewrite Hinv HlenC1 subnn lSum_cut_last; last by rewrite size_cat /= HlenC1 addnC.
rewrite -Hinv HC' -lSum_beyond // subSS subn0 (ZbetaE (ni + nk)); ring.

(**    addiu t t four16; *)

apply hoare_addiu with (fun s h => exists C ni,
  size C = (nk + nk)%nat /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\ store.multi_null s /\
  u2Z [t]_s = u2Z vc + 4 * (Z_of_nat ni.+1) /\ [atmp]_s = A `32_ ni /\
  \S_{(ni + nk).+1} C = \S_{ ni } A * \S_{ nk } B + \S_{ nk } B * u2Z (A `32_ ni) * \B^ni).

move=> s h [C [ni [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hik [Hm [Hrt [Hrz [Hratmp Hinv]]]]]]]]]]]]]]].

exists C, ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.multi_null_upd.
rewrite sext_Z2u // u2Z_add_Z2u //.
rewrite Hrt Z_S; ring.
rewrite -Zbeta1E; ssromega.

(**    addiu i i one16). *)

apply hoare_addiu'.
move=> s h [C [ni [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hri [Hik [Hm [Hrt [Hratmp Hinv]]]]]]]]]]]]]].

exists C, ni.+1; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite sext_Z2u // u2Z_add_Z2u //.
- by rewrite Hri Z_S.
- rewrite -Zbeta1E; move: (min_u2Z vc) => ?; ssromega.
by rewrite store.multi_null_upd.
rewrite addSn Hinv lSum_remove_last -ZbetaE -/zero32 -/(A `32_ ni); ring.
Qed.

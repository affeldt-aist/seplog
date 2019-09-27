(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_tactics mips_contrib mapstos.
Require Import multi_add_u_u_prg.
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

Lemma multi_add_u_u_triple k one a b t j a0 :
  uniq(k, one, a, b, t, j, a0, r0) ->
  forall nk va vb, u2Z vb + 4 * Z_of_nat nk < \B^1 ->
  forall A B, size A = nk -> size B = nk ->
 {{ fun s h => [ one ]_s = one32 /\ [ a ]_s = va /\ [ b ]_s = vb /\
   u2Z [ k ]_s = Z_of_nat nk /\ (var_e a |--> A ** var_e b |--> B) s h }}
 multi_add_u_u k one a b b t j a0
 {{ fun s h => exists B', size B' = nk /\ [ a ]_s = va /\ [ b ]_s = vb /\
   (var_e a |--> A ** var_e b |--> B') s h /\ u2Z (store.lo s) <= 1 /\
   \S_{ nk } B' + u2Z (store.lo s) * \B^nk = \S_{ nk } A + \S_{ nk } B }}.
Proof.
move=> Hset nk va vb Hnb A B Ha Hb; rewrite /multi_add_u_u.

(** addiu j r0 zero16; *)

NextAddiu.
move=> s h [C [H [H2 [H1 H4]]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** addiu t c zero16; *)

NextAddiu.
move=> s h [[C [H0 [H3 [H2 H5]]]] H1].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** multu r0 r0 *)

apply hoare_multu with (fun s h => [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [j]_s = 0 /\ u2Z [t]_s = u2Z vb /\ store.multi_null s /\
  (var_e a |--> A ** var_e b |--> B) s h ).

move=> s h [[[H [r_a [r_b [r_k mem]]]] r_j] r_t].
rewrite /wp_multu.
repeat Reg_upd.
rewrite umul_0 /store.multi_null store.utoZ_multu Z2uK //.
repeat (split => //).
by rewrite r_j add0i sext_Z2u // Z2uK.
by rewrite r_t sext_Z2u // addi0 r_b.
by Assert_upd.

(** while (bne j k) *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists nj B',
  size B' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj <= nk)%nat /\
  store.utoZ s <= 1 /\ u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\
  \S_{ nj } B' + u2Z (store.lo s) * \B^nj = \S_{ nj } A + \S_{ nj } B /\
  drop nj B = drop nj B').

move=> s h [r_one [r_a [r_b [r_k [r_j [r_t [Hm mem]]]]]]].
exists O, B; repeat (split; trivial).
by rewrite store.multi_null_utoZ.
by rewrite /= addZ0.
by rewrite store.multi_null_lo //= Z2uK.

move=> s h [[nj [B' [H [H3 [H2 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 Hnth]]]]]]]]]]]]] H1];
  rewrite /= in H1. move/negPn/eqP in H1.
exists B'; repeat (split; trivial).
have : store.utoZ s < \B^1 by apply (@leZ_ltZ_trans 1).
by case/store.utoZ_lo_beta1=> _ [] _ <-.
suff : nk = nj by move=> ->.
rewrite H7 H5 in H1; exact/Z_of_nat_inj.

(** lwxs a0 j a; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists nj B',
  size B' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 1 /\ u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\
  \S_{ nj } B' + u2Z (store.lo s) * \B^nj = \S_{ nj } A + \S_{ nj } B /\
  drop nj B = drop nj B' /\ [a0]_s = A `32_ nj).

move=> s h [ [nj [B' [HlenC [Hone [r_a [r_b [r_k [mem [r_j [Hjk2 [Hm [r_t [Hinv Hnth]]]]]]]]]]]]] Hjk];
  rewrite /= r_j r_k in Hjk; move/eqP/Z_of_nat_inj_neq in Hjk.
  have {}Hjk : (nj < nk)%nat.
    rewrite ltn_neqAle Hjk2 andbT; exact/eqP.
exists (A `32_ nj); split.
- Decompose_32 A nj A1 A2 HlenA1 HA'; last by rewrite Ha.
  rewrite HA' (decompose_equiv _ _ _ _ _ HlenA1) !assert_m.conAE assert_m.conCE !assert_m.conAE in mem.
  move: mem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u inj_mult [_ ^^ _]/= r_j mulZC.
- exists nj, B'; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** maddu a0 one; *)

apply hoare_maddu with (fun s h => exists nj B',
  size B' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 2 ^^ 32 /\ u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\
  \S_{ nj } B' + store.utoZ s * \B^nj = \S_{nj.+1} A + \S_{ nj } B /\
  drop nj B = drop nj B').

move=> s h [nj [B' [HlenC [Hone [r_a [r_b [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv [Hnth r_a0]]]]]]]]]]]]]].

exists nj, B'; rewrite Hone umul_1; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite store.utoZ_maddu.
  + rewrite (@u2Z_zext 32) (_ : 2 ^^ 32 = 2 ^^ 32 - 1 + 1) //.
    apply leZ_add => //; exact/leZsub1/max_u2Z.
  + exact: (@leZ_ltZ_trans 1).
- rewrite store.utoZ_maddu; last exact: (@leZ_ltZ_trans 1).
  rewrite lSum_remove_last -/(\B^nj) -/zero32 (addZC (\S_{ nj } A)) -addZA -Hinv r_a0 (@u2Z_zext 32) store.acxhi_zero; last first.
    exact: (@leZ_ltZ_trans 1).
  ring_simplify.
  rewrite -2!addZA; congr (_ + _); by rewrite mulZC addZC.

(** lwxs a0 j b; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists nj B',
  size B' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 2 ^^ 32 /\ u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\
  \S_{ nj } B' +  store.utoZ s * \B^nj = \S_{nj.+1} A + \S_{ nj } B /\
  drop nj B = drop nj B' /\ [a0]_s = B `32_ nj).

move=> s h [nj [B' [HlenC [Hone [Hrega [Hregb [Hregk [Hmem [Hregj [Hjk [Hm [Hregt [Hinv Hnth]]]]]]]]]]]]].
exists (B' `32_ nj); split.
- Decompose_32 B' nj B'1 B'2 HlenB1 HB'; last by rewrite HlenC.
  rewrite HB' (decompose_equiv _ _ _ _ _ HlenB1) in Hmem.
  rewrite assert_m.conCE !assert_m.conAE in Hmem.
  rewrite assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u inj_mult Hregj [Zmult]lock /= -lock mulZC.
- exists nj, B'; repeat Reg_upd; repeat (split; trivial).
  + by Assert_upd.
  + rewrite (drop_nth zero32) in Hnth; last by rewrite Hb.
    symmetry in Hnth.
    rewrite (drop_nth zero32) in Hnth; last by rewrite HlenC.
    by case: Hnth.

(** maddu btmp one; *)

apply hoare_maddu with (fun s h => exists nj B',
  size B' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 2 ^^ 33 - 1 /\ u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\
  \S_{ nj } B' + store.utoZ s * \B^nj = \S_{nj.+1} A + \S_{nj.+1} B /\
  drop nj B = drop nj B').

move=> s h [nj [B' [HlenC [Hone [r_a [r_b [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv [Hnth r_a0]]]]]]]]]]]]]].

exists nj, B'; rewrite Hone umul_1; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite store.utoZ_maddu.
  + rewrite (@u2Z_zext 32) (_ : 2 ^^ 33 - 1 = 2 ^^ 32 - 1 + 2 ^^ 32) //.
    apply leZ_add => //; exact/leZsub1/max_u2Z.
  + exact: (leZ_ltZ_trans Hm).
- rewrite store.utoZ_maddu; last exact: (leZ_ltZ_trans Hm).
  rewrite r_a0 (lSum_remove_last _ B) -/zero32 addZA -Hinv (u2Z_zext 32) /= -ZbetaE -/(B `32_ nj); ring.

(** mflhxu a0; *)

apply hoare_mflhxu with (fun s h => exists nj B',
  size B' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s < 2 /\ u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\
  u2Z [a0]_s * \B^nj + \S_{ nj } B' + store.utoZ s * \B^nj.+1 = \S_{nj.+1} A + \S_{nj.+1} B /\
  drop nj B = drop nj B').

move=> s h [nj [B' [HlenC [Hone [r_a [r_b [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv Hnth]]]]]]]]]]]]].

exists nj, B'; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite store.mflhxu_upd store.utoZ_upd.
  apply store.mflhxu_kbeta1_utoZ; exact: (leZ_ltZ_trans Hm).
- rewrite -Hinv (store.mflhxu_utoZ s) Zbeta_S store.mflhxu_upd // store.utoZ_upd; ring.

(** sw a0 zero16 t; *)

apply hoare_sw_back'' with (fun s h => exists nj B',
  size B' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  B' `32_ nj = [a0]_s /\ u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s < 2 /\ u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\
  \S_{nj.+1} B' + store.utoZ s * \B^nj.+1 = \S_{nj.+1} A + \S_{nj.+1} B /\
  drop nj.+1 B = drop nj.+1 B').

move=> s h [nj [B' [HlenC [Hone [r_a [r_b [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv Hnth]]]]]]]]]]]]].

have Htmp : [ var_e b \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) ]e_s = [ var_e t \+ int_e (sext 16 zero16) ]e_s.
  rewrite /= sext_0 addi0.
  apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat.
  by rewrite inj_mult r_b r_t.
  rewrite inj_mult -Zbeta1E r_b; simpl Z_of_nat.
  apply: ltZ_trans; last exact/Hnb.
  apply/ltZ_add2l/ltZ_pmul2l => //; exact/inj_lt/ltP.

Decompose_32 B' nj B'1 B'2 HlenB1 HB'; last by rewrite HlenC.

rewrite HB' assert_m.conCE (decompose_equiv _ _ _ _ _ HlenB1) !assert_m.conAE
  assert_m.conCE !assert_m.conAE in Hmem.
exists (int_e (B' `32_ nj)).
move: Hmem; apply monotony => ht.
exact/mapsto_ext.
apply currying => h' H'; simpl app in H'.
exists nj, (upd_nth B' nj [a0]_s).
repeat (split; trivial).
exact/size_upd_nth.
rewrite HB' upd_nth_cat HlenB1 // subnn /= (_ : [a0]_s :: B'2 = ([a0]_s ::nil) ++ B'2) // (decompose_equiv _ _ _ _ _ HlenB1).
rewrite cat0s in H'.
assoc_comm H'.
by move: H'; apply mapsto_ext.

by rewrite /nth' nth_upd_nth // HlenC.

rewrite lSum_remove_last -ZbetaE nth_upd_nth; last by rewrite HlenC.
rewrite -Hinv.
suff : \S_{ nj } (upd_nth B' nj [a0]_s) = \S_{ nj } B' by move=> ->; ring.
rewrite {1}HB' upd_nth_cat; last by rewrite HlenB1.
by rewrite -lSum_beyond // HB' -lSum_beyond.

rewrite drop_upd_nth //.
rewrite (drop_nth zero32) in Hnth; last by rewrite Hb.
symmetry in Hnth. rewrite (drop_nth zero32) in Hnth; last by rewrite HlenC.
by case: Hnth.

(** addi t t four16; *)

apply hoare_addiu with (fun s h => exists nj B',
  size B' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj.+1 <= nk)%nat /\
  store.utoZ s < 2 /\ u2Z [t]_s = u2Z vb + 4 * (Z_of_nat nj + 1) /\
  \S_{nj.+1} B' + u2Z (store.lo s) * \B^nj.+1 = \S_{nj.+1} A + \S_{nj.+1} B /\
  drop nj.+1 B = drop nj.+1 B').

move=> s h [nj [B' [HlenC [Hone [r_a [r_b [r_k [Hmem [r_ctmp [r_j [Hjk [Hm [r_t [Hinv Hnth]]]]]]]]]]]]]].

exists nj, B'; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite u2Z_add // r_t sext_Z2u // Z2uK //.
- ring.
- rewrite -Zbeta1E; apply: (leZ_ltZ_trans _ Hnb).
  rewrite -addZA -{2}(mulZ1 4) -mulZDr.
  apply/leZ_add2l/leZ_pmul2l => //.
  rewrite -Z_S; exact/inj_le/leP.
rewrite store.acxhi_zero // in Hinv.
exact: (@ltZ_trans 2).

(** addi j j one16 *)

apply hoare_addiu'.

move=> s h [nj [B' [len_C [Hone [r_a [r_b [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv Hnth]]]]]]]]]]]]].
exists nj.+1, B'; rewrite Z_S.
repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite u2Z_add // sext_Z2u // r_j Z2uK // -Zbeta1E.
  apply: (leZ_ltZ_trans _ Hnb).
  apply leZ_addl; first exact/min_u2Z.
  rewrite -Z_S (_ : 4 = Z_of_nat 4) // -inj_mult multE.
  apply/inj_le/(@le_trans _ nk) => //.
  exact/leP; rewrite -ltnS.
  by apply/leP; rewrite leq_pmull.
- move/leZsub1 : Hm; exact.
Qed.

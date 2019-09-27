(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_tactics mips_contrib mapstos multi_incr_u_prg.
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

Lemma multi_incr_u_triple k one a t j a0 : uniq(k, one, a, t, j, a0, r0) ->
  forall nk va, u2Z va + 4 * Z_of_nat nk < \B^1 ->
  forall A , size A = nk ->
 {{ fun s h => [ one ]_s = one32 /\ [ a ]_s = va /\
   u2Z [ k ]_s = Z_of_nat nk /\ (var_e a |--> A) s h }}
 multi_incr_u k one a t j a0
 {{ fun s h => exists A', size A' = nk /\ [ one ]_s = one32 /\ [ a ]_s = va /\
   (var_e a |--> A' ) s h /\ u2Z (store.lo s) <= 1 /\
   \S_{ nk } A' + u2Z (store.lo s) * \B^nk = \S_{ nk } A + if nk == O then 0 else 1 }}.
Proof.
move=> Hset nk va Hna A Ha.
rewrite /multi_incr_u.

(** addiu j r0 zero16; *)

NextAddiu.
move=> s h [C [H [H1 H4]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** addiu t a zero16; *)

NextAddiu.
move=> s h [[C [H0 [H3 H2]]] H1].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** multu r0 r0 *)

apply hoare_multu with (fun s h => [one]_s = one32 /\ [a]_s = va /\
  u2Z [k]_s = Z_of_nat nk /\
  u2Z [j]_s = 0 /\ u2Z [t]_s = u2Z va /\ store.multi_null s /\
  (var_e a |--> A) s h).

move=> s h [[[H [r_a [r_k mem]]] r_j] r_t].
rewrite /wp_multu.
repeat Reg_upd.
rewrite umul_0 /store.multi_null store.utoZ_multu Z2uK //.
repeat (split => //).
by rewrite r_j add0i sext_Z2u // Z2uK.
by rewrite r_t sext_Z2u // addi0 r_a.
by Assert_upd.

(** while (bne j k) *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists nj A',
  size A' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj <= nk)%nat /\
  store.utoZ s <= 1 /\ u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\
  (\S_{nj} A' + u2Z (store.lo s) * \B^nj = \S_{nj} A + if nj == O then 0 else 1) /\
  drop nj A = drop nj A').

move=> s h [r_one [r_a [r_k [r_j [r_t [Hm mem]]]]]].
exists O, A; repeat (split; trivial).
by rewrite store.multi_null_utoZ.
by rewrite /= addZ0.
by rewrite store.multi_null_lo //= Z2uK.

move=> s h [[nj [B' [H [H3 [H2 [H4 [H5 [H6 [H7 [H8 [H9 [H10 Hnth]]]]]]]]]]]] ].
rewrite /= negbK => /eqP H1.
exists B'; repeat (split; trivial).
have : store.utoZ s < \B^1 by exact: (@leZ_ltZ_trans 1).
by case/store.utoZ_lo_beta1=> _ [] _ <-.
suff : nk = nj by move=> ->.
rewrite H6 H4 in H1; by apply Z_of_nat_inj.

(** lwxs a0 j a; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists nj A',
  size A' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 1 /\ u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\
  (\S_{ nj } A' + u2Z (store.lo s) * \B^nj = \S_{ nj } A + if nj == O then 0 else 1) /\
  drop nj A = drop nj A' /\ [a0]_s = A `32_ nj).

move=> s h [ [nj [A' [HlenC [Hone [r_a [r_k [mem [r_j [Hjk2 [Hm [r_t [Hinv Hnth]]]]]]]]]]]] Hjk];
  rewrite /= r_j r_k in Hjk.
  have {}Hjk : (nj < nk)%nat.
    rewrite ltn_neqAle Hjk2 andbT.
    by apply: contra Hjk => /eqP ->.
exists (A `32_ nj); split.
- Decompose_32 A' nj A1 A2 HlenA1 HA'; last by rewrite HlenC.
  rewrite HA' (decompose_equiv _ _ _ _ _ HlenA1) in mem.
  rewrite assert_m.conCE in mem.
  rewrite !assert_m.conAE in mem.
  move: mem; apply monotony => // h'.
  apply mapsto_ext.
  by rewrite /= shl_Z2u inj_mult [_ ^^ _]/= r_j mulZC.
  rewrite HA' drop_cat // (drop_nth zero32) in Hnth; last by rewrite Ha.
  rewrite HlenA1 ltnn subnn drop0 in Hnth.
  by case: Hnth.
- exists nj, A'; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** maddu a0 one; *)

apply hoare_maddu with (fun s h => exists nj A',
  size A' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 2 ^^ 32 /\ u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\
  (\S_{ nj } A' + store.utoZ s * \B^nj = \S_{ nj.+1 } A + if nj == O then 0 else 1) /\
  drop nj A = drop nj A').

move=> s h [nj [A' [HlenC [Hone [r_a [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv [Hnth r_a0]]]]]]]]]]]]].

exists nj, A'; rewrite Hone umul_1; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite store.utoZ_maddu.
  + rewrite (@u2Z_zext 32) (_ : 2 ^^ 32 = 2 ^^ 32 - 1 + 1) //.
    apply leZ_add => //; exact/leZsub1/max_u2Z.
  + exact: (@leZ_ltZ_trans 1).
- rewrite store.utoZ_maddu; last exact: (@leZ_ltZ_trans 1).
  rewrite lSum_remove_last -/zero32 (addZC (\S_{nj} A)) -addZA -Hinv r_a0 (@u2Z_zext 32) store.acxhi_zero; last first.
    exact: (@leZ_ltZ_trans 1).
  ring_simplify.
  rewrite -2!addZA; f_equal; by rewrite mulZC addZC.

(** ifte_beq j,r0 thendo *)

apply while.hoare_seq with (fun s h => exists nj A',
  size A' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 2 ^^ 32 /\ u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\
  (\S_{ nj } A' + store.utoZ s * \B^nj = \S_{ nj.+1 } A + if nj == O then 0 else 1) /\
  drop nj A = drop nj A' /\
  ((nj = O -> [ a0 ]_s = one32) /\ ((O < nj)%nat -> [ a0 ]_s = zero32))).

apply while.hoare_ifte.

apply hoare_addiu'.
move=> s h [[nj [A' [HlenC [Hone [r_a [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv Hnth]]]]]]]]]]]] ].
rewrite /= store.get_r0 Z2uK // => /eqP.
rewrite r_j => Ht.

rewrite /wp_addiu.
exists nj, A'.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.
move=> _.
by rewrite sext_Z2u // addi0.
move=> abs.
by destruct nj.

apply hoare_addiu'.
move=> s h [[nj [A' [HlenC [Hone [r_a [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv Hnth]]]]]]]]]]]]].
rewrite /= store.get_r0 Z2uK // => /eqP.
rewrite r_j => Ht.

rewrite /wp_addiu.
exists nj, A'.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.
by move=> ?; subst nj.
move=> ?.
by rewrite sext_Z2u // addi0.

(** maddu a0 one; *)

apply hoare_maddu with (fun s h => exists nj A',
  size A' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 2 ^^ 33 - 1 /\ u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\
  (\S_{ nj } A' + store.utoZ s * \B^nj = \S_{ nj.+1 } A + 1) /\
  drop nj A = drop nj A').

move=> s h [nj [A' [HlenC [Hone [r_a [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv [Hnth r_a0]]]]]]]]]]]]].

exists nj, A'; rewrite Hone umul_1; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite store.utoZ_maddu.
  + rewrite (@u2Z_zext 32) (_ : 2 ^^ 33 - 1 = 2 ^^ 32 - 1 + 2 ^^ 32) //.
    apply leZ_add => //; exact/leZsub1/max_u2Z.
  + exact: (leZ_ltZ_trans Hm).
- rewrite store.utoZ_maddu; last exact: (leZ_ltZ_trans Hm).
  case: r_a0 => r_a0 r_a0'.
  destruct nj.
    rewrite addZ0 in Hinv.
    rewrite r_a0 // zext_Z2u // !Z2uK // -Hinv ZbetaE [_ ^^ _]/=; ring.
  by rewrite r_a0' // zext_Z2u // !Z2uK.

(** mflhxu a0; *)

apply hoare_mflhxu with (fun s h => exists nj A',
  size A' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s < 2 /\ u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\
  u2Z [a0]_s * \B^nj + \S_{ nj } A' + store.utoZ s * \B^nj.+1 = \S_{ nj.+1 } A + 1 /\
  drop nj A = drop nj A').

move=> s h [nj [A' [HlenC [Hone [Hrega [Hregk [Hmem [Hregj [Hjk [Hm [Hregt [Hinv Hnth]]]]]]]]]]]].

exists nj, A'; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite store.mflhxu_upd store.utoZ_upd.
  exact/store.mflhxu_kbeta1_utoZ/(leZ_ltZ_trans Hm).
- rewrite -Hinv (store.mflhxu_utoZ s) Zbeta_S store.mflhxu_upd // store.utoZ_upd; ring.

(** sw a0 zero16 t; *)

apply hoare_sw_back'' with (fun s h => exists nj A',
  size A' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A') s h /\
  A' `32_ nj = [a0]_s /\ u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s < 2 /\ u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\
  \S_{ nj.+1 } A' + store.utoZ s * \B^nj.+1 = \S_{ nj.+1 } A + 1 /\
  drop nj.+1 A = drop nj.+1 A').

move=> s h [nj [A' [A'_nk [Hone [r_a [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv Hnth]]]]]]]]]]]].

have Htmp : [ var_e a \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) ]e_s = [ var_e t \+ int_e (sext 16 zero16) ]e_s.
  rewrite /= sext_0 addi0.
  apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat.
  by rewrite inj_mult r_a r_t.
  rewrite inj_mult -Zbeta1E r_a; simpl Z_of_nat.
  apply/(ltZ_trans _ Hna)/ltZ_add2l/ltZ_pmul2l => //; exact/inj_lt/ltP.

Decompose_32 A' nj A'1 A'2 HlenA1 HA'; last by rewrite A'_nk.

rewrite HA' in Hmem.
rewrite (decompose_equiv _ _ _ _ _ HlenA1) in Hmem.
rewrite assert_m.conCE in Hmem.
rewrite !assert_m.conAE in Hmem.
exists (int_e (A' `32_ nj)).
move: Hmem; apply monotony => ht.
by apply mapsto_ext.
apply currying => h' H'; simpl app in H'.
exists nj, (upd_nth A' nj [a0]_s).
repeat (split; trivial).
by apply size_upd_nth.
rewrite HA' upd_nth_cat HlenA1 // subnn /=.
rewrite (_ : [a0]_s :: A'2 = ([a0]_s ::nil) ++ A'2) // .
rewrite (decompose_equiv _ _ _ _ _ HlenA1).
rewrite cat0s in H'.
assoc_comm H'.
by move: H'; apply mapsto_ext.

by rewrite /nth' nth_upd_nth // A'_nk.

rewrite lSum_remove_last -ZbetaE nth_upd_nth; last by rewrite A'_nk.
rewrite -Hinv.
have -> : \S_{ nj } (upd_nth A' nj [a0]_s) = \S_{ nj } A'.
  rewrite {1}HA' upd_nth_cat; last by rewrite HlenA1.
  by rewrite -lSum_beyond // HA' -lSum_beyond.
ring.

rewrite drop_upd_nth //.
rewrite (drop_nth zero32) in Hnth; last by rewrite Ha.
symmetry in Hnth. rewrite (drop_nth zero32) in Hnth; last by rewrite A'_nk.
by case: Hnth.

(** addi t t four16; *)

apply hoare_addiu with (fun s h => exists nj A',
  size A' = nk /\ [one]_s = one32 /\ [a]_s = va /\
  u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj.+1 <= nk)%nat /\
  store.utoZ s < 2 /\ u2Z [t]_s = u2Z va + 4 * (Z_of_nat nj + 1) /\
  \S_{ nj.+1 } A' + u2Z (store.lo s) * \B^nj.+1 = \S_{ nj.+1 } A + 1 /\
  drop nj.+1 A = drop nj.+1 A').

move=> s h [nj [A' [A'_nk [Hone [r_a [r_k [Hmem [r_ctmp [r_j [Hjk [Hm [r_t [Hinv Hnth]]]]]]]]]]]]].

exists nj, A'; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite u2Z_add // r_t sext_Z2u // Z2uK //.
- ring.
- rewrite -Zbeta1E; apply: (leZ_ltZ_trans _ Hna).
  rewrite -addZA -{2}(mulZ1 4) -mulZDr.
  apply leZ_add2l, leZ_pmul2l => //.
  rewrite -Z_S; by apply/inj_le/leP.
rewrite store.acxhi_zero // in Hinv.
exact: (@ltZ_trans 2).

(** addi j j one16 *)

apply hoare_addiu'.

move=> s h [nj [A' [A'_nk [Hone [r_a [r_k [Hmem [r_j [Hjk [Hm [r_t [Hinv Hnth]]]]]]]]]]]].
exists nj.+1, A'; rewrite Z_S.
repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite u2Z_add // sext_Z2u // r_j Z2uK // -Zbeta1E.
  apply: (leZ_ltZ_trans _ Hna).
  apply leZ_addl; first exact/min_u2Z.
  rewrite -Z_S (_ : 4 = Z_of_nat 4) // -inj_mult.
  apply/inj_le/leP/(leq_trans Hjk); by rewrite multE leq_pmull.
- move/leZsub1: Hm; exact.
Qed.

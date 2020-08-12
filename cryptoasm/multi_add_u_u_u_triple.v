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
Local Open Scope heap_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope multi_int_scope.

Lemma multi_add_u_u_u_triple k one a b c t j atmp :
  uniq(k, one, a, b, c, t, j, atmp, r0) ->
 forall nk va vb vc, u2Z vc + 4 * Z_of_nat nk < \B^1 ->
 forall A B, size A = nk -> size B = nk ->
 {{ fun s h => exists C, size C = nk /\ [ one ]_s = one32 /\
    [ a ]_s = va /\ [ b ]_s = vb /\ [ c ]_s = vc /\
    u2Z [ k ]_s = Z_of_nat nk /\
    (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h }}
 multi_add_u_u k one a b c t j atmp
 {{ fun s h => exists C, size C = nk /\
    [ a ]_s = va /\ [ b ]_s = vb /\ [ c ]_s = vc /\
    u2Z [ k ]_s = Z_of_nat nk /\
    (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
    u2Z (store.lo s) <= 1 /\
    \S_{ nk } C + u2Z (store.lo s) * \B^nk = \S_{ nk } A + \S_{ nk } B }}.
Proof.
move=> Hset nk va vb vc Hnc A B Ha Hb; rewrite /multi_add_u_u.

(** addiu j r0 zero16; *)

NextAddiu.
move=> s h [C [H [H2 [H1 [H3 [H4 [H5 H6]]]]]]]; rewrite /wp_addiu; repeat Reg_upd.
split; last by reflexivity.
exists C; repeat (split; trivial).
by Assert_upd.

(** addiu t c zero16; *)

NextAddiu.
move=> s h [[C [H0 [H3 [H2 [H4 [H5 [H6 H7]]]]]]] H1].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
exists C; repeat (split; trivial).
by Assert_upd.

(** multu r0 r0 *)

apply hoare_multu with (fun s h => exists C,
  size C = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [j]_s = 0 /\ u2Z [t]_s = u2Z vc /\ store.multi_null s /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h ).

move=> s h [[[C [H [H4 [H3 [H5 [H6 [H7 H10]]]]]]] H2] H1].
rewrite /wp_multu.
exists C; repeat Reg_upd.
rewrite umul_0 /store.multi_null store.utoZ_multu Z2uK //.
repeat (split => //).
by rewrite H2 add0i sext_Z2u // Z2uK.
by rewrite H1 sext_Z2u // addi0 H6.
by Assert_upd.

(** while (bne j k) *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists nj C,
  size C = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj <= nk)%nat /\
  store.utoZ s <= 1 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\
  \S_{ nj }C + u2Z (store.lo s) * \B^nj = \S_{ nj } A + \S_{ nj } B).

move=> s h [C [len_C [r_one [r_a [r_b [r_c [r_k [r_j [r_t [Hm mem]]]]]]]]]].
exists O, C; repeat (split; trivial).
by rewrite Hm.
by rewrite r_t /= addZ0.
by rewrite store.multi_null_lo // Z2uK.

move=> s h [[nj [C [H [H3 [H2 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 H13]]]]]]]]]]]]] /=].
move/negPn/eqP => H1.
exists C; repeat (split; trivial).
have : store.utoZ s < \B^1 by apply (@leZ_ltZ_trans 1).
by case/store.utoZ_lo_beta1=> _ [] _ <-.
suff : nk = nj by move ->.
rewrite H8 H6 in H1; exact/Z_of_nat_inj.

(** lwxs atmp j a; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists nj C,
  size C = nk /\ [ one ]_s = one32 /\ [ a ]_s = va /\
  [ b ]_s = vb /\ [ c ]_s = vc /\ u2Z [ k ]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 1 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\
  \S_{ nj }C + u2Z (store.lo s) * \B^nj = \S_{ nj } A + \S_{ nj } B /\
  [atmp]_s = A `32_ nj).

move=> s h [[nj [C [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk2 [Hm [Hrt Hinv]]]]]]]]]]]]] Hjk];
  rewrite /= in Hjk; move/eqP in Hjk.
have {}Hjk : (nj < nk)%nat.
  rewrite ltn_neqAle Hjk2 andbT; apply/eqP/Z_of_nat_inj_neq; by rewrite -Hrj -Hrk.
exists (A `32_ nj); split.
- Decompose_32 A nj A1 A2 HlenA1 HA'; last by rewrite Ha.
  rewrite HA' (decompose_equiv _ _ _ _ _ HlenA1) !assert_m.conAE
    assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u inj_mult Hrj [Zmult]lock /= -lock mulZC.
- rewrite /update_store_lwxs.
  exists nj, C; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** maddu atmp one; *)

apply hoare_maddu with (fun s h => exists nj C,
  size C = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 2 ^^ 32 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\
  \S_{ nj }C + store.utoZ s * \B^nj = \S_{ nj.+1 } A + \S_{ nj } B).

move=> s h [nj [C [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hm [Hrt [Hinv Hratmp]]]]]]]]]]]]]].

exists nj, C; rewrite Hone umul_1; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite store.utoZ_maddu.
- rewrite (@u2Z_zext 32) (_ : 2 ^^ 32 = 2 ^^ 32 - 1 + 1) //.
  apply leZ_add => //; exact/leZsub1/max_u2Z.
  exact: (@leZ_ltZ_trans 1).
- rewrite store.utoZ_maddu; last exact: (@leZ_ltZ_trans 1).
  rewrite lSum_remove_last -/zero32 (addZC (\S_{ nj } A)) -addZA -Hinv Hratmp (@u2Z_zext 32) store.acxhi_zero; last first.
    exact: (@leZ_ltZ_trans 1).
  ring_simplify.
  rewrite -2!addZA; f_equal; by rewrite mulZC addZC.

(** lwxs atmp j b; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists nj C,
  size C = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 2 ^^ 32 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\
  \S_{ nj }C + store.utoZ s * \B^nj = \S_{ nj.+1 } A + \S_{ nj } B /\
  [atmp]_s = B `32_ nj).

move=> s h [nj [C [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hm [Hrt Hinv]]]]]]]]]]]]].
exists (B `32_ nj); split.
- Decompose_32 B nj B1 B2 HlenB1 HB'; last by rewrite Hb.
  rewrite HB' (decompose_equiv _ _ _ _ _ HlenB1) !assert_m.conAE assert_m.conCE
    !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u inj_mult Hrj [Zmult]lock /= -lock mulZC.
- rewrite /update_store_lwxs.
  exists nj, C; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** maddu atmp one; *)

apply hoare_maddu with (fun s h => exists nj C,
  size C = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s <= 2 ^^ 33 - 1 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\
  \S_{ nj }C + store.utoZ s * \B^nj = \S_{ nj.+1 } A + \S_{ nj.+1 } B).

move=> s h [nj [C [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hm [Hrt [Hinv Hratmp]]]]]]]]]]]]]].

exists nj, C; rewrite Hone umul_1; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite store.utoZ_maddu.
rewrite (@u2Z_zext 32) (_ : 2 ^^ 33 - 1 = 2 ^^ 32 - 1 + 2 ^^ 32) //.
apply leZ_add => //; exact/leZsub1/max_u2Z.
exact: (leZ_ltZ_trans Hm).
rewrite store.utoZ_maddu; last exact: (leZ_ltZ_trans Hm).
rewrite Hratmp (lSum_remove_last _ B) -/zero32 -ZbetaE addZA -Hinv (@u2Z_zext 32) /= -/(B `32_ nj); ring.

(** mflhxu atmp; *)

apply hoare_mflhxu with (fun s h => exists nj C,
  size C = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s < 2 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\
  u2Z [atmp]_s * \B^nj + \S_{ nj }C + store.utoZ s * \B^nj.+1 = \S_{ nj.+1 } A + \S_{ nj.+1 } B).

move=> s h [nj [C [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hm [Hrt Hinv]]]]]]]]]]]]].

exists nj, C; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite store.mflhxu_upd store.utoZ_upd.
  apply store.mflhxu_kbeta1_utoZ.
  rewrite (_ : \B^1 * 2 = 2 ^^ 33) //; exact: (leZ_ltZ_trans Hm).
- rewrite -Hinv (store.mflhxu_utoZ s) Zbeta_S store.mflhxu_upd // store.utoZ_upd; ring.

(** sw atmp zero16 t; *)

apply hoare_sw_back'' with (fun s h => exists nj C,
  size C = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  C `32_ nj = [atmp]_s /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  store.utoZ s < 2 /\ u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\
  \S_{ nj.+1 } C + store.utoZ s * \B^nj.+1 = \S_{ nj.+1 } A + \S_{ nj.+1 } B).

move=> s h [nj [C [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hm [Hrt Hinv]]]]]]]]]]]]].

have Htmp : [ var_e c \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) ]e_s = [ var_e t \+ int_e (sext 16 zero16) ]e_ s.
  rewrite /= sext_0 addi0.
  apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat.
  by rewrite inj_mult Hrc Hrt.
  rewrite inj_mult -Zbeta1E Hrc; simpl Z_of_nat.
  apply: (ltZ_trans _ Hnc).
  apply/ltZ_add2l/ltZ_pmul2l => //; exact/inj_lt/ltP.

Decompose_32 C nj C1 C2 HlenC1 HC'; last by rewrite HlenC.
rewrite HC' (decompose_equiv _ _ _ _ _ HlenC1) in Hmem.
do 3 rewrite conCE !conAE in Hmem.
exists (int_e (C `32_ nj)).
move: Hmem; apply monotony => ht.
exact/mapsto_ext.
apply currying => h' H'; simpl app in H'.
exists nj, (upd_nth C nj [atmp]_s).
repeat (split; trivial).
exact/size_upd_nth.
rewrite HC' upd_nth_cat HlenC1 // subnn /= (decompose_equiv _ _ _ _ _ HlenC1).
rewrite cat0s in H'.
assoc_comm H'.
move: H'; exact/mapsto_ext.

by rewrite /nth' nth_upd_nth // HC' size_cat /= addnS HlenC1 ltnS leq_addr.

rewrite lSum_remove_last -ZbetaE nth_upd_nth; last by rewrite HlenC.
rewrite -Hinv.
have -> : \S_{ nj }(upd_nth C nj [atmp]_s) = \S_{ nj }C.
  rewrite {1}HC' upd_nth_cat; last by rewrite HlenC1.
  by rewrite -lSum_beyond // HC' -lSum_beyond.
ring.

(** addi t t four16; *)

apply hoare_addiu with (fun s h => exists nj C,
  size C = nk /\ [one]_s = one32 /\ [a]_s = va /\
  [b]_s = vb /\ [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj.+1 <= nk)%nat /\
  store.utoZ s < 2 /\ u2Z [t]_s = u2Z vc + 4 * (Z_of_nat nj + 1) /\
  \S_{ nj.+1 } C + u2Z (store.lo s) * \B^nj.+1 = \S_{ nj.+1 } A + \S_{ nj.+1 } B).

move=> s h [nj [C [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hratmp [Hrj [Hjk [Hm [Hrt Hinv]]]]]]]]]]]]]].

exists nj, C; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite u2Z_add // Hrt sext_Z2u // Z2uK //.
  + ring.
  + rewrite -Zbeta1E; apply: (leZ_ltZ_trans _ Hnc).
    rewrite -addZA; apply leZ_add2l.
      move/ltP : Hjk => /inj_lt ?; lia.
    rewrite store.acxhi_zero // in Hinv.
    exact: (@ltZ_trans 2).

(** addi j j one16 *)

apply hoare_addiu'.
move=> s h [nj [C [HlenC [Hone [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hm [Hrt Hinv]]]]]]]]]]]]].

exists nj.+1, C; repeat Reg_upd.
rewrite Z_S.
repeat (split; trivial).
- by Assert_upd.
- rewrite u2Z_add // sext_Z2u // Hrj Z2uK // -Zbeta1E.
  apply: (leZ_ltZ_trans _ Hnc).
  move/ltP : Hjk => /inj_lt ?.
  move: (min_u2Z vc) => ?; lia.
- move/leZsub1 : Hm; exact.
Qed.

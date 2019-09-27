(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext machine_int multi_int.
Import MachineInt.
Require Import uniq_tac.
Require Import mips_seplog mips_tactics mips_contrib mapstos.
Require Import multi_sub_u_u_prg.
Import expr_m.
Import assert_m.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope multi_int_scope.
Local Open Scope zarith_ext_scope.

Section multi_sub.

Variables k a b t j u bor atmp btmp : reg.

Lemma multi_sub_u_u_L_triple : uniq(k, a, b, t, j, u, bor, atmp, btmp, r0) ->
forall nk va vb, u2Z va + 4 * Z_of_nat nk < \B^1 ->
forall A B, size A = nk -> size B = nk ->
{{ fun s h => [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B) s h }}
 multi_sub_u_u k a b a t j u bor atmp btmp
{{ fun s h => exists A', size A' = nk /\ [a]_s = va /\ [b]_s = vb /\
  u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  u2Z [bor]_s <= 1 /\
  \S_{ nk } A' = \S_{ nk } A - \S_{ nk } B + u2Z [bor]_s * \B^nk }}.
Proof.
move=> Hset nk va vb Hna A B Ha Hb; rewrite /multi_sub_u_u.

(** addiu j zero zero16; *)

NextAddiu.
move=> s h [Hra [Hrb [Hrk H]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** addi t c zero16 *)

NextAddiu.
move=> s h [[Hra [Hrb [Hrk H]]] Hj].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** addi bor zero zero16; *)

NextAddiu.
move=> s h [[[Hra [Hrb [Hrk H]]] Hj] Ht].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** while (bne j k) ( *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists A' nj nbor,
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj <= nk)%nat /\
  u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } A' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  drop nj A = drop nj A').

move=> s h [[[[Hra [Hrb [Hrk H]]] Hj] Ht Hbor]].
exists A, O, 0; repeat (split => //).
by rewrite store.get_r0 add0i sext_Z2u // Z2uK in Hj.
rewrite Ht sext_0 addi0 Hra //; ring.
by rewrite Hbor sext_0 addi0 // store.get_r0 Z2uK.

move=> s h [[A' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv Hnth]]]]]]]]]]]]] Hjk]].
rewrite /= Hrj Hrk in Hjk. move/negPn/eqP/Z_of_nat_inj in Hjk; subst nj.
exists A'; repeat (split; trivial).
by rewrite Hrbor.
by rewrite Hrbor -HInv.

(** lwxs atmp j b; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists A' nj nbor,
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj } A' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  drop nj A = drop nj A' /\ [atmp]_s = B `32_ nj).

move=> s h [ [A' [nj [nbor [HlenA' [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv Hnth]]]]]]]]]]]]] Hjk]].
rewrite /= in Hjk; move/eqP in Hjk.

exists (B `32_ nj); split.
- Decompose_32 B nj B1 B2 HlenB' HB'; last by ssromega.
  rewrite HB' (decompose_equiv _ _ _ _ _ HlenB') in Hmem.
  rewrite assert_m.conCE !assert_m.conAE in Hmem.
  rewrite assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u Hrj inj_mult mulZC.
- rewrite /update_store_lwxs.
  exists A', nj, nbor; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

ssromega.

(** addu btmp atmp bor; *)

apply hoare_addu with (fun s h => exists A' nj nbor,
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } A' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  drop nj A = drop nj A' /\ [atmp]_s = B `32_ nj /\
  [btmp]_s = B `32_ nj `+ [bor]_s).

move=> s h [A' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hnth Hratmp]]]]]]]]]]]]]]].

exists A', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite -Hratmp.

(** sltu btmp atmp; *)

apply hoare_sltu with (fun s h => exists A' nj nbor,
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } A' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  drop nj A = drop nj A' /\
  [btmp]_s = B `32_ nj `+ [bor]_s /\
  [u]_s = if Zlt_bool (u2Z [btmp]_s) (u2Z (B `32_ nj)) then one32 else zero32).

move=> s h [A' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hnth [Hratmp Hrbtmp]]]]]]]]]]]]]]]].

exists A', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite -Hratmp.

(** lwxs atmp j a; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists A' nj nbor,
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\ u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\
  u2Z [bor]_s = nbor /\ nbor <= 1 /\ \S_{ nj } A' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj  /\
  drop nj A = drop nj A' /\ [atmp]_s = A `32_ nj /\
  [btmp]_s = B `32_ nj `+ [bor]_s /\
  [u]_s = if Zlt_bool (u2Z [btmp]_s) (u2Z (B `32_ nj)) then one32 else zero32).

move=> s h [A' [nj [nbor [HlenA' [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hnth [Hrbtmp Hru]]]]]]]]]]]]]]]].
exists (A' `32_ nj); split.
- Decompose_32 A' nj A'1 A'2 HlenA'1 HA''; last by ssromega.
  rewrite HA'' (decompose_equiv _ _ _ _ _ HlenA'1) !assert_m.conAE assert_m.conCE
    !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u Hrj inj_mult mulZC.
- rewrite /update_store_lwxs.
  exists A', nj, nbor; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  rewrite (drop_nth zero32) in Hnth; last by ssromega.
  symmetry in Hnth.
  rewrite (drop_nth zero32) in Hnth; last by ssromega.
  by case: Hnth.

(** ifte_beq u, zero thendo *)

apply while.hoare_seq with (fun s h => exists A' nj nbor,
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\ drop nj A = drop nj A' /\
  u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj } A' + u2Z [atmp]_s * \B^nj =
  \S_{ nj } A - \S_{ nj } B + u2Z (A `32_ nj) * \B^nj - u2Z (B `32_ nj) * \B^nj + nbor * \B^nj.+1).

apply while.hoare_ifte.

(** addiu u r0 one16; *)

apply hoare_addiu with (fun s h => exists A' nj nbor,
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  [u]_s = one32 /\ u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } A' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\ drop nj A = drop nj A' /\ [btmp]_s = B `32_ nj `+ [bor]_s /\
  u2Z [btmp]_s = u2Z (B `32_ nj) + nbor).

move=> s h [ [A' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hnth [Hratmp [Hrbtmp Hru]]]]]]]]]]]]]]]]] Huzero]; rewrite /= in Huzero.
exists A', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite add0i sext_Z2u.
rewrite Hrbtmp -Hrbor u2Z_add //.
apply u2Z_add_no_overflow.
rewrite -Hrbtmp.
apply Znot_gt_le; move/Z.gt_lt/ltZP => X.
by rewrite Hru X Z2uK // Z2uK in Huzero.

(** multu atmp one; *)

apply hoare_multu with (fun s h => exists A' nj nbor,
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  [u]_s = one32 /\ u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } A' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\ drop nj A = drop nj A' /\ [btmp]_s = B `32_ nj `+ [bor]_s /\
  u2Z [btmp]_s = u2Z (B `32_ nj) + nbor /\ store.utoZ s = u2Z (A `32_ nj)).

move=> s h [A' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrone [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hnth [Hratmp [Hrbtmp Hru]]]]]]]]]]]]]]]]]].
exists A', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.utoZ_multu Hnth Hrone umul_1 (@u2Z_zext 32).

(** msubu btmp one; *)

apply hoare_msubu with (fun s h => exists A' nj nbor,
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  [u]_s = one32 /\ u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj } A' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\ [atmp]_s = A `32_ nj /\
  drop nj A = drop nj A' /\
  [btmp]_s = B `32_ nj `+ [bor]_s /\ u2Z [btmp]_s = u2Z (B `32_ nj) + nbor /\
  ((u2Z [btmp]_s <= u2Z (A `32_ nj) -> store.utoZ s = u2Z (A `32_ nj) - u2Z [btmp]_s) /\
   (u2Z (A `32_ nj) < u2Z [btmp]_s -> store.utoZ s = \B^ 2 + u2Z (A `32_ nj) - u2Z [btmp]_s))).

move=> s h [A' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hone [Hrj [Hjk [Hrt [Hrbor [Hnbor [Hinv [Hratmp [Hnth [Hrbtmp [Hrbtmp2 Hm]]]]]]]]]]]]]]]]]]].
exists A', nj, nbor.
rewrite Hone umul_1.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
move=> H; rewrite store.msubu_utoZ Hm ?(@u2Z_zext 32) //.
apply (@ltZ_trans (\B^1)); by [apply max_u2Z | ].
exact/Z.le_ge.
move=> H; rewrite store.msubu_utoZ_overflow Hm ?(@u2Z_zext 32) //.
apply (@ltZ_trans (\B^1)); by [exact: max_u2Z | ].

(** sltu bor atmp btmp; *)

apply hoare_sltu with (fun s h => exists A' nj nbor,
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A' ** var_e b |--> B) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\ nbor <= 1 /\
  \S_{ nj } A' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\
  drop nj A = drop nj A' /\
  [btmp]_s = B `32_ nj `+ Z2u 32 nbor /\
  u2Z [btmp]_s = u2Z (B `32_ nj) + nbor /\
  (u2Z [btmp]_s <= u2Z (A `32_ nj) -> store.utoZ s = u2Z (A `32_ nj) - u2Z [btmp]_s) /\
  (u2Z (A `32_ nj) < u2Z [btmp]_s -> store.utoZ s = \B^2 + u2Z (A `32_ nj) - u2Z [btmp]_s) /\
  [bor]_s = if Zlt_bool (u2Z (A `32_ nj)) (u2Z [btmp]_s) then one32 else zero32).

move=> s h [A' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hone [Hrj [Hjk [Hrt [Hrbor [Hnbor [Hinv [Hratmp [Hnth [Hrbtmp [Hrbtmp2 [Hinv1 Hinv2]]]]]]]]]]]]]]]]]]]].

exists A', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite -Hrbor Z2u_u2Z.
by rewrite -Hratmp.

(** mflhxu atmp *)

apply hoare_mflhxu'.
move=> s h [A' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem  [Hrj [Hjk [Hrt [Hnbor [Hinv [Hratmp [Hrbtmp [Hnth [Hrbtmp2 [Hm1 [Hm2 Hrbor]]]]]]]]]]]]]]]]]]].

case: (Z_lt_le_dec (u2Z (A `32_ nj)) (u2Z [btmp]_s)).
- move/ltZP => X.
  rewrite X in Hrbor.
  move/ltZP in X.
  exists A', nj, (u2Z one32); repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  by rewrite Hrbor.
  by rewrite Z2uK.
  move: {Hm1 Hm2}(Hm2 X) => Hm.
  have Hacx0 : store.acx s = Z2u store.acx_size 0 by apply store.utoZ_acx_beta2; rewrite Hm; omega.
  rewrite store.utoZ_def Hacx0{Hacx0} Z2uK // in Hm.
  rewrite mul0Z addZ0 in Hm.
  rewrite (_ : \B^2 = \B^1 * (\B^1 - 1) + \B^1) // addZC (mulZC (\B^1)) in Hm.
  rewrite (_ : forall a b c d, a + b + c - d = a + (b + c - d)) in Hm; last by (move=> *; ring).
  apply poly_eq_inv in Hm; last first.
    rewrite Zbeta1E.
    split; first exact: min_u2Z.
    split; first by split; [apply min_u2Z | apply max_u2Z].
    split; first by [].
    move: (min_u2Z (A `32_ nj)) (max_u2Z [btmp]_s) => ? ?; omega.
  case: Hm => _ ->.
  rewrite Hinv (Zbeta_S nj) Hrbtmp2 Z2uK //; ring.
- move/leZNgt/ltZP/negbTE => X.
  rewrite X in Hrbor.
  move/ltZP/leZNgt in X.
  exists A', nj, (u2Z zero32); repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  by rewrite Hrbor.
  by rewrite Z2uK.
  move: {Hm1 Hm2}(Hm1 X) => Hm.
  have Hm_Zbeta1 : store.utoZ s < \B^1.
    move: (max_u2Z (A `32_ nj)) (min_u2Z [btmp]_s).
    rewrite Hm -Zbeta1E => ? ?; omega.
  case/store.utoZ_lo_beta1 : Hm_Zbeta1 => _ [_ <-].
  rewrite Hinv Hm Hrbtmp2 Z2uK //; ring.

(** nop; *)

apply hoare_nop'.

(** we are in the branch where btmp = atmp + bor has overflowed *)

move=> s h [[A' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk [Hrt [Hrbor [Hnbor [Hinv [Hnth [Hratmp [Hrbtmp Hru]]]]]]]]]]]]]]]]] Huzero].
rewrite /= in Huzero. move/negbTE/eqP in Huzero.
exists A', nj, nbor; repeat Reg_upd; repeat (split; trivial).
have [X1 X2] : nbor = 1 /\ u2Z (B `32_ nj) = \B^1 - 1.
  have H : u2Z [btmp]_s < u2Z (B `32_ nj).
    apply/ltZP.
    apply: Bool.not_false_is_true => X; by rewrite Hru X in Huzero.
  rewrite Hrbtmp in H.
  apply u2Z_add_overflow' in H; rewrite -Zbeta1E in H.
  move: (max_u2Z (B `32_ nj)) => H'; rewrite -Zbeta1E in H'; omega.
rewrite Hratmp Hinv X1 X2 !mul1Z (Zbeta_S nj); ring.

(** sw atmp zero16 t; *)

apply hoare_sw_back'' with (fun s h => exists A' nj nbor,
 size A' = nk /\ [a]_s = va /\ [b]_s = vb /\
 u2Z [k]_s = Z_of_nat nk /\ (var_e a |--> A' ** var_e b |--> B) s h /\
 u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
 u2Z [t]_s = u2Z va + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
 nbor <= 1 /\ \S_{ S nj } A' = \S_{ S nj } A - \S_{ S nj } B + nbor * \B^nj.+1 /\
 drop (S nj) A = drop (S nj) A').

move=> s h [A' [nj [nbor [HlenA' [Hra [Hrb [Hrk [Hmem [Hrj [Hjk [Hrt [Hnth [Hrbor [Hnbor Hinv]]]]]]]]]]]]]].

have Htmp : [ var_e t \+ int_e (sext 16 zero16) ]e_ s = [ var_e a \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) ]e_ s.
  rewrite /= sext_Z2u // addi0.
  apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat.
  rewrite inj_mult Hrt Hra; ring.
  rewrite inj_mult -Zbeta1E Hra; simpl Z_of_nat; ssromega.

exists (int_e (A' `32_ nj)).
Decompose_32 A' nj A'1 A'2 HlenA'1 HA''; last by ssromega.

rewrite HA'' (decompose_equiv _ _ _ _ _ HlenA'1) !assert_m.conAE assert_m.conCE
  !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // ht.
exact/mapsto_ext.
apply currying => h' H'; simpl app in H'.
exists (upd_nth A' nj [atmp]_s), nj, nbor; repeat (split; trivial).
exact: size_upd_nth.
rewrite HA'' upd_nth_cat HlenA'1 // subnn /= (decompose_equiv _ _ _ _ _ HlenA'1).
rewrite cat0s in H'.
assoc_comm H'.
exact: mapsto_ext H'.

rewrite HA'' -cat1s.
rewrite catA upd_nth_cat'; last by rewrite size_cat /= HlenA'1; ssromega.
rewrite upd_nth_cat; last by rewrite HlenA'1; ssromega.
rewrite HlenA'1 subnn; simpl upd_nth; rewrite -lSum_beyond; last by rewrite size_cat /= HlenA'1 addnC.
rewrite (lSum_cut_last _ A'1) //; last by rewrite size_cat /= HlenA'1 addnC.
rewrite HA'' -lSum_beyond // in Hinv.
rewrite subn1 [_.+1.-1]/= -/(\B^nj) mulZC Hinv.

Decompose_32 A nj A1 A2 HlenA1 HA'; last by ssromega.
rewrite {3}HA' -cat1s.
rewrite -> catA. rewrite -lSum_beyond; last by rewrite size_cat /= HlenA1 addnC.
rewrite (lSum_cut_last _ A1) //; last by rewrite size_cat /= HlenA1 addnC.
rewrite -/(_ `32_ nj) subn1 [_.+1.-1]/=.

Decompose_32 B nj B1 B2 HlenB1 HB'; last by ssromega.
rewrite {3}HB' -[in X in _ = _ + _ - X + _]cat1s.
rewrite -> catA. rewrite -lSum_beyond; last by rewrite size_cat /= HlenB1 addnC.
rewrite (lSum_cut_last _ B1) //; last by rewrite size_cat /= HlenB1 addnC.
rewrite -/(_ `32_ nj) subn1 [_.+1.-1]/=.

rewrite HB' -lSum_beyond //.
have -> : (B1 ++ (B `32_ nj :: B2)) `32_ nj = B `32_ nj.
  by rewrite /nth' nth_cat HlenB1 ltnn subnn.
rewrite HA' -lSum_beyond //.
have -> : (A1 ++ (A `32_ nj :: A2)) `32_ nj = A `32_ nj.
  by rewrite /nth' nth_cat HlenA1 ltnn subnn.
rewrite -ZbetaE /=; ring.

rewrite drop_upd_nth //.
rewrite (drop_nth zero32) in Hnth; last by rewrite Ha.
symmetry in Hnth.
rewrite (drop_nth zero32) in Hnth; last by rewrite HlenA'.
by case: Hnth.

(** addiu t t four16; *)

apply hoare_addiu with (fun s h => exists A' nj nbor,
 size A' = nk /\ [a]_s = va /\ [b]_s = vb /\
 u2Z [k]_s = Z_of_nat nk /\ (var_e a |--> A' ** var_e b |--> B) s h /\
 u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
 u2Z [t]_s = u2Z va + 4 * ((Z_of_nat nj) + 1) /\ u2Z [bor]_s = nbor /\
 nbor <= 1 /\ \S_{ S nj } A' = \S_{ S nj } A - \S_{ S nj } B + nbor * \B^nj.+1 /\ drop (S nj) A = drop (S nj) A').

move=> s h [A' [nj [nbor [HlenA' [Hra [Hrb [Hrk [Hmem [Hrj [Hjk [Hrt [Hbor [Hnbor [Hinv Hnth]]]]]]]]]]]]]].

exists A', nj, nbor; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite u2Z_add sext_Z2u // Z2uK //.
  omega.
  rewrite -Zbeta1E; ssromega.

(** addiu j j one16 *)

apply hoare_addiu'.
move=> s h [A' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk [Hrt [Hbor [Hnbor [Hinv Hnth]]]]]]]]]]]]]].

exists A', (S nj), nbor.
rewrite Z_S.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite u2Z_add sext_Z2u // Z2uK //.
- omega.
- move: (min_u2Z va) => ?; rewrite -Zbeta1E; ssromega.
Qed.

Lemma multi_sub_u_u_L_triple_B_le_A : uniq(k, a, b, t, j, u, bor, atmp, btmp, r0) ->
forall nk va vb, u2Z va + 4 * Z_of_nat nk < \B^1 ->
forall A B, size A = nk -> size B = nk -> \S_{ nk } B <= \S_{ nk } A ->
{{ fun s h => [a]_s = va /\ [b]_s = vb /\
  u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B) s h }}
 multi_sub_u_u k a b a t j u bor atmp btmp
{{ fun s h => exists A', size A' = nk /\ [a]_s = va /\
   [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
   [bor]_s = zero32 /\
   (var_e a |--> A' ** var_e b |--> B) s h /\
   \S_{ nk } A' = \S_{ nk } A - \S_{ nk } B }}.
Proof.
move=> Hset nk va vb Hna A B Ha Hb HAB.
eapply hoare_prop_m.hoare_weak; last by eapply multi_sub_u_u_L_triple; eauto.
move=> s h [A' [HlenA [Hra [Hrb [Hrk [Hmem [Hbor Hsum]]]]]]].
have X : u2Z [bor]_s = 0.
  have {}Hsum : u2Z [bor ]_ s * \B^nk + (\S_{ nk } A - \S_{ nk } B - \S_{ nk } A') = 0 * \B^nk + 0.
    rewrite Hsum; ring.
  apply poly_eq0_inv in Hsum.
  tauto.
  exact: expZ_ge0.
  move: (min_lSum nk B) (min_lSum nk A') (max_lSum nk A) (max_lSum nk A') => ????.
  rewrite ZbetaE; ssromega.
exists A'; repeat (split => //).
rewrite (_ : 0 = u2Z zero32) in X; last by rewrite Z2uK.
by move/u2Z_inj : X.
rewrite Hsum X mul0Z addZ0; reflexivity.
Qed.

End multi_sub.

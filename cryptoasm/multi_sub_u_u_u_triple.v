(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext uniq_tac machine_int.
Require Import multi_int.
Import MachineInt.
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

Lemma multi_sub_u_u_u_triple k a b c t j u bor atmp btmp :
  uniq(k, a, b, c, t, j, u, bor, atmp, btmp, r0) ->
  forall nk va vb vc, u2Z vc + 4 * Z_of_nat nk < \B^1 ->
  forall A B C, size A = nk -> size B = nk -> size C = nk ->
{{ fun s h => [ a ]_s = va /\ [ b ]_s = vb /\ [ c ]_s = vc /\
    u2Z [ k ]_s = Z_of_nat nk /\
   (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h }}
 multi_sub_u_u k a b c t j u bor atmp btmp
{{ fun s h => exists C, size C = nk /\ [ a ]_s = va /\
   [ b ]_s = vb /\ [ c ]_s = vc /\ u2Z [ k ]_s = Z_of_nat nk /\
   (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
   u2Z [bor]_s <= 1 /\
   \S_{ nk } C = \S_{ nk } A - \S_{ nk } B + u2Z [bor]_s * \B^nk }}.
Proof.
move=> Hset nk va vb vc Hnc A B C Ha Hb Hc; rewrite /multi_sub_u_u.

(** addiu j zero zero16; *)

NextAddiu.
move=> s h [Hra [Hrb [Hrc [Hrk H]]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
repeat (split; trivial).
by Assert_upd.

(** addi t c zero16 *)

NextAddiu.
move=> s h [[Hra [Hrb [Hrc [Hrk H]]]] Hj].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
repeat (split; trivial).
by Assert_upd.

(** addi bor zero zero16; *)

NextAddiu.
move=> s h [[[Hra [Hrb [Hrc [Hrk H]]]] Hj] Ht].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
repeat (split; trivial).
by Assert_upd.

(** while (bne j k) ( *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists C, exists nj, exists nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj <= nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj } C = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj).

move=> s h [[[[Hra [Hrb [Hrc [Hrk H]]]] Hj] Ht Hbor]].
exists C, O, 0; repeat (split => //).
by rewrite store.get_r0 add0i sext_Z2u // Z2uK in Hj.
rewrite Ht sext_0 addi0 Hrc; ring.
by rewrite sext_Z2u // addi0 store.get_r0 Z2uK in Hbor.

move=> s h [[C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor HInv]]]]]]]]]]]]] Hjk]]; rewrite /= in Hjk.
move/negPn/eqP in Hjk.
exists C'; repeat (split; trivial).
by rewrite Hrbor.
have -> : nk = nj by rewrite Hrj Hrk in Hjk; apply Z_of_nat_inj.
by rewrite Hrbor -HInv.

(** lwxs atmp j b; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj } C = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = B `32_ nj).

move=> s h [[C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor HInv]]]]]]]]]]]]] Hjk]];
  rewrite /= in Hjk. move/eqP in Hjk.
have {}Hjk : (nj < nk)%nat by ssromega.

exists (B `32_ nj); split.
- Decompose_32 B nj B1 B2 HlenB1 HB'; last by rewrite Hb.
  rewrite HB' (decompose_equiv _ _ _ _ _ HlenB1) !assert_m.conAE assert_m.conCE
    !assert_m.conAE  assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u Hrj inj_mult mulZC.
- rewrite /update_store_lwxs.
  exists C', nj, nbor; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** addu btmp atmp bor; *)

apply hoare_addu with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } C = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = B `32_ nj /\ [btmp]_s = B `32_ nj `+ [bor]_s).

move=> s h [C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv Hratmp]]]]]]]]]]]]]]].
exists C', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite Hratmp.

(** sltu u btmp atmp; *)

apply hoare_sltu with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } C = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [btmp]_s = B `32_ nj `+ [bor]_s /\
  [u]_s = if Zlt_bool (u2Z [btmp]_s) (u2Z (B `32_ nj)) then one32 else zero32).

move=> s h [C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hratmp Hrtmp']]]]]]]]]]]]]]]].

exists C', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite Hratmp.

(** lwxs atmp j a; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } C = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\ [btmp]_s = B `32_ nj `+ [bor]_s /\
  [u]_s = if Zlt_bool (u2Z [btmp]_s) (u2Z (B `32_ nj)) then one32 else zero32).

move=> s h [C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hrbtmp Hru]]]]]]]]]]]]]]]].

exists (A `32_ nj); split.
- Decompose_32 A nj A1 A2 HlenA1 HA'; last by rewrite Ha.
  rewrite HA' (decompose_equiv _ _ _ _ _ HlenA1) !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u Hrj inj_mult mulZC.
- rewrite /update_store_lwxs; exists C', nj, nbor; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** ifte_beq u, r0 thendo *)

apply while.hoare_seq with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\
  u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj } C + u2Z ([atmp]_s) * \B^nj = \S_{ nj } A - \S_{ nj } B +
  u2Z (A `32_ nj) * \B^nj - u2Z (B `32_ nj) * \B^nj + nbor * \B^nj.+1).

apply while.hoare_ifte.

(** addiu u r0 one16 ; *)

apply hoare_addiu with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  [u]_s = one32 /\ u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } C = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\ [btmp]_s = B `32_ nj `+ [bor]_s /\
  u2Z [btmp]_s = u2Z (B `32_ nj) + nbor).

move=> s h [[C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hratmp [Hrbtmp Hru]]]]]]]]]]]]]]]]] Hu]; rewrite /= in Hu.
rewrite store.get_r0 Z2uK // in Hu.
move/eqP in Hu.
exists C', nj, nbor; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- by rewrite add0i sext_Z2u.
- rewrite Hrbtmp -Hrbor u2Z_add //.
  apply u2Z_add_no_overflow.
  rewrite -Hrbtmp.
  apply/leZP; rewrite leZNgt'; apply/negP => X.
  by rewrite Hru X Z2uK // u2Z_Z2u in Hu.

(** multu atmp one; *)

apply hoare_multu with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  [u]_s = one32 /\ u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } C = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\ [btmp]_s = B `32_ nj `+ [bor]_s /\
  u2Z [btmp]_s = u2Z (B `32_ nj) + nbor /\
  store.utoZ s = u2Z (A `32_ nj)).

move=> s h [C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hu [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hratmp [Hrbtmp Hru]]]]]]]]]]]]]]]]]].
exists C', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.utoZ_multu Hu umul_1 (@u2Z_zext 32) Hratmp.

(** msubu btmp one; *)

apply hoare_msubu with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } C = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\ [btmp]_s = B `32_ nj `+ [bor]_s /\
  u2Z [btmp]_s = u2Z (B `32_ nj) + nbor /\
  ((u2Z [btmp]_s <= u2Z (A `32_ nj) -> store.utoZ s = u2Z (A `32_ nj) - u2Z [btmp]_s) /\
   (u2Z (A `32_ nj) < u2Z [btmp]_s -> store.utoZ s = \B^2 + u2Z (A `32_ nj) - u2Z [btmp]_s))).

move=> s h [C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hone [Hrj [Hjk [Hrt [Hrbor [Hnbor [Hinv [Hratmp [Hrbtmp [Hrbtmp2 Hm]]]]]]]]]]]]]]]]]]].
exists C', nj, nbor.
rewrite Hone umul_1.
repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- move=> H; rewrite store.msubu_utoZ Hm ?(@u2Z_zext 32) //; last exact: Z.le_ge.
  apply (@ltZ_trans \B^1) => //; exact: max_u2Z.
- move=> H; rewrite store.msubu_utoZ_overflow Hm ?(@u2Z_zext 32) //.
  apply (@ltZ_trans \B^1) => //; exact: max_u2Z.

(** sltu bor atmp btmp; *)

apply hoare_sltu with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\ nbor <= 1 /\
  \S_{ nj } C = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\
  [btmp]_s = B `32_ nj `+ Z2u 32 nbor /\
  u2Z [btmp]_s = u2Z (B `32_ nj) + nbor /\
  (u2Z [btmp]_s <= u2Z (A `32_ nj) ->
    store.utoZ s = u2Z (A `32_ nj) - u2Z [btmp]_s) /\
  (u2Z (A `32_ nj) < u2Z [btmp]_s ->
    store.utoZ s = \B^2 + u2Z (A `32_ nj) - u2Z [btmp]_s)  /\
  [bor]_s = if Zlt_bool (u2Z [atmp]_s) (u2Z [btmp]_s) then one32 else zero32).

move=> s h [C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hrt [Hrbor [Hnbor [Hinv [Hratmp [Hrbtmp [Hrbtmp2 [Hinv1 Hinv2]]]]]]]]]]]]]]]]]]].
exists C', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite -Hrbor Z2u_u2Z.

(** mflhxu atmp; *)

apply hoare_mflhxu'.

move=> s h [C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hrt [Hnbor [Hinv [Hratmp [Hrbtmp [Hrbtmp2 [Hm1 [Hm2 Hrbor]]]]]]]]]]]]]]]]]]].

case: (Z_lt_le_dec (u2Z [atmp]_s) (u2Z [btmp]_s)).
- move/ltZP => X.
  rewrite X in Hrbor.
  move/ltZP in X.
  rewrite Hratmp in X.
  exists C', nj, (u2Z one32); repeat Reg_upd.
  do 6 (split; trivial).
  by Assert_upd.
  do 4 (split; trivial).
  by rewrite Hrbor.
  split; first by rewrite Z2uK.
  move: {Hm1 Hm2}(Hm2 X) => Hm.
  have Hacx0 : store.acx s = Z2u store.acx_size 0.
    apply store.utoZ_acx_beta2; rewrite Hm.
    rewrite ltZ_subLR addZC; exact/ltZ_le_add.
  rewrite store.utoZ_def Hacx0{Hacx0} Z2uK // in Hm.
  rewrite mul0Z addZ0 in Hm.
  rewrite (_ : \B^2 = \B^1 * (\B^1 - 1) + \B^1) // addZC (mulZC (\B^1)) in Hm.
  rewrite (_ : forall a b c d, a + b + c - d = a + (b + c - d)) in Hm; last by (move=> *; ring).
  apply poly_eq_inv in Hm; last first.
    rewrite Zbeta1E.
    split; first exact: min_u2Z.
    split.
    by split; [apply min_u2Z | apply max_u2Z].
    split; first by [].
    split.
      apply/leZ_subRL/leZ_add; [exact/ltZW/max_u2Z | exact/min_u2Z].
    by apply/ltZ_subLR; rewrite addZC ltZ_add2r.
  case: Hm => _ Hm.
  rewrite Hinv Hm (Zbeta_S nj) Hrbtmp2 Z2uK //; ring.
- move/leZNgt/ltZP/negbTE => X.
  rewrite X in Hrbor.
  move/ltZP/leZNgt in X.
  rewrite Hratmp in X.
  exists C', nj, (u2Z zero32).
  repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  by rewrite Hrbor.
  by rewrite Z2uK.
  move: {Hm1 Hm2}(Hm1 X) => Hm.
  have H0 : store.utoZ s < \B^1.
    rewrite Hm.
    rewrite ltZ_subLR.
    apply (@ltZ_leZ_trans \B^1); first exact: max_u2Z.
    rewrite addZC -leZ_subLR subZZ; exact: min_u2Z.
  rewrite -(proj2 (proj2 (store.utoZ_lo_beta1 _ H0))).
  rewrite Hinv Hm Hrbtmp2 Z2uK //; ring.

(** nop); *)

apply hoare_nop'.

(** we are in the branch where btmp = atmp + bor has overflowed *)

move=> s h [[C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hrt [Hrbor [Hnbor [Hinv [Hratmp [Hrbtmp Hru]]]]]]]]]]]]]]]] Huzero]];
  rewrite /= in Huzero; move/negbTE/eqP in Huzero.
exists C', nj, nbor; repeat Reg_upd; repeat (split; trivial).
have [X1 X2] : nbor = 1 /\ u2Z (B `32_ nj) = \B^1 - 1.
  have H : u2Z [btmp]_s < u2Z (B `32_ nj).
    apply/ltZP.
    apply: Bool.not_false_is_true => X.
    by rewrite Hru X in Huzero.
  rewrite Hrbtmp in H.
  apply u2Z_add_overflow' in H; rewrite -Zbeta1E in H.
  move: (max_u2Z (B `32_ nj)) => H'; rewrite -Zbeta1E in H'; omega.
rewrite Hratmp Hinv X1 X2 !mul1Z (Zbeta_S nj); ring.

(** sw ctmp zero16 t; *)

apply hoare_sw_back'' with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj.+1 } C = \S_{ nj.+1 } A - \S_{ nj.+1 } B + nbor * \B^nj.+1).

move=> s h [C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hrt [Hrbor [Hnbor Hinv]]]]]]]]]]]]]].

have Htmp : [ var_e t \+ int_e (sext 16 zero16) ]e_s = [ var_e c \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) ]e_s.
rewrite /= sext_Z2u // addi0.
  apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat.
  rewrite inj_mult Hrt Hrc; ring.
  rewrite inj_mult -Zbeta1E Hrc. omegaz' ssromega.

exists (int_e (C' `32_ nj)).
Decompose_32 C' nj C1 C2 HlenC1 HC'; last by rewrite HlenC.
rewrite HC' (decompose_equiv _ _ _ _ _ HlenC1) in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // ht.
exact: mapsto_ext.
apply currying => h' H'; simpl app in H'.
exists (upd_nth C' nj [atmp]_s), nj, nbor.
repeat (split; trivial).
exact: size_upd_nth.
rewrite HC' upd_nth_cat HlenC1 // subnn /= (decompose_equiv _ _ _ _ _ HlenC1).
rewrite cat0s in H'.
assoc_comm H'.
exact: mapsto_ext H'.

rewrite HC' -cat1s.
rewrite -> catA.
rewrite upd_nth_cat'; last by rewrite size_cat /= HlenC1 addnC.
rewrite upd_nth_cat; last by rewrite HlenC1.
rewrite HlenC1 subnn; simpl upd_nth; simpl cat; rewrite -lSum_beyond; last first.
  by rewrite size_cat /= HlenC1 addnC.
rewrite (lSum_cut_last _ C1) //; last by rewrite size_cat /= HlenC1 addnC.
rewrite HC' -lSum_beyond // in Hinv.
rewrite subn1 [_.+1.-1]/= -/(\B^nj) mulZC Hinv.

Decompose_32 A nj A1 A2 HlenA1 HA'; last by rewrite Ha.
rewrite {3}HA' -cat1s.
rewrite -> catA.
rewrite -lSum_beyond; last by rewrite size_cat /= HlenA1 addnC.
rewrite (lSum_cut_last _ A1) //; last by rewrite size_cat /= HlenA1 addnC.
rewrite -/(_ `32_ nj) subn1 [_.+1.-1]/=.

Decompose_32 B nj B1 B2 HlenB1 HB'; last by rewrite Hb.
rewrite {3}HB' -[in X in _ = _ + _ - X + _]cat1s.
rewrite -> catA.
rewrite -lSum_beyond; last by rewrite size_cat /= HlenB1 addnC.
rewrite (lSum_cut_last _ B1) //; last by rewrite size_cat /= HlenB1 addnC.
rewrite -/(_ `32_ nj) subn1 [_.+1.-1]/=.

rewrite HA' -lSum_beyond //.
have -> : (A1 ++ (A `32_ nj :: A2)) `32_ nj = A `32_ nj.
  by rewrite /nth' nth_cat HlenA1 ltnn subnn.
rewrite HB' -lSum_beyond //.
have -> : (B1 ++ (B `32_ nj :: B2)) `32_ nj = B `32_ nj.
  by rewrite /nth' nth_cat HlenB1 ltnn subnn.
rewrite ZbetaE /=; ring.

(** addiu t t four16; *)

apply hoare_addiu with (fun s h => exists C nj nbor,
  size C = nk /\ [a]_s = va /\ [b]_s = vb /\
  [c]_s = vc /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B ** var_e c |--> C) s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vc + 4 * (Z_of_nat nj + 1) /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj.+1 } C = \S_{ nj.+1 } A - \S_{ nj.+1 } B + nbor * \B^nj.+1).

move=> s h [C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hrt [Hbor [Hnbor Hinv]]]]]]]]]]]]]].

exists C', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite u2Z_add sext_Z2u // Z2uK //.
- omega.
- rewrite -Zbeta1E; ssromega.

(** addiu j j one16 *)

apply hoare_addiu'.
move=> s h [C' [nj [nbor [HlenC [Hra [Hrb [Hrc [Hrk [Hmem [Hrj [Hjk [Hrt [Hbor [Hnbor Hinv]]]]]]]]]]]]]].

exists C', nj.+1, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite sext_Z2u // u2Z_add_Z2u //.
by rewrite Hrj Z_S.
move: (min_u2Z vc) => ?; rewrite -Zbeta1E; ssromega.
omegaz.
Qed.

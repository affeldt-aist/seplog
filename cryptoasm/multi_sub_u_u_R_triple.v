(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_tactics mips_contrib mips_tactics mapstos.
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

Variables k a b t j u bor atmp btmp' : reg.

Lemma multi_sub_u_u_R_triple : uniq(k, a, b, t, j, u, bor, atmp, btmp', r0) ->
  forall nk va vb, u2Z vb + 4 * Z_of_nat nk < \B^1 ->
  forall A B, size A = nk -> size B = nk ->
  {{ fun s h => [a]_s = va /\ [b]_s = vb /\
    u2Z [k]_s = Z_of_nat nk /\ (var_e a |--> A ** var_e b |--> B) s h }}
  multi_sub_u_u k a b b t j u bor atmp btmp'
  {{ fun s h => exists B', size B' = nk /\ [a]_s = va /\
    [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
    (var_e a |--> A ** var_e b |--> B') s h /\
    u2Z [bor]_s <= 1 /\
    \S_{ nk } B' = \S_{ nk } A - \S_{ nk } B + u2Z [bor]_s * \B^nk }}.
Proof.
move=> Hset nk va vb Hnb A B Ha Hb; rewrite /multi_sub_u_u.

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

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj <= nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } B' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  drop nj B = drop nj B').

move=> s h [[[[Hra [Hrb [Hrk H]]] Hj] Ht Hbor]].

exists B, O, 0; repeat (split => //).
by rewrite Hj store.get_r0 add0i sext_Z2u // Z2uK.
rewrite Ht sext_0 addi0 Hrb; ring.
by rewrite Hbor sext_0 addi0 store.get_r0 Z2uK.

move=> s h [[B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv Hnth]]]]]]]]]]]]] Hjk]];
  rewrite /= in Hjk. move/negPn/eqP in Hjk.
exists B'; repeat (split; trivial).
by rewrite Hrbor.
have -> : nk = nj by rewrite Hrj Hrk in Hjk; exact: Z_of_nat_inj.
by rewrite Hrbor -HInv.

(** lwxs atmp j b; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj } B' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\ drop nj B = drop nj B' /\
  [atmp]_s = B `32_ nj).

move=> s h [[B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv Hnth]]]]]]]]]]]]] Hjk]];
  rewrite /= in Hjk. move/eqP in Hjk.

have {}Hjk : (nj < nk)%nat.
  rewrite ltn_neqAle Hjk2 andbT; apply/eqP.
  rewrite Hrj Hrk in Hjk.
  contradict Hjk; by rewrite Hjk.

exists (B' `32_ nj); split.
- Decompose_32 B' nj B'1 B'2 HlenB1 HB'; last by rewrite HlenC.
  rewrite HB' (decompose_equiv _ _ _ _ _ HlenB1) in Hmem.
  rewrite assert_m.conCE !assert_m.conAE in Hmem.
  rewrite assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u Hrj inj_mult mulZC.
- rewrite /update_store_lwxs.
  exists B', nj, nbor; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  rewrite (drop_nth zero32) in Hnth; last by rewrite Hb.
  symmetry in Hnth.
  rewrite (drop_nth zero32) in Hnth; last by rewrite HlenC.
  by case: Hnth.

(** addu btmp' atmp bor; *)

apply hoare_addu with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } B' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  drop nj B = drop nj B' /\
  [atmp]_s = B `32_ nj /\ [btmp']_s = B `32_ nj `+ [bor]_s).

move=> s h [B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hnth Hratmp]]]]]]]]]]]]]]].
exists B', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite -Hratmp.

(** sltu u btmp' atmp; *)

apply hoare_sltu with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj } B' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  drop nj B = drop nj B' /\
  [btmp']_s = B `32_ nj `+ [bor]_s /\
  [u]_s = if Zlt_bool (u2Z [btmp']_s) (u2Z (B `32_ nj)) then one32 else zero32).

move=> s h [B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hnth [Hratmp Hrbtmp']]]]]]]]]]]]]]]].
exists B', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite -Hratmp.

(** lwxs atmp j a; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj } B' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj  /\
  drop nj B = drop nj B' /\ [atmp]_s = A `32_ nj /\
  [btmp']_s = B `32_ nj `+ [bor]_s /\
  [u]_s = if Zlt_bool (u2Z [btmp']_s) (u2Z (B `32_ nj)) then one32 else zero32).

move=> s h [B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hnth [Hrbtmp' Hru]]]]]]]]]]]]]]]].

exists (A `32_ nj); split.
- Decompose_32 A nj A1 A2 HlenA1 HA'; last by rewrite Ha.
  rewrite HA' (decompose_equiv _ _ _ _ _ HlenA1) !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u Hrj inj_mult mulZC.
- rewrite /update_store_lwxs.
  exists B', nj, nbor; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** ifte_beq u, zero thendo *)

apply while.hoare_seq with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\
  drop nj B = drop nj B' /\ u2Z [bor]_s = nbor /\ nbor <= 1 /\
  \S_{ nj } B' + u2Z [atmp]_s * \B^nj =
  \S_{ nj } A - \S_{ nj } B + u2Z (A `32_ nj) * \B^nj - u2Z (B `32_ nj) * \B^nj + nbor * \B^nj.+1).

apply while.hoare_ifte.

(** addiu u r0 one16; *)

apply hoare_addiu with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  [u]_s = one32 /\ u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } B' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\
  drop nj B = drop nj B' /\ [btmp']_s = B `32_ nj `+ [bor]_s /\
  u2Z [btmp']_s = u2Z (B `32_ nj) + nbor).

move=> s h [[B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HInv [Hnth [Hratmp [Hrbtmp' Hru]]]]]]]]]]]]]]]]] Huzero]; rewrite /= in Huzero.

exists B', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite add0i sext_Z2u.
rewrite Hrbtmp' -Hrbor u2Z_add //.
have X : u2Z (B `32_ nj) <= u2Z [btmp']_s.
  rewrite leZNgt => /ltZP X.
  by rewrite Hru X /zero32 /one32 ?Z2uK in Huzero.
rewrite Hrbtmp' in X; by move/u2Z_add_no_overflow in X.

(** multu atmp one; *)

apply hoare_multu with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  [u]_s = one32 /\ u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } B' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\
  drop nj B = drop nj B' /\ [btmp']_s = B `32_ nj `+ [bor]_s /\
  u2Z [btmp']_s = u2Z (B `32_ nj) + nbor /\ store.utoZ s = u2Z (A `32_ nj)).

move=> s h [B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrone [Hrj [Hjk2 [Hrt [Hrbor [Hnbor [HSum [Hnth [Hratmp [Hrbtmp' Hru]]]]]]]]]]]]]]]]]].

exists B', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite store.utoZ_multu Hrone umul_1 (@u2Z_zext 32) Hnth.

(** msubu btmp' one; *)

apply hoare_msubu with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  [u]_s = one32 /\ u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{ nj } B' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\
  drop nj B = drop nj B' /\ [btmp']_s = B `32_ nj `+ [bor]_s /\
  u2Z [btmp']_s = u2Z (B `32_ nj) + nbor /\
  ((u2Z [btmp']_s <= u2Z (A `32_ nj) -> store.utoZ s = u2Z (A `32_ nj) - u2Z [btmp']_s) /\
   (u2Z (A `32_ nj) < u2Z [btmp']_s -> store.utoZ s = \B^2 + u2Z (A `32_ nj) - u2Z [btmp']_s))).

move=> s h [B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hone [Hrj [Hjk [Hrt [Hrbor [Hnbor [Hinv [Hratmp [Hnth [Hrbtmp' [Hrbtmp'2 Hm]]]]]]]]]]]]]]]]]]].
exists B'; exists nj; exists nbor.
rewrite Hone umul_1.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
move=> H; rewrite store.msubu_utoZ Hm ?(@u2Z_zext 32) //.
apply (@ltZ_trans \B^1) => //.
exact: max_u2Z.
exact: Z.le_ge.
move=> H; rewrite store.msubu_utoZ_overflow Hm ?(@u2Z_zext 32) //.
apply (@ltZ_trans \B^1) => //; exact: max_u2Z.

(** sltu bor atmp btmp'; *)

apply hoare_sltu with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\ nbor <= 1 /\
  \S_{ nj } B' = \S_{ nj } A - \S_{ nj } B + nbor * \B^nj /\
  [atmp]_s = A `32_ nj /\
  drop nj B = drop nj B' /\
  [btmp']_s = B `32_ nj `+ Z2u 32 nbor /\
  u2Z [btmp']_s = u2Z (B `32_ nj) + nbor /\
  (u2Z [btmp']_s <= u2Z (A `32_ nj) -> store.utoZ s = u2Z (A `32_ nj) - u2Z [btmp']_s) /\
  (u2Z (A `32_ nj) < u2Z [btmp']_s -> store.utoZ s = \B^2 + u2Z (A `32_ nj) - u2Z [btmp']_s) /\
  [bor]_s = if u2Z (A `32_ nj) <? u2Z [btmp']_s then one32 else zero32).

move=> s h [B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hone [Hrj [Hjk [Hrt [Hrbor [Hnbor [Hinv [Hratmp [Hnth [Hrbtmp' [Hrbtmp'2 [Hinv1 Hinv2]]]]]]]]]]]]]]]]]]]].

exists B', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite -Hrbor Z2u_u2Z.
by rewrite -Hratmp.

(** mflhxu atmp *)

apply hoare_mflhxu'.
move=> s h [B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk [Hrt [Hnbor [Hinv [Hratmp [Hnth [Hrbtmp' [Hrbtmp'2 [Hm1 [Hm2 Hrbor]]]]]]]]]]]]]]]]]]].

case: (Z_lt_le_dec (u2Z (A `32_ nj)) (u2Z [btmp']_s)).
- move/ltZP => X.
  rewrite X in Hrbor.
  move/ltZP in X.
  exists B', nj, (u2Z one32).
  repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  by rewrite Hrbor.
  by rewrite Z2uK.
  move: {Hm1 Hm2}(Hm2 X) => Hm.
  have Hacx0 : store.acx s = Z2u store.acx_size 0.
    apply store.utoZ_acx_beta2.
    rewrite Hm; lia.
  rewrite store.utoZ_def Hacx0{Hacx0} Z2uK // mul0Z addZ0 in Hm.
  rewrite (_ : \B^2 = \B^1 * (\B^1 - 1) + \B^1) // addZC (mulZC (\B^1)) in Hm.
  rewrite (_ : forall a b c d, a + b + c - d = a + (b + c - d)) in Hm; last by move=> *; ring.
  apply poly_eq_inv in Hm; last first.
    rewrite Zbeta1E.
    split; first exact: min_u2Z.
    split.
    by split; [apply min_u2Z | apply max_u2Z].
    split; first by [].
    move: (min_u2Z (A `32_ nj)) (max_u2Z [btmp']_s) => ? ?; lia.
  case: Hm => _ Hm.
  rewrite Hinv Hm (Zbeta_S nj) Hrbtmp'2 Z2uK //; ring.
- move/leZNgt/ltZP/negbTE => X.
  rewrite X in Hrbor.
  move/ltZP/leZNgt in X.
  exists B', nj, (u2Z zero32).
  repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  by rewrite Hrbor.
  by rewrite Z2uK.
  move: {Hm1 Hm2}(Hm1 X) => Hm.
  have H0 : store.utoZ s < \B^1.
    move: (max_u2Z (A `32_ nj)) (min_u2Z [btmp']_s).
    rewrite Hm -Zbeta1E => ? ?; lia.
  case/store.utoZ_lo_beta1 : H0 => _ [_ <-].
  rewrite Hinv Hm Hrbtmp'2 Z2uK //; ring.

(** nop); *)

apply hoare_nop'.

(** we are in the branch where btmp' = atmp + bor has overflowed *)

move=> s h [[B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk [Hrt [Hrbor [Hnbor [Hinv [Hnth [Hratmp [Hrbtmp' Hru]]]]]]]]]]]]]]]] Huzero]];
  rewrite /= in Huzero. move/negbTE/eqP in Huzero.
exists B', nj, nbor.
repeat Reg_upd.
repeat (split; trivial).
have [X1 X2] : nbor = 1 /\ u2Z (B `32_ nj) = \B^1 - 1.
  have H : u2Z [btmp']_s < u2Z (B `32_ nj).
    apply/ltZP.
    apply: Bool.not_false_is_true => X.
    by rewrite Hru X in Huzero.
  rewrite Hrbtmp' in H.
  apply u2Z_add_overflow' in H; rewrite -Zbeta1E in H.
  move: (max_u2Z (B `32_ nj)) => H'; rewrite -Zbeta1E in H'; lia.
rewrite Hratmp Hinv X1 X2 !mul1Z (Zbeta_S nj); ring.

(** sw ctmp zero16 t; *)

apply hoare_sw_back'' with (fun s h => exists B' nj nbor,
  size B' = nk /\ [a]_s = va /\ [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\
  (var_e a |--> A ** var_e b |--> B') s h /\
  u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
  u2Z [t]_s = u2Z vb + 4 * Z_of_nat nj /\ u2Z [bor]_s = nbor /\
  nbor <= 1 /\ \S_{nj.+1} B' = \S_{nj.+1} A - \S_{nj.+1} B + nbor * \B^nj.+1 /\
  drop nj.+1 B = drop nj.+1 B').

move=> s h [B' [nj [nbor [HlenB' [Hra [Hrb [Hrk [Hmem [Hrj [Hjk [Hrt [Hnth [Hrbor [Hnbor Hinv]]]]]]]]]]]]]].

have Htmp : [ var_e t \+ int_e (sext 16 zero16) ]e_s = [ var_e b \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) ]e_ s.
  rewrite /= sext_Z2u // addi0.
  apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat.
  rewrite inj_mult Hrt Hrb; ring.
  rewrite inj_mult -Zbeta1E Hrb; simpl Z_of_nat; move/ltP in Hjk; lia.

exists (int_e (B' `32_ nj)).

Decompose_32 B' nj B'1 B'2 HlenB'1 HB'; last by rewrite HlenB'.

rewrite HB' (decompose_equiv _ _ _ _ _ HlenB'1) in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // ht.
exact: mapsto_ext.
apply currying => h' H'; simpl app in H'.
exists (upd_nth B' nj [atmp]_s); exists nj, nbor.
repeat (split; trivial).
exact: size_upd_nth.
rewrite HB' upd_nth_cat HlenB'1 // subnn /= (decompose_equiv _ _ _ _ _ HlenB'1).
rewrite cat0s in H'.
assoc_comm H'.
exact: mapsto_ext H'.

rewrite HB' -cat1s catA upd_nth_cat'; last first.
  rewrite size_cat/= HlenB'1 addnC /=; exact/ltP/lt_n_Sn.
rewrite upd_nth_cat; last first.
  by rewrite HlenB'1.
rewrite HlenB'1 subnn; simpl upd_nth; simpl app; rewrite -lSum_beyond; last first.
  by rewrite size_cat /= HlenB'1 addnC.
rewrite (lSum_cut_last _ B'1) //; last first.
  by rewrite size_cat /= HlenB'1 addnC.
rewrite subn1 [_.+1.-1]/=.

rewrite HB' -lSum_beyond // in Hinv.
rewrite -/(\B^nj) mulZC Hinv.

Decompose_32 A nj A1 A2 HlenA1 HA'; last by rewrite Ha.

rewrite {3}HA' -cat1s catA -lSum_beyond; last first.
  by rewrite size_cat /= HlenA1 addnC.
rewrite (lSum_cut_last _ A1) //; last by rewrite size_cat/= HlenA1 addnC.
rewrite -/(_ `32_ nj) subn1 [_.+1.-1]/=.

Decompose_32 B nj B1 B2 HlenB1 HB_; last by rewrite Hb.
rewrite {3}HB_ -(cat1s (B `32_ nj)) catA -lSum_beyond //; last first.
  by rewrite size_cat /= HlenB1 addnC.
rewrite (lSum_cut_last _ B1) //; last by rewrite size_cat /= HlenB1 addnC.
rewrite -/(_ `32_ nj) subn1 [_.+1.-1]/= HA' -lSum_beyond //.
rewrite ( _ : (A1 ++ (A `32_ nj :: A2)) `32_ nj = A `32_ nj); last first.
  by rewrite /nth' nth_cat HlenA1 ltnn subnn /=.
rewrite  HB_ -lSum_beyond //.
rewrite ( _ : (B1 ++ (B `32_ nj :: B2)) `32_ nj = B `32_ nj); last first.
  by rewrite /nth' nth_cat HlenB1 ltnn subnn /=.
rewrite -ZbetaE /=; ring.

rewrite drop_upd_nth //.
rewrite (drop_nth zero32) in Hnth; last by rewrite Hb.
symmetry in Hnth.
rewrite (drop_nth zero32) in Hnth; last by rewrite HlenB'.
by case: Hnth.

(** addiu t t four16; *)

apply hoare_addiu with (fun s h => exists B' nj nbor,
 length B' = nk /\ [a]_s = va /\ [b]_s = vb /\
 u2Z [k]_s = Z_of_nat nk /\ (var_e a |--> A ** var_e b |--> B') s h /\
 u2Z [j]_s = Z_of_nat nj /\ (nj < nk)%nat /\
 u2Z [t]_s = u2Z vb + 4 * (Z_of_nat nj + 1) /\ u2Z [bor]_s = nbor /\ nbor <= 1 /\
 \S_{nj.+1} B' = \S_{nj.+1} A - \S_{nj.+1} B + nbor * \B^nj.+1 /\ drop nj.+1 B = drop nj.+1 B').

move=> s h [B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk [Hrt [Hbor [Hnbor [Hinv Hnth]]]]]]]]]]]]]].

move/ltP in Hjk.
exists B', nj, nbor; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
exact/ltP.
rewrite u2Z_add sext_Z2u // Z2uK //.
- lia.
- rewrite -Zbeta1E; lia.

(** addiu j j one16 *)

apply hoare_addiu'.
move=> s h [B' [nj [nbor [HlenC [Hra [Hrb [Hrk [Hmem [Hrj [Hjk [Hrt [Hbor [Hnbor [Hinv Hnth]]]]]]]]]]]]]].

exists B', nj.+1, nbor.
rewrite Z_S.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

rewrite sext_Z2u // u2Z_add_Z2u //.
by rewrite Hrj.
move/ltP in Hjk.
move: (min_u2Z vb) => ?; rewrite -Zbeta1E; lia.
Qed.

Lemma multi_sub_u_u_R_triple_B_le_A : uniq(k, a, b, t, j, u, bor, atmp, btmp', r0) ->
  forall nk va vb, u2Z vb + 4 * Z_of_nat nk < \B^1 ->
  forall A B, size A = nk -> size B = nk -> \S_{ nk } B <= \S_{ nk } A ->
  {{ fun s h =>
    [a]_s = va /\ [b]_s = vb /\
    u2Z [k]_s = Z_of_nat nk /\ (var_e a |--> A ** var_e b |--> B) s h }}
  multi_sub_u_u k a b b t j u bor atmp btmp'
  {{ fun s h => exists B', size B' = nk /\ [a]_s = va /\
    [b]_s = vb /\ u2Z [k]_s = Z_of_nat nk /\ [bor]_s = zero32 /\
    (var_e a |--> A ** var_e b |--> B') s h /\
    \S_{ nk } B' = \S_{ nk } A - \S_{ nk } B }}.
Proof.
move=> Hset nk va vb Hna A B Ha Hb HAB.
eapply hoare_prop_m.hoare_weak; last by eapply multi_sub_u_u_R_triple; eauto.
move=> s h [A' [HlenA [Hra [Hrb [Hrk [Hmem [Hbor Hsum]]]]]]].
have X : u2Z [bor]_s = 0.
  have {}Hsum : u2Z [bor ]_ s * \B^nk + (\S_{ nk } A - \S_{ nk } B - \S_{ nk } A') = 0 * \B^nk + 0.
    rewrite Hsum; ring.
  apply poly_eq0_inv in Hsum.
  tauto.
  exact: expZ_ge0.
  move: (min_lSum nk B) (min_lSum nk A') (max_lSum nk A) (max_lSum nk A') => ????.
  rewrite ZbetaE; lia.
exists A'; repeat (split => //).
rewrite (_ : 0 = u2Z zero32) in X; last by rewrite Z2uK.
by move/u2Z_inj : X.
rewrite Hsum X mul0Z addZ0; reflexivity.
Qed.

End multi_sub.

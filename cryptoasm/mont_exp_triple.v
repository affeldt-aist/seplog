(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int multi_int uniq_tac.
Import MachineInt.
Require Import mips_seplog mips_frame mips_contrib mips_tactics mapstos.
Require Import mont_mul_strict_prg mont_exp_prg.
Require Import mont_mul_strict_init_triple mont_square_strict_init_triple.

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

Lemma mont_exp_specif (k alpha x a' x' i l a ei e one' m one ext int_ X_ Y_ M_ Z_ quot C t s_ : reg) :
  uniq(k, alpha, x, a, a', m, one, ext, int_, X_, Y_, M_, Z_, quot, C, x', t, s_, i, e, ei, l, one', r0) ->
  forall nk valpha M, u2Z (M `32_ 0) * u2Z valpha =m -1 {{ \B^1 }} ->
  forall ve vl, (*vl = number_of_significant_bits of ve*) u2Z ve < 2 ^^ vl -> (vl < 32)%nat ->
  forall va (A : list (int 32)) va' (A' : list (int 32)) vx X vx' vone' ONE' vm,
  size A = nk -> size A' = nk -> size X = nk -> size ONE' = nk -> size M = nk ->
  u2Z va + 4 * Z_of_nat nk.+1 < \B^1 ->
  u2Z va' + 4 * Z_of_nat nk.+1 < \B^1 ->
  u2Z vx' + 4 * Z_of_nat nk.+1 < \B^1 ->
  \S_{ nk } A =m \B^nk {{ \S_{ nk } M }} -> \S_{ nk } A' =m \B^(2 * nk) {{ \S_{ nk } M }} ->
  \S_{ nk } X < \S_{ nk } M -> \S_{ nk } A < \S_{ nk } M -> \S_{ nk } A' < \S_{ nk } M -> \S_{ nk } ONE' < \S_{ nk } M ->
  \S_{ nk } ONE' = 1 -> Zodd (\S_{ nk } M) ->
  {{ fun s h => exists X', size X' = nk /\ [x]_s = vx /\ [a']_s = va' /\
    [x']_s = vx' /\ [m]_s = vm /\ u2Z ([k]_s) = Z_of_nat nk /\ [alpha]_s = valpha /\
    [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\ [a]_s = va /\ [one']_s = vone' /\
    (var_e x |--> X ** var_e a |--> A ++ zero32 :: nil ** var_e a' |--> A' ++ zero32 :: nil **
      var_e x' |--> X' ++ zero32 :: nil ** var_e one' |--> ONE' ** var_e m |--> M ++ zero32 :: nil) s h}}
  mont_exp k alpha x a' x' i l a ei e one' m one ext int_ X_ Y_ M_ Z_ quot C t s_
  {{ fun s h => exists A A' X' new_va new_va',
    size A = nk /\ size A' = nk /\ size X' = nk /\ u2Z [k]_s = Z_of_nat nk /\
    [alpha]_s = valpha /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
    [a]_s = new_va /\ u2Z new_va + 4 * Z_of_nat nk.+1 < \B^1 /\
    [a']_s = new_va' /\ u2Z new_va' + 4 * Z_of_nat nk.+1 < \B^1 /\
    [x]_s = vx /\ [x']_s = vx' /\ [one']_s = vone' /\ [m]_s = vm /\
    (var_e a |--> A ++ zero32 :: nil ** var_e a' |--> A' ++ zero32 :: nil ** var_e x |--> X **
      var_e x' |--> X' ++ zero32 :: nil ** var_e one' |--> ONE' ** var_e m |--> M ++ zero32 :: nil) s h /\
    \S_{ nk } A' =m (\S_{ nk } X) ^^ Z.abs_nat (u2Z [e]_s) {{ \S_{ nk } M }} }}.
Proof.
move=> Hset nk valpha M Halpha ve vl Hvevl Hvl va A va' A' vx X
  vx' vone' ONE' vm HlenA HlenA' HlenX HlenONE' HlenM
  Hna Hna' Hxn' HA HA' HSumXSumM HSumA HSumA'SumM HSumONE' HSumONE'_is_1 HZoddM.
rewrite /mont_exp.

(** mont_mul_strict_init k alpha x a' x' m one ext int_ X_ Y_ M_ Z_ quot C t s_ ; *)

apply (hoare_prop_m.hoare_stren ((fun s h => exists X', size X' = nk /\
  [x]_s = vx /\ [a']_s = va' /\ [x']_s = vx' /\ [m]_s = vm /\
  u2Z ([k]_s) = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e a' |--> A' ** var_e x' |--> X' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h) **
(fun s h => [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\ [a]_s = va /\  [one']_s = vone' /\
  (var_e a |--> A ++ zero32 :: nil **
  var_e a' \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 ** var_e one' |--> ONE') s h))).

move=> s h [X' [HlenX' [r_x [r_a' [r_x' [r_m [r_k [r_alpha [r_e [r_l [r_a [r_one' Hmem]]]]]]]]]]]].

have {}Hmem :
  ((var_e x |--> X ** var_e a' |--> A' ** var_e x' |--> X' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) **
   (var_e a |--> A ++ zero32 :: nil ** var_e a' \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 ** var_e one' |--> ONE')) s h.
  rewrite (decompose_last_equiv _ A') HlenA' in Hmem.
  by assoc_comm Hmem.
case: Hmem => h1 [h2 [Hdisj [Hunion [Hmem1 Hmem2]]]].
exists h1, h2; repeat (split; trivial).
by exists X'.

apply while.hoare_seq with ((fun s h => exists X', size X' = nk /\ [x]_s = vx /\
  [a']_s = va' /\ [x']_s = vx' /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\
  (var_e x |--> X ** var_e a' |--> A' ** var_e x' |--> X' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  \S_{ nk } X' =m \S_{ nk } X * \B^nk {{ \S_{ nk } M }} /\ \S_{ nk } X' < \S_{ nk } M) **
(fun s h => [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\ [a]_s = va /\
  [one']_s = vone' /\
  (var_e a |--> A ++ zero32 :: nil ** (var_e a' \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) ** var_e one' |--> ONE') s h)).

(* TODO: adapt before_frame to work with a sequence
Lemma before_frame : forall R P' Q' P c Q, {{ P' ** R }} c {{ Q' ** R }} ->
  P ===> P' ** R -> Q' ** R ===> Q -> {{ P }} c {{ Q }}.
Proof. move=> R P' Q' P c Q H1 H2 H3; by eapply while.hoare_conseq; eauto. Qed.
*)

apply frame_rule_R.
- apply (hoare_prop_m.hoare_weak (fun s h => exists X', size X' = nk /\
    [x]_s = vx /\ [a']_s = va' /\ [x']_s = vx' /\ [m]_s = vm /\
    u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
    (var_e x |--> X ** var_e a' |--> A' ** var_e x' |--> X' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
    \B^nk * \S_{ nk } X' =m \S_{ nk } X * \S_{ nk } A' {{ \S_{ nk } M }} /\ \S_{ nk } X' < \S_{ nk } M)).
  move=> s h [X' [HlenX' [r_x [r_a' [r_x' [r_m [r_k [r_alpha [Hmem [Sum_X'1 Sum_X'2]]]]]]]]]].
  exists X'; repeat (split; trivial).
  apply: (eqmod_reg_mult' _ _ (\B^nk)).
  apply Zis_gcd_sym; rewrite ZbetaE; exact: Zis_gcd_Zpower_odd.
  rewrite mulZC.
  eapply eqmod_trans; first exact: Sum_X'1.
  rewrite -mulZA.
  apply eqmod_reg_mult_l.
  by rewrite -ZbetaD addnn -mul2n.
  eapply mont_mul_strict_init_triple; eauto.
  by Uniq_uniq r0.
- by Inde_frame.
- move=> ?; by Inde_mult.

apply pull_out_exists_con => X'.

apply (hoare_prop_m.hoare_stren (!(fun s => size X' = nk /\
  \S_{ nk } X' =m \S_{ nk } X * \B^nk {{ \S_{ nk } M }} /\ \S_{ nk } X' < \S_{ nk } M) **
(fun s h => [x]_s = vx /\ [a]_s = va /\ [a']_s = va' /\ [x']_s = vx' /\
  [m]_s = vm /\ [one']_s = vone' /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  [e]_s = ve /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e a |--> A ++ zero32 :: nil ** var_e a' |--> A' ++ zero32::nil ** var_e x' |--> X' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e one' |--> ONE') s h))).

move=> s h [h1 [h2 [Hdisj [Hunion [[HlenX' [r_x [r_a' [r_x' [r_m [r_k [r_alpha [Hmem1 [Sum_X'1 Sum_X'2]]]]]]]]] [r_e [r_l [r_a [r_one' Hmem2]]]]]]]]].
exists heap.emp, (h1 \U h2); repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.
move: {Hmem1 Hmem2}(assert_m.con_cons _ _ _ _ _ Hdisj Hmem1 Hmem2) => Hmem.
rewrite (decompose_last_equiv _ A') HlenA'.
by abstract assoc_comm Hmem.

apply pull_out_bang; case=> HlenX' [HSumX'1 HSumX'2].

apply (hoare_prop_m.hoare_stren ((fun s h => u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  [a]_s = va /\ [a']_s = va' /\ [x']_s = vx' /\ [m]_s = vm /\
  (var_e a|--> A ++ zero32 :: nil ** var_e a'|-->A' ++ zero32 :: nil ** var_e x'|-->X' ** var_e m |-->M ++ zero32 :: nil) s h) **
(fun s h => [x]_s = vx /\ [one']_s = vone' /\
  (var_e x|-->X ** var_e x' \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 ** var_e one' |--> ONE') s h))).

move=> s h [r_x [r_a [r_a' [r_x' [r_m [r_one' [r_l [r_e [r_k [r_alpha Hmem]]]]]]]]]].

have {}Hmem : ((var_e a |--> A ++ zero32 :: nil ** var_e a' |--> A' ++ zero32 :: nil ** var_e x' |--> X' ** var_e m |--> M ++ zero32 :: nil) ** (var_e x|--> X ** var_e x' \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 ** var_e one' |--> ONE')) s h.
  rewrite (decompose_last_equiv _ X') HlenX' in Hmem.
  by abstract assoc_comm Hmem.
case: Hmem => h1 [h2 [Hdisj [Hunion [Hmem1 Hmem2]]]].
by exists h1, h2.

apply while.hoare_seq with ((fun s h => exists A A' new_va new_va',
  size A = nk /\ size A' = nk /\ u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  [a]_s = new_va /\ u2Z new_va + 4 * Z_of_nat nk.+1 < \B^1 /\
  [a']_s = new_va' /\ u2Z new_va' + 4 * Z_of_nat nk.+1 < \B^1 /\
  [x']_s = vx' /\ [m]_s = vm /\
  (var_e a|--> A ++ zero32 :: nil ** var_e a'|-->A' ++ zero32::nil ** var_e x'|-->X' ** var_e m|-->M ++ zero32 :: nil) s h /\
    \S_{ nk } A =m \S_{ nk } X ^^ (Z.abs_nat (u2Z ve)) * \B^nk {{ \S_{ nk } M }} /\ \S_{ nk } A < \S_{ nk } M) **
(fun s h => [x]_s = vx /\ [one']_s = vone' /\
  (var_e x|-->X ** var_e x' \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 ** var_e one' |--> ONE') s h)).

apply frame_rule_R.

(** (addiu i l zero16 ; *)

apply hoare_addiu with (fun s h => u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  [i]_s = Z2s 32 (Z_of_nat vl) /\ [a]_s = va /\ [a']_s = va' /\ [x']_s = vx' /\
  [m]_s = vm /\
  (var_e a|--> A ++ zero32 :: nil ** var_e a'|-->A' ++ zero32 :: nil ** var_e x'|-->X' ** var_e m |-->M ++ zero32 :: nil) s h).

move=> s h [r_k [r_alpha [r_e [r_l [r_a [r_a' [r_x' [r_m Hmem]]]]]]]].
rewrite /wp_addiu.
repeat Reg_upd.
repeat (split; trivial).
by rewrite sext_0 addi0.
by Assert_upd.

(** while (bgez i) ( *)

apply hoare_prop_m.hoare_while_invariant with (fun s h =>
  (exists A0 A'0 new_va new_va' ni,
  size A0 = nk /\ size A'0 = nk /\ u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  [a]_s = new_va /\ u2Z new_va + 4 * Z_of_nat nk.+1 < \B^1 /\
  [a']_s = new_va' /\ u2Z new_va' + 4 * Z_of_nat nk.+1 < \B^1 /\
  [x']_s = vx' /\ [m]_s = vm /\ s2Z [i]_s = ni /\ -1 <= ni <= Z_of_nat vl /\
  (var_e a |--> A0 ++ zero32::nil ** var_e a' |--> A'0 ++ zero32::nil ** var_e x' |--> X' ** var_e m |--> M ++ zero32::nil) s h /\
  \S_{ nk } A0 =m \S_{ nk } X ^^ Z.abs_nat (u2Z (ve `>> Z.abs_nat (ni+1))) * \B^nk {{ \S_{ nk } M }} /\ \S_{ nk } A0 < \S_{ nk } M)).

move=> s h [r_k [r_alpha [r_e [r_l [r_i [r_a [r_a' [r_x' [r_m Hmem]]]]]]]]].
exists A, A', va, va', (Z_of_nat vl); repeat (split; trivial).
rewrite r_i Z2sK //.
split.
  apply (@leZ_trans 0); by [| apply Zle_0_nat].
apply (@leZ_ltZ_trans 32); last by [].
rewrite (_ : 32 = Z_of_nat 32) //; by apply/inj_le/leP; rewrite ltnW.
apply (@leZ_trans 0); by [ | apply Zle_0_nat].
exact/leZZ.

have -> : ve `>> Z.abs_nat (Z_of_nat vl + 1) = zero32.
  rewrite shrl_overflow // Zabs_nat_Zplus //; last exact: Zle_0_nat.
  rewrite plus_comm [plus _ _]/= Zabs2Nat.id.
  apply (@ltZ_trans (2 ^^ vl)); by [ | apply expZ_2_lt].
by rewrite Z2uK // [Zmult]lock /= -lock mul1Z.

clear Hna'.
move=> s h [[A0 [A0' [new_va [new_va' [ni [HlenA0 [HlenA0' [r_k [r_alpha [r_e [r_l [r_a [Hnew_na [r_a' [Hna' [r_x' [r_m [r_i [Hi [Hmem [HSumA01 HSumA02]]]]]]]]]]]]]]]]]]]]] r_i'];
  rewrite /= in r_i'. move/leZP in r_i'.

have {}r_i' : s2Z [i]_s < 0.
 apply Znot_ge_lt; contradict r_i'; exact: Z.ge_le.
exists A0, A0', new_va, new_va'; repeat (split; trivial).
have Hni : ni = -1.
  rewrite r_i in r_i'; case: Hi => Hi _; lia.
by rewrite Hni //= shrl_0 in HSumA01.

clear HlenA HA A HSumA HlenA' A' HA' HSumA'SumM va Hna va' Hna'.

(** mont_mul_strict_init k alpha a a a' m one ext int_ X_ Y_ M_ Z_ quot C t s_; *)

apply (hoare_prop_m.hoare_stren (fun s h => (exists A0 ni new_va new_va' A'0,
  size A0 = nk /\ size A'0 = nk /\ u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  [a]_s = new_va /\ u2Z new_va + 4 * Z_of_nat nk.+1 < \B^1 /\
  [a']_s = new_va' /\ u2Z new_va' + 4 * Z_of_nat nk.+1 < \B^1 /\
  [x']_s = vx' /\ [m]_s = vm /\ s2Z [i]_s = ni /\ 0 <= ni <= Z_of_nat vl /\
  (var_e a |--> A0 ++ zero32 :: nil ** var_e a' |--> A'0 ++ zero32 :: nil ** var_e x' |--> X' ** var_e m |--> M ++ zero32 :: nil) s h /\
  \S_{ nk } A0 =m \S_{ nk } X ^^ Z.abs_nat (u2Z (ve `>> Z.abs_nat (ni + 1))) * \B^nk {{\S_{ nk } M}} /\ \S_{ nk } A0 < \S_{ nk } M))).

move=> s h [ [A [A' [va [va' [ni [HlenA [HlenA' [r_k [r_alpha [r_e [r_l [r_a [Hna [r_a' [Hna' [r_x' [r_m [Hni [Hni' [Hmem [HSumA1 HSumA2]]]]]]]]]]]]]]]]]]]]] Hi];
  rewrite /= in Hi. move/Zle_is_le_bool in Hi.
exists A, ni, va, va', A'; repeat (split; trivial).
by rewrite -Hni.
by case: Hni'.

apply pull_out_exists => A.
apply pull_out_exists => ni.
apply pull_out_exists => va.
apply pull_out_exists => va'.

apply (hoare_prop_m.hoare_stren (!(fun s  => size A = nk /\
  \S_{ nk } A =m \S_{ nk } X ^^ Z.abs_nat (u2Z (ve `>> Z.abs_nat (ni + 1))) * \B^nk {{ \S_{ nk } M }} /\
  \S_{ nk } A < \S_{ nk } M /\ 0 <= ni <= Z_of_nat vl /\
  u2Z va + 4 * Z_of_nat nk.+1 < \B^1 /\
  u2Z va' + 4 * Z_of_nat nk.+1 < \B^1) **
(fun s h => (exists A'0, size A'0 = nk /\ u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  [a]_s = va /\ [a']_s = va' /\ [x']_s = vx' /\ [m]_s = vm /\ s2Z [i]_s = ni /\
  (var_e a |--> A ++ zero32 :: nil ** var_e a' |--> A'0 ++ zero32 :: nil ** var_e x' |--> X' ** var_e m |--> M ++ zero32 :: nil) s h)))).

move=> s h [A' [HlenA [HlenA' [r_k [r_alpha [r_e [r_l [r_a [Hna [r_a' [Hna' [r_x' [r_m [r_i [Hni [Hmem [HSumA1 HsumA2]]]]]]]]]]]]]]]]].
exists heap.emp, h; repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.
by exists A'.

apply pull_out_bang; case=> HlenA [HSumA1 [HSumA2 [Hni [Hna Hna']]]].

apply while.hoare_seq with ((fun s h => exists A'0, size A'0 = nk /\ [a]_s = va /\ [a']_s = va' /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e a|-->A ** var_e a'|-->A'0 ++ zero32 :: nil ** var_e m|-->M ++ zero32 :: nil) s h /\
  \B^nk * \S_{ nk } A'0 =m \S_{ nk } A * \S_{ nk } A {{ \S_{ nk } M }} /\ \S_{ nk } A'0 < \S_{ nk } M) **
((fun s h => s2Z [i]_s = ni /\ [x']_s = vx' /\
  [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl)) //\\
(var_e x'|-->X' ** var_e a \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32))).

apply (hoare_prop_m.hoare_stren ((fun s h => exists A'0, size A'0 = nk /\ [a]_s = va /\
  [a']_s = va' /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e a |--> A ** var_e a' |--> A'0 ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h) **
((fun s h => s2Z [i]_s = ni /\ [x']_s = vx' /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl)) //\\
  (var_e x' |--> X' ** var_e a \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32)))).

move=> s h [A' [HlenA' [r_k [r_alpha [r_e [r_l [r_a [r_a' [r_x' [r_m [r_i Hmem]]]]]]]]]]].

have {}Hmem : ((var_e a |--> A  ** var_e a' |--> A' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) **
  (var_e x' |--> X' ** var_e a \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32)) s h.
  rewrite (decompose_last_equiv _ A) HlenA in Hmem.
  by abstract assoc_comm Hmem.
case: Hmem => h1 [h2 [Hdisj [Hunion [H1 H2]]]].
exists h1, h2; repeat (split; trivial).
by exists A'.

apply frame_rule_R.
- eapply mont_square_strict_init_triple => //.
  by abstract Uniq_uniq r0.
- by Inde_frame.
- move=> ?; by Inde_mult.

apply pull_out_exists_con => A'.

apply (hoare_prop_m.hoare_stren (!(fun s => size A' = nk /\
  \B^nk * \S_{ nk } A' =m \S_{ nk } A * \S_{ nk } A {{\S_{ nk } M}} /\ \S_{ nk } A' < \S_{ nk } M) **
(fun s h => exists A, size A = nk /\ [a']_s = va' /\ [x']_s = vx' /\ [a]_s = va /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e a' |--> A' ++ zero32 :: nil ** var_e x' |--> X' ** var_e a |--> A ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  s2Z [i]_s = ni /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl)))).

move=> s h [h1 [h2 [Hdisj [Hunion [[HlenA' [r_a [r_a' [r_m [r_k [r_alpha [Hmem [HSumA'1 HSumA'2]]]]]]]] [[r_i [r_x' [r_e H1]]] Hmem2]]]]]].

exists heap.emp, (h1 \U h2); repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.

exists A; repeat (split; trivial).
move: {Hmem Hmem2}(assert_m.con_cons _ _ _ _ _ Hdisj Hmem Hmem2) => Hmem.
rewrite (decompose_last_equiv _ A) HlenA.
by abstract assoc_comm Hmem.

apply pull_out_bang; case=> HlenA' [HSumA'1 HSumA'2].
apply eqmod_sym in HSumA'1.
move: {HSumA'1}(eqmod_rewrite _ _ _ _ _ HSumA1 HSumA'1) => HSumA'1.
rewrite mulZC in HSumA'1.
move: {HSumA1 HSumA'1}(eqmod_rewrite _ _ _ _ _ HSumA1 HSumA'1) => HSumA'1.
apply eqmod_sym in HSumA'1.
rewrite mulZC mulZA in HSumA'1.
apply eqmod_reg_mult' in HSumA'1; last first.
  apply Zis_gcd_sym; rewrite ZbetaE; exact: Zis_gcd_Zpower_odd.
rewrite -(mulZC (\B^nk)) -mulZA -ZpowerD in HSumA'1.
rewrite addnn -mul2n mulZC in HSumA'1.

clear A HlenA HSumA2.

(** srlv ei e i ; *)

apply hoare_srlv with (fun s h => exists A, size A = nk /\ [a']_s = va' /\
  [x']_s = vx' /\ [a]_s = va /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\
  (var_e a' |--> A' ++ zero32 :: nil ** var_e x' |--> X' ** var_e a |--> A ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  s2Z [i]_s = ni /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\ [ei]_s = ve `>> (Z.abs_nat ni)).

move=> s h [A [HlenA [r_a' [r_x' [r_a [r_m [r_k [r_alpha [Hmem [r_i [r_e r_l]]]]]]]]]]].
rewrite /wp_srlv.
repeat Reg_upd.
exists A; repeat (split; trivial).

by Assert_upd.
rewrite u2Z_rem' //; last first.
  rewrite -s2Z_u2Z_pos /= r_i.
  apply (@leZ_ltZ_trans (Z_of_nat vl)); first by case: Hni.
  apply (@ltZ_leZ_trans  (Z_of_nat 32)) => //; exact/inj_lt/ltP.
by case: Hni.
rewrite -s2Z_u2Z_pos; last by rewrite r_i; case: Hni.
by rewrite r_i r_e.

(** andi ei ei one16 ; *)

apply hoare_andi with (fun s h => exists A, size A = nk /\ [a']_s = va' /\
  [x']_s = vx' /\ [a]_s = va /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\
  [alpha]_s = valpha /\
  (var_e a' |--> A' ++ zero32 :: nil ** var_e x' |--> X' ** var_e a |--> A ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  s2Z [i]_s = ni /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  u2Z [ei]_s + 2 * u2Z (ve `>> Z.abs_nat (ni + 1)) = u2Z (ve `>> Z.abs_nat ni) /\
  ([ei]_s = zero32 \/ [ei]_s = one32)).

move=> s h [A [HlenA [r_a' [r_x' [r_a [r_m [r_k [r_alpha [Hmem [r_i [r_e [r_l r_ei]]]]]]]]]]]].
rewrite /wp_andi.
repeat Reg_upd.
exists A; repeat (split; trivial).
by Assert_upd.

rewrite r_ei /one16 zext_Z2u // int_and_rem_1 Zabs_nat_Zplus //; last by exact (proj1 Hni).
rewrite -shrl_comp mulZC addZC u2Z_shrl //; rewrite (_ : Z.abs_nat 1 = 1%nat) //; by repeat constructor.
rewrite zext_Z2u //.
case: (Zeven_odd_dec (u2Z [ei]_s)).
- move/int_even_and_1 => ->; by left.
- move/int_odd_and_1 => ->; by right.

(** ifte_beq ei, r0 thendo *)

apply while.hoare_seq with (fun s h => exists A A' new_va new_va',
  size A = nk /\ size A' = nk /\ [a']_s = new_va' /\
  u2Z new_va' + 4 * Z_of_nat nk.+1 < \B^1 /\
  [x']_s = vx' /\ [a]_s = new_va /\ u2Z new_va + 4 * Z_of_nat nk.+1 < \B^1 /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e a |--> A ++ zero32::nil ** var_e x' |--> X' ** var_e a' |--> A' ++ zero32::nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  \S_{ nk } A =m \S_{ nk } X ^^ Z.abs_nat ((2 * u2Z (ve `>> Z.abs_nat (ni+1))) + u2Z((ve `>> Z.abs_nat ni) `& one32)) * \B^nk {{ \S_{ nk } M }} /\
  \S_{ nk } A < \S_{ nk } M /\ s2Z [i]_s = ni /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  u2Z [ei]_s + 2 * u2Z (ve `>> Z.abs_nat (ni + 1)) = u2Z (ve `>> Z.abs_nat ni)).

apply while.hoare_ifte.

(**  (xor a a a'; *)

apply hoare_xor with (fun s h => exists A, size A = nk /\ [a']_s = va' /\
  [x']_s = vx' /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (((var_e a' |--> A' ++ zero32 :: nil ** var_e x' |--> X') ** int_e va |--> A ++ zero32 :: nil) ** var_e m |--> M ++ zero32 :: nil) s h /\
  s2Z [i]_s = ni /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  u2Z [ei]_s + 2 * u2Z (ve `>> Z.abs_nat (ni + 1)) = u2Z (ve `>> Z.abs_nat ni) /\
  [ei]_s = zero32 /\ [a]_s = va `(+) va').

move=> s h [[A [HlenA [r_a' [r_x' [r_a [r_m [r_k [r_alpha [Hmem [r_i [r_e [r_l [r_ei r_ei']]]]]]]]]]]]] Heqei0];
  rewrite /= in Heqei0. move/eqP in Heqei0.

rewrite /wp_xor.
repeat Reg_upd.
exists A; repeat (split; trivial).
Assert_upd.
assoc_comm Hmem.
move: Hmem.
exact: mapstos_ext.
by move/u2Z_inj : Heqei0.
by rewrite -r_a -r_a'.

(**  xor a' a a'; *)

apply hoare_xor with (fun s h => exists A, size A = nk /\ [x']_s = vx' /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (((int_e va' |--> A' ++ zero32 :: nil ** var_e x' |--> X') ** int_e va |--> A ++ zero32 :: nil) ** var_e m |--> M ++ zero32 :: nil) s h /\
  s2Z [i]_s = ni /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  u2Z [ei]_s + 2 * u2Z (ve `>> Z.abs_nat (ni + 1)) = u2Z (ve `>> Z.abs_nat ni) /\
  [ei]_s = zero32 /\ [a]_s = va `(+) va' /\ [a']_s = va' `(+) (va `(+) va')).

move=> s h [A [HlenA [r_a' [r_x' [r_m [r_k [r_alpha [Hmem [r_i [r_e [r_l [r_ei [r_ei' r_a]]]]]]]]]]]]].

rewrite /wp_xor.
repeat Reg_upd.
exists A; repeat (split; trivial).
Assert_upd.
assoc_comm Hmem.
by move: Hmem; apply mapstos_ext.
by rewrite r_a r_a' int_xorC.

(**  xor a a a')
 elsedo *)

apply hoare_xor'.

move=> s h [A [HlenA [r_x' [r_m [r_k [r_alpha [Hmem [r_i [r_e [r_l [r_ei [r_ei' [r_a r_a']]]]]]]]]]]]].

rewrite /wp_xor.
repeat Reg_upd.
exists A', A, va', va; repeat (split; trivial).
by rewrite r_a' int_xorC int_xorA int_xor_self int_xor_0.
by rewrite r_a' r_a int_xorC int_xorA int_xor_self int_xor_0.

(* NB: here, the "strategy" implemented by Assert_upd fails *)
move: Hmem.
rewrite 2!conAE.
apply monotony => h'.
apply mapstos_ext => //=.
Reg_upd.
by rewrite r_a r_a' /= int_xorC int_xorA int_xor_self int_xor_0.
apply monotony => h''.
apply mapstos_ext => //=.
by Reg_upd.
apply monotony => h'''.
apply mapstos_ext => //=.
Reg_upd.
by rewrite /= r_a' int_xorC int_xorA int_xor_self int_xor_0.
apply mapstos_ext => //=.
by Reg_upd.

rewrite Zabs_nat_Zplus; last 2 first.
  apply mulZ_ge0 => //; exact: min_u2Z.
  exact: min_u2Z.
apply: (eqmod_trans _ _ _ _ HSumA'1).
apply eqmod_reg_mult.
rewrite Zabs_nat_mult (_ : Z.abs_nat 2 = 2%nat); last by [].
rewrite int_even_and_1; last first.
  rewrite -r_ei r_ei' Z2uK // add0Z; exact: Zeven_2.
rewrite Z2uK // [Z.abs_nat 0]/= plusE addn0; exact: eqmod_refl.

(**  mont_mul_strict_init k alpha a' x' a m one ext int_ X_ Y_ M_ Z_ quot C t s_; *)

apply (hoare_prop_m.hoare_stren ((fun s h => exists A, size A = nk /\
  [a']_s = va' /\ [x']_s = vx' /\ [a]_s = va /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e a' |--> A' ** var_e x' |--> X' ** var_e a |--> A ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h) **
((fun s _ => s2Z [i]_s = ni /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  u2Z [ei]_s + 2 * u2Z (ve `>> Z.abs_nat (ni + 1)) = u2Z (ve `>> Z.abs_nat ni) /\ [ei]_s = one32) //\\
 (var_e a' \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32)))).

move=> s h [ [A [HlenA [r_a' [r_x' [r_a [r_m [r_k [r_alpha [Hmem [r_i [r_e [r_l [r_ei r_ei']]]]]]]]]]]]] Hbneei0];
  rewrite /= in Hbneei0. move/eqP in Hbneei0.

have {}Hmem : ((((var_e a' |--> A' ** var_e x' |--> X') ** var_e a |--> A ++ zero32 :: nil) ** var_e m |--> M ++ zero32 :: nil) ** (var_e a' \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32)) s h.
  rewrite (decompose_last_equiv _ A') HlenA' in Hmem.
  by abstract assoc_comm Hmem.
case: Hmem => h1 [h2 [Hdisj [Hunion [Hmem1 Hmem2]]]].
exists h1, h2; repeat (split; trivial).
exists A; repeat (split; trivial).
by rewrite -2!conAE.
case: r_ei' => r_ei' //.
by rewrite store.get_r0 r_ei' in Hbneei0.

apply hoare_prop_m.hoare_weak with ((fun s h => exists A, size A = nk /\
  [a']_s = va' /\ [x']_s = vx' /\ [a]_s = va /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e a' |--> A' ** var_e x' |--> X' ** var_e a |--> A ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  \B^nk * \S_{ nk } A =m \S_{ nk } A' * \S_{ nk } X' {{ \S_{ nk } M }} /\ \S_{ nk } A < \S_{ nk } M) **
((fun s m => s2Z [i]_s = ni /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  u2Z [ei]_s + 2 * u2Z (ve `>> Z.abs_nat (ni + 1)) = u2Z (ve `>> Z.abs_nat ni) /\ [ei]_s = one32) //\\
 (var_e a' \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32))).

move=> s h [h1 [h2 [Hdisj [Hunion [[A [HlenA [r_a' [r_x' [r_a [r_m [r_k [r_alpha [Hmem1 [Sum_A1 Sum_A2]]]]]]]]]] [[r_i [r_e [r_l [r_ei r_ei']]]] Hmem2]]]]]].

exists A, A', va, va'; repeat (split; trivial).
rewrite (decompose_last_equiv _ A') HlenA'.
move: {Hmem1 Hmem2}(assert_m.con_cons _ _ _ _ _ Hdisj Hmem1 Hmem2) => Hmem.
rewrite -Hunion in Hmem.
by abstract assoc_comm Hmem.

apply: (eqmod_reg_mult_beta_odd _ _ nk _ HZoddM).
apply: (eqmod_trans _ _ _ _ Sum_A1).
apply eqmod_sym in HSumA'1; apply: (eqmod_rewrite _ _ _ _ _ HSumA'1).
rewrite mulZC.
apply eqmod_sym in HSumX'1; apply: (eqmod_rewrite _ _ _ _ _ HSumX'1).

rewrite mulZA mulZC.

apply eqmod_reg_mult_l.
rewrite mulZC mulZA.
apply eqmod_reg_mult.
rewrite mulZC -ZpowerS int_odd_and_1; last first.
  rewrite -r_ei r_ei' Z2uK // addZC.
  exact: Zodd_1.
rewrite Z2uK //.
apply eqmod_sym.
rewrite Zabs_nat_Zplus //; last by apply mulZ_ge0; [ | exact: min_u2Z].
rewrite Zabs_nat_mult plusE addnC; exact: eqmod_refl.

apply frame_rule_R.
- eapply mont_mul_strict_init_triple => //.
  by abstract Uniq_uniq r0.
- by Inde_frame.
- move=> ?; by Inde_mult.

clear HSumA'1 HSumA'2 HlenA' A'.

apply pull_out_exists => A.
apply pull_out_exists => A'.
clear va Hna va' Hna'.
apply pull_out_exists => va.
apply pull_out_exists => va'.

apply (hoare_prop_m.hoare_stren (!(fun s  => size A = nk /\ size A' = nk /\
    u2Z va + 4 * Z_of_nat nk.+1 < \B^1 /\ u2Z va' + 4 * Z_of_nat nk.+1 < \B^1 /\
    \S_{ nk } A =m \S_{ nk } X ^^ Z.abs_nat (2 * u2Z (ve `>> Z.abs_nat (ni + 1)) + u2Z ((ve `>> Z.abs_nat ni) `& one32)) * \B^nk {{\S_{ nk } M}} /\
    \S_{ nk } A < \S_{ nk } M) **
(fun s h => [a']_s = va' /\ [x']_s = vx' /\ [a]_s = va /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  s2Z [i]_s = ni /\ [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\
  u2Z [ei]_s + 2 * u2Z (ve `>> Z.abs_nat (ni + 1)) = u2Z (ve `>> Z.abs_nat ni) /\
  ((((var_e a' |--> A' ** var_e x' |--> X') ** var_e a |--> A ++ zero32 :: nil) ** var_e m |--> M ++ zero32 :: nil) **
    (var_e a' \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32)) s h))).

move=> s h [HlenA [HlenA' [r_a' [Hna' [r_x' [r_a [Hna [r_m [r_k [r_alpha [Hmem [Sum_A1 [Sum_A2 [r_i [Hgpe [r_l r_ei]]]]]]]]]]]]]]]].
exists heap.emp, h; repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.
rewrite (decompose_last_equiv _ A') HlenA' in Hmem.
by abstract assoc_comm Hmem.

apply pull_out_bang; case => HlenA [HlenA' [Hna [Hna' [HSumA1 HSumA2]]]].

(** addiu i i mone16)); *)

apply hoare_addiu'.

move=> s h [r_a' [r_x' [r_a [r_m [r_k [r_alpha [r_i [r_e [r_l [ r_ei Hmem]]]]]]]]]].

rewrite /wp_addiu.
exists A, A', va, va', (ni - 1).
repeat Reg_upd.
repeat (split; trivial).

rewrite /mone16 s2Z_add.
by rewrite (@sext_s2Z 16) Z2sK // r_i.
rewrite (@sext_s2Z 16) Z2sK // r_i.
split.
  apply (@leZ_trans (-1)); first by [].
  rewrite -{1}(add0Z (-1)) leZ_add2r; by case: Hni.
move: (max_s2Z [i]_s) => Y.
rewrite r_i in Y.
  apply (@ltZ_trans (2 ^^ 31 + -1)); by [exact: ltZ_le_add | ].
rewrite -{1}(add0Z (-1)) leZ_add2r; by case: Hni.
apply (@leZ_trans ni); by [ apply Zminus_le_decr | case: Hni].

rewrite (decompose_last_equiv _ A') HlenA'.
Assert_upd.
by abstract assoc_comm Hmem.

rewrite addZC Zplus_minus.
apply (eqmod_trans _ _ _ _ HSumA1), eqmod_reg_mult.
rewrite (Zabs_nat_Zplus ni _ (proj1 Hni)) // -shrl_comp int_and_rem_1 -(@u2Z_shrl _ (ve `>> Z.abs_nat ni) 1%nat); last by repeat constructor.
rewrite mulZC [2 ^^ 1]/=; exact: eqmod_refl.
by Inde_frame.
move=> ?; by Inde_mult.

clear HlenA HlenA' HA HA' HSumA HSumA'SumM A A' Hna va Hna' va'.

apply pull_out_exists_con => A.
apply pull_out_exists_con => A'.
apply pull_out_exists_con => va.
apply pull_out_exists_con => va'.

(** mont_mul_strict_init k alpha a one' a' m one ext int_ X_ Y_ M_ Z_ quot C t s_. *)

apply (hoare_prop_m.hoare_stren (!(fun s => ((size A = nk /\ size A' = nk /\
  u2Z va + 4 * Z_of_nat nk.+1 < \B^1 /\
  u2Z va' + 4 * Z_of_nat nk.+1 < \B^1 /\
  \S_{ nk } A =m \S_{ nk } X ^^ Z.abs_nat (u2Z ve) * \B^nk {{\S_{ nk } M}} /\ \S_{ nk } A < \S_{ nk } M))) **
(fun s h => u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\ [e]_s = ve /\
  [l]_s = Z2s 32 (Z_of_nat vl) /\ [a]_s = va /\ [a']_s = va' /\
  [x']_s = vx' /\ [m]_s = vm /\ [x]_s = vx /\ [one']_s = vone' /\
  (var_e x|-->X ** var_e a |--> A ++ zero32 :: nil ** var_e a' |--> A' ++ zero32 :: nil ** var_e x' |--> X' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e one' |--> ONE') s h))).

move=> s h [h1 [h2 [Hdisj [Hunion [[HlenA [HlenA' [r_k [r_alpha [r_e [r_l [r_a [Hna [r_a' [Hna' [r_x' [r_m [Hmem [HSumA1 HSumA2]]]]]]]]]]]]]] [r_x [r_one' Hmem2]]]]]]].

exists heap.emp, (h1 \U h2); repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.
move: {Hmem Hmem2}(assert_m.con_cons _ _ _ _ _ Hdisj Hmem Hmem2) => Hmem.
rewrite (decompose_last_equiv _ X') HlenX'.
by abstract assoc_comm Hmem.

apply pull_out_bang; case => HlenA [HlenA' [Hna [Hna' [HSumA1 HSumA2]]]].

apply (hoare_prop_m.hoare_stren ((fun s h => exists A', size A' = nk /\
  [a]_s = va /\ [one']_s = vone' /\ [a']_s = va' /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e a |--> A ** var_e one' |--> ONE' ** var_e a' |--> A' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h) **
(fun s h => [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\ [x]_s = vx /\  [x']_s = vx' /\
  (var_e x|-->X ** var_e x' |--> X' ++ zero32 :: nil ** var_e a \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h))).

move=> s h [r_k [r_alpha [r_e [r_l [r_a [r_a' [r_x' [r_m [hgprx [rone' Hmem]]]]]]]]]].

have {}Hmem : ((var_e a |--> A ** var_e a' |--> A' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e one' |--> ONE') ** (var_e x|-->X**var_e x' |--> X' ++ zero32 :: nil ** var_e a \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32)) s h.
  rewrite (decompose_last_equiv _ A) HlenA in Hmem.
  by abstract assoc_comm Hmem.
case:Hmem => [h1 [h2 [Hdisj [Hunion [Hmem1 Hmem2]]]]].
exists h1, h2; repeat (split; trivial).
exists A'; repeat (split; trivial).
by abstract assoc_comm Hmem1.

clear A' HlenA'.

apply hoare_prop_m.hoare_weak with ((fun s h => exists A', size A' = nk /\
  [a]_s = va /\ [one']_s = vone' /\ [a']_s = va' /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e a |--> A ** var_e one' |--> ONE' ** var_e a' |--> A' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  \S_{ nk } A' =m \S_{ nk } X ^^ (Z.abs_nat (u2Z ve)) {{ \S_{ nk } M }} /\ \S_{ nk } A' < \S_{ nk } M) **
(fun s h => [e]_s = ve /\ [l]_s = Z2s 32 (Z_of_nat vl) /\ [x]_s = vx /\  [x']_s = vx' /\
  (var_e x|-->X ** var_e x' |--> X' ++ zero32 :: nil ** var_e a \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h)).

move=> s h [h1 [h2 [Hdisj [Hunion [[A' [HlenA' [r_a [r_one' [r_a' [r_m [r_k [r_alpha [Hmem [HSumA'1 HSumA'2]]]]]]]]]] [r_e [r_l [r_x [r_x' Hmem2]]]]]]]]].

exists A, A', X', va, va'; repeat (split; trivial).
move: {Hmem Hmem2}(assert_m.con_cons _ _ _ _ _ Hdisj Hmem Hmem2) => Hmem.
rewrite (decompose_last_equiv _ A) HlenA Hunion.
by abstract assoc_comm Hmem.
by rewrite r_e.

apply frame_rule_R.

apply hoare_prop_m.hoare_weak with (fun s h => exists A', size A' = nk /\ [a]_s = va /\
  [one']_s = vone' /\ [a']_s = va' /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e a |--> A ** var_e one' |--> ONE' ** var_e a' |--> A' ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  \B^nk * \S_{ nk } A' =m \S_{ nk } A * \S_{ nk } ONE' {{ \S_{ nk } M }} /\ \S_{ nk } A' < \S_{ nk } M).

move=> s h [A' [HlenA' [r_a [r_one' [r_a' [r_m [r_k [r_alpha [Hmem [Sum_A1' Sum_A2']]]]]]]]]].
exists A'; repeat (split; trivial).

apply eqmod_reg_mult' with (\B^nk).
apply Zis_gcd_sym.
rewrite ZbetaE.
apply Zis_gcd_Zpower_odd; first by [].
eapply eqmod_trans.
rewrite mulZC; exact: Sum_A1'.
by rewrite HSumONE'_is_1 mulZ1.

eapply mont_mul_strict_init_triple; eauto.
by abstract Uniq_uniq r0.
by Inde_frame.
move=> ?; by Inde_mult.
Qed.

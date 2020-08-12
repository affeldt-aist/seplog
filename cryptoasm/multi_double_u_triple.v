(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext uniq_tac machine_int.
Require Import multi_int.
Import MachineInt.
Require Import mips_seplog mips_tactics mips_contrib mapstos.
Require Import multi_double_u_prg.
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

Section multi_double_u.

Variables k a i tmp prev next : reg.

Lemma multi_double_u_triple : uniq(k, a, i, tmp, prev, next, r0) ->
forall nk va, u2Z va + 4 * Z_of_nat nk < \B^1 ->
forall A, size A = nk ->
  {{ fun s h => [a]_s = va /\ u2Z [k]_s = Z_of_nat nk /\ (var_e a |--> A) s h }}
  multi_double_u k a i tmp prev next
  {{ fun s h => exists A', size A' = nk /\ [a]_s = va /\ u2Z [k]_s = Z_of_nat nk /\
     (var_e a |--> A') s h /\ \S_{ nk } A' + u2Z [prev]_s * 2 ^^ (nk * 32) = 2 * \S_{ nk } A }}.
Proof.
move=> Hset nk va Hna A HA; rewrite /multi_double_u.

(** addiu i r0 zero16; *)

apply hoare_addiu with (fun s h => [a]_s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i]_s = 0 /\ (var_e a |--> A) s h).

move=> s h [Hra [Hri Hmem]]; rewrite /wp_addiu.
repeat Reg_upd; repeat (split; trivial).
by rewrite sext_0 addi0 Z2uK.
by Assert_upd.

(** addiu prev r0 zero16; *)

apply hoare_addiu with (fun s h => [a]_s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i]_s = 0 /\ [prev]_s = zero32 /\ (var_e a |--> A) s h).

move=> s h [Hra [Hri [Hrk Hmem]]]; rewrite /wp_addiu.
repeat Reg_upd; repeat (split; trivial).
by rewrite sext_0 addi0.
by Assert_upd.

(** while (bne i k) *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = one32) /\
  (ni <= nk)%nat /\
  (var_e a |--> A') s h /\
  drop ni A' = drop ni A /\
  \S_{ ni } (take ni A') + u2Z [prev]_s * 2 ^^ (ni * 32) = 2 * \S_{ ni } (take ni A)).

move=> s h [Hra [Hrk [Hri [Hrprev Hmem]]]].
exists A, O; repeat (split; trivial).
by rewrite Hrprev; left.
by rewrite /= Hrprev Z2uK.

move=> s h [[A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 Hinv2]]]]]]]]]] Hri'].
rewrite /= in Hri'. move/negPn/eqP in Hri'.
have {Hri'} ? : ni = nk by rewrite /= Hrk Hri in Hri'; apply Z_of_nat_inj.
subst ni.
rewrite take_oversize // in Hinv2; last by rewrite HlenA'.
rewrite take_oversize // in Hinv2; last by rewrite HA.
by exists A'.

(** lwxs tmp i a; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = one32) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  drop ni A' = drop ni A /\
  \S_{ ni } (take ni A') + u2Z [prev ]_ s * 2 ^^ (ni * 32) = 2 * \S_{ ni } (take ni A) /\
  [tmp]_s = A' `32_ ni).

move=> s h [[A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 Hinv2]]]]]]]]]] Hik'].
rewrite /= in Hik'; move/eqP in Hik'.
have {}Hik' : (ni < nk)%nat.
  rewrite ltnNge; apply/negP; contradict Hik'.
  by rewrite Hrk Hri; f_equal; apply/eqP; rewrite eqn_leq Hik.
exists (A' `32_ ni); split.
Decompose_32 A' ni A1 A2 HlenA1 HA'; last by rewrite HlenA'.
rewrite HA' (decompose_equiv _ _ _ _ _ HlenA1) in Hmem.
rewrite conCE !conAE in Hmem.
move: Hmem; apply monotony => // h'.
apply mapsto_ext => //.
by rewrite /= shl_Z2u inj_mult Hri [Zmult]lock /= -lock mulZC.

rewrite /update_store_lwxs.
exists A', ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** srl next tmp thirtyone5; *)

apply hoare_srl with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = one32) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  drop ni A' = drop ni A /\
  \S_{ ni } (take ni A') + u2Z ([prev ]_ s) * 2 ^^ (ni * 32) = 2 * \S_{ ni } (take ni A) /\
  [tmp]_s = A' `32_ ni /\
  [next]_s = (A' `32_ ni) `>> 31).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 Htmp]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite Htmp Z2uK.

(** sll tmp tmp one5; *)

apply hoare_sll with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = one32) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  drop ni A' = drop ni A /\
  \S_{ ni } (take ni A') + u2Z ([prev ]_ s) * 2 ^^ (ni * 32) = 2 * \S_{ ni } (take ni A) /\
  [tmp]_s = (A' `32_ ni) `<< 1 /\
  [next]_s = (A' `32_ ni) `>> 31).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp Hnext]]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite Htmp Z2uK.

(** cmd_or tmp tmp prev; *)

apply hoare_or with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = one32) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  drop ni A' = drop ni A /\
  \S_{ ni } (take ni A') + u2Z ([prev ]_ s) * 2 ^^ (ni * 32) = 2 * \S_{ ni } (take ni A) /\
  [tmp]_s = ((A' `32_ ni) `<< 1) `|` [prev]_s /\
  [next]_s = (A' `32_ ni) `>> 31).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp Hnext]]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite Htmp.

(** addiu prev next zero16; *)

apply hoare_addiu with  (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = one32) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  drop ni A' = drop ni A /\
  \S_{ ni } (take ni A') + u2Z ([tmp]_s `% 1) * 2 ^^ (ni * 32) = 2 * \S_{ ni } (take ni A) /\
  [tmp]_s `>> 1 = (A' `32_ ni `<< 1) `>> 1 /\
  [prev]_s = A' `32_ ni `>> 31).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp Hnext]]]]]]]]]]]].
rewrite /wp_addiu; exists A', ni.
repeat Reg_upd; repeat (split; trivial).
- rewrite sext_0 addi0 Hnext.
  move: (shrl_lt (A' `32_ ni) 31) => /=.
  move X : (u2Z _) => x Hx.
  have [Y|Y] : x = 0 \/ x = 1.
    move: (min_u2Z (A' `32_ ni `>> 31)) => Hy; lia.
  subst x.
  rewrite (_ : 0 = u2Z (Z2u 32 0)) in Y; last by rewrite Z2uK.
  apply u2Z_inj in Y.
  rewrite Y; by auto.
  subst x.
  rewrite (_ : 1 = u2Z (Z2u 32 1)) in Y; last by rewrite Z2uK.
  move/u2Z_inj : Y => ->; by right.
- by Assert_upd.
- rewrite Htmp.
  have X : u2Z (((A' `32_ ni `<< 1) `|` [prev ]_ s) `% 1) = u2Z ([prev ]_ s).
    rewrite rem_distr_or shl_rem_m; last by repeat constructor.
    rewrite int_orC int_or_0 u2Z_rem' //.
    case: Hprev => ->; by rewrite Z2uK.
  by rewrite X.
- rewrite Htmp shrl_distr_or (@shrl_overflow _ ([prev]_s) 1).
  by rewrite int_or_0.
  by case: Hprev => ->; rewrite Z2uK.
- by rewrite sext_Z2u // addi0.

(** sll next i two5; *)

apply hoare_sll with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = one32) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  drop ni A' = drop ni A /\
  \S_{ ni } (take ni A') + u2Z ([tmp]_s `% 1) * 2 ^^ (ni * 32) = 2 * \S_{ ni } (take ni A) /\
  [tmp]_s `>> 1 = ((A' `32_ ni) `<< 1) `>> 1 /\
  [prev]_s = (A' `32_ ni) `>> 31 /\
  u2Z [next]_s = 4 * Z_of_nat ni).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp Hnext]]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite Z2uK // (_ : '|2| = 2%nat) // (@u2Z_shl 2 _ _ 30) //.
- rewrite Hri [_ ^^ _]/=; ring.
- rewrite (_ : \B^1 = 4 * 2 ^^ 30) in Hna; last by rewrite Zbeta1E.
  move: (min_u2Z va) => ?; ssromega.

(** addu next a next; *)

apply hoare_addu with  (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = one32) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  drop ni A' = drop ni A  /\
  \S_{ ni } (take ni A') + u2Z ([tmp]_s `% 1) * 2 ^^ (ni * 32) = 2 * \S_{ ni } (take ni A) /\
  [tmp]_s `>> 1 = ((A' `32_ ni) `<< 1) `>> 1 /\
  [prev]_s = A' `32_ ni `>> 31 /\
  u2Z [next]_s = u2Z va + 4 * Z_of_nat ni).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp [Hprev2 Hnext]]]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite u2Z_add.
  + rewrite Hra Hnext; ring.
  + rewrite (_ : \B^1 = 4 * 2 ^^ 30) in Hna; last by rewrite Zbeta1E.
    rewrite (_ : 2 ^^ 32 = 4 * 2 ^^ 30) // Hnext Hra; ssromega.

(** sw tmp zero16 next *)

apply hoare_sw_back'' with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = one32) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  drop ni.+1 A' = drop ni.+1 A /\
  \S_{ni.+1} (take ni.+1 A') + u2Z ([prev]_s) * 2 ^^ (ni.+1 * 32) = 2 * \S_{ni.+1} (take ni.+1 A) /\
  u2Z [next]_s = u2Z va + 4 * Z_of_nat ni).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Hrtmp [Hprev2 Hrnext]]]]]]]]]]]]].

have Htmp : [ var_e next \+ int_e (sext 16 zero16) ]e_ s = [ var_e a \+ int_e (Z2u 32 (Z_of_nat (4 * ni))) ]e_ s.
  rewrite sext_0 /= addi0.
  apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat.
  rewrite inj_mult Hra Hrnext //; ring.
  rewrite inj_mult -Zbeta1E Hra; simpl Z_of_nat; ssromega.

Decompose_32 A' ni A'1 A'2 HlenA1 HA'; last by rewrite HlenA'.
rewrite HA' (decompose_equiv _ _ _ _ _ HlenA1) in Hmem.
rewrite conCE !conAE in Hmem.
exists (int_e (A' `32_ ni)).
move: Hmem; apply monotony => ht.
exact: mapsto_ext.
apply currying => h' H'; simpl app in H'.
exists (upd_nth A' ni [tmp]_s), ni.
repeat (split; trivial).

- exact: size_upd_nth.
- rewrite HA' upd_nth_cat HlenA1 // subnn /= (decompose_equiv _ _ _ _ _ HlenA1).
  rewrite cat0s in H'.
  assoc_comm H'.
  by move: H'; apply mapsto_ext.
- by rewrite drop_upd_nth // dropS [in RHS]dropS Hinv1.
- rewrite (take_nth zero32); last by rewrite (@size_upd_nth _ nk).
  rewrite -cats1 lSum_cut_last; last first.
    by rewrite size_cat addn1 size_take (@size_upd_nth _ nk) // Hik.
  rewrite subn1 [_.+1.-1]/= nth_upd_nth; last by rewrite HlenA'.
  rewrite take_upd_nth (take_nth zero32); last by rewrite HA.
  rewrite -cats1 (lSum_cut_last _ (take ni A)) //; last first.
    by rewrite size_cat /= addnC /= size_take HA Hik add1n.
  rewrite subn1 [_.+1.-1]/= mulZDr -Hinv2 -!addZA.
  congr (_ + _).
  have X : u2Z ([tmp ]_ s) = u2Z (([tmp]_s `% 1)) + u2Z (([tmp]_s `>> 1) `<< 1).
    rewrite {1}(@or_sh_rem 32 ([tmp]_s) 1 (refl_equal _)).
    have X1 : u2Z (@cast_subnK 1 32 Logic.eq_refl (zext 31 ([tmp ]_ s `% 1))) < 2 ^^ 1.
      rewrite u2Z_cast u2Z_zext -int_and_rem_1.
      case: (Zeven_odd_dec (u2Z ([tmp ]_ s))) => X.
      + apply int_even_and_1 in X; by rewrite X Z2uK.
      + apply int_odd_and_1 in X; by rewrite X Z2uK.
    have X2 : (([tmp ]_ s `>> 1) `<< 1) `% 1 = Z2u 1 0 by rewrite shl_rem_m.
    rewrite (@or_concat 32 _ _ 1 Logic.eq_refl X1 X2) /cast_subnK u2Z_cast u2Z_concat addZC.
    f_equal.
    by rewrite u2Z_rem' // u2Z_cast u2Z_zext.
    by rewrite u2Z_shr_shrink' // shl_rem_m // Z2uK // subZ0.
  rewrite X mulZDr -!addZA.
  f_equal; first exact: mulZC.
  rewrite Hrtmp Hprev2.
  have -> : ((A' `32_ ni `<< 1) `>> 1) `<< 1 = A' `32_ ni `<< 1 by rewrite shrl_shl // shl_rem_m.
  have <- : A `32_ ni = A' `32_ ni.
    rewrite (drop_nth zero32) in Hinv1; last by rewrite HlenA'.
    symmetry in Hinv1.
    rewrite (drop_nth zero32) in Hinv1; last by rewrite HA.
    by case: Hinv1.
  have U : 2 * u2Z (A `32_ ni) = u2Z (A `32_ ni `<< 1) + 2 ^^ 32 * u2Z (A `32_ ni `>> 31).
    case: (Z_lt_le_dec (u2Z (A `32_ ni)) (2 ^^ 31)) => V.
    * by rewrite (@u2Z_shl 1 _ _ 31) // shrl_overflow // Z2uK // mulZ0 addZ0 mulZC.
    * rewrite -(@u2Z_shrl _ (A `32_ ni) 31) // mulZDr addZC; congr (_ + _).
      - by rewrite u2Z_shl_rem.
      - by rewrite mulZC -mulZA mulZC -mulZA.
  symmetry.
  rewrite mulZC -mulZA -(mulZC 2) U mulZDr mulSn addnC ZpowerD; ring.

apply hoare_addiu'.
move=> s m [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 Hnext]]]]]]]]]]].
rewrite /wp_addiu.
exists A', ni.+1.
rewrite sext_Z2u //.
repeat Reg_upd; repeat (split; trivial).
- rewrite u2Z_add_Z2u //.
  + by rewrite Z_S Hri.
  + rewrite Hri -Zbeta1E.
    move: (min_u2Z va) => ?; ssromega.
- by Assert_upd.
Qed.

End multi_double_u.

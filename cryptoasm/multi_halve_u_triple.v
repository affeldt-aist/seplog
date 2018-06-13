(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext uniq_tac machine_int.
Require Import multi_int.
Import MachineInt.
Require Import mips_seplog mips_tactics mips_contrib mapstos multi_halve_u_prg.
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

Lemma multi_halve_u_triple k a i tmp prev next : uniq(k, a, i, tmp, prev, next, r0) ->
  forall nk va, u2Z va + 4 * Z_of_nat nk < \B^1 ->
    forall A, size A = nk ->
      {{ fun s h => [ a ]_s = va /\ u2Z [ k ]_s = Z_of_nat nk /\ (var_e a |--> A) s h }}
      multi_halve_u k a i tmp prev next
      {{ fun s h => exists A', size A' = nk /\ [a]_s = va /\ u2Z [ k ]_s = Z_of_nat nk /\
        (var_e a |--> A') s h /\ 2 * \S_{ nk } A' + u2Z ([prev]_s `>> 31) = \S_{ nk } A }}.
Proof.
move=> Hset nk va Hna A HA; rewrite /multi_halve_u.

(** addiu i k zero16; *)

apply hoare_addiu with (fun s h => [a]_s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i]_s = Z_of_nat nk /\ (var_e a |--> A) s h).

move=> s h [Hra [Hri Hmem]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by rewrite sext_0 addi0.
by Assert_upd.

(** addiu prev r0 zero16; *)

apply hoare_addiu with (fun s h => [a]_s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i]_s = Z_of_nat nk /\ [prev]_s = zero32 /\ (var_e a |--> A) s h).

move=> s h [Hra [Hri [Hrk Hmem]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by rewrite sext_0 addi0.
by Assert_upd.

(** while (bne i r0) *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = Z2u 32 (2 ^^ 31)) /\
  (ni <= nk)%nat /\
  (var_e a |--> A') s h /\
  take ni A' = take ni A /\
  2 * \S_{ nk - ni } (drop ni A') + u2Z ([prev]_s `>> 31) = \S_{ nk - ni } (drop ni A)).

move=> s h [Hra [Hrk [Hri [Hrprev Hmem]]]].
exists A, nk; repeat (split; trivial).
by rewrite Hrprev; left.
rewrite (_ : (_ - _ = O)%nat) /=; last by rewrite subnn.
by rewrite Hrprev shrl_Z2u_0 // Z2uK.

move=> s h [[A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 Hinv2]]]]]]]]]] Hri'].
rewrite /= in Hri'. move/negPn/eqP in Hri'.
have {Hri'} ? : ni = O.
  apply Z_of_nat_inj; by rewrite -Hri Hri' /= store.get_r0 Z2uK.
subst ni.
rewrite subn0 2!drop0 in Hinv2.
exists A'; by repeat (split; trivial).

(**  addiu i i mone16; *)

apply hoare_addiu with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = Z2u 32 (2 ^^ 31)) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  take ni.+1 A' = take ni.+1 A /\
  2 * \S_{ nk - ni.+1} (drop ni.+1 A') + u2Z ([prev ]_ s `>> 31) = \S_{ nk - ni.+1} (drop ni.+1 A)).

move=> s h [[A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 Hinv2]]]]]]]]]] Hri'].
rewrite /= store.get_r0 Z2uK // in Hri'.
move/eqP in Hri'.
exists A', (ni - 1)%nat.
repeat Reg_upd.
rewrite Hri (_ : 0 = Z_of_nat 0) // in Hri'; apply Z_of_nat_inj_neq, not_eq_sym in Hri'.
rewrite -subSn; last by rewrite lt0n; apply/eqP; auto.
rewrite subSS subn0.
repeat (split; trivial).
- rewrite sext_Z2s // u2Z_add_Z2s //; last first.
    rewrite Hri -(Zmult_1_l (-1)) -(Zopp_eq_mult_neg_1 1) (_ : 1 = Z_of_nat 1) //.
    exact/Zle_left/inj_le/neq_0_lt.
  rewrite inj_minus1 //; by [rewrite Hri | apply neq_0_lt].
- by Assert_upd.

(** lwxs tmp i a; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists A' ni, length A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = Z2u 32 (2 ^^ 31)) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  take ni.+1 A' = take ni.+1 A /\
  2 * \S_{nk - ni.+1} (drop ni.+1 A') + u2Z ([prev ]_ s `>> 31) = \S_{nk - ni.+1} (drop ni.+1 A) /\
  [tmp]_s = A' `32_ ni).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 Hinv2]]]]]]]]]].
exists (A' `32_ ni); split.
- Decompose_32 A' ni A1 A2 HlenA1 HA'; last by rewrite HlenA'.
  rewrite HA' (decompose_equiv _ _ _ _ _ HlenA1) in Hmem.
  rewrite conCE !conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u inj_mult Hri [Zmult]lock /= -lock mulZC.
- rewrite /update_store_lwxs.
  exists A', ni; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** andi next tmp one16; *)

apply hoare_andi with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = Z2u 32 (2 ^^ 31)) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  take ni.+1 A' = take ni.+1 A /\
  2 * \S_{nk - ni.+1} (drop ni.+1 A') + u2Z ([prev ]_ s `>> 31) = \S_{nk - ni.+1} (drop ni.+1 A) /\
  [tmp]_s = A' `32_ ni /\
  [next]_s = (A' `32_ ni) `& one32).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 Htmp]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite Htmp zext_Z2u.

(** srl tmp tmp one5; *)

apply hoare_srl with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = Z2u 32 (2 ^^ 31)) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  take ni.+1 A' = take ni.+1 A /\
  2 * \S_{nk - ni.+1} (drop ni.+1 A') + u2Z ([prev ]_ s `>> 31) = \S_{nk - ni.+1} (drop ni.+1 A) /\
  [tmp]_s = (A' `32_ ni) `>> 1 /\
  [next]_s = (A' `32_ ni) `& one32).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp Hnext]]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite Htmp Z2uK.

(** cmd_or tmp tmp prev; *)

apply hoare_or with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = Z2u 32 (2 ^^ 31)) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  take ni.+1 A' = take ni.+1 A /\
  2 * \S_{nk - ni.+1} (drop ni.+1 A') + u2Z ([prev ]_ s `>> 31) = \S_{nk - ni.+1} (drop ni.+1 A) /\
  [tmp]_s = ((A' `32_ ni) `>> 1) `|` [prev]_s /\
  [next]_s = (A' `32_ ni) `& one32).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp Hnext]]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite Htmp.

(** addiu prev next zero16; *)

apply hoare_addiu with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = one32) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  take ni.+1 A' = take ni.+1 A /\
  2 ^^ 33 * \S_{nk - ni.+1} (drop ni.+1 A') + 2 * u2Z ([tmp]_s) + u2Z ([prev ]_ s) = \S_{ nk - ni } (drop ni A) /\
  [tmp]_s `% 31 = ((A' `32_ ni) `>> 1) `% 31 /\
  [next]_s = (A' `32_ ni) `& one32).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp Hnext]]]]]]]]]]]].
rewrite /wp_addiu; exists A', ni; repeat Reg_upd; repeat (split; trivial).
- rewrite sext_0 addi0 Hnext.
  case: (Zeven_odd_dec (u2Z (A' `32_ ni))).
  + move/int_even_and_1; by left.
  + move/int_odd_and_1; by right.
- by Assert_upd.
- rewrite (@drop_nth _ zero32 ni) ; last by rewrite HA.
  rewrite (_ : nk - ni = (nk - ni.+1).+1)%nat; last by rewrite -subSn.
  rewrite lSum_S Hnext Htmp.
  have -> : 2 * u2Z ((A' `32_ ni `>> 1) `|` [prev ]_ s) =
    2 * u2Z (A' `32_ ni `>> 1) + 2 * u2Z ([prev ]_ s).
    case: Hprev => Hprev.
    - by rewrite Hprev Z2uK // mulZ0 addZ0 int_or_0 //.
    - rewrite int_orC (@or_concat 32 _ _ 31 Logic.eq_refl); last 2 first.
        by move: (shrl_lt (A' `32_ ni) 1).
        apply u2Z_inj.
        move: (@u2Z_rem'' _ ([prev ]_ s) 30 1).
        rewrite {1}Hprev Z2uK // => -> //; by rewrite Z2uK.
      rewrite /cast_subnK u2Z_cast u2Z_concat u2Z_shr_shrink' //.
      rewrite Hprev !Z2uK // rem_Zpower // !Z2uK //.
      ring_simplify.
      rewrite u2Z_rem' //.
      by move: (shrl_lt (A' `32_ ni) 1).
  have -> : u2Z (A `32_ ni) = 2 * u2Z (A' `32_ ni `>> 1) + u2Z (A' `32_ ni `& one32).
    rewrite -(@u2Z_shrl 32 _ 1); last by repeat constructor.
    rewrite [_ ^^ _]/=.
    ring_simplify.
    rewrite (take_nth zero32) in Hinv1; last by rewrite HlenA'.
    rewrite (take_nth zero32) in Hinv1; last by rewrite HA.
    move/eqP : Hinv1.
    rewrite eqseq_rcons => /andP [/eqP Hinv' /eqP Hinv''].
    by rewrite /nth' Hinv'' int_and_rem_1.
  rewrite -Hinv2.
  suff -> : 2 * u2Z ([prev ]_ s) = 2 ^^ 32 * u2Z ([prev ]_ s `>> 31).
    rewrite mulZDr ZpowerS sext_0 addi0; ring.
- case: Hprev => Hprev.
  + by rewrite Hprev Z2uK // mulZ0 shrl_Z2u_0 Z2uK.
  + by rewrite Hprev Z2uK // shrl_Zpower // ssrnat.subnn Z2uK.
- rewrite Htmp.
  case: Hprev => ->.
  + by rewrite int_or_0.
  + by rewrite rem_distr_or rem_Zpower // int_or_0.

(** sll prev prev thirtyone5; *)

apply hoare_sll with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = Z2u 32 (2 ^^ 31)) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  take ni.+1 A' = take ni.+1 A /\
  2 ^^ 33 * \S_{nk - ni.+1} (drop ni.+1 A') + 2 * u2Z ([tmp]_s) + u2Z ([prev]_ s `>> 31) =
  \S_{ nk - ni} (drop ni A) /\
  [tmp]_s `% 31 = ((A' `32_ ni) `>> 1) `% 31 /\
  [next]_s = (A' `32_ ni) `& one32).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp Hnext]]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
- case : Hprev => ->.
  + rewrite shl_zero; by left.
  + rewrite Z2uK // shl_1 //; by right.
- by Assert_upd.
- case : Hprev => Hprev.
  + by rewrite Hprev shl_zero shrl_Z2u_0 Z2uK // -Hinv2 Hprev Z2uK.
  + rewrite Z2uK // (_ : '|31| = 31%nat) //.
    by rewrite Hprev (@shl_1 32 31 erefl) shrl_Zpower // -Hinv2 ssrnat.subnn [2 ^^ 0]/= Hprev.

(** sll next i two5; *)

apply hoare_sll with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = Z2u 32 (2^^31)) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  take ni.+1 A' = take ni.+1 A /\
  2 ^^ 33 * \S_{nk - ni.+1} (drop ni.+1 A') + 2 * u2Z ([tmp]_s) + u2Z ([prev]_ s `>> 31) =
  \S_{ nk - ni } (drop ni A) /\
  [tmp]_s `% 31 = (A' `32_ ni `>> 1) `% 31 /\
  u2Z [next]_s = 4 * Z_of_nat ni).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp Hnext]]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
rewrite Z2uK // (_ : '| 2 | = 2%nat) // (@u2Z_shl 2 _ _ 30) //.
- by rewrite Hri [_ ^^ _]/= mulZC.
- rewrite (_ : \B^1 = 4 * 2 ^^ 30) in Hna; last by rewrite Zbeta1E.
  move: (min_u2Z va) => ?; ssromega.

(** addu next a next; *)

apply hoare_addu with (fun s h => exists A' ni, size A' = nk /\
  [a ]_ s = va /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [i ]_ s = Z_of_nat ni /\
  ([prev]_s = zero32 \/ [prev]_s = Z2u 32 (2 ^^ 31)) /\
  (ni < nk)%nat /\
  (var_e a |--> A') s h /\
  take ni.+1 A' = take ni.+1 A /\
  2 ^^ 33 * \S_{nk - ni.+1} (drop ni.+1 A') + 2 * u2Z ([tmp]_s) + u2Z ([prev]_ s `>> 31) =
  \S_{ nk - ni } (drop ni A) /\
  [tmp]_s `% 31 = (A' `32_ ni `>> 1) `% 31 /\
  u2Z [next]_s = u2Z va + 4 * Z_of_nat ni).

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Htmp Hnext]]]]]]]]]]]].
exists A', ni; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- rewrite u2Z_add.
  + rewrite Hra Hnext; ring.
  + rewrite (_ : \B^1 = 4 * 2 ^^ 30) in Hna; last by rewrite Zbeta1E.
    rewrite (_ : 2 ^^ 32 = 4 * 2 ^^ 30) // Hnext Hra; ssromega.

(** sw tmp zero16 next *)

apply hoare_sw_back'.

move=> s h [A' [ni [HlenA' [Hra [Hrk [Hri [Hprev [Hik [Hmem [Hinv1 [Hinv2 [Hrtmp Hrnext]]]]]]]]]]]].

have Htmp : [ var_e next \+ int_e (sext 16 zero16) ]e_ s = [ var_e a \+ int_e (Z2u 32 (Z_of_nat (4 * ni))) ]e_ s.
  rewrite /= sext_0 addi0.
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
- by apply size_upd_nth.
- by apply ltnW.
- rewrite HA' upd_nth_cat HlenA1 // (_ : (ni - ni = 0)%nat); last by rewrite subnn.
  rewrite /= (decompose_equiv _ _ _ _ _ HlenA1).
  rewrite cat0s in H'.
  assoc_comm H'.
  move: H'; by apply mapsto_ext.
- rewrite HA' upd_nth_cat; last by rewrite HlenA1.
  rewrite take_size_cat //.
  rewrite (take_nth zero32) in Hinv1; last by rewrite HlenA'.
  rewrite (take_nth zero32) in Hinv1; last by rewrite HA.
  move/eqP : Hinv1.
  rewrite eqseq_rcons => /andP [/eqP <- _].
  by rewrite HA' take_size_cat.
- rewrite -Hinv2.
  f_equal.
  rewrite HA' upd_nth_cat; last by rewrite HlenA1.
  rewrite drop_size_cat // HlenA1 subnn [upd_nth _ _ _]/=.
  have -> : (nk - ni = (nk - ni.+1).+1)%nat by rewrite -subSn.
  rewrite lSum_S -cat1s catA drop_size_cat; last by rewrite size_cat /= HlenA1 addnC.
  by ring_simplify.
Qed.

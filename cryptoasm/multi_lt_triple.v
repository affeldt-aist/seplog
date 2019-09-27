(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int multi_int uniq_tac.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_tactics mapstos.
Require Import multi_lt_prg.

Local Open Scope machine_int_scope.
Import expr_m.
Local Open Scope mips_expr_scope.
Import assert_m.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope uniq_scope.
Local Open Scope multi_int_scope.

Section multi_lt.

Variables k a b i flag ret ret2 a0 a1 : reg.

Lemma multi_lt_triple : uniq(k, a, b, i, flag, ret, ret2, a0, a1, r0) ->
  forall nk A B va vb, size A = nk -> size B = nk ->
  {{ fun s h => u2Z [ k ]_s = Z_of_nat nk /\ [ a ]_s = va /\ [ b ]_s = vb /\
     (var_e a |--> A ** var_e b |--> B) s h }}
  multi_lt k a b i flag ret ret2 a0 a1
  {{ fun s h => u2Z [ k ]_s = Z_of_nat nk /\ [ a ]_s = va /\ [ b ]_s = vb /\
    (((\S_{ nk } A < \S_{ nk } B /\ [ret]_s = one32 /\ [ret2]_s = zero32) \/
      (\S_{ nk } A > \S_{ nk } B /\ [ret]_s = zero32 /\ [ret2]_s = one32) \/
      (\S_{ nk } A = \S_{ nk } B /\ [ret]_s = zero32 /\ [ret2]_s = zero32)) /\
    (var_e a |--> A ** var_e b |--> B) s h) }}.
Proof.
move=> Hset nk A B va vb HlenA HlenB.
rewrite /multi_lt.

(** addiu i k zero16 ; *)

apply hoare_addiu with (fun s h => u2Z [k]_s = Z_of_nat nk /\ [a]_s = va /\
  [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\ [i]_s = [k]_s).

move => s h [r_k [r_a [r_b Hmem]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite sext_0 addi0.

(** addiu flag r0 one16 ; *)

apply hoare_addiu with (fun s h => u2Z [k]_s = Z_of_nat nk /\ [a]_s = va /\
  [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\
  [i]_s = [k]_s /\ [flag]_s = one32).

move=> s h [r_k [r_a [r_b [Hmem r_i]]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.
by rewrite add0i sext_Z2u.

(** ifte (beq i r0) *)

apply while.hoare_ifte.

(** addiu ret r0 zero16 *)

apply hoare_addiu with (fun s h => u2Z [k]_s = Z_of_nat nk /\ [a]_s = va /\
  [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\
  [i]_s = [k]_s /\ [flag]_s = one32 /\ [i]_s = zero32 /\ [ret]_s = zero32).

rewrite /wp_addiu => s h [[r_k [r_a [r_b [Hmem [r_i r_flag]]]]] r_i'].
repeat Reg_upd.
have {}r_i' : [i]_s = zero32.
  move/eqP : r_i' => /= /u2Z_inj ->.
  by rewrite store.get_r0.
repeat (split; trivial).
by Assert_upd.
by rewrite sext_Z2u // addi0.

apply hoare_addiu'.
move => s h [r_k [r_a [r_b [Hmem [r_i [r_flag [r_i' r_ret]]]]]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
- right; right.
  rewrite -r_i r_i' Z2uK // in r_k.
  destruct nk; last by [].
  by rewrite sext_Z2u // addi0.
- by Assert_upd.

(** while (bne flag r0) ( *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => u2Z [k]_s = Z_of_nat nk /\ [a]_s = va /\
  [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\
  exists ni, u2Z [i]_s = Z_of_nat ni /\
    (ni <= nk)%nat /\
    (([flag]_s <> zero32 /\ [i]_s <> zero32 /\
      \S_{ nk - ni } (drop ni A) = \S_{ nk - ni } (drop ni B)) \/
     [flag]_s = zero32 /\
     (([ret]_s = one32 /\ [ret2]_s = zero32 /\
       \S_{ nk - ni } (drop ni A) < \S_{ nk - ni } (drop ni B)) \/
      ([ret]_s = zero32 /\ [ret2]_s = one32 /\
        \S_{ nk - ni } (drop ni A) > \S_{ nk - ni } (drop ni B)) \/
      ([ret]_s = zero32 /\ [i]_s = zero32 /\ [ret2]_s = zero32 /\
       \S_{ nk - ni } (drop ni A) = \S_{ nk - ni } (drop ni B))))).

move=> s h [[r_k [r_a [r_b [Hmem [r_i r_flag]]]]] r_i'].
rewrite /= store.get_r0 Z2uK // in r_i'; move/eqP in r_i'.
repeat (split; trivial).
exists nk; split; first by rewrite r_i r_k.
split => //.
left; split.
- rewrite r_flag; exact: Z2u_dis.
- split.
  + contradict r_i'; by rewrite r_i' Z2uK.
  + by rewrite subnn.

move=> s h [ [r_k [r_a [r_b [Hmem [ni [r_i [Hnink [
  [r_flag [r_ret2 Hsum]] |
  [ r_flag [ [r_ret [r_ret2 Hsum] ] |
  [ [r_ret [r_ret2 Hsum]] |
  [gprret [r_i' [r_ret2 Hsum]]]]]]]]]]]]]] Hneq]; rewrite /= in Hneq.
- have {}Hneq : u2Z [flag]_s = u2Z zero32.
    move/negPn/eqP : Hneq.
    by rewrite store.get_r0.
  apply u2Z_inj in Hneq; contradiction.
- repeat (split; trivial).
  left; split; last by [].
  by eapply lSum_skipn; eauto.
- repeat (split; trivial).
  right; left; split; last by [].
  apply Z.lt_gt.
  apply Z.gt_lt in Hsum.
  by eapply lSum_skipn; eauto.
- repeat (split; trivial).
  right; right; split; last by [].
  have ni_O : ni = O .
    symmetry in r_i; move: r_i.
    rewrite r_i' /zero32 Z2uK //; by move/Z_of_nat_0.
  by rewrite ni_O subn0 !drop0 in Hsum.

(**  addiu i i mone16 ; *)

apply hoare_addiu with (fun s h => u2Z [k]_s = Z_of_nat nk /\ [a]_s = va /\
  [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\
  exists ni, u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\
    ([flag]_s <> zero32 /\
      \S_{ nk - S ni } (drop (S ni) A) = \S_{ nk - S ni } (drop (S ni) B))).

move=> s h [ [r_k [ r_a [r_b [Hmem [ni [r_i [Hnink [
  [r_flag [r_i' Hsum] ] |
  [ r_flag [ [r_ret Hsum] |
  [ [r_ret Hsum] |
  [r_ret [r_i' Hsum]]]]]]]]]]]]] Hneq]; rewrite /= in Hneq.
- have X : (1 <= ni)%nat.
    apply/ltP/not_ge; contradict r_i'.
    apply u2Z_inj; rewrite r_i Z2uK //.
    apply le_n_0_eq in r_i'; by subst ni.
  rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
  + by Assert_upd.
  + exists (ni - 1)%nat; repeat (split; trivial).
    * rewrite sext_Z2s // u2Z_add_Z2s //.
      rewrite r_i inj_minus1 //; exact/leP.
      rewrite r_i.
      apply (@leZ_trans (1 + -1)); first by [].
      apply leZ_add2r.
      rewrite (_ : 1 = Z_of_nat 1) //; exact/inj_le/leP.
    * destruct ni.
      by move/leP in X; apply le_Sn_0 in X.
      by rewrite /= subn1.
    * by rewrite -subSn //= subn1.
- move/eqP: Hneq; by rewrite r_flag store.get_r0.
- move/eqP: Hneq; by rewrite r_flag store.get_r0.
- move/eqP: Hneq; by rewrite r_flag store.get_r0.

(**  lwxs a0 i a ; *)

apply hoare_lwxs_back_alt'' with (fun s h => u2Z [k]_s = Z_of_nat nk /\
  [a]_s = va /\ [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\
  exists ni, u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\
    ([flag]_s <> zero32 /\
      \S_{ nk - S ni } (drop (S ni) A) = \S_{ nk - S ni } (drop (S ni) B)) /\
    [a0]_s = A `32_ ni).

move=> s h [r_k [r_a [r_b [Hmem [ni [r_i [ni_nk [r_flag Hsum]]]]]]]].
exists (A `32_ ni); split.
- Decompose_32 A ni A1 A2 HlenA1 HA'; last by rewrite HlenA.
  rewrite HA' (decompose_equiv _ _ _ _ _ HlenA1) !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u r_i inj_mult mulZC.
- rewrite /update_store_lwxs; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  by exists ni.

(**  lwxs a1 i b ; *)

apply hoare_lwxs_back_alt'' with (fun s h => u2Z [k]_s = Z_of_nat nk /\
  [a]_s = va /\ [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\
  exists ni, u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\
    ([flag]_s <> zero32 /\
      \S_{ nk - S ni } (drop (S ni) A) = \S_{ nk - S ni } (drop (S ni) B)) /\
    [a0]_s = A `32_ ni /\ [a1]_s = B `32_ ni).

move=> s h [r_k [r_a [r_b [Hmem [ni [r_i [ni_nk [[r_flag Hsum] r_a0]]]]]]]].
exists (B `32_ ni); split.
- Decompose_32 B ni B1 B2 HlenB1 HB'; last by rewrite HlenB.
  rewrite HB' (decompose_equiv _ _ _ _ _ HlenB1) assert_m.conCE !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
  move: Hmem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u r_i inj_mult mulZC.
- rewrite /update_store_lwxs; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  by exists ni.

(**  sltu ret a0 a1 ; *)

apply hoare_sltu with (fun s h => u2Z [k]_s = Z_of_nat nk /\ [a]_s = va /\
  [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\
  exists ni, u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\
    ([flag]_s <> zero32 /\
      \S_{ nk - S ni } (drop (S ni) A) = \S_{ nk - S ni } (drop (S ni) B)) /\
    [a0]_s = A `32_ ni /\ [a1]_s = B `32_ ni /\
    (([ret]_s = one32 /\ u2Z [a0]_s < u2Z [a1]_s) \/
      ([ret]_s = zero32 /\ u2Z [a0]_s >= u2Z [a1]_s))).

move=> s h [r_k [r_a [r_b [Hmem [ni [r_i [ni_nk [[r_flag Hsum [r_a0 r_a1]]]]]]]]]].
rewrite /wp_sltu; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- exists ni; repeat (split; trivial).
  case: ifP; move/ltZP.
  by move=> ?; left.
  by move/Znot_lt_ge; right.

(**  movn flag r0 ret ; *)

apply hoare_movn with (fun s h => u2Z [k]_s = Z_of_nat nk /\ [a]_s = va /\
  [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\
  exists ni, u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\
    (\S_{ nk - S ni } (drop (S ni) A) = \S_{ nk - S ni } (drop (S ni) B)) /\
    [a0]_s = A `32_ ni /\ [a1]_s = B `32_ ni /\
    (([ret]_s = one32 /\ [flag]_s = zero32 /\
      u2Z [a0]_s < u2Z [a1]_s) \/
     ([ret]_s = zero32 /\ [flag]_s <> zero32 /\
      u2Z [a0]_s >= u2Z [a1]_s))).

move=> s h [r_k [r_a [r_b [Hmem [ni [r_i [ni_nk [[r_flag HSum]]]]]]]] [r_a0 [r_a1 [ [X1 X2] | [X1 X2]]]]].
- rewrite /wp_movn; repeat Reg_upd; split => Hr_ret.
  + repeat (split; trivial).
    * by Assert_upd.
    * exists ni; repeat (split; trivial); by left.
  + rewrite X1 in Hr_ret.
    have {Hr_ret}: u2Z one32 = u2Z zero32 by rewrite Hr_ret.
    by rewrite ?Z2uK.
- rewrite /wp_movn; repeat Reg_upd; split => Hr_ret.
  + done.
  + repeat (split; trivial).
    exists ni; repeat (split; trivial).
    by right.

(**  sltu ret2 a1 a0 ; *)

apply hoare_sltu with (fun s h => u2Z [k]_s = Z_of_nat nk /\ [a]_s = va /\
  [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\
  exists ni, u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\
    \S_{ nk - S ni } (drop (S ni) A) = \S_{ nk - S ni } (drop (S ni) B) /\
    [a0]_s = A `32_ ni /\ [a1]_s = B `32_ ni /\
    (([ret]_s = one32 /\ [ret2]_s = zero32 /\
        [flag]_s = zero32 /\ u2Z [a0]_s < u2Z [a1]_s) \/
     ([ret]_s = zero32 /\ [ret2]_s = one32 /\
        [flag]_s <> zero32 /\ u2Z [a0]_s > u2Z [a1]_s) \/
     ([ret]_s = zero32 /\ [ret2]_s = zero32 /\
        [flag]_s <> zero32 /\ u2Z [a0]_s = u2Z [a1]_s))).

move=> s h [r_k [r_a [r_b [Hmem [ni [r_i [ni_nk [Hsum [r_a0 [r_a1 [
  [r_ret [r_flag Hneq] ] |
  [r_ret [r_flag Hneq]]]]]]]]]]]]].
- rewrite /wp_sltu; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  exists ni; repeat (split; trivial).
  left; split; first by [].
  rewrite ifF //; apply/negbTE/ltZP; rewrite -leZNgt; exact/ltZW.
- rewrite /wp_sltu; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.
  exists ni; repeat (split; trivial).
  right.
  move/Z.ge_le : Hneq; case/leZ_eqVlt => Hneq.
  * right; repeat (split => //).
    by rewrite Hneq ltZZ'.
  * left; repeat (split; trivial).
    by move/ltZP : Hneq => ->.
    exact/Z.lt_gt.

(**  movn flag r0 ret2 ; *)

apply hoare_movn with (fun s h => u2Z [k]_s = Z_of_nat nk /\ [a]_s = va /\
  [b]_s = vb /\ (var_e a |--> A ** var_e b |--> B) s h /\
  exists ni, u2Z [i]_s = Z_of_nat ni /\ (ni < nk)%nat /\
    \S_{ nk - S ni } (drop (S ni) A) = \S_{ nk - S ni} (drop (S ni) B) /\
    [a0]_s = A `32_ ni /\ [a1]_s = B `32_ ni /\
    (([ret]_s = one32 /\ [ret2]_s = zero32 /\ [flag]_s = zero32 /\ u2Z [a0]_s < u2Z [a1]_s) \/
     ([ret]_s = zero32 /\ [ret2]_s = one32 /\ [flag]_s = zero32 /\ u2Z [a0]_s > u2Z [a1]_s) \/
     ([ret]_s = zero32 /\ [ret2]_s = zero32 /\ [flag]_s <> zero32 /\ u2Z [a0]_s = u2Z [a1]_s))).

move=> s h [r_k [r_a [r_b [Hmem [ni [r_i [ni_nk [Hsum [r_a0 [r_a1 [
[r_ret [r_ret2 [r_flag Hneq] ] ] |
[[r_ret [r_ret2 [r_flag Hneq] ] ] |
[r_ret [r_ret2 [r_flag Hneq]]]]]]]]]]]]]]].
- rewrite /wp_movn; repeat Reg_upd; split=> r_ret2'.
  + by rewrite r_ret2 in r_ret2'.
  + repeat (split; trivial).
    exists ni; repeat (split; trivial).
    by left.
- rewrite /wp_movn; repeat Reg_upd; split=> r_ret2'.
  + repeat (split; trivial).
    by Assert_upd.
    exists ni; repeat (split; trivial).
    by right; left.
  + rewrite r_ret2 in r_ret2'.
    have {r_ret2'} : u2Z one32 = u2Z zero32 by rewrite r_ret2'.
    by rewrite ?Z2uK.
- rewrite /wp_movn; repeat Reg_upd; split => r_ret2'.
  + by rewrite r_ret2 in r_ret2'.
  + repeat (split; trivial).
    exists ni; repeat (split; trivial).
    by right; right.

(**  movz flag r0 i
). *)

apply hoare_movz'.

move=> s h [r_k [r_a [r_b [Hmem [ni [r_i [Hnink [Hsum [r_a0 [r_a1 [ [r_ret [r_ret2 [r_flag Hneq]] ] |
[ [r_ret [r_ret2 [r_flag Hneq]] ] |
[r_ret [r_ret2 [r_flag Hneq] ]]]]]]]]]]]]]].
- rewrite /wp_movz; repeat Reg_upd; split => r_i'.
  + repeat (split; trivial).
    by Assert_upd.
    exists ni; repeat (split; trivial).
    by rewrite ltnW.
    right; split; first by [].
    left; split; first by [].
    have ? : ni = O.
      symmetry in r_i; move: r_i.
      rewrite r_i' Z2uK //; by move/Z_of_nat_0.
    subst ni.
    rewrite subn0 !drop0.
    destruct nk as [|nk].
    * by move: (lt_irrefl O).
    * split; first by [].
      destruct A => //; destruct B => //.
      rewrite /= subn1 /= !drop0 in Hsum.
      rewrite /nth' /= in r_a0 r_a1.
      rewrite 2!lSum_S Hsum -r_a0 -r_a1; exact/ltZ_add2r.
  + repeat (split; trivial).
    exists ni; repeat (split; trivial).
    exact/ltnW.
    right; split; first by [].
    left; split; first by [].
    destruct nk as [|nk].
    * by rewrite ltn0 in Hnink.
    * split; first by []; rewrite /= in Hsum.
      rewrite subSn; last by rewrite -ltnS.
      rewrite (drop_nth zero32); last by rewrite HlenA.
      apply Z.gt_lt.
      rewrite -/(A `32_ ni) -r_a0 lSum_S [drop _ _]/= (drop_nth zero32); last by rewrite HlenB.
      rewrite -/(B `32_ ni) [drop _ _]/= -r_a1 lSum_S Hsum; exact/Z.lt_gt/ltZ_add2r.
- rewrite /wp_movz; repeat Reg_upd; split => r_i'.
  + repeat (split; trivial).
    by Assert_upd.
    exists ni; split; first by [].
    split; first exact/ltnW.
    right; split; first by [].
    right; left; split; first by [].
    have ? : ni = O.
      symmetry in r_i; move: r_i.
      rewrite r_i' Z2uK //; by move/Z_of_nat_0.
    subst ni.
    rewrite /= subn0.
    rewrite /= in Hsum.
    destruct A.
    * rewrite -HlenA in Hnink; by rewrite lt0n in Hnink.
    * destruct B.
      - by rewrite -HlenB in Hnink; rewrite lt0n in Hnink.
      - rewrite /= in Hsum.
        destruct nk.
        + by rewrite ltnn in Hnink.
        + split; first by [].
          rewrite /= subn1 !drop0 in Hsum.
          rewrite /nth' /= in r_a0 r_a1.
          rewrite 2!lSum_S Hsum -r_a0 -r_a1; exact/Z.lt_gt/ltZ_add2r/Z.gt_lt.
  + repeat (split; trivial).
    exists ni; split; trivial.
    split; first exact/ltnW.
    right; split; first by [].
    right; left; split; first by [].
    rewrite /= in Hsum.
    destruct A.
    * rewrite -HlenA in Hnink; by rewrite ltn0 in Hnink.
    * destruct B.
      - rewrite -HlenB in Hnink; by rewrite ltn0 in Hnink.
      - split; first by [].
        rewrite /= in Hsum.
        rewrite (drop_nth zero32); last by rewrite HlenA.
        apply Z.lt_gt.
        rewrite (drop_nth zero32); last by rewrite HlenB.
        have -> : (nk - ni = S (nk - S ni))%nat by rewrite -subSn.
        simpl drop; rewrite 2!lSum_S.
        rewrite Hsum -!/(nth' _ _ _).
        rewrite -r_a0 -r_a1; exact/ltZ_add2r/Z.gt_lt.
- rewrite /wp_movz; repeat Reg_upd; split=> r_i'.
  + repeat (split; trivial).
    by Assert_upd.
    exists ni; split; trivial.
    split; first exact/ltnW.
    right; split; first by [].
    right; right; split; first by [].
    split; first by [].
    have ? : ni = O.
      rewrite r_i' Z2uK // in r_i.
      symmetry in r_i; by move/Z_of_nat_0 : r_i.
    subst ni.
    rewrite /= subn0.
    rewrite /= in Hsum.
    destruct nk => //; destruct A => //; destruct B => //.
    rewrite /= subn1 !drop0 in Hsum.
    rewrite /nth' /= in r_a0 r_a1.
    by rewrite 2!lSum_S Hsum -r_a0 -r_a1 Hneq.
  + repeat (split; trivial).
    exists ni; split; first by [].
    split; first exact/ltnW.
    left; split; first by [].
    split; first by [].
    rewrite /= in Hsum.
    destruct nk as [|nk].
    * by rewrite ltn0 in Hnink.
    * destruct A => //; destruct B => //.
      rewrite /= in Hsum.
      rewrite subSn; last by rewrite -ltnS.
      rewrite (drop_nth zero32); last by rewrite HlenA.
      symmetry.
      rewrite (drop_nth zero32); last by rewrite HlenB.
      rewrite 2!lSum_S Hsum; simpl drop.
      by rewrite -!/(nth' _ _ _) -r_a0 -r_a1 Hneq.
Qed.

End multi_lt.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_tactics.
Import expr_m.
Import assert_m.

Require Import pick_sign_prg.

Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope uniq_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.

Lemma pick_sign_triple P Q va slen a a0 a1 : uniq(a, a0, a1, r0) ->
  inde (a1 :: a0 :: nil) Q -> inde (a1 :: a0 :: nil) P ->
  {{ fun s h => [a ]_ s = va /\ (var_e a |~> int_e slen ** Q) s h /\
     P s h}}
  pick_sign a a0 a1
  {{ fun s h => [a ]_ s = va /\ [a0 ]_ s = slen /\
     sgZ (s2Z [a1 ]_ s) = sgZ (s2Z slen) /\
     (s2Z [ a1 ]_ s = 0 \/ s2Z [ a1 ]_ s = 1 \/ s2Z [ a1 ]_s = - 1) /\
     (var_e a |~> int_e slen ** Q) s h /\ P s h }}.
Proof.
move=> Hregs inde_Q inde_P.
rewrite /pick_sign.

(** lw a0 zero16 a ; *)

apply hoare_lw_back_alt'' with (fun s h => [a ]_ s = va /\ [a0]_s = slen /\
  (var_e a |~> int_e slen ** Q) s h /\ P s h).

rewrite /while.entails => s h [r_a [Hmem HP]].
exists slen; split.
- move: Hmem; apply assert_m.monotony => // h'.
  apply assert_m.mapsto_ext => //=.
  by rewrite sext_Z2u // addi0.
- rewrite /mips_contrib.update_store_lw.
  repeat Reg_upd; repeat (split => //).
  Assert_upd; apply (incl_inde _ _ _ inde_Q); by intuition.
  Assert_upd; apply (incl_inde _ _ _ inde_P); by intuition.

(** If_beq a0,r0 Then *)

apply while.hoare_ifte.

(** addiu a1 r0 zero16 *)

apply hoare_addiu' => s h [[a_va [a0_slen [mem HP]]]].
move/eqP/u2Z_inj => /=.
rewrite store.get_r0 => a0_0.
rewrite /wp_addiu.
repeat Reg_upd; repeat (split => //).
- rewrite add0i -a0_slen a0_0; by rewrite sext_Z2u.
- left; rewrite add0i sext_Z2u // s2Z_u2Z_pos'; by rewrite Z2uK.
- Assert_upd. apply (incl_inde _ _ _ inde_Q); by intuition.
- rewrite /inde in inde_P.
  rewrite -(incl_inde _ _ _ inde_P) //.
  + by apply List.incl_refl.
  + In_tac.

(** srl a1 a0 (Z2u 5 31) ; *)

apply mips_contrib.hoare_srl with (fun s h => [a ]_ s = va /\ [a0 ]_ s = slen /\
  bZsgn (u2Z [a1]_s) = sgZ (s2Z slen) /\ (var_e a |~> int_e slen ** Q) s h /\
  P s h).

rewrite /while.entails => s h [[r_a [r_a0 [Hmem HP]]] a0_0].
rewrite /mips_seplog.wp_srl.
repeat Reg_upd; repeat (split => //).
- rewrite r_a0 Z2uK // (_ : '|31| = 2 ^ 5 - 1)%nat //.
  apply (@bZsgn_Zsgn_s2Z 5 slen).
  rewrite -r_a0.
  rewrite /= in a0_0.
  move/eqP : a0_0.
  by rewrite store.get_r0 Z2uK.
- Assert_upd. apply (incl_inde _ _ _ inde_Q); by intuition.
- rewrite /inde in inde_P.
  rewrite -(incl_inde _ _ _ inde_P) //.
  + by apply List.incl_refl.
  + In_tac.

(** If_beq a1,r0 Then *)

apply while.hoare_ifte.

(** addiu a1 r0 one16 *)

apply hoare_addiu' => s h [[a_va [a0_slen [sgn_a1 [mem HP]]]] Ha1].
rewrite /wp_addiu.
repeat Reg_upd; repeat (split => //).
- rewrite add0i sext_Z2u // s2Z_u2Z_pos'; last by rewrite Z2uK.
  rewrite Z2uK //=.
  rewrite /= in Ha1.
  move/eqP : Ha1.
  by rewrite store.get_r0 Z2uK // => Ha1; rewrite Ha1 /bZsgn /= in sgn_a1.
- right; left.
  by rewrite add0i sext_Z2u // s2Z_u2Z_pos' Z2uK.
- Assert_upd. apply (incl_inde _ _ _ inde_Q); by intuition.
- rewrite /inde in inde_P.
  rewrite -(incl_inde _ _ _ inde_P) //.
  + by apply List.incl_refl.
  + In_tac.

(** addiu a1 r0 mone16 *)

apply hoare_addiu' => s h [[a_va [a0_slen [sgn_a1 [mem HP]]]] Ha1].
rewrite /wp_addiu.
repeat Reg_upd; repeat (split => //).
- rewrite add0i sext_Z2s //.
  rewrite /= in Ha1.
  move/eqP : Ha1; rewrite store.get_r0 Z2uK //; move/eqP => Ha1.
  by rewrite -sgn_a1 /bZsgn (negbTE Ha1) Z2sK.
- right; right.
  by rewrite add0i sext_Z2s // Z2sK.
- Assert_upd. apply (incl_inde _ _ _ inde_Q); by intuition.
- rewrite /inde in inde_P.
  rewrite -(incl_inde _ _ _ inde_P) //.
  + exact: List.incl_refl.
  + In_tac.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_frame mips_tactics mips_contrib mapstos.
Require Import multi_zero_s_prg multi_zero_u_triple multi_negate_triple.
Import expr_m.
Import assert_m.

Local Open Scope heap_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.

Lemma multi_zero_s'_triple rx a0 a1 a2 a3 : uniq(rx, a0, a1, a2, a3, r0) ->
  forall nk X vx ptr, size X = nk ->
    u2Z vx + 4 * 2 < Zbeta 1 ->
    u2Z ptr + 4 * Z_of_nat nk < Zbeta 1 ->
  {{ fun s h => [ rx ]_s = vx /\
     (var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil ** int_e ptr |--> X) s h }}
  multi_zero_s' rx a0 a1 a2 a3
  {{ fun s h => [ rx ]_s = vx /\
      [ a0 ]_s = Z2u 32 (Z_of_nat nk) /\
     (var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil ** int_e ptr |--> nseq nk zero32) s h }}.
Proof.
move=> regs nk X vx ptr len_X vx_fit ptr_fit.
rewrite /multi_zero_s.

(** lw a0 zero16 rx *)

apply mips_contrib.hoare_lw_back_alt'' with (fun s h => [rx ]_ s = vx /\
  (var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil ** int_e ptr |--> X) s h /\
  u2Z [ a0 ]_ s = Z_of_nat nk).
move=> s h [Hx mem].
exists (Z2u 32 (Z_of_nat nk)); split.
- rewrite /= assert_m.conAE in mem.
  move: mem; apply assert_m.monotony => // h'.
  apply assert_m.mapsto_ext => //.
  by rewrite sext_Z2u //= addi0.
- rewrite /mips_contrib.update_store_lw.
  repeat Reg_upd.
  repeat (split=> //).
  move: mem; apply assert_m.monotony => // h'.
  apply assert_m.mapstos_ext => //=.
  by Reg_upd.
  apply assert_m.mapstos_ext => //.
  rewrite Z2uK // -Zbeta1E.
  split; first exact: Zle_0_nat.
  move: (min_u2Z ptr) => ?; lia.

(** lw a1 four16 rx *)

apply mips_contrib.hoare_lw_back_alt'' with (fun s h => [rx ]_ s = vx /\
  (var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: List.nil ** int_e ptr |--> X) s h /\
  u2Z [ a0 ]_ s = Z_of_nat nk /\ [ a1 ]_ s = ptr).
move=> s h [Hx [mem Ha0]].
exists ptr; split.
- rewrite /= assert_m.conAE assert_m.conCE assert_m.conAE in mem.
  move: mem; apply assert_m.monotony => // h' mem.
  case: mem => h1 [h2 [Hdisj [Hunion [Hh1 [Hh2 H']]]]].
  rewrite /assert_m.emp in H'; subst h2.
  rewrite heap.unionhe in Hunion; subst h'.
  move: Hh1; apply assert_m.mapsto_ext => //=.
  by rewrite sext_Z2u //.
- rewrite /mips_contrib.update_store_lw.
  repeat Reg_upd.
  repeat (split => //).
  move: mem; apply assert_m.monotony => // h'.
  apply assert_m.mapstos_ext => //=.
  by Reg_upd.
  by apply assert_m.mapstos_ext.

(** multi_zero a0 a1 a2 a3 *)

apply (before_frame
  (fun s h => [rx ]_ s = vx /\ (var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil) s h)
  (fun s h => [a1]_s = ptr /\ u2Z [a0]_s = Z_of_nat nk /\ (var_e a1 |--> X) s h)
  (fun s h => [a1]_s = ptr /\ u2Z [a0]_s = Z_of_nat nk /\ (var_e a1 |--> nseq nk zero32) s h)).

- apply mips_frame.frame_rule_R.
  apply multi_zero_u_triple => //; by Uniq_uniq r0.
  by Inde_frame.
  by move=> ?; Inde_mult.
- rewrite /while.entails => s h [Hx [mem [Ha0 Ha1]]].
  case: mem => h1 [h2 [Hdisj [Hunion [Hh1 Hh2]]]].
  Compose_sepcon h2 h1.
  repeat (split=> //).
  move: Hh2; by apply assert_m.mapstos_ext.
  by repeat (split=> //).
- rewrite /while.entails => s h mem.
  case: mem => h1 [h2 [Hdisj [Hunion [[Ha1 [Ha0 Hh1]] [Hrx Hh2]]]]].
  split; first by assumption.
  split.
    apply u2Z_inj.
    rewrite Ha0 Z2uK //.
    split; first by apply Zle_0_nat.
    rewrite -Zbeta1E; move: (min_u2Z ptr) => ?; lia.
  Compose_sepcon h2 h1; first by [].
  move: Hh1; by apply assert_m.mapstos_ext.
Qed.

Lemma multi_zero_s_triple rx : uniq(rx, r0) -> forall X ptr slen,
  {{ var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X }}
  multi_zero_s rx
  {{ var_e rx |--> zero32 :: ptr :: nil ** int_e ptr |--> X }}.
Proof.
move=> Hnodup X ptr slen.
rewrite /multi_zero_s.
apply hoare_sw_back'.
move=> s h Hmem.
exists (int_e slen).
rewrite /= assert_m.conAE in Hmem.
move: Hmem; apply monotony => h'.
  apply mapsto_ext => //.
  by rewrite /= sext_Z2u // addi0.
apply currying => h'' Hmem.
rewrite assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem => /=.
rewrite !assert_m.conAE.
apply monotony => h3 //.
apply mapsto_ext => /=.
  by rewrite sext_Z2u // addi0.
by rewrite store.get_r0.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool seq.
Require Import ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_tactics.
Import expr_m.
Import assert_m.

Require Import multi_negate_prg.

Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope uniq_scope.

Lemma multi_negate_triple_new a a0 slen ptr A' : uniq(a, a0, r0) -> forall va,
  {{ fun s h => [a]_s = va /\ 
     (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A') s h }}
  multi_negate a a0
  {{ fun s h => [a]_s = va /\
    (var_e a |--> cplt2 slen :: ptr :: nil ** int_e ptr |--> A') s h }}.
Proof.
move=> Hregs va; rewrite /multi_negate.

(** lw a0 zero16 a *)

apply hoare_lw_back_alt'' with (fun s h => [a]_s = va /\
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A') s h /\
  [a0]_s = slen).

rewrite /while.entails => s h [Ha Hmem].
exists slen; split.
- rewrite /= !assert_m.conAE in Hmem.
  case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
  Compose_sepcon h1 h2; last by done.
  move: Hh1; apply assert_m.mapsto_ext => //=.
  by rewrite sext_0 addi0.
- rewrite /mips_contrib.update_store_lw.
  repeat Reg_upd.
  repeat (split=> //).
  move: Hmem; apply assert_m.monotony => //= h'.
  apply assert_m.monotony => // h''.
  apply assert_m.mapsto_ext => //=; by Reg_upd.
  apply assert_m.monotony => // h'''; last by Reg_upd.
  apply assert_m.mapsto_ext => //=; by Reg_upd.
  by apply assert_m.mapstos_ext.

(** subu a0 r0 a0 *)

apply mips_contrib.hoare_subu with (fun s h => [a]_s = va /\
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A') s h /\
  [a0 ]_ s = cplt2 slen).

rewrite /while.entails => s h [Ha [Hmem Ha0]].
rewrite /mips_seplog.wp_subu.
repeat Reg_upd.
repeat (split=> //).
- move: Hmem. apply assert_m.monotony => // h'.
  + apply assert_m.monotony => // h''.
    * apply assert_m.mapsto_ext=> //=; by Reg_upd.
    * apply assert_m.monotony => //= h'''; last by Reg_upd.
      apply assert_m.mapsto_ext => //=; by Reg_upd.
  + by apply assert_m.mapstos_ext.
- by rewrite add0i Ha0.

(** sw a0 zero16 a *)

apply mips_contrib.hoare_sw_back'.

rewrite /while.entails => s h [Ha [Hmem Ha0]].
exists (int_e slen).
rewrite /= !assert_m.conAE in Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h1 h2.
- move: Hh1; apply assert_m.mapsto_ext => //=.
  by rewrite sext_0 addi0.
- rewrite /assert_m.imp => h' [h2_d_h' Hh'] h'' Hh''.
  split; first by assumption.
  rewrite /= !assert_m.conAE.
  Compose_sepcon h' h2; last by exact Hh2.
  move: Hh'; apply mapsto_ext.
  + by rewrite /= sext_0 addi0.
  + by rewrite /= Ha0.
Qed.

Lemma multi_negate_triple a a0 slen ptr A' : uniq(a, a0, r0) ->
  {{ var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A' }}
  multi_negate a a0
  {{ var_e a |--> cplt2 slen :: ptr :: nil ** int_e ptr |--> A' }}.
Proof.
move=> Hregs; rewrite /multi_negate.

(** lw a0 zero16 a *)

apply hoare_lw_back_alt'' with (fun s h =>
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A') s h /\
  [a0]_s = slen).

rewrite /while.entails => s h Hmem.
exists slen; split.
- rewrite /= !assert_m.conAE in Hmem.
  case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
  Compose_sepcon h1 h2; last by done.
  move: Hh1; apply assert_m.mapsto_ext => //=.
  by rewrite sext_0 addi0.
- rewrite /mips_contrib.update_store_lw.
  repeat Reg_upd.
  repeat (split=> //).
  move: Hmem; apply assert_m.monotony => //= h'.
  + apply assert_m.monotony => // h''.
    * apply assert_m.mapsto_ext => //=; by Reg_upd.
    * apply assert_m.monotony => // h'''; last by Reg_upd.
      apply assert_m.mapsto_ext => //=; by Reg_upd.
  + by apply assert_m.mapstos_ext.

(** subu a0 r0 a0 *)

apply mips_contrib.hoare_subu with (fun s h => 
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A') s h /\ 
  [a0 ]_ s = cplt2 slen).

rewrite /while.entails => s h [Hmem Ha0].
rewrite /mips_seplog.wp_subu.
repeat Reg_upd.
repeat (split=> //).
- move: Hmem. apply assert_m.monotony => // h'.
  + apply assert_m.monotony => // h''.
    * apply assert_m.mapsto_ext=> //=; by Reg_upd.
    * apply assert_m.monotony => //= h'''; last by Reg_upd.
      apply assert_m.mapsto_ext => //=; by Reg_upd.
  + by apply assert_m.mapstos_ext.
- by rewrite add0i Ha0.

(** sw a0 zero16 a *)

apply mips_contrib.hoare_sw_back'.

rewrite /while.entails => s h [Hmem Ha0].
exists (int_e slen).
rewrite /= !assert_m.conAE in Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h1 h2.
- move: Hh1; apply assert_m.mapsto_ext => //=.
  by rewrite sext_0 addi0.
- rewrite /assert_m.imp.
  move=> h' [h2_d_h' Hh'] h'' Hh''.
  rewrite /= !assert_m.conAE.
  Compose_sepcon h' h2; last by exact Hh2.
  move: Hh'; apply mapsto_ext.
  + by rewrite /= sext_0 addi0.
  + by rewrite /= Ha0.
Qed.

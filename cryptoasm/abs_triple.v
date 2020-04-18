(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool.
Require Import ZArith uniq_tac machine_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_tactics.
Import expr_m.
Import assert_m.

Require Import abs_prg.

Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope uniq_scope.
Local Open Scope machine_int_scope.
Local Open Scope Z_scope.

Lemma abs_triple_bang rx a : uniq(rx, a, r0) ->
  forall vx, s2Z vx <> - 2 ^31 ->
  {{ !(fun s => [ rx ]_ s = vx) }}
  abs rx a
  {{ !(fun s => s2Z [ rx ]_ s  = Z.abs (s2Z vx)) }}.
Proof.
move=> Hnodup vx Hvx.
rewrite /abs.
apply mips_contrib.hoare_addu with
  (!(fun s => [rx ]_ s = vx /\ [ a ]_s = [ rx ]_s )).
move=> s h /= H.
rewrite /wp_addu.
case: H => ? H; subst h.
split => //.
repeat Reg_upd.
by rewrite add0i.
apply mips_contrib.hoare_sra with
  !(fun s => [rx ]_ s = vx /\
    ((0 <= s2Z [rx]_s /\ [a]_s = zero32)
    \/
    (s2Z [rx]_s < 0 /\ [a]_s = int_not zero32)))%mips_expr.
move=> s h [] [H1 H2] ?; subst h.
rewrite /wp_sra.
split => //.
repeat Reg_upd.
split; first by assumption.
rewrite Z2uK //.
case: (Z_lt_le_dec (s2Z vx) 0) => H.
right.
split; first by congruence.
rewrite s2Z_shra_neg //.
by subst vx.
left.
split; first by congruence.
rewrite s2Z_shra_pos //.
 congruence.
apply mips_contrib.hoare_xor with
  !(fun s => (0 <= s2Z vx  /\ [a]_s = zero32 /\ [rx]_s = vx)
    \/
    (s2Z vx < 0 /\ [a]_s = int_not zero32 /\ [rx]_s = int_not vx))%mips_expr.
move=> s h [] [H1 H2] ?; subst h.
rewrite /wp_xor.
split => //.
repeat Reg_upd.
case : H2 => H2.
- case: H2 => H2 H3.
  left.
  subst vx.
  split; first by assumption.
  split; first by assumption.
  by rewrite H3 int_xor_0.
- case: H2 => H2 H3.
  right.
  subst vx.
  split; first by assumption.
  split; first by assumption.
  by rewrite H3 int_xor_1s.
apply mips_contrib.hoare_subu'.
move=> s h [] H ?; subst h.
case: H => [ [H1 [a0 rxvx]] | [H1 [H2 H3]]]; rewrite /wp_subu; split => //; Reg_upd.
- by rewrite a0 cplt2_zero addi0 rxvx Z.abs_eq.
- rewrite H3 H2 cplt2_1s not_add_1_cplt2 // s2Z_cplt2 //.
  rewrite Zabs_non_eq //; omega.
  by rewrite weirdE2.
Qed.

Lemma abs_triple rx a : uniq(rx, a, r0) ->
  forall vx, s2Z vx <> - 2 ^31 ->
  {{ fun s h => [ rx ]_ s = vx }}
  abs rx a
  {{ fun s h => s2Z [ rx ]_ s = Z.abs (s2Z vx)}}.
Proof.
move=> Hnodup vx Hvx.
rewrite /abs.
apply mips_contrib.hoare_addu with
  (fun s _ => [rx ]_ s = vx /\ [ a ]_s = [ rx ]_s)%mips_expr.
move=> s h /= H.
rewrite /wp_addu.
repeat Reg_upd.
by rewrite add0i.
apply mips_contrib.hoare_sra with
  (fun s _ => [rx ]_ s = vx /\
    ((0 <= s2Z [rx]_s /\ [a]_s = zero32)
    \/
    (s2Z [rx]_s < 0 /\ [a]_s = int_not zero32)))%mips_expr.
move=> s h [H1 H2].
rewrite /wp_sra.
repeat Reg_upd.
split; first by assumption.
rewrite Z2uK //.
case: (Z_lt_le_dec (s2Z vx) 0) => H.
right.
split; first by congruence.
rewrite s2Z_shra_neg //.
by subst vx.
left.
split; first by congruence.
rewrite s2Z_shra_pos //.
by congruence.
apply mips_contrib.hoare_xor with
  (fun s _ =>
    (0 <= s2Z vx  /\ [a]_s = zero32 /\ [rx]_s = vx)
    \/ (s2Z vx < 0 /\ [a]_s = int_not zero32 /\ [rx]_s = int_not vx))%mips_expr.
move=> s h [H1 H2].
rewrite /wp_xor.
repeat Reg_upd.
case : H2 => H2.
- case: H2 => H2 H3.
  left.
  subst vx.
  split; first by assumption.
  split; first by assumption.
  by rewrite H3 int_xor_0.
- case: H2 => H2 H3.
  right.
  subst vx.
  split; first by assumption.
  split; first by assumption.
  by rewrite H3 int_xor_1s.
apply mips_contrib.hoare_subu'.
move=> s h [] [H1 [H2 H3]]; rewrite /wp_subu; Reg_upd.
- by rewrite H2 cplt2_zero addi0 H3 Z.abs_eq.
- rewrite H3 H2 cplt2_1s not_add_1_cplt2 // s2Z_cplt2 //.
  rewrite Zabs_non_eq //; omega.
  by rewrite weirdE2.
Qed.

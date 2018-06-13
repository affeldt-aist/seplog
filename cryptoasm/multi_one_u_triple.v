(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_tactics mips_contrib mapstos mips_frame.
Require Import multi_one_u_prg multi_zero_u_triple.
Import expr_m.
Import assert_m.

Local Open Scope heap_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope machine_int_scope.

Lemma multi_one_u_triple k z ext Z_ : uniq(k, z, ext, Z_, r0) ->
  forall nk Z vz, (0 < nk)%nat -> size Z = nk -> u2Z vz + 4 * Z_of_nat nk < Zbeta 1 ->
  {{ fun s h => [z]_s = vz /\ u2Z [k]_s = Z_of_nat nk /\ (var_e z |--> Z) s h }}
    multi_one_u k z ext Z_
  {{ fun s h => [z]_s = vz /\ u2Z [k]_s = Z_of_nat nk /\
   (var_e z |--> one32 :: nseq (nk - 1) zero32) s h }}.
Proof.
move=> Hnodup=> nk Z vz nk0 Z_nk vz_fit.
rewrite /multi_one_u.
apply while.hoare_seq with (fun s h => ([z ]_ s) = vz /\
  u2Z ([k ]_ s) = Z_of_nat nk /\ (var_e z |--> nseq nk zero32) s h).
move/multi_zero_u_triple : (Hnodup).
move/(_ nk Z vz Z_nk vz_fit) => Htmp.
by apply Htmp.
apply hoare_addiu with (fun s h => ([z ]_ s) = vz /\
  u2Z ([k ]_ s) = Z_of_nat nk /\ (var_e z |--> nseq nk zero32) s h /\ [ext]_s = one32).
rewrite /while.entails => s h.
case=> z_vz [k_nk Hmem].
rewrite /wp_addiu.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.
by rewrite add0i sext_Z2u.
apply hoare_sw_back'.
move=> s h.
case => z_vz [k_nk [Hmem Hext]].
exists (int_e zero32).
destruct nk => //.
rewrite /= in Hmem.
move: Hmem.
apply assert_m.monotony => // h1.
  apply assert_m.mapsto_ext => //=.
  by rewrite sext_Z2u // addi0.
apply assert_m.currying => h2 Hh2.
repeat (split => //).
rewrite assert_m.conCE in Hh2.
rewrite /=.
move: Hh2.
apply assert_m.monotony => // h3.
  apply assert_m.mapsto_ext => //=.
  by rewrite sext_Z2u // addi0.
by rewrite subSS subn0.
Qed.

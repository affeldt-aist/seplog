(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Init_ext ZArith_ext uniq_tac.
Require Import machine_int multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_negate_prg multi_negate_termination multi_negate_triple.

Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope machine_int_scope.

Lemma multi_negate_safe_termination a0 rx x nk d : uniq(rx, a0, r0) ->
  safe_termination (state_mint (x |=> signed nk rx \U+ d)) (multi_negate rx a0).
Proof.
move=> Hregs.
rewrite /safe_termination.
move=> s st h s_st_h.
case/(multi_negate_termination st h) : (Hregs) => sf Hsf.
move: (proj1 s_st_h x (signed nk rx)).
rewrite assoc.get_union_sing_eq.
move/(_ (refl_equal _)).
case=> len ptr X rx_fit encX ptr_fit HX.
move/(multi_negate_triple) : (Hregs).
move/(_ len ptr X) => hoare_triple.
apply constructive_indefinite_description'.
move: (triple_exec_precond _ _ _ hoare_triple _ _ _ Hsf (heap.dom (heap_mint (signed nk rx) st h))).
apply.
suff : h |P| heap.dom (heap_mint (signed nk rx) st h) = heap_mint (signed nk rx) st h by move=> ->.
rewrite -heap.incluE; by apply heap_inclu_heap_mint_signed.
Qed.


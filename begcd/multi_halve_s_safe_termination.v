(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Init_ext ZArith_ext uniq_tac machine_int multi_int.
Require Import encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_halve_s_prg multi_halve_s_triple multi_halve_s_termination.

Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope asm_expr_scope.
Local Open Scope asm_cmd_scope.

Lemma multi_halve_s_safe_termination a0 a1 a2 a3 a4 a5 nk rx x d :
  Z_of_nat nk < 2 ^^ 31 ->
  uniq(rx, a0, a1, a2, a3, a4, a5, r0) ->
  safe_termination
  (state_mint (x |=> signed nk rx \U+ d))
  (multi_halve_s rx a0 a1 a2 a3 a4 a5).
Proof.
move=> Hnk Hregs.
rewrite /safe_termination.
move=> s st h s_st_h.
case/(multi_halve_s_termination st h) : (Hregs) => sf Hsf.
move: (proj1 s_st_h x (signed nk rx)).
rewrite assoc.get_union_sing_eq.
move/(_ refl_equal).
case=> len ptr X rx_fit encX ptr_fit HX.
move/(multi_halve_s_triple) : (Hregs).
move/(_ nk ([rx]_st)%asm_expr Hnk ([x]_s)%pseudo_expr) => hoare_triple.
apply constructive_indefinite_description'.
move: (triple_exec_precond _ _ _ hoare_triple _ _ _ Hsf (heap.dom (heap_mint (signed nk rx) st h))).
apply.
split => //.
apply mkVarSigned with len ptr X => //.
suff : heap.proj h (heap.dom (heap_mint (signed nk rx) st h)) = heap_mint (signed nk rx) st h.
  by move=> ->.
rewrite -heap.incluE; by apply heap_inclu_heap_mint_signed.
Qed.

Lemma multi_halve_s_safe_termination2 a0 a1 a2 a3 a4 a5 nk rx x d :
  uniq(rx, a0, a1, a2, a3, a4, a5, r0) ->
  safe_termination
  (fun s st h => state_mint (x |=> signed nk rx \U+ d) s st h /\ Z_of_nat nk < 2 ^^ 31)
  (multi_halve_s rx a0 a1 a2 a3 a4 a5).
Proof.
move=> Hregs.
rewrite /safe_termination.
move=> s st h [s_st_h Hnk].
case/(multi_halve_s_termination st h) : (Hregs) => sf Hsf.
move: (proj1 s_st_h x (signed nk rx)).
rewrite assoc.get_union_sing_eq.
move/(_ (refl_equal _)).
case=> len ptr X rx_fit encX ptr_fit HX.
move/(multi_halve_s_triple) : (Hregs).
move/(_ nk ([rx]_st)%asm_expr Hnk ([x]_s)%pseudo_expr) => hoare_triple.
apply constructive_indefinite_description'.
move: (triple_exec_precond _ _ _ hoare_triple _ _ _ Hsf (heap.dom (heap_mint (signed nk rx) st h))).
apply.
split => //.
apply mkVarSigned with len ptr X => //.
suff : h |P| heap.dom (heap_mint (signed nk rx) st h) = heap_mint (signed nk rx) st h by move=> ->.
rewrite -heap.incluE; by apply heap_inclu_heap_mint_signed.
Qed.

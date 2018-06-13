(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ssrZ ZArith_ext uniq_tac machine_int multi_int.
Require Import encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_one_s_prg multi_one_s_triple multi_one_s_termination.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope asm_expr_scope.

Lemma multi_one_s_safe_termination a0 a1 a2 a3 nk rx rk x d :
  uniq(rx, rk, a0, a1, a2, a3, r0) -> safe_termination
  (fun s st h => state_mint (x |=> signed nk rx \U+ d) s st h /\
                 (0 < (Z_of_nat nk) < 2 ^^ 31) /\ nk = '|u2Z ([rk]_st)|)
  (multi_one_s rx rk a0 a1 a2 a3).
Proof.
move=> Hset.
rewrite /safe_termination.
move=> s st h s_st_h.
case: (multi_one_s_termination st h _ _ _ _ _ _ Hset) => sf Hsf.
move: (multi_one_s_triple rx rk a0 a1 a2 a3 Hset).
move: (proj1 (proj1 s_st_h) x (signed nk rx)).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => len ptr A rx_fit encoding ptr_fit Hmem.
move/(_ nk A ([rx]_st)%asm_expr ptr (proj1 (proj2 s_st_h))).
case: encoding => A_nk len_nk len_x x_A.
move/(_ A_nk rx_fit ptr_fit _ len_nk) => hoare_triple.
apply constructive_indefinite_description'.
move: (mips_syntax.triple_exec_precond _ _ _ hoare_triple _ _ _ Hsf
  (heap.dom (heap_mint (signed nk rx) st h))).
apply.
split; first by [].
split.
  case: s_st_h => _ [] _ ->.
  rewrite Z_of_nat_Zabs_nat //; exact: min_u2Z.
suff : h |P| heap.dom (heap_mint (signed nk rx) st h) = heap_mint (signed nk rx) st h by move=> ->.
rewrite -heap.incluE; exact: heap_inclu_heap_mint_signed.
Qed.

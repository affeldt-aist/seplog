(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Init_ext ssrZ ZArith_ext uniq_tac.
Require Import machine_int multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import copy_s_s_prg copy_s_s_triple copy_s_s_termination.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.

Lemma safe_termination_copy_s_s u x d L rk ru rx a0 a1 a2 a3 a4 : uniq(u, x) ->
  uniq(rk, ru, rx, a0, a1, a2, a3, a4, r0) ->
  safe_termination
  (fun s st h => state_mint (u |=> signed L ru \U+ (x |=> signed L rx \U+ d)) s st h /\
                 L = '| u2Z ([rk]_st) |)
  (copy_s_s rk ru rx a0 a1 a2 a3 a4).
Proof.
move=> Hvars Hregs.
rewrite /safe_termination.
move=> s st h s_st_h.
move/copy_s_s_termination : (Hregs).
case/(_ st h) => si Hsi.
move/copy_s_s_triple : (Hregs).
move: ((proj1 (proj1 s_st_h)) u (signed L ru)).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => lu pu U ru_fit [U_L lu_L lu_u u_U] pu_fit mem_u.
move: ((proj1 (proj1 s_st_h)) x (signed L rx)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => lx px X rx_fit [X_L lx_L lx_x x_X] px_fit mem_x.
move/(_ U X L U_L X_L _ _ pu_fit _ _ px_fit).
move/(_ _ _ _ lx_L).
rewrite -x_X.
move/(_ lu ([rx]_st) lx_x) => hoare_triple.
apply constructive_indefinite_description'.
apply (triple_exec_precond _ _ _ hoare_triple _ _ _ Hsi
  (heap.dom (heap_mint (signed L ru) st h \U
             heap_mint (signed L rx) st h))).
split => //.
split.
  case: s_st_h => _ ->.
  rewrite Z_of_nat_Zabs_nat //.
  by apply min_u2Z.
suff : h |P| heap.dom (heap_mint (signed L ru) st h \U
         heap_mint (signed L rx) st h) =
       heap_mint (signed L ru) st h \U heap_mint (signed L rx) st h.
  move=> ->.
  apply assert_m.con_cons => //.
  apply (proj2 (proj1 s_st_h) u x) => //.
  by Uniq_neq.
  by rewrite assoc.get_union_sing_eq.
  rewrite assoc.get_union_sing_neq; last by Uniq_neq.
  by rewrite assoc.get_union_sing_eq.
rewrite -heap.incluE.
apply heap_prop_m.inclu_union; by apply heap_inclu_heap_mint_signed.
Qed.

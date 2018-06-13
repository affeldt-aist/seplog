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
Require Import copy_u_u_prg copy_u_u_triple copy_u_u_termination.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope asm_expr_scope.
Local Open Scope asm_cmd_scope.
Local Open Scope zarith_ext_scope.

Lemma copy_u_u_safe_termination a0 a1 a2 rk rx x ru u d :
  uniq(x, u) -> uniq(rk, rx, ru, a0, a1, a2, r0) ->
  safe_termination
  (state_mint (x |=> unsign rk rx \U+ (u |=> unsign rk ru \U+ d)))
  (copy_u_u rk rx ru a0 a1 a2).
Proof.
move=> Hvars Hregs.
rewrite /safe_termination.
move=> s st h s_st_h.
set code := copy_u_u _ _ _ _ _ _.
move: (proj1 s_st_h x (unsign rk rx)).
rewrite assoc.get_union_sing_eq.
case/(_ Logic.eq_refl) => rx_fit x_rk Hx.
move: (proj1 s_st_h u (unsign rk ru)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
case/(_ Logic.eq_refl) => ru_fit u_rk Hu.
case: (copy_u_u_termination st h _ _ _ _ _ _ Hregs) => si Hsi.
move: (copy_u_u_triple _ _ _ _ _ _ Hregs
  (Z2ints 32 '|u2Z ([rk ]_ st)| ([u ]_ s)%pseudo_expr)
  (Z2ints 32 '|u2Z ([rk ]_ st)| ([x ]_ s)%pseudo_expr)
  '|u2Z ([rk ]_ st)|).
rewrite 2!size_Z2ints.
move/(_ erefl erefl _ rx_fit) => hoare_triple.
apply constructive_indefinite_description'.
move: (triple_exec_precond _ _ _ hoare_triple _ _ _ Hsi (heap.dom (heap_mint (unsign rk ru) st h \U heap_mint (unsign rk rx) st h))).
apply.
split => //.
split.
  rewrite Z_of_nat_Zabs_nat //; exact/min_u2Z.
suff : h |P|
        heap.dom
           (heap_mint (unsign rk ru) st h \U heap_mint (unsign rk rx) st h) =
heap_mint (unsign rk ru) st h \U heap_mint (unsign rk rx) st h.
  move=> ->.
  apply assert_m.con_cons => //.
  apply (proj2 s_st_h u x) => //.
  by Uniq_neq.
  rewrite assoc.get_union_sing_neq; last by Uniq_neq.
  by rewrite assoc.get_union_sing_eq.
  by rewrite assoc.get_union_sing_eq.
rewrite -heap.incluE.
apply heap_prop_m.inclu_union; by apply heap_inclu_heap_mint_unsign.
Qed.

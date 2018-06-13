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
Require Import multi_sub_s_u_prg multi_sub_s_u_termination multi_sub_s_u_triple.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.

Lemma safe_termination_multi_sub_s_u x b L d rk rx rB a0 a1 a2 a3 a4 ret X :
  uniq(b, x) ->
  uniq(rk, rB, rx, a0, a1, a2, a3, a4, ret, X, r0) ->
  safe_termination (fun s st h =>
    state_mint (b |=> signed L rB \U+ (x |=> unsign rk rx \U+ d)) s st h /\
    L = '|u2Z ([rk]_st)| /\ 0 < Z.of_nat L < 2 ^^ 31)
  (multi_sub_s_u rk rB rx a0 a1 a2 a3 a4 ret X).
Proof.
move=> Hvars Hregs.
rewrite /safe_termination.
move=> s st h [s_st_h [HL L_231]].
case/(multi_sub_s_u_termination st h) : (Hregs) => sf Hsf.
move/multi_sub_s_u_triple : Hregs.
move: (proj1 s_st_h b (signed L rB)).
rewrite assoc.get_union_sing_eq.
move/(_ refl_equal).
case=> lB pB B rB_fit encB pB_fit HB.
move: (proj1 s_st_h x (unsign rk rx)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => rx_fit x_L mem_x.
have L0 : L <> O.
  move=> L0; subst L.
  rewrite L0 in L_231.
  by case: L_231.
rewrite -HL in rx_fit.
rewrite -HL in mem_x.
case: encB => B_L lB_L lB_b b_B.
move/(_ L ([rB ]_ st) [rx]_st pB L0 (proj2 L_231) pB_fit rx_fit
     B (Z2ints 32 L ([ x ]_s)%pseudo_expr) B_L).
rewrite size_Z2ints.
move/(_ refl_equal _ lB_L).
rewrite -b_B.
move/(_ lB_b) => hoare_triple.
apply constructive_indefinite_description'.
apply (triple_exec_precond _ _ _ hoare_triple _ _ _ Hsf
  (heap.dom (heap_mint (signed L rB) st h \U heap_mint (unsign rk rx) st h))).
repeat (split => //).
rewrite HL Z_of_nat_Zabs_nat //; by apply min_u2Z.
suff : h |P| heap.dom (heap_mint (signed L rB) st h \U
         heap_mint (unsign rk rx) st h) =
       heap_mint (signed L rB) st h \U heap_mint (unsign rk rx) st h.
  move=> ->.
  apply assert_m.con_cons => //.
  apply (proj2 s_st_h b x) => //.
  by Uniq_neq.
  by rewrite assoc.get_union_sing_eq.
  rewrite assoc.get_union_sing_neq; last by Uniq_neq.
  by rewrite assoc.get_union_sing_eq.
rewrite -heap.incluE.
apply heap_prop_m.inclu_union.
by apply heap_inclu_heap_mint_signed.
by apply heap_inclu_heap_mint_unsign.
Qed.

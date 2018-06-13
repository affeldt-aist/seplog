(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Init_ext ZArith_ext uniq_tac machine_int multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_add_s_u_prg multi_add_s_u_termination multi_add_s_u_triple.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.

Lemma safe_termination_multi_add_s_u a y L d rk rA ry a0 a1 a2 a3 a4 ret X :
  uniq(a, y) ->
  uniq(rk, rA, ry, a0, a1, a2, a3, a4, ret, X, r0) ->
  safe_termination (fun s st h => state_mint (a |=> signed L rA \U+ (y |=> unsign rk ry \U+ d)) s st h /\
    L = Zabs_nat (u2Z ([rk]_st)) /\ 0 < Z.of_nat L < 2 ^^ 31)
  (multi_add_s_u rk rA ry a0 a1 a2 a3 a4 ret X).
Proof.
move=> Hvars Hregs.
rewrite /safe_termination.
move=> s st h [s_st_h [Hk L_231]].
case/(multi_add_s_u_termination st h) : (Hregs) => sf Hsf.
move/multi_add_s_u_triple : Hregs.
move: (proj1 s_st_h a (signed L rA)).
rewrite assoc.get_union_sing_eq.
move/(_ (refl_equal _)).
case=> lA pA A rA_fit encA pA_fit HA.
move: (proj1 s_st_h y (unsign rk ry)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => ry_fit y_L mem_y.
move/(_ L L_231 ([rA ]_ st) [ry]_st (([a ]_ s)%pseudo_expr) (([y ]_ s)%pseudo_expr)) => hoare_triple.
apply constructive_indefinite_description'.
apply (triple_exec_precond _ _ _ hoare_triple _ _ _ Hsf
  (heap.dom (heap_mint (signed L rA) st h \U 
             heap_mint (unsign rk ry) st h))).
repeat (split => //).
rewrite Hk Z_of_nat_Zabs_nat //; by apply min_u2Z.
suff : h |P| heap.dom (heap_mint (signed L rA) st h \U
         heap_mint (unsign rk ry) st h) =
       heap_mint (signed L rA) st h \U heap_mint (unsign rk ry) st h.
  move=> ->.
  apply assert_m.con_cons => //.
  apply (proj2 s_st_h a y) => //.
  by Uniq_neq.
  by rewrite assoc.get_union_sing_eq.
  rewrite assoc.get_union_sing_neq; last by Uniq_neq.
  by rewrite assoc.get_union_sing_eq.
by apply mkVarSigned with lA pA A => //.
apply mkVarUnsign => //.
congruence.
congruence.
congruence.
rewrite -heap.incluE.
apply heap_prop_m.inclu_union.
by apply heap_inclu_heap_mint_signed.
by apply heap_inclu_heap_mint_unsign.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Init_ext ssrZ ZArith_ext uniq_tac machine_int multi_int.
Require Import encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_add_s_s_u_prg multi_add_s_s_u_termination multi_add_s_s_u_triple.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.

Lemma safe_termination_multi_add_s_s_u z x y d L rz rx rk ry a0 a1 a2 a3 a4 ret rX rY :
  uniq(z, x, y) ->
  uniq(rk, rz, rx, ry, a0, a1, a2, a3, a4, ret, rX, rY, r0) ->
  safe_termination (fun s st h => state_mint (z |=> signed L rz \U+
    (x |=> signed L rx \U+ (y |=> unsign rk ry \U+ d))) s st h /\
    L = '|u2Z ([rk]_st)| /\ 0 < Z.of_nat L < 2 ^^ 31)
  (multi_add_s_s_u rk rz rx ry a0 a1 a2 a3 a4 ret rX rY).
Proof.
move=> Hvars Hregs.
rewrite /safe_termination.
move=> s st h [s_st_h [HL L_231]].
case/(multi_add_s_s_u_termination st h) : (Hregs) => sf Hsf.
move/multi_add_s_s_u_triple : Hregs.
move: (proj1 s_st_h z (signed L rz)).
rewrite assoc.get_union_sing_eq.
move/(_ (Logic.eq_refl _)).
case=> lz pz Z rz_fit encZ pZ_fit HZ.
move: (proj1 s_st_h x (signed L rx)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
move/(_ (Logic.eq_refl _)).
case=> lx px X rx_fit encX pX_fit HX.
move: (proj1 s_st_h y (unsign rk ry)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
case/(_ (Logic.eq_refl _)) => ry_fit y_L mem_y.
move/(_ L [rz]_st [rx]_st [ry]_st L_231 pz px pZ_fit pX_fit).
rewrite -HL in ry_fit.
move/(_ ry_fit Z X (Z2ints 32 L [y ]_ s)%pseudo_expr).
case: encZ => ZL Zlz lzz zZ.
move/(_ ZL).
case: encX => XL Xlx lxx xX.
move/(_ XL).
rewrite size_Z2ints.
move/(_ Logic.eq_refl lx lz Xlx Zlz).
rewrite -{1}xX.
move/(_ lxx) => hoare_triple.
apply constructive_indefinite_description'.
apply (triple_exec_precond _ _ _ hoare_triple _ _ _ Hsf
  (heap.dom (heap_mint (signed L rz) st h \U
             heap_mint (signed L rx) st h \U
             heap_mint (unsign rk ry) st h))).
repeat (split => //).
rewrite HL Z_of_nat_Zabs_nat //; by apply min_u2Z.
suff : h |P| heap.dom ((heap_mint (signed L rz) st h \U heap_mint (signed L rx) st h) \U
            heap_mint (unsign rk ry) st h) =
       (heap_mint (signed L rz) st h \U heap_mint (signed L rx) st h) \U
            heap_mint (unsign rk ry) st h.
  move=> ->.
  rewrite -assert_m.conAE.
  apply assert_m.con_cons => //.
  - apply heap.disjUh.
      apply (proj2 s_st_h z y) => //.
      by Uniq_neq.
      by rewrite assoc.get_union_sing_eq.
      rewrite assoc.get_union_sing_neq; last by Uniq_neq.
      rewrite assoc.get_union_sing_neq; last by Uniq_neq.
      by rewrite assoc.get_union_sing_eq.
    apply (proj2 s_st_h x y) => //.
    by Uniq_neq.
    rewrite assoc.get_union_sing_neq; last by Uniq_neq.
    by rewrite assoc.get_union_sing_eq.
    rewrite assoc.get_union_sing_neq; last by Uniq_neq.
    rewrite assoc.get_union_sing_neq; last by Uniq_neq.
    by rewrite assoc.get_union_sing_eq.
  - apply assert_m.con_cons => //.
    + apply (proj2 s_st_h z x) => //.
      by Uniq_neq.
      by rewrite assoc.get_union_sing_eq.
      rewrite assoc.get_union_sing_neq; last by Uniq_neq.
      by rewrite assoc.get_union_sing_eq.
      apply con_heap_mint_unsign_cons with (heap_mint (unsign rk ry) st h) => //.
      by apply heap_inclu_heap_mint_unsign.
      rewrite size_Z2ints; congruence.
      rewrite size_Z2ints; congruence.
      congruence.
rewrite -heap.incluE.
apply heap_prop_m.inclu_union.
apply heap_prop_m.inclu_union.
by apply heap_inclu_heap_mint_signed.
by apply heap_inclu_heap_mint_signed.
by apply heap_inclu_heap_mint_unsign.
Qed.

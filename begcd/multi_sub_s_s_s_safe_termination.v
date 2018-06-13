(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ZArith_ext.
Require Import ssrZ machine_int multi_int encode_decode integral_type uniq_tac.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_sub_s_s_s_prg multi_sub_s_s_s_termination multi_sub_s_s_s_triple.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.

Lemma safe_termination_multi_sub_s_s_s z x y d L rz rx rk ry a0 a1 a2 a3 a4 ret rX rY rZ :
  uniq(z, x, y) ->
  uniq(rk, rz, rx, ry, a0, a1, a2, a3, a4, ret, rX, rY, rZ, r0) ->
  safe_termination (fun s st h => state_mint (z |=> signed L rz \U+
    (x |=> signed L rx \U+ (y |=> signed L ry \U+ d))) s st h /\
  L = '|u2Z ([rk]_st)| /\ 0 < Z.of_nat L < 2 ^^ 31)
  (multi_sub_s_s_s rk rz rx ry a0 a1 a2 a3 a4 ret rX rY rZ).
Proof.
move=> Hvars Hregs.
rewrite /safe_termination.
move=> s st h [s_st_h [HL L_231]].
case/(multi_sub_s_s_s_termination st h) : (Hregs) => sf Hsf.
move/multi_sub_s_s_s_triple : Hregs.
move: (proj1 s_st_h z (signed L rz)).
rewrite assoc.get_union_sing_eq.
move/(_ (Logic.eq_refl _)).
case=> lz pz Z rz_fit encZ pZ_fit HZ.
move: (proj1 s_st_h x (signed L rx)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
move/(_ (Logic.eq_refl _)).
case=> lx px X rx_fit encX pX_fit HX.
move: (proj1 s_st_h y (signed L ry)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
move/(_ (Logic.eq_refl _)).
case=> ly py Y ry_fit encY pY_fit HY.
move/(_ L [rx]_st [ry]_st [rz]_st px py pz L_231 pX_fit pY_fit pZ_fit X Y Z).
case: encX => XL Xlx lxx xX.
move/(_ XL).
case: encY => YL Yly lyy yY.
move/(_ YL).
case: encZ => ZL Zlz lzz zZ.
move/(_ ZL).
move/(_ lx ly lz Xlx Yly Zlz).
rewrite -{1}xX -{1}yY -{1}zZ.
move/(_ lxx lyy lzz) => hoare_triple.
apply constructive_indefinite_description'.
apply (triple_exec_precond _ _ _ hoare_triple _ _ _ Hsf
  (heap.dom (heap_mint (signed L rz) st h \U
             heap_mint (signed L rx) st h \U
             heap_mint (signed L ry) st h))).
repeat (split => //).
rewrite HL Z_of_nat_Zabs_nat //; by apply min_u2Z.
suff : h |P| heap.dom ((heap_mint (signed L rz) st h \U heap_mint (signed L rx) st h) \U
            heap_mint (signed L ry) st h) =
       (heap_mint (signed L rz) st h \U heap_mint (signed L rx) st h) \U
            heap_mint (signed L ry) st h.
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
rewrite -heap.incluE.
apply heap_prop_m.inclu_union.
  apply heap_prop_m.inclu_union; exact/heap_inclu_heap_mint_signed.
exact/heap_inclu_heap_mint_signed.
Qed.

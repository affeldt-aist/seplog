(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Init_ext ZArith_ext seq_ext uniq_tac.
Require Import machine_int multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import copy_s_u_prg copy_s_u_triple copy_s_u_termination.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope asm_expr_scope.

Lemma copy_s_u_safe_termination a0 a1 a2 a3 rk ry y rx x d :
  uniq(x, y) ->  uniq(rk, rx, ry, a0, a1, a2, a3, r0) ->
  safe_termination
  (fun st s h => state_mint (x |=> signed (Z.abs_nat (u2Z ([rk ]_ s))) rx \U+
      (y |=> unsign rk ry \U+ d s)) st s h)
  (copy_s_u rk rx ry a0 a1 a2 a3).
Proof.
move=> Hvars Hnodup.
rewrite /safe_termination => st s h st_s_h.
case: (copy_s_u_termination s h _ _ _ _ _ _ _ Hnodup) => si Hsi.
move: (proj1 st_s_h x (signed (Z.abs_nat (u2Z ([rk ]_ s))) rx)).
rewrite assoc.get_union_sing_eq.
move/(_ (refl_equal _)).
case=> len ptr U ru_fit encU ptr_fit HU.
case: encU => u1 u2 u3 u4.
move: (proj1 st_s_h y (unsign rk ry)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => rx_fit Hx HX.
move: (copy_s_u_triple _ _ _ _ _ _ _ Hnodup U (Z2ints 32 (Z.abs_nat (u2Z ([rk ]_ s)))
               ([ y ]_ st)%pseudo_expr) (Z.abs_nat (u2Z ([rk ]_ s))) u1).
rewrite size_Z2ints.
move/(_ (refl_equal _) len ptr ptr_fit _ rx_fit) => hoare_triple.
apply constructive_indefinite_description'.
move: (triple_exec_precond _ _ _ hoare_triple _ _ _ Hsi
  (heap.dom (heap_mint (signed (Z.abs_nat (u2Z ([rk ]_ s))) rx) s h \U
  heap_mint (unsign rk ry) s h))).
apply.
split; first reflexivity.
split; first by rewrite Z_of_nat_Zabs_nat //; exact: min_u2Z.
suff : h |P|
        (heap.dom (heap_mint (signed (Z.abs_nat (u2Z ([rk ]_ s))) rx) s h \U
            heap_mint (unsign rk ry) s h)) =
       heap_mint (signed (Z.abs_nat (u2Z ([rk ]_ s))) rx) s h \U
                 heap_mint (unsign rk ry) s h.
  move=> ->.
  apply assert_m.con_cons => //.
  apply (proj2 st_s_h x y) => //; by [Uniq_neq | assoc_get_Some | assoc_get_Some].
rewrite -heap.incluE.
apply heap_prop_m.inclu_union.
exact: heap_inclu_heap_mint_signed.
exact: heap_inclu_heap_mint_unsign.
Qed.

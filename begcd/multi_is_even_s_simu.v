(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Require Import encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_cmd mips_tactics mips_syntax.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_is_even_s_prg multi_is_even_s_triple.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope multi_int_scope.

Lemma fwd_sim_b_multi_is_even_s x rx rk a0 a1 L d : uniq(rx, rk, a0, a1, r0) ->
  0 < Z_of_nat L < 2 ^^ 31 ->
  fwd_sim_b
  (state_mint (x |=> signed L rx \U+ d))
  (var_e x \% nat_e 2 \= nat_e 0)%pseudo_expr
  (multi_is_even_s rx rk a0 a1)
  (bne a1 r0).
Proof.
move=> Hset HL.
rewrite /fwd_sim_b.
move=> s st h s_st_h.
move: (proj1 s_st_h x (signed L rx)).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => len ptr A rx_fit encoding ptr_fit Hmem.
case: encoding => H1 H2 H3 H4.
have htmp : s2Z len <> - 2 ^ 31.
  move=> abs.
  rewrite abs (_ : sgZ (- 2 ^ 31) = -1) // mulN1Z in H2.
  apply Z.opp_inj in H2.
  rewrite -H2 in HL.
  by case: HL => _ => /ltZZ.
move: (multi_is_even_s_triple _ _ _ _ Hset L A len ptr H1 htmp H2) => hoare_triple.
have [st' Hst'] : exists st',
  (Some (st, heap_mint (signed L rx) st h) -- multi_is_even_s rx rk a0 a1 ---> st')%mips_cmd.
  exact: no_while_terminate.
move/mips_seplog.hoare_prop_m.soundness : (hoare_triple).
rewrite /while.hoare_semantics.
case/(_ st (heap_mint (signed L rx) st h) Hmem) => no_fail.
destruct st' as [[st' h']|] => //.
clear no_fail.
case/(_ _ _ Hst') => Heven Hodd.
exists st'.
split.
  have : heap_mint (signed L rx) st h = h'.
    eapply no_sw_heap_invariant.
    apply Hst'.
    by [].
    reflexivity.
    reflexivity.
  move=> ?; subst h'.
  move/safety_monotonicity : (Hst').
  have X : heap_mint (signed L rx) st h
    # h \D\ heap.dom (heap_mint (signed L rx) st h).
    exact/heap.disj_difs'/inc_refl.
  move/(_ _ X).
  rewrite -heap.union_difsK //; last exact: heap_inclu_heap_mint_signed.
  by case.
rewrite /= /ZIT.eqb /ZIT.rem store.get_r0 Z2uK //.
split => [/eqP Hx | Ha1].
  rewrite Heven.
    by rewrite Z2uK.
  rewrite -H4; exact: Zmod_2_Zeven.
apply/eqP/Zeven_Zmod_2.
rewrite H4.
case: (Zeven_odd_dec (sgZ (s2Z len) * \S_{ L } A)) => // /Hodd abs.
by rewrite abs Z2uK in Ha1.
Qed.

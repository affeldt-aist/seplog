(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ssrZ ZArith_ext seq_ext uniq_tac.
Require Import machine_int multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_is_even_u_prg multi_is_even_u_triple.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope asm_cmd_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.

Lemma var_mint_multi_is_even u rk ru s st h a0 :
  uniq(rk, ru, a0, r0) ->
  var_mint u (unsign rk ru) s st (heap_mint (unsign rk ru) st h) ->
  forall st' h',
    Some (st, h) -- multi_is_even_u rk ru a0 ---> Some (st', h')->
  (([var_e u \% nat_e 2 \= nat_e 1 ]b_ s)%pseudo_expr <-> [ beq a0 r0 ]b_ st').
Proof.
move=> Hset u_ru st' h' exec_asm.
case: u_ru => u_ru u_ru' u_ru''.
  move: (multi_is_even_u_triple _ _ _ Hset '|u2Z ([rk ]_ st)| (Z2ints 32 '|u2Z ([rk ]_ st)| ([u ]_ s)%pseudo_expr) ([ru]_st)).
  rewrite size_Z2ints.
  move/(_ refl_equal) => hoare_triple.
  move/mips_seplog.hoare_prop_m.soundness : (hoare_triple).
  rewrite /while.hoare_semantics.
  move/(_ st (heap_mint (unsign rk ru) st h)).
  rewrite Z_of_nat_Zabs_nat; last exact: min_u2Z.
  move/( _ (conj (refl_equal _) (conj (refl_equal _) u_ru''))).
  case=> _.
  have exec_asm':
    ((Some (st, heap_mint (unsign rk ru) st h)) -- multi_is_even_u rk ru a0 ---> Some (st', heap_mint (unsign rk ru) st h')).
    rewrite /heap_mint /heap_cut.
    eapply mips_syntax.triple_exec_proj; last exact: exec_asm.
    apply hoare_triple.
    rewrite /= Z_of_nat_Zabs_nat //; exact: min_u2Z.
  case/(_ _ _ exec_asm') => Hrk [Hru [Hmem [Heven Hodd]]].
split.
- rewrite /= /ZIT.eqb /ZIT.rem => /eqP X.
  rewrite store.get_r0 Z2uK //.
  apply/eqP.
  rewrite Hodd //; last first.
    rewrite lSum_Z2ints_pos //.
    apply not_Zmod_2_Zodd; by rewrite X.
  by rewrite Z2uK.
- rewrite /= /ZIT.eqb /ZIT.rem => /eqP X.
  rewrite store.get_r0 Z2uK // in X.
  apply/eqP.
  rewrite lSum_Z2ints_pos // in Heven.
  rewrite lSum_Z2ints_pos // in Hodd.
  case: (Zeven_odd_dec ([u]_s)%pseudo_expr).
    move/Heven => abs.
    by rewrite abs Z2uK in X.
  by apply Zodd_Zmod_2.
Qed.

Lemma fwd_sim_b_multi_is_even_u u rk ru d a0 : uniq(rk, ru, a0, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: nil) ->
  u \notin assoc.dom d ->
  unsign rk ru \notin assoc.cdom d ->
  fwd_sim_b (state_mint (u |=> unsign rk ru \U+ d ))
  (var_e u \% nat_e 2 \= nat_e 1)%pseudo_expr
  (multi_is_even_u rk ru a0)
  (beq a0 r0).
Proof.
move=> Hregs d_a0 u_d rk_ru_d.
rewrite /fwd_sim_b => s st h s_st_h.
set nk := '|u2Z [rk]_st|.
set U := Z2ints 32 nk ([ u ]_ s)%pseudo_expr.
have Hpre : (var_e ru |--> U)%asm_assert st (heap_mint (unsign rk ru) st h).
  move: (proj1 s_st_h u (unsign rk ru)).
  rewrite assoc.get_union_sing_eq. case/(_ refl_equal) => _ [_]; exact.
move: (multi_is_even_u_triple _ _ _ Hregs nk U [ru]_st).
rewrite /U size_Z2ints.
move/(_ (refl_equal _)) => Htriple.
set code := multi_is_even_u _ _ _.
have [st' Hst'] : exists st', Some (st, h) -- code ---> Some (st', h).
  have [[st' he'] Hst'] : exists st', Some (st, h) -- code ---> Some st'.
    apply constructive_indefinite_description'.
    eapply mips_seplog.hoare_prop_m.termi.
    - apply mips_frame.frame_rule_R with (R := assert_m.TT).
      + exact: Htriple.
      + by Inde.
      + move=> ?; by Inde_mult.
    - move=> s0 h0 /= H.
      apply Epsilon.constructive_indefinite_description.
      by apply mips_syntax.no_while_terminate.
    - exists (heap_mint (unsign rk ru) st h).
      exists (h \D\ iota '|u2Z ([ru ]_ st) / 4| nk).
      split.
        rewrite /= /heap_cut.
        by apply heap.proj_difs_disj, inc_refl.
      split.
        rewrite /= /heap_cut; by apply heap.proj_difs.
      split; last by [].
      split; first by rewrite /nk Z_of_nat_Zabs_nat //; apply min_u2Z.
      split; first by reflexivity.
      exact Hpre.
  exists st'.
  suff : h = he' by move=> X; rewrite -X in Hst'.
  by apply (mips_syntax.no_sw_heap_invariant _ _ _ Hst' refl_equal _ _ _ _ refl_equal refl_equal).
exists st'; split; first by exact Hst'.
move/mips_seplog.soundness : (Htriple).
rewrite /while.hoare_semantics.
move/(_ st (heap_mint (unsign rk ru) st h)).
rewrite {1}/nk Z_of_nat_Zabs_nat; last by apply min_u2Z.
case/(_ (conj (refl_equal _) (conj (refl_equal _) Hpre))) => _ Hpost.
move: {Htriple}(triple_exec_proj _ _ _ Htriple) => Hexec_proj.
rewrite {1}/nk Z_of_nat_Zabs_nat in Hexec_proj; last by apply min_u2Z.
rewrite /heap_mint /heap_cut in Hpre.
move: {Hexec_proj Hpre}(Hexec_proj _ _ _ _ _ (conj refl_equal (conj refl_equal Hpre)) Hst').
move/Hpost => {}Hpost.
case: Hpost => Hrk' [Hru' [Hmem Hret]].
rewrite lSum_Z2ints_pos in Hret; last first.
  move: (proj1 s_st_h u (unsign rk ru)).
  rewrite assoc.get_union_sing_eq.
  move/(_ refl_equal).
  rewrite /var_mint.
  by case=> ? [].
split=> [u_mod_2|].
+ apply/eqP.
  congr (Z<=u _).
  rewrite store.get_r0.
  apply (proj2 Hret).
  rewrite /= in u_mod_2.
  apply not_Zmod_2_Zodd.
  move/eqP : u_mod_2; by rewrite /ZIT.rem => ->.
+ move => u_mod_2.
  apply/eqP => /=.
  move/eqP : u_mod_2.
  rewrite store.get_r0 Z2uK // => Ha0.
  case: (Zeven_odd_dec ([u ]_ s)%pseudo_expr) => Hu.
  by rewrite (proj1 Hret Hu) Z2uK in Ha0.
  by apply Zodd_Zmod_2.
Qed.

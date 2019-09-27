(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ssrZ ZArith_ext seq_ext machine_int uniq_tac multi_int.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_frame mips_syntax.
Import expr_m.
Require Import integral_type.
Require Import simu.
Import simu_m.
Require Import multi_lt_prg multi_lt_triple multi_lt_termination.

Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope uniq_scope.
Local Open Scope assoc_scope.
Local Open Scope heap_scope.
Local Open Scope asm_expr_scope.
Local Open Scope asm_cmd_scope.
Local Open Scope mips_hoare_scope.

Lemma fwd_sim_b_ge_multi_lt rk ru rv a3 flag a0 a1 ret ret2 z u d :
  uniq(z, u) ->
  uniq(rk, ru, rv, a3, flag, ret, ret2, a0, a1, r0) ->
  fwd_sim_b (state_mint (u |=> unsign rk ru \U+ (z |=> unsign rk rv \U+ d)))
  (var_e u \>= var_e z)%pseudo_expr
  (multi_lt rk ru rv a3 flag ret ret2 a0 a1)
  (beq ret r0).
Proof.
move=> Hvars Hregs.
rewrite /fwd_sim_b => s st h s_st_h.
set nk := '|u2Z [rk]_st|.
set U := Z2ints 32 nk ([ u ]_ s)%pseudo_expr.
set ZE := Z2ints 32 nk ([ z ]_ s)%pseudo_expr.
have Hpre : (var_e ru |--> U ** var_e rv |--> ZE)%asm_assert st
  (heap_mint (unsign rk ru) st h \U heap_mint (unsign rk rv) st h).
  apply assert_m.con_cons.
  - apply (proj2 s_st_h u z); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  - move: (proj1 s_st_h u (unsign rk ru)).
    rewrite assoc.get_union_sing_eq. case/(_ (refl_equal _)) => _ [_]; exact.
  - move: (proj1 s_st_h z (unsign rk rv)).
    rewrite assoc_prop_m.swap_heads; last by rewrite [Equality.sort _]/= in Hvars *; Uniq_uniq O.
    rewrite assoc.get_union_sing_eq. case/(_ (refl_equal _)) => _ [_]; exact.
move: (multi_lt_triple _ _ _ _ _ _ _ _ _ Hregs nk U ZE [ru]_st [rv]_st).
rewrite /U size_Z2ints /ZE size_Z2ints.
move/(_ Logic.eq_refl Logic.eq_refl) => Htriple.
set code := multi_lt _ _ _ _ _ _ _ _ _.
have [st' Hst'] : exists st', Some (st, h) -- code ---> Some (st', h).
  have [[st' he'] Hst'] : exists st', Some (st, h) -- code ---> Some st'.
    apply constructive_indefinite_description'.
    eapply hoare_prop_m.termi.
    - apply frame_rule_R with (R := assert_m.TT).
      + exact: Htriple.
      + by Inde.
      + move=> ?; by Inde_mult.
    - move=> s0 h0 /= H.
      apply multi_lt_termination; by Uniq_uniq r0.
    - exists (heap_mint (unsign rk ru) st h \U heap_mint (unsign rk rv) st h).
      exists (h \D\ (iota '|u2Z ([ru ]_ st) / 4| nk ++
                      iota '|u2Z ([rv ]_ st) / 4| nk)).
      split.
        rewrite /= /heap_cut -heap.proj_app.
        exact/heap.proj_difs_disj/inc_refl.
      split.
        rewrite /= /heap_cut -heap.proj_app; exact: heap.proj_difs.
      split; last by [].
      split; first by rewrite /nk Z_of_nat_Zabs_nat //; apply min_u2Z.
      split; first by reflexivity.
      split; first by reflexivity.
      exact Hpre.
  exists st'.
  suff : h = he' by move=> X; rewrite -X in Hst'.
  by apply (no_sw_heap_invariant _ _ _ Hst' Logic.eq_refl _ _ _ _ erefl erefl).
exists st'; split; first by exact Hst'.
move/mips_seplog.soundness : (Htriple).
rewrite /while.hoare_semantics.
move/(_ st (heap_mint (unsign rk ru) st h \U heap_mint (unsign rk rv) st h)).
rewrite {1}/nk Z_of_nat_Zabs_nat; last by apply min_u2Z.
case/(_ (conj (refl_equal _) (conj (refl_equal _) (conj (refl_equal _) Hpre)))) => _ Hpost.
move: {Htriple}(mips_syntax.triple_exec_proj _ _ _ Htriple) => Hexec_proj.
rewrite {1}/nk Z_of_nat_Zabs_nat in Hexec_proj; last by apply min_u2Z.
rewrite /heap_mint /heap_cut -heap.proj_app in Hpre.
move: {Hexec_proj Hpre}(Hexec_proj _ _ _ _ _ (conj (refl_equal _) (conj (refl_equal _) (conj (refl_equal _) Hpre))) Hst').
rewrite heap.proj_app.
move/Hpost => {}Hpost.
case: Hpost => Hrk' [Hru' [Hrv' [Hret Hmem]]].
rewrite lSum_Z2ints_pos in Hret; last first.
  move: (proj1 s_st_h u (unsign rk ru)).
  rewrite assoc.get_union_sing_eq.
  move/(_ (refl_equal _)).
  rewrite /var_mint.
  by case=> _ [].
rewrite lSum_Z2ints_pos in Hret; last first.
  move: (proj1 s_st_h z (unsign rk rv)).
  rewrite assoc_prop_m.swap_heads; last by rewrite [Equality.sort _]/= in Hvars *; Uniq_uniq O.
  rewrite assoc.get_union_sing_eq.
  move/(_ (refl_equal _)).
  rewrite /var_mint.
  by case=> _ [].
split => u_z.
+ case: Hret => Hret.
  * (* absurd *) case: Hret => u_z' _.
    rewrite /= in u_z.
    move/ZIT.geP : u_z; rewrite /ZIT.ge => u_z.
    exfalso; omega.
  * apply/eqP.
    rewrite store.get_r0.
    f_equal.
    tauto.
+ case : Hret => Hret.
  * exfalso.
    move/negP : u_z => /=; apply.
    case: Hret => _ [] -> _.
    by rewrite store.get_r0 !Z2uK.
  * apply/geZP.
    case: Hret.
    - case=> Hret _.
      exact/Z.le_ge/ltZW/Z.gt_lt.
    - case => /= => -> _.
      exact/Z.le_ge/leZZ.
Qed.

Lemma fwd_sim_b_gt_multi_lt rk ru rv a3 flag a0 a1 ret ret2 z u d :
  uniq(z, u) -> uniq(rk, ru, rv, a3, flag, ret, ret2, a0, a1, r0) ->
  fwd_sim_b (state_mint (u |=> unsign rk ru \U+ (z |=> unsign rk rv \U+ d)))
  (var_e z \> var_e u)%pseudo_expr
  (multi_lt rk ru rv a3 flag ret ret2 a0 a1)
  (bne ret r0).
Proof.
move=> Hvars Hset.
apply fwd_sim_b_cond_neg with (var_e u \>= var_e z)%pseudo_expr (beq ret r0).
move=> s st h s_st_h.
rewrite /= ZIT.gebNgt.
exact/negbRL.
by move=> ?.
exact: fwd_sim_b_ge_multi_lt.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Require Import encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_halve_s_prg multi_halve_s_triple.

Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope simu_scope.

(** x <- x / 2, x signed *)

Lemma pfwd_sim_halve_s (x : bipl.var.v) d k rx a0 a1 a2 a3 a4 a5 :
  uniq(rx, a0, a1, a2, a3, a4, a5, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: nil) ->
  x \notin assoc.dom d ->
  signed k rx \notin assoc.cdom d ->
  (x <- var_e x ./e nat_e 2)%pseudo_expr%pseudo_cmd
    <=p( state_mint (x |=> signed k rx \U+ d), fun st s h => Z_of_nat k < 2 ^^ 31)
  multi_halve_s rx a0 a1 a2 a3 a4 a5.
Proof.
move=> Hnodup Hdisj x_d rx_d.
rewrite /pfwd_sim.
move=> st s h [st_s_h k_231] st' exec_pseudo s' h' exec_asm.

move/state_mint_var_mint : (st_s_h).
move/(_ x (signed k rx)).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => slen ptr A rx_fit A_x ptr_fit memA.

move/multi_halve_s_triple_gen : (Hnodup).
case: A_x => A_nk slen_nk slen_x x_A.
move/(_ k k_231 ([ rx ]_ s)%asm_expr rx_fit _ ptr_fit _ slen_nk _ A_nk).
rewrite x_A in slen_x.
move/(_ slen_x) => Hhoare_triple.

have [s'' [h'' exec_triple_proj]] : exists s'' h'',
  (Some (s, heap.proj h (heap.dom (heap_mint (signed k rx) s h))) --
    multi_halve_s rx a0 a1 a2 a3 a4 a5 ---> Some (s'', h''))%asm_cmd.
  exists s', (heap.proj h' (heap.dom (heap_mint (signed k rx) s h))).
  apply: (mips_syntax.triple_exec_proj _ _ _ Hhoare_triple) => //.
  split; first by reflexivity.
  suff : heap.proj h (heap.dom (heap_mint (signed k rx) s h)) = heap_mint (signed k rx) s h.
    by move=> ->.
  by apply heap.incluE, heap_inclu_heap_mint_signed.

set postcond := (fun _ _ => exists _, _) in Hhoare_triple.
have {Hhoare_triple}Hoare_triple_post_cond : (postcond ** assert_m.TT)%asm_assert s' h'.
  move: (mips_frame.frame_rule_R _ _ _ Hhoare_triple assert_m.TT (assert_m.inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
  move/mips_seplog.hoare_prop_m.soundness.
  rewrite /while.hoare_semantics.
  move/(_ s h) => Hhoare_triple_sem.
  lapply Hhoare_triple_sem; last first.
    exists (heap_mint (signed k rx) s h), (h \D\ heap.dom (heap_mint (signed k rx) s h)).
    split; first by apply heap.disj_difs', seq_ext.inc_refl.
    split.
      apply heap.union_difsK => //; by apply heap_inclu_heap_mint_signed.
    split; last by [].
    split; first by reflexivity.
    assumption.
  move=> {Hhoare_triple_sem}[Hhoare_triple_sem Hhoare_triple_sem'].
  by apply Hhoare_triple_sem' in exec_asm.
split.
- have rx_st_st' : ([ rx ]_ s = [ rx ]_ s')%asm_expr.
    Reg_unchanged. rewrite [mips_frame.modified_regs _]/=. by Uniq_not_In.
  move=> y my.
  case/assoc.get_union_Some_inv.
  + (* y = x *)  case/assoc.get_sing_inv => ? ?; subst y my.
    case: Hoare_triple_post_cond => h1 [h2 [h1dh2 [h1Uh2 [Hh1 _]]]].
    rewrite /postcond in Hh1.
    case: Hh1 => slen' [A' [A'_nk [slen'_nk [slen'_A' [rx_st'_st [Hmem' Hdiv]]]]]].
    apply mkVarSigned with slen' ptr A' => //.
    * congruence.
    * apply mkSignMagn => //.
      - move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
        syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        rewrite x_A /ZIT.div -Hdiv -mulZA mulZC Z_div_plus_full_l //.
        rewrite Zdiv_small //; last first.
          move: (shrl_lt ([a3 ]_ s')%asm_expr 31) => /= ?.
          move: (min_u2Z (([a3 ]_ s')%asm_expr `>> 31)) => ?.
          lia.
        by rewrite addZ0.
      - rewrite /ZIT.div.
        move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
        syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        rewrite x_A /ZIT.div -Hdiv.
        rewrite -mulZA mulZC Z_div_plus_full_l //.
        rewrite Zdiv_small //; last first.
          move: (shrl_lt ([a3 ]_ s')%asm_expr 31) => /= ?.
          move: (min_u2Z (([a3 ]_ s')%asm_expr `>> 31)) => ?.
          lia.
        by rewrite addZ0.
      - apply con_heap_mint_signed_cons with h1 => //.
        rewrite h1Uh2.
        apply heap.inclu_union_L => //; by apply heap.inclu_refl.
        congruence.
        by rewrite A'_nk.
  + (* y \in d *) move=> y_my.
    have y_x : y <> x.
      move=> ?; subst y.
      apply assoc.get_Some_in in y_my.
      rewrite -assoc.elts_dom in x_d.
      move/negP : x_d; apply.
      apply/mapP.
      by exists (x, my).
    move: (proj2 st_s_h _ _ y_x my (signed k rx)).
    rewrite assoc.get_union_sing_neq; last by [].
    rewrite assoc.get_union_sing_eq.
    move/(_ y_my (refl_equal _)) => heap_mint_disj.
    move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ exec_triple_proj) => [st'_st'' [h''_h' h_h']].
    have Hd_unchanged : forall v r, assoc.get v d = Some r ->
      disj (mint_regs r) (mips_frame.modified_regs (multi_halve_s rx a0 a1 a2 a3 a4 a5)).
      move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
      apply (disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
      exact/incP/inc_mint_regs/(assoc.get_Some_in_cdom _ v).
    have <- : heap_mint my s h = heap_mint my s' h'.
      apply (heap_mint_state_invariant (heap_mint (signed k rx) s h) y st) => //.
      move=> ry Hry; Reg_unchanged.
      apply (@disj_not_In _ (mint_regs my)); last by [].
      exact/disj_sym/(Hd_unchanged y).
      move: (proj1 st_s_h y my).
      rewrite assoc.get_union_sing_neq; last by [].
      by apply.
    apply var_mint_invariant with st s => //.
    * move=> ry ry_my; Reg_unchanged.
      apply (@disj_not_In _ (mint_regs my)); last by [].
      apply/disj_sym/(Hd_unchanged y) => //.
    * Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    * move: (proj1 st_s_h y my).
      rewrite assoc.get_union_sing_neq; last by [].
      by apply.
- have Hdom : heap.dom (heap_mint (signed k rx) s' h') = heap.dom (heap_mint (signed k rx) s h).
    symmetry.
    case: Hoare_triple_post_cond => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
    case: Hh1 => slen' [A' [A'_nk [slen'_nk [slen'_A' [rx_s'_s [Hh1 Hdiv]]]]]].
    apply (dom_heap_mint_sign_state_invariant _ _ _ _ _ _ x st slen slen') => //.
      by move/assert_m.mapstos_get1/heap_get_heap_mint_inv : memA.
    apply assert_m.mapstos_get1 in Hh1.
    rewrite h1_U_h2. by apply heap.get_union_L => //.
    apply assert_m.mapstos_get2 in memA.
    apply assert_m.mapstos_get2 in Hh1.
    rewrite h1_U_h2.
    apply heap_get_heap_mint_inv in memA.
    rewrite memA.
    symmetry.
    by apply heap.get_union_L.
    apply mkVarSigned with slen ptr A => //.
    apply mkSignMagn => //.
    congruence.
    by eapply dom_heap_invariant; eauto.
- apply (state_mint_part2_one_variable _ _ _ _ _ _ _ _ st_s_h Hdom).
  + move=> t x0 Ht Hx0.
    Reg_unchanged. simpl mips_frame.modified_regs.
    case/assoc.in_cdom_union_inv : Ht => Ht.
    * rewrite assoc.cdom_sing /= seq.mem_seq1 in Ht.
      move/eqP : Ht => Ht; subst t.
      apply (@disj_not_In _ (mint_regs (signed k rx))); last by [].
      Disj_remove_dup.
      rewrite /=.
      apply uniq_disj.
      rewrite [cat _ _]/=.
      by Uniq_uniq r0.
    * apply (@disj_not_In _ (mint_regs t)); last by [].
      Disj_remove_dup.
      apply/disj_sym/(disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
      exact/incP/inc_mint_regs.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ exec_triple_proj); tauto.
  + by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
Qed.

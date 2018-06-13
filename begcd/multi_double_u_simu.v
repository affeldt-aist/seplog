(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Require Import encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_double_u_prg multi_double_u_triple.

Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope simu_scope.

(** x <- x * 2, x unsigned *)

Lemma pfwd_sim_double_u (x : bipl.var.v) (d : assoc.t) (rk rx a0 a1 a2 a3 : reg) :
  uniq(rk, rx, a0, a1, a2, a3, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: a2 :: a3 :: nil) ->
  x \notin assoc.dom d -> unsign rk rx \notin assoc.cdom d ->
  (x <- var_e x \* nat_e 2)%pseudo_expr%pseudo_cmd
    <=p( state_mint (x |=> unsign rk rx \U+ d), fun s st h =>
         ([ x ]_ s)%pseudo_expr < 2 ^^ ('|u2Z ([ rk ]_st)%asm_expr| * 32 - 1))
  multi_double_u rk rx a0 a1 a2 a3.
Proof.
move=> Haux Hd Hd' Hd''.
rewrite /pfwd_sim.
move=> s st h [s_st_h x_k] s' exec_pseudo st' h' exec_mips.
have d_unchanged : forall v r, assoc.get v d = Some r ->
    disj (mint_regs r) (mips_frame.modified_regs (multi_double_u rk rx a0 a1 a2 a3)).
  move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
  apply (disj_incl_LR Hd); last by apply incl_refl_Permutation; PermutProve.
  exact/incP/inc_mint_regs/(assoc.get_Some_in_cdom _ v).
set k := '|u2Z ([rk ]_ st)%asm_expr|.
move/multi_double_u_triple : (Haux).
move/(_ '|u2Z ([rk ]_ st)%asm_expr| ([rx ]_ st)%asm_expr
  (state_mint_head_unsign_fit _ _ _ _ _ _ _ s_st_h) (Z2ints 32 k ([var_e x ]e_ s)%pseudo_expr)).
rewrite size_Z2ints.
move/(_ Logic.eq_refl) => hoare_triple_double_u.

have [st'' [h'' exec_mips_proj]] : exists st'' h'',
  (Some (st, heap.proj h (heap.dom (heap_mint (unsign rk rx) st h)))
  -- multi_double_u rk rx a0 a1 a2 a3 ---> Some (st'', h''))%mips_cmd.
  exists st', (heap.proj h' (heap.dom (heap_mint (unsign rk rx) st h))).
  move/mips_syntax.triple_exec_proj : hoare_triple_double_u; apply => //.
  split; first by [].
  split; first by rewrite Z_of_nat_Zabs_nat //; apply min_u2Z.
  rewrite /heap_cut heap.proj_dom_proj.
  apply (state_mint_var_mint _ _ _ _ x (unsign rk rx)) in s_st_h; last by assoc_get_Some.
  rewrite /var_mint in s_st_h.
  by case: s_st_h => _ [_ ?].

set postcond := (fun s h => exists _, _) in hoare_triple_double_u.
have {hoare_triple_double_u}hoare_triple_post_condition : ( postcond ** assert_m.TT)%asm_assert
     st' h'.
    move: (mips_frame.frame_rule_R _ _ _ hoare_triple_double_u assert_m.TT (assert_m.inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
    move/mips_seplog.hoare_prop_m.soundness.
    rewrite /while.hoare_semantics.
    move/(_ st h) => Hdouble_u.
    lapply Hdouble_u; last first.
      exists (heap_mint (unsign rk rx) st h), (h \D\ heap.dom (heap_mint (unsign rk rx) st h)).
      split; first by apply heap.disj_difs', seq_ext.inc_refl.
      split.
        apply heap.union_difsK => //; by apply heap.inclu_proj.
      split; last by [].
      split; first by [].
      split.
      rewrite Z_of_nat_Zabs_nat //; by apply min_u2Z.
      move: (state_mint_var_mint _ s st h x (unsign rk rx) s_st_h).
        rewrite assoc.get_union_sing_eq.
        case/(_ refl_equal) => ? ? ?; tauto.
    move=> {Hdouble_u} [Hdouble_u Hdouble_u'].
    by move: {Hdouble_u'}(Hdouble_u' _ _ exec_mips).
split.
- move=> y ry y_ry.
  have [yx | yx] : y \in assoc.dom d \/ y = x.
    case/assoc.get_union_Some_inv : y_ry => y_ry.
    * by case/assoc.get_sing_inv : y_ry => -> _; right.
    * by apply assoc.get_Some_in_dom in y_ry; left.
  + (* y \in assoc.dom d *) have x_y : y <> x.
      move=> ?; subst y; by rewrite yx in Hd'.
    move: {s_st_h}(proj1 s_st_h _ _ y_ry) (proj2 s_st_h) => s_st_h1 s_st_h2.
    have y_unchanged : ([ y ]_s = [ y ]_s')%pseudo_expr.
      Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    case: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_mips
      (heap.dom (heap_mint (unsign rk rx) st h)) _ _ exec_mips_proj) => H4 [H5 H_h_h'].
    have <- : heap_mint ry st h = heap_mint ry st' h'.
      apply (heap_mint_state_invariant (heap_mint (unsign rk rx) st h) y s) => //.
      move=> rx0 Hrx0; Reg_unchanged.
      apply (@disj_not_In _ (mint_regs ry)); last by [].
      apply/disj_sym/(d_unchanged y).
      by rewrite -y_ry assoc.get_union_sing_neq.
      apply s_st_h2 with y x => //.
      by rewrite assoc.get_union_sing_eq.
    move: s_st_h1; apply var_mint_invariant.
    move=> rx0 Hrx0; Reg_unchanged.
    apply (@disj_not_In _ (mint_regs ry)); last by [].
    apply/disj_sym/(d_unchanged y) => //.
    by rewrite -y_ry assoc.get_union_sing_neq.
    Var_unchanged; rewrite /= mem_seq1; exact/negP/eqP.
  + (* yx : y = x *) subst y.
    have ? : ry = unsign rk rx.
      rewrite assoc.get_union_sing_eq in y_ry.
      by case: y_ry.
    subst ry.
    set vx := u2Z ([ rx ]_ st)%asm_expr.
    set k' := '| u2Z ([ rk ]_ st')%asm_expr |.
    set vx' := u2Z ([ rx ]_ st')%asm_expr.
  move: (state_mint_var_mint _ s st h x (unsign rk rx) s_st_h).
    rewrite assoc.get_union_sing_eq.
    case/(_ refl_equal) => X1 X2 X3.
    case : hoare_triple_post_condition => h1 [h2 [Hdisj [Hunion [[A' [Hmul2_1 [Hmul2_2 [Hmul2_3 [Hmul2_4 Hmul2_5]]]]] HTT]]]].

    have k_k' : k = k' by rewrite /k /k' Hmul2_3 Z_of_nat_Zabs_nat //; apply min_u2Z.
    subst k'.
    apply mkVarUnsign.
    + by rewrite -k_k' Hmul2_2.
    + split.
      - move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
        syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        apply mulZ_ge0 => //; tauto.
      - move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
        syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        rewrite /ZIT.mul mulZC.
        case : (ltnP 0 k) => Hk'; last first.
          rewrite leqn0 in Hk'. move/eqP in Hk'.
          rewrite -/k Hk' ZbetaE mul0n /= in X2.
          have {X2}X2 : ([x]_s = 0)%pseudo_expr by omega.
          rewrite X2 mulZ0; by apply Zbeta_gt0.
        - rewrite -k_k' ZbetaE (_ : k * 32 = S (k * 32 - 1))%nat; last first.
            by rewrite -subSn // ?subn1 // muln_gt0 Hk'.
          rewrite ZpowerS; exact/ltZ_pmul2l.
    + apply mapstos_inv_list2heap in Hmul2_4 => //; last first.
        by rewrite [eval _ _]/= Hmul2_2 Hmul2_1.
      rewrite u2Z_shrl' in Hmul2_4; last by repeat constructor.
      rewrite /= Hmul2_2 in Hmul2_4.
      rewrite /heap_cut Hunion Hmul2_4.
      move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
      case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
      syntax_m.seplog_m.assert_m.expr_m.Store_upd.
      rewrite lSum_Z2ints_pos // [ ( [ _ ]e_ _ )%pseudo_expr ]/= in Hmul2_5.
      rewrite /ZIT.mul mulZC.
      case: (zerop k) => Hk'.
      - rewrite -k_k' Hk' Z2ints_0 /= /heap_cut heap.proj_nil.
        split; last by [].
        move/assert_m.mapstos_inv_addr : X3 => /=.
        by rewrite Hmul2_2.
      - have Htmp : u2Z ([a2 ]_st')%asm_expr = 0.
          have Htmp1 : 2 * ([ x ]_ s)%pseudo_expr < 2 ^^ (k * 32).
            rewrite (_ : k * 32 = S (k * 32 - 1))%nat; last first.
              move/ltP in Hk'.
              by rewrite -subSn // ?subn1 // muln_gt0 Hk'.
            rewrite ZpowerS; exact/ltZ_pmul2l.
          rewrite -Hmul2_5 in Htmp1.
          move: (min_u2Z ([a2]_st')%asm_expr).
          case/leZ_eqVlt => Htmp2 //.
          rewrite addZC mulnC in Htmp1. (* TODO *)
          move/(poly_Zlt1_inv _ _ _ (min_lSum _ _) (min_u2Z _) (expZ_ge0 _)) : Htmp1 => Htmp1.
          rewrite Htmp1 in Htmp2; by move/ltZZ : Htmp2.
        rewrite -Hmul2_5.
        rewrite Htmp.
        rewrite mul0Z addZ0.
        rewrite Z_of_nat_Zabs_nat in Hmul2_3.
        rewrite Hmul2_3.
        rewrite -Z2ints_lSum.
        rewrite /heap_cut.
        rewrite Hmul2_2.
        have <- : heap.dom (list2heap '|vx / 4| A') = iota '|vx / 4| k.
          by rewrite dom_list2heap Hmul2_1.
        rewrite heap.proj_union_L_dom; last by rewrite -Hmul2_4.
        rewrite heap.proj_itself.
        apply mapstos_list2heap.
        + rewrite Z_of_nat_Zabs_nat //; last first.
            apply Z_div_pos => //; by apply min_u2Z.
          rewrite -Zdivide_Zdiv_eq //.
          by rewrite -Hmul2_2.
          move/assert_m.mapstos_inv_addr : X3.
          by apply Zmod_divide.
        + rewrite /vx in X1.
          rewrite [eval _ _]/= Hmul2_2; omega.
        + by [].
        + by apply min_u2Z.
- apply (state_mint_part2_one_variable_unsign _ _ _ _ _ _ _ _ _ s_st_h).
  + move=> t x0 Ht Hx0.
    Reg_unchanged. simpl mips_frame.modified_regs.
    case/assoc.in_cdom_union_inv : Ht => Ht.
    * rewrite assoc.cdom_sing /= seq.mem_seq1 in Ht.
      move/eqP : Ht => Ht; subst t.
      apply (@disj_not_In _ (mint_regs (unsign rk rx))); last by [].
      simpl.
      Disj_remove_dup.
      by Disj_uniq r0.
    * apply (@disj_not_In _ (mint_regs t)); last by [].
      Disj_remove_dup.
      apply/disj_sym/(disj_incl_LR Hd); last by apply incl_refl_Permutation; PermutProve.
      exact/incP/inc_mint_regs.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_mips _ _ _ exec_mips_proj); tauto.
  + exact: (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_mips).
Qed.

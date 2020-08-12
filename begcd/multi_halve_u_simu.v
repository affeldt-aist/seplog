(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Require Import encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_cmd mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_halve_u_prg multi_halve_u_triple.

Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope machine_int_scope.
Local Open Scope asm_expr_scope.
Local Open Scope simu_scope.
Local Open Scope zarith_ext_scope.

(** x <- x / 2, x unsigned  *)

Lemma pfwd_sim_halve_u P (x : bipl.var.v) d (rk rx a0 a1 a2 a3 : reg) :
  uniq(rk, rx, a0, a1, a2, a3, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: a2 :: a3 :: nil) ->
  x \notin assoc.dom d ->
  unsign rk rx \notin assoc.cdom d ->
  (x <- var_e x ./e nat_e 2)%pseudo_expr%pseudo_cmd
    <=p( state_mint (x |=> unsign rk rx \U+ d), P )
  multi_halve_u rk rx a0 a1 a2 a3.
Proof.
move=> Haux Hd Hd' Hd''.
rewrite /pfwd_sim.
move=> s st h [s_st_h _] s' exec_pseudo st' h' exec_mips.
have Hd_unchanged : forall v r, assoc.get v d = Some r ->
  disj (mint_regs r) (mips_frame.modified_regs (multi_halve_u rk rx a0 a1 a2 a3)).
  move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
  apply (disj_incl_LR Hd); last by apply incl_refl_Permutation; PermutProve.
  exact/incP/inc_mint_regs/(assoc.get_Some_in_cdom _ v).
set nk := '|u2Z ([rk ]_ st)|.

move/multi_halve_u_triple : (Haux).
move/(_ nk [rx ]_ st (state_mint_head_unsign_fit _ _ _ _ _ _ _ s_st_h) (Z2ints 32 nk ([ x ]_ s)%pseudo_expr)).
rewrite size_Z2ints.
move/(_ Logic.eq_refl) => Hhoare_multi_halve_u.

have [st'' [h'' exec_mips_proj]] : exists st'' h'',
  (Some (st, heap.proj h (heap.dom (heap_mint (unsign rk rx) st h))) --
    multi_halve_u rk rx a0 a1 a2 a3 ---> Some (st'', h''))%mips_cmd.
  exists st', (heap.proj h' (heap.dom (heap_mint (unsign rk rx) st h))).
  apply (mips_syntax.triple_exec_proj _ _ _ Hhoare_multi_halve_u) => {Hhoare_multi_halve_u} //.
  split; first by reflexivity.
  split; first by rewrite Z_of_nat_Zabs_nat //; apply min_u2Z.
  rewrite /heap_cut heap.proj_dom_proj.
  apply (state_mint_var_mint _ _ _ _ x (unsign rk rx)) in s_st_h; last by assoc_get_Some.
  rewrite /var_mint in s_st_h; case: s_st_h; tauto.
set postcond := (fun s h => exists _, _) in Hhoare_multi_halve_u.
have {Hhoare_multi_halve_u} hoare_triple_post_condition : (
  postcond ** assert_m.TT)%asm_assert st' h'.
  move: (mips_frame.frame_rule_R _ _ _ Hhoare_multi_halve_u assert_m.TT (assert_m.inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
  move/mips_seplog.hoare_prop_m.soundness.
  rewrite /while.hoare_semantics.
  move/(_ st h) => Hhalve_u.
  lapply Hhalve_u; last first.
    exists (heap_mint (unsign rk rx) st h), (h \D\ heap.dom (heap_mint (unsign rk rx) st h)).
    split; first by apply heap.disj_difs', inc_refl.
    split.
      apply heap.union_difsK => //; by apply heap.inclu_proj.
    split; last by reflexivity.
    split; first by reflexivity.
    split; first by rewrite Z_of_nat_Zabs_nat //; apply min_u2Z.
    move: (state_mint_var_mint _ s st h x (unsign rk rx) s_st_h).
    rewrite assoc.get_union_sing_eq.
    by case/(_ (refl_equal _)).
  move=> {Hhalve_u} [Hhalve_u Hhalve_u'].
  by move: {Hhalve_u'}(Hhalve_u' _ _ exec_mips).
split.
- move=> y ry y_ry.
  have [yx | yx] : y \in assoc.dom d \/ y = x.
    case/assoc.get_union_Some_inv : y_ry => y_ry.
    * by case/assoc.get_sing_inv : y_ry => -> _; right.
    * by apply assoc.get_Some_in_dom in y_ry; left.
  + (* y \in assoc.dom d *) have x_y : y <> x.
      move=> ?; subst y; by rewrite yx in Hd'.
    move: {s_st_h}(proj1 s_st_h _ _ y_ry) (proj2 s_st_h) => s_st_h1 s_st_h2.
    have x'_unchanged : ([ y ]_s = [ y ]_s')%pseudo_expr.
      Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    case: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_mips
      (heap.dom (heap_mint (unsign rk rx) st h)) _ _ exec_mips_proj) => H4 [H5 H_h_h'].
    have <- : heap_mint ry st h = heap_mint ry st' h'.
      apply (heap_mint_state_invariant (heap_mint (unsign rk rx) st h) y s) => //.
      move=> rx0 Hrx0; Reg_unchanged.
      apply (@disj_not_In _ (mint_regs ry)); last by [].
      apply/disj_sym/(Hd_unchanged y).
      by rewrite -y_ry assoc.get_union_sing_neq.
      apply s_st_h2 with y x => //.
      by rewrite assoc.get_union_sing_eq.
    move: s_st_h1; apply var_mint_invariant.
    move=> rx0 Hrx0; Reg_unchanged.
    apply (@disj_not_In _ (mint_regs ry)); last by [].
    apply/disj_sym/(Hd_unchanged y) => //.
    by rewrite -y_ry assoc.get_union_sing_neq.
    exact x'_unchanged.
  + (* yx : y = x *) subst y.
    have ? : ry = unsign rk rx.
      rewrite assoc.get_union_sing_eq in y_ry.
      by case: y_ry.
    subst ry.

    set vx := u2Z ([ rx ]_ st).
    set nk' := '|u2Z (store.get rk st')|.
    set vx' := u2Z (store.get rx st').
    move: (state_mint_var_mint _ s st h x (unsign rk rx) s_st_h).
    rewrite assoc.get_union_sing_eq.
    move/(_ (refl_equal _)).
    case=> X1 X2 X3.

    rewrite /postcond in hoare_triple_post_condition.
    case: hoare_triple_post_condition => [h1 [h2 [Hdisj [Hunion [[A' [Hdiv2_1 [Hdiv2_2 [Hdiv2_3 [Hdiv2_4 Hdiv2_5]]]]] HTT]]]]].
    have Hnknk' : nk = nk'.
      rewrite /nk /nk'; do 2 f_equal.
      Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
    subst nk'.
    have Hvxvx' : vx = vx'.
      rewrite /vx /vx'; f_equal.
      Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
    subst vx'.
    apply mkVarUnsign.
    - by rewrite -Hvxvx' -Hnknk'.
    - split.
      - move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
        syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        apply Z_div_pos => //; tauto.
      - move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv=> _ -> /=.
        syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        rewrite /ZIT.div.
        apply (@leZ_ltZ_trans ([ x ]_s)%pseudo_expr) => //.
        apply Zdiv_le_upper_bound => //; lia.
        rewrite -Hnknk'; tauto.
    - move: (Hdiv2_4) => Hdiv2_4_save.
      apply mapstos_inv_list2heap in Hdiv2_4 => //; last first.
        by rewrite [eval _ _]/= Hdiv2_1 -Hvxvx'.
      rewrite u2Z_shrl' in Hdiv2_4; last by repeat constructor.
      rewrite /= -Hvxvx' in Hdiv2_4.
      rewrite /heap_cut Hunion Hdiv2_4.
      move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
      case/syntax_m.seplog_m.exec0_assign_inv=> _ -> /=.
      syntax_m.seplog_m.assert_m.expr_m.Store_upd.
      rewrite lSum_Z2ints_pos // in Hdiv2_5.
      rewrite -Hdiv2_5 mulZC /ZIT.div Z_div_plus_full_l //.
      rewrite (Zdiv_small (u2Z ([a2]_ st' `>> 31))).
      rewrite addZ0 -Hnknk' -Z2ints_lSum //.
      rewrite /heap_cut.
      have <- : heap.dom (list2heap '|(vx / 4)| A') =
        ((iota '|u2Z ([rx ]_ st') / 4| nk) : list assoc.l).
        by rewrite dom_list2heap Hdiv2_1 Hvxvx'.
      rewrite heap.proj_union_L_dom; last by rewrite -Hdiv2_4.
      rewrite heap.proj_itself.
      rewrite -Hdiv2_4; exact Hdiv2_4_save.
      split; first by apply min_u2Z.
      by apply (shrl_lt ([ a2 ]_ st') 31).
- apply (state_mint_part2_one_variable_unsign _ _ _ _ _ _ _ _ _ s_st_h).
  + move=> t x0 Ht Hx0.
    Reg_unchanged. simpl mips_frame.modified_regs.
    case/assoc.in_cdom_union_inv : Ht => Ht.
    * rewrite assoc.cdom_sing /= seq.mem_seq1 in Ht.
      move/eqP : Ht => Ht; subst t.
      apply (@disj_not_In _ (mint_regs (unsign rk rx))); last by [].
      Disj_remove_dup.
      rewrite /=.
      apply uniq_disj.
      simpl cat.
      by Uniq_uniq r0.
    * apply (@disj_not_In _ (mint_regs t)); last by [].
      Disj_remove_dup.
      apply disj_sym.
      apply (disj_incl_LR Hd); last by apply incl_refl_Permutation; PermutProve.
      exact/incP/inc_mint_regs.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_mips _ _ _ exec_mips_proj); tauto.
  + exact: (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_mips).
Qed.

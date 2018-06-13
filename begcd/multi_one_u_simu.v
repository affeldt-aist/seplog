(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ssrZ ZArith_ext seq_ext uniq_tac machine_int.
Require Import multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_one_u_prg multi_one_u_triple.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope simu_scope.
Local Open Scope zarith_ext_scope.

(** x <- 1, x unsigned *)

Lemma pfwd_sim_one_u (x : bipl.var.v) d (rk rx a0 a1 : reg) :
  uniq(rk, rx, a0, a1, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: nil) ->
  x \notin assoc.dom d ->
  unsign rk rx \notin assoc.cdom d ->
  (x <- nat_e%pseudo_expr 1%nat)%pseudo_cmd
    <=p( state_mint (x |=> unsign rk rx \U+ d), fun _ st _ => 0 <  (u2Z [rk ]_ st)%asm_expr)
  multi_one_u rk rx a0 a1.
Proof.
move=> Hregs Hd x_d rk_rk_d.
have Hd_unchanged : forall v r, assoc.get v d = |_ r _| ->
  disj (mint_regs r) (mips_frame.modified_regs (multi_one_u rk rx a0 a1)).
  move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
  apply (disj_incl_LR Hd); last by apply incl_refl_Permutation; PermutProve.
  exact/incP/inc_mint_regs/(assoc.get_Some_in_cdom _ v).
rewrite /pfwd_sim.
move=> s st h [s_st_h rk_0] s' exec_seplog st' h' exec_mips.
have [st'' [h'' exec_mips_proj]] : exists st'' h'',
  (Some (st, heap.proj h (heap.dom (heap_mint (unsign rk rx) st h)))
  -- multi_one_u rk rx a0 a1 ---> Some (st'', h''))%mips_cmd.
  exists st', (heap.proj h' (heap.dom (heap_mint (unsign rk rx) st h))).
  set nk := '| u2Z ([rk ]_ st)%asm_expr |.

  move/multi_one_u_triple : Hregs.
  move/(_ nk (Z2ints 32 nk ([ x ]_s)%pseudo_expr) ([rx ]_ st)%asm_expr).
  have : (0 < nk)%nat by apply/O_lt_Zabs_nat.
  let x := fresh in move=> x; move/(_ x); clear x.
  rewrite size_Z2ints.
  move/(_ Logic.eq_refl (state_mint_head_unsign_fit _ _ _ _ _ _ _ s_st_h)).
  move/mips_syntax.triple_exec_proj; apply => //.
  split; first by [].
  split; first by rewrite Z_of_nat_Zabs_nat //; apply min_u2Z.
  rewrite /heap_cut heap.proj_dom_proj.
  apply (state_mint_var_mint _ _ _ _ x (unsign rk rx)) in s_st_h; last by assoc_get_Some.
  rewrite /var_mint in s_st_h.
  by case: s_st_h => _ [_ ?].
rewrite /state_mint; split.
- move=> y ry y_ry.
  have [y_d | y_x] : y \in assoc.dom d \/ y = x.
    case/assoc.get_union_Some_inv : y_ry => y_ry.
    + by case/assoc.get_sing_inv : y_ry => -> _; right.
    + by apply assoc.get_Some_in_dom in y_ry; left.
  + move: (proj1 s_st_h y) => s_st_h1.
    have x_y : x <> y.
      move=> X; subst y. by rewrite y_d in x_d.
    move: {s_st_h1}(s_st_h1 _ y_ry) => s_st_h1.
    have <- : heap_mint ry st h = heap_mint ry st' h'.
      case: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_mips
        (heap.dom (heap_mint (unsign rk rx) st h)) _ _ exec_mips_proj) => H4 [H5 H_h_h'].
      apply (heap_mint_state_invariant (heap_mint (unsign rk rx) st h) y s) => //.
      move=> rx0 Hrx0; Reg_unchanged.
      apply (@disj_not_In _ (mint_regs ry)); last by [].
      apply/disj_sym/(Hd_unchanged y).
      by rewrite -y_ry assoc.get_union_sing_neq; auto.
      apply (proj2 s_st_h) with y x => //.
      by auto.
      by assoc_get_Some.
    move: s_st_h1; apply var_mint_invariant.
    move=> rx0 Hrx0; Reg_unchanged.
    apply (@disj_not_In _ (mint_regs ry)); last by [].
    apply/disj_sym/(Hd_unchanged y) => //.
    by rewrite -y_ry assoc.get_union_sing_neq; auto.
    Var_unchanged; by rewrite /= mem_seq1 eq_sym; apply/negP/eqP.
  + (* y = x *) subst y.
    rewrite assoc.get_union_sing_eq in y_ry; case: y_ry => ?; subst ry.
    move: {s_st_h}(proj1 s_st_h x (unsign rk rx)).
    rewrite assoc.get_union_sing_eq.
    case/(_ (refl_equal _)) => s_st_h1 s_st_h2 s_st_h3.
    rewrite /var_mint.
    have Hrx : ([rx ]_ st = [rx ]_ st')%asm_expr.
      Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
    have Hrk : ([rk ]_ st = [rk ]_ st')%asm_expr.
      Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
    move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_seplog.
    case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
    syntax_m.seplog_m.assert_m.expr_m.Store_upd.
    apply mkVarUnsign.
    - rewrite -Hrx -Hrk.
      exact s_st_h1.
    - split; first by [].
      rewrite /= (_ : 1 = Zbeta 0) //.
      apply Zbeta_lt, O_lt_Zabs_nat.
      congruence.
    - have : uniq(rk, rx, a0, a1, r0) by Uniq_uniq r0.
      have Hnk := O_lt_Zabs_nat _ rk_0.
      move/multi_one_u_triple.
      set nk := '|u2Z ([rk ]_ st)%asm_expr|.
      set vx := ([rx ]_ st)%asm_expr.
      move/(_ nk (Z2ints 32 nk ([x ]_ s)%pseudo_expr) vx Hnk).
      rewrite size_Z2ints.
      move/(_ (refl_equal _) s_st_h1).
      move/mips_seplog.hoare_prop_m.soundness.
      rewrite /while.hoare_semantics.
      move/(_ st (heap_mint (unsign rk rx) st h)).
      rewrite {1}/nk Z_of_nat_Zabs_nat; last exact: min_u2Z.
      rewrite {1}/vx {1}/nk.
      case/( _ (conj (refl_equal _) (conj (refl_equal _) s_st_h3))) => _.
      rewrite (var_mint_unsign_dom_heap_mint x s rk rx st h (mkVarUnsign _ _ _ _ _ s_st_h1 s_st_h2 s_st_h3)) in exec_mips_proj.
      move/(_ _ _ exec_mips_proj).
      case=> _ [] _.
      rewrite (proj1 (proj2 (mips_syntax.exec_deter_proj _ _ _ _ _ exec_mips _ _ _ exec_mips_proj))).
      rewrite -(proj1 (mips_syntax.exec_deter_proj _ _ _ _ _ exec_mips _ _ _ exec_mips_proj)).
      rewrite /heap_mint /heap_cut -Hrx -Hrk.
      suff : one32 :: nseq (nk - 1) zero32 = Z2ints 32 '|(u2Z [rk ]_ st)%asm_expr| ([nat_e 1 ]e_ s)%pseudo_expr.
        by move=> ->.
      by rewrite -/nk [([nat_e 1 ]e_ s)%pseudo_expr]/= Z2ints_1 // -subSn // subn1.
- apply (state_mint_part2_one_variable_unsign _ _ _ _ _ _ _ _ _ s_st_h).
  + move=> t x0 Ht Hx0.
    Reg_unchanged. simpl mips_frame.modified_regs.
    case/assoc.in_cdom_union_inv : Ht => Ht.
    * rewrite assoc.cdom_sing /= seq.mem_seq1 in Ht.
      move/eqP : Ht => Ht; subst t.
      (* TODO: Ltac pour ca? *)
      apply (@disj_not_In _ (mint_regs (unsign rk rx))); last by [].
      Disj_remove_dup.
      rewrite /=.
      apply uniq_disj.
      simpl cat.
      by Uniq_uniq r0.
    * apply (@disj_not_In _ (mint_regs t)); last by [].
      Disj_remove_dup.
      apply/disj_sym/(disj_incl_LR Hd); last by apply incl_refl_Permutation; PermutProve.
      exact/incP/inc_mint_regs.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_mips _ _ _ exec_mips_proj); tauto.
  + exact/(mips_syntax.dom_heap_invariant _ _ _ _ _ exec_mips).
Qed.

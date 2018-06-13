(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac.
Require Import machine_int multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_one_s_prg multi_one_s_triple.

Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope simu_scope.

(** x <- 1, x signed *)

Lemma pfwd_sim_one_s (x : bipl.var.v) d k (rx rk a0 a1 a2 a3 : reg) :
  uniq(rx, rk, a0, a1, a2, a3, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: a2 :: a3 :: nil) ->
  x \notin assoc.dom d ->
  signed k rx \notin assoc.cdom d ->
  (x <- nat_e 1)%pseudo_expr%pseudo_cmd
    <=p( state_mint (x |=> signed k rx \U+ d), (fun s st h =>
    0 < u2Z ([rk]_st) < 2 ^^ 31 /\
    k = '|u2Z ([rk ]_ st)|)%asm_expr)
  multi_one_s rx rk a0 a1 a2 a3.
Proof.
move=> Hnodup Hdisj x_d k_d.
rewrite /pfwd_sim.
move=> s st h [s_st_h [k_bound k_rk]] s' exec_pseudo st' h' exec_asm.
have rx_st_st' : ([ rx ]_ st = [ rx ]_ st')%asm_expr.
  mips_syntax.Reg_unchanged; simpl mips_frame.modified_regs; by Uniq_not_In.
have rk_st_st' : ([ rk ]_ st = [ rk ]_ st')%asm_expr.
  mips_syntax.Reg_unchanged; simpl mips_frame.modified_regs; by Uniq_not_In.

have : uniq(rx,rk,a0,a1,a2,a3,r0) by Uniq_uniq r0.
move/(multi_one_s_triple rx rk a0 a1 a2 a3).
move/(_ ('|u2Z ([rk ]_ st)%asm_expr|)).
rewrite Z_of_nat_Zabs_nat; last exact/min_u2Z.

move/(state_mint_var_mint _ _ _ _ x (signed k rx)) : (s_st_h).
rewrite assoc.get_union_sing_eq.
move/(_ refl_equal).
case => slen ptr A rx_fit [A_k Hslen slen_x x_A] ptr_fit Hmem.

move/(_ A).

(* 1'. exhibit the hoare triple *)

move/(_ ([rx ]_ st)%asm_expr ptr k_bound).
rewrite A_k.
move/(_ k_rk).
rewrite k_rk in ptr_fit.
rewrite Z_of_nat_Zabs_nat in ptr_fit; last exact/min_u2Z.
move/(_ rx_fit ptr_fit).
rewrite k_rk Z_of_nat_Zabs_nat in Hslen; last exact/min_u2Z.
move/(_ slen Hslen) => Hhoare_triple.

(* 2. exists st'', h'' so that execution on the projected heap is safe *)

have [st'' [h'' Hexec_triple_proj]] : exists st'' h'',
  (Some (st, heap.proj h (heap.dom (heap_mint (signed k rx) st h))) --
     multi_one_s rx rk a0 a1 a2 a3 --->
     Some (st'', h''))%mips_cmd.
  exists st', (heap.proj h' (heap.dom (heap_mint (signed k rx) st h))).
  apply: (mips_syntax.triple_exec_proj _ _ _ Hhoare_triple (heap.dom (heap_mint (signed k rx) st h)) st h st' h').
  split; first by reflexivity.
  split; first by reflexivity.
  suff : h |P| heap.dom (heap_mint (signed k rx) st h) = heap_mint (signed k rx) st h by move=> ->.
  by apply heap.incluE, heap_inclu_heap_mint_signed.
  by [].

(* 3. instantiate la postcondition du hoare triple *)

set postcond := (fun s h => _ /\ _ /\ (_ ** (_ |--> one32 :: _)) s h)%asm_assert in Hhoare_triple.

have {Hhoare_triple} Hhoare_triple_post_condition : (postcond **
assert_m.TT)%asm_expr%asm_assert st' h'.
  move: (mips_frame.frame_rule_R _ _ _ Hhoare_triple assert_m.TT (assert_m.inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
  move/mips_seplog.hoare_prop_m.soundness.
  rewrite /while.hoare_semantics.
  move/(_ st h) => Hhoare_triple_sem.
  lapply Hhoare_triple_sem; last first.
    exists (heap_mint (signed k rx) st h), (h \D\ heap.dom (heap_mint (signed k rx) st h)).
    split; first by apply heap.disj_difs', seq_ext.inc_refl.
    split => //.
    apply heap.union_difsK => //; exact/heap_inclu_heap_mint_signed.
  move=> {Hhoare_triple_sem}[Hhoare_triple_sem Hhoare_triple_sem'].
  by apply Hhoare_triple_sem' in exec_asm.

rewrite /state_mint; split.
- move=> x0 mx0 x0_mx0.
  case/assoc.get_union_Some_inv : x0_mx0 => x0_mx0.
  + case/assoc.get_sing_inv : x0_mx0 => ? ?; subst x0 mx0.
    case: Hhoare_triple_post_condition => [h1 [h2 [h1_d_h2 [h1_U_h2 [[Hrx [Hrk Hh1]] Hh2]]]]].
    have Zsgn_nk : sgZ (Z_of_nat k) = 1.
      destruct k => //=.
      symmetry in k_rk.
      apply Zabs_nat_0_inv in k_rk.
      omega.
    destruct k as [|k].
      symmetry in k_rk.
      apply Zabs_nat_0_inv in k_rk.
      rewrite k_rk in k_bound.
      by case: k_bound.
    apply mkVarSigned with (Z2s 32 (Z_of_nat (S k))) ptr (one32 :: nseq ('|u2Z ([rk ]_ st)%asm_expr| - 1) zero32) => //.
    - by rewrite Hrx.
    - apply mkSignMagn => //.
      * by rewrite /= size_nseq -k_rk /= subn1.
      * rewrite Z2sK; last first.
          rewrite k_rk Z_of_nat_Zabs_nat; last exact: min_u2Z.
          omega.
        rewrite Zsgn_nk; ring.
      * rewrite Z2sK; last first.
          rewrite k_rk Z_of_nat_Zabs_nat; last exact: min_u2Z.
          omega.
        move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
        by syntax_m.seplog_m.assert_m.expr_m.Store_upd.
      * rewrite Z2sK; last first.
          rewrite k_rk Z_of_nat_Zabs_nat; last exact: min_u2Z.
          omega.
        move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
        syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        by rewrite [sgZ _]/= Zmult_1_l lSum_S Z2uK // lSum_nseq_0 mulZ0.
    - rewrite k_rk Z_of_nat_Zabs_nat //; exact: min_u2Z.
    - apply con_heap_mint_signed_cons with h1 => //.
      + rewrite h1_U_h2.
        apply heap.inclu_union_L => //.
        exact: heap.inclu_refl.
      + by rewrite -rx_st_st'.
      + rewrite [size _]/= size_nseq.
        set xx := Z_of_nat _.
        suff : xx = u2Z ([rk ]_ st)%asm_expr by move=> ->.
        rewrite {}/xx minus_Sn_m; last by omega.
        rewrite /= -minus_n_O Z_of_nat_Zabs_nat //; exact: min_u2Z.
      + rewrite /= size_nseq subn1 prednK //; apply/ltP; omega.
      + suff : Z2u 32 (u2Z ([rk ]_ st)%asm_expr) = Z2s 32 (Z_of_nat (S k)).
          by move=> <-.
        have k_rk' : u2Z ([rk ]_ st)%asm_expr = Z_of_nat (S k).
          rewrite k_rk Z_of_nat_Zabs_nat //; exact: min_u2Z.
        rewrite Z2u_u2Z.
        apply s2Z_inj.
        rewrite Z2sK; last first.
          rewrite -k_rk'.
          clear -k_bound.
          omega.
        rewrite -k_rk' s2Z_u2Z_pos' //.
        clear -k_bound.
        rewrite [Peano.pred _]/=; omega.
  + have x0_x : x0 <> x.
      move=> ?; subst x0.
      apply assoc.get_Some_in in x0_mx0.
      rewrite -assoc.elts_dom in x_d.
      move/negP : x_d; apply.
      apply/mapP.
      by exists (x, mx0).
    move: (proj2 s_st_h _ _ x0_x mx0 (signed k rx)).
    rewrite assoc.get_union_sing_neq; last by [].
    rewrite assoc.get_union_sing_eq.
    move/(_ x0_mx0 (refl_equal _)) => heap_mint_disj.
    move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ Hexec_triple_proj) => [st'_st'' [h''_h' h_h']].
    have Hd_unchanged : forall v r, assoc.get v d = Some r ->
      disj (mint_regs r) (mips_frame.modified_regs (multi_one_s rx rk a0 a1 a2 a3)).
      move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
      apply (disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
      exact/incP/inc_mint_regs/(assoc.get_Some_in_cdom _ v).
    have <- : heap_mint mx0 st h = heap_mint mx0 st' h'.
      apply (heap_mint_state_invariant (heap_mint (signed k rx) st h) x0 s) => //.
      move=> rx0 Hrx0; Reg_unchanged.
      apply (@disj_not_In _ (mint_regs mx0)); last by [].
      exact/disj_sym/(Hd_unchanged x0).
      move: (proj1 s_st_h x0 mx0).
      rewrite assoc.get_union_sing_neq; last by [].
      by apply.
    apply var_mint_invariant with s st => //.
    move=> rx0 Hrx0; Reg_unchanged.
    apply (@disj_not_In _(mint_regs mx0)); last by [].
    apply/disj_sym/(Hd_unchanged x0) => //.
    Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    move: (proj1 s_st_h x0 mx0).
    rewrite assoc.get_union_sing_neq; last by [].
    by apply.
- have Hdom : heap.dom (heap_mint (signed k rx) st' h') = heap.dom (heap_mint (signed k rx) st h).
    symmetry.
    case: Hhoare_triple_post_condition => h1 [h2 [h1_d_h2 [h1_U_h2 [[_ [_ Hh1]] Hh2]]]].
    apply (dom_heap_mint_sign_state_invariant _ _ _ _ _ _ x s slen (Z2u 32 (u2Z ([rk ]_ st)%asm_expr))) => //.
      by move/assert_m.mapstos_get1/heap_get_heap_mint_inv : Hmem.
    apply assert_m.mapstos_get1 in Hh1.
    rewrite h1_U_h2; exact: heap.get_union_L.
    apply assert_m.mapstos_get2 in Hmem.
    apply assert_m.mapstos_get2 in Hh1.
    rewrite h1_U_h2.
    apply heap_get_heap_mint_inv in Hmem.
    rewrite Hmem.
    symmetry.
    exact: heap.get_union_L.
    apply mkVarSigned with slen ptr A => //.
    apply mkSignMagn => //; rewrite k_rk Z_of_nat_Zabs_nat //; exact: min_u2Z.
    rewrite k_rk Z_of_nat_Zabs_nat //; exact: min_u2Z.
    by eapply dom_heap_invariant; eauto.
  apply (state_mint_part2_one_variable _ _ _ _ _ _ _ _ s_st_h Hdom).
  + move=> t x0 Ht Hx0.
    Reg_unchanged. simpl mips_frame.modified_regs.
    case/assoc.in_cdom_union_inv : Ht => Ht.
    * rewrite assoc.cdom_sing /= seq.mem_seq1 in Ht.
      move/eqP : Ht => Ht; subst t.
      apply (@disj_not_In _(mint_regs (unsign rk rx))); last by rewrite /=; auto.
      Disj_remove_dup.
      rewrite /=.
      apply uniq_disj. rewrite [cat _ _]/=. by Uniq_uniq r0.
    * apply (@disj_not_In _ (mint_regs t)); last by [].
      Disj_remove_dup.
      apply/disj_sym/(disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
      exact/incP/inc_mint_regs.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ Hexec_triple_proj); tauto.
  + exact: (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ZArith_ext seq_ext uniq_tac.
Require Import machine_int multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_zero_s_prg multi_zero_s_triple.

Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope asm_expr_scope.
Local Open Scope simu_scope.

(** x <- 0, x signed  *)

Lemma pfwd_sim_zero_s P (x : bipl.var.v) d k rx :
  uniq(rx, r0) -> x \notin assoc.dom d ->
  signed k rx \notin (assoc.cdom d) ->
  (x <- nat_e O)%pseudo_expr%pseudo_cmd
    <=p(state_mint (x |=> signed k rx \U+ d), P)
  multi_zero_s rx.
Proof.
move=> Hnodup x_d rx_d.
move=> s st h [s_st_h HP] s' exec_pseudo st' h' exec_asm.

(* TODO: clean *)
(* 1. exhiber le triplet de Hoare *)

move: (state_mint_var_mint _ _ _ _ x (signed k rx) s_st_h).
rewrite assoc.get_union_sing_eq.
move/(_ refl_equal).
case=> slen ptr A rx_fit [len_A slen_k slen_x x_A] ptr_fit Hmem.

move: (multi_zero_s_triple _ Hnodup A ).
move/(_ ptr slen) => Hhoare_triple.

(* 2. exists st'', h'' so that execution on the projected heap is safe *)

have [st'' [h'' Hexec_triple_proj]] : exists st'' h'',
  (Some (st, heap.proj h (heap.dom (heap_mint (signed k rx) st h))) --
     multi_zero_s rx ---> Some (st'', h''))%mips_cmd.
  exists st', (heap.proj h' (heap.dom (heap_mint (signed k rx) st h))).
  apply (mips_syntax.triple_exec_proj _ _ _ Hhoare_triple) => //.
  suff : h |P| heap.dom (heap_mint (signed k rx) st h) = heap_mint (signed k rx) st h by move=> ->.
  by apply heap.incluE, heap_inclu_heap_mint_signed.

(* 3. instiate la post condition du Hoare triple *)

set postcond := (_ |--> zero32 :: _ ** _)%asm_assert in Hhoare_triple.
have {Hhoare_triple}Hhoare_triple_post_condition : ((postcond ** assert_m.TT) st' h')%asm_assert.
  move/mips_seplog.hoare_prop_m.soundness: (mips_frame.frame_rule_R _ _ _ Hhoare_triple assert_m.TT (assert_m.inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
  rewrite /while.hoare_semantics.
  move/(_ st h) => Hhoare_triple_sem.
  lapply Hhoare_triple_sem; last first.
    exists (heap_mint (signed k rx) st h), (h \D\ heap.dom (heap_mint (signed k rx) st h)).
    split; first by apply heap.disj_difs', seq_ext.inc_refl.
    split.
      apply heap.union_difsK => //; exact/heap_inclu_heap_mint_signed.
    split; last by [].
    exact Hmem.
  move=> {Hhoare_triple_sem}[Hhoare_triple_sem Hhoare_triple_sem'].
  by apply Hhoare_triple_sem' in exec_asm.

(* state_mint (x |=> signed L rx \U+ d) s' st' h' *)

have rx_st_st' : [ rx ]_ st = [ rx ]_ st'.
  mips_syntax.Reg_unchanged; simpl mips_frame.modified_regs; by Uniq_not_In.

rewrite /state_mint; split.
- move=> y my.
  case/assoc.get_union_Some_inv => y_my.
  + case/assoc.get_sing_inv : y_my => ? ?; subst y my.
    move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
    case/syntax_m.seplog_m.exec0_assign_inv => _ Hs'.
    apply mkVarSigned with zero32 ptr A => //.
    * by rewrite -rx_st_st'.
    * apply mkSignMagn => //.
      - rewrite s2Z_u2Z_pos' //; by rewrite Z2uK.
      - rewrite Hs'.
        syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        rewrite s2Z_u2Z_pos' //; by rewrite Z2uK.
      - rewrite Hs'.
        syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        rewrite s2Z_u2Z_pos' //; by rewrite Z2uK.
        case: Hhoare_triple_post_condition => [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
        apply con_heap_mint_signed_cons with h1 => //.
        - rewrite h1_U_h2.
          apply heap.inclu_union_L => //.
          by apply heap.inclu_refl.
        - by rewrite -rx_st_st'.
        - by rewrite len_A.
  + have y_x : y <> x.
      move=> ?; subst y.
      apply assoc.get_Some_in_dom in y_my.
      by rewrite y_my in x_d.
    apply var_mint_invariant with s st.
    * move=> rx0 Hrx0.
      Reg_unchanged.
      rewrite [mips_frame.modified_regs _]/=.
      by auto.
    * Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    * suff : heap_mint my st' h' = heap_mint my st h.
        move=> ->.
        apply (state_mint_var_mint _ _ _ _ _ _ s_st_h).
        by rewrite assoc.get_union_sing_neq.
      symmetry.

      move: (proj2 s_st_h _ _ y_x my (signed k rx)).
      rewrite assoc.get_union_sing_neq // assoc.get_union_sing_eq.
      move/(_ y_my (refl_equal _)) => heap_mint_disj.
      case: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ Hexec_triple_proj)
        => st'_st'' [h''_h' h_h'_dif].

      apply (heap_mint_state_invariant (heap_mint (signed k rx) st h) y s) => //.
      - move=> rx0 Hrx0; Reg_unchanged.
        apply (@disj_not_In _ (mint_regs my)); last by [].
        have Hd_unchanged : forall v r, assoc.get v d = Some r ->
          disj (mint_regs r) (mips_frame.modified_regs (multi_zero_s rx)).
          move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; by apply disj_nil_R.
          rewrite [mips_frame.modified_regs _]/=; exact/disj_nil_L.
      - apply (state_mint_var_mint _ _ _ _ _ _ s_st_h).
        by rewrite assoc.get_union_sing_neq.
- have Hdom : heap.dom (heap_mint (signed k rx) st' h') = heap.dom (heap_mint (signed k rx) st h).
    symmetry.
    case: Hhoare_triple_post_condition => [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
    apply dom_heap_mint_sign_state_invariant with x s slen zero32 => //.
    - apply assert_m.mapstos_get1 in Hmem.
      by apply heap_get_heap_mint_inv in Hmem.
    - apply assert_m.mapstos_get1 in Hh1.
      rewrite h1_U_h2.
      by apply heap.get_union_L.
    - move/assert_m.mapstos_get2 : Hmem.
      move/heap_get_heap_mint_inv => ->.
      symmetry.
      rewrite h1_U_h2.
      apply heap.get_union_L => //.
      by apply assert_m.mapstos_get2 in Hh1.
    - apply mkVarSigned with slen ptr A => //.
      by eapply dom_heap_invariant; eauto.
  apply (state_mint_part2_one_variable _ _ _ _ _ _ _ _ s_st_h Hdom).
  + move=> t x0 Ht Hx0.
    Reg_unchanged. simpl mips_frame.modified_regs.
    by auto.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ Hexec_triple_proj); tauto.
  + by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
Qed.

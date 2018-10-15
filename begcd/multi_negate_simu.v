(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac.
Require Import machine_int multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax mips_mint mips_frame.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.

Require Import multi_negate_prg multi_negate_triple.

Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope simu_scope.

(** x <- - x, x signed *)

Lemma pfwd_sim_multi_negate (x : bipl.var.v) d k rx a0 :
  uniq(rx, a0, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: nil) ->
  x \notin assoc.dom d ->
  signed k rx \notin assoc.cdom d ->
  (x <- .--e (var_e x))%pseudo_expr%pseudo_cmd
    <=p( state_mint (x |=> signed k rx \U+ d), fun _ _ _ => 0 < Z_of_nat k < 2 ^^ 31 )
  multi_negate rx a0.
Proof.
move=> Hset Hdisj x_d rx_d.
rewrite /pfwd_sim.
move=> s st h [s_st_h k_231] s' exec_pseudo st' h' exec_asm.

move: (proj1 s_st_h x (signed k rx)).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => slen ptr A rx_fit encoding ptr_fit memA.

move: (multi_negate_triple rx a0 slen ptr A Hset) => hoare_triple.

have [st'' [h'' exec_triple_proj]] : exists st'' h'',
  (Some (st, heap.proj h (heap.dom (heap_mint (signed k rx) st h))) --
  multi_negate rx a0 ---> Some (st'', h''))%asm_cmd.
  exists st', (heap.proj h' (heap.dom (heap_mint (signed k rx) st h))).
  apply: (mips_syntax.triple_exec_proj _ _ _ hoare_triple) => //.
  move: (heap_inclu_heap_mint_signed h st k rx).
  move/heap.incluE => ->; exact memA.

set postcond := (_ |--> cplt2 _ :: _ ** _)%asm_assert in hoare_triple.

have {hoare_triple}hoare_triple_postcond : (postcond ** assert_m.TT)%asm_assert st' h'.
  move: {hoare_triple}(frame_rule_R _ _ _ hoare_triple assert_m.TT (assert_m.inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
  move/mips_seplog.hoare_prop_m.soundness.
  rewrite /while.hoare_semantics.
  move/(_ st h) => Hhoare_triple.
  lapply Hhoare_triple; last first.
    exists (heap_mint (signed k rx) st h), (h \D\ heap.dom (heap_mint (signed k rx) st h)).
    split; first exact/heap.disj_difs'/inc_refl.
    split; last by [].
    apply heap.union_difsK; last by [].
    exact: heap_inclu_heap_mint_signed.
  case=> _.
  by move/(_ _ _ exec_asm).
have rx_st_st' : ([rx ]_ st = [rx]_st')%asm_expr.
  Reg_unchanged. rewrite [modified_regs _]/=. by Uniq_not_In.
rewrite /state_mint; split.
- move=> z mz.
  case/assoc.get_union_Some_inv => [z_is_x | z_in_y_or_d].
  + case/assoc.get_sing_inv : z_is_x => ? ?; subst z mz.
    have not_weird_slen : ~ weird slen.
      rewrite weirdE2.
      case: encoding => H1 -> H3 H4.
      move=> abs.
      have : sgZ (s2Z slen) = -1.
        case: (Zsgn_spec (s2Z slen)).
          case=> _ abs'.
          rewrite abs' in abs.
          omega.
        case.
          case=> abs'.
          by rewrite -abs' /= in abs.
        by case.
      move=> abs'.
      rewrite abs' mulN1Z in abs.
      apply Z.opp_inj in abs.
      rewrite abs in k_231.
      by case: k_231 => _ /ltZZ.
    apply mkVarSigned with (cplt2 slen) ptr A => //.
    * by rewrite -rx_st_st'.
    * move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
      case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
      syntax_m.seplog_m.assert_m.expr_m.Store_upd.
      case: encoding => H1 H2 H3 H4.
      apply mkSignMagn => //.
      rewrite s2Z_cplt2 // H2 Zsgn_Zopp Zsgn_Zmult ZsgnK.
      suff : sgZ (Z_of_nat k) = 1 by move=> ->; rewrite mulZ1; ring.
      case: k_231 => k_231 _.
      by apply Zsgn_pos in k_231.
      by rewrite Zsgn_Zopp s2Z_cplt2 // Zsgn_Zopp H3.
      rewrite s2Z_cplt2 // Zsgn_Zopp H4; ring.
    * case: hoare_triple_postcond => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
      apply con_heap_mint_signed_cons with h1 => //.
      - rewrite h1Uh2.
        apply heap.inclu_union_L => //.
        by apply heap.inclu_refl.
      - by rewrite -rx_st_st'.
      - case: encoding => H1 H2 H3 H4.
        by rewrite H1.
      - by case: encoding.
  + (* z \in d *) have z_x : z <> x.
      move=> ?; subst z.
      apply assoc.get_Some_in in z_in_y_or_d.
      rewrite -assoc.elts_dom in x_d.
      move/negP : x_d; apply.
      apply/mapP.
      by exists (x, mz).
    move: (proj2 s_st_h _ _ z_x mz (signed k rx)).
    rewrite assoc.get_union_sing_neq; last by [].
    rewrite assoc.get_union_sing_eq.
    move/(_ z_in_y_or_d (refl_equal _)) => heap_mint_disj.
    move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ exec_triple_proj) => [st'_st'' [h''_h' h_h']].
    have Hd_unchanged : forall v r, assoc.get v d = Some r ->
      disj (mint_regs r) (mips_frame.modified_regs (multi_negate rx a0)).
      move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
      apply (disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
      exact/incP/inc_mint_regs/(assoc.get_Some_in_cdom _ v).
    have <- : heap_mint mz st h = heap_mint mz st' h'.
      apply (heap_mint_state_invariant (heap_mint (signed k rx) st h) z s) => //.
      move=> ry Hry; Reg_unchanged.
      apply (@disj_not_In _ (mint_regs mz)); last by [].
      exact/disj_sym/(Hd_unchanged z).
      move: (proj1 s_st_h z mz).
      rewrite assoc.get_union_sing_neq; last by [].
      exact.
    apply var_mint_invariant with s st => //.
    * move=> ry ry_my; Reg_unchanged.
      apply (@disj_not_In _ (mint_regs mz)); last by [].
      exact/disj_sym/(Hd_unchanged z).
    * Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    * move: (proj1 s_st_h z mz).
      rewrite assoc.get_union_sing_neq //; by apply.
- have Hdom : heap.dom (heap_mint (signed k rx) st' h') = heap.dom (heap_mint (signed k rx) st h).
    symmetry.
    case: hoare_triple_postcond => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
    rewrite /postcond in Hh1.
    apply (dom_heap_mint_sign_state_invariant _ _ _ _ _ _ x s slen (cplt2 slen)) => //.
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
    by eapply dom_heap_invariant; eauto.
  apply (state_mint_part2_one_variable _ _ _ _ _ _ _ _ s_st_h Hdom).
  + move=> t x0 Ht Hx0.
    Reg_unchanged. simpl mips_frame.modified_regs.
    case/assoc.in_cdom_union_inv : Ht => Ht.
    * rewrite assoc.cdom_sing /= seq.mem_seq1 in Ht.
      move/eqP in Ht; subst t.
      apply (@disj_not_In _ (mint_regs (signed k rx))); last by [].
      Disj_remove_dup.
      rewrite /=.
      apply uniq_disj. rewrite [cat _ _]/=. by Uniq_uniq r0.
    * apply (@disj_not_In _ (mint_regs t)); last by [].
      Disj_remove_dup.
      apply/disj_sym/(disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
      exact/incP/inc_mint_regs.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ exec_triple_proj); tauto.
  + exact: (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
Qed.

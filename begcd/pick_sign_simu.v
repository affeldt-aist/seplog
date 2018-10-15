(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ssrZ ZArith_ext seq_ext uniq_tac machine_int.
Require Import multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax mips_mint mips_seplog mips_frame.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import pick_sign_prg pick_sign_triple.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope asm_expr_scope.
Local Open Scope asm_cmd_scope.

Lemma fwd_sim_b_pick_sign x rx a0 a1 L d : uniq(rx, a0, a1, r0) ->
  fwd_sim_b
  (state_mint (x |=> signed L rx \U+ d))
  (var_e x \>= nat_e 0)%pseudo_expr
  (pick_sign rx a0 a1) (bgez a1).
Proof.
move=> Hnodup.
rewrite /fwd_sim_b => s st h s_st_h.
move: (state_mint_var_mint _ _ _ _ x (signed L rx) s_st_h).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => slen ptr A rx_fit encoding ptr_fit memA.
move: (pick_sign_triple (fun _ _ => True)  (assert_m.emp)
  ([rx]_st) slen rx a0 a1 Hnodup (assert_m.inde_emp _) (assert_m.inde_TT _)) => hoare_triple.
set code := pick_sign _ _ _.

have Hmem_sing : (var_e rx |~> int_e slen ** assert_m.emp)%asm_assert st
  (heap.sing (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)) slen).
  rewrite assert_m.con_emp_equiv.
  eexists; split; last reflexivity.
  case: memA => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
  move/assert_m.mapstos_inv_addr : Hh1.
  case/Zmod_divides => // c Hh1.
  rewrite Hh1 mulZC Z_div_mult_full // Z_of_nat_Zabs_nat.
  by rewrite mulZC.
  move: (min_u2Z ([var_e rx ]e_ st)) => ?; omega.

have [st' Hst'] : exists st', Some (st, h) -- code ---> Some (st', h).
  have [[st' he'] Hst'] : exists st', Some (st, h) -- code ---> Some st'.
    apply constructive_indefinite_description'.
    eapply hoare_prop_m.termi.
    - apply frame_rule_R with (R := assert_m.TT).
      + exact: hoare_triple.
      + by Inde.
      + move=> ?; by Inde_mult.
    - move=> s0 h0 /= H.
      apply Epsilon.constructive_indefinite_description.
      exact: no_while_terminate.
    - exists (heap.sing (Z.abs_nat (u2Z ([ rx ]_st) / 4)) slen).
      exists (h \D\ Z.abs_nat (u2Z ([ rx ]_st) / 4) :: nil).
      split.
        rewrite -(heap.dom_sing _ slen).
        exact/heap.disj_difs'/inc_refl.
      split => //.
      rewrite -heap.union_difsK //; last by rewrite heap.dom_sing.
      apply heap.get_inclu_sing.
      move/assert_m.mapstos_get1 : memA.
      by move/heap_get_heap_mint_inv.
    exists st'.
    suff : h = he' by move=> X; rewrite -X in Hst'.
    exact: (no_sw_heap_invariant _ _ _ Hst' (erefl _) _ _ _ _ (erefl _) (erefl _)).

exists st'; split => //.
move/mips_seplog.soundness : (hoare_triple).
rewrite /while.hoare_semantics.
move/(_ st (heap.sing (Z.abs_nat (u2Z ([ rx ]_st) / 4)) slen)) => Htmp.
lapply Htmp; last by [].
case=> {Htmp}Hsafe.
have Hst'_proj :
  (Some (st, heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen) -- code --->
    Some (st', heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen))%mips_cmd.
  have Htmp : heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen =
    heap.proj h (Z.abs_nat (u2Z ([rx ]_ st) / 4) :: nil).
    rewrite -(heap.dom_sing _ slen).
    symmetry.
    rewrite -heap.incluE.
    apply heap.get_inclu_sing.
    move/assert_m.mapstos_get1 : memA.
    by move/heap_get_heap_mint_inv.
  rewrite Htmp.
  apply (triple_exec_proj _ _ _ hoare_triple) => //.
  split => //.
  split => //.
  by rewrite -Htmp.
move/(_ st' (heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen)).
move/(_ Hst'_proj) => H; split => Htest.
- apply/leZP.
  decompose [and] H; clear H.
  case: H3.
    by move=> ->.
  case.
    by move=> ->.
  move=> abs.
  case: encoding => Ha Hb Hc Hd.
  rewrite /= /ZIT.geb in Htest.
  move/geZP in Htest.
  rewrite abs /= in H1.
  rewrite Hd -H1 in Htest.
  case/Z_le_lt_eq_dec: (min_lSum L A); first by move=> ?; omega.
  move=> abs'.
  rewrite -abs' mulZ0 in Hd.
  by rewrite Hd -H1 in Hc.
- rewrite /= /ZIT.geb in Htest.
  move: Htest => /=.
  move/leZP/Zsgn_pos0 => Ha1.
  apply/geZP.
  decompose [and] H; clear H.
  case: encoding => Ha Hb Hc Hd.
  rewrite Hd -H1.
  apply/Z.le_ge/mulZ_ge0 => //; exact: min_lSum.
Qed.

Lemma fwd_sim_b_pick_sign_bne x rx a0 a1 L d : uniq(rx, a0, a1, r0) ->
  fwd_sim_b
  (state_mint (x |=> signed L rx \U+ d))
  (var_e x \!= nat_e 0)%pseudo_expr
  (pick_sign rx a0 a1) (bne a1 r0).
Proof.
(* copipe *)
move=> Hnodup.
rewrite /fwd_sim_b => s st h s_st_h.
move: (state_mint_var_mint _ _ _ _ x (signed L rx) s_st_h).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => slen ptr A rx_fit encoding ptr_fit memA.
move: (pick_sign_triple (fun _ _ => True)  (assert_m.emp)
  ([rx]_st) slen rx a0 a1 Hnodup (assert_m.inde_emp _) (assert_m.inde_TT _)) => hoare_triple.
set code := pick_sign _ _ _.

have Hmem_sing : (var_e rx |~> int_e slen ** assert_m.emp)%asm_assert st
  (heap.sing (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)) slen).
  rewrite assert_m.con_emp_equiv.
  eexists; split; last reflexivity.
  case: memA => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
  move/assert_m.mapstos_inv_addr : Hh1.
  case/Zmod_divides => // c Hh1.
  rewrite Hh1 mulZC Z_div_mult_full // Z_of_nat_Zabs_nat.
  by rewrite mulZC.
  move: (min_u2Z ([var_e rx ]e_ st)) => ?; omega.

have [st' Hst'] : exists st', Some (st, h) -- code ---> Some (st', h).
  have [[st' he'] Hst'] : exists st', Some (st, h) -- code ---> Some st'.
    apply constructive_indefinite_description'.
    eapply hoare_prop_m.termi.
    - apply frame_rule_R with (R := assert_m.TT).
      + exact: hoare_triple.
      + by Inde.
      + move=> ?; by Inde_mult.
    - move=> s0 h0 /= H.
      apply Epsilon.constructive_indefinite_description.
      exact: no_while_terminate.
    - exists (heap.sing (Z.abs_nat (u2Z ([ rx ]_st) / 4)) slen).
      exists (h \D\ (Z.abs_nat (u2Z ([ rx ]_st) / 4)) :: nil).
      split.
        rewrite -(heap.dom_sing _ slen); exact/heap.disj_difs'/inc_refl.
      split => //.
      rewrite -heap.union_difsK //; last by rewrite heap.dom_sing.
      apply heap.get_inclu_sing.
      move/assert_m.mapstos_get1 : memA.
      by move/heap_get_heap_mint_inv.
    exists st'.
    suff : h = he' by move=> X; rewrite -X in Hst'.
    exact: (no_sw_heap_invariant _ _ _ Hst' (erefl _) _ _ _ _ (erefl _) (erefl _)).

exists st'; split => //.
move/mips_seplog.soundness : (hoare_triple).
rewrite /while.hoare_semantics.
move/(_ st (heap.sing (Z.abs_nat (u2Z ([ rx ]_st) / 4)) slen)) => Htmp.
lapply Htmp; last by [].
case=> {Htmp}Hsafe.
have Hst'_proj :
  (Some (st, heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen) -- code --->
    Some (st', heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen))%mips_cmd.
  have Htmp : heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen =
    heap.proj h ((Z.abs_nat (u2Z ([rx ]_ st) / 4)) :: nil).
    rewrite -(heap.dom_sing _ slen).
    symmetry.
    rewrite -heap.incluE.
    apply heap.get_inclu_sing.
    move/assert_m.mapstos_get1 : memA.
    by move/heap_get_heap_mint_inv.
  rewrite Htmp.
  apply (triple_exec_proj _ _ _ hoare_triple) => //.
  split => //.
  split => //.
  by rewrite -Htmp.
move/(_ st' (heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen)).
move/(_ Hst'_proj) => H; split => Htest.
(* copipe *)
- apply/eqP.
  rewrite store.get_r0 Z2uK //.
  rewrite /= /ZIT.eqb in Htest.
  move/eqP in Htest.
  contradict Htest.
  decompose [and] H; clear H.
  case: encoding => Ha Hb Hc Hd.
  rewrite Hd -H1.
  rewrite s2Z_u2Z_pos'; last by rewrite Htest.
  by rewrite Htest.
- rewrite /= in Htest.
  rewrite store.get_r0 /= Z2uK // in Htest.
  move/eqP in Htest.
  rewrite /= /ZIT.eqb.
  apply/negPn.
  contradict Htest.
  move/eqP in Htest.
  decompose [and] H; clear H.
  case: encoding => Ha Hb Hc Hd.
  rewrite Htest /= in Hc.
  rewrite Hc in H1. rewrite -> Zsgn_null in H1; by rewrite -s2Z_u2Z_pos // H1.
Qed.

Lemma fwd_sim_b_pick_sign_lez x rx a0 a1 L d : uniq(rx, a0, a1, r0) ->
  fwd_sim_b
  (state_mint (x |=> signed L rx \U+ d))
  (nat_e 0 \>= var_e x)%pseudo_expr (pick_sign rx a0 a1)
  (blez a1).
Proof.
(* copipe *)
move=> Hnodup.
rewrite /fwd_sim_b => s st h s_st_h.
move: (state_mint_var_mint _ _ _ _ x (signed L rx) s_st_h).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => slen ptr A rx_fit encoding ptr_fit memA.
move: (pick_sign_triple (fun _ _ => True)  (assert_m.emp)
  ([rx]_st) slen rx a0 a1 Hnodup (assert_m.inde_emp _) (assert_m.inde_TT _)) => hoare_triple.
set code := pick_sign _ _ _.

have Hmem_sing : (var_e rx |~> int_e slen ** assert_m.emp)%asm_assert st
  (heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen).
  rewrite assert_m.con_emp_equiv.
  eexists; split; last by reflexivity.
  case: memA => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
  move/assert_m.mapstos_inv_addr : Hh1.
  case/Zmod_divides => // c Hh1.
  rewrite Hh1 mulZC Z_div_mult_full // Z_of_nat_Zabs_nat.
  by rewrite mulZC.
  move: (min_u2Z ([var_e rx ]e_ st)%asm_expr) => ?; omega.

have [st' Hst'] : exists st', Some (st, h) -- code ---> Some (st', h).
  have [[st' he'] Hst'] : exists st', Some (st, h) -- code ---> Some st'.
    apply constructive_indefinite_description'.
    eapply hoare_prop_m.termi.
    - apply mips_frame.frame_rule_R with (R := assert_m.TT).
      + exact: hoare_triple.
      + by Inde.
      + move=> ?; by Inde_mult.
    - move=> s0 h0 /= H.
      apply Epsilon.constructive_indefinite_description.
      exact: no_while_terminate.
    - exists (heap.sing (Z.abs_nat (u2Z ([ rx ]_st) / 4)) slen).
      exists (h \D\ Z.abs_nat (u2Z ([ rx ]_st) / 4) :: nil)%asm_expr.
      split.
        rewrite -(heap.dom_sing _ slen).
        by apply/heap.disj_difs'/inc_refl.
      split => //.
      rewrite -heap.union_difsK //; last by rewrite heap.dom_sing.
      apply heap.get_inclu_sing.
      move/assert_m.mapstos_get1 : memA.
      by move/heap_get_heap_mint_inv.
    exists st'.
    suff : h = he' by move=> X; rewrite -X in Hst'.
    exact: (no_sw_heap_invariant _ _ _ Hst' (refl_equal _) _ _ _ _ (refl_equal _) (refl_equal _)).

exists st'; split => //.
move/mips_seplog.soundness : (hoare_triple).
rewrite /while.hoare_semantics.
move/(_ st (heap.sing (Z.abs_nat (u2Z ([ rx ]_st) / 4)) slen)) => Htmp.
lapply Htmp; last by [].
case=> {Htmp}Hsafe.
have Hst'_proj :
  (Some (st, heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen) -- code --->
    Some (st', heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen))%mips_cmd.
  have Htmp : heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen =
    heap.proj h ((Z.abs_nat (u2Z ([rx ]_ st) / 4)) :: nil).
    rewrite -(heap.dom_sing _ slen).
    symmetry.
    rewrite -heap.incluE.
    apply heap.get_inclu_sing.
    move/assert_m.mapstos_get1 : memA.
    by move/heap_get_heap_mint_inv.
  rewrite Htmp.
  apply (triple_exec_proj _ _ _ hoare_triple) => //.
  split => //.
  split => //.
  by rewrite -Htmp.
move/(_ st' (heap.sing (Z.abs_nat (u2Z ([rx ]_ st) / 4)) slen)).
move/(_ Hst'_proj) => H; split => Htest.
(* copipe *)
- rewrite /=.
  apply/leZP.
  rewrite /= /ZIT.geb in Htest.
  move/geZP in Htest.
  decompose [and] H; clear H.
  case: encoding => Ha Hb Hc Hd.
  rewrite Hd -H1 in Htest.
  apply Zsgn_neg0.
  apply Z.ge_le in Htest.
  case: H3.
    by move=> ->.
    case.
      move=> H3.
      rewrite H3 /= in H1.
      rewrite H3 in Htest.
      rewrite Zmult_1_l in Htest.
      move: (min_lSum L A).
      case/Z_le_lt_eq_dec => abs; first omega.
      rewrite -abs mulZ0 in Hd .
      rewrite Hd /= in Hc.
      by rewrite Hc in H1.
    by move=> ->.
- rewrite /= /ZIT.geb.
  apply/geZP/Z.le_ge.
  rewrite /= in Htest.
  move/leZP in Htest.
  case: encoding => Ha Hb Hc Hd.
  decompose [and] H; clear H.
  rewrite Hd -H1.
  apply Zsgn_neg0 in Htest.
  move: (min_lSum L A) => ?.
  rewrite mulZC; exact: mulZ_ge0_le0.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax.
Import expr_m.
Require Import integral_type.
Require Import simu.
Import simu_m.
Require Import multi_is_even_s_and_prg.
Require Import multi_is_even_s_simu.
Require Import multi_is_even_s_triple.
Require Import multi_is_even_s_prg.
Require Import mips_frame.

Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope uniq_scope.
Local Open Scope assoc_scope.
Local Open Scope heap_scope.
Local Open Scope asm_expr_scope.
Local Open Scope mips_cmd_scope.

Lemma fwd_sim_b_multi_is_even_s_and rx ry a0 a1 a2 a3 x y d k :
  0 < Z_of_nat k < 2 ^^ 31 ->
  uniq(x, y) -> uniq(rx, ry, a0, a1, a2, a3, r0) ->
  let c := (multi_is_even_s_and rx ry a0 a1 a2 a3) in
  let d' := x |=> signed k rx \U+ (y |=> signed k ry \U+ d) in
  disj (mips_frame.modified_regs c) (mints_regs (assoc.cdom d')) ->
  fwd_sim_b (state_mint d')
  (var_e x \% nat_e 2 \= nat_e 0 \&& var_e y \% nat_e 2 \= nat_e 0)%pseudo_expr
  c (bne a0 r0).
Proof.
move=> Hk Hvars Hregs c d' Hdisj.
rewrite /fwd_sim_b => st s h Hst_s_h.
rewrite /multi_is_even_s_and.
have : uniq(rx,a0,a1,a2,r0) by Uniq_uniq r0.
move/(fwd_sim_b_multi_is_even_s x rx a0 a1 a2 k (y |=> signed k ry \U+ d)).
move/(_ Hk).
rewrite /fwd_sim_b.
case/(_ st s h Hst_s_h) => s' [Hs'1 Hs'2].
have st_s'_h : state_mint (y |=> signed k ry \U+ (x |=> signed k rx \U+ d)) st s' h.
  have : state_mint (x |=> signed k rx \U+ (y |=> signed k ry \U+ d)) st s' h.
    have : disj (mips_frame.modified_regs (multi_is_even_s rx a0 a1 a2))
      (mints_regs (assoc.cdom (x |=> signed k rx \U+ (y |=> signed k ry \U+ d)))).
      rewrite [mips_frame.modified_regs _]/=.
      Disj_remove_dup.
      apply/disP.
      eapply dis_inc_L.
        exact/disP/Hdisj.
      apply/incP; rewrite /List.incl /=; by intuition.
    move/(state_mint_invariant (x |=> signed k rx \U+ (y |=> signed k ry \U+ d))
                               (multi_is_even_s rx a0 a1 a2) (refl_equal _)).
    rewrite /invariant.
    by move/(_ _ _ _ Hst_s_h); apply.
  move=> ?.
  rewrite assoc.unionA (assoc.unionC (y |=> signed k ry)).
  by rewrite -assoc.unionA.
  apply assoc.disj_sing; apply/eqP; by Uniq_neq.
have : uniq(ry,a0,a1,a3,r0) by Uniq_uniq r0.
move/(fwd_sim_b_multi_is_even_s y ry a0 a1 a3 k (x |=> signed k rx \U+ d)).
move/(_ Hk) => Heven.
rewrite /fwd_sim_b in Heven.
case: {Heven}(Heven st s' h st_s'_h) => s'' [Hs''1 Hs''2].
exists (store.upd a0 ([a2]_s'' `& [a3]_s'') s'')%asm_expr.
split.
  apply while.exec_seq with (Some (s', h)) => //.
  apply while.exec_seq with (Some (s'', h)) => //.
  constructor.
  by constructor.
move: Hs'2 Hs''2.
rewrite /= /ZIT.eqb /ZIT.rem.
repeat Reg_upd.
split.
  case/andP => K1 K2.
  apply Hs'2 in K1.
  apply Hs''2 in K2.
  have Ha2_st'' : ([a2 ]_ s'')%asm_expr = one32.
    have Ha2_st' : ([a2 ]_ s')%asm_expr = one32.
      move: (proj1 Hst_s_h x (signed k rx)).
      rewrite assoc.get_union_sing_eq.
      case/(_ (refl_equal _)) => len ptr X ru_fit encU p_fit HX.
      case: encU => H1 H2 H3 H4.
      have slen_231 : s2Z len <> - 2 ^^ 31.
        rewrite H2.
        move=> abs.
        suff : `| Z.sgn (s2Z len) * Z_of_nat k | = `| - 2 ^^ 31 |.
          rewrite Zabs_Zopp Zabs_Zmult Zabs_Zsgn_1; last first.
            move=> abs'; by rewrite abs' in abs.
          rewrite mul1Z Zabs_Z_of_nat Zabs_power //.
          move=> abs'; rewrite abs' in Hk.
          by case: Hk => _ /ltZZ.
        by rewrite abs.
      have : uniq(rx, a0, a1, a2, r0) by Uniq_uniq r0.
      move/(multi_is_even_s_triple).
      move/(_ k X len ptr H1 slen_231 H2) => hoare_triple.
      move: (frame_rule_R _ _ _ hoare_triple assert_m.TT (assert_m.inde_TT _) (inde_cmd_mult_TT _))
        => {hoare_triple}hoare_triple.
      move/soundness : (hoare_triple).
      rewrite /while.hoare_semantics.
      move/(_ s h).
      have Htmp : ((fun s0 h0 => (var_e rx |--> len :: ptr :: nil ** int_e ptr |--> X)
                        s0 h0) ** assert_m.TT)%asm_assert s h.
        exists (heap_mint (signed k rx) s h), (h \D\ heap.dom ((heap_mint (signed k rx) s h))).
        split; first exact/heap.disj_difs'/seq_ext.inc_refl.
        split; last by [].
        rewrite -heap.union_difsK //; exact: heap_inclu_heap_mint_signed.
      move/(_ Htmp) => {Htmp}.
      case=> _.
      move/(_ _ _ Hs'1) => Htmp.
      rewrite assert_m.con_bangE_R assert_m.conAE in Htmp.
      apply assert_m.con_and_bang_inv_L in Htmp.
      case: Htmp => Htmp _.
      apply Htmp.
      rewrite -H4.
      apply Zmod_2_Zeven.
      case: Hs'2 => _ Hs'2.
      exact/eqP/Hs'2.
    rewrite -Ha2_st'.
    symmetry.
    Reg_unchanged.
    rewrite [modified_regs _]/=; by Uniq_not_In.
  have Ha3_st'' : ([a3 ]_ s'')%asm_expr = one32.
    move: (proj1 st_s'_h y (signed k ry)).
    rewrite assoc.get_union_sing_eq.
    case/(_ (refl_equal _)) => len ptr X ru_fit encU p_fit HX.
    case: encU => H1 H2 H3 H4.
    have slen_231 : s2Z len <> - 2 ^ 31.
      rewrite H2.
      move=> abs.
      suff : `| Z.sgn (s2Z len) * Z_of_nat k | = `| - 2 ^^ 31 |.
        rewrite Zabs_Zopp Zabs_Zmult Zabs_Zsgn_1; last first.
          move=> abs'; by rewrite abs' in abs.
        rewrite Zmult_1_l Zabs_Z_of_nat Zabs_power //.
        move=> abs'; rewrite abs' in Hk.
        by case: Hk => _ /ltZZ.
      by rewrite abs.
    have : uniq(ry, a0, a1, a3, r0) by Uniq_uniq r0.
    move/(multi_is_even_s_triple).
    move/(_ k X len ptr H1 slen_231 H2) => hoare_triple.
    move: (frame_rule_R _ _ _ hoare_triple assert_m.TT (assert_m.inde_TT _) (inde_cmd_mult_TT _))
      => {hoare_triple}hoare_triple.
    move/soundness : (hoare_triple).
    rewrite /while.hoare_semantics.
    move/(_ s' h).
    have Htmp : ((fun s0 h0 =>
        (var_e%asm_expr ry |--> len :: ptr :: nil ** int_e ptr |--> X)
          s0 h0) ** assert_m.TT)%asm_assert s' h.
      exists (heap_mint (signed k ry) s' h), (h \D\ heap.dom ((heap_mint (signed k ry) s' h))).
      split; first exact/heap.disj_difs'/seq_ext.inc_refl.
      split; last by [].
      rewrite -heap.union_difsK //; exact: heap_inclu_heap_mint_signed.
    move/(_ Htmp) => {Htmp}.
    case=> _.
    move/(_ _ _ Hs''1) => Htmp.
    rewrite assert_m.con_bangE_R assert_m.conAE in Htmp.
    apply assert_m.con_and_bang_inv_L in Htmp.
    case: Htmp => Htmp _.
    apply Htmp.
    rewrite -H4.
    apply Zmod_2_Zeven.
    case: Hs''2 => _ Hs''2.
    exact/eqP/Hs''2.
  by rewrite Ha2_st'' Ha3_st'' int_and_idempotent !Z2uK.
move=> K.
apply/andP; split.
  apply Hs'2.
  move: K; apply contra => /eqP K.
  apply u2Z_inj in K.
  Rewrite_reg a2 s'.
  by rewrite K int_andC int_and_0.
apply Hs''2.
move: K; apply contra => /eqP K.
apply u2Z_inj in K.
by rewrite K int_and_0.
Qed.

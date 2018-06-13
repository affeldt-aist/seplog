(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext machine_int multi_int.
Require Import encode_decode integral_type uniq_tac.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.

Require Import multi_halve_u_prg multi_halve_u_simu.
Require Import multi_double_u_prg multi_double_u_simu multi_double_u_safe_termination.
Require Import multi_lt_prg multi_lt_termination.
Require Import multi_is_even_u_and_prg multi_is_even_u_and_simu.
Require Import multi_halve_u_safe_termination.
Require Import begcd begcd_mips0.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope heap_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope asm_expr_scope.
Local Open Scope simu_scope.

Definition prelude_mips rk rg rx ry a0 a1 a2 a3 :=
  multi_is_even_u_and rk rx ry a0 a1 ;
  While (bne a0 r0) {{
    (multi_halve_u rk rx a0 a1 a2 a3 ;
     multi_halve_u rk ry a0 a1 a2 a3 ;
     multi_double_u rk rg a0 a1 a2 a3) ;
    multi_is_even_u_and rk rx ry a0 a1 }}.

Lemma sim_begcd_prelude g u v u1 u2 u3 v1 v2 v3 t1 t2 t3 k
  rk rg ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) ->
  uniq(rk, rg, ru, rv, ru1, ru2, ru3, rv1, rv2, rv3, rt1, rt2, rt3, a0, a1, a2, a3, r0) ->
  EGCD.prelude u v g
    <=( state_mint
          (g |=> unsign rk rg \U+ (u |=> unsign rk ru \U+ (v |=> unsign rk rv  \U+
          (u1 |=> signed k ru1 \U+ (u2 |=> signed k ru2 \U+ (u3 |=> signed k ru3 \U+
          (v1 |=> signed k rv1 \U+ (v2 |=> signed k rv2 \U+ (v3 |=> signed k rv3 \U+
          (t1 |=> signed k rt1 \U+ (t2 |=> signed k rt2 \U+ t3 |=> signed k rt3))))))))))),
        fun st s h =>
           ([ u ]_ st * [ g ]_ st)%pseudo_expr < \B^(Z.abs_nat (u2Z [ rk ]_ s)) /\
           (0 <= [ g ]_ st)%pseudo_expr /\
           (0 < [ u ]_ st)%pseudo_expr /\
           0 < (u2Z [ rk ]_s) )
  prelude_mips rk rg ru rv a0 a1 a2 a3.
Proof.
move=> Hvars Hregs.
apply fwd_sim_while ; first by done.
- rewrite /invariant => st s h [st_s_h H] s' h' Hmips; split.
  + set d := assoc.union _ _ in st_s_h.
    have : invariant (state_mint d) (multi_is_even_u_and rk ru rv a0 a1).
      apply state_mint_invariant => //.
      rewrite /d [mips_frame.modified_regs _]/=; by Disj_mints_regs.
    by move/(_ _ _ _ st_s_h _ _ Hmips).
  + Rewrite_reg rk s. exact H.
- rewrite /rela_hoare => st s h Hyp st' Hseplog s' h' Hmips.
  have -> : ([ u ]_ st' = [ u ]_ st / 2)%pseudo_expr.
    case/syntax_m.seplog_m.semop_prop_m.exec_seq_inv : Hseplog.
    case.
    + move=> [st'' h''] [Hseplog1 Hseplog2].
      apply trans_eq with ([ u ]_ st'')%pseudo_expr.
      + Rewrite_var u st''. reflexivity.
      + move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : Hseplog1.
        case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
        by syntax_m.seplog_m.assert_m.expr_m.Store_upd.
    + case=> _. by move/syntax_m.seplog_m.semop_prop_m.from_none.
  have -> : ([ g ]_ st' = [ g ]_ st * 2)%pseudo_expr.
    move/syntax_m.seplog_m.semop_prop_m.exec_seq_assoc' : Hseplog.
    case/syntax_m.seplog_m.semop_prop_m.exec_seq_inv => st'' [st_st''].
    destruct st'' as [[st'' h'']|]; last by move/syntax_m.seplog_m.semop_prop_m.from_none.
    move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv.
    case/syntax_m.seplog_m.exec0_assign_inv => Hh'' /= ->.
    syntax_m.seplog_m.assert_m.expr_m.Store_upd.
    rewrite (syntax_m.var_unchanged _ _ _ _ _ st_st'' g) //.
    rewrite [syntax_m.seplog_m.modified_vars _]/=; move/inP; rewrite -/(~ _); by Uniq_not_In.
  Rewrite_reg rk s.
  have u_st_even : (2 | ([ u ]_st)%pseudo_expr).
    apply Zmod_divide => //.
    case : Hyp => _ [] _ /= /andP []. by move/eqP.
  split.
    rewrite mulZC -mulZA -Zdivide_Zdiv_eq // mulZC; tauto.
  split; first omega.
  split; last tauto.
  apply: (proj1 (Zdivide_Zdiv_lt_pos _ _ _ _ _)) => //; tauto.
- apply fwd_sim_b_stren with (state_mint
        (g |=> unsign rk rg \U+ (u |=> unsign rk ru \U+ (v |=> unsign rk rv \U+
        (u1 |=> signed k ru1 \U+ (u2 |=> signed k ru2 \U+ (u3 |=> signed k ru3 \U+
        (v1 |=> signed k rv1 \U+ (v2 |=> signed k rv2 \U+ (v3 |=> signed k rv3 \U+
        (t1 |=> signed k rt1 \U+ (t2 |=> signed k rt2 \U+ t3 |=> signed k rt3)))))))))))).
    by intuition.
  assoc_tac_m.put_in_front v.
  assoc_tac_m.put_in_front u.
  apply fwd_sim_b_multi_is_even_u_and.
  + rewrite [Equality.sort assoc.l]/= in Hvars *; by Uniq_uniq O.
  + by Uniq_uniq r0 .
- apply fwd_sim_seq with (fun st s _ => 0 <= [ g ]_ st /\ 0 < [ u ]_ st /\
  ([ u ]_ st * [ g ]_ st) < 2 ^^ (Z.abs_nat (u2Z ([rk ]_ s)%asm_expr) * 32 - 1))%pseudo_expr => //.
  + rewrite /rela_hoare => st s h Hyp st' Hseplog s' h' Hmips.
    have -> : ([ u ]_ st' = [ u ]_ st / 2)%pseudo_expr.
      move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : Hseplog.
      case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
      by syntax_m.seplog_m.assert_m.expr_m.Store_upd.
    Rewrite_var g st. Rewrite_reg rk s.
    split; first tauto.
    have u_st_even : (2 | ([ u ]_st)%pseudo_expr).
      apply Zmod_divide => //. case : Hyp => _ [] _ /=. by case/andP => /eqP.
    split.
    * apply: (proj1 (Zdivide_Zdiv_lt_pos _ _ _ _ _)) => //; tauto.
    * apply (@Z.lt_le_trans _ (\B^(Z.abs_nat (u2Z ([rk ]_ s))) / 2)).
      - rewrite mulZC -Zdivide_Zdiv_eq_2 //.
        apply Zdiv_lt_upper_bound => //.
        rewrite (mulZC _ 2) -Z_div_exact_full_2 //.
        + rewrite mulZC; tauto.
        + apply Zpower_mod, lt_O_neq.
          apply/ltP; rewrite muln_gt0 /= andbT.
          apply/O_lt_Zabs_nat; tauto.
     - rewrite Zpower_div //; first exact: leZZ.
       apply/lt_O_neq/ltP; rewrite muln_gt0 /= andbT.
       apply/O_lt_Zabs_nat; tauto.
  + assoc_tac_m.put_in_front u.
    apply pfwd_sim_fwd_sim_spec; last by apply multi_halve_u_safe_termination; Uniq_uniq r0.
    apply pfwd_sim_halve_u.
    - by Uniq_uniq r0.
    - by Disj_mints_regs.
    - by Notin_dom.
    - by Notin_cdom.
  + apply fwd_sim_seq with (fun st s _ =>
    ([ g ]_ st)%pseudo_expr < 2 ^^ ((Z.abs_nat (u2Z ([rk ]_ s)) * 32) - 1)) => //.
    * rewrite /rela_hoare => st s h HP0 st' Hseplog s' h' Hmips.
      Rewrite_var g st. Rewrite_reg rk s.
      apply Zlt_Zmult_inv with ([ u ]_ st)%pseudo_expr.
      - tauto.
      - tauto.
      - apply (@leZ_trans 1) => //; exact: expZ_ge1.
    * assoc_tac_m.put_in_front u.
      apply pfwd_sim_fwd_sim_spec; last first.
        assoc_tac_m.put_in_front v.
        apply multi_halve_u_safe_termination; by Uniq_uniq r0.
      assoc_tac_m.put_in_front v.
      apply pfwd_sim_halve_u => //.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_cdom.
    * apply pfwd_sim_fwd_sim_spec; last by apply multi_double_u_safe_termination; Uniq_uniq r0.
      apply pfwd_sim_double_u.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_cdom.
Qed.

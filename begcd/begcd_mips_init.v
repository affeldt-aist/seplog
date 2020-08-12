(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int multi_int encode_decode.
Require Import ssrnat_ext.
Require Import integral_type uniq_tac.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.

Require Import multi_zero_s_prg multi_zero_s_simu multi_zero_s_safe_termination.
Require Import multi_one_s_prg multi_one_s_simu multi_one_s_safe_termination.
Require Import multi_negate_prg multi_negate_simu multi_negate_safe_termination.
Require Import multi_is_even_u_prg multi_is_even_u_simu.
Require Import multi_sub_s_u_prg multi_sub_s_u_simu multi_sub_s_u_safe_termination.
Require Import copy_s_u_prg copy_s_u_simu copy_s_u_safe_termination.
Require Import begcd begcd_mips0.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope heap_scope.
Local Open Scope uniq_scope.
Local Open Scope assoc_scope.

Definition init_mips rk ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3
  a0 a1 a2 a3 a4 a5 a6 :=
  ((multi_one_s ru1 rk a0 a1 a2 a3 ;
    multi_zero_s ru2 ;
    copy_s_u rk ru3 ru a0 a1 a2 a3 ;
    copy_s_u rk rv1 rv a0 a1 a2 a3 ;
    (multi_one_s rv2 rk a0 a1 a2 a3 ;
     multi_sub_s_u rk rv2 ru a0 a1 a2 a3 a4 a5 a6) ;
    copy_s_u rk rv3 rv a0 a1 a2 a3) ;
   multi_is_even_u rk ru a0 ;
   If_beq a0 , r0 Then
    multi_zero_s rt1 ;
    (multi_one_s rt2 rk a0 a1 a2 a3 ;
     multi_negate rt2 a0) ;
    (copy_s_u rk rt3 rv a0 a1 a2 a3 ;
      multi_negate rt3 a0)
   Else
    (multi_one_s rt1 rk a0 a1 a2 a3 ;
     multi_zero_s rt2 ;
     copy_s_u rk rt3 ru a0 a1 a2 a3))%asm_cmd.

Local Open Scope simu_scope.

Lemma fwd_sim_begcd_init vu vv g u v u1 u2 u3 v1 v2 v3 t1 t2 t3 k
  rk rg ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 :
  uniq(g,u,v,u1,u2,u3,v1,v2,v3,t1,t2,t3) ->
  uniq(rk,rg,ru,rv,ru1,ru2,ru3,rv1,rv2,rv3,rt1,rt2,rt3,a0,a1,a2,a3,a4,a5,a6,r0) ->
  0 < vu -> 0 < vv ->
  EGCD.BEGCD_TAOCP.init u v u1 u2 u3 v1 v2 v3 t1 t2 t3
    <=( state_mint
          (g |=> unsign rk rg \U+ (u |=> unsign rk ru \U+ (v |=> unsign rk rv \U+
          (u1 |=> signed k ru1 \U+ (u2 |=> signed k ru2 \U+ (u3 |=> signed k ru3 \U+
          (v1 |=> signed k rv1 \U+ (v2 |=> signed k rv2 \U+ (v3 |=> signed k rv3 \U+
          (t1 |=> signed k rt1 \U+ (t2 |=> signed k rt2 \U+ t3 |=> signed k rt3))))))))))),
        fun st s _ => (EGCD.C2 vu vv u v g st /\ EGCD.C3 vu vv u v g st) /\ uv_bound rk s u v st k)
  init_mips rk ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6.
Proof.
move=> Hvars Hregs Hvu Hvv.
rewrite /EGCD.BEGCD_TAOCP.init /init_mips.
apply fwd_sim_seq with (fun st s _ => (EGCD.C2 vu vv u v g st /\ EGCD.C3 vu vv u v g st /\
    EGCD.uivi_init u v u1 u2 u3 v1 v2 v3 st) /\ uv_bound rk s u v st k) => //.
- rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm; split.
  + move/syntax_m.seplog_m.hoare_prop_m.soundness:
      (EGCD.BEGCD_TAOCP_FUN_COR.triple_init0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvars Hvu Hvv).
    rewrite /while.hoare_semantics.
    case/( _ _ syntax_m.seplog_m.assert_m.heap.emp (proj1 Hcond)) => _.
    by move/(_ _ _ exec_pseudo).
  + rewrite /uv_bound.
    Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
- apply fwd_sim_seq with (fun st s _ => (EGCD.C2 vu vv u v g st /\
    EGCD.C3 vu vv u v g st) /\ uv_bound rk s u v st k) => //.
  + rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm; split.
    * rewrite /EGCD.C2 /EGCD.C3 /= in Hcond *.
      Rewrite_var u st. Rewrite_var v st. Rewrite_var g st. tauto.
    * rewrite /uv_bound.
      Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
  + assoc_tac_m.put_in_front u1.
    apply (fwd_sim_stren _ (fun st s _ => 0 < u2Z ([ rk ]_s)%asm_expr < 2 ^^ 31 /\
      k = '|u2Z ([ rk ]_ s)%asm_expr|)); last first.
      apply pfwd_sim_fwd_sim; last first.
        set st_s_h := state_mint _.
        apply safe_termination_stren with (fun st s h => st_s_h st s h /\
          (0 < Z_of_nat k < 2 ^^ 31) /\ k = '|u2Z ([ rk ]_ s)%asm_expr|).
          move=> st s h [] H_st_s_h [] [Hrk1 Hrk2] Hk.
          split; first by [].
          split; last by [].
          rewrite Hk Z_of_nat_Zabs_nat //; by apply min_u2Z.
        by apply multi_one_s_safe_termination; Uniq_uniq r0.
      rewrite /pfwd_sim => st s h st_s_h Hcond.
      apply pfwd_sim_one_s; last exact st_s_h.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_cdom.
    move=> st s _ [] _ []; tauto.
  + apply fwd_sim_seq with (fun st s _ => (EGCD.C2 vu vv u v g st /\
      EGCD.C3 vu vv u v g st) /\ uv_bound rk s u v st k) => //.
    * rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm; split.
      - rewrite /EGCD.C2 / EGCD.C3 in Hcond *.
        rewrite /=.
        Rewrite_var u st. Rewrite_var v st. Rewrite_var g st. tauto.
      - rewrite /uv_bound.
        Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
    * assoc_tac_m.put_in_front u2.
      apply pfwd_sim_fwd_sim_spec; last by apply multi_zero_s_safe_termination; Uniq_uniq r0.
      apply pfwd_sim_zero_s.
      - by Uniq_uniq r0.
      - by Notin_dom.
      - by Notin_cdom.
    * apply fwd_sim_seq with (fun st s _ => (EGCD.C2 vu vv u v g st /\
        EGCD.C3 vu vv u v g st) /\ uv_bound rk s u v st k) => //.
      - rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm; split.
        + rewrite /EGCD.C2 / EGCD.C3 in Hcond *.
          rewrite /=.
          Rewrite_var u st. Rewrite_var v st. Rewrite_var g st. tauto.
        + rewrite /uv_bound.
          Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
      - assoc_tac_m.put_in_front u.
        assoc_tac_m.put_in_front u3.
        apply (fwd_sim_stren _ (fun st s _ => 0 < (u2Z [rk ]_ s)%asm_expr < 2 ^^ 31 /\
          k = '|u2Z ([rk ]_ s)%asm_expr| /\ 0 <= ([u ]_ st)%pseudo_expr < \B^k)).
          move=> st s _ [] _ [] Hrk [] Hk [] [Hu1 Hu2] _.
          repeat (split; first by []).
          split; first exact: ltZW.
          apply/(ltZ_trans Hu2)/Zbeta_lt.
          rewrite minusE subn1 prednK // Hk.
          apply O_lt_Zabs_nat; by case: Hrk.
        apply pfwd_sim_fwd_sim; last first.
          move=> st s h [] st_s_h [] _ [] Hk _; subst k.
          move: st s h st_s_h.
          apply copy_s_u_safe_termination.
          by rewrite [Equality.sort _]/= in Hvars *; Uniq_uniq O.
          by Uniq_uniq r0.
        apply pfwd_sim_copy_s_u.
        + rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
        + by Uniq_uniq r0.
        + by Disj_mints_regs.
        + by Notin_dom.
        + by Notin_dom.
        + by Notin_cdom.
        + by Notin_cdom.
      - apply fwd_sim_seq with (fun st s _ => (EGCD.C2 vu vv u v g st /\
          EGCD.C3 vu vv u v g st) /\ uv_bound rk s u v st k) => //.
        + rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm; split.
          * rewrite /EGCD.C2 / EGCD.C3 in Hcond *.
            rewrite /=.
            Rewrite_var u st. Rewrite_var v st. Rewrite_var g st. tauto.
          * rewrite /uv_bound.
            Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
        + assoc_tac_m.put_in_front v.
          assoc_tac_m.put_in_front v1.
          apply (fwd_sim_stren _ (fun st s _ => 0 < u2Z [rk ]_ s < 2 ^^ 31 /\
            k = '|u2Z ([ rk ]_ s)| /\
            0 <= ([v ]_ st)%pseudo_expr < \B^k))%asm_expr.
            move=> st s _ [] _ [] Hrk [] Hk [] _ [Hv1 Hv2].
            repeat (split; first by []).
            split; first exact: ltZW.
            apply/(ltZ_trans Hv2)/Zbeta_lt.
            rewrite minusE subn1 prednK // Hk.
            apply O_lt_Zabs_nat; by case: Hrk.
          apply pfwd_sim_fwd_sim; last first.
            move=> st s h [] st_s_h [] _ [] Hk _; subst k.
            move: st s h st_s_h.
            apply copy_s_u_safe_termination.
            by rewrite [Equality.sort _]/= in Hvars *; Uniq_uniq O.
            by Uniq_uniq r0.
          apply pfwd_sim_copy_s_u.
          - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
          - by Uniq_uniq r0.
          - by Disj_mints_regs.
          - by Notin_dom.
          - by Notin_dom.
          - by Notin_cdom.
          - by Notin_cdom.
        + apply fwd_sim_seq with (fun st s _ => (EGCD.C2 vu vv u v g st /\
            EGCD.C3 vu vv u v g st) /\ uv_bound rk s u v st k) => //.
          - rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm; split.
            + rewrite /EGCD.C2 / EGCD.C3 in Hcond *.
              rewrite /=.
              Rewrite_var u st. Rewrite_var v st. Rewrite_var g st. tauto.
            + rewrite /uv_bound.
              Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
          - apply fwd_sim_pcode_equiv with (v2 <- nat_e 1 ; v2 <- var_e v2 \- var_e u)%pseudo_expr%pseudo_cmd;
              last by apply equiv_pcode_example2; Uniq_neq.
            apply fwd_sim_seq with (fun st s _ => [ rk ]_ s <> zero32 /\
              u2Z ([ rk ]_ s) < 2 ^^ 31 /\ k = '|u2Z ([ rk ]_ s)| /\
              `| ([ v2 ]_ st)%pseudo_expr | < \B^(k - 1) /\
              0 <= ([ u ]_ st)%pseudo_expr < \B^(k - 1))%asm_expr => //.
            + rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
              rewrite /uv_bound in Hcond.
              Rewrite_reg rk s. Rewrite_var u st.
              move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
              case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
              repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
              split; first by move=> abs; rewrite abs Z2uK // in Hcond; lia.
              repeat (split; first by tauto).
              split; first by move: (Zbeta_ge0 k) => /= ?; ssromega.
              ssromega.
            + assoc_tac_m.put_in_front v2.
              apply (fwd_sim_stren _ (fun st s _ => 0 < u2Z ([ rk ]_ s)%asm_expr < 2 ^^ 31 /\
                k = '|u2Z ([ rk ]_ s)%asm_expr|)).
                move=> st s _ [] _ []; tauto.
              apply pfwd_sim_fwd_sim; last first.
                set st_s_h := state_mint _.
                apply safe_termination_stren with (fun st s h => st_s_h st s h /\
                  (0 < Z_of_nat k < 2 ^^ 31) /\ k = '|u2Z ([ rk ]_ s)%asm_expr|).
                  move=> st s h [] st_s_h' [] [Hrk1 Hrk2] Hk.
                  split; first by [].
                  split; last by [].
                  rewrite Hk Z_of_nat_Zabs_nat //; exact: min_u2Z.
                by apply multi_one_s_safe_termination ; Uniq_uniq r0.
              rewrite /pfwd_sim => st s h st_s_h Hcond.
              apply pfwd_sim_one_s; last exact st_s_h.
              - by Uniq_uniq r0.
              - by Disj_mints_regs.
              - by Notin_dom.
              - by Notin_cdom.
            + assoc_tac_m.put_in_front u.
              assoc_tac_m.put_in_front v2.
              apply pfwd_sim_fwd_sim; last first.
                eapply safe_termination_stren; last first.
                  apply (safe_termination_multi_sub_s_u u v2 k).
                  - rewrite [Equality.sort _]/= /bipl.var.v in Hvars *. by Uniq_uniq O.
                  - by Uniq_uniq r0.
                move=> st s h [] st_s_h H.
                split; first by apply st_s_h.
                case: H => rk0 [rk231 [HL [Hv2 Hu]]].
                split; first by [].
                rewrite HL Z_of_nat_Zabs_nat; last by apply min_u2Z.
                split; last by [].
                rewrite ltZ_neqAle; split; last by apply min_u2Z.
                contradict rk0.
                rewrite (_ : 0 = u2Z zero32) in rk0; last by rewrite Z2uK.
                by move/u2Z_inj in rk0.
              apply pfwd_sim_multi_sub_s_u_wo_overflow.
              - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
              - by Uniq_uniq r0.
              - by Disj_mints_regs.
              - by Notin_dom.
              - by Notin_dom.
              - by Notin_cdom.
              - by Notin_cdom.
          - assoc_tac_m.put_in_front v.
            assoc_tac_m.put_in_front v3.
            apply (fwd_sim_stren _ (fun st s _ => 0 < u2Z ([ rk ]_s)%asm_expr < 2 ^^ 31 /\
              k = '|u2Z ([ rk ]_ s)%asm_expr| /\
              0 <= ([ v ]_ st)%pseudo_expr < \B^k)%asm_expr).
              move=> st s _ [] _ [] Hrk [] Hk [] _ [Hv1 Hv2].
              repeat (split; first by []).
              split; first exact/ltZW.
              apply/(ltZ_trans Hv2)/Zbeta_lt.
              rewrite minusE subn1 prednK // Hk.
              apply O_lt_Zabs_nat; by case: Hrk.
            apply pfwd_sim_fwd_sim; last first.
              move=> st s h [] st_s_h [] _ [] Hk _; subst k.
              move: st s h st_s_h.
              apply copy_s_u_safe_termination.
              by rewrite [Equality.sort _]/= in Hvars *; Uniq_uniq O.
              by Uniq_uniq r0.
            apply pfwd_sim_copy_s_u.
            - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
            - by Uniq_uniq r0.
            - by Disj_mints_regs.
            - by Notin_dom.
            - by Notin_dom.
            - by Notin_cdom.
            - by Notin_cdom.
- apply fwd_sim_ifte_spec => //.
  + rewrite /invariant => st s h [st_s_h Hcond] s' h' exec_asm; split.
    * eapply state_mint_invariant; [idtac | idtac | apply st_s_h | apply exec_asm] => //.
      rewrite [mips_frame.modified_regs _]/=.
      by Disj_mints_regs.
    * rewrite /uv_bound.
      Rewrite_reg rk s. tauto.
  + assoc_tac_m.put_in_front u.
    apply fwd_sim_b_multi_is_even_u.
    + by Uniq_uniq r0.
    + by Disj_mints_regs.
    + by Notin_dom.
    + by Notin_cdom.
  + apply fwd_sim_seq with (fun st s _ => ((EGCD.C2 vu vv u v g st /\
      EGCD.C3 vu vv u v g st /\ EGCD.uivi_init u v u1 u2 u3 v1 v2 v3 st) /\
      uv_bound rk s u v st k) /\
      ([var_e u \% nat_e 2 \= nat_e 1 ]b_ st)%pseudo_expr) => //.
    * rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
      move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
      case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
      rewrite /EGCD.C2 /EGCD.C3 /EGCD.uivi_init /uv_bound in Hcond *.
      simpl.
      repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
      Rewrite_reg rk s. tauto.
    * assoc_tac_m.put_in_front t1.
      apply pfwd_sim_fwd_sim_spec; last by apply multi_zero_s_safe_termination; Uniq_uniq r0.
      apply pfwd_sim_zero_s.
      - by Uniq_uniq r0.
      - by Notin_dom.
      - by Notin_cdom.
  + apply fwd_sim_seq with (fun st s _ => ((EGCD.C2 vu vv u v g st /\
      EGCD.C3 vu vv u v g st /\ EGCD.uivi_init u v u1 u2 u3 v1 v2 v3 st) /\
      uv_bound rk s u v st k) /\
      ([var_e u \% nat_e 2 \= nat_e 1 ]b_ st)%pseudo_expr) => //.
    * rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
      move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
      case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
      rewrite /EGCD.C2 /EGCD.C3 /EGCD.uivi_init /uv_bound in Hcond *.
      simpl.
      repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
      Rewrite_reg rk s. tauto.
    * apply fwd_sim_pcode_equiv with (t2 <- nat_e 1 ; t2 <- .--e (var_e t2))%pseudo_expr%pseudo_cmd; last first.
        eapply equiv_pcode_trans; by [apply equiv_pcode_example3 | apply equiv_pcode_example_assign].
      apply fwd_sim_seq with (fun st s _ => ((EGCD.C2 vu vv u v g st /\
        EGCD.uivi_init u v u1 u2 u3 v1 v2 v3 st) /\ uv_bound rk s u v st k)) => //.
      - rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
        move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
        rewrite /EGCD.C2 /EGCD.uivi_init /uv_bound in Hcond *.
        repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        Rewrite_reg rk s. tauto.
      - assoc_tac_m.put_in_front t2.
        apply (fwd_sim_stren _ (fun st s _ => 0 < u2Z ([ rk ]_ s)%asm_expr < 2 ^^ 31 /\
          k = '|u2Z ([ rk ]_ s)%asm_expr|)).
          move=> st s _ [] [] _ []; tauto.
        apply pfwd_sim_fwd_sim; last first.
          set st_s_h := state_mint _.
          apply safe_termination_stren with (fun st s h => st_s_h st s h /\
            0 < Z_of_nat k < 2 ^^ 31 /\ k = '|u2Z ([ rk ]_s)%asm_expr|).
            move=> st s h [] Hst_s_h [] Hrk Hk.
            split; first by [].
            split; last by [].
            rewrite Hk Z_of_nat_Zabs_nat //; exact: min_u2Z.
          by apply multi_one_s_safe_termination; Uniq_uniq r0.
        rewrite /pfwd_sim => st s h st_s_h Hcond.
        apply pfwd_sim_one_s; last by exact st_s_h.
        + by Uniq_uniq r0.
        + by Disj_mints_regs.
        + by Notin_dom.
        + by Notin_cdom.
     - assoc_tac_m.put_in_front t2.
       apply (fwd_sim_stren _ (fun st s h => 0 < Z_of_nat k < 2 ^^ 31)).
         move=> st s _ [] _ [] H [] -> _.
         rewrite Z_of_nat_Zabs_nat //; exact: min_u2Z.
       apply pfwd_sim_fwd_sim_spec; last by apply multi_negate_safe_termination; Uniq_uniq r0.
       apply pfwd_sim_multi_negate.
       + by Uniq_uniq r0.
       + by Disj_mints_regs.
       + by Notin_dom.
       + by Notin_cdom.
     - apply fwd_sim_pcode_equiv with (t3 <- var_e v ; t3 <- .--e (var_e t3))%pseudo_expr%pseudo_cmd; last first.
         eapply equiv_pcode_trans; by [apply equiv_pcode_example3 | apply equiv_pcode_example_assign].
       apply fwd_sim_seq with (fun st s _ =>
         ((EGCD.C2 vu vv u v g st /\ EGCD.uivi_init u v u1 u2 u3 v1 v2 v3 st) /\
         uv_bound rk s u v st k)) => //.
       + rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
         move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
         case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
         rewrite /EGCD.C2 /EGCD.uivi_init /uv_bound in Hcond *.
         repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
         Rewrite_reg rk s. tauto.
       + assoc_tac_m.put_in_front v.
         assoc_tac_m.put_in_front t3.
         apply (fwd_sim_stren _ (fun st s h => 0 < u2Z ([ rk ]_ s)%asm_expr < 2 ^^ 31 /\
           k = '|u2Z ([ rk ]_ s)%asm_expr| /\ 0 <= ([ v ]_ st)%pseudo_expr < \B^k)%asm_expr).
           move=> st s _ [] [] _ [] Hrk [] Hk [] _ [Hv1 Hv2] _.
           repeat (split; first by []).
           split; first exact/ltZW.
           apply/(ltZ_trans Hv2)/Zbeta_lt.
           rewrite minusE subn1 prednK // Hk.
           apply O_lt_Zabs_nat; by case: Hrk.
         apply pfwd_sim_fwd_sim; last first.
           move=> st s h [] st_s_h [] _ [] Hk _; subst k.
           move: st s h st_s_h.
           apply copy_s_u_safe_termination.
           by rewrite [Equality.sort _]/= in Hvars *; Uniq_uniq O.
           by Uniq_uniq r0.
         apply pfwd_sim_copy_s_u.
         * rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
         * by Uniq_uniq r0.
         * by Disj_mints_regs.
         * by Notin_dom.
         * by Notin_dom.
         * by Notin_cdom.
         * by Notin_cdom.
       + assoc_tac_m.put_in_front t3.
        apply (fwd_sim_stren _ (fun st s _ => 0 < Z_of_nat k < 2 ^^ 31)).
          move=> st s _ [] _ [] H [] -> _.
          rewrite Z_of_nat_Zabs_nat //; exact: min_u2Z.
        apply pfwd_sim_fwd_sim_spec; last by apply multi_negate_safe_termination; Uniq_uniq r0.
        apply pfwd_sim_multi_negate.
        * by Uniq_uniq r0.
        * by Disj_mints_regs.
        * by Notin_dom.
        * by Notin_cdom.
- apply fwd_sim_seq with (fun st s _ => ((EGCD.C2 vu vv u v g st /\
     EGCD.uivi_init u v u1 u2 u3 v1 v2 v3 st) /\ uv_bound rk s u v st k) ) => //.
  + rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
    move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
    case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
    rewrite /EGCD.C2 /EGCD.uivi_init /uv_bound in Hcond *.
    repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
    Rewrite_reg rk s; tauto.
  + assoc_tac_m.put_in_front t1.
    apply (fwd_sim_stren _ (fun st s h => 0 < (u2Z ([ rk ]_s)%asm_expr) < 2 ^^ 31 /\
      k = '|u2Z ([ rk ]_ s)%asm_expr|)).
      move=> st s _ [] [] _ []; tauto.
    apply pfwd_sim_fwd_sim; last first.
      set st_s_h := state_mint _.
      apply safe_termination_stren with (fun st s h => st_s_h st s h /\
        0 < Z_of_nat k < 2 ^^ 31 /\ k = '|u2Z ([ rk ]_ s)%asm_expr|).
        move=> st s h [] Hst_s_h [] Hrk Hk.
        split; first by [].
        split; last by [].
        rewrite Hk Z_of_nat_Zabs_nat //; exact: min_u2Z.
      by apply multi_one_s_safe_termination; Uniq_uniq r0.
    rewrite /pfwd_sim => st s h Hst_s_h Hcond.
    apply pfwd_sim_one_s; last exact Hst_s_h.
    * by Uniq_uniq r0.
    * by Disj_mints_regs.
    * by Notin_dom.
    * by Notin_cdom.
  + apply fwd_sim_seq with (fun st s _ => (EGCD.C2 vu vv u v g st /\
      EGCD.uivi_init u v u1 u2 u3 v1 v2 v3 st) /\ uv_bound rk s u v st k) => //.
    * rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
      move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
      case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
      rewrite /EGCD.C2 /EGCD.uivi_init /uv_bound in Hcond *.
      repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
      Rewrite_reg rk s. tauto.
    * assoc_tac_m.put_in_front t2.
      apply pfwd_sim_fwd_sim_spec; last by apply multi_zero_s_safe_termination; Uniq_uniq r0.
      apply pfwd_sim_zero_s.
      - by Uniq_uniq r0.
      - by Notin_dom.
      - by Notin_cdom.
    * assoc_tac_m.put_in_front u.
      assoc_tac_m.put_in_front t3.
      apply (fwd_sim_stren _ (fun st s h => 0 < u2Z ([ rk ]_s)%asm_expr < 2 ^^ 31 /\
        k = '|u2Z ([ rk ]_ s)%asm_expr| /\ 0 <= ([ u ]_ st)%pseudo_expr < \B^k)%asm_expr).
        move=> st s _ [] _ [] Hrk [] Hk [] [Hu1 Hu2] _.
        repeat (split; first by []).
        split; first exact/ltZW.
        apply/(ltZ_trans Hu2)/Zbeta_lt.
        rewrite minusE subn1 prednK // Hk.
        apply O_lt_Zabs_nat; by case: Hrk.
      apply pfwd_sim_fwd_sim; last first.
        move=> st s h [] st_s_h [] _ [] Hk _; subst k.
        move: st s h st_s_h.
        apply copy_s_u_safe_termination.
        by rewrite [Equality.sort _]/= in Hvars *; Uniq_uniq O.
        by Uniq_uniq r0.
      apply pfwd_sim_copy_s_u.
      - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_cdom.
      - by Notin_cdom.
Qed.

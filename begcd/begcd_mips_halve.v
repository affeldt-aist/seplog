(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int multi_int encode_decode.
Require Import ssrnat_ext integral_type uniq_tac.
Import MachineInt.
Require Import mips_bipl mips_cmd mips_tactics mips_syntax.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.

Require Import multi_add_s_u_prg multi_add_s_u_simu multi_add_s_u_safe_termination.
Require Import multi_sub_s_u_prg multi_sub_s_u_simu multi_sub_s_u_safe_termination.
Require Import multi_halve_s_prg multi_halve_s_simu multi_halve_s_safe_termination.
Require Import multi_is_even_s_and_prg multi_is_even_s_and_simu.
Require Import begcd begcd_mips0.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope heap_scope.
Local Open Scope uniq_scope.
Local Open Scope assoc_scope.
Local Open Scope simu_scope.

Definition halve_mips rk ru rv rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 :=
  (multi_is_even_s_and rt1 rt2 a0 a1 a2 a3 ;
   If_bne a0 , r0 Then
     multi_halve_s rt1 a0 a1 a2 a3 a4 a5 ;
     multi_halve_s rt2 a0 a1 a2 a3 a4 a5 ;
     multi_halve_s rt3 a0 a1 a2 a3 a4 a5
   Else
   ((multi_add_s_u rk rt1 rv a0 a1 a2 a3 a4 a5 a6 ;
     multi_halve_s rt1 a0 a1 a2 a3 a4 a5) ;
    (multi_sub_s_u rk rt2 ru a0 a1 a2 a3 a4 a5 a6 ;
     multi_halve_s rt2 a0 a1 a2 a3 a4 a5) ;
     multi_halve_s rt3 a0 a1 a2 a3 a4 a5))%mips_cmd.

Lemma fwd_sim_begcd_halve vu vv g u v u1 u2 u3 v1 v2 v3 t1 t2 t3 k
  rk rg ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 :
  uniq(g,u,v,u1,u2,u3,v1,v2,v3,t1,t2,t3) ->
  uniq(rk,rg,ru,rv,ru1,ru2,ru3,rv1,rv2,rv3,rt1,rt2,rt3,a0,a1,a2,a3,a4,a5,a6,r0) ->
  0 < vu -> 0 < vv ->
  EGCD.BEGCD_TAOCP.halve u v t1 t2 t3
    <=( state_mint
          (g |=> unsign rk rg \U+ (u |=> unsign rk ru \U+ (v |=> unsign rk rv \U+
          (u1 |=> signed k ru1 \U+ (u2 |=> signed k ru2 \U+ (u3 |=> signed k ru3 \U+
          (v1 |=> signed k rv1 \U+ (v2 |=> signed k rv2 \U+ (v3 |=> signed k rv3 \U+
          (t1 |=> signed k rt1 \U+ (t2 |=> signed k rt2 \U+  t3 |=> signed k rt3))))))))))),
        (fun st s _ =>
           (((EGCD.C2 vu vv u v g st /\
              (Zodd ([u ]_ st) \/ Zodd ([v ]_ st)) /\
              EGCD.CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 st /\
              EGCD.C4 u3 v3 t3 st /\
              EGCD.C5 u3 v3 st /\
              gcdZ ([ u ]_ st) ([ v ]_ st) = gcdZ ([ u3 ]_ st) ([v3 ]_ st) /\
              EGCD.uivi_bounds u v u1 v1 u2 v2 u3 v3 st /\
              EGCD.ti_bounds u v t1 t2 t3 st) /\ uv_bound rk s u v st k) /\
            ([var_e t3 \!= nat_e 0 ]b_ st)) /\
           ([var_e t3 \% nat_e 2 \= nat_e 0 ]b_ st))%pseudo_expr )
  halve_mips rk ru rv rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6.
Proof.
move=> Hvars Hregs Hvu Hvv.
rewrite /EGCD.BEGCD_TAOCP.halve /halve_mips.
apply fwd_sim_ifte => //.
- rewrite /invariant => st s h st_s_h s' h' exec_asm; split.
  + eapply state_mint_invariant; [idtac | idtac | apply st_s_h | apply exec_asm] => //.
    rewrite [mips_frame.modified_regs _]/=.
    by Disj_mints_regs.
  + rewrite /uv_bound. Rewrite_reg rk s. tauto.
- assoc_tac_m.put_in_front t2.
  assoc_tac_m.put_in_front t1.
  apply (fwd_sim_b_pull_out _ (0 < Z_of_nat k < 2 ^^ 31)).
    move=> st s h [] st_s_h H.
    rewrite /uv_bound in H.
    decompose [and] H; clear H.
    rewrite H10 Z_of_nat_Zabs_nat //; exact: min_u2Z.
  move=> Hrk.
  set st_s_h := state_mint _.
  apply fwd_sim_b_stren with st_s_h; first by intuition.
  apply fwd_sim_b_multi_is_even_s_and => //.
  + rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
  + by Uniq_uniq r0.
  + rewrite [mips_frame.modified_regs _]/=; by Disj_mints_regs.
- apply fwd_sim_seq with (fun _ _ _ => Z_of_nat k < 2 ^^ 31) => //.
  + rewrite /rela_hoare => st s h P0 st' exec_pseudo s' h' exec_asm.
    rewrite /uv_bound in P0.
    decompose [and] P0; clear P0.
    rewrite H10 Z_of_nat_Zabs_nat //; exact: min_u2Z.
  + assoc_tac_m.put_in_front t1.
    apply (fwd_sim_stren _ (fun _ _ _ => Z_of_nat k < 2 ^^ 31)).
      move=> st s h H.
      rewrite /uv_bound in H.
      decompose [and] H; clear H; subst k.
      rewrite Z_of_nat_Zabs_nat //; exact: min_u2Z.
    apply pfwd_sim_fwd_sim; last first.
      apply multi_halve_s_safe_termination2.
      by Uniq_uniq r0.
    apply pfwd_sim_halve_s.
    * by Uniq_uniq r0.
    * by Disj_mints_regs.
    * by Notin_dom.
    * by Notin_cdom.
  + apply fwd_sim_seq with (fun _ _ _h => Z_of_nat k < 2 ^^ 31) => //.
    * assoc_tac_m.put_in_front t2.
      apply pfwd_sim_fwd_sim; last first.
        apply (safe_termination_pull_out _ (Z_of_nat k < 2 ^^ 31)) => //; first by intuition.
        move=> Hk.
        set st_s_h := state_mint _.
        apply safe_termination_stren with st_s_h; first by intuition.
        apply multi_halve_s_safe_termination => //; by Uniq_uniq r0.
      apply pfwd_sim_halve_s.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_cdom.
    * assoc_tac_m.put_in_front t3.
      apply pfwd_sim_fwd_sim; last first.
        apply (safe_termination_pull_out _ (Z_of_nat k < 2 ^^ 31)) => //; first by intuition.
        move=> Hk.
        set st_s_h := state_mint _.
        apply safe_termination_stren with st_s_h; first by intuition.
        apply multi_halve_s_safe_termination => //; by Uniq_uniq r0.
      apply pfwd_sim_halve_s.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_cdom.
- apply fwd_sim_seq with (fun st s h => [ rk ]_ s <> zero32 /\
    u2Z ([ rk ]_ s) < 2 ^^ 31 /\ k = Z.abs_nat (u2Z ([ rk ]_ s)) /\
    Z.abs ([ t2]_ st)%pseudo_expr < \B^(k - 1) /\
    0 <= ([ u ]_ st)%pseudo_expr < \B^(k - 1))%asm_expr => //.
  + rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
    Rewrite_reg rk s.
    rewrite /uv_bound in Hcond.
    split.
      move=> abs; rewrite abs Z2uK // in Hcond; omega.
    repeat (split; first tauto).
    rewrite /EGCD.ti_bounds in Hcond.
    Rewrite_var t2 st.
    rewrite Zabs_non_eq; last omega.
    Rewrite_var u st. by ssromega.
  + apply fwd_sim_pcode_equiv with (t1 <- var_e t1 \+ var_e v ; t1 <- var_e t1 ./e nat_e 2)%pseudo_expr%pseudo_cmd; last by apply equiv_pcode_example; Uniq_neq.
    apply fwd_sim_seq with (fun _ _ _ => Z_of_nat k < 2 ^^ 31) => //.
    * rewrite /rela_hoare => st s h P0 st' exec_pseudo s' h' exec_asm.
      rewrite /uv_bound in P0.
      decompose [and] P0; clear P0.
      rewrite H10 Z_of_nat_Zabs_nat //; by apply min_u2Z.
    * assoc_tac_m.put_in_front v.
      assoc_tac_m.put_in_front t1.
      apply pfwd_sim_fwd_sim; last first.
        eapply safe_termination_stren; last first.
          apply (safe_termination_multi_add_s_u t1 v k).
          - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
          - by Uniq_uniq r0.
        move=> st s h [] st_s_h H.
        split; first by apply st_s_h.
        decompose [and] H; clear H.
        rewrite /uv_bound in H5.
        case: H5 => Hrk [Hk _].
        split; first by assumption.
        rewrite Hk Z_of_nat_Zabs_nat //; exact: min_u2Z.
      apply (pfwd_sim_stren _ (fun st s _ => [ rk ]_ s <> zero32 /\
        u2Z ([ rk ]_ s) < 2 ^^ 31 /\ k = Z.abs_nat (u2Z ([ rk ]_ s)) /\
        Z.abs ([ t1 ]_ st)%pseudo_expr < \B^(k - 1) /\
        0 <= ([ v ]_ st)%pseudo_expr < \B^(k - 1))%asm_expr).
        move=> st s h H.
        rewrite /uv_bound in H.
        split.
          move=> abs; rewrite abs Z2uK // in H; omega.
        repeat (split; first by tauto).
        rewrite /EGCD.ti_bounds in H.
        rewrite Z.abs_eq; ssromega.
      apply pfwd_sim_multi_add_s_u_wo_overflow.
      - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_cdom.
      - by Notin_cdom.
    * assoc_tac_m.put_in_front t1.
      apply pfwd_sim_fwd_sim; last first.
        apply (safe_termination_pull_out _ (Z_of_nat k < 2 ^^ 31)) => //; first by intuition.
        move=> Hk.
        set st_s_h := state_mint _.
        apply safe_termination_stren with st_s_h; first by intuition.
        apply multi_halve_s_safe_termination => //; by Uniq_uniq r0.
      apply pfwd_sim_halve_s.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_cdom.
    * apply fwd_sim_seq with (fun _ _ _ => Z_of_nat k < 2 ^^ 31) => //.
      - rewrite /rela_hoare => st s h P0 st' exec_pseudo s' h' exec_asm.
        decompose [and] P0; clear P0.
        rewrite H0 Z_of_nat_Zabs_nat //; exact: min_u2Z.
      - apply fwd_sim_pcode_equiv with (t2 <- var_e t2 \- var_e u ; t2 <- var_e t2 ./e nat_e 2)%pseudo_expr%pseudo_cmd; last by apply equiv_pcode_example; Uniq_neq.
        apply fwd_sim_seq with (fun _ _ _ => Z_of_nat k < 2 ^^ 31) => //.
        + rewrite /rela_hoare => st s h P0 st' exec_pseudo s' h' exec_asm.
          decompose [and] P0; clear P0; subst k.
          rewrite Z_of_nat_Zabs_nat //; exact: min_u2Z.
        + assoc_tac_m.put_in_front u.
          assoc_tac_m.put_in_front t2.
          apply pfwd_sim_fwd_sim; last first.
            eapply safe_termination_stren; last first.
              apply (safe_termination_multi_sub_s_u u t2 k).
             - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
             - by Uniq_uniq r0.
            move=> st s h [] st_s_h H.
            split; first exact: st_s_h.
            case: H => rk0 [rk231 [Hk [Ht2 Hu]]].
            split; first by [].
            rewrite Hk Z_of_nat_Zabs_nat //; last exact: min_u2Z.
            split; last by [].
            rewrite ltZ_neqAle; split; last exact: min_u2Z.
            contradict rk0.
            rewrite (_ : 0 = u2Z zero32) in rk0; last by rewrite Z2uK.
            by move/u2Z_inj in rk0.
          apply pfwd_sim_multi_sub_s_u_wo_overflow.
          * rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
          * by Uniq_uniq r0.
          * by Disj_mints_regs.
          * by Notin_dom.
          * by Notin_dom.
          * by Notin_cdom.
          * by Notin_cdom.
        + assoc_tac_m.put_in_front t2.
          apply pfwd_sim_fwd_sim; last first.
            apply (safe_termination_pull_out _ (Z_of_nat k < 2 ^^ 31)) => //; first by intuition.
            move=> Hk.
            set st_s_h := state_mint _.
            apply safe_termination_stren with st_s_h; first by intuition.
            apply multi_halve_s_safe_termination => //; by Uniq_uniq r0.
          apply pfwd_sim_halve_s.
          * by Uniq_uniq r0.
          * by Disj_mints_regs.
          * by Notin_dom.
          * by Notin_cdom.
      - assoc_tac_m.put_in_front t3.
          apply pfwd_sim_fwd_sim; last first.
            apply (safe_termination_pull_out _ (Z_of_nat k < 2 ^^ 31)) => //; first by intuition.
            move=> Hk.
            set st_s_h := state_mint _.
            apply safe_termination_stren with st_s_h; first by intuition.
            apply multi_halve_s_safe_termination => //; by Uniq_uniq r0.
        apply pfwd_sim_halve_s.
        + by Uniq_uniq r0.
        + by Disj_mints_regs.
        + by Notin_dom.
        + by Notin_cdom.
Qed.

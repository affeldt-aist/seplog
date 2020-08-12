(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrnat_ext ssrZ ZArith_ext seq_ext machine_int multi_int.
Require Import encode_decode integral_type uniq_tac.
Import MachineInt.
Require Import mips_bipl mips_cmd mips_tactics mips_syntax.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.

Require Import pick_sign_prg pick_sign_simu multi_negate_simu.
Require Import multi_negate_prg multi_negate_safe_termination.
Require Import multi_sub_s_s_u_prg multi_sub_s_s_u_simu multi_sub_s_s_u_safe_termination.
Require Import multi_add_s_s_u_prg multi_add_s_s_u_simu multi_add_s_s_u_safe_termination.
Require Import copy_s_s_prg copy_s_s_simu copy_s_s_safe_termination .
Require Import multi_sub_s_s_s_prg.
Require Import begcd begcd_mips0.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope heap_scope.
Local Open Scope uniq_scope.
Local Open Scope assoc_scope.
Local Open Scope simu_scope.

Definition reset_mips rk ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 a7 :=
  (pick_sign rt3 a0 a1;
  If_bgez a1 Then
   (copy_s_s rk ru1 rt1 a0 a1 a2 a3 a4 ;
    copy_s_s rk ru2 rt2 a0 a1 a2 a3 a4 ;
    copy_s_s rk ru3 rt3 a0 a1 a2 a3 a4)
  Else
  ((multi_sub_s_s_u rk rv1 rt1 rv a0 a1 a2 a3 a4 a5 a6 a7 ;
    multi_negate rv1 a0) ;
   (multi_add_s_s_u rk rv2 rt2 ru a0 a1 a2 a3 a4 a5 a6 a7 ;
    multi_negate rv2 a0) ;
   copy_s_s rk rv3 rt3 a0 a1 a2 a3 a4 ;
   multi_negate rv3 a0
  ))%mips_cmd.

Lemma fwd_sim_begcd_reset vu vv g u v u1 u2 u3 v1 v2 v3 t1 t2 t3 k
  rk rg ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 a7 :
  uniq(g,u,v,u1,u2,u3,v1,v2,v3,t1,t2,t3) ->
  uniq(rk,rg,ru,rv,ru1,ru2,ru3,rv1,rv2,rv3,rt1,rt2,rt3,a0,a1,a2,a3,a4,a5,a6,a7,r0) ->
  0 < vu -> 0 < vv ->
  (EGCD.BEGCD_TAOCP.reset u v u1 u2 u3 v1 v2 v3 t1 t2 t3)
    <=( state_mint
          (g |=> unsign rk rg \U+ (u |=> unsign rk ru \U+ (v |=> unsign rk rv \U+
          (u1 |=> signed k ru1 \U+ (u2 |=> signed k ru2 \U+ (u3 |=> signed k ru3 \U+
          (v1 |=> signed k rv1 \U+ (v2 |=> signed k rv2 \U+ (v3 |=> signed k rv3 \U+
          (t1 |=> signed k rt1 \U+ (t2 |=> signed k rt2 \U+  t3 |=> signed k rt3))))))))))),
        (fun st s _ => (EGCD.C2 vu vv u v g st /\
                        (Zodd ([u ]_ st) \/ Zodd ([v ]_ st)) /\
                        EGCD.CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 st /\
                        EGCD.C4 u3 v3 t3 st /\ EGCD.C5 u3 v3 st /\
                        gcdZ vu vv = ([ g ]_ st) * gcdZ ([ u3 ]_ st) ([ v3 ]_ st) /\
                        EGCD.uivi_bounds u v u1 v1 u2 v2 u3 v3 st /\
                        EGCD.ti_bounds u v t1 t2 t3 st /\ Zodd ([ t3 ]_ st)) /\
                       uv_bound rk s u v st k)%pseudo_expr )
  reset_mips rk ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 a7.
Proof.
move=> Hvars Hregs Hvu Hvv.
rewrite /EGCD.BEGCD_TAOCP.reset /reset_mips.
apply fwd_sim_ifte_spec => //.
- rewrite /invariant => st s h st_s_h s' h' exec_asm; split.
  + eapply state_mint_invariant; [idtac | idtac | apply st_s_h | apply exec_asm] => //.
    rewrite [mips_frame.modified_regs _]/=.
    by Disj_mints_regs.
  + rewrite /uv_bound. Rewrite_reg rk s. tauto.
- assoc_tac_m.put_in_front t3.
  apply fwd_sim_b_pick_sign; by Uniq_uniq r0.
- apply fwd_sim_seq with (fun _ s _ => k = '|u2Z ([rk ]_ s)%asm_expr|) => //.
  + rewrite /rela_hoare => st s h HP st' exec_pseudo s' h' exec_asm.
    rewrite /uv_bound in HP.
    Rewrite_reg rk s. tauto.
  + assoc_tac_m.put_in_front t1.
    assoc_tac_m.put_in_front u1.
    apply pfwd_sim_fwd_sim; last first.
      eapply safe_termination_stren; last first.
        apply (safe_termination_copy_s_s u1 t1).
        rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
        by Uniq_uniq r0.
      move=> st s h [] st_s_h H.
      split; first by apply st_s_h.
      rewrite /uv_bound in H; tauto.
    apply (pfwd_sim_stren _ (fun _ s _ => k = Z.abs_nat (u2Z ([rk ]_ s)%asm_expr))).
      move=> st s _ [] [] _.
      rewrite /uv_bound; tauto.
    apply pfwd_sim_copy_s_s.
    * rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
    * by Uniq_uniq r0.
    * by Disj_mints_regs.
    * by Notin_dom.
    * by Notin_dom.
    * by Notin_cdom.
    * by Notin_cdom.
  + apply fwd_sim_seq with (fun _ s _ => k = Z.abs_nat (u2Z ([rk ]_ s)%asm_expr)) => //.
    * rewrite /rela_hoare => st s h HP st' exec_pseudo s' h' exec_asm.
      Rewrite_reg rk s. tauto.
    * assoc_tac_m.put_in_front t2.
      assoc_tac_m.put_in_front u2.
      apply pfwd_sim_fwd_sim; last first.
        eapply safe_termination_stren; last first.
          apply (safe_termination_copy_s_s u2 t2).
          rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
          by Uniq_uniq r0.
        move=> st s h [] st_s_h H.
        split; first by apply st_s_h.
        rewrite /uv_bound in H; tauto.
      apply (pfwd_sim_stren _ (fun _ s _ => k = Z.abs_nat (u2Z ([ rk ]_ s)%asm_expr))); first done.
      apply pfwd_sim_copy_s_s.
      - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_cdom.
      - by Notin_cdom.
    * assoc_tac_m.put_in_front t3.
      assoc_tac_m.put_in_front u3.
      apply pfwd_sim_fwd_sim; last first.
        eapply safe_termination_stren; last first.
          apply (safe_termination_copy_s_s u3 t3).
          rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
          by Uniq_uniq r0.
        move=> st s h [] st_s_h H.
        split; first by apply st_s_h.
        rewrite /uv_bound in H; tauto.
      apply (pfwd_sim_stren _ (fun st s h => k = Z.abs_nat (u2Z ([rk ]_ s)%asm_expr))); first done.
      apply pfwd_sim_copy_s_s.
      - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_cdom.
      - by Notin_cdom.
- apply fwd_sim_seq with (fun st s h => ([rk ]_ s)%asm_expr <> zero32 /\
   u2Z ([ rk ]_ s)%asm_expr < 2 ^^ 31 /\ k = Z.abs_nat (u2Z ([ rk ]_ s)%asm_expr) /\
   Z.abs ([ t2 ]_ st)%pseudo_expr < \B^(k - 1) /\ 0 <= ([ u ]_ st)%pseudo_expr < \B^(k - 1)) => //.
  + rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
    Rewrite_reg rk s.
    rewrite /uv_bound in Hcond.
    split.
      move=> abs; rewrite abs Z2uK // in Hcond; lia.
    repeat (split; first tauto).
    rewrite /EGCD.ti_bounds in Hcond.
    Rewrite_var t2 st.
    rewrite Zabs_non_eq; last lia.
    Rewrite_var u st; ssromega.
  + apply fwd_sim_pcode_equiv with (v1 <- var_e t1 \- var_e v ; v1 <- .--e var_e v1)%pseudo_expr%pseudo_cmd; last first.
      apply equiv_pcode_trans with (v1 <- .--e (var_e t1 \- var_e v))%pseudo_expr%pseudo_cmd.
      by apply equiv_pcode_example3.
      apply equiv_pcode_expr => s; rewrite /= /ZIT.sub; ring.
    apply fwd_sim_seq with (fun _ _ _ => 0 < Z_of_nat k < 2 ^^ 31) => //.
    * rewrite /rela_hoare => st s h P1 st' exec_pseudo s' h' exec_asm.
      case: P1 => [] [] _ [] P1 [] P2 _ _.
      rewrite P2 Z_of_nat_Zabs_nat //; exact: min_u2Z.
    * assoc_tac_m.put_in_front v.
      assoc_tac_m.put_in_front t1.
      assoc_tac_m.put_in_front v1.
      apply pfwd_sim_fwd_sim; last first.
        eapply safe_termination_stren; last first.
          eapply (safe_termination_multi_sub_s_s_u v1 t1 v _ k).
          rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
          by Uniq_uniq r0.
        move=> st s h [] st_s_h H.
        split; first by apply st_s_h.
        rewrite /uv_bound in H.
        case: H => [[_ [H [Hk _]]] _].
        rewrite Hk Z_of_nat_Zabs_nat //; exact: min_u2Z.
      apply (pfwd_sim_stren _ (fun st s _ => [rk ]_ s <> zero32 /\
        u2Z ([ rk ]_ s) < 2 ^^ 31 /\ k = Z.abs_nat (u2Z ([ rk ]_ s)) /\
        Z.abs ([ t1 ]_ st)%pseudo_expr < \B^(k - 1) /\
        0 <= ([ v ]_ st)%pseudo_expr < \B^(k - 1))%asm_expr).
        move=> st s h H.
        rewrite /uv_bound in H.
        split.
          move=> abs; rewrite abs Z2uK // in H; lia.
        repeat (split; first by tauto).
        rewrite /EGCD.ti_bounds in H.
        rewrite Z.abs_eq; ssromega.
      apply pfwd_sim_multi_sub_s_s_u_wo_overflow.
      - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_cdom.
      - by Notin_cdom.
      - by Notin_cdom.
    * assoc_tac_m.put_in_front v1.
      apply pfwd_sim_fwd_sim_spec; last by apply multi_negate_safe_termination; Uniq_uniq r0.
      apply pfwd_sim_multi_negate.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_cdom.
  + apply fwd_sim_seq with (fun st s _ => 0 < Z_of_nat k < 2 ^^ 31 /\
      k = Z.abs_nat (u2Z ([ rk ]_ s)%asm_expr)) => //.
    * rewrite /rela_hoare => st s h P1 st' exec_pseudo s' h' exec_asm.
      case: P1 => P1 [] P2 [] P3 _.
      Rewrite_reg rk s.
      rewrite P3 Z_of_nat_Zabs_nat; last exact: min_u2Z.
      split; last by [].
      split; last by [].
      rewrite ltZ_neqAle; split; last exact: min_u2Z.
      contradict P1.
      rewrite (_ : 0 = u2Z zero32) in P1; last by rewrite Z2uK.
      by move/u2Z_inj : P1.
    * apply fwd_sim_pcode_equiv with (v2 <- var_e t2 \+ var_e u ; v2 <- .--e var_e v2)%pseudo_expr%pseudo_cmd; last first.
        apply equiv_pcode_trans with (v2 <- var_e u \+ var_e t2 ; v2 <- .--e var_e v2)%pseudo_expr%pseudo_cmd.
        apply equiv_pcode_seq; last by done.
        apply equiv_pcode_expr => s /=; by rewrite ZIT.addC.
        by apply equiv_pcode_example3.
      apply fwd_sim_seq with (fun _ _ _=> 0 < Z_of_nat k < 2 ^^ 31) => //.
      - rewrite /rela_hoare => st s h P1 st' exec_pseudo s' h' exec_asm.
        case: P1 => P1 [] P2 [] P3 _.
        rewrite P3 Z_of_nat_Zabs_nat; last exact: min_u2Z.
        split => //.
        rewrite ltZ_neqAle; split; last exact: min_u2Z.
        contradict P1.
        rewrite (_ : 0 = u2Z zero32) in P1; last by rewrite Z2uK.
        by move/u2Z_inj : P1.
      - assoc_tac_m.put_in_front u.
        assoc_tac_m.put_in_front t2.
        assoc_tac_m.put_in_front v2.
        apply pfwd_sim_fwd_sim; last first.
          eapply safe_termination_stren; last first.
            apply (safe_termination_multi_add_s_s_u v2 t2 u).
            rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
            by Uniq_uniq r0.
          move=> st s h [] st_s_h H.
          split; first exact: st_s_h.
          split; first tauto.
          case: H => H1 [] H2 [] H3 [] H4 H5.
          rewrite H3 Z_of_nat_Zabs_nat; last exact: min_u2Z.
          split; last by [].
          rewrite ltZ_neqAle; split; last exact: min_u2Z.
          contradict H1.
          apply u2Z_inj; by rewrite -H1 Z2uK.
        apply pfwd_sim_multi_add_s_s_u_wo_overflow.
        + rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
        + by Uniq_uniq r0.
        + by Disj_mints_regs.
        + by Notin_dom.
        + by Notin_dom.
        + by Notin_dom.
        + by Notin_cdom.
        + by Notin_cdom.
        + by Notin_cdom.
      - assoc_tac_m.put_in_front v2.
        apply pfwd_sim_fwd_sim_spec; last by apply multi_negate_safe_termination; Uniq_uniq r0.
        apply pfwd_sim_multi_negate.
        + by Uniq_uniq r0.
        + by Disj_mints_regs.
        + by Notin_dom.
        + by Notin_cdom.
    * apply fwd_sim_pcode_equiv with (v3 <- var_e t3 ; v3 <- .--e var_e v3)%pseudo_expr%pseudo_cmd; last first.
        by apply equiv_pcode_example3.
      apply fwd_sim_seq with (fun st s _ => 0 < Z_of_nat k < 2 ^^ 31 /\
        k = Z.abs_nat (u2Z ([rk ]_ s)%asm_expr)) => //.
      - rewrite /rela_hoare => st s h P1 st' exec_pseudo s' h' exec_asm.
        Rewrite_reg rk s. by [].
      - assoc_tac_m.put_in_front t3.
        assoc_tac_m.put_in_front v3.
        apply pfwd_sim_fwd_sim; last first.
          eapply safe_termination_stren; last first.
            apply (safe_termination_copy_s_s v3 t3).
            rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
            by Uniq_uniq r0.
          move=> st s h [] st_s_h H.
          split; first by apply st_s_h.
          rewrite /uv_bound in H; tauto.
        apply (pfwd_sim_stren _ (fun _ s _ => k = '|u2Z ([rk ]_ s)%asm_expr|)).
          move=> st s _ [] [] _.
          rewrite /uv_bound. tauto.
        apply pfwd_sim_copy_s_s.
        + rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
        + by Uniq_uniq r0.
        + by Disj_mints_regs.
        + by Notin_dom.
        + by Notin_dom.
        + by Notin_cdom.
        + by Notin_cdom.
      - assoc_tac_m.put_in_front v3.
        apply pfwd_sim_fwd_sim_spec; last by apply multi_negate_safe_termination; Uniq_uniq r0.
        apply (pfwd_sim_stren _ (fun _ _ _ => 0 < Z_of_nat k < 2 ^^ 31)); first by intuition.
        apply pfwd_sim_multi_negate.
        + by Uniq_uniq r0.
        + by Disj_mints_regs.
        + by Notin_dom.
        + by Notin_cdom.
Qed.

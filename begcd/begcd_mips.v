(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrnat_ext ssrZ ZArith_ext seq_ext machine_int multi_int.
Require Import encode_decode integral_type uniq_tac.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.

Require Import multi_one_u_prg multi_one_u_simu multi_one_u_safe_termination.
Require Import multi_negate_prg pick_sign_prg pick_sign_simu.
Require Import multi_is_even_s_prg multi_is_even_s_simu.
Require Import begcd_mips_prelude begcd_mips_init begcd_mips_halve begcd_mips_reset begcd_mips_subtract.
Require Import begcd begcd_mips0.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope simu_scope.

Definition begcd_mips rk rg ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3
  a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 :=
  (multi_one_u rk rg a0 a1 ;
  prelude_mips rk rg ru rv a0 a1 a2 a3 ;
  init_mips rk ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 ;
  pick_sign rt3 a0 a1 ;
  While (bne a1 r0) {{
  ((multi_is_even_s rt3 a0 a1 a2 ;
    While (bne a2 r0) {{
      halve_mips rk ru rv rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6;
      multi_is_even_s rt3 a0 a1 a2 }}) ;
    reset_mips rk ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a7 a8 a9 ;
    subtract_mips rk ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 a7 a8);
    pick_sign rt3 a0 a1 }}
)%mips_cmd.

Lemma fwd_sim_begcd vu vv g u v u1 u2 u3 v1 v2 v3 t1 t2 t3 k
  rk rg ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) ->
  uniq(rk, rg, ru, rv, ru1, ru2, ru3, rv1, rv2, rv3, rt1, rt2, rt3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, r0) ->
  0 < vu -> 0 < vv -> vu < Zbeta k -> vv < Zbeta k ->
  EGCD.BEGCD_TAOCP.begcd g u v u1 u2 u3 v1 v2 v3 t1 t2 t3
    <=( state_mint (g |=> unsign rk rg \U+ (u |=> unsign rk ru \U+ (v |=> unsign rk rv \U+
                   (u1 |=> signed k ru1 \U+ (u2 |=> signed k ru2 \U+ (u3 |=> signed k ru3 \U+
                   (v1 |=> signed k rv1 \U+ (v2 |=> signed k rv2 \U+ (v3 |=> signed k rv3 \U+
                   (t1 |=> signed k rt1 \U+ (t2 |=> signed k rt2 \U+ t3 |=> signed k rt3))))))))))),
        (fun st s h => EGCD.uv_init vu vv u v st /\ uv_bound rk s u v st k)%pseudo_expr)
  begcd_mips rk rg ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9.
Proof.
move=> Hvars Hregs Hvu Hvv vu_max vv_max.
rewrite /EGCD.BEGCD_TAOCP.begcd /begcd_mips.
(** g <- snat 1 *)
apply fwd_sim_seq with (fun st s _ => EGCD.C1 vu vv u v g st /\ uv_bound rk s u v st k) => //.
- rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm; split.
  + rewrite /EGCD.C1.
    rewrite /EGCD.uv_init in Hcond *.
    move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
    case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
    repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
    tauto.
  + rewrite /uv_bound.
    repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
    Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st.
    rewrite /uv_bound in Hcond; tauto.
- set st_s_h := state_mint _.
  apply pfwd_sim_fwd_sim; last first.
    apply safe_termination_stren with (fun st s h => st_s_h st s h /\
      (0 < '|u2Z ([rk ]_ s)%asm_expr|)%nat); last first.
      by apply safe_termination_one_u; Uniq_uniq r0.
    move=> st s h [] Hst_s_h [] _ [] [] H _ _.
    split=> //; exact/O_lt_Zabs_nat.
  rewrite /pfwd_sim => st s h Hst_s_h.
  apply pfwd_sim_one_u.
  + by Uniq_uniq r0.
  + by Disj_mints_regs.
  + by Notin_dom.
  + by Notin_cdom.
  + split; first tauto.
    case: Hst_s_h => _.
    rewrite /EGCD.uv_init /uv_bound => ?; tauto.
(** EGCD.prelude u v g *)
- apply fwd_sim_stren with (fun st s _ => EGCD.C2 vu vv u v g st /\ uv_bound rk s u v st k).
    move=> st s h.
    rewrite /EGCD.C1 /EGCD.C2 /EGCD.uv_init.
    move=> [[[Hu Hv] Hg] Hcond].
    by rewrite Hu Hv Hg !mulZ1.
  apply fwd_sim_seq with (fun st s _ => (EGCD.C2 vu vv u v g st /\ EGCD.C3 vu vv u v g st) /\
    uv_bound rk s u v st k) => //.
  + rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
    split.
      have Htmp : uniq(u,v,g) by rewrite [Equality.sort _]/= in Hvars *; Uniq_uniq O.
      move: (EGCD.BEGCD_TAOCP_FUN_COR.prelude_triple_strict _ _ _ _ _ Htmp Hvu Hvv) => {Htmp}.
      move/syntax_m.seplog_m.hoare_prop_m.soundness.
      rewrite /while.hoare_semantics.
      case/(_ st syntax_m.seplog_m.assert_m.heap.emp (proj1 Hcond)) => _.
      case/(_ _ _ exec_pseudo) => HC2 Hb.
      split; first by [].
      rewrite /EGCD.C3.
      split; last exact/negP.
      rewrite /EGCD.C2 in HC2.
      case: HC2 => Hu [Hv [Hg [u_g v_g]]].
      rewrite -Zgcd_mult; last omega.
      by rewrite mulZC u_g mulZC v_g.
    rewrite /uv_bound in Hcond *.
    Rewrite_reg rk s.
    repeat (split; first tauto).
    rewrite /EGCD.prelude in exec_pseudo.
    split.
    * have Hu0 : 0 < ([ u ]_ st)%pseudo_expr < Zbeta (k - 1) by tauto.
      apply (syntax_m.seplog_m.semop_prop_m.while_preserves _ _
        (fun st => 0 < ([u ]_ st)%pseudo_expr < Zbeta (k - 1)) _ _ _ _ Hu0 exec_pseudo) => {Hu0} s0 h0 s'0 h'0 Hu0 while_cond.
      case/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_seq_inv_Some.
      move=> [s1 h1] [Hs1 Hs'0].
      Rewrite_var u s1.
      move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : Hs1.
      case/syntax_m.seplog_m.exec0_assign_inv => ? ?; subst h1 s1.
      syntax_m.seplog_m.assert_m.expr_m.Store_upd.
      rewrite /= /ZIT.div; split.
      - apply Zlt_0_Zdiv => //.
        case/andP : while_cond => while_cond _.
        move/eqP : while_cond => /Zmod_2_Zeven.
        case/Zeven_ex => uhalf Huhalf.
        by rewrite [LHS]/= in Huhalf; omega.
      - apply (@leZ_ltZ_trans ([u]_s0)%pseudo_expr); last by tauto.
        apply Zdiv_le_upper_bound => //; omega.
    * have Hv0 : 0 < ([v ]_ st)%pseudo_expr < Zbeta (k - 1) by tauto.
      apply (syntax_m.seplog_m.semop_prop_m.while_preserves _ _ (fun st => 0 < ([v ]_ st)%pseudo_expr < Zbeta (k - 1)) _ _ _ _ Hv0 exec_pseudo) => {Hv0} s0 h0 s'0 h'0 Hv0 while_cond.
      move/syntax_m.seplog_m.semop_prop_m.exec_seq_assoc'.
      case/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_seq_inv_Some.
      move=> [s1 h1] [Hs1 Hs0].
      Rewrite_var v s1.
      case/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_seq_inv_Some : Hs1.
      move=> [s2 h2] [Hs2 Hs1].
      move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : Hs1.
      case/syntax_m.seplog_m.exec0_assign_inv => ? ?; subst h1 s1.
      syntax_m.seplog_m.assert_m.expr_m.Store_upd.
      rewrite /= /ZIT.div.
      Rewrite_var v s0.
      split.
      - apply Zlt_0_Zdiv => //.
        case/andP : while_cond => _.
        move/eqP/Zmod_2_Zeven.
        case/Zeven_ex => uhalf Huhalf.
        rewrite [LHS]/= in Huhalf; omega.
      - apply (@leZ_ltZ_trans ([v]_s0)%pseudo_expr); last tauto.
        apply Zdiv_le_upper_bound => //; omega.
  + eapply fwd_sim_stren; last first.
      apply sim_begcd_prelude.
      by rewrite [Equality.sort _]/= in Hvars *; Uniq_uniq O.
      by Uniq_uniq r0.
    move=> st s h [HC2 Hcond] /=.
    rewrite /EGCD.C2 in HC2.
    rewrite /uv_bound in Hcond.
    decompose [and] Hcond; clear Hcond.
    subst k.
    split; last omega.
    case: HC2 => Hu [Hv [Hg [u_g v_g]]].
    by rewrite u_g.
  (** EGCD.init u v u1 u2 u3 v1 v2 v3 t1 t2 t3 *)
  + apply fwd_sim_seq with (fun st s _ => EGCD.C2 vu vv u v g st /\ EGCD.C3 vu vv u v g st /\
      EGCD.uivi_init u v u1 u2 u3 v1 v2 v3 st /\ EGCD.ti_init u v t1 t2 t3 st /\
      uv_bound rk s u v st k) => //.
    * rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
      move: (EGCD.BEGCD_TAOCP_FUN_COR.triple_init _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvars Hvu Hvv).
      move/syntax_m.seplog_m.hoare_prop_m.soundness.
      rewrite /while.hoare_semantics.
      move/(_ _ _ (proj1 Hcond)).
      move/(_ syntax_m.seplog_m.assert_m.heap.emp).
      case=> _.
      move/(_ _ _ exec_pseudo) => Hcond'.
      repeat (split; first tauto).
      rewrite /uv_bound.
      Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
    * apply fwd_sim_begcd_init => //; by Uniq_uniq r0.
    (** While (var_e t3 \!= nat_e 0) {{ *)
    * apply fwd_sim_stren with (fun st s _ => (EGCD.C2 vu vv u v g st /\
        (Zodd [u ]_ st \/ Zodd [v ]_ st) /\
        EGCD.CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 st /\
        EGCD.C4 u3 v3 t3 st /\ EGCD.C5 u3 v3 st /\
        gcdZ [u ]_ st [v ]_ st = gcdZ [u3 ]_ st [v3 ]_ st /\
        EGCD.uivi_bounds u v u1 v1 u2 v2 u3 v3 st /\ EGCD.ti_bounds u v t1 t2 t3 st) /\
        uv_bound rk s u v st k)%pseudo_expr.
        move=> st s h; split.
        - apply EGCD.BEGCD_TAOCP_COR.triple_intermediate_invariant_stren => //.
          exact syntax_m.seplog_m.assert_m.heap.emp.
          repeat (split; first tauto).
          rewrite /EGCD.C2 in H; apply EGCD.init_bounds; tauto.
        - tauto.
      apply fwd_sim_while => //.
      - rewrite /invariant => st s h [st_s_h Hcond] s' h' exec_asm; split.
        + eapply state_mint_invariant; [idtac | idtac | apply st_s_h | apply exec_asm] => //.
          rewrite [mips_frame.modified_regs _]/=.
          by Disj_mints_regs.
        + rewrite /uv_bound.
          Rewrite_reg rk s. tauto.
      - rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm; split.
        + move: (EGCD.BEGCD_TAOCP_COR.triple_intermediate_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvars Hvu Hvv).
          move/syntax_m.seplog_m.hoare_prop_m.soundness.
          rewrite /while.hoare_semantics.
          move/(_ st syntax_m.seplog_m.assert_m.heap.emp).
          set tmp := (_ /\ _).
          have Htmp : tmp by rewrite {}/tmp; tauto.
          case/(_ Htmp) => {Htmp} _.
          move/(_ _ _ exec_pseudo); tauto.
        + rewrite /uv_bound.
          Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
      - assoc_tac_m.put_in_front t3.
        eapply fwd_sim_b_stren; last first.
          apply fwd_sim_b_pick_sign_bne.
          by Uniq_uniq r0.
        move=> st s ? [] H _; exact: H.
      - apply fwd_sim_seq with (fun st s _ => (EGCD.C2 vu vv u v g st /\
          (Zodd [u ]_ st \/ Zodd [v ]_ st) /\
          EGCD.CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 st /\
          EGCD.C4 u3 v3 t3 st /\ EGCD.C5 u3 v3 st /\
          gcdZ vu vv = [g ]_ st * gcdZ [u3 ]_ st [v3 ]_ st /\
          EGCD.uivi_bounds u v u1 v1 u2 v2 u3 v3 st /\
          EGCD.ti_bounds u v t1 t2 t3 st /\ Zodd [t3 ]_ st) /\ uv_bound rk s u v st k)%pseudo_expr => //.
        + rewrite /rela_hoare => st s h Hcond st' exec_p s' h' exec_c; split.
          * move: (EGCD.BEGCD_TAOCP_COR.while_halve _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvars Hvu Hvv).
            move/syntax_m.seplog_m.hoare_prop_m.soundness.
            rewrite /while.hoare_semantics /=.
            move/(_ st syntax_m.seplog_m.assert_m.heap.emp).
            set tmp := (_ /\ _).
            have Htmp : tmp by rewrite {}/tmp; tauto.
            case/(_ Htmp) => {Htmp} _.
            move/(_ _ _ exec_p); tauto.
          * rewrite /uv_bound.
            Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
        + apply fwd_sim_stren with (fun st s _ => ((EGCD.C2 vu vv u v g st /\
            (Zodd ([u ]_ st) \/ Zodd ([v ]_ st)) /\
            EGCD.CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 st /\
            EGCD.C4 u3 v3 t3 st /\ EGCD.C5 u3 v3 st /\
            gcdZ ([u ]_ st) ([v ]_ st) = gcdZ ([u3 ]_ st) ([v3 ]_ st) /\
            EGCD.uivi_bounds u v u1 v1 u2 v2 u3 v3 st /\
            EGCD.ti_bounds u v t1 t2 t3 st) /\ uv_bound rk s u v st k) /\
           ([var_e t3 \!= nat_e 0 ]b_ st))%pseudo_expr.
            move=> st s h; tauto.
          apply fwd_sim_while => //.
          * rewrite /invariant.
            move=> st s h [st_s_h Hcond] s' h' exec_asm; split.
            - eapply state_mint_invariant; [idtac | idtac | apply st_s_h | apply exec_asm] => //.
              rewrite [mips_frame.modified_regs _]/=.
              by Disj_mints_regs.
            - rewrite /uv_bound.
              Rewrite_reg rk s. tauto.
          * rewrite /rela_hoare => st s h Hcond st' exec_p s' h' exec_c.
            move: (EGCD.BEGCD_TAOCP_COR.while_halve_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvars Hvu Hvv).
            move/syntax_m.seplog_m.hoare_prop_m.soundness.
            rewrite /while.hoare_semantics /=.
            move/(_ st syntax_m.seplog_m.assert_m.heap.emp).
            set tmp := (_ /\ _).
            have Htmp : tmp.
              rewrite /tmp {tmp}.
              split.
              - repeat (split; first by tauto).
                have {}Hcond : ([var_e t3 \!= nat_e 0 ]b_ st)%pseudo_expr by tauto.
                rewrite /= in Hcond.
                by move/eqP : Hcond.
              - tauto.
            case/(_ Htmp) => {Htmp} _.
            move/(_ _ _ exec_p) => Htmp.
            split.
              split.
              - tauto.
              - rewrite /uv_bound.
                Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
            apply/eqP; tauto.
          * assoc_tac_m.put_in_front t3.
            apply fwd_sim_b_pull_out with (0 < Z_of_nat k < 2 ^^ 31).
              move=> st s h H.
              decompose [and] H; clear H.
              clear -H4.
              rewrite /uv_bound in H4.
              decompose [and] H4; clear H4.
              rewrite H Z_of_nat_Zabs_nat //; exact: min_u2Z.
            move=> Zk.
            set st_s_h := state_mint _.
            apply fwd_sim_b_stren with st_s_h; last first.
              apply fwd_sim_b_multi_is_even_s.
              by Uniq_uniq r0.
              exact: Zk.
            move=> st s ? [] H _; exact: H.
          * apply fwd_sim_stren with (fun st s _ => (((EGCD.C2 vu vv u v g st /\
              (Zodd ([u ]_ st) \/ Zodd ([v ]_ st)) /\
              EGCD.CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 st /\
              EGCD.C4 u3 v3 t3 st /\ EGCD.C5 u3 v3 st /\
              gcdZ ([u ]_ st) ([v ]_ st) = gcdZ ([u3 ]_ st) ([v3 ]_ st) /\
              EGCD.uivi_bounds u v u1 v1 u2 v2 u3 v3 st /\
              EGCD.ti_bounds u v t1 t2 t3 st) /\ uv_bound rk s u v st k) /\
             ([var_e t3 \!= nat_e 0 ]b_ st)) /\
             ([var_e t3 \% nat_e 2 \= nat_e 0 ]b_ st))%pseudo_expr.
              move=> st s _; tauto.
            apply fwd_sim_begcd_halve => //; by Uniq_uniq r0.
        + apply fwd_sim_seq with (fun st s _ => (EGCD.C2 vu vv u v g st /\
            (Zodd [u ]_ st \/ Zodd [v ]_ st) /\
            EGCD.CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 st /\
            (0 <= [t3 ]_ st ->
              gcdZ vu vv = [g ]_ st * gcdZ [t3 ]_ st [v3 ]_ st /\
              Zodd [u3 ]_ st /\ [u3 ]_ st = [t3 ]_ st) /\
            ([t3 ]_ st < 0 ->
              gcdZ vu vv = [g ]_ st * gcdZ [u3 ]_ st [t3 ]_ st /\
              Zodd [v3 ]_ st /\ [v3 ]_ st = - [t3 ]_ st) /\
            EGCD.uivi_bounds u v u1 v1 u2 v2 u3 v3 st /\
            EGCD.ti_bounds u v t1 t2 t3 st /\ EGCD.C5 u3 v3 st) /\
            uv_bound rk s u v st k)%pseudo_expr => //.
          * rewrite /rela_hoare => st s h Hcond st' exec_p s' h' exec_c; split.
            + move: (EGCD.BEGCD_TAOCP_COR.reset_triple _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvars Hvu Hvv).
              move/syntax_m.seplog_m.hoare_prop_m.soundness.
              rewrite /while.hoare_semantics /=.
              move/(_ st syntax_m.seplog_m.assert_m.heap.emp).
              set tmp := (_ /\ _).
              have Htmp : tmp.
                rewrite /tmp {tmp}.
                tauto.
              case/(_ Htmp) => {Htmp} _.
              move/(_ _ _ exec_p) => Htmp.
              tauto.
            + rewrite /uv_bound.
              Rewrite_reg rk s. Rewrite_var u st. Rewrite_var v st. tauto.
          * apply fwd_sim_begcd_reset => //; by Uniq_uniq r0.
          * apply fwd_sim_begcd_subtract => //; by Uniq_uniq r0.
Qed.

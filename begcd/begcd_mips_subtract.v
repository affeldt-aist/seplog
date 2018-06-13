(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ssrnat_ext ZArith_ext seq_ext machine_int multi_int.
Require Import encode_decode integral_type uniq_tac.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.

Require Import pick_sign_prg pick_sign_simu.
Require Import multi_add_s_u_prg multi_add_s_u_simu multi_add_s_u_safe_termination.
Require Import multi_sub_s_u_prg multi_sub_s_u_simu multi_sub_s_u_safe_termination.
Require Import multi_sub_s_s_s_prg multi_sub_s_s_s_safe_termination multi_sub_s_s_s_simu.
Require Import begcd begcd_mips0.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope simu_scope.

Definition subtract_mips rk ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ((multi_sub_s_s_s rk rt1 ru1 rv1 a0 a1 a2 a3 a4 a5 a6 a7 a8 ;
    multi_sub_s_s_s rk rt2 ru2 rv2 a0 a1 a2 a3 a4 a5 a6 a7 a8 ;
    multi_sub_s_s_s rk rt3 ru3 rv3 a0 a1 a2 a3 a4 a5 a6 a7 a8);
   (pick_sign rt1 a0 a1;
    If_blez a1 Then
     (multi_add_s_u rk rt1 rv a0 a1 a2 a3 a4 a5 a6 ;
      multi_sub_s_u rk rt2 ru a0 a1 a2 a3 a4 a5 a6)
    Else
      nop))%mips_cmd.

Lemma fwd_sim_begcd_subtract vu vv g u v u1 u2 u3 v1 v2 v3 t1 t2 t3 k
  rk rg ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 a7 a8 :
  uniq(g,u,v,u1,u2,u3,v1,v2,v3,t1,t2,t3) ->
  uniq(rk,rg,ru,rv,ru1,ru2,ru3,rv1,rv2,rv3,rt1,rt2,rt3,a0,a1,a2,a3,a4,a5,a6,a7,a8,r0) ->
  0 < vu -> 0 < vv ->
  (EGCD.BEGCD_TAOCP.subtract u v u1 u2 u3 v1 v2 v3 t1 t2 t3)
    <=( state_mint
           (g |=> unsign rk rg \U+ (u |=> unsign rk ru \U+ (v |=> unsign rk rv \U+
           (u1 |=> signed k ru1 \U+ (u2 |=> signed k ru2 \U+ (u3 |=> signed k ru3 \U+
           (v1 |=> signed k rv1 \U+ (v2 |=> signed k rv2 \U+ (v3 |=> signed k rv3 \U+
           (t1 |=> signed k rt1 \U+ (t2 |=> signed k rt2 \U+ t3 |=> signed k rt3))))))))))),
        (fun st s _ => (EGCD.C2 vu vv u v g st /\
                        (Zodd ([ u ]_ st) \/ Zodd ([ v ]_ st)) /\
                        EGCD.CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 st /\
                        (0 <= [ t3 ]_ st ->
                         gcdZ vu vv = ([ g ]_ st) * gcdZ ([ t3 ]_ st) ([v3 ]_ st) /\
                         Zodd ([ u3 ]_ st) /\ [ u3 ]_ st = [ t3 ]_ st) /\
                        ([t3 ]_ st < 0 ->
                         gcdZ vu vv = ([ g ]_ st) * gcdZ ([ u3 ]_ st) ([ t3 ]_ st) /\
                         Zodd ([ v3 ]_ st) /\
                         [ v3 ]_ st = - [t3 ]_ st) /\
                        EGCD.uivi_bounds u v u1 v1 u2 v2 u3 v3 st /\
                        EGCD.ti_bounds u v t1 t2 t3 st /\ EGCD.C5 u3 v3 st) /\
                       uv_bound rk s u v st k)%pseudo_expr )
  subtract_mips rk ru rv ru1 ru2 ru3 rv1 rv2 rv3 rt1 rt2 rt3 a0 a1 a2 a3 a4 a5 a6 a7 a8.
Proof.
move=> Hvars Hregs Hvu Hvv.
rewrite /EGCD.BEGCD_TAOCP.subtract /subtract_mips.
apply fwd_sim_seq with (fun st s _ => uv_bound rk s u v st k /\
  ([ t1 ]_ st <= 0 -> 0 <= [ t1 ]_ st + [ v ]_ st <= [ v ]_ st /\
    - [u ]_ st <= [ t2 ]_ st - [ u ]_ st <= 0))%pseudo_expr => //.
- rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
  rewrite /uv_bound.
  Rewrite_reg rk s.
  rewrite /uv_bound in Hcond.
  split.
    Rewrite_var u st. Rewrite_var v st. tauto.
  move/syntax_m.seplog_m.hoare_prop_m.soundness :
    (EGCD.BEGCD_TAOCP_COR.subtract_part1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvars Hvu Hvv).
  rewrite /while.hoare_semantics.
  case/( _ _ syntax_m.seplog_m.assert_m.heap.emp (proj1 Hcond)) => _.
  move/(_ _ _ exec_pseudo) => H Ht1; tauto.
- apply fwd_sim_seq with (fun st s _ => [rk ]_ s <> zero32 /\
    u2Z ([ rk ]_ s) < 2 ^^ 31 /\ k = Z.abs_nat (u2Z ([rk ]_ s)) /\
    Z.abs ([ u2 ]_ st)%pseudo_expr < \B^(k - 1) /\
    Z.abs ([ v2 ]_ st)%pseudo_expr < \B^(k - 1) /\
    Z.abs ([ u3 ]_ st)%pseudo_expr < \B^(k - 1) /\
    Z.abs ([ v3 ]_ st)%pseudo_expr < \B^(k - 1))%asm_expr => //.
  + rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
    Rewrite_reg rk s.
    rewrite /uv_bound in Hcond.
    split.
      move=> abs; rewrite abs Z2uK // in Hcond; omega.
    repeat (split; first by tauto).
    rewrite /EGCD.uivi_bounds in Hcond.
    Rewrite_var u2 st. Rewrite_var v2 st. Rewrite_var u3 st. Rewrite_var v3 st.
    rewrite Zabs_non_eq; last omega.
    rewrite Zabs_non_eq; last omega.
    rewrite Z.abs_eq; last omega.
    rewrite Z.abs_eq; ssromega.
  + apply (fwd_sim_stren _ (fun st s _ => [ rk ]_ s <> zero32 /\
       u2Z ([ rk ]_ s) < 2 ^^ 31 /\ k = Z.abs_nat (u2Z ([rk ]_ s)) /\
       Z.abs ([ u1 ]_ st)%pseudo_expr < \B^(k - 1) /\
       Z.abs ([ v1 ]_ st)%pseudo_expr < \B^(k - 1))%asm_expr).
      move=> st s h H.
      rewrite /uv_bound in H.
      split.
        move=> abs; rewrite abs Z2uK // in H; omega.
      repeat (split; first by tauto).
      rewrite /EGCD.uivi_bounds in H.
      rewrite Z.abs_eq; last omega.
      rewrite Z.abs_eq; ssromega.
    assoc_tac_m.put_in_front v1.
    assoc_tac_m.put_in_front u1.
    assoc_tac_m.put_in_front t1.
    apply pfwd_sim_fwd_sim; last first.
      eapply safe_termination_stren; last first.
        eapply (safe_termination_multi_sub_s_s_s t1 u1 v1 _ k).
        - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
        - by Uniq_uniq r0.
      move=> st s h [] st_s_h [rk0 [rk231 [Hk [Hu1 Hv1]]]].
      split; first by apply st_s_h.
      split; first by assumption.
      rewrite Hk Z_of_nat_Zabs_nat; last by apply min_u2Z.
      split; last by assumption.
      apply/ltZP; rewrite ltZ_neqAle.
      apply/andP; split; last by apply/leZP/min_u2Z.
      rewrite -(@Z2uK 0 32) //.
      apply/eqP => /u2Z_inj; by auto.
    apply pfwd_sim_multi_sub_s_s_s_wo_overflow.
    * rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
    * by Uniq_uniq r0.
    * by Disj_mints_regs.
    * by Notin_dom.
    * by Notin_dom.
    * by Notin_dom.
    * by Notin_cdom.
    * by Notin_cdom.
    * by Notin_cdom.
  + apply fwd_sim_seq with (fun st s _ => [rk ]_ s <> zero32 /\
       u2Z ([ rk ]_ s) < 2 ^^ 31 /\ k = Z.abs_nat (u2Z ([rk ]_ s)) /\
       Z.abs ([ u3 ]_ st)%pseudo_expr < \B^(k - 1) /\
       Z.abs ([ v3 ]_ st)%pseudo_expr < \B^(k - 1))%asm_expr => //.
    * rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
      Rewrite_reg rk s.
      rewrite /uv_bound in Hcond.
      split.
        move=> abs; rewrite abs Z2uK // in Hcond; tauto.
      repeat (split; first by tauto).
      rewrite /EGCD.uivi_bounds in Hcond.
      Rewrite_var u3 st. Rewrite_var v3 st. tauto.
    * apply (fwd_sim_stren _ (fun st s _ => ([ rk ]_ s)%asm_expr <> zero32 /\
          u2Z ([ rk ]_ s)%asm_expr < 2 ^^ 31 /\ k = Z.abs_nat (u2Z ([ rk ]_ s)%asm_expr) /\
          Z.abs ([ u2 ]_ st)%pseudo_expr < \B^(k - 1) /\
          Z.abs ([ v2 ]_ st)%pseudo_expr < \B^(k - 1))).
        move=> *; tauto.
      assoc_tac_m.put_in_front v2.
      assoc_tac_m.put_in_front u2.
      assoc_tac_m.put_in_front t2.
      apply pfwd_sim_fwd_sim; last first.
        eapply safe_termination_stren; last first.
          eapply (safe_termination_multi_sub_s_s_s t2 u2 v2 _ k).
          - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
          - by Uniq_uniq r0.
        move=> st s h [] st_s_h [rk0 [rk231 [Hk [Hu1 Hv1]]]].
        split; first exact:st_s_h.
        split; first assumption.
        rewrite Hk Z_of_nat_Zabs_nat; last exact: min_u2Z.
        split; last assumption.
        apply/ltZP; rewrite ltZ_neqAle.
        apply/andP; split; last by apply/leZP/min_u2Z.
        rewrite -(@Z2uK 0 32) //.
        apply/eqP => /u2Z_inj; by auto.
      apply pfwd_sim_multi_sub_s_s_s_wo_overflow.
      - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_cdom.
      - by Notin_cdom.
      - by Notin_cdom.
    * assoc_tac_m.put_in_front v3.
      assoc_tac_m.put_in_front u3.
      assoc_tac_m.put_in_front t3.
      apply pfwd_sim_fwd_sim; last first.
        eapply safe_termination_stren; last first.
          eapply (safe_termination_multi_sub_s_s_s t3 u3 v3 _ k).
          - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
          - by Uniq_uniq r0.
        move=> st s h [] st_s_h [rk0 [rk231 [Hk [Hu1 Hv1]]]].
        split; first by apply st_s_h.
        split; first by assumption.
        rewrite Hk Z_of_nat_Zabs_nat; last exact: min_u2Z.
        split; last by assumption.
        apply/ltZP; rewrite ltZ_neqAle.
        apply/andP; split; last by apply/leZP/min_u2Z.
        rewrite -(@Z2uK 0 32) //.
        apply/eqP => /u2Z_inj; by auto.
      apply pfwd_sim_multi_sub_s_s_s_wo_overflow.
      - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_cdom.
      - by Notin_cdom.
      - by Notin_cdom.
- apply fwd_sim_ifte_spec => //.
  + rewrite /invariant => st s h [st_s_h Hcond] s' h' exec_asm; split.
    + eapply state_mint_invariant; [idtac | idtac | apply st_s_h | apply exec_asm] => //.
      rewrite [mips_frame.modified_regs _]/=.
      by Disj_mints_regs.
    + rewrite /uv_bound.
      Rewrite_reg rk s. tauto.
  + assoc_tac_m.put_in_front t1.
    apply fwd_sim_b_pick_sign_lez; by Uniq_uniq r0.
  + apply fwd_sim_seq with (fun st s _ =>  [ rk ]_ s <> zero32 /\
       u2Z ([ rk ]_ s) < 2 ^^ 31 /\ k = Z.abs_nat (u2Z ([ rk ]_ s)) /\
       Z.abs ([ t2 ]_ st)%pseudo_expr < \B^(k - 1) /\
       0 <= ([ u ]_ st)%pseudo_expr < \B^(k - 1))%asm_expr => //.
    * rewrite /rela_hoare => st s h Hcond st' exec_pseudo s' h' exec_asm.
      rewrite /uv_bound.
      Rewrite_reg rk s.
      rewrite /uv_bound in Hcond.
      split.
        move=> abs; rewrite abs Z2uK // in Hcond; omega.
      Rewrite_var t2 st. Rewrite_var u st.
      repeat (split; first tauto).
      case: Hcond => Hcond [_] /=.
      move/geZP.
      rewrite /= in Hcond => H.
      rewrite Z.abs_eq; ssromega.
    * apply (fwd_sim_stren _ (fun st s _ => [rk ]_ s <> zero32 /\
        u2Z ([rk ]_ s) < 2 ^^ 31 /\ k = Z.abs_nat (u2Z ([ rk ]_ s)) /\
        Z.abs ([ t1 ]_ st)%pseudo_expr < \B^(k - 1) /\
        0 <= ([ v ]_ st)%pseudo_expr < \B^(k - 1))%asm_expr).
        move=> st s h H.
        rewrite /uv_bound in H.
        split.
          move=> abs; rewrite abs Z2uK // in H; omega.
        repeat (split; first by tauto).
        rewrite Zabs_non_eq; last first.
          case: H => _ [_] /=; by move/geZP/Zge_le.
        ssromega.
      assoc_tac_m.put_in_front v.
      assoc_tac_m.put_in_front t1.
      apply pfwd_sim_fwd_sim; last first.
        eapply safe_termination_stren; last first.
          apply (safe_termination_multi_add_s_u t1 v k).
          - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
          - by Uniq_uniq r0.
        move=> st s h [] st_s_h [rk0 [rk231 [Hk [Ht1 Hv]]]].
        split; first by apply st_s_h.
        split; first by assumption.
        rewrite Hk Z_of_nat_Zabs_nat; last by apply min_u2Z.
        split; last by assumption.
        apply/ltZP; rewrite ltZ_neqAle.
        apply/andP; split; last exact/leZP/min_u2Z.
        rewrite -(@Z2uK 0 32) //.
        apply/eqP => /u2Z_inj; by auto.
      apply pfwd_sim_multi_add_s_u_wo_overflow.
      - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_cdom.
      - by Notin_cdom.
    * assoc_tac_m.put_in_front u.
      assoc_tac_m.put_in_front t2.
      apply pfwd_sim_fwd_sim; last first.
        eapply safe_termination_stren; last first.
          apply (safe_termination_multi_sub_s_u u t2 k).
          - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
          - by Uniq_uniq r0.
         move=> st s h [] st_s_h H.
         split; first by apply st_s_h.
         case: H => rk0 [rk231 [Hk [Ht2 Hu]]].
         split; first by [].
         rewrite Hk Z_of_nat_Zabs_nat; last exact: min_u2Z.
         split; last by [].
         apply/ltZP; rewrite ltZ_neqAle.
         apply/andP; split; last exact/leZP/min_u2Z.
         rewrite -(@Z2uK 0 32) //.
         apply/eqP => /u2Z_inj; by auto.
      apply pfwd_sim_multi_sub_s_u_wo_overflow.
      - rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq O.
      - by Uniq_uniq r0.
      - by Disj_mints_regs.
      - by Notin_dom.
      - by Notin_dom.
      - by Notin_cdom.
      - by Notin_cdom.
  + by apply fwd_sim_nop.
Qed.

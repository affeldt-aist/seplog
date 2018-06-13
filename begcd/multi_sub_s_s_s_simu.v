(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext machine_int uniq_tac.
Require Import multi_int integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_mint mips_frame.
Import expr_m.
Require Import simu.
Import simu_m.
Require Import multi_sub_s_s_s_prg multi_sub_s_s_s_triple.

Local Open Scope machine_int_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope heap_scope.
Local Open Scope asm_cmd_scope.
Local Open Scope simu_scope.
Local Open Scope multi_int_scope.

Import assert_m.

(** z <- x - y, z, x, y signed *)

Lemma pfwd_sim_multi_sub_s_s_s_wo_overflow (z x y : assoc.l)
  d k rk rz rx ry a0 a1 a2 a3 a4 ret rX rY rZ :
  uniq(z, x, y) ->
  uniq(rk, rz, rx, ry, a0, a1, a2, a3, a4, ret, rX, rY, rZ, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: a2 :: a3 :: a4 :: ret :: rX :: rY :: rZ :: nil) ->
  z \notin assoc.dom d -> x \notin assoc.dom d -> y \notin assoc.dom d ->
  signed k rz \notin assoc.cdom d -> signed k rx \notin assoc.cdom d -> signed k ry \notin assoc.cdom d ->
  (z <- (var_e x \- var_e y)%pseudo_expr)%pseudo_cmd
    <=p( state_mint (z |=> signed k rz \U+ (x |=> signed k rx \U+ (y |=> signed k ry \U+ d))),
         (fun s st _ => [rk ]_ st <> zero32 /\
                        u2Z ([rk ]_ st) < 2 ^^ 31 /\
                        k = '|u2Z ([rk ]_ st)| /\
                        `| ([x ]_ s)%pseudo_expr | < \B^(k - 1) /\
                        `| ([y ]_ s)%pseudo_expr | < \B^(k - 1))%asm_expr )
  multi_sub_s_s_s rk rz rx ry a0 a1 a2 a3 a4 ret rX rY rZ.
Proof.
move=> Hvars Hregs Hdisj z_d x_d y_d rz_d rx_d ry_d.
rewrite /pfwd_sim => s st h [s_st_h [rk_0 [rk_231 [Hk [x_fit y_fit]]]]] s' exec_pseudo st' h' exec_asm.

move: (proj1 s_st_h z (signed k rz)).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => lz pz Z rz_fit [Z_k lz_k lz_z z_Z] pz_fit mem_z.

move: (proj1 s_st_h x (signed k rx)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => lx px X rx_fit [X_k lx_k lx_x x_X] px_fit mem_x.

move: (proj1 s_st_h y (signed k ry)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => ly py Y ry_fit [Y_k ly_k ly_y y_Y] py_fit mem_y.

have Htmp : 0 < Z_of_nat k < 2 ^^ 31.
  rewrite Hk Z_of_nat_Zabs_nat; last exact/min_u2Z.
  split => //.
  apply Zle_neq_lt.
  by apply min_u2Z.
  contradict rk_0.
  by apply u2Z_inj; rewrite -rk_0 Z2uK.
move/multi_sub_s_s_s_triple : (Hregs).
move/(_ k [rx]_st [ry]_st [rz]_st px py pz Htmp px_fit py_fit pz_fit X Y Z
  X_k Y_k Z_k lx ly lz lx_k ly_k lz_k) => {Htmp}.
rewrite -x_X -y_Y -z_Z.
move/(_ lx_x ly_y lz_z) => hoare_triple.

have [st'' [h'' exec_asm_proj]] : exists st'' h'',
  (Some (st, h |P| heap.dom (heap_mint (signed k rz) st h \U
    heap_mint (signed k rx) st h \U heap_mint (signed k ry) st h))
    -- multi_sub_s_s_s rk rz rx ry a0 a1 a2 a3 a4 ret rX rY rZ --->
    Some (st'', h''))%mips_cmd.
  exists st', (h' |P| heap.dom (heap_mint (signed k rz) st h \U
    heap_mint (signed k rx) st h \U heap_mint (signed k ry) st h)).
  rewrite conCE in hoare_triple.
  rewrite [in X in ({{ _ }} _ {{ X }} )%asm_hoare]conCE in hoare_triple.
  apply (mips_syntax.triple_exec_proj _ _ _ hoare_triple) => {hoare_triple} //.
  repeat (split; first by reflexivity).
  split.
    rewrite Hk Z_of_nat_Zabs_nat //; exact/min_u2Z.
  rewrite conCE.
  rewrite -conAE.
  rewrite heap.proj_dom_union; last first.
    apply heap.disjUh.
    apply (proj2 s_st_h z y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
    apply (proj2 s_st_h x y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  apply con_cons.
    apply heap.dis_disj_proj.
    rewrite -heap.disjE.
    apply heap.disjUh.
    apply (proj2 s_st_h z y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
    apply (proj2 s_st_h x y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  rewrite heap.proj_dom_union; last first.
    apply (proj2 s_st_h z x); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  apply con_cons.
    apply heap.dis_disj_proj.
    rewrite -heap.disjE.
    apply (proj2 s_st_h z x); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  move: (heap_inclu_heap_mint_signed h st k rz).
  by move/heap.incluE => ->.
  move: (heap_inclu_heap_mint_signed h st k rx).
  by move/heap.incluE => ->.
  move: (heap_inclu_heap_mint_signed h st k ry).
  by move/heap.incluE => ->.

set postcond := (fun s h => exists _, _)%asm_assert in hoare_triple.
have {hoare_triple}hoare_triple_post_cond : (postcond ** TT)%asm_assert st' h'.
  move: {hoare_triple}(mips_frame.frame_rule_R _ _ _ hoare_triple TT (inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
    move/mips_seplog.hoare_prop_m.soundness.
    rewrite /while.hoare_semantics.
    move/(_ st h) => Hmulti_sub_s_s_s.
    lapply Hmulti_sub_s_s_s; last first.
      exists (heap_mint (signed k rz) st h \U heap_mint (signed k rx) st h \U heap_mint (signed k ry) st h),
       (h \D\ heap.dom (heap_mint (signed k rz) st h \U heap_mint (signed k rx) st h \Uheap_mint (signed k ry) st h)).
      split; first by apply heap.disj_difs', seq_ext.inc_refl.
      split.
        apply heap.union_difsK; last by [].
        apply heap_prop_m.inclu_union.
        apply heap_prop_m.inclu_union; by [apply heap_inclu_heap_mint_signed | apply heap.inclu_proj].
        by apply heap_inclu_heap_mint_signed.
      split; last by [].
      repeat (split=> //).
      rewrite Hk Z_of_nat_Zabs_nat //; exact/min_u2Z.
      rewrite -conAE.
      apply con_cons => //.
      + apply heap.disjUh.
        apply (proj2 s_st_h z y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
        apply (proj2 s_st_h x y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
      + apply con_cons => //.
        apply (proj2 s_st_h z x); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
    case=> _.
    by move/(_ _ _ exec_asm).

have rz_st_st' : [ rz ]_ st = [ rz ]_ st'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
have rx_st_st' : [ rx ]_ st = [ rx ]_ st'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
have ry_st_st' : [ ry ]_ st = [ ry ]_ st'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
have rk_st_st' : [ rk ]_ st = [ rk ]_ st'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.

split.
- move=> x0 mx0 x0_mx0.
  case/assoc.get_union_Some_inv : x0_mx0.
  + case/assoc.get_sing_inv => ? ?; subst x0 mx0.
    case: hoare_triple_post_cond => h1 [h2 [h1dh2 [h1Uh2 [Hh1 _]]]].
    case: Hh1 => Z' [lz' [Z'_k [lz'_k [lz'_x_y [Hh1 [Ha3 Z'_x_y]]]]]].
        have Hk' : k <> O.
          move=> abs.
          rewrite Hk in abs.
          move: abs.
          contradict rk_0.
          apply Zabs_nat_0_inv in rk_0.
          rewrite (_ : 0 = u2Z zero32) in rk_0; last by rewrite Z2uK.
          by move/u2Z_inj : rk_0.
    apply mkVarSigned with lz' pz Z' => //.
    * by rewrite -rz_st_st'.
    * apply mkSignMagn => //.
      - rewrite lz'_k Zsgn_Zmult ZsgnK.
        have -> : sgZ (Z_of_nat k) = 1.
          apply Z.sgn_pos.
          rewrite Hk Z_of_nat_Zabs_nat; last exact/min_u2Z.
          apply Zle_neq_lt.
          exact/min_u2Z.
          contradict rk_0.
          apply u2Z_inj.
          by rewrite -rk_0 Z2uK.
        rewrite mulZ1.
        move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
        repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        by rewrite lz'_x_y.
      - move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
        case/syntax_m.seplog_m.exec0_assign_inv => _ ->.
        repeat syntax_m.seplog_m.assert_m.expr_m.Store_upd.
        + case: (Z_zerop (s2Z lz')) => lz'_neq0.
            by rewrite lz'_neq0 /= /ZIT.sub /= -Z'_x_y lz'_neq0.
          have {Ha3}Ha3 : u2Z [a3]_st' = 0.
            have Htmp : `|u2Z [a3 ]_ st' * \B^k + \S_{ k } Z'| < \B^k.
              apply Zabs_Zsgn_1 in lz'_neq0.
              rewrite -[X in X < _]Zmult_1_l -lz'_neq0 -Z.abs_mul addZC Z'_x_y.
              apply: leZ_ltZ_trans; first exact: Z.abs_triangle.
              apply (@ltZ_leZ_trans (\B^(k - 1) + \B^(k - 1))).
              apply ltZ_add => //; by rewrite Z.abs_opp.
              apply/leZP; rewrite /Zbeta Zpower_plus Zpower_2_le; ssromega.
            eapply poly_Zlt1_Zabs_inv; last exact/Htmp.
            exact: min_lSum.
            exact: min_u2Z.
            by [].
          rewrite /= /ZIT.sub -Z'_x_y Ha3; ring.
    * case: Hh1 => h11 [h12 [h11dh12 [h11Uh12 [Hh11 Hh12]]]].
       apply con_heap_mint_signed_cons with h11 => //.
      - rewrite h1Uh2.
        apply heap.inclu_union_L => //.
        rewrite h11Uh12.
        apply heap.inclu_union_L => //.
        exact: heap.inclu_refl.
      - by rewrite -rz_st_st'.
      - by rewrite Z'_k.
  + move=> x0_mx0.
    have x0z : x0 <> z.
      move=> ?; subst x0.
      case/assoc.get_union_Some_inv : x0_mx0.
        case/assoc.get_sing_inv => abs _; move: abs.
        rewrite -/(z <> x); by Uniq_neq.
      case/assoc.get_union_Some_inv.
        case/assoc.get_sing_inv => abs _; move: abs.
        rewrite -/(z <> y); by Uniq_neq.
      move/assoc.get_Some_in_dom => abs; by rewrite abs in z_d.

have Hd_unchanged : forall v r, assoc.get v d = Some r ->
  disj (mint_regs r) (mips_frame.modified_regs (multi_sub_s_s_s rk rz rx ry a0 a1 a2 a3 a4 ret rX rY rZ)).
  move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
  apply (disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
  apply/incP/inc_mint_regs.
  by move/assoc.get_Some_in_cdom : Hvr.

    apply var_mint_invariant with s st.
    - move=> rx0 Hrx0.
      mips_syntax.Reg_unchanged.
      apply (@disj_not_In _ (mint_regs mx0)); last by [].
      case/assoc.get_union_Some_inv : x0_mx0.
        case/assoc.get_sing_inv => ? ?; subst x0 mx0.
        simpl mint_regs. simpl modified_regs. Disj_remove_dup. simpl. apply uniq_disj.
        simpl cat. by Uniq_uniq r0.
      case/assoc.get_union_Some_inv.
        case/assoc.get_sing_inv => ? ?; subst x0 mx0.
        simpl mint_regs. simpl modified_regs. Disj_remove_dup. simpl. apply uniq_disj.
        simpl cat. by Uniq_uniq r0.
      move=> x0_mx0.
      by apply disj_sym, (Hd_unchanged x0).
    - Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    - suff -> : heap_mint mx0 st' h' = heap_mint mx0 st h.
        apply (proj1 s_st_h); by rewrite assoc.get_union_sing_neq.
      symmetry.
      case: hoare_triple_post_cond => h1 [h2 [h1dh2 [h1Uh2 [Hh1 _]]]].
      case: Hh1 => Z' [lz' [Z'_k [lz'_k [sgn_lz' [Hh1 [Ha3 HSum]]]]]].
      case: Hh1 => h11 [h12 [h11dh12 [h11Uh12 [Hh11 Hh12]]]].
      case: Hh12 => h121 [h122 [h121dh122 [h121Uh122 [Hh121 Hh122]]]].
      case/assoc.get_union_Some_inv : (x0_mx0).
        case/assoc.get_sing_inv => ? ?; subst x0 mx0.
        have Htmp : (strictly_exact (var_e%asm_expr rx |--> lx :: px ::nil ** int_e px |--> X))%asm_assert.
          apply strictly_exact_con; by apply strictly_exact_mapstos.
        apply: Htmp (conj mem_x _).
        suff : (var_e%asm_expr rx |--> lx :: px :: nil ** int_e px |--> X)%asm_assert st'
          (heap_mint (signed k rx) st' h').
          apply monotony => ?; by apply mapstos_ext.
        apply con_heap_mint_signed_cons with h121 => //.
        rewrite h1Uh2 h11Uh12 h121Uh122.
        apply heap.inclu_union_L; first by map_tac_m.Disj.
        apply heap.inclu_union_R; first by map_tac_m.Disj.
        apply heap.inclu_union_L.
        assumption.
        by apply heap.inclu_refl.
        by rewrite -rx_st_st'.
        by rewrite X_k.
      case/assoc.get_union_Some_inv.
        case/assoc.get_sing_inv => ? ?; subst x0 mx0.
        have Htmp : (strictly_exact (var_e%asm_expr ry |--> ly :: py ::nil ** int_e py |--> Y))%asm_assert.
          apply strictly_exact_con; by apply strictly_exact_mapstos.
        apply: Htmp (conj mem_y _).
        suff : (var_e%asm_expr ry |--> ly :: py :: nil ** int_e py |--> Y)%asm_assert st'
          (heap_mint (signed k ry) st' h').
          apply monotony => ?; by apply mapstos_ext.
        apply con_heap_mint_signed_cons with h122 => //.
        rewrite h1Uh2 h11Uh12 h121Uh122.
        apply heap.inclu_union_L; first by map_tac_m.Disj.
        apply heap.inclu_union_R; first by map_tac_m.Disj.
        apply heap.inclu_union_R.
        assumption.
        exact/heap.inclu_refl.
        by rewrite -ry_st_st'.
        by rewrite Y_k.
      move=> x0_d_mx0.
      apply (heap_mint_state_invariant (heap_mint (signed k rz) st h \U
        heap_mint (signed k rx) st h \U heap_mint (signed k ry) st h) x0 s) => //.
      + move=> x1 Hx1.
        mips_syntax.Reg_unchanged.
        apply (@disj_not_In _ (mint_regs mx0)); last by [].
        exact/disj_sym/(Hd_unchanged x0).
      + apply (proj1 s_st_h).
        rewrite assoc.get_union_sing_neq //; by auto.
      + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ exec_asm_proj).
        tauto.
      + apply heap.disjhU.
        * apply heap.disjhU.
          - apply (proj2 s_st_h x0 z) => //.
            rewrite assoc.get_union_sing_neq //; by auto.
            by assoc_get_Some.
          - case/orP : (orbN (x0 == x)).
            + move/eqP => ?; subst x0.
              apply assoc.get_Some_in_dom in x0_d_mx0.
              by rewrite x0_d_mx0 in x_d.
            + move=> x0x.
              apply (proj2 s_st_h x0 x) => //.
              by apply/eqP.
              rewrite assoc.get_union_sing_neq //; by auto.
              by assoc_get_Some.
        * case/boolP : (x0 == y) => [/eqP ?|x0y].
          - subst x0.
            apply assoc.get_Some_in_dom in x0_d_mx0.
            by rewrite x0_d_mx0 in y_d.
          - apply (proj2 s_st_h x0 y) => //.
            by apply/eqP.
            rewrite assoc.get_union_sing_neq //; by auto.
            by assoc_get_Some.
- case: hoare_triple_post_cond => h1 [h2 [h1dh2 [h1Uh2 [Hh1 _]]]].
  case: Hh1 => Z' [lz' [Z'_k [lz'_k [sgn_lz' [Hh1 [Ha3 HSum]]]]]].
  case: Hh1 => h11 [h12 [h11dh12 [h11Uh12 [Hh11 Hh12]]]].
  case: Hh12 => h121 [h122 [h121dh122 [h121Uh122 [Hh121 Hh122]]]].
  apply state_mint_part2_three_variables with s st h => //.
  + symmetry.
    apply dom_heap_mint_sign_state_invariant with z s lz lz' => //.
    move/mapstos_get1 : mem_z.
    by apply heap_get_heap_mint_inv.
    move/mapstos_get1 in Hh11.
    rewrite h1Uh2 h11Uh12.
    apply heap.get_union_L.
    by map_tac_m.Disj.
    by apply heap.get_union_L.
    move/mapstos_get2 : mem_z.
    move/heap_get_heap_mint_inv => ->.
    symmetry.
    move/mapstos_get2 in Hh11.
    rewrite h1Uh2 h11Uh12.
    apply heap.get_union_L.
    by map_tac_m.Disj.
    by apply heap.get_union_L.
    apply (proj1 s_st_h z) => //.
    by assoc_get_Some.
    by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
  + symmetry.
    apply dom_heap_mint_sign_state_invariant with x s lx lx => //.
    move/mapstos_get1 : mem_x.
    by apply heap_get_heap_mint_inv.
    move/mapstos_get1 in Hh121.
    rewrite h1Uh2 h11Uh12 h121Uh122.
    apply heap.get_union_L.
    by map_tac_m.Disj.
    apply heap.get_union_R.
    by map_tac_m.Disj.
    by apply heap.get_union_L.
    move/mapstos_get2 : mem_x.
    move/heap_get_heap_mint_inv => ->.
    symmetry.
    move/mapstos_get2 in Hh121.
    rewrite h1Uh2 h11Uh12 h121Uh122.
    apply heap.get_union_L.
    by map_tac_m.Disj.
    apply heap.get_union_R.
    by map_tac_m.Disj.
    by apply heap.get_union_L.
    apply (proj1 s_st_h x) => //.
    by assoc_get_Some.
    by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
  + symmetry.
    apply dom_heap_mint_sign_state_invariant with y s ly ly => //.
    move/mapstos_get1 : mem_y.
    by apply heap_get_heap_mint_inv.
    move/mapstos_get1 in Hh122.
    rewrite h1Uh2 h11Uh12 h121Uh122.
    apply heap.get_union_L.
    by map_tac_m.Disj.
    apply heap.get_union_R.
    by map_tac_m.Disj.
    by apply heap.get_union_R.
    move/mapstos_get2 : mem_y.
    move/heap_get_heap_mint_inv => ->.
    symmetry.
    move/mapstos_get2 in Hh122.
    rewrite h1Uh2 h11Uh12 h121Uh122.
    apply heap.get_union_L.
    by map_tac_m.Disj.
    apply heap.get_union_R.
    by map_tac_m.Disj.
    by apply heap.get_union_R.
    apply (proj1 s_st_h y) => //.
    by assoc_get_Some.
    by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
  + move=> t Ht x0 Hx0.
    mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs.
    case/assoc.in_cdom_union_inv : Ht.
    * rewrite assoc.cdom_sing seq.mem_seq1.
      move/eqP=> ?; subst t.
      apply (@disj_not_In _ (mint_regs (signed k rz))); last by [].
      Disj_remove_dup.
      rewrite /=.
      apply uniq_disj. rewrite [cat _ _]/=. by Uniq_uniq r0.
    * case/assoc.in_cdom_union_inv.
      - rewrite assoc.cdom_sing seq.mem_seq1.
        move/eqP=> ?; subst t.
        apply (@disj_not_In _ (mint_regs (signed k rx))); last by [].
        Disj_remove_dup.
        rewrite /=.
        apply uniq_disj. rewrite [cat _ _]/=. by Uniq_uniq r0.
      - case/assoc.in_cdom_union_inv.
        * rewrite assoc.cdom_sing seq.mem_seq1.
          move/eqP=> ?; subst t.
          apply (@disj_not_In _ (mint_regs (signed k ry))); last by [].
          Disj_remove_dup.
          rewrite /=.
          apply uniq_disj. rewrite [cat _ _]/=. by Uniq_uniq r0.
        * move=> Ht. apply: (@disj_not_In _ (mint_regs t)); last by [].
          Disj_remove_dup.
          apply/disj_sym/(disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
          exact/incP/inc_mint_regs.
- move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ exec_asm_proj); tauto.
Qed.

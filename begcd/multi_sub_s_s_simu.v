(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int uniq_tac multi_int.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_mint.
Import expr_m.
Require Import simu.
Import simu_m.
Require Import multi_sub_s_s_prg multi_sub_s_s_triple.
From mathcomp Require Import seq.

Local Open Scope machine_int_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope heap_scope.
Local Open Scope simu_scope.
Local Open Scope multi_int_scope.

(** x <- x - y, x signed, y signed *)

Lemma pfwd_sim_multi_sub_s_s (x y : assoc.l) d k rk ry rx a0 a1 a2 a3 a4 ret rX rY :
  uniq(x, y) ->
  uniq(rk, rx, ry, a0, a1, a2, a3, a4, ret, rX, rY, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: a2 :: a3 :: a4 :: ret :: rX :: rY :: nil) ->
  x \notin assoc.dom d -> y \notin assoc.dom d ->
  signed k rx \notin assoc.cdom d -> unsign rk ry \notin assoc.cdom d ->
  (x <- var_e x \- var_e y)%pseudo_expr%pseudo_cmd
    <=p( state_mint (x |=> signed k rx \U+ (y |=> signed k ry \U+ d)),
         fun s st _ => [rk ]_ st <> zero32 /\
                        u2Z ([rk ]_ st) < 2 ^^ 31 /\
                        k = '|u2Z ([rk ]_ st)| /\
                        `|([ x ]_ s)%pseudo_expr| < \B^k /\
                        `|([ y ]_ s)%pseudo_expr| < \B^k /\
                        `|([ x ]_ s)%pseudo_expr - ([y ]_ s)%pseudo_expr| < \B^k)
  multi_sub_s_s rk rx ry a0 a1 a2 a3 a4 ret rX rY.
Proof.
move=> Hvars Hreg Hd x_d y_d rx_d ry_d.
rewrite /pfwd_sim.
move=> st s h [st_s_h [rk_s_neq0 [rk_s_max [k_rk [x_st [y_st x_y_st]]]]]] st' exec_pseudo s' h' exec_asm.
have Hd_unchanged : forall v r, assoc.get v d = Some r ->
  disj (mint_regs r) (mips_frame.modified_regs (multi_sub_s_s rk rx ry a0 a1 a2 a3 a4 ret rX rY)).
  move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
  apply (disj_incl_LR Hd); last by apply incl_refl_Permutation; PermutProve.
  apply/incP/inc_mint_regs.
  by move/assoc.get_Some_in_cdom : Hvr.
set vx := [rx ]_ s.
set vy := [ry ]_ s.
lapply (state_mint_var_mint _ _ _ _ x (signed k rx) st_s_h); [move=> var_mint_x | by assoc_get_Some].
rewrite /var_mint in var_mint_x.
case: var_mint_x => slen ptr X vx_fit [X_k Hlen Hsgn Sum_X] ptr_fit Hmem.

lapply (state_mint_var_mint _ _ _ _ y (signed k ry) st_s_h); [move=> var_mint_y | by assoc_get_Some].
rewrite /var_mint in var_mint_y.
case: var_mint_y => sleny ptry Y vy_fit [Y_k Hleny Hsgny Sum_Y] ptry_fit Hmemy.

move/multi_sub_s_s_triple : (Hreg).
move/(_ k vx vy ptr ptry).
have : k <> O.
  contradict rk_s_neq0. apply u2Z_inj. rewrite rk_s_neq0 in k_rk.
  symmetry in k_rk. apply Zabs_nat_0_inv in k_rk. by rewrite Z2uK.
let x := fresh in move=> x; move/(_ x); clear x.
have : Z<=nat k < 2 ^^ 31.
  rewrite k_rk Z_of_nat_Zabs_nat //; by apply min_u2Z.
let x := fresh in move=> x; move/(_ x); clear x.
move/(_ ptr_fit ptry_fit X Y X_k Y_k slen sleny Hlen Hleny).
rewrite -{1}Sum_X.
rewrite -{1}Sum_Y.
move/(_ Hsgn Hsgny) => Hhoare_multi_sub_s_s.

have [s'' [h'' exec_asm_proj]] : exists s'' h'',
  (Some (s, h |P| heap.dom (heap_mint (signed k ry) s h \U heap_mint (signed k rx) s h))
    -- multi_sub_s_s rk rx ry a0 a1 a2 a3 a4 ret rX rY --->
    Some (s'', h''))%mips_cmd.
  exists s', (h' |P| heap.dom (heap_mint (signed k ry) s h \U heap_mint (signed k rx) s h)).
  apply (mips_syntax.triple_exec_proj _ _ _ Hhoare_multi_sub_s_s) => {Hhoare_multi_sub_s_s} //.
  split; first by [].
  split; first by [].
  split.
    rewrite k_rk Z_of_nat_Zabs_nat //; exact: min_u2Z.
  rewrite heap.proj_dom_union; last first.
    apply (proj2 st_s_h y x); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  rewrite heap.unionC; last first.
    apply heap.dis_disj_proj.
    rewrite -heap.disjE.
    apply (proj2 st_s_h y x); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  apply assert_m.con_cons.
    apply heap.dis_disj_proj.
    rewrite -heap.disjE.
    apply (proj2 st_s_h x y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  move: (heap_inclu_heap_mint_signed h s k rx).
  move/heap.incluE => ->; exact Hmem.
  move: (heap_inclu_heap_mint_signed h s k ry).
  move/heap.incluE => ->; exact Hmemy.
have ry_s_s' : [ ry ]_ s = [ ry ]_ s'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
have rk_s_s' : [ rk ]_ s = [ rk ]_ s'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
have y_st_st' : ([ y ]_ st = [ y ]_ st')%pseudo_expr.
  Var_unchanged. simpl syntax_m.seplog_m.modified_vars.
  move/inP.
  rewrite -/(~ _).
  by Uniq_not_In.
have rx_s_s' : [ rx ]_ s = [rx ]_ s'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
set postcond := (fun s h => exists _, _) in Hhoare_multi_sub_s_s.
have {Hhoare_multi_sub_s_s}hoare_triple_post_condition : (postcond  ** assert_m.TT)%asm_assert s' h'.
    move: {Hhoare_multi_sub_s_s}(mips_frame.frame_rule_R _ _ _ Hhoare_multi_sub_s_s assert_m.TT (assert_m.inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
    move/mips_seplog.hoare_prop_m.soundness.

Notation "'hoare_semantics'" := (@while.hoare_semantics WMIPS_Hoare.store WMIPS_Hoare.heap _
WMIPS_Hoare.exec0 _ WMIPS_Hoare.eval_b) : mips_hoare_scope.

    rewrite /while.hoare_semantics.

Notation "s -- c ---> t" := (@while.exec WMIPS_Hoare.store WMIPS_Hoare.heap _ WMIPS_Hoare.exec0 _
  WMIPS_Hoare.eval_b s c t)  (at level 74, no associativity) : mips_cmd_scope.

    move/(_ s h) => Hmulti_sub_s_u.
    lapply Hmulti_sub_s_u; last first.
      exists (heap_mint (signed k rx) s h \U heap_mint (signed k ry) s h).
      exists (h \D\ heap.dom (heap_mint (signed k rx) s h \U heap_mint (signed k ry) s h)).
      split.
        exact/heap.disj_difs'/seq_ext.inc_refl.
      split.
        apply heap.union_difsK; last by [].
        apply heap_prop_m.inclu_union; by [apply heap_inclu_heap_mint_signed | apply heap.inclu_proj].
      split; last by [].
      repeat (split=> //).
      - rewrite k_rk Z_of_nat_Zabs_nat //; by apply min_u2Z.
      - apply assert_m.con_cons.
        + apply (proj2 st_s_h x y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
        + exact Hmem.
        + exact Hmemy.
    case=> _.
    by move/(_ _ _ exec_asm).
rewrite /state_mint; split.
- move=> z rz z_rz.
  have [z_d | z_x ] : z \in assoc.dom (y |=> signed k ry \U+ d) \/ z = x.
    rewrite assoc.unionC in z_rz; last first.
      apply assoc.disjhU.
      apply assoc.disj_sing; apply/eqP; by Uniq_neq.
      by apply assoc.disj_sym, assoc.disj_sing_R.
    case/assoc.get_union_Some_inv : z_rz => z_rz.
    left.
    by apply assoc.get_Some_in_dom with rz.
    case/assoc.get_sing_inv : z_rz => ? ?; subst z rz.
    by right.
  + (* NB: it is about proving that x is unchanged, which is true since
       neither y nor d are touched by execution *)
    have z_x : z <> x.
      move=> ?; subst z.
      case/assoc.in_dom_union_inv : z_d.
      * case/assoc.in_dom_get_Some => x0.
        case/assoc.get_sing_inv => x_y _.
        move: x_y.
        rewrite -/(~ _); by Uniq_neq.
      * by rewrite (negbTE x_d).
    case/orP : (orbN (z == y)) => z_y.
    (* z = y *)
    move/eqP : z_y => ?; subst z.
    rewrite assoc.unionC in z_rz; last first.
      apply assoc.disjhU.
      apply assoc.disj_sing; apply/eqP; by auto.
      by apply assoc.disj_sym, assoc.disj_sing_R.
    rewrite -assoc.unionA assoc.get_union_sing_eq in z_rz.
    case: z_rz => ?; subst rz.
    case : hoare_triple_post_condition => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
    case: Hh1 => X' [slen' Hh1].
    case: Hh1 => H [H1 [H0 [H2 [H3 H4]]]].
    case: H2 => h11 [h12 [h11_d_h12 [h11_U_h12 [Hh11 Hh12]]]].
    move: (proj1 st_s_h y (signed k ry)).
    rewrite assoc.get_union_sing_neq; last by Uniq_neq.
    rewrite assoc.get_union_sing_eq.
    move/(_ (refl_equal _)).
    move=> K.
    have <- : heap_mint (signed k ry) s h = heap_mint (signed k ry) s' h'.
      case: (Hmemy) => k1 [k2 [k1_d_k2 [k1_U_k2 [Hk1 Hk2]]]].
      rewrite k1_U_k2.

      rewrite {1}/heap_mint.
      move: (assert_m.mapstos_get1 _ _ _ _ _ _ Hh12).
      move/(heap.get_union_R _ _ h11_d_h12).
      rewrite -h11_U_h12.
      move/(heap.get_union_L _ _ h1_d_h2).
      rewrite -h1_U_h2.
      move=> ->.
      move: (assert_m.mapstos_get2 _ _ _ _ _ _ Hh12).
      move/(heap.get_union_R _ _ h11_d_h12).
      rewrite -h11_U_h12.
      move/(heap.get_union_L _ _ h1_d_h2).
      rewrite -h1_U_h2.
      move=> ->.
      cbv zeta iota beta.

      rewrite /heap_cut.
      rewrite -ry_s_s'.
      case: Hh12 => i1 [i2 [i1_d_i2 [i1_U_i2 [Hi1 Hi2]]]].
      move: (Hi1) => Hi1_save.
      apply assert_m.mapstos_inv_dom in Hi1; last first.
        by rewrite /= -ry_s_s'.
      move: (Hi2) => Hi2_save.
      apply assert_m.mapstos_inv_dom in Hi2; last by rewrite Y_k.
      rewrite ry_s_s'.
      rewrite Hi1 -Y_k.
      rewrite Hi2.
      rewrite h1_U_h2.
      rewrite h11_U_h12.
      rewrite i1_U_i2.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_R_dom; last by heap_tac_m.Disj.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_itself.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_R_dom; last by heap_tac_m.Disj.
      rewrite heap.proj_union_R_dom; last by heap_tac_m.Disj.
      rewrite heap.proj_itself.
      congr (_ \U _).
      apply: assert_m.strictly_exact_mapstos (conj Hk1 _); by apply: assert_m.mapstos_ext Hi1_save.
      apply: assert_m.strictly_exact_mapstos (conj Hk2 _); by apply: assert_m.mapstos_ext Hi2_save.
    move: K.
    by apply var_mint_invariant_signed.
    (* z <> y *)
    move: {st_s_h}(proj1 st_s_h _ _ z_rz) (proj2 st_s_h) => st_s_h1 st_s_h2.
    have z_unchanged : ( [ z ]_ st = [ z ]_st' )%pseudo_expr.
      Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    case: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm
      (heap.dom (heap_mint (signed k ry) s h \U heap_mint (signed k rx) s h)) _ _
      exec_asm_proj) => H4 [H5 H_h_h'].
    have <- : heap_mint rz s h = heap_mint rz s' h'.
      apply (heap_mint_state_invariant (heap_mint (signed k ry) s h \U
                            heap_mint (signed k rx) s h) z st) => //.
      move=> rx0 Hrx0; mips_syntax.Reg_unchanged.
      apply (@disj_not_In _ (mint_regs rz)); last by [].
      apply/disj_sym/(Hd_unchanged z).
      rewrite assoc.get_union_sing_neq in z_rz; last by [].
      rewrite assoc.get_union_sing_neq // in z_rz.
      by apply/eqP.
      apply heap.disjhU.
      apply st_s_h2 with z y => //.
      by apply/eqP.
      rewrite assoc.get_union_sing_neq; last by Uniq_neq.
      by rewrite assoc.get_union_sing_eq.
      apply st_s_h2 with z x => //.
      by rewrite assoc.get_union_sing_eq.
    move: st_s_h1; apply var_mint_invariant; last exact z_unchanged.
    move=> rx0 Hrx0; mips_syntax.Reg_unchanged.
    apply (@disj_not_In _ (mint_regs rz)); last by [].
    apply/disj_sym/(Hd_unchanged z) => //.
    rewrite assoc.get_union_sing_neq in z_rz; last by [].
    rewrite assoc.get_union_sing_neq // in z_rz.
    by apply/eqP.
  + subst z.
    have rz_rx : rz = signed k rx.
      rewrite assoc.get_union_sing_eq in z_rz; by case: z_rz.
    subst rz.
    move: (proj1 st_s_h x (signed k rx) z_rz).
    rewrite /var_mint.
    case: hoare_triple_post_condition => [h1 [h2 [Hdisj [Hunion [[X' [slen' [Hsub_s_s_1 [r_x [r_y [Hsub_s_s_2 [Hsub_s_s_3 Hsub_s_s_4]]]]]]]] HTT]]]].
    move=> K.
    have x'_x_y : ([ x ]_ st' = [ x ]_ st - [y ]_ st )%pseudo_expr.
      move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
      case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
      by syntax_m.seplog_m.assert_m.expr_m.Store_upd.
    apply (mkVarSigned _ _ _ _ _ slen' ptr X') => //.
    + by rewrite /vx -rx_s_s'.
    + apply mkSignMagn.
      * exact Hsub_s_s_1.
      * by rewrite {1}r_x.
      * by rewrite {1}r_y -Sum_X x'_x_y Sum_Y.
      * rewrite x'_x_y Sum_X Sum_Y -Hsub_s_s_4.
        case: (Z_zerop (s2Z slen')) => slen'_neq0.
          by rewrite slen'_neq0.
        have Hi : u2Z [a3 ]_ s' = 0.
          have : `|Z.sgn (s2Z slen') * (\S_{ k } X' + u2Z [a3 ]_ s' * \B^k)| < \B^k.
            by rewrite Hsub_s_s_4 -Sum_X -Sum_Y.
          rewrite Zabs_Zmult Zabs_Zsgn_1 // Zmult_1_l addZC.
          apply: poly_Zlt1_Zabs_inv => //.
          exact: min_lSum.
          exact: min_u2Z.
        rewrite Hi mul0Z addZ0 in Hsub_s_s_4.
        by rewrite Hi mul0Z addZ0.
    + case: Hsub_s_s_2 => h11 [h12 [h11_d_h12 [h11_U_h12 [Hh11 Hh12]]]].
      suff : heap_mint (signed k rx) s' h' = h11 by move=> ->.
      simpl heap_mint.
      have K1 : heap.get '|u2Z ([ rx ]_ s')%asm_expr / 4| h' = Some slen'.
        rewrite Hunion; apply heap.get_union_L => //.
        rewrite h11_U_h12; apply heap.get_union_L => //.
        by apply assert_m.mapstos_get1 in Hh11.
      have K2 : heap.get '|u2Z ([ rx ]_ s' `+ four32) / 4| h' = Some ptr.
        rewrite Hunion; apply heap.get_union_L => //.
        rewrite h11_U_h12; apply heap.get_union_L => //.
        by apply assert_m.mapstos_get2 in Hh11.
      rewrite K1 K2.
      rewrite /heap_cut.
      case: Hh11 => h111 [h112 [h111_d_h112 [h111_U_h112 [Hh111 Hh112]]]].
      apply assert_m.mapstos_inv_dom in Hh111; last first.
        by rewrite [u2Z _]/= [Z_of_nat _]/= -rx_s_s'.
      rewrite Hh111.
      apply assert_m.mapstos_inv_dom in Hh112; last first.
        by rewrite [u2Z _]/= Hsub_s_s_1.
      rewrite -Hsub_s_s_1 Hh112.
      rewrite h111_U_h112.
      congr (_ \U _).
      rewrite Hunion h11_U_h12 h111_U_h112.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      by rewrite heap.proj_itself.
      rewrite Hunion h11_U_h12 h111_U_h112.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_R_dom; last by heap_tac_m.Disj.
      by rewrite heap.proj_itself.
- case: hoare_triple_post_condition => [h1 [h2 [Hdisj [Hunion [[X' [slen' [Hsub_s_s_1 [r_x [r_y [Hsub_s_s_2 [Hsub_s_s_3 Hsub_s_s_4]]]]]]]] HTT]]]].

  have Hslen' : heap.get '|u2Z ([ rx ]_ s')%asm_expr / 4| h' = Some slen'.
    rewrite Hunion.
    apply heap.get_union_L => //.
    rewrite 1!assert_m.conAE in Hsub_s_s_2.
    by apply assert_m.mapstos_get1 in Hsub_s_s_2.

  have Hptr : heap.get '|u2Z ([ rx ]_ s' `+ four32 )%asm_expr / 4| h' = Some ptr.
    rewrite Hunion.
    apply heap.get_union_L => //.
    rewrite 1!assert_m.conAE in Hsub_s_s_2.
    by apply assert_m.mapstos_get2 in Hsub_s_s_2.

  have Hsleny : heap.get '|u2Z [ ry ]_ s / 4| h = Some sleny.
    apply assert_m.mapstos_get1 in Hmemy.
    by apply heap_get_heap_mint_inv in Hmemy.

  apply state_mint_part2_two_variables with st s h => //.
  + move/assert_m.mapstos_get2 : (Hmem).
    move/heap_get_heap_mint_inv => ptr_vx4.
    move/assert_m.mapstos_get1 : (Hmem).
    move/heap_get_heap_mint_inv => slen_vx.
    symmetry.
    apply dom_heap_mint_sign_state_invariant with x st slen slen'.
    exact rx_s_s'.
    exact slen_vx.
    exact Hslen'.
    by rewrite Hptr.
    rewrite assoc_prop_m.swap_heads in st_s_h; last first.
      rewrite [Equality.sort _]/= in Hvars *. by Uniq_uniq y.
    apply (state_mint_var_mint _ _ _ _ _ _ st_s_h).
    rewrite assoc.get_union_sing_neq; last by Uniq_neq.
    by rewrite assoc.get_union_sing_eq.
    by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
  + symmetry.
    apply dom_heap_mint_sign_state_invariant with y st sleny sleny => //.

  have Hptry : heap.get '| u2Z [ry ]_ s' / 4 | h' = Some sleny.
    rewrite assert_m.conCE in Hsub_s_s_2.
    rewrite 1!assert_m.conAE in Hsub_s_s_2.
    apply assert_m.mapstos_get1 in Hsub_s_s_2.
    rewrite Hunion.
    by apply heap.get_union_L.
    exact Hptry.

    move/assert_m.mapstos_get2/heap_get_heap_mint_inv in Hmemy.
    rewrite assert_m.conCE assert_m.conAE in Hsub_s_s_2.
    apply assert_m.mapstos_get2 in Hsub_s_s_2.
    rewrite Hunion.
    symmetry.
    rewrite Hmemy.
    by apply heap.get_union_L.

    apply (state_mint_var_mint _ _ _ _ _ _ st_s_h).
    rewrite assoc.get_union_sing_neq; last by Uniq_neq.
    by rewrite assoc.get_union_sing_eq.
    by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
  + move=> t Ht x0 Hx0.
    mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs.
    case/assoc.in_cdom_union_inv : Ht => Ht.
    * rewrite assoc.cdom_sing /= seq.mem_seq1 in Ht.
      move/eqP : Ht => Ht; subst t.
      apply (@disj_not_In _ (mint_regs (signed k rx))); last by [].
      Disj_remove_dup.
      rewrite /=.
      apply uniq_disj.
      rewrite [cat _ _]/=.
      by Uniq_uniq r0.
    * case/assoc.in_cdom_union_inv : Ht => Ht.
      - rewrite assoc.cdom_sing /= mem_seq1 in Ht.
        move/eqP : Ht => Ht; subst t.
        apply (@disj_not_In _ (mint_regs (unsign rk ry))); last by rewrite /=; auto.
        Disj_remove_dup.
        rewrite /=.
        apply uniq_disj.
        rewrite [cat _ _]/=.
        by Uniq_uniq r0.
      - apply (@disj_not_In _ (mint_regs t)); last by [].
        Disj_remove_dup.
        apply disj_sym.
        apply (disj_incl_LR Hd); last by apply incl_refl_Permutation; PermutProve.
        exact/incP/inc_mint_regs.
  + by Uniq_neq.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ exec_asm_proj); tauto.
Qed.

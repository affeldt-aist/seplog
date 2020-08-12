(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext machine_int uniq_tac.
Require Import multi_int.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_mint.
Import expr_m.
Require Import simu.
Import simu_m.
Require Import multi_sub_s_u_prg multi_sub_s_u_triple.
From mathcomp Require Import seq.

Local Open Scope machine_int_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope heap_scope.
Local Open Scope simu_scope.
Local Open Scope multi_int_scope.

(** x <- x - y, x signed, y unsigned *)

Lemma pfwd_sim_multi_sub_s_u (x y : assoc.l) d k rk rx ry a0 a1 a2 a3 a4 a5 rX :
  uniq(x, y) ->
  uniq(rk, rx, ry, a0, a1, a2, a3, a4, a5, rX, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: rX :: nil) ->
  x \notin assoc.dom d -> y \notin assoc.dom d ->
  signed k rx \notin assoc.cdom d -> unsign rk ry \notin assoc.cdom d ->
  (x <- (var_e x \- var_e y)%pseudo_expr)%pseudo_cmd
    <=p( state_mint (x |=> signed k rx \U+ (y |=> unsign rk ry \U+ d)),
         fun s st _ =>
           [rk ]_ st <> zero32 /\
           u2Z ([rk ]_ st) < 2 ^^ 31 /\
           k = '|u2Z ([rk ]_ st)| /\
           `|([ x ]_ s)%pseudo_expr| < \B^k /\
           0 <= ([y ]_ s)%pseudo_expr < \B^k /\
           `|([ x ]_ s)%pseudo_expr - ([y ]_ s)%pseudo_expr| < \B^k)
  multi_sub_s_u rk rx ry a0 a1 a2 a3 a4 a5 rX.
Proof.
move=> Hvars Hregs Hd x_d y_d rx_d rk_ry_d.
rewrite /pfwd_sim.
move=> st s h [st_s_h [rk_st_neq0 [rk_st_max [k_rk [x_k [y_st x_y_st]]]]]] st' exec_pseudo s' h' exec_asm.
have Hd_unchanged : forall v r, assoc.get v d = Some r ->
  disj (mint_regs r) (mips_frame.modified_regs (multi_sub_s_u rk rx ry a0 a1 a2 a3 a4 a5 rX)).
  move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
  apply (disj_incl_LR Hd); last by apply incl_refl_Permutation; PermutProve.
  apply/incP/inc_mint_regs.
  by move/assoc.get_Some_in_cdom : Hvr.
set vx := [ rx ]_ s.
set vy := [ ry ]_ s.
lapply (state_mint_var_mint _ _ _ _ x (signed k rx) st_s_h); [move=> var_mint_x | by assoc_get_Some].
rewrite /var_mint in var_mint_x.
case: var_mint_x => slen ptr X vx_fit [X_k Hlen Hsgn Sum_X] ptr_fit Hmem.

move/multi_sub_s_u_triple : (Hregs).
move/(_ k vx vy ptr).
have : k <> O.
  contradict rk_st_neq0. apply u2Z_inj. rewrite rk_st_neq0 in k_rk.
  symmetry in k_rk. apply Zabs_nat_0_inv in k_rk. by rewrite Z2uK.
let x := fresh in move=> x; move/(_ x); clear x.
have : Z<=nat k < 2 ^^ 31 by rewrite k_rk Z_of_nat_Zabs_nat //; apply min_u2Z.
let x := fresh in move=> x; move/(_ x); clear x.
move/(_ ptr_fit).
have : Z<=u vy + 4 * Z<=nat k < \B^1.
  rewrite assoc_prop_m.swap_heads in st_s_h; last by [].
  move: (state_mint_head_unsign_fit _ _ _ _ _ _ _ st_s_h); by rewrite k_rk.
let x := fresh in move=> x; move/(_ x); clear x.
move/(_ X (Z2ints 32 k ([ y ]_ st)%pseudo_expr) X_k).
rewrite size_Z2ints.
move/(_ Logic.eq_refl slen Hlen).
rewrite -Sum_X.
move/(_ Hsgn) => Hhoare_multi_sub_s_u.

have [s'' [h'' exec_asm_proj]] : exists s'' h'',
  (Some (s, h |P| heap.dom (heap_mint (unsign rk ry) s h \U heap_mint (signed k rx) s h))
    -- multi_sub_s_u rk rx ry a0 a1 a2 a3 a4 a5 rX --->
    Some (s'', h''))%mips_cmd.
  exists s', (h' |P| heap.dom (heap_mint (unsign rk ry) s h \U heap_mint (signed k rx) s h)).
  apply (mips_syntax.triple_exec_proj _ _ _ Hhoare_multi_sub_s_u) => {Hhoare_multi_sub_s_u} //.
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
  have y_ry : var_mint y (unsign rk ry) st s (heap_mint (unsign rk ry) s h).
    apply (state_mint_var_mint _ _ _ _ _ _ st_s_h); by assoc_get_Some.
  case: (y_ry) => _ [] _ Hry.
  rewrite /heap_mint /heap_cut in y_ry.
  by rewrite k_rk (var_mint_unsign_dom_heap_mint _ _ _ _ _ _ y_ry).
have ry_s_s' : [ ry ]_ s = [ ry ]_ s'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
have rk_s_s' : [ rk ]_ s = [ rk ]_ s'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
have y_st_st' : ([ y ]_ st = [ y ]_ st')%pseudo_expr.
  Var_unchanged. simpl syntax_m.seplog_m.modified_vars.
  move/inP.
  rewrite -/(~ _).
  by Uniq_not_In.
have rx_s_s' : [ rx ]_ s = [ rx ]_ s'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
set postcond := (fun s h => exists _, _) in Hhoare_multi_sub_s_u.
have {Hhoare_multi_sub_s_u}hoare_triple_post_condition : (postcond
 ** assert_m.TT)%asm_assert s' h'.
    move: {Hhoare_multi_sub_s_u}(mips_frame.frame_rule_R _ _ _ Hhoare_multi_sub_s_u assert_m.TT (assert_m.inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
    move/mips_seplog.hoare_prop_m.soundness.
    rewrite /while.hoare_semantics.

(* TODO *)
Notation "s -- c ---> t" := (@while.exec WMIPS_Hoare.store WMIPS_Hoare.heap _ WMIPS_Hoare.exec0 _
  WMIPS_Hoare.eval_b s c t)  (at level 74, no associativity) : mips_cmd_scope.

    move/(_ s h) => Hmulti_sub_s_u.
    lapply Hmulti_sub_s_u; last first.
      exists (heap_mint (signed k rx) s h \U heap_mint (unsign rk ry) s h),
        (h \D\ heap.dom (heap_mint (signed k rx) s h \U heap_mint (unsign rk ry) s h)).
      split.
        by apply heap.disj_difs', seq_ext.inc_refl.
      split.
        apply heap.union_difsK; last by [].
        apply heap_prop_m.inclu_union; by [apply heap_inclu_heap_mint_signed | apply heap.inclu_proj].
      split; last by [].
      repeat (split=> //).
      - rewrite k_rk Z_of_nat_Zabs_nat //; exact: min_u2Z.
      - apply assert_m.con_cons.
        + apply (proj2 st_s_h x y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
        + exact Hmem.
        + move: (proj1 st_s_h y (unsign rk ry)).
          rewrite assoc.get_union_sing_neq; last by Uniq_neq.
          rewrite assoc.get_union_sing_eq.
          case/(_ refl_equal)=> _ [] _; by rewrite -k_rk.
    case=> _.
    by move/(_ _ _ exec_asm).
rewrite /state_mint; split.
- move=> z rz z_rz.
  have [z_d | z_x ] : z \in assoc.dom (y |=> unsign rk ry \U+ d) \/ z = x.
    rewrite assoc.unionC in z_rz; last first.
      apply assoc.disjhU.
      apply assoc.disj_sing; apply/eqP; by Uniq_neq.
      by apply assoc.disj_sym, assoc.disj_sing_R.
    case/assoc.get_union_Some_inv : z_rz => z_rz.
    left.
    by apply assoc.get_Some_in_dom with rz.
    case/assoc.get_sing_inv : z_rz => ? ?; subst z rz.
    by right.
  + (* NB: it is about proving that z is unchanged, which is true since
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
    case: hoare_triple_post_condition => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
    case: Hh1 => X' [slen' Hh1].
    case: Hh1 => H [H1 [H0 [H2 [H3 [H4 [H5 H7]]]]]].
    case: H4 => h11 [h12 [h11_d_h12 [h11_U_h12 [Hh11 Hh12]]]].
    move: (proj1 st_s_h y (unsign rk ry)).
    rewrite assoc.get_union_sing_neq; last by Uniq_neq.
    rewrite assoc.get_union_sing_eq.
    move/(_ (refl_equal _)).
    have <- : heap_mint (unsign rk ry) s h = heap_mint (unsign rk ry) s' h'.
      (* show that rhs = h12 *)
      rewrite {2}/heap_mint /heap_cut h1_U_h2 h11_U_h12.
      move/assert_m.mapstos_inv_dom : (Hh12) => Hh12'.
      have : u2Z [var_e ry ]e_ s' +
        4 * Z_of_nat (size (Z2ints 32 k ([y ]_ st)%pseudo_expr)) < \B^1.
        rewrite [u2Z _]/= size_Z2ints -ry_s_s'.
        move: (proj1 st_s_h y (unsign rk ry)).
        rewrite assoc.get_union_sing_neq; last by Uniq_neq.
        rewrite assoc.get_union_sing_eq k_rk.
        by case/(_ (refl_equal _)).
      move/Hh12' => {}Hh12'.
      rewrite size_Z2ints k_rk rk_s_s' in Hh12'.
      rewrite {}Hh12'.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_R_dom; last by heap_tac_m.Disj.

      move: (proj1 st_s_h y (unsign rk ry)).
      rewrite assoc.get_union_sing_neq; last by auto.
      rewrite assoc.get_union_sing_eq.
      case/(_ (refl_equal _)) => X1 X2 X3.
      rewrite -k_rk in X3.
      rewrite heap.proj_itself.

      apply: (assert_m.strictly_exact_mapstos (Z2ints 32 k ([ y ]_ st)%pseudo_expr) (var_e ry) s).
      split; first by [].
      move: Hh12; by apply assert_m.mapstos_ext.

    apply var_mint_invariant_unsign; [exact ry_s_s' | exact rk_s_s' | exact y_st_st'].
    (* x <> y *)
    move: {st_s_h}(proj1 st_s_h _ _ z_rz) (proj2 st_s_h) => st_s_h1 st_s_h2.
    have z_unchanged : ( [ z ]_ st = [ z ]_st' )%pseudo_expr.
      Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    case: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm
      (heap.dom (heap_mint (unsign rk ry) s h \U heap_mint (signed k rx) s h)) _ _
      exec_asm_proj) => H4 [H5 H_h_h'].
    have <- : heap_mint rz s h = heap_mint rz s' h'.
      apply (heap_mint_state_invariant (heap_mint (unsign rk ry) s h \U
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
    move: st_s_h1; apply var_mint_invariant; last by exact z_unchanged.
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
    case: hoare_triple_post_condition => [h1 [h2 [Hdisj [Hunion [[X' [slen' [Hsub_s_us_1 [r_x [r_y [Hsub_s_us_2 [Hsub_s_us_3 [Hsub_s_us_4 [Hsub_s_us_5 Hsub_s_us_6]]]]]]]]]] HTT]]]].
    move=> ?.
    have x'_x_y : ([ x ]_ st' = [ x ]_ st - [ y ]_ st )%pseudo_expr.
      move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
      case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
      by syntax_m.seplog_m.assert_m.expr_m.Store_upd.
    apply (mkVarSigned _ _ _ _ _ slen' ptr X') => //.
    + by rewrite /vx -rx_s_s'.
    + apply mkSignMagn.
      * exact Hsub_s_us_1.
      * exact Hsub_s_us_2.
      * rewrite !lSum_Z2ints_pos in Hsub_s_us_6 Hsub_s_us_3; last exact y_st.
        by rewrite Hsub_s_us_3 x'_x_y.
      * rewrite !lSum_Z2ints_pos in Hsub_s_us_6 Hsub_s_us_3; last exact y_st.
        rewrite -x'_x_y in Hsub_s_us_6.
        case: (Z_zerop (s2Z slen')) => slen'_neq0.
          rewrite -Hsub_s_us_6 slen'_neq0 /=; ring.
        have Hi : u2Z [a3 ]_ s' = 0.
          have : `|sgZ (s2Z slen') * (\S_{ k } X' + u2Z [ a3 ]_ s' * \B^k)| < \B^k.
            by rewrite Hsub_s_us_6 x'_x_y.
          rewrite Zabs_Zmult Zabs_Zsgn_1 // Zmult_1_l addZC.
          apply: poly_Zlt1_Zabs_inv => //.
          exact: min_lSum.
          exact: min_u2Z.
        by rewrite Hi mul0Z addZ0 in Hsub_s_us_6.
    + rewrite [heap_mint _ _ _]/=.
      have -> : heap.get '|u2Z ([ rx ]_ s') / 4| h' = Some slen'.
        rewrite Hunion; apply heap.get_union_L => //.
        rewrite assert_m.conAE in Hsub_s_us_4.
        by apply assert_m.mapstos_get1 in Hsub_s_us_4.
      have -> : heap.get '|u2Z ([ rx ]_ s' `+ four32) / 4| h' = Some ptr.
        rewrite Hunion; apply heap.get_union_L => //.
        rewrite assert_m.conAE in Hsub_s_us_4.
        by apply assert_m.mapstos_get2 in Hsub_s_us_4.
      case: Hsub_s_us_4 => h11 [h12 [h11_d_h12 [h11_U_h12 [Hh11 Hh12]]]].
      set hh := _ \U _.
      suff : hh = h11 by move=> ->.
      rewrite /hh.
      case: Hh11 => h111 [h112 [h111_d_h112 [h111_U_h112 [Hh111 Hh112]]]].
      rewrite /heap_cut.
      apply assert_m.mapstos_inv_dom in Hh111; last first.
        rewrite [size _]/= [u2Z _]/= -rx_s_s'; exact vx_fit.
      rewrite Hh111.
      apply assert_m.mapstos_inv_dom in Hh112; last by rewrite Hsub_s_us_1.
      rewrite Hsub_s_us_1 in Hh112.
      rewrite Hh112 /hh /heap_cut Hunion h11_U_h12 h111_U_h112.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_L_dom; last exact h111_d_h112.
      rewrite heap.proj_itself.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
      rewrite heap.proj_union_R_dom; last by heap_tac_m.Disj.
      by rewrite heap.proj_itself.
- case: hoare_triple_post_condition => [h1 [h2 [Hdisj [Hunion [[X' [slen' [Hsub_s_us_1 [r_x [r_y [Hsub_s_us_2 [Hsub_s_us_3 [Hsub_s_us_4 [Hsub_s_us_5 Hsub_s_us_6]]]]]]]]]] HTT]]]].

  have Hslen' : heap.get '|u2Z ([ rx ]_ s') / 4| h' = Some slen'.
    rewrite Hunion.
    apply heap.get_union_L => //.
    rewrite assert_m.conAE in Hsub_s_us_4.
    by apply assert_m.mapstos_get1 in Hsub_s_us_4.

  have Hptr : heap.get '|u2Z ([ rx ]_ s' `+ four32) / 4| h' = Some ptr.
    rewrite Hunion.
    apply heap.get_union_L => //.
    rewrite assert_m.conAE in Hsub_s_us_4.
    by apply assert_m.mapstos_get2 in Hsub_s_us_4.

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
    rewrite assoc_prop_m.swap_heads in st_s_h; last by [].
    apply (state_mint_var_mint _ _ _ _ _ _ st_s_h).
    rewrite assoc.get_union_sing_neq; last by Uniq_neq.
    by rewrite assoc.get_union_sing_eq.
    by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
  + symmetry.
    apply dom_heap_mint_unsign_state_invariant with y st.
    exact rk_s_s'.
    exact ry_s_s'.
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
      - rewrite assoc.cdom_sing /= seq.mem_seq1 in Ht.
        move/eqP : Ht => Ht; subst t.
        apply (@disj_not_In _ (mint_regs (unsign rk ry))); last by [].
        Disj_remove_dup.
        rewrite /=.
        apply uniq_disj.
        rewrite [cat _ _]/=.
        by Uniq_uniq r0.
      - apply (@disj_not_In _ (mint_regs t)); last by [].
        Disj_remove_dup.
        apply/disj_sym/(disj_incl_LR Hd); last by apply incl_refl_Permutation; PermutProve.
        exact/incP/inc_mint_regs.
  + by Uniq_neq.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ exec_asm_proj); tauto.
Qed.

(* TODO: use the notation for lists *)
Lemma pfwd_sim_multi_sub_s_u_wo_overflow (x y : assoc.l) d k rk ry rx a0 a1 a2 a3 a4 a5 rX :
  uniq(x, y) ->
  uniq(rk, rx, ry, a0, a1, a2, a3, a4, a5, rX, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: rX :: nil)%list ->
  x \notin assoc.dom d -> y \notin assoc.dom d ->
  signed k rx \notin assoc.cdom d -> unsign rk ry \notin assoc.cdom d ->
  (x <- var_e x \- var_e y)%pseudo_expr%pseudo_cmd
    <=p( state_mint (x |=> signed k rx \U+ (y |=> unsign rk ry \U+ d)),
         (fun st s _ =>  [rk ]_ s <> zero32 /\
                         u2Z ([rk ]_ s) < 2 ^^ 31 /\
                         k = '|u2Z ([rk ]_ s)| /\
                         `|([ x ]_ st)%pseudo_expr| < \B^(k - 1) /\
                         0 <= ([y ]_ st)%pseudo_expr < \B^(k - 1)) )
  multi_sub_s_u rk rx ry a0 a1 a2 a3 a4 a5 rX.
Proof.
move=> Hvars Hregs Hd x_d y_d rx_d rk_ry_d.
eapply pfwd_sim_stren; last by apply pfwd_sim_multi_sub_s_u.
move=> s st h [rk_neq0 [rk_max [k_rk [x_max y_bounds]]]].
split; first by [].
split; first by [].
split; first by [].
have k_neq0 : k <> O.
  rewrite k_rk.
  contradict rk_neq0.
  apply Zabs_nat_0_inv in rk_neq0.
  rewrite (_ : 0 = u2Z (Z2u 32 0)) in rk_neq0; last by rewrite Z2uK.
  by move/u2Z_inj : rk_neq0.
split.
  apply/(ltZ_trans x_max)/Zbeta_lt; ssromega.
split.
  split; first tauto.
  apply/(ltZ_trans (proj2 y_bounds))/Zbeta_lt; ssromega.
apply: leZ_ltZ_trans; first exact: Z.abs_triangle.
rewrite Z.abs_opp (geZ0_norm ([y ]_ s)%pseudo_expr); last lia.
apply: ltZ_trans.
- apply ltZ_add; [exact: x_max | exact: (proj2 y_bounds)].
- rewrite /Zbeta Zpower_plus.
  apply expZ_2_lt; by ssromega.
Qed.

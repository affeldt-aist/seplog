(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_mint mips_syntax mips_frame.
Require Import encode_decode.
Import expr_m.
Require Import simu.
Import simu_m.
Require Import copy_s_u_prg copy_s_u_triple.
From mathcomp Require Import seq.

Local Open Scope machine_int_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope heap_scope.
Local Open Scope simu_scope.

(** x <- y, x signed, y unsigned *)

Lemma pfwd_sim_copy_s_u (x y : assoc.l) d  (rk ry rx a0 a1 a2 a3 : reg) k :
  uniq(x, y) ->
  uniq(rk, rx, ry, a0, a1, a2, a3, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: a2 :: a3 :: nil) ->
  x \notin assoc.dom d -> y \notin assoc.dom d ->
  unsign rk rx \notin assoc.cdom d -> signed k ry \notin assoc.cdom d ->
  (x <- var_e%pseudo_expr y)%pseudo_cmd
    <=p( state_mint (x |=> signed k rx \U+ (y |=> unsign rk ry \U+ d)),
         (fun s st _ =>  0 < u2Z ([rk ]_ st) < 2 ^^ 31 /\
         k = '|u2Z ([rk ]_ st)| /\
         0 <= ([y ]_ s)%pseudo_expr < \B^k)%asm_expr)
  copy_s_u rk rx ry a0 a1 a2 a3.
Proof.
move=> Hvars Hregs Hdisj x_d y_d rx_d ry_d.
rewrite /pfwd_sim => s st h [s_st_h HP] s' exec_pseudo st' h' exec_asm.

move/state_mint_var_mint : (s_st_h).
move/(_ x (signed k rx)).
rewrite assoc.get_union_sing_eq.
case/(_ refl_equal) => slen ptr X rx_fit X_x ptr_fit memX.

move/state_mint_var_mint : (s_st_h).
move/(_ y (unsign rk ry)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
case/(_ refl_equal) => ry_fit y_safe memY.

case: X_x => X_nk slen_nk slen_x x_X.
move/copy_s_u_triple : (Hregs).
move/(_ _ (Z2ints 32 k ([y ]_ s)%pseudo_expr) _ X_nk).
rewrite size_Z2ints.
move/(_ (refl_equal _) slen _ ptr_fit ([ry ]_ st)%asm_expr).
case: HP => HP0 [HP1 HP2].
rewrite {1}HP1.
move/(_ ry_fit).
move=> Hhoare_triple.

have [st'' [h'' exec_triple_proj]] : exists st'' h'',
  (Some (st, h |P| heap.dom (heap_mint (signed k rx) st h \U heap_mint (unsign rk ry) st h)) --
    copy_s_u rk rx ry a0 a1 a2 a3 --->
    Some (st'', h''))%mips_cmd.
  exists st', (h' |P| heap.dom (heap_mint (signed k rx) st h \U heap_mint (unsign rk ry) st h)).
  apply: (mips_syntax.triple_exec_proj _ _ _ Hhoare_triple) => //.
  split; first by reflexivity.
  split.
    rewrite HP1 Z_of_nat_Zabs_nat //; exact/min_u2Z.
  rewrite heap.proj_dom_union; last first.
    apply (proj2 s_st_h x y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  apply assert_m.con_cons => //.
    apply heap.dis_disj_proj.
    rewrite -heap.disjE.
    apply (proj2 s_st_h x y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  move: (heap_inclu_heap_mint_signed h st k rx).
  move/heap.incluE => ->; exact memX.

  move/heap.incluE: (heap_inclu_heap_mint_unsign h st rk ry) => ->.
  by rewrite -HP1 in memY.

rewrite lSum_Z2ints in Hhoare_triple; last first.
  rewrite /Zbeta -HP1 in y_safe.
  rewrite geZ0_norm; tauto.

set postcond := (fun s h => _ /\ _ /\ ((_ |--> (if _ then _ else _) :: _ ** _ ) ** _) s h )%asm_assert in Hhoare_triple.
have {Hhoare_triple}hoare_triple_post_cond : (postcond ** assert_m.TT)%asm_assert st' h'.
  move: {Hhoare_triple}(mips_frame.frame_rule_R _ _ _ Hhoare_triple assert_m.TT (assert_m.inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
  move/mips_seplog.hoare_prop_m.soundness.
  rewrite /while.hoare_semantics.
  move/(_ st h) => Hhoare_triple.
  lapply Hhoare_triple; last first.
    exists (heap_mint (signed k rx) st h \U heap_mint (unsign rk ry) st h),
      (h \D\ heap.dom (heap_mint (signed k rx) st h \U heap_mint (unsign rk ry) st h)).
    split; first by apply heap.disj_difs', inc_refl.
    split.
      apply heap.union_difsK; last by [].
      apply heap_prop_m.inclu_union; by [apply heap_inclu_heap_mint_signed | apply heap.inclu_proj].
    split; last by [].
    repeat (split=> //).
    rewrite HP1.
    rewrite Z_of_nat_Zabs_nat //; exact/min_u2Z.
    apply assert_m.con_cons.
    + apply (proj2 s_st_h x y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
    + exact memX.
    + move: (proj1 s_st_h y (unsign rk ry)).
      rewrite assoc.get_union_sing_neq; last by Uniq_neq.
      rewrite assoc.get_union_sing_eq.
      case/(_ (refl_equal _))=> _ [] _ _.
      by rewrite -HP1.
  by case=> _ /(_ _ _ exec_asm).

have s2Z_Z2u_k : s2Z (Z2u 32 (Z_of_nat k)) = Z_of_nat k.
  rewrite HP1 Z_of_nat_Zabs_nat; last by apply min_u2Z.
  rewrite s2Z_u2Z_pos' //.
  rewrite Z2uK //; last by rewrite /= in HP0 *; omega.
  rewrite Z2uK //; last by rewrite /= in HP0 *; omega.
  rewrite /= in HP0 *; omega.

have rx_st_st' : ([rx ]_ st = [rx]_st')%asm_expr.
  Reg_unchanged. rewrite [modified_regs _]/=. by Uniq_not_In.
have rk_st_st' : ([rk ]_ st = [rk]_st')%asm_expr.
  Reg_unchanged. rewrite [modified_regs _]/=. by Uniq_not_In.

rewrite /state_mint; split.

- move=> z mz.
  case/assoc.get_union_Some_inv => [z_is_x | z_in_y_or_d].
  + apply assoc.get_sing_inv in z_is_x.
    case: z_is_x => ? ?; subst z mz.
    case: HP2.
    case/leZ_eqVlt => HP2 HP2'.
    * apply mkVarSigned with zero32 ptr X => //.
      + by rewrite -rx_st_st'.
      + apply mkSignMagn => //.
        - by rewrite s2Z_u2Z_pos' Z2uK.
        - move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
          case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
          syntax_m.seplog_m.assert_m.expr_m.Store_upd.
          rewrite -HP2.
          by rewrite s2Z_u2Z_pos' Z2uK.
        - move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
          case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
          syntax_m.seplog_m.assert_m.expr_m.Store_upd.
          rewrite -HP2.
          by rewrite s2Z_u2Z_pos' Z2uK.
      + case: hoare_triple_post_cond => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
        rewrite /postcond in Hh1.
        case: Hh1 => ry_st_st' [rk_nk Hh1].
        rewrite -HP2 eqxx in Hh1.
        case: Hh1 => h11 [h12 [h11dh12 [h11Uh12 [Hh11 Hh12]]]].
        apply con_heap_mint_signed_cons with h11 => //.
        - rewrite h1Uh2 h11Uh12.
          apply heap.inclu_union_L.
          heap_tac_m.Disj.
          apply heap.inclu_union_L => //.
          by apply heap.inclu_refl.
        - by rewrite -rx_st_st'.
        - by rewrite X_nk.
    * have Zsgn_y_k : sgZ ([y ]_ s)%pseudo_expr = sgZ (Z_of_nat k).
        apply Zsgn_pos in HP2; rewrite HP2.
        apply/esym/Zsgn_pos.
        rewrite HP1 Z_of_nat_Zabs_nat; last exact/min_u2Z.
        tauto.
      apply mkVarSigned with (Z2u 32 (Z_of_nat k)) ptr (Z2ints 32 k ([y ]_ s)%pseudo_expr) => //.
      + by rewrite -rx_st_st'.
      + apply mkSignMagn => //.
        - by rewrite size_Z2ints.
        - rewrite s2Z_Z2u_k.
          by apply Z_of_nat_Zsgn.
        - move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
          case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
          syntax_m.seplog_m.assert_m.expr_m.Store_upd.
          by rewrite s2Z_Z2u_k.
        - move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
          case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
          syntax_m.seplog_m.assert_m.expr_m.Store_upd.
          rewrite s2Z_Z2u_k.
          rewrite -{1}(Zabs_Zsgn ([y]_s)%pseudo_expr) mulZC Zsgn_y_k; congr (_ * _).
          rewrite lSum_Z2ints // geZ0_norm //; exact: ltZW.
      + case: hoare_triple_post_cond => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
        rewrite /postcond in Hh1.
        case: Hh1 => ry_st_st' [rk_k Hh1].
        case: Hh1 => h11 [h12 [h11dh12 [h11Uh12 [Hh11 Hh12]]]].
        rewrite geZ0_norm in Hh11; last exact: ltZW.
        have HP2'' : ([y ]_ s)%pseudo_expr == 0 = false by apply/eqP; omega.
        rewrite HP2'' in Hh11.
        apply con_heap_mint_signed_cons with h11 => //.
        - rewrite h1Uh2 h11Uh12.
          apply heap.inclu_union_L.
          heap_tac_m.Disj.
          apply heap.inclu_union_L => //.
          by apply heap.inclu_refl.
        - by rewrite -rx_st_st'.
        - by rewrite size_Z2ints.
        - by rewrite size_Z2ints.
  + (* z is unchanged *)
    have z_x : z <> x.
      move=> ?; subst z.
      case/assoc.get_union_Some_inv : z_in_y_or_d => [xy | xd].
      apply assoc.get_sing_inv in xy.
      case: xy => tmp _; move: tmp.
      rewrite -/(x <>y).
      by Uniq_neq.
      apply assoc.get_Some_in_dom in xd.
      by rewrite xd in x_d.
    move: (proj2 s_st_h) => s_st_h2.
    move: {s_st_h}(proj1 s_st_h z mz).
    rewrite assoc.get_union_sing_neq //.
    move/(_ z_in_y_or_d) => s_st_h1.
    have z_unchanged : ( [ z ]_s = [ z ]_s' )%pseudo_expr.
      Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    have Hd_unchanged : forall v r, assoc.get v d = Some r ->
      disj (mint_regs r) (mips_frame.modified_regs (copy_s_u rk rx ry a0 a1 a2 a3)).
      move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
      apply (disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
      apply/incP/inc_mint_regs.
      by move/assoc.get_Some_in_cdom : Hvr.
    case: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm
      (heap.dom (heap_mint (signed k rx) st h \U heap_mint (unsign rk ry) st h)) _ _
      exec_triple_proj) => Hst'_st'' [Hh'' H_h_h'].
    have <- : heap_mint mz st h = heap_mint mz st' h'.
      have [zy | zy] : z = y \/ z <> y.
        omega.
      - subst z.
        rewrite assoc.get_union_sing_eq in z_in_y_or_d.
        case: z_in_y_or_d => ?; subst mz.

        case: s_st_h1 => X1 X2 X3.
        apply mapstos_inv_list2heap in X3; last by rewrite size_Z2ints.
        rewrite X3 [ ([ _ ]e_ _)%asm_expr ]/= -!HP1.

        rewrite /heap_mint /heap_cut.
        case: hoare_triple_post_cond => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
        rewrite /postcond in Hh1.
        case: Hh1 => ry_st_st' [rk_st' Hh1].
        rewrite h1Uh2.
        (* TODO: investigate *)
        rewrite heap.proj_union_L; last first.
          rewrite ry_st_st'.
          set d1 := iota _ _.
          suff : inc d1 (heap.dom h1).
            by apply/dis_inc_R; rewrite dis_sym -heap.disjE.
          apply inv_list2heap in Hh1; last first.
            by rewrite size_Z2ints [ ([ _ ]e_ _)%asm_expr ]/= ry_st_st' HP1.
          rewrite size_Z2ints in Hh1.
          by rewrite /d1 rk_st' Zabs2Nat.id -ry_st_st'.

        apply mapstos_inv_proj_list2heap in Hh1.
        by rewrite -ry_st_st' -Hh1 size_Z2ints HP1 rk_st_st'.

        rewrite size_Z2ints [ ([ _ ]e_ _)%asm_expr ]/= ry_st_st' HP1; exact X1.

      - rewrite assoc.get_union_sing_neq // in z_in_y_or_d.
        apply (heap_mint_state_invariant (heap_mint (signed k rx) st h \U
            heap_mint (unsign rk ry) st h) z s) => //.
        move=> rx0 Hrx0; mips_syntax.Reg_unchanged.
        apply (@disj_not_In _ (mint_regs mz)); last by [].
        apply/disj_sym/(Hd_unchanged z).
        exact z_in_y_or_d.
        apply heap.disjhU.
        apply s_st_h2 with z x => //; by assoc_get_Some.
        apply s_st_h2 with z y => //; by assoc_get_Some.
    move: s_st_h1; apply var_mint_invariant; last exact z_unchanged.
    move=> rx0 Hrx0; mips_syntax.Reg_unchanged.
    apply (@disj_not_In _ (mint_regs mz)); last by [].
    have [zy | zy] : z = y \/ z <> y.
      omega.
    - subst z.
      rewrite assoc.get_union_sing_eq in z_in_y_or_d.
      case: z_in_y_or_d => ?; subst mz.
      simpl.
      by Disj_uniq r0.
    - apply disj_sym, (Hd_unchanged z) => //.
      by rewrite assoc.get_union_sing_neq in z_in_y_or_d.
- case: hoare_triple_post_cond => h1 [h2 [H1dh2 [h1Uh2 [Hh1 _]]]].
  rewrite /postcond in Hh1.
  case: Hh1 => ry_st_st' [rk_st'_k Hh1].
  have Hslen' : heap.get '|u2Z ([rx ]_ st')%asm_expr / 4| h' = Some (if `| ([y ]_ s)%pseudo_expr | == 0
                then zero32
                else Z2u 32 (Z_of_nat k)).
    rewrite h1Uh2.
    apply heap.get_union_L => //.
    rewrite assert_m.conAE in Hh1.
    by apply assert_m.mapstos_get1 in Hh1.
  have Hptr : heap.get '|u2Z ([rx ]_ st' `+ four32 )%asm_expr / 4| h' = Some ptr.
    rewrite h1Uh2.
    apply heap.get_union_L => //.
    rewrite assert_m.conAE in Hh1.
    by apply assert_m.mapstos_get2 in Hh1.
  apply state_mint_part2_two_variables with s st h => //.
  + move/assert_m.mapstos_get2 : (memX).
    move/heap_get_heap_mint_inv => ptr_vx4.
    move/assert_m.mapstos_get1 : (memX).
    move/heap_get_heap_mint_inv => slen_vx.
    symmetry.
    apply dom_heap_mint_sign_state_invariant with x s slen (if `| ([y ]_ s)%pseudo_expr | == 0
                then zero32
                else Z2u 32 (Z_of_nat k)).
    exact rx_st_st'.
    exact slen_vx.
    exact Hslen'.
    by rewrite Hptr.
    rewrite assoc_prop_m.swap_heads in s_st_h; last by [].
    apply (state_mint_var_mint _ _ _ _ _ _ s_st_h); by assoc_get_Some.
    by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
  + symmetry.
    apply dom_heap_mint_unsign_state_invariant with y s.
    exact rk_st_st'.
    symmetry; exact ry_st_st'.
    apply (state_mint_var_mint _ _ _ _ _ _ s_st_h); by assoc_get_Some.
    by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
  + move=> t Ht x0 Hx0.
    mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs.
    case/assoc.in_cdom_union_inv : Ht => Ht.
    * rewrite assoc.cdom_sing /= seq.mem_seq1 in Ht.
      move/eqP : Ht => Ht; subst t.
      apply (@disj_not_In _ (mint_regs (signed k rx))); last by [].
      Disj_remove_dup.
      rewrite /=.
      apply uniq_disj. rewrite [cat _ _]/=. by Uniq_uniq r0.
    * case/assoc.in_cdom_union_inv : Ht => Ht.
      - rewrite assoc.cdom_sing /= seq.mem_seq1 in Ht.
        move/eqP : Ht => Ht; subst t.
        apply (@disj_not_In _ (mint_regs (unsign rk ry))); last by [].
        Disj_remove_dup.
        rewrite /=.
        apply uniq_disj. rewrite [cat _ _]/=. by Uniq_uniq r0.
      - apply (@disj_not_In _ (mint_regs t)); last by [].
        Disj_remove_dup.
        apply/disj_sym/(disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
        exact/incP/inc_mint_regs.
  + by Uniq_neq.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ exec_triple_proj).
    case=> st'_st'' [Hh'' h_h'].
    rewrite heap.unionC //.
    apply: (proj2 s_st_h y x); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
Qed.

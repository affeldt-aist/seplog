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
Require Import copy_s_s_prg copy_s_s_triple.
From mathcomp Require Import seq.

Local Open Scope machine_int_scope.
Local Open Scope asm_expr_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope heap_scope.
Local Open Scope simu_scope.

(** x <- y, x, y signed *)

Lemma pfwd_sim_copy_s_s (x y : assoc.l) d k (rk rx ry a0 a1 a2 a3 a4 : reg) :
  uniq(x, y) -> uniq(rk, rx, ry, a0, a1, a2, a3, a4, r0) ->
  disj (mints_regs (assoc.cdom d)) (a0 :: a1 :: a2 :: a3 :: a4 :: nil)%list ->
  x \notin assoc.dom d -> y \notin assoc.dom d ->
  signed k rx \notin assoc.cdom d -> signed k ry \notin assoc.cdom d ->
  (x <- var_e y)%pseudo_expr%pseudo_cmd
    <=p( state_mint (x |=> signed k rx \U+ (y |=> signed k ry \U+ d)),
         fun s st _ => k = '|u2Z ([rk ]_ st)|)
  copy_s_s rk rx ry a0 a1 a2 a3 a4.
Proof.
move=> Hvars Hregs Hdisj x_d y_d rx_d ry_d st s h [st_s_h HP] st' exec_pseudo s' h' exec_asm.

move: (proj1 st_s_h x (signed k rx)).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => len_x ptr_x X rx_fit [X_k s2Z_len_x Zsgn_len_x x_X] ptr_x_fit mem_rx.

move: (proj1 st_s_h y (signed k ry)).
rewrite assoc.get_union_sing_neq; last by Uniq_neq.
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => len_y ptr_y Y ry_fit [Y_k s2Z_len_y Zsgn_len_y y_Y] ptr_y_fit mem_ry.

rewrite y_Y in Zsgn_len_y.
move: (copy_s_s_triple _ _ _ _ _ _ _ _ Hregs X Y _ X_k Y_k len_x ptr_x ptr_x_fit
  len_y ptr_y ptr_y_fit ([ry]_s) s2Z_len_y Zsgn_len_y) => hoare_triple.

have [s'' [h'' exec_asm_proj]] : exists s'' h'',
  (Some (s, heap.proj h (heap.dom (heap_mint (signed k ry) s h \U heap_mint (signed k rx) s h)))
    -- copy_s_s rk rx ry a0 a1 a2 a3 a4 ---> Some (s'', h''))%mips_cmd.
  exists s', (heap.proj h' (heap.dom (heap_mint (signed k ry) s h \U heap_mint (signed k rx) s h))).
  rewrite assert_m.conCE in hoare_triple.
  rewrite [in X in ({{ _ }} _ {{ X }} )%asm_hoare]assert_m.conCE in hoare_triple.
  apply (mips_syntax.triple_exec_proj _ _ _ hoare_triple) => {hoare_triple} //.
  split; first by reflexivity.
  split.
    rewrite HP Z_of_nat_Zabs_nat //; exact/min_u2Z.
  rewrite heap.proj_dom_union; last first.
    apply (proj2 st_s_h y x); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  apply assert_m.con_cons.
    apply heap.dis_disj_proj.
    rewrite -heap.disjE.
    apply (proj2 st_s_h y x); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
  move: (heap_inclu_heap_mint_signed h s k ry).
  move/heap.incluE => ->; exact mem_ry.
  move: (heap_inclu_heap_mint_signed h s k rx).
  move/heap.incluE => ->; exact mem_rx.

have rk_s_s' : [ rk ]_ s = [ rk ]_ s'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
have rx_s_s' : [ rx ]_ s = [ rx ]_ s'.
  mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
have x_y_st_st' : ([ x ]_ st' = [ y ]_st)%pseudo_expr.
  move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : exec_pseudo.
  case/syntax_m.seplog_m.exec0_assign_inv => _ -> /=.
  by syntax_m.seplog_m.assert_m.expr_m.Store_upd.

set postcond := (fun s h => _ /\ _ /\ ((_ |--> _ ** _ |--> (if _ then _ else _)) ** _ ) s h )%asm_assert in hoare_triple.
have {hoare_triple}hoare_triple_post_cond : (postcond ** assert_m.TT)%asm_assert s' h'.
  move: {hoare_triple}(mips_frame.frame_rule_R _ _ _ hoare_triple assert_m.TT (assert_m.inde_TT _) (mips_frame.inde_cmd_mult_TT _)).
  move/mips_seplog.hoare_prop_m.soundness.
  rewrite /while.hoare_semantics.
  move/(_ s h) => Hhoare_triple.
  lapply Hhoare_triple; last first.
    exists (heap_mint (signed k rx) s h \U heap_mint (signed k ry) s h),
      (h \D\ heap.dom (heap_mint (signed k rx) s h \U heap_mint (signed k ry) s h)).
    split; first by apply heap.disj_difs', seq_ext.inc_refl.
    split.
      apply heap.union_difsK; last by [].
      apply heap_prop_m.inclu_union; by [apply heap_inclu_heap_mint_signed | apply heap.inclu_proj].
    split; last by [].
    repeat (split=> //).
    rewrite HP Z_of_nat_Zabs_nat //; by apply min_u2Z.
    apply assert_m.con_cons.
    + apply (proj2 st_s_h x y); by [Uniq_neq | assoc_get_Some | assoc_get_Some].
    + exact mem_rx.
    + exact mem_ry.
  case=> _.
  by move/(_ _ _ exec_asm).

rewrite /state_mint; split.
- move=> z mz.
  case/assoc.get_union_Some_inv.
  + case/assoc.get_sing_inv => ? ?; subst z mz.
    apply mkVarSigned with len_y ptr_x (if len_y == zero32 then X else Y) => //.
    - by rewrite -rx_s_s'.
    - apply mkSignMagn => //.
      + by case: ifP.
      + rewrite x_y_st_st'; congruence.
      + rewrite x_y_st_st'.
        case: ifP => // /eqP len_x_0.
        by rewrite y_Y len_x_0 s2Z_u2Z_pos' // Z2uK.
      + case: hoare_triple_post_cond => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
        rewrite /postcond in Hh1.
        case: Hh1 => _ [_ Hh1].
        case: Hh1 => h11 [h12 [h11dh12 [h11Uh12 [Hh11 Hh12]]]].
        apply con_heap_mint_signed_cons with h11 => //.
        * rewrite h1Uh2 h11Uh12.
          apply heap.inclu_union_L.
          by heap_tac_m.Disj.
          apply heap.inclu_union_L => //.
          by apply heap.inclu_refl.
        * by rewrite -rx_s_s'.
        * case: ifP => _.
          by rewrite X_k.
          by rewrite Y_k.
        * by case: ifP.
  + move=> z_mz.
    have z_x : z <> x.
      move=> ?; subst z.
      case/assoc.get_union_Some_inv : z_mz => [xy | xd].
      apply assoc.get_sing_inv in xy.
      case: xy => tmp _; move: tmp.
      rewrite -/(x <> y); by Uniq_neq.
      apply assoc.get_Some_in_dom in xd.
      by rewrite xd in x_d.
    move: (proj2 st_s_h) => st_s_h2.
    move: {st_s_h}(proj1 st_s_h z mz).
    rewrite assoc.get_union_sing_neq //.
    move/(_ z_mz) => st_s_h1.
    have z_unchanged : ( [ z ]_ st = [ z ]_ st' )%pseudo_expr.
      Var_unchanged. rewrite /= mem_seq1; exact/negP/eqP.
    have Hd_unchanged : forall v r, assoc.get v d = Some r ->
      disj (mint_regs r) (mips_frame.modified_regs (copy_s_s rk rx ry a0 a1 a2 a3 a4)).
      move=> v r Hvr; rewrite [mips_frame.modified_regs _]/=; Disj_remove_dup.
      apply (disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
      apply/incP/inc_mint_regs.
      by move/assoc.get_Some_in_cdom : Hvr.
    case: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm
      (heap.dom (heap_mint (signed k ry) s h \U heap_mint (signed k rx) s h)) _ _
      exec_asm_proj) => Hst'_st'' [Hh'' H_h_h'].
    have <- : heap_mint mz s h = heap_mint mz s' h'.
      have [zy | zy] : z = y \/ z <> y. lia.
      - subst z.
        case/assoc.get_union_Some_inv : z_mz => z_mz; last first.
          apply assoc.get_Some_in_dom in z_mz.
          by rewrite z_mz in y_d.
        case/assoc.get_sing_inv : z_mz => _ ?; subst mz.
        case : hoare_triple_post_cond => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
        case: Hh1 => ry_s_s' [rk_s' Hh1].
        case: Hh1 => h11 [h12 [h11_d_h12 [h11_U_h12 [Hh11 Hh12]]]].
        case: (mem_ry) => k1 [k2 [k1_d_k2 [k1_U_k2 [Hk1 Hk2]]]].
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
        rewrite ry_s_s'.
        case: Hh12 => i1 [i2 [i1_d_i2 [i1_U_i2 [Hi1 Hi2]]]].
        move: (Hi1) => Hi1_save.
        apply assert_m.mapstos_inv_dom in Hi1; last by rewrite /= ry_s_s'.
        move: (Hi2) => Hi2_save.
        apply assert_m.mapstos_inv_dom in Hi2; last by rewrite Y_k.
        rewrite -ry_s_s'.
        rewrite Hi1.
        rewrite -Y_k.
        rewrite Hi2.
        rewrite h1_U_h2 h11_U_h12 i1_U_i2.
        rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
        rewrite heap.proj_union_R_dom; last by heap_tac_m.Disj.
        rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
        rewrite heap.proj_itself.
        rewrite heap.proj_union_L; last by rewrite -heap.disjE; heap_tac_m.Disj.
        rewrite heap.proj_union_R_dom; last by heap_tac_m.Disj.
        rewrite heap.proj_union_R_dom; last by heap_tac_m.Disj.
        rewrite heap.proj_itself.
        congr (_ \U _).
        apply: assert_m.strictly_exact_mapstos (conj Hk1 _).
        by apply: assert_m.mapstos_ext Hi1_save.
        apply: assert_m.strictly_exact_mapstos (conj Hk2 _).
        by apply: assert_m.mapstos_ext Hi2_save.

      - rewrite assoc.get_union_sing_neq // in z_mz.
        apply (heap_mint_state_invariant (heap_mint (signed k ry) s h \U
             heap_mint (signed k rx) s h) z st) => //.
        move=> rx0 Hrx0; mips_syntax.Reg_unchanged.
        apply (@disj_not_In _ (mint_regs mz)); last by [].
        apply/disj_sym/(Hd_unchanged z).
        exact z_mz.

        apply heap.disjhU.
        apply st_s_h2 with z y => //; by assoc_get_Some.
        apply st_s_h2 with z x => //; by assoc_get_Some.

      move: st_s_h1; apply var_mint_invariant; last exact z_unchanged.
      move=> rx0 Hrx0; mips_syntax.Reg_unchanged.
      apply (@disj_not_In _ (mint_regs mz)); last by [].
      have [zy | zy] : z = y \/ z <> y. lia.
      - subst z.
        rewrite assoc.get_union_sing_eq in z_mz.
        case: z_mz => ?; subst mz.
        rewrite [modified_regs _]/=.
        Disj_remove_dup.
        apply uniq_disj.
        rewrite [cat _ _]/=.
        by Uniq_uniq r0.
      - apply disj_sym, (Hd_unchanged z) => //.
        by rewrite assoc.get_union_sing_neq // in z_mz.
- case: hoare_triple_post_cond => [h1 [h2 [h1dh2 [h1Uh2 [[rx_s'_s [rk_s' Hh1]] HTT]]]]].
  case: Hh1 => h11 [h12 [h11dh12 [h11Uh12 [Hh11 Hh12]]]].

  have len_u' : heap.get '|u2Z ([rx ]_ s')%asm_expr / 4| h' = Some len_y.
    rewrite h1Uh2.
    apply heap.get_union_L => //.
    rewrite h11Uh12.
    apply heap.get_union_L => //.
    by apply assert_m.mapstos_get1 in Hh11.

  have ptr_x' : heap.get '|u2Z ([ rx ]_ s' `+ four32 )%asm_expr / 4| h' = Some ptr_x.
    rewrite h1Uh2.
    apply heap.get_union_L => //.
    rewrite h11Uh12.
    apply heap.get_union_L => //.
    by apply assert_m.mapstos_get2 in Hh11.

  have len_x' : heap.get '|u2Z [ ry ]_ s' / 4| h' = Some len_y.
    rewrite h1Uh2.
    apply heap.get_union_L => //.
    rewrite h11Uh12.
    apply heap.get_union_R => //.
    by apply assert_m.mapstos_get1 in Hh12.

  have Hlen_x : heap.get '|u2Z [ ry ]_ s / 4| h = Some len_y.
    apply assert_m.mapstos_get1 in mem_ry.
    by move/heap_get_heap_mint_inv in mem_ry.

  apply state_mint_part2_two_variables with st s h => //.
  + move/assert_m.mapstos_get2 : (mem_rx).
    move/heap_get_heap_mint_inv => ptr_x_get.
    move/assert_m.mapstos_get1 : (mem_rx).
    move/heap_get_heap_mint_inv => len_x_get.
    symmetry.
    apply dom_heap_mint_sign_state_invariant with x st len_x len_y => //.
    rewrite ptr_x_get.
    symmetry; exact ptr_x'.
    apply (state_mint_var_mint _ _ _ _ _ _ st_s_h); by assoc_get_Some.
    by apply (mips_syntax.dom_heap_invariant _ _ _ _ _ exec_asm).
  + symmetry.
    apply dom_heap_mint_sign_state_invariant with y st len_y len_y => //.
    apply assert_m.mapstos_get2 in mem_ry.
    move/heap_get_heap_mint_inv : mem_ry => ->.
    symmetry.
    apply assert_m.mapstos_get2 in Hh12.
    rewrite h1Uh2.
    apply heap.get_union_L => //.
    rewrite h11Uh12.
    by apply heap.get_union_R.
    apply (state_mint_var_mint _ _ _ _ _ _ st_s_h); by assoc_get_Some.
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
        move/eqP in Ht; subst t.
        apply (@disj_not_In _ (mint_regs (signed k ry))); last by [].
        Disj_remove_dup.
        rewrite /=.
        by Disj_uniq r0.
      - apply (@disj_not_In _ (mint_regs t)); last by [].
        Disj_remove_dup.
        apply/disj_sym/(disj_incl_LR Hdisj); last by apply incl_refl_Permutation; PermutProve.
        exact/incP/inc_mint_regs.
  + by Uniq_neq.
  + move: (mips_syntax.exec_deter_proj _ _ _ _ _ exec_asm _ _ _ exec_asm_proj); tauto.
Qed.

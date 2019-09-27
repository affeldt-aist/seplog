(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ssrZ ZArith_ext seq_ext machine_int uniq_tac multi_int.
Import MachineInt.
Require Import integral_type mips_bipl mips_seplog mips_tactics mips_frame.
Require Import mips_syntax mips_contrib.
Import expr_m.
Require Import simu.
Import simu_m.
Require Import multi_is_even_u_and_prg multi_is_even_u_triple.

Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope uniq_scope.
Local Open Scope assoc_scope.
Local Open Scope heap_scope.
Local Open Scope asm_expr_scope.
Local Open Scope asm_cmd_scope.

Lemma fwd_sim_b_multi_is_even_u_and rk ru rv a0 a1 u v d :
  uniq(u, v) -> uniq(rk, ru, rv, a0, a1, r0) ->
  fwd_sim_b (fun s st h =>
    state_mint ((u |=> unsign rk ru \U+ (v |=> unsign rk rv \U+ d ))) s st h)
  (var_e u \% nat_e 2 \= nat_e 0 \&& var_e v \% nat_e 2 \= nat_e 0)%pseudo_expr
  (multi_is_even_u_and rk ru rv a0 a1) (bne a0 r0).
Proof.
move=> u_v Hregs.
- rewrite /fwd_sim_b => s st he Hstate_mint.
  have Hset_rx : uniq(rk, ru, a0, r0) by Uniq_uniq r0.
  move: (size_Z2ints '|u2Z [rk]_ st| 32 ([u ]_ s)%pseudo_expr).
  move/(multi_is_even_u_triple _ _ _ Hset_rx _ _) => {Hset_rx} Heven_rx.
  have Hset_ry : uniq(rk, rv, a1, r0) by Uniq_uniq r0.
  move: (size_Z2ints '|u2Z [rk ]_ st| 32 ([v ]_ s)%pseudo_expr).
  move/(multi_is_even_u_triple _ _ _ Hset_ry _ _) => {Hset_ry} Heven_ry.
  have [st' Hst'] : exists st', Some (st, he) -- multi_is_even_u_and rk ru rv a0 a1 ---> Some (st', he).
    have [[st' he'] Hst'] : exists st', Some (st, he) -- multi_is_even_u_and rk ru rv a0 a1 ---> Some st'.
      apply constructive_indefinite_description'.
      apply mips_seplog.hoare_prop_m.termi with (P :=
        ((fun st0 h => u2Z [rk ]_ st0 = u2Z [rk ]_ st /\ [ru ]_ st0 = [ru ]_ st /\
          (var_e ru |--> Z2ints 32 '|u2Z [rk ]_ st| ([u ]_ s)%pseudo_expr)%asm_assert
          st0 h) **
        ((fun st0 h => u2Z [rk ]_ st0 = u2Z [rk ]_ st /\ [rv ]_ st0 = [rv ]_ st /\
          (var_e rv |--> Z2ints 32 '|u2Z ([rk ]_ st)| ([v ]_ s)%pseudo_expr)%asm_assert
          st0 h) ** assert_m.TT))%asm_assert) (Q := assert_m.TT).
      + eapply while.hoare_seq.
        * apply frame_rule_R.
          - rewrite Z_of_nat_Zabs_nat in Heven_rx; last exact: min_u2Z.
            by apply Heven_rx.
          - by Inde_frame.
          - move=> ?; by Inde_mult.
        * eapply while.hoare_seq.
          - apply mips_contrib.hoare_con_comm_pre.
            apply mips_contrib.hoare_con_assoc_pre.
            apply frame_rule_R.
            + rewrite Z_of_nat_Zabs_nat in Heven_ry; last exact: min_u2Z.
              by apply Heven_ry.
            + Inde_frame.
              * apply assert_m.inde_imp.
                apply assert_m.inde_get.
                by Uniq_not_In.
              * apply assert_m.inde_imp.
                apply assert_m.inde_get.
                by Uniq_not_In.
            + move=> ?; by Inde_mult.
          - by apply cmd_and_true.
      (* termination proof *)
      + move=> st0 h0 H0.
        by apply constructive_indefinite_description, mips_syntax.no_while_terminate.
      + exists (heap_mint (unsign rk ru) st he).
        exists (heap_mint (unsign rk rv) st he \U (he \D\
            iota '|u2Z ([ru ]_ st) / 4| '|u2Z ([rk ]_ st)| ++
            iota '|u2Z ([rv ]_ st) / 4| '|u2Z ([rk ]_ st)|)).
        split.
        * apply heap.disjhU.
          - apply (proj2 Hstate_mint u v).
            by Uniq_neq.
            by assoc_get_Some.
            by assoc_get_Some.
          - apply heap.proj_difs_disj.
            by rewrite inc_app_L.
        * split.
          - by rewrite heap.unionA -heap.proj_app -heap.proj_difs.
          - split.
            + split.
              * done.
              * apply (state_mint_var_mint _ _ _ _ u (unsign rk ru)) in Hstate_mint; last by assoc_get_Some.
                rewrite /var_mint in Hstate_mint; case: Hstate_mint; tauto.
            + apply assert_m.con_cons; last by [].
              * apply heap.proj_difs_disj.
                by rewrite inc_app_R.
              * split; first by reflexivity.
                apply (state_mint_var_mint _ _ _ _ v (unsign rk rv)) in Hstate_mint; last by assoc_get_Some.
                rewrite /var_mint in Hstate_mint; case: Hstate_mint; tauto.
    exists st'.
    suff : he = he' by move=> X; rewrite -X in Hst'.
    by apply (no_sw_heap_invariant _ _ _ Hst' (refl_equal _) _ _ _ _ (refl_equal _) (refl_equal _)).
  exists st'; split; first by [].
  (* on decompose l'execution de Hst' *)
  case/mips_cmd.semop_prop_m.exec_seq_inv : Hst' => st1 [] Hst1.
  case/mips_cmd.semop_prop_m.exec_seq_inv=> st2 [] Hst2 Hst'.
  destruct st1 as [[st1 he1]|]; last first.
    destruct st2 as [[st2 he2]|]; last first.
      by move/semop_prop_m.from_none : Hst'.
    by move/semop_prop_m.from_none : Hst2.
  have ? : he = he1 by eapply (no_sw_heap_invariant _ _ _ Hst1).
  subst he1.
  destruct st2 as [[st2 he2]|]; last by move/semop_prop_m.from_none : Hst'.
  have Htmp : he = he2 by eapply (no_sw_heap_invariant _ _ _ Hst2).
  subst he2.
  have Hry : [rv ]_ st = [rv ]_ st1.
    Reg_unchanged. rewrite [modified_regs _ ]/=; by Uniq_not_In.
  have Hrk : [rk ]_ st = [rk ]_ st1.
    Reg_unchanged. rewrite [modified_regs _ ]/=; by Uniq_not_In.
  split.
  + rewrite /= /ZIT.eqb /ZIT.rem.
    case/andP. move/eqP => Heval_b1. move/eqP => Heval_b2.
    (* prove that even "is_even" refines "mod 2", both calls return "1", "1 & 1 = 1", therefore
       the result is not 0 *)
    have Ha0 : [ a0 ]_ st1 = one32.
      clear Heven_ry.
      move/hoare_prop_m.soundness : (Heven_rx [ru]_st).
      rewrite /while.hoare_semantics.
      move/(_ st (heap_cut he '|u2Z ([ru ]_ st) / 4| '|u2Z ([rk ]_ st)|)).
      rewrite Z_of_nat_Zabs_nat; last exact/min_u2Z.
      have Htmp : (var_e%asm_expr ru |-->
        Z2ints 32 '|u2Z ([rk ]_ st)| ([u ]_ s)%pseudo_expr)%asm_assert
        st
        (heap_cut he '|u2Z ([ru ]_ st) / 4| '|u2Z ([rk ]_ st)|).
        apply (state_mint_var_mint _ _ _ _ u (unsign rk ru)) in Hstate_mint; last by assoc_get_Some.
        rewrite /var_mint in Hstate_mint; case: Hstate_mint; tauto.
      move/(_ (conj (refl_equal _) (conj (refl_equal _) Htmp))) => Heven_rx'.
      eapply (proj2 Heven_rx'); clear Heven_rx'.
      eapply triple_exec_proj; first exact: (Heven_rx [ru]_st).
        split.
        rewrite Z_of_nat_Zabs_nat //; exact/min_u2Z.
        split; first by reflexivity.
        exact Htmp.
        by apply Hst1.
      apply (state_mint_var_mint _ _ _ _ u (unsign rk ru)) in Hstate_mint; last by assoc_get_Some.
      rewrite lSum_Z2ints_pos.
      + exact/Zmod_2_Zeven
      + rewrite /var_mint in Hstate_mint. case: Hstate_mint.
        rewrite -ZbetaE; tauto.
    have Ha1 : [a1]_st2 = one32.
      clear Heven_rx.
      move/hoare_prop_m.soundness : (Heven_ry [rv]_st).
      rewrite /while.hoare_semantics.
      move/(_ st1 (heap_cut he '|u2Z [rv ]_ st / 4| '|u2Z ([rk ]_ st)|)).
      have Htmp : u2Z ([rk ]_ st1) = Z_of_nat '|u2Z ([rk ]_ st)| /\
        (var_e rv |--> Z2ints 32 '|u2Z ([rk ]_ st)| ([v ]_ s)%pseudo_expr)%asm_assert
        st1
        (heap_cut he '|u2Z ([rv ]_ st) / 4| '|u2Z ([rk ]_ st)|).
        split.
        rewrite Z_of_nat_Zabs_nat; last exact/min_u2Z.
        congr (Z<=u _).
        symmetry.
        Reg_unchanged. rewrite [modified_regs _]/=; by Uniq_not_In.
        apply (state_mint_var_mint _ _ _ _ v (unsign rk rv)) in Hstate_mint; last by assoc_get_Some.
        rewrite /var_mint /heap_mint in Hstate_mint.
        case: Hstate_mint => _ _.
        apply assert_m.mapstos_ext => /=.
        congruence.
      case: Htmp => Htmp1 Htmp2.
      symmetry in Hry.
      move/(_ (conj Htmp1 (conj Hry Htmp2))) => Heven_ry'.
      eapply (proj2 Heven_ry'); clear Heven_ry'.
      eapply triple_exec_proj; first exact: (Heven_ry [rv]_st).
        tauto.
        by apply Hst2.
      apply (state_mint_var_mint _ _ _ _ v (unsign rk rv)) in Hstate_mint; last by assoc_get_Some.
      rewrite lSum_Z2ints_pos.
      + by apply Zmod_2_Zeven.
      + rewrite /var_mint in Hstate_mint; case: Hstate_mint.
        rewrite -ZbetaE; tauto.
    have {}Ha0 : [a0 ]_ st2 = one32.
      rewrite -Ha0.
      symmetry. Reg_unchanged. rewrite [modified_regs _ ]/=; by Uniq_not_In.
    move/semop_prop_m.exec_cmd0_inv : Hst'.
    case/exec0_and_inv => Hst'.
    rewrite Ha1 Ha0 int_and_idempotent in Hst'.
    rewrite {1}Hst'.
    Reg_upd.
    by rewrite store.get_r0 !Z2uK.
  + rewrite /= /ZIT.eqb /ZIT.rem.
    apply contraR.
    case/nandP.
    * move/eqP => Heval_b.
      have Ha0 : [a0]_st' = zero32.
        have Ha0 : [a0]_st1 = zero32.
          clear Heven_ry.
          move/hoare_prop_m.soundness : (Heven_rx [ru]_st).
          rewrite /while.hoare_semantics.
          move/(_ st (heap_cut he '|u2Z ([ru ]_ st) / 4| '|u2Z ([rk ]_ st)|)).
          have Htmp : u2Z [rk ]_ st = Z_of_nat '|u2Z ([rk ]_ st)| /\
            (var_e ru |--> Z2ints 32 '|u2Z ([rk ]_ st)| ([u ]_ s)%pseudo_expr)%asm_assert st
            (heap_cut he '|u2Z ([ru ]_ st) / 4| '|u2Z ([rk ]_ st)|).
            split.
            by rewrite Z_of_nat_Zabs_nat; last exact: min_u2Z.
            apply (state_mint_var_mint _ _ _ _ u (unsign rk ru)) in Hstate_mint; last by assoc_get_Some.
            rewrite /var_mint in Hstate_mint; case: Hstate_mint; tauto.
          case: Htmp => Htmp1 Htmp2.
          move/(_ (conj Htmp1 (conj (refl_equal _) Htmp2))) => Heven_rx'.
          eapply (proj2 Heven_rx'); clear Heven_rx'.
          eapply triple_exec_proj; first exact: (Heven_rx [ru]_st).
          tauto.
          by apply Hst1.
          apply (state_mint_var_mint _ _ _ _ u (unsign rk ru)) in Hstate_mint; last by assoc_get_Some.
          rewrite lSum_Z2ints_pos.
          + by apply not_Zmod_2_Zodd.
          + rewrite /var_mint in Hstate_mint; case: Hstate_mint.
            rewrite -ZbetaE; tauto.
        have Ha0' : [ a0 ]_ st2 = zero32.
          rewrite -Ha0.
          symmetry.
          Reg_unchanged. rewrite [modified_regs _ ]/=; by Uniq_not_In.
        move/semop_prop_m.exec_cmd0_inv : Hst'.
        case/exec0_and_inv => Hst'.
        rewrite Ha0' int_andC int_and_0 in Hst'.
        rewrite Hst'.
        by Reg_upd.
      by rewrite Ha0 store.get_r0 eqxx.
    * move/eqP => Heval_b.
      have Ha0 : [a0]_st' = zero32.
        have Ha1 : [a1]_st2 = zero32.
          clear Heven_rx.
          move/hoare_prop_m.soundness : (Heven_ry [rv]_st).
          rewrite /while.hoare_semantics.
          move/(_ st1 (heap_cut he '|u2Z ([rv ]_ st) / 4| '|u2Z ([rk ]_ st)|)).
          have Htmp : u2Z ([rk ]_ st1) = Z_of_nat '|u2Z ([rk ]_ st)| /\
            (var_e rv |--> Z2ints 32 '|u2Z ([rk ]_ st)| ([v ]_ s)%pseudo_expr)%asm_assert st1
            (heap_cut he '|u2Z ([rv ]_ st) / 4| '|u2Z ([rk ]_ st)|).
            split.
            - rewrite Z_of_nat_Zabs_nat; last exact/min_u2Z.
              f_equal.
              symmetry.
              Reg_unchanged. rewrite [modified_regs _]/=; by Uniq_not_In.
              apply (state_mint_var_mint _ _ _ _ v (unsign rk rv)) in Hstate_mint; last by assoc_get_Some.
              rewrite /var_mint /heap_mint in Hstate_mint.
              case: Hstate_mint => _ _.
              apply assert_m.mapstos_ext => /=; exact Hry.
          case: Htmp => H1 H2.
          symmetry in Hry.
          move/(_ (conj H1 (conj Hry H2))) => Heven_ry'.
          eapply (proj2 Heven_ry'); clear Heven_ry'.
          eapply triple_exec_proj; first exact: (Heven_ry [rv]_st).
          tauto.
          by apply Hst2.
          apply (state_mint_var_mint _ _ _ _ v (unsign rk rv)) in Hstate_mint; last by assoc_get_Some.
          rewrite lSum_Z2ints_pos.
          - by apply not_Zmod_2_Zodd.
          - rewrite /var_mint in Hstate_mint; case: Hstate_mint.
            rewrite -ZbetaE; tauto.
        move/semop_prop_m.exec_cmd0_inv : Hst'.
        case/exec0_and_inv.
        rewrite Ha1 int_and_0 => ->.
        by Reg_upd.
      by rewrite Ha0 store.get_r0 eqxx.
Qed.

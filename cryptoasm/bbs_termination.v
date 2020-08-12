(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Classical Epsilon Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Require mips_syntax.
Require Import mont_mul_strict_prg bbs_prg.
Require Import mont_mul_strict_termination mont_square_strict_termination.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.
Import expr_m.

Lemma termination_inner_loop
  s h j32 L_ l j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w :
  uniq(L_, l, j, thirtytwo, k, alpha, x, y, m, one, ext, int_, X_, Y_, M_, quot, C_, t, s_, b2k, B2K_, w', w, r0) ->
  u2Z [thirtytwo]_s - u2Z [j]_s = Z_of_nat j32 ->
  { sf | (Some (s, h) --
    while.while (bne j thirtytwo)
    (mont_mul_strict_init k alpha x x y m one ext int_ X_ B2K_ Y_ M_ quot C_ t s_;
      mont_mul_strict_init k alpha y b2k x m one ext int_ Y_ B2K_ X_ M_ quot C_ t s_;
      lw w' zero16 x;
      andi w' w' one16;
      sllv w' w' j;
      cmd_or w w w';
      addiu j j one16) ---> sf) }.
Proof.
move=> Hset Hj32.
move: j32 s h Hj32.
elim.
- (* case j = 32 *) move=> s h Hj32.
  exists (Some (s, h)).
  apply while.exec_while_false.
  rewrite /= in Hj32 *.
  apply/negPn/eqP; lia.
- (* case j < 32 *) move=> j32 IHj32 s h Hj32; apply exists_while.
  + rewrite Z_S in Hj32; rewrite /=; apply/eqP; lia.
  + apply exists_seq_P2 with (fun st => u2Z [thirtytwo]_(fst st) - u2Z [j]_(fst st) = Z_of_nat j32).
    * apply exists_seq_P with (fun s' => forall st, s' = Some st ->
      u2Z [thirtytwo]_(fst st) - u2Z [j]_(fst st) = Z_of_nat (S j32)).
      - have : uniq(k, alpha, x, y, m, one, ext, int_, X_, B2K_, Y_, M_, quot, C_, t, s_, r0) by Uniq_uniq r0.
        case/(mont_square_strict_init_termination s h) => si Hsi.
        exists si; split; first by assumption.
        move=> [st h'] Hst /=; subst si.
        have <- : [thirtytwo ]_ s = [thirtytwo ]_ st.
          mips_syntax.Reg_unchanged. rewrite [mips_frame.modified_regs _]/=. by Uniq_not_In.
        have <- : [ j ]_ s = [ j ]_ st.
          mips_syntax.Reg_unchanged. rewrite [mips_frame.modified_regs _]/=. by Uniq_not_In.
        by [].
      - move=> [[si hi] |] Hsi; last by exists None; split; by [apply while.exec_none | ].
        apply exists_seq_P with (fun s' => forall st, s' = Some st ->
          u2Z [thirtytwo]_(fst st) - u2Z [j]_(fst st) = Z_of_nat (S j32)).
        + have : uniq(k, alpha, y, b2k, x, m, one, ext, int_, Y_, B2K_, X_, M_, quot, C_, t, s_, r0) by Uniq_uniq r0.
          case/(mont_mul_strict_init_termination si hi) => sj Hsj.
          exists sj; split; first by [].
          move=> [st h'] Hst /=; subst sj.
          have <- : [ j ]_si = [ j ]_ st.
            mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
          have <- : [ thirtytwo ]_si = [ thirtytwo ]_ st.
            mips_syntax.Reg_unchanged. simpl mips_frame.modified_regs. by Uniq_not_In.
          by move: (Hsi _ (refl_equal _)).
        + move=> [[sj hj] |] Hsj; last by exists None; split; by [apply while.exec_none | ].
          exists_lw l0 Hl0 z Hz.
          apply exists_andi_seq_P.
          repeat Reg_upd.
          apply exists_sllv_seq_P.
          repeat Reg_upd.
          apply exists_or_seq_P.
          repeat Reg_upd.
          apply exists_addiu_P.
          simpl fst.
          repeat Reg_upd.
          rewrite Z_S in Hsj.
          move: {Hsj}(Hsj _ (refl_equal _)) => Hsj.
          simpl fst in Hsj.
          rewrite u2Z_add sext_Z2u // Z2uK //.
          lia.
          move: (max_u2Z ([thirtytwo]_sj)) => ?; lia.
    * move=> [si hi] Hj32'.
      case: {IHj32}(IHj32 si hi Hj32') => sf IHj32.
      by exists sf.
Qed.

Lemma termination_outer_loop
  s h ni i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w :
  uniq(i, L_, l, n, j, thirtytwo, k, alpha, x, y, m, one, ext, int_, X_, Y_, M_, quot, C_, t, s_, b2k, B2K_, w', w, r0) ->
  u2Z [n]_s - u2Z [i]_s = Z_of_nat (S ni) ->
  { sf | (Some (s, h) --
    addiu j r0 zero16;
    addiu w r0 zero16;
    while.while (bne j thirtytwo)
    (mont_mul_strict_init k alpha x x y m one ext int_ X_ B2K_ Y_ M_ quot C_ t s_;
      mont_mul_strict_init k alpha y b2k x m one ext int_ Y_ B2K_ X_ M_ quot C_ t s_;
      lw w' zero16 x;
      andi w' w' one16;
      sllv w' w' j;
      cmd_or w w w';
      addiu j j one16);
    sw w zero16 L_;
    addiu L_ L_ four16;
    addiu i i one16 ---> sf) /\
  (forall st, sf = Some st -> u2Z [n]_(fst st) - u2Z [i]_(fst st) = Z_of_nat ni) }.
Proof.
move=> Hset Hni.
apply exists_addiu_seq_P.
rewrite sext_0 addi0 store.get_r0.
apply exists_addiu_seq_P.
rewrite sext_0 addi0 store.get_r0.
apply exists_seq_P with (fun sf => forall st, sf = Some st ->
  u2Z [n]_(fst st) - u2Z [i]_(fst st) = Z_of_nat (S ni)).
- set _s := store.upd _ _ _.
  have [j32 Hj32 ]: { j32 | u2Z [thirtytwo]_ _s - u2Z [j]_ _s = Z_of_nat j32 }.
    apply Z_of_nat_complete_inf.
    rewrite /_s.
    repeat Reg_upd.
    rewrite Z2uK // subZ0; exact: min_u2Z.
  have : uniq(L_, l, j, thirtytwo, k, alpha, x, y, m, one, ext, int_, X_, Y_, M_, quot, C_, t, s_, b2k, B2K_, w', w,r0) by Uniq_uniq r0.
  move/(termination_inner_loop _s h j32).
  move/(_ Hj32).
  case=> si Hsi.
  exists si; split; first by [].
  move=> st Hst; subst si.
  destruct st as [s' h'].
  have <- : [n ]_ (_s) = [n ]_ (s').
    apply (mips_syntax.reg_unchanged _ _ _ _ _ Hsi).
    rewrite [mips_frame.modified_regs _]/=.
    by Uniq_not_In.
  have <- : [i ]_ (_s) = [i ]_ (s').
    apply (mips_syntax.reg_unchanged _ _ _ _ _ Hsi).
    rewrite [mips_frame.modified_regs _]/=.
    by Uniq_not_In.
  rewrite /_s; by repeat Reg_upd.
- move=> [[si hi ] |] Hi.
  + exists_sw_P l0 Hl0 z Hz.
    apply exists_addiu_seq_P.
    apply exists_addiu_P.
    rewrite /=.
    repeat Reg_upd.
    move: (Hi _ (refl_equal _)).
    rewrite Z_S /= => X.
    rewrite u2Z_add sext_Z2u // Z2uK //.
    lia.
    move: (max_u2Z ([n]_si)) => ?; lia.
  + exists None; split; by [apply while.exec_none | ].
Qed.

Lemma bbs_termination s_init h_init i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w :
  uniq(i, L_, l, n, j, thirtytwo, k, alpha, x, y, m, one, ext, int_, X_, Y_, M_, quot, C_, t, s_, b2k, B2K_, w', w, r0) ->
  { final_state | Some (s_init, h_init) --
    bbs i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w --->
    final_state }.
Proof.
move=> Hset.
rewrite /bbs.
apply exists_addiu_seq.
rewrite sext_0 addi0 store.get_r0.
apply exists_addiu_seq.
repeat Reg_upd.
rewrite sext_0 addi0.
move Hs0 : (store.upd _ _ _) => s0.
have [ni Hni] : { ni | u2Z [n]_s0 - u2Z [i]_s0 = Z_of_nat ni }.
  have : { zi | u2Z [n]_s0 - u2Z [i]_s0 = zi } by eapply exist; reflexivity.
  case => zi.
  rewrite -Hs0.
  repeat Reg_upd.
  rewrite /zero32 Z2uK // subZ0 => Hzi.
  move: (min_u2Z [n]_s_init).
  rewrite Hzi => Hmin.
  case: (Z_of_nat_complete_inf _ Hmin) => ni Hni.
  exists ni; by rewrite -Hni.
move: ni s0 Hni h_init {s_init Hs0}; elim.
- move=> s0 Hni h0.
  eapply exist.
  apply while.exec_while_false.
  rewrite /= in Hni *.
  apply/negPn/eqP; lia.
- move=> ni IH s0 Hni h0.
  move: {Hset}(termination_outer_loop s0 h0 ni i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w Hset Hni) => [ sf [Hsf Hni'] ].
  destruct sf as [[sf hf] |].
  * simpl fst in Hni'.
    case: (IH sf (Hni' _ Logic.eq_refl) hf) => sf0 Hsf0.
    exists sf0.
    eapply while.exec_while_true => /=.
    - rewrite Z_S in Hni; apply/eqP; lia.
    - exact: Hsf.
    - exact: Hsf0.
  * exists None.
    eapply while.exec_while_true; eauto.
    - rewrite /=. apply/eqP. by omegaz. (*rewrite Z_S in Hni; apply/eqP. lia.*)
    - exact/while.exec_none.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_tactics mips_frame.
Require Import multi_is_even_u_prg abs_triple multi_is_even_u_triple.
Require Import pick_sign_triple multi_is_even_s_prg.
Import expr_m.
Import assert_m.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope multi_int_scope.

Section multi_is_even_s.

Variables rx rk a0 a1 : reg.

Lemma multi_is_even_s_triple : uniq(rx, rk, a0, a1, r0) ->
  forall nk A slen ptr, size A = nk ->
    s2Z slen <> - 2 ^ 31 ->
    s2Z slen = sgZ (s2Z slen) * Z_of_nat nk ->
    {{ (var_e rx |--> slen :: ptr :: nil) ** (int_e ptr |--> A) }}
    multi_is_even_s rx rk a0 a1
    {{ fun s h => (Zeven (sgZ (s2Z slen) * \S_{ nk } A) -> [a1]_s = one32) /\
                  (Zodd (sgZ (s2Z slen) * \S_{ nk } A) -> [a1]_s = zero32) }}.
Proof.
move=> Hset nk A slen ptr A_nk slen_weird slen_nk.
rewrite /multi_is_even_s.
apply while.hoare_seq with ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) **
 !(fun s => (slen = zero32 -> [a1]_s = zero32) /\
            (slen <> zero32 -> [a1]_s <> zero32))).

apply (hoare_prop_m.hoare_stren (fun s h => exists vx, [rx]_s = vx /\
  (var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) s h)).
  move=> s h H; by exists ([rx ]_ s).

apply pull_out_exists => vx.

eapply (before_frame (var_e rx \+ int_e four32 |--> ptr :: nil ** int_e ptr |--> A)).
apply frame_rule_R; last by done.
have : uniq(rx,a0,a1,r0) by Uniq_uniq r0.
move/(pick_sign_triple assert_m.TT assert_m.emp vx slen)/(_ (inde_emp _) (inde_TT _)).
apply.
rewrite [modified_regs _]/=.
by Inde.

move=> s h [rx_vx H].
rewrite -assert_m.mapsto2_mapstos assert_m.conAE in H.
move: H.
apply assert_m.monotony => // h1 Hh1.
repeat (split => //).
by rewrite assert_m.con_emp_equiv.
by rewrite -assert_m.mapsto1_mapstos.

move=> s h H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
case: Hh1 => Hrx [Ha0 [Ha1 [Hsgn [Hh1 _]]]].
apply assert_m.con_and_bang_R.
rewrite assert_m.con_emp_equiv in Hh1.
rewrite -assert_m.mapsto2_mapstos.
rewrite assert_m.conAE.
exists h1, h2; repeat (split => //).
by rewrite -assert_m.mapsto1_mapstos in Hh2.

split => Hslen.
  symmetry in Ha1.
  rewrite Hslen s2Z_u2Z_pos' Z2uK //= in Ha1.
  symmetry in Ha1.
  rewrite -> Zsgn_null in Ha1.
  rewrite (_ : 0 = s2Z zero32) in Ha1; last by rewrite s2Z_u2Z_pos' Z2uK.
  by apply s2Z_inj in Ha1.
contradict Hslen.
rewrite Hslen s2Z_u2Z_pos' Z2uK //= in Ha1.
symmetry in Ha1.
rewrite -> Zsgn_null in Ha1.
rewrite (_ : 0 = s2Z zero32) in Ha1; last by rewrite s2Z_u2Z_pos' Z2uK.
by apply s2Z_inj in Ha1.

apply while.hoare_ifte.

apply hoare_addiu' => s h H.
rewrite /wp_addiu.
repeat Reg_upd.
case: H => H1 H2.
rewrite /= store.get_r0 Z2uK // in H2.
move/eqP in H2.
apply assert_m.con_and_bang_inv_R in H1.
case: H1 => H1 H3.
rewrite add0i.
split.
  move=> _; by rewrite sext_Z2u.
case: H3 => H3 H3'.
case: (dec_int slen zero32) => X.
  subst slen.
  by rewrite s2Z_u2Z_pos' Z2uK.
apply H3' in X.
suff : False by done.
apply X.
rewrite (_ : 0 = u2Z zero32) in H2; last by rewrite Z2uK.
by apply u2Z_inj in H2.

apply (hoare_prop_m.hoare_stren (!(fun s => slen <> zero32) **
  (var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A))).

move=> s h [H Htest].
rewrite /= store.get_r0 Z2uK // in Htest.
apply assert_m.con_and_bang_inv_R in H.
apply assert_m.con_and_bang_L.
tauto.
decompose [and] H; clear H.
move/H2.
by move=> abs; rewrite abs Z2uK in Htest.

apply pull_out_bang => slen_zero.

apply hoare_lw_back_alt'' with (
  (var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) **
  (!fun s => [rk]_s = slen))%mips_expr.
move=> s h H.
exists slen; split.
move: H.
rewrite -assert_m.mapsto2_mapstos.
rewrite assert_m.conAE.
apply assert_m.monotony => //= h1.
apply assert_m.mapsto_ext => //=.
by rewrite sext_Z2u // addi0.
rewrite /update_store_lw.
apply assert_m.con_and_bang_R.
by Assert_upd.
by repeat Reg_upd.

apply while.hoare_seq with ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) **
       !(fun s => u2Z ([rk ]_ s) = `| s2Z slen |)).
eapply (before_frame (var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A)).
apply frame_rule_R.
have : uniq(rk, a0, r0) by Uniq_uniq r0.
move/abs_triple_bang/(_ slen slen_weird); apply.
rewrite [modified_regs _]/=; by Inde.
done.
move=> s h; by rewrite assert_m.conCE.
move=> s h.
rewrite assert_m.conCE => H.
suff : s2Z ([rk ]_ s) = u2Z ([rk ]_ s).
  move=> Hsuff.
  apply assert_m.con_and_bang_inv_R in H.
  case: H => H Hrk.
  apply assert_m.con_and_bang_R => //; congruence.
rewrite s2Z_u2Z_pos //.
apply assert_m.con_and_bang_inv_R in H.
case: H => _ ->.
exact/normZ_ge0.

apply hoare_lw_back_alt'' with (
      (var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) **
      !(fun s => u2Z ([rk ]_ s) = `| s2Z slen |) **
      !(fun s => [a0]_s = ptr)).
move=> s h H.
exists ptr; split.
  rewrite -assert_m.mapsto2_mapstos in H.
  rewrite 2!assert_m.conAE assert_m.conCE 2!assert_m.conAE in H.
  move: H.
  apply assert_m.monotony => // h1.
  apply assert_m.mapsto_ext => //=.
  by rewrite sext_Z2u.
rewrite /update_store_lw -assert_m.conAE.
apply assert_m.con_and_bang_R.
Assert_upd.
by repeat Reg_upd.

eapply (before_frame (var_e rx |--> slen :: ptr :: nil)).
apply frame_rule_R; last by done.
have : uniq(rk, a0, a1, r0) by Uniq_uniq r0.
move/multi_is_even_u_triple/(_ nk A ptr A_nk); by apply.
rewrite [modified_regs _]/=; by Inde.

move=> s h H.
rewrite -assert_m.mapsto2_mapstos !assert_m.conAE in H.
rewrite assert_m.conCE -assert_m.mapsto2_mapstos !assert_m.conAE.
move: H; apply assert_m.monotony => // h1.
apply assert_m.monotony => // h2 Hh2.
rewrite -assert_m.conAE in Hh2.
apply assert_m.con_and_bang_inv_R in Hh2.
case: Hh2 => Hh2 Ha0.
apply assert_m.con_and_bang_inv_R in Hh2.
case: Hh2 => Hh2 Hrk.
split.
  rewrite Hrk slen_nk normZM Zabs_Zsgn_1; first by rewrite mul1Z Zabs_Z_of_nat.
  contradict slen_zero.
  rewrite (_ : 0 = s2Z (Z2u 32 0)) in slen_zero; last by rewrite s2Z_u2Z_pos' // Z2uK.
  by move/s2Z_inj : slen_zero.
split=> //.
move: Hh2; by apply assert_m.mapstos_ext.

move=> s h H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
case: Hh1 => rk_nk [a0_ptr [Hh1 [Heven Hodd]]].
split.
  case/Zeven_mult_inv => //.
  have : s2Z slen <> 0.
    contradict slen_zero.
    rewrite (_ : 0 = s2Z zero32) in slen_zero; last by rewrite s2Z_u2Z_pos' // Z2uK.
    by apply s2Z_inj in slen_zero.
  by move/Zodd_Zsgn/Zodd_not_Zeven.
by case/Zodd_mult_inv.
Qed.

End multi_is_even_s.

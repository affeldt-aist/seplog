(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_frame mips_mint mips_tactics.
Import expr_m.
Import assert_m.
Require Import multi_halve_s_prg multi_is_zero_u_triple multi_zero_s_triple.
Require Import abs_triple multi_halve_u_triple multi_incr_u_triple.
Require Import multi_is_even_u_triple multi_halve_s_noneucl_triple.

Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.
Local Open Scope multi_int_scope.

Lemma multi_halve_s_triple_gen rk a a0 i tmp prev next : uniq(a, a0, i, tmp, prev, next, rk, r0) ->
  forall nk, Z_of_nat nk < 2 ^^ 31 ->
    forall va, u2Z va + 4 * 2 < \B^1 ->
    forall ptr, u2Z ptr + 4 * Z_of_nat nk < \B^1 ->
      forall slen, s2Z slen = Z.sgn (s2Z slen) * Z_of_nat nk ->
        forall A, size A = nk ->
          Z.sgn (s2Z slen) = Z.sgn (Z.sgn (s2Z slen) * \S_{ nk } A) (* so that A cannot be zero with slen <> 0*) ->
      {{ fun s h => [ a ]_s = va /\
        (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h }}
      multi_halve_s a a0 i tmp prev next rk
      {{ fun s h => exists slen' A',
        size A' = nk /\
        s2Z slen' = Z.sgn (s2Z slen') * Z_of_nat nk /\
        Z.sgn (s2Z slen') = Z.sgn (Z.sgn (s2Z slen') * \S_{ nk } A') /\
        [ a ]_s = va /\
        (var_e a |--> slen' :: ptr :: nil ** int_e ptr |--> A') s h /\
        2 * Z.sgn (s2Z slen') * \S_{ nk } A' + u2Z ([prev]_s `>> 31) = Z.sgn (s2Z slen) * \S_{ nk } A
      }}.
Proof.
move=> Hnodup nk nk_231 va va_fit ptr ptr_fit slen slen_nk A A_nk slen_A.
rewrite /multi_halve_s.

(** lw rk zero16 a ; *)

apply hoare_lw_back_alt'' with (
  !(fun s => [ rk ]_s = slen) **
  (fun s h => ([a ]_ s) = va /\
    ((var_e a |--> slen :: ptr :: nil) ** (int_e ptr |--> A)) s h)).

move=> s h [Ha Hmem].
exists slen; split.
  move: Hmem.
  rewrite -mapsto2_mapstos.
  rewrite conAE.
  apply monotony => // h1.
  apply mapsto_ext => //=.
  by rewrite sext_Z2u // addi0.

rewrite /update_store_lw.
apply store_upd_con.
apply con_and_bang_L; repeat Reg_upd => //.
split; first by [].
by Assert_upd.

apply hoare_ifte_bang.

  (* size = 0 *)

  apply hoare_addiu' => s h H.
  apply con_and_bang_inv_R in H.
  case: H => H.
  rewrite [in X in X -> _]/=.
  move/eqP/u2Z_inj.
  rewrite store.get_r0 => Hr.
  case: H => h1 [h2 [h1dh2 [h1Uh2 [[Hh1 ?] [a_va Hh2]]]]]; subst h1.
  clear h1dh2.
  rewrite heap.unioneh in h1Uh2; subst h2.
  rewrite /wp_addiu.
  subst slen.
  exists zero32, A.
  repeat Reg_upd.
  split; first by [].
  rewrite !s2Z_u2Z_pos' // ?Z2uK //; last by rewrite Hr Z2uK.
  split; first by Assert_upd.
  split; first by reflexivity.
  split; first by [].
  split.
    rewrite -Hr.
    by Assert_upd.
  by rewrite sext_Z2u // addi0 Hr shrl_Z2u_0 Z2uK // addZ0.

(* size <> 0 *)

apply hoare_prop_m.hoare_stren with (
  !(fun s => slen != zero32) **
  !(fun s => ([rk ]_ s) = slen) **
  (fun s h =>
    ([a ]_ s) = va  /\
    (var_e a |--> slen :: ptr :: nil **
      int_e ptr |--> A) s h)).

move=> s h H.
apply con_and_bang_inv_R in H.
case: H => H H2.
apply con_and_bang_inv_L in H.
case: H => H3 H.
apply con_and_bang_L => //.
apply con_and_bang_L => //.
rewrite /= in H2.
move: H2.
rewrite H3.
rewrite store.get_r0 Z2uK //.
apply contra.
move/eqP => ->.
by rewrite Z2uK.

apply pull_out_bang => slen0.

(** lw a0 four16 a *)

apply hoare_lw_back_alt'' with (
  (fun s h => [a ]_ s = va /\
    [rk]_s = slen /\
    (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h /\
    [a0]_s = ptr)).

move=> s h H.
exists ptr.
rewrite conCE in H.
rewrite -mapsto2_mapstos /= in H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
case: Hh1 => a_va Hh1.
case: Hh2 => ? Hh2; subst h2.
clear h1dh2.
rewrite heap.unionhe in h1Uh2; subst h1.
split.
  rewrite conAE in Hh1.
  rewrite conCE conAE in Hh1.
  move: Hh1.
  apply monotony => // h'.
  apply mapsto_ext => //=.
  by rewrite sext_Z2u.
rewrite /update_store_lw.
repeat Reg_upd.
split; first by [].
split; first by [].
split; last by reflexivity.
Assert_upd.
by rewrite -mapsto2_mapstos.

(** while.ifte (bgtz rk) *)

apply hoare_ifte_bang.

apply hoare_prop_m.hoare_stren with ((fun s h =>
      [a ]_ s = va /\
      [rk ]_ s = slen /\
      (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h /\
      [a0 ]_ s = ptr) ** !(fun s : store.t => 0 < s2Z slen)).
move=> s h H.
apply con_and_bang_inv_R in H.
case : H => H Hrk.
apply con_and_bang_R => //.
rewrite /= in Hrk.
move/ltZP in Hrk.
case: H => Ha [Hb [Hc Hd]].
by rewrite Hb in Hrk.

rewrite assert_m.conCE.
apply pull_out_bang => Hslen.

apply while.hoare_seq with ((fun s h => exists A',
    size A' = nk /\
    [a0 ]_ s = ptr /\
    u2Z [rk ]_ s = Z_of_nat nk /\
    (var_e a0 |--> A') s h /\
    2 * \S_{ nk } A' + u2Z ([prev ]_ s `>> 31) = \S_{ nk } A) **
  ((var_e a |--> slen :: ptr :: nil) ** !(fun s => [a]_s = va))).

eapply (before_frame ((var_e a |--> slen :: ptr :: nil) ** !(fun s => [a]_s = va))
_
(fun s h => exists A', size A' = nk /\
    [a0 ]_ s = ptr /\
    u2Z [rk ]_ s = Z_of_nat nk /\
    (var_e a0 |--> A') s h /\
    2 * \S_{ nk } A' + u2Z ([prev ]_ s `>> 31) = \S_{ nk } A)).

apply mips_frame.frame_rule_R.
  eapply multi_halve_u_triple => //.
  by Uniq_uniq r0.
  rewrite [modified_regs _]/=.
  by Inde.
  by [].

move=> s h [Ha [Hb [Hc Hd]]].
rewrite assert_m.conCE in Hc.
move: Hc.
apply monotony => // h' Hh'.
split => //.
split; last by move: Hh'; exact/mapstos_ext.
rewrite Hb -s2Z_u2Z_pos; last by omega.
apply Zsgn_pos in Hslen.
by rewrite slen_nk Hslen mul1Z.

by apply con_and_bang_R.

by apply hoare_prop_m.entails_id.

apply exists_conC_hoare.
apply pull_out_exists => A'.

rewrite con_bangE_R.
rewrite conAE.
apply pull_out_bang => A'_nk.

apply while.hoare_seq with ((fun s h =>
  u2Z ([rk ]_ s) = Z_of_nat nk /\
  ([a0 ]_ s) = ptr /\
  (var_e a0 |--> A') s h /\
  (0 = \S_{ nk } A' -> ([next ]_ s) = one32) /\
  (0 < \S_{ nk } A' -> ([next ]_ s) = zero32)) **
!(fun s0 => 2 * \S_{ nk } A' + u2Z (([prev ]_ s0) `>> 31) = \S_{ nk } A) **
(var_e a |--> slen :: ptr :: nil) **
!(fun s => [a]_s = va)).

eapply hoare_prop_m.hoare_stren; last first.
  apply mips_frame.frame_rule_R.
  apply multi_is_zero_u_triple => //.
  by Uniq_uniq r0.
  rewrite [modified_regs _]/=.
  Inde.
  apply inde_u2Z_b_get_R with (b := fun x => @shrl x 32).
  by Uniq_not_In.
  by [].

move=> s h H.
rewrite -assert_m.conAE.
move: H; apply monotony => // h' H.
apply con_and_bang_R; tauto.

(** while.ifte (bne next r0) *)

apply while.hoare_ifte.

have : uniq(a, r0) by Uniq_uniq r0.
move/multi_zero_s_triple.
move/(_ A' ptr slen) => Htmp.
eapply (before_frame !(fun s0 =>
  [a ]_ s0 = va /\
  u2Z ([rk ]_ s0) = Z_of_nat nk /\
  [a0 ]_ s0 = ptr /\
  0 = \S_{ nk } A' /\
  2 * \S_{ nk } A' + u2Z (([prev ]_ s0) `>> 31) = \S_{ nk } A /\
  u2Z ([a ]_ s0) + 4 * 2 < \B^1)).
apply frame_rule_R.
  by apply Htmp.
  simpl modified_regs; by apply inde_nil.
by [].

move=> s h [H Htest].

  apply con_and_bang_R.
  rewrite -2!assert_m.conAE in H.
  apply con_and_bang_inv_R in H.
  case: H => H a_va.
  rewrite conCE in H.
  move: H; apply monotony => // h' Hh'.
  apply con_and_bang_inv_R in Hh'.
  case: Hh' => [[Ha [Hb [Hc Hd]]] He].
  move: Hc.
  by apply mapstos_ext.

  rewrite -2!assert_m.conAE in H.
  apply con_and_bang_inv_R in H.
  case: H => H a_va.
  case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
  apply con_and_bang_inv_R in Hh1.
  case: Hh1 => Hh1 Hshift.
  case: Hh1 => [Ha [Hb [Hc [Hd He]]]].
  repeat (split => //).
  rewrite /= store.get_r0 /= Z2uK // in Htest.
  case/leZ_eqVlt : (min_lSum nk A') => // abs.
  apply He in abs.
  by rewrite abs Z2uK // in Htest.
  by rewrite a_va.

move=> s h H.

apply con_and_bang_inv_R in H.
case: H => [Ha [Hb [Hc [Hd [He [Hf Hg]]]]]].

have [X|X] : u2Z (([prev ]_ s) `>> 31) = 0 \/
  u2Z (([prev ]_ s) `>> 31) = 1.
  move: (shrl_lt ([prev ]_ s) 31) => /= X1.
  move: (min_u2Z (([prev ]_ s) `>> 31)) => ?; omega.

exists zero32.
exists A'(*0*).
split; first by [].
rewrite s2Z_u2Z_pos'; last by rewrite Z2uK.
rewrite Z2uK //.
split; first by [].
split; first by [].
split; first by [].
split; first by [].
rewrite X -Hf -He X; ring.

exists zero32, A'.
split; first by [].
rewrite s2Z_u2Z_pos'; last by rewrite Z2uK.
rewrite Z2uK //.
split; first by [].
split; first by [].
split; first by [].
split; first by [].
rewrite X -Hf X -He.
apply Zsgn_pos in Hslen.
rewrite Hslen; ring.

apply hoare_nop'.
move=> s h H.
case: H => H Htest.
rewrite /= in Htest.
move/negPn : Htest.
rewrite store.get_r0 Z2uK //.
move/eqP=> Htest.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
apply con_and_bang_inv_L in Hh2.
case: Hh2 => Hshift Hh2.

exists slen, A'.
apply con_and_bang_inv_R in Hh2.
case: Hh2 => Hh2 a_va.
apply Zsgn_pos in Hslen.
split; first by [].
split; first by [].
case: Hh1 => Hrk [a0_ptr [Hh1 [HSum1 HSum2]]].
rewrite Hslen !mul1Z.
case/leZ_eqVlt : (min_lSum nk A') => // abs.
- apply HSum1 in abs.
  by rewrite abs Z2uK in Htest.
- split.
    by apply/esym/Zsgn_pos.
  split; first by [].
  split.
    rewrite assert_m.conCE.
    exists h1, h2; repeat (split => //).
    by move: Hh1; apply mapstos_ext.
  by rewrite mulZ1.

apply hoare_prop_m.hoare_stren with ((fun s h =>
  [a ]_ s = va /\
  [rk ]_ s = slen /\
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h /\
  [a0 ]_ s = ptr) ** !(fun s : store.t => s2Z slen < 0)).

move=> s h H.
apply con_and_bang_inv_R in H.
case: H => [[H1 [H2 [H3 H4]]] Htest].
rewrite /= in Htest.
move/ltZP in Htest.
apply con_and_bang_R => //.
move: Htest; rewrite H2 => /leZNgt/leZ_eqVlt[|] // /eqP abs.
suff : s2Z slen != 0 by rewrite abs.
apply: contra slen0 => /eqP.
rewrite (_ : 0 = s2Z (Z2u 32 0)).
by move/s2Z_inj/eqP.
by rewrite s2Z_u2Z_pos' // Z2uK.

rewrite assert_m.conCE.
apply pull_out_bang => Hslen.

(** abs_prg.abs rk i ; *)

apply while.hoare_seq with
  (!(fun s => s2Z ([rk ]_ s) = Z.abs (s2Z slen)) **
  (fun s h => ([a ]_ s) = va /\
    (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h /\
    [a0]_s = ptr)).

have Hslen' : s2Z slen <> - 2 ^ 31.
  move=> H.
  apply Zsgn_neg in Hslen.
  rewrite slen_nk Hslen mulN1Z eqZ_opp in H *.
  exact/ltZ_eqF.
have : uniq(rk, i, r0) by Uniq_uniq r0.
move/abs_triple_bang/(_ _ Hslen') => Htmp.

eapply hoare_prop_m.hoare_stren; last first.
  apply mips_frame.frame_rule_R.
  apply Htmp.
  rewrite [modified_regs _]/=; by Inde.
  by [].
move=> s h H.
rewrite [_ |--> _]lock -lock in H.
apply con_and_bang_L; tauto.

apply while.hoare_seq with (fun s h =>
  u2Z [rk ]_ s = Z_of_nat nk /\
  [a ]_ s = va /\
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h /\
  [a0 ]_ s = ptr /\
  (Zeven (\S_{ nk } A) -> [tmp]_s = one32) /\
  (Zodd (\S_{ nk } A) -> [tmp]_s = zero32)).

have : uniq(rk, a0, tmp, r0) by Uniq_uniq r0.
move/multi_is_even_u_triple/(_ nk A ptr A_nk) => Htmp.
eapply (before_frame (fun s h => [a ]_ s = va /\ (var_e a |--> slen :: ptr :: nil) s h)).
apply mips_frame.frame_rule_R.
  apply Htmp.
  rewrite [modified_regs _]/=; by Inde.
by [].

move=> s h H.
apply con_and_bang_inv_L in H.
case: H => H1 [H2 [H3 H4]].
rewrite assert_m.conCE in H3.
move: H3.
apply monotony => // h' Hh'.
split.
  by apply auxili with slen.
split => //.
move: Hh'.
by apply mapstos_ext.

move=> s h H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
rewrite assert_m.conCE.
split; first by tauto.
split; first by tauto.
split.
  exists h1, h2; repeat (split => //).
  2: tauto.
  case: Hh1 => H1 [H2 [H3 [H4 H5]]].
  move: H3.
  by apply mapstos_ext.
  tauto.

apply while.hoare_ifte.

apply hoare_prop_m.hoare_stren with (fun s h =>
  Zeven (\S_{ nk } A) /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  [a ]_ s = va /\
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h /\
  [a0 ]_ s = ptr).

move=> s h [H Htest].
rewrite /= store.get_r0 Z2uK // in Htest .
split; last by tauto.
case: H => _ [_ [_ [_ [Heven Hodd]]]].
case: (Zeven_odd_dec (\S_{ nk } A)) => //.
move/Hodd => abs.
by rewrite abs !Z2uK // in Htest.

apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => Heven.

have : uniq(rk, a0, i, tmp, prev, next, r0) by Uniq_uniq r0.
move/multi_halve_u_triple/(_ _ _ ptr_fit _ A_nk) => Htmp.
eapply (before_frame (fun s h => [a ]_ s = va /\ (var_e a |--> slen :: ptr :: nil) s h)).
apply mips_frame.frame_rule_R.
  by apply Htmp.
  rewrite [modified_regs _]/=; by Inde.
by [].

clear Htmp.
move=> s h H.
case: H => nk_rk [a_va [Hh a0_ptr]].
case: Hh => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
rewrite assert_m.conCE.
exists h1, h2; (repeat (split => //)).
move: Hh2.
by apply mapstos_ext.

clear Htmp.
move=> s h H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 [a_va Hh2]]]]].
case: Hh1 => A' [A'_nk [a0_ptr [rk_nk [Hh1 HSum]]]].
have no_overflow : u2Z ([prev ]_ s `>> 31) = 0.
  rewrite -HSum in Heven.
  apply Zeven_plus_inv in Heven.
  case: Heven => Heven.
    case: Heven => _ Heven.
    have [Hoverflow|Hoverflow] : u2Z ([prev ]_ s `>> 31) = 0 \/ u2Z ([prev ]_ s `>> 31) = 1.
      move: (shrl_lt ([prev ]_ s) 31) => /= X1.
      move: (min_u2Z (([prev ]_ s) `>> 31)) => ?; omega.
      assumption.
    rewrite Hoverflow in Heven .
    by inversion Heven.
  case: Heven => abs _.
  apply Zodd_not_Zeven in abs.
  exfalso.
  by apply/abs/Zeven_2.

case/leZ_eqVlt : (min_lSum nk A') => // abs.
- rewrite -HSum -abs no_overflow mulZ0 addZ0 mulZ0 /= in slen_A.
  apply Zsgn_neg in Hslen.
  by rewrite Hslen in slen_A.
- exists slen, A'.
  split; first by [].
  split; first by [].
  split.
    rewrite no_overflow addZ0 in HSum.
    apply Zsgn_pos in abs.
    by rewrite Zsgn_Zmult ZsgnK abs mulZ1.
  split; first by [].
  split.
    rewrite assert_m.conCE.
    exists h1, h2; repeat (split => //).
    move: Hh1.
    by apply mapstos_ext.
  rewrite no_overflow -HSum no_overflow 2!addZ0; ring.

apply hoare_prop_m.hoare_stren with (fun s h =>
  Zodd (\S_{ nk } A) /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  [a ]_ s = va /\
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h /\
  [a0 ]_ s = ptr).

move=> s h [H Htest].
rewrite /= store.get_r0 Z2uK // in Htest .
split; last tauto.
case: H => _ [_ [_ [_ [Heven Hodd]]]].
case: (Zeven_odd_dec (\S_{ nk } A)) => //.
move/Heven => abs.
by rewrite abs !Z2uK // in Htest.

apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => Hodd.

apply while.hoare_seq with (fun s h =>
  exists A', size A' = nk /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  [a ]_ s = va /\
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A') s h /\
  [a0 ]_ s = ptr /\
  2 * \S_{ nk } A' + u2Z ([prev]_s `>> 31) = \S_{ nk } A).

have : uniq(rk, a0, i, tmp, prev, next, r0) by Uniq_uniq r0.
move/multi_halve_u_triple/(_ _ _ ptr_fit _ A_nk) => Htmp.
eapply (before_frame (fun s h => (var_e a |--> slen :: ptr :: nil) s h /\ [a ]_s = va)).
apply mips_frame.frame_rule_R.
  by apply Htmp.
  rewrite [modified_regs _]/=; by Inde.
by [].

move=> s h H.
case: H => rk_nk [a_va [Hh a0_ptr]].
rewrite assert_m.conCE.
case: Hh => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
exists h1, h2; repeat (split => //).
move: Hh2.
by apply assert_m.mapstos_ext.

move=> s h H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 [Hh2 va_a]]]]].
case: Hh1 => A' [a'_nk [a0_ptr [rk_nk [Hh1 HSum]]]].
exists A'.
repeat (split => //).
rewrite assert_m.conCE.
exists h1, h2; repeat (split => //).
move: Hh1; by apply mapstos_ext.

apply pull_out_exists => A'.
apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => A'_nk.

apply hoare_addiu with (fun s h =>
  u2Z [rk ]_ s = Z_of_nat nk /\
  [a ]_ s = va /\
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A') s h /\
  [a0 ]_ s = ptr /\ 2 * \S_{ nk } A' + 1 = \S_{ nk } A /\
  [next]_ s = one32).

move=> s h H.
case: H => rk_nk [a_va [Hh [a0_ptr HSum]]].
rewrite /wp_addiu.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.

rewrite -HSum in Hodd.

have [Hoverflow|Hoverflow] : u2Z ([prev ]_ s `>> 31) = 0 \/ u2Z ([prev ]_ s `>> 31) = 1.
  move: (shrl_lt ([prev ]_ s) 31) => /= X1.
  move: (min_u2Z (([prev ]_ s) `>> 31)) => ?; omega.
- rewrite Hoverflow addZ0 in Hodd.
  apply Zodd_not_Zeven in Hodd.
  exfalso.
  by apply Hodd, Zeven_2.
- congruence.

by rewrite sext_Z2u // add0i.

apply while.hoare_seq with (fun s h => exists A',
  size A' = nk /\
  [next]_s = one32 /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  [a ]_ s = va /\
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A') s h /\
  [a0 ]_ s = ptr /\ 2 * \S_{ nk } A' = \S_{ nk } A + 1).

have : uniq(rk, next, a0, i, tmp, prev, r0) by Uniq_uniq r0.
move/multi_incr_u_triple/(_ _ _ ptr_fit _ A'_nk) => Htmp.
eapply (before_frame (fun s h =>
  u2Z [rk ]_ s = Z_of_nat nk /\
  [a ]_ s = va /\
  (var_e a |--> slen :: ptr :: nil) s h /\
  2 * \S_{ nk } A' + 1  = \S_{ nk } A)).
apply mips_frame.frame_rule_R.
  by apply Htmp.
  rewrite [modified_regs _]/=; by Inde.
by [].

move=> s h H.
case: H => nk_rk [a_va [Hh [a0_ptr [HSum Hnext]]]].
case: Hh => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
rewrite assert_m.conCE.
exists h1, h2; repeat (split => //).
move: Hh2.
by apply assert_m.mapstos_ext.

move=> s h H.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
case: Hh1 => A'' [A''_nk [Hnext [a0_ptr [Hh1 [Hlo HSum]]]]].
case: Hh2 => rk_nk [a_va [Hh2 HSum']].
destruct nk => //.
rewrite [(if beq_nat nk.+1 0 then 0 else 1)]/= in HSum.
have no_overflow : u2Z (store.lo s) = 0.
  have [X|X] : u2Z (store.lo s) = 0 \/ u2Z (store.lo s) = 1.
    move: (min_u2Z (store.lo s)) => ?; omega.
  by [].
  rewrite X mul1Z in HSum.
  have A'_bound : \S_{ nk.+1 } A' <= 2 ^^ (nk.+1 * 32 - 1).
    have H1 : 2 * \S_{ nk.+1 } A' + 1 < \B^nk.+1.
      rewrite HSum'.
      by apply max_lSum.
    have {}H1 : 2 * \S_{ nk.+1 } A' <= \B^nk.+1 by omega.
    rewrite ZbetaE in H1.
    rewrite (_ : (nk.+1 * 32 = (nk.+1 * 32 - 1).+1)%nat) in H1; last by rewrite mulSn -subSn.
    rewrite (_ : 2 ^^ (nk.+1 * 32 - 1).+1 = 2 * 2 ^^ (nk.+1 * 32 - 1) ) in H1; last by [].
    do 2 rewrite (mulZC 2) in H1.
    by apply Zmult_le_reg_r in H1.
  have H1 : \S_{ nk.+1 } A'' <= 2 ^^ (nk.+1 * 32 - 1) + 1 - \B^nk.+1 by omega.
  have H2 : 2 ^^ (nk.+1 * 32 - 1) + 1 - \B^nk.+1 <= 0.
    have H2 : 2 ^^ (nk.+1 * 32 - 1) + 1 <= \B^nk.+1.
      rewrite ZbetaE.
      have ? : 2 ^^ (nk.+1 * 32 - 1) < 2 ^^ (nk.+1 * 32).
        apply/expZ_2_lt; by rewrite subn1 prednK.
      omega.
    omega.
  have H3 : \S_{ nk.+1 } A'' = 0 by move: (min_lSum nk.+1 A'') => ?; omega.
  have H4 : \S_{ nk.+1 } A' = \B^nk.+1 - 1 by omega.
  rewrite H4 in HSum'.
  rewrite (_ : 2 * (\B^nk.+1 - 1) + 1 = 2 * \B^nk.+1 - 1) in HSum'; last by omega.
  have H5 : 2 * \B^nk.+1 <= \B^nk.+1.
    suff H5 : 2 * \B^nk.+1 - 1 < \B^nk.+1 by omega.
    apply: leZ_ltZ_trans; last by apply max_lSum.
    rewrite HSum'; exact/leZZ.
  move/leZP in H5; rewrite {1}(_ : 2 = 2 ^^ 1) // -ZpowerD Zpower_2_le in H5.
  ssromega.

rewrite no_overflow mul0Z addZ0 in HSum.
exists A''.
repeat (split; first by []).
split.
  rewrite assert_m.conCE.
  exists h1, h2; repeat (split => //).
  move: Hh1.
  by apply assert_m.mapstos_ext.
split; first by [].
rewrite HSum -HSum'; ring.

apply hoare_sll' => s h [A'' [A''_nk [Hone [H1 [a_va [Hmem [a0_ptr A''_A]]]]]]].
rewrite /wp_sll.
exists slen, A''.
repeat Reg_upd.
repeat (split; first by []).
apply Zsgn_neg in Hslen.
rewrite Hslen.
rewrite !mulN1Z.
split.
  symmetry.
  apply Zsgn_neg.
  case/leZ_eqVlt : (min_lSum nk A'') => abs.
  - rewrite -abs mulZ0 in A''_A.
    move: (min_lSum nk A) => ?; omega.
  - omega.
split; first by [].
split; first by Assert_upd.
rewrite Z2uK // Hone (_ : '| 31 | = 31)%nat //.
move: (@shl_shrl 32 one32 1).
move=> ->.
  rewrite Z2uK //; omega.
by rewrite Z2uK.
Qed.

Lemma multi_halve_s_triple rk a a0 i tmp prev next : uniq(a, a0, i, tmp, prev, next, rk, r0) ->
  forall nk va, Z_of_nat nk < 2 ^^ 31 ->
    forall val : Z,
      {{ fun s h => [ a ]_s = va /\ (var_signed nk a val) s h }}
      multi_halve_s a a0 i tmp prev next rk
      {{ fun s h => exists val',
        (var_signed nk a val') s h /\ 2 * val' + u2Z ([prev]_s `>> 31) = val }}.
Proof.
move=> Hnodup nk va nk_231 val.

apply hoare_prop_m.hoare_stren with (fun s h => exists slen ptr A,
  SignMagn slen nk A val /\
  u2Z ptr + 4 * Z_of_nat nk < \B^1 /\
  u2Z va + 4 * 2 < \B^1 /\
  [a ]_ s = va /\
  ((var_e a |--> slen :: ptr :: nil) ** (int_e ptr |--> A)) s h).

move=> s h [Ha Hmem].
case: Hmem => slen ptr A a_fit encodingA ptr_fit Hmem.
exists slen, ptr, A.
repeat (split; first by []).
split; by [congruence | ].

apply pull_out_exists => slen.
apply pull_out_exists => ptr.
apply pull_out_exists => A.
apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => encoding.
apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => ptr_fit.
apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => va_fit.

case: encoding => H1 H2 H3 H4.
move: (multi_halve_s_triple_gen _ _ _ _ _ _ _ Hnodup _ nk_231 _ va_fit _ ptr_fit _ H2 _ H1).
rewrite {1}H3 -{1}H4.
move/(_ (refl_equal _)) => Htmp.

eapply hoare_prop_m.hoare_weak; last by apply Htmp.
move=> s h [slen' [A' [A'_nk [slen'_nk [slen'_A' [a_va [Hmem H]]]]]]].
exists (Z.sgn (s2Z slen') * \S_{ nk } A').
split.
  apply mkVarSigned with slen' ptr A' => //.
  congruence.
by rewrite mulZA H.
Qed.

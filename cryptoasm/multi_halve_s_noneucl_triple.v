(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int uniq_tac multi_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_frame mips_mint mips_tactics.
Import expr_m.
Import assert_m.
Require Import multi_halve_s_prg multi_is_zero_u_triple multi_zero_s_triple.
Require Import abs_triple multi_halve_u_triple.

Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.
Local Open Scope multi_int_scope.

(* TODO: clean *)

Lemma auxili nk (slen rk : int 32) :
  Z_of_nat nk < 2 ^^ 31 ->
(* TODO: really useful? *)
  slen != zero32 ->
  s2Z slen = sgZ (s2Z slen) * Z_of_nat nk ->
  s2Z rk = `|s2Z slen| ->
  u2Z rk = Z_of_nat nk.
Proof.
move=> nk_231 slen0 slen_nk rk_nk.
have H1 : 0 <= s2Z rk by rewrite rk_nk; apply normZ_ge0.
have Haux : s2Z slen <> 0.
  rewrite (_ : 0 = s2Z (Z2u 32 0)); last first.
    rewrite s2Z_u2Z_pos' //; by rewrite Z2uK.
    move/eqP in slen0.
    contradict slen0.
    by apply s2Z_inj in slen0.
have H2 : s2Z rk < 2 ^^ 31.
  rewrite rk_nk slen_nk Zabs_Zmult Zabs_Zsgn_1 // mul1Z Z.abs_eq //.
  exact: Zle_0_nat.
rewrite s2Z_u2Z_pos' in rk_nk; last by rewrite -s2Z_u2Z_pos.
rewrite rk_nk slen_nk Zabs_Zmult Zabs_Zsgn_1 // mul1Z Z.abs_eq //.
exact: Zle_0_nat.
Qed.

Lemma multi_halve_s_noneucl_triple rk a a0 i tmp prev next : uniq(rk, a, a0, i, tmp, prev, next, r0) ->
  forall nk va, Z_of_nat nk < 2 ^^ 31 ->
    forall val : Z,
      {{ fun s h => [ a ]_s = va /\ (var_signed nk a val) s h}}
      multi_halve_s_noneucl a a0 i tmp prev next rk
      {{ fun s h => exists val',
        (var_signed nk a val') s h /\ 2 * val' + sgZ val * u2Z ([prev]_s `>> 31) = val}}.
Proof.
move=> Hnodup nk va nk_231 val.
rewrite /multi_halve_s_noneucl.

apply (hoare_prop_m.hoare_stren (fun s h => exists slen ptr A,
  SignMagn slen nk A val /\
  u2Z ptr + 4 * Z_of_nat nk < \B^1 /\
  u2Z va + 4 * 2 < \B^1 /\
  [a ]_ s = va /\
  ((var_e a |--> slen :: ptr :: nil) ** (int_e ptr |--> A)) s h)).

move=> s h [Ha Hmem].
case: Hmem => slen ptr A a_fit encodingA ptr_fit Hmem.
exists slen, ptr, A.
repeat (split; first by done).
split; [congruence | done].

apply pull_out_exists => slen.
apply pull_out_exists => ptr.
apply pull_out_exists => A.
apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => encoding.
apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => ptr_fit.
apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => va_fit.

apply hoare_lw_back_alt'' with (!(fun s => [ rk ]_s = slen) **
  (fun s h => ([a ]_ s) = va /\
    ((var_e a |--> slen :: ptr :: nil) ** (int_e ptr |--> A)) s h)).

move=> s h [Ha Hmem].
exists slen; split.
  move: Hmem.
  rewrite -mapsto2_mapstos conAE.
  apply monotony => // h1.
  apply mapsto_ext => //=.
  by rewrite sext_Z2u // addi0.

rewrite /update_store_lw.
apply store_upd_con.
apply con_and_bang_L; repeat Reg_upd => //.
split; first by assumption.
by Assert_upd.

apply hoare_ifte_bang.

  (* length = 0 *)

  apply hoare_addiu' => s h H.
  apply con_and_bang_inv_R in H.
  case: H => H Hr.
  rewrite /= in Hr.
  move/eqP/u2Z_inj : Hr.
  rewrite store.get_r0 => Hr.
  case: H => h1 [h2 [h1dh2 [h1Uh2 [[Hh1 ?] [a_va Hh2]]]]]; subst h1.
  clear h1dh2.
  rewrite heap.unioneh in h1Uh2; subst h2.
  exists 0.
  case: encoding => H1 H2 H3 H4.
  split.
    apply mkVarSigned with slen ptr A => //.
    Reg_upd.
    congruence.
    rewrite -Hh1 Hr.
    apply mkSignMagn => //.
    rewrite s2Z_u2Z_pos' //; by rewrite Z2uK.
    rewrite s2Z_u2Z_pos' //; by rewrite Z2uK.
    rewrite s2Z_u2Z_pos' //; by rewrite Z2uK.
    by Assert_upd.
  rewrite H4.
  rewrite -Hh1 Hr.
  rewrite s2Z_u2Z_pos' //; by rewrite Z2uK.

(* length <> 0 *)

apply (hoare_prop_m.hoare_stren (!(fun s => slen != zero32) **
  !(fun s => ([rk ]_ s) = slen) **
  (fun s h => ([a ]_ s) = va  /\
    (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h))).

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

apply while.hoare_seq with (!(fun s => s2Z ([rk ]_ s) = `|s2Z slen|) **
  fun s h => ([a ]_ s) = va /\
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h).

have : s2Z slen <> - 2 ^ 31.
  case: encoding => H1 H2 H3 H4.
  rewrite H2.
  move=> abs.
  have : Z_of_nat nk = 2 ^ 31.
    destruct (s2Z slen) => //.
    rewrite Zmult_1_l in abs.
    by destruct nk.
    rewrite mulN1Z in abs.
    by apply Zopp_inj in abs.
  move=> abs'; by rewrite abs' in nk_231.
have : uniq(rk, a0,r0) by Uniq_uniq r0.
move/abs_triple_bang/(_ slen) => Habs_triple.
move/Habs_triple => {Habs_triple} Habs_triple.
apply frame_rule_R => //.
rewrite [modified_regs _]/=.
by Inde.

apply hoare_lw_back_alt'' with (
  (fun s h => ([a ]_ s) = va /\
    ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A)) s h /\
    [a0]_s = ptr /\
    s2Z ([rk ]_ s) = Z.abs (s2Z slen))).

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
split; last by [].
Assert_upd.
by rewrite -mapsto2_mapstos.

eapply while.hoare_seq.

case: encoding. move=> A_nk slen_nk slen_val val_A.

have Hnodup' : uniq(rk,a0,i,tmp,prev,next,r0) by  Uniq_uniq r0.
move: (multi_halve_u_triple _ _ _ _ _ _ Hnodup' nk ptr ptr_fit A A_nk) => Htmp {Hnodup'}.

apply (before_frame
(!(fun s => u2Z ([a ]_ s) + 4 * 2 < \B^1 /\ [a]_s = va) ** (var_e a |--> slen :: ptr :: nil))
(fun s h => [a0 ]_ s = ptr /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  (var_e a0 |--> A) s h)
(fun s h => exists A',
  size A' = nk /\
  ([a0 ]_ s) = ptr /\
  u2Z ([rk ]_ s) = Z_of_nat nk /\
  (var_e a0 |--> A') s h /\
  2 * \S_{ nk } A' + u2Z (([prev ]_ s) `>> 31) = \S_{ nk } A)).
apply frame_rule_R.
exact Htmp.
simpl modified_regs.
Inde.
apply inde_u2Z_fit.
by Uniq_not_In.
done.

move=> s h [a_va [Hmem [Ha0 rk_nk]]].
rewrite conCE.
move: Hmem; apply monotony => // h' Hh'.
apply con_and_bang_L => //.
by rewrite a_va.
split => //.
split.
  by apply (auxili nk slen ([rk]_s)).
move: Hh'; by apply mapstos_ext.

by apply hoare_prop_m.entails_id.

case: encoding. move=> A_nk slen_nk slen_val val_A.

have Hnodup' : uniq(rk,a0,i,tmp,next,r0) by  Uniq_uniq r0.

apply exists_conC_hoare.
apply pull_out_exists => A'.

rewrite con_bangE_R.
rewrite conAE.
apply pull_out_bang => A'_nk.

apply while.hoare_seq with (((fun s h =>
  u2Z ([rk ]_ s) = Z_of_nat nk /\
  ([a0 ]_ s) = ptr /\
  (var_e a0 |--> A') s h /\
  (0 = \S_{ nk } A' -> ([next ]_ s) = one32) /\
  (0 < \S_{ nk } A' -> ([next ]_ s) = zero32)) **
!(fun s0 => 2 * \S_{ nk } A' + u2Z (([prev ]_ s0) `>> 31) = \S_{ nk } A) **
!(fun s0 => u2Z ([a ]_ s0) + 4 * 2 < \B^1 /\ [a]_s0 = va) **
var_e a |--> slen :: ptr :: nil)).

move: (multi_is_zero_u_triple _ _ _ _ _ Hnodup' nk A' ptr A'_nk ptr_fit) => Htmp {Hnodup'}.

apply (before_frame
(!(fun s0 => 2 * \S_{ nk } A' + u2Z (([prev ]_ s0) `>> 31) = \S_{ nk } A) **
 !(fun s0 => u2Z ([a ]_ s0) + 4 * 2 < \B^1 /\ [a]_s0 = va) **
 var_e a |--> slen :: ptr :: nil)
(fun s h => u2Z [rk ]_ s = Z_of_nat nk /\ [a0 ]_ s = ptr /\ (var_e a0 |--> A') s h)
(fun s h =>
   u2Z ([rk ]_ s) = Z_of_nat nk /\
   ([a0 ]_ s) = ptr /\
   (var_e a0 |--> A') s h /\
   (0 = \S_{ nk } A' -> ([next ]_ s) = one32) /\
   (0 < \S_{ nk } A' -> ([next ]_ s) = zero32))).
apply frame_rule_R.
by apply Htmp.
Inde.
apply inde_u2Z_b_get_R with (b := fun x => @shrl x 32).
rewrite [modified_regs _]/=.
by Uniq_not_In.
apply inde_u2Z_get_plus_Zlt.
rewrite [modified_regs _]/=; by Uniq_not_In.
simpl modified_regs; by Uniq_not_In.
simpl modified_regs; by Uniq_not_In.
done.

move=> s h H.
rewrite -conAE in H.
rewrite -2!conAE.
move: H.
apply monotony => // h1 Hh1.
move: Hh1.
apply monotony => // h2 Hh2.
apply con_and_bang_R; tauto.
by apply hoare_prop_m.entails_id.

apply hoare_ifte_bang.

have : uniq(a, r0) by Uniq_uniq r0.
move/multi_zero_s_triple/(_ A' ptr slen) => Htmp.

eapply (before_frame !(fun s0 =>
  [a ]_ s0 = va/\
  u2Z ([rk ]_ s0) = Z_of_nat nk /\
  [a0 ]_ s0 = ptr /\
  0 = \S_{ nk } A' /\
  2 * \S_{ nk } A' + u2Z (([prev ]_ s0) `>> 31) = \S_{ nk } A /\
  u2Z ([a ]_ s0) + 4 * 2 < \B^1)).
apply frame_rule_R.
apply Htmp.
by Inde.
done.

  move=> s h H.
  apply con_and_bang_inv_R in H.
  case: H => H Htest.
  rewrite /= in Htest.
  rewrite conCE 2!conAE in H.
  apply con_and_bang_inv_L in H.
  case: H => A'shift H.
  apply con_and_bang_inv_L in H.
  case: H => [[Ha Ha'] H].
  rewrite !con_bangE_R in H.
  rewrite !con_bangE_L in H.
  rewrite conCE !conAE in H.
  apply con_and_bang_inv_L in H.
  case: H => rk_nk H.
  apply con_and_bang_inv_L in H.
  case: H => a0_ptr H.
  rewrite conCE 1!conAE in H.
  apply con_and_bang_inv_L in H.
  case: H => [[HSum1 HSum2] H].

  apply con_and_bang_R => //.

  move: H.
  apply monotony => // h'.
  by apply mapstos_ext.

  repeat (split; first by done).
  case/leZ_eqVlt : (min_lSum nk A') => // abs.
  apply HSum2 in abs.
  rewrite abs in Htest.
  by rewrite store.get_r0 Z2uK //  in Htest.

move=> s h H.
(*rewrite !con_bangE_R in H.*)
(*rewrite conAE in H.*)
apply con_and_bang_inv_R in H.
case: H => H [a_va [rk_nk [a0_ptr [HSum [Hshift a_fit]]]]].

have [X|X] : u2Z (([prev ]_ s) `>> 31) = 0 \/
  u2Z (([prev ]_ s) `>> 31) = 1.
  move: (shrl_lt ([prev ]_ s) 31) => /= X1.
  move: (min_u2Z (([prev ]_ s) `>> 31)) => ?; omega.
exists 0.
split.
  apply mkVarSigned with zero32 ptr A' => //.
  apply mkSignMagn => //.
  by rewrite s2Z_u2Z_pos' // Z2uK.
  by rewrite s2Z_u2Z_pos' // Z2uK.
  by rewrite s2Z_u2Z_pos' // Z2uK.
rewrite {2}val_A /= X -Hshift -HSum X; ring.

exists 0.
split.
  apply mkVarSigned with zero32 ptr A' => //.
  apply mkSignMagn => //.
  by rewrite s2Z_u2Z_pos' // Z2uK.
  by rewrite s2Z_u2Z_pos' // Z2uK.
  by rewrite s2Z_u2Z_pos' // Z2uK.
rewrite val_A X Zsgn_Zmult ZsgnK -Hshift -HSum /= X /=; ring.

apply hoare_nop'.
move=> s h H.
apply con_and_bang_inv_R in H.
case: H => H Htest.
rewrite /= in Htest.
move/negPn : Htest.
rewrite store.get_r0 Z2uK //.
move/eqP=> Htest.
case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].

exists (sgZ (s2Z slen) * (\S_{ nk } A')).
apply con_and_bang_inv_L in Hh2.
case: Hh2 => A'shift Hh2.
case: Hh1 => rk_nk [a0_ptr [Hh1 His_zero]].
rewrite val_A.
have A'_not_0 : 0 < \S_{ nk } A'.
  apply Zle_neq_lt => //.
  by apply min_lSum.
  move/(proj1 (His_zero)) => abs; rewrite abs in Htest.
  by rewrite Z2uK in Htest.
apply con_and_bang_inv_L in Hh2.
split.
  apply mkVarSigned with slen ptr A' => //.
  tauto.
  apply mkSignMagn => //.
  rewrite Zsgn_Zmult ZsgnK (proj2 (Zsgn_pos (\S_{ nk } A')) A'_not_0); ring.
exists h2, h1 => //.
split; first by apply heap.disj_sym.
split.
  rewrite heap.unionC //; exact: heap.disj_sym.
split; first by tauto.
by move: Hh1; apply mapstos_ext => //.
rewrite -A'shift.
rewrite mulZDr !mulZA.
f_equal; first ring.
f_equal.
rewrite -mulZA -mulZDr Zsgn_Zmult ZsgnK.
have : 0 < 2 * \S_{ nk } A' + u2Z (([prev ]_ s) `>> 31).
  move: (min_u2Z (([prev ]_ s) `>> 31)) => ?; omega.
move/Zsgn_pos => ->; ring.
Qed.

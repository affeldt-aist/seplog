(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_frame mips_tactics mips_contrib mapstos.
Import expr_m.
Import assert_m.
Require Import multi_zero_s_prg multi_zero_s_triple multi_one_s_prg.

Local Open Scope heap_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.

Lemma multi_zero_s'_triple_bang rx a0 a1 a2 a3 : uniq(rx, a0, a1, a2, a3, r0) ->
  forall nk X vx ptr, size X = nk ->
    u2Z vx + 4 * 2 < \B^1 ->
    u2Z ptr + 4 * Z_of_nat nk < \B^1 ->
  {{ !(fun s => [ rx ]_s = vx) **
     var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil ** int_e ptr |--> X }}
  multi_zero_s' rx a0 a1 a2 a3
  {{ !(fun s => [ rx ]_s = vx) ** !(fun s => [ a0 ]_s = Z2u 32 (Z_of_nat nk)) **
     var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil ** int_e ptr |--> nseq nk zero32 }}.
Proof.
move=> Hregs nk X vx ptr X_nk vx_fit ptr_fit.
eapply while.hoare_conseq; last first.
  have : uniq(rx, a0, a1, a2, a3, r0) by Uniq_uniq r0.
  move/multi_zero_s'_triple.
  move/(_ nk X vx ptr X_nk vx_fit ptr_fit)=> hoare_triple.
  exact: hoare_triple.
  move=> s h H.
  apply con_and_bang_inv_L in H.
  by case: H.
move=> s h [Hrx [Ha0 H]].
apply con_and_bang_L => //; exact: con_and_bang_L.
Qed.

Lemma multi_one_s_triple_bang rx rk a0 a1 a2 a3 : uniq(rx, rk, a0, a1, a2, a3, r0) ->
  forall nk X vx ptr, 0 < Z_of_nat nk < 2 ^^ 31 -> size X = nk ->
    u2Z vx + 4 * 2 < \B^1 ->
    u2Z ptr + 4 * Z_of_nat nk < \B^1 ->
    forall slen, s2Z slen = sgZ (s2Z slen) * Z_of_nat nk ->
  {{ !(fun s => [ rx ]_ s = vx) **
     !(fun s => u2Z [ rk ]_s = Z_of_nat nk) **
      var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X}}
  multi_one_s rx rk a0 a1 a2 a3
  {{ !(fun s => [ rx ]_ s = vx) **
     !(fun s => u2Z [ rk ]_s = Z_of_nat nk) **
      var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil ** int_e ptr |--> one32 :: nseq (nk - 1) zero32 }}.
Proof.
move=> Hnodup nk X vx ptr Hnk X_nk vx_fit ptr_fit slen Hslen.
rewrite /multi_one_s.

(** lw a0 zero16 rx *)

apply mips_contrib.hoare_lw_back_alt'' with (
  !(fun s => [rx ]_ s = vx) **
  !(fun s => u2Z [ rk ]_s = Z_of_nat nk) **
  var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X **
  !(fun s => [ a0 ]_ s = slen)).

move=> s h Hmem.
exists slen; split.
  move: Hmem.
  rewrite !assert_m.conAE.
  do 2 rewrite assert_m.conCE !assert_m.conAE.
  apply monotony => // h1.
  apply mapsto_ext => //.
  by rewrite /= sext_Z2u // addi0.
rewrite [assert_m.mapstos]lock -!assert_m.conAE -lock.
apply con_and_bang_R.
  apply inde_upd_store => //.
  by rewrite /bang; Inde.
by rewrite [assert_m.mapstos]lock !assert_m.conAE -lock.
by Reg_upd.

(** ifte_beq a0, r0 thendo *)

apply while.hoare_seq with (!(fun s => [rx ]_ s = vx) **
        !(fun s => u2Z [rk ]_ s = Z_of_nat nk) **
       var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil ** int_e ptr |--> X).

apply hoare_ifte_bang.
- apply hoare_sw_back' => s h H.
  exists (int_e slen).
  rewrite -mapsto2_mapstos in H.
  do 4 rewrite assert_m.conCE !assert_m.conAE in H.
  move: H; apply monotony => h1 //.
    apply mapsto_ext => //=.
    by rewrite sext_Z2u // addi0.
  apply currying => {h1} h1 H.
  rewrite !assert_m.conAE in H.
  do 5 rewrite assert_m.conCE !assert_m.conAE in H.
  rewrite -mapsto2_mapstos.
  do 1 rewrite assert_m.conCE !assert_m.conAE.
  move: H.
  apply con_bang_L_pull_out => rk_nk H.
  move: H; apply monotony => // h2.
    apply mapsto_ext => //.
    by rewrite /= sext_Z2u // addi0.
    by rewrite /= -rk_nk Z2u_u2Z.
  apply monotony => // h3.
  apply monotony => // h4 H.
  rewrite -assert_m.conAE in H.
  rewrite con_bangE in H.
  by apply con_and_bang_inv_L in H; case: H.

(** ifte_bltz a0 thendo *)

apply hoare_ifte_bang.
- set pre := _ ** _.
  apply mips_seplog.hoare_prop_m.hoare_stren with (fun s h => s2Z slen < 0 /\ pre s h).
    move=> s h H /=.
    split; last by [].
    rewrite /pre {pre} in H.
    rewrite [assert_m.mapstos]lock -!assert_m.conAE -lock in H.
    apply con_and_bang_inv_R in H; case: H => H /=.
    move/ltZP => Ha0.
    apply con_and_bang_inv_R in H; case: H => H _.
    apply con_and_bang_inv_R in H; case: H => _ H.
    by subst slen.
  apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => slen_neq.
  rewrite /pre.
  move/Zsgn_neg in slen_neq.
  have <- : cplt2 slen = Z2u 32 (Z_of_nat nk).
    apply s2Z_inj.
    rewrite [X in _ = X]s2Z_u2Z_pos'; last first.
      rewrite Z2uK //; clear -Hnk; simpl in *; omega.
    rewrite Z2uK; last by clear -Hnk; simpl in *; omega.
    rewrite s2Z_cplt2; last first.
      move/weirdE2.
      rewrite Hslen slen_neq mulN1Z.
      move/Zopp_inj => abs.
      case: Hnk => _.
      rewrite abs.
      by move/ltZZ.
    rewrite Hslen slen_neq mulN1Z; ring.
  have : uniq(rx, a0, r0) by Uniq_uniq r0.
  move/(multi_negate_triple.multi_negate_triple rx a0 slen ptr X) => Htmp.

  apply hoare_prop_m.hoare_stren with (
    (var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X) **
    (!(fun s : store.t => [rx ]_ s = vx) **
        !(fun s : store.t => u2Z [rk ]_ s = Z_of_nat nk)
        )).
    move=> s h.
    rewrite [mapstos]lock.
    rewrite !assert_m.conAE.
    do 2 rewrite assert_m.conCE !assert_m.conAE.
    apply monotony => // h1.
    apply monotony => // h2.
    do 3 rewrite assert_m.conCE !assert_m.conAE.
    apply monotony => // h3.
    rewrite con_bangE.
    rewrite con_bangE.
    by move/con_bang_L.
  rewrite [mapstos]lock.
  do 2 rewrite [X in WMIPS_Hoare.hoare _ _ X]assert_m.conCE ![X in WMIPS_Hoare.hoare _ _ X]assert_m.conAE.
  rewrite -[X in WMIPS_Hoare.hoare _ _ X]assert_m.conAE.
  rewrite -lock.
  apply frame_rule_R.
  by [].
    rewrite [modified_regs _]/=; rewrite /bang; by Inde.
    rewrite /bang; by Inde.

(** nop *)

apply hoare_nop' => s h H.
rewrite [assert_m.mapstos]lock in H.
rewrite assert_m.conCE !assert_m.conAE in H.
apply con_and_bang_inv_L in H; case: H => H1 H.
do 4 rewrite assert_m.conCE !assert_m.conAE in H.
apply con_and_bang_inv_L in H; case: H => H H2.
apply con_and_bang_inv_L in H2; case: H2 => H2 H3.
rewrite -lock in H3.
suff : slen = Z2u 32 (Z_of_nat nk) by move=> <-.
apply s2Z_inj.
rewrite Hslen.
move/ltZP in H1.
move/eqP in H2.
rewrite store.get_r0 Z2uK // in H2.
have {H1 H2}H1 : 0 < s2Z slen.
  have {H2}H2 : s2Z [ a0 ]_ s <> 0.
    contradict H2.
    rewrite (_ : 0 = s2Z (Z2u 32 0)) in H2; last first.
      rewrite s2Z_u2Z_pos' //; last by rewrite Z2uK.
      by rewrite Z2uK.
    apply s2Z_inj in H2.
    by rewrite H2 Z2uK.
  subst slen; omega.
move/Zsgn_pos in H1.
rewrite H1 s2Z_u2Z_pos'; last first.
  rewrite Z2uK //; clear -Hnk; simpl in *; omega.
rewrite Z2uK //; last by clear -Hnk; simpl in *; omega.
ring.

(** multi_zero_signed' rx rk a1 a2 a3 ; *)

apply while.hoare_seq with (!(fun s => [rx ]_ s = vx) **
       !(fun s => [ rk ]_ s = Z2u 32 (Z_of_nat nk)) **
      var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil **
     int_e ptr |--> nseq nk zero32).
  apply hoare_prop_m.hoare_stren with (
    !(fun s => [rk ]_ s = Z2u 32 (Z_of_nat nk)) **
    !(fun s => [rx ]_ s = vx) **
    var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil **
      int_e ptr |--> X).
    move=> s h H.

    rewrite [mapstos]lock.
    do 1 rewrite assert_m.conCE !assert_m.conAE.
    rewrite -lock.
    move: H; apply monotony => // {h}h H.
    rewrite [mapstos]lock.
    do 2 rewrite assert_m.conCE !assert_m.conAE.
    rewrite -lock.
    move: H; apply monotony => // {h}h.
    apply bangify => <-.
    by rewrite Z2u_u2Z.
  apply hoare_prop_m.hoare_weak with (
    !(fun s => [rk ]_ s = Z2u 32 (Z_of_nat nk)) **
      !(fun s => [rx ]_ s = vx) **
        !(fun s => [a0 ]_ s = Z2u 32 (Z_of_nat nk)) **
        var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil **
          int_e ptr |--> nseq nk zero32).
    move=> s h H.
    rewrite [mapstos]lock in H.
    do 2 rewrite assert_m.conCE !assert_m.conAE in H.
    rewrite -lock in H.
    apply con_and_bang_inv_L in H; case: H => _ H.
    rewrite [mapstos]lock.
    do 2 rewrite assert_m.conCE !assert_m.conAE.
    rewrite -lock.
    move: H; apply monotony => {h}h //.
    apply monotony => {h}h //.
    by rewrite assert_m.conCE.
  apply frame_rule_L; last 2 first.
    rewrite [modified_regs _]/=; rewrite /bang; by Inde.
    rewrite /bang; by Inde.
  apply multi_zero_s'_triple_bang => //.
  by Uniq_uniq r0.

(** lw a0 four16 rx; *)

apply mips_contrib.hoare_lw_back_alt'' with
  (!(fun s => [rx ]_ s = vx) **
   !(fun s => [rk ]_ s = Z2u 32 (Z_of_nat nk)) **
   var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil **
   int_e ptr |--> nseq nk zero32 **
   !(fun s => [ a0 ]_s = ptr)).

move=> s h H.
exists ptr; split.
  rewrite -mapsto2_mapstos in H.
  do 3 rewrite assert_m.conCE 3!assert_m.conAE in H.
move: H; apply monotony => // {h} h.
by rewrite sext_Z2u.
rewrite /update_store_lw.
rewrite -mapsto2_mapstos.
rewrite -!assert_m.conAE.
apply con_and_bang_R; last by Reg_upd.
apply inde_upd_store.
rewrite /bang; by Inde.
rewrite !assert_m.conAE.
rewrite -mapsto2_mapstos in H.
rewrite !assert_m.conAE in H.
by [].

(** addiu a1 r0 one16; *)

apply hoare_addiu with (
!(fun s => [rx ]_ s = vx) **
  !(fun s => [rk ]_ s = Z2u 32 (Z_of_nat nk)) **
       var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil **
      int_e ptr |--> nseq nk zero32 ** !(fun s : store.t => [a0 ]_ s = ptr) **
!(fun s => [ a1 ]_s = one32)).

move=> s h H.
rewrite /wp_addiu -mapsto2_mapstos -!assert_m.conAE.
apply con_and_bang_R; last first.
  Reg_upd.
  by rewrite store.get_r0 add0i sext_Z2u.
apply inde_upd_store => //.
rewrite /bang; by Inde.
rewrite !assert_m.conAE.
by rewrite -mapsto2_mapstos !assert_m.conAE in H.

(** sw a1 zero16 a0 *)

apply hoare_sw_back' => s h H.
exists (int_e zero32).
rewrite sext_Z2u //.
destruct nk.
  by case: Hnk.
rewrite subn1.
rewrite [nseq (S nk) zero32]/= in H.
have a0_ptr : [a0]_s = ptr.
  do 4 rewrite assert_m.conCE 3!assert_m.conAE in H.
  apply con_and_bang_inv_L in H.
  tauto.
rewrite -mapsto2_mapstos [_ |--> _]/= in H.
do 4 rewrite assert_m.conCE 4!assert_m.conAE in H.
move: H; apply monotony => // {h}h.
  apply mapsto_ext => //=.
  by rewrite addi0.
apply currying => {h}h H.
rewrite !assert_m.conAE in H.
rewrite -mapsto2_mapstos [_ |--> _]/=.
rewrite -!assert_m.conAE.
do 1 rewrite assert_m.conCE !assert_m.conAE.
move: H; apply monotony => {h}h // H.
do 4 rewrite assert_m.conCE !assert_m.conAE in H.
do 2 rewrite assert_m.conCE !assert_m.conAE.
move: H; apply monotony => {h}h // H.
move: H; apply monotony => {h}h // H.
do 2 rewrite assert_m.conCE !assert_m.conAE in H.
apply con_and_bang_inv_L in H.
case: H => H' H.
do 2 rewrite assert_m.conCE !assert_m.conAE in H.
move: H; apply monotony => {h}h //.
  apply mapsto_ext => //.
  by rewrite /= addi0.
move=> H.
apply con_and_bang_inv_L in H.
case: H => H'' H.
move: H.
apply monotony=> // h3.
apply bangify => ->.
rewrite Z2uK //.
clear -Hnk; simpl in *; omega.
Qed.

Lemma multi_one_s_triple rx rk a0 a1 a2 a3 : uniq(rx, rk, a0, a1, a2, a3, r0) ->
  forall nk X vx ptr, 0 < Z_of_nat nk < 2 ^^ 31 -> size X = nk ->
    u2Z vx + 4 * 2 < \B^1 ->
    u2Z ptr + 4 * Z_of_nat nk < \B^1 ->
    forall slen, s2Z slen = sgZ (s2Z slen) * Z_of_nat nk ->
  {{ fun s h => [ rx ]_s = vx /\ u2Z [ rk ]_s = Z_of_nat nk /\
     (var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X) s h }}
  multi_one_s rx rk a0 a1 a2 a3
  {{ fun s h => [ rx ]_s = vx /\ u2Z [ rk ]_s = Z_of_nat nk /\
     (var_e rx |--> Z2u 32 (Z_of_nat nk) :: ptr :: nil **
       int_e ptr |--> one32 :: nseq (nk - 1) zero32) s h }}.
Proof.
move=> Hnodup nk X vx ptr Hnk X_nk vx_fit ptr_fit slen slen_nk.
move: (multi_one_s_triple_bang _ _ _ _ _ _ Hnodup _ _ _ _ Hnk X_nk vx_fit ptr_fit _ slen_nk) => Htmp.
eapply while.hoare_conseq; last exact: Htmp.
move=> s h H.
apply con_and_bang_inv_L in H; case: H => Hrx H.
split; first by [].
apply con_and_bang_inv_L in H; case: H => Hrk H.
by [].
move=> s h [Hrx [Hrk H]].
apply con_and_bang_L => //.
exact/con_and_bang_L.
Qed.

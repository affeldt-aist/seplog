(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_frame mips_contrib mips_tactics mips_mint.
Import expr_m.
Import assert_m.
Require Import multi_add_s_u_prg pick_sign_prg copy_u_u_prg multi_add_u_u_prg.
Require Import multi_lt_prg multi_sub_u_u_prg multi_negate_prg multi_is_zero_u_prg.
Require Import pick_sign_triple multi_add_u_u_triple.
Require Import multi_lt_triple multi_sub_u_u_R_triple.
Require Import multi_sub_u_u_L_triple multi_negate_triple.
Require Import multi_is_zero_u_triple copy_u_u_triple.

Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope uniq_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope multi_int_scope.

Lemma multi_add_s_u'_triple rk rx ry a0 a1 a2 a3 a4 a5 rX :
  uniq(rk, rx, ry, a0, a1, a2, a3, a4, a5, rX, r0) ->
  forall k vx vy ptr, k <> O -> Z_of_nat k < 2 ^^ 31 ->
    u2Z ptr + 4 * Z_of_nat k < \B^1 ->
  forall X Y, size X = k -> size Y = k -> 0 < \S_{ k } Y ->
  forall slen, s2Z slen = sgZ (s2Z slen) * Z_of_nat k ->
{{ fun s h => [ rx ]_s = vx /\ [ ry ]_s = vy /\ u2Z [ rk ]_s = Z_of_nat k /\
   ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X) ** var_e ry |--> Y) s h }}
 multi_add_s_u0 rk rx ry a0 a1 a2 a3 a4 a5 rX
{{ fun s h => exists X' slen', size X' = k /\
  [ rx ]_s = vx /\ [ ry ]_s = vy /\ s2Z slen' = sgZ (s2Z slen') * Z_of_nat k /\
  sgZ (s2Z slen') = sgZ (sgZ (s2Z slen) * \S_{ k } X + \S_{ k } Y) /\
  ((var_e rx |--> slen' :: ptr :: nil ** int_e ptr |--> X') ** var_e ry |--> Y) s h /\
  u2Z ([a3]_ s) <= 1 /\
  sgZ (s2Z slen') * (\S_{ k } X' + u2Z ([a3]_ s) * \B^k) =
  sgZ (s2Z slen) * \S_{ k } X + \S_{ k } Y }}.
Proof.
move=> Hregs nk va vb ptr Hnk Hnk' ptr_fit A B len_A len_B nk_B slen slen_no_weird.
rewrite /multi_add_s_u0.

(** lw rX four16 rx *)

apply hoare_lw_back_alt'' with (fun s h => [ rx ]_ s = va /\ [ ry ]_ s = vb /\
  u2Z ([ rk ]_ s) = Z_of_nat nk /\ [ rX ]_s = ptr /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e ry |--> B) s h).

rewrite /while.entails => s h [r_a [r_b [r_k Hmem]]].
exists ptr; split.
- rewrite conCE !conAE conCE !conAE
    conCE !conAE in Hmem.
  move: Hmem; apply monotony => // h'; apply mapsto_ext => //; by rewrite sext_Z2u.
- rewrite /update_store_lw.
  repeat Reg_upd; repeat (split => //).
  by Assert_upd.

(** pick_sign rx a0 a1 *)

apply while.hoare_seq with (fun s h => [ rx ]_ s = va /\ [ ry ]_ s = vb /\
  u2Z ([ rk ]_ s) = Z_of_nat nk /\ [ rX ]_s = ptr /\ [a0]_s = slen /\
  sgZ (s2Z [a1]_s) = sgZ (s2Z slen) /\ (s2Z [a1]_s = 0 \/ s2Z [a1]_s = 1 \/ s2Z [a1]_s = -1 ) /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e ry |--> B) s h).

eapply while.hoare_conseq; last first.
apply (pick_sign_triple
  (fun s h => [ ry ]_ s = vb /\ u2Z [ rk ]_ s = Z_of_nat nk /\ [ rX ]_ s = ptr)
  (((var_e rx \+ int_e four32 |~> int_e ptr ** (fun st h0 =>
    u2Z (([ rx ]_ st `+ four32) `+ four32) mod 4 = 0 /\
    emp st h0)) ** int_e ptr |--> A) ** var_e ry |--> B) va slen).

by Uniq_uniq r0.
Inde.
move=> s h x v /= [].
move=> ?; subst a1; by Reg_upd.
case=> // ?; subst a0; by Reg_upd.
by Inde.
move=> s h /= [Ha [Hb [Hk [HX Hmem]]]].
by rewrite !conAE in Hmem *.
move=> s h /= [Ha [Ha0 [Ha1 [Ha1' [Hmem [Hb [Hk HX]]]]]]].
by rewrite !conAE in Hmem *.

(** If_bgez a1 Then *)

apply while.hoare_ifte.

(** If_beq a1, r0 Then *)

apply while.hoare_ifte.

apply while.hoare_seq with (fun s h => [ rx ]_ s = va /\ [ ry ]_ s = vb /\
  u2Z [ rk ]_ s = Z_of_nat nk /\ [ rX ]_ s = ptr /\ [a0 ]_ s = slen /\
  sgZ (s2Z slen) = 0 /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> B) ** var_e ry |--> B) s h).

(** copy_u_u rk rX ry a2 a3 a4 *)

apply (before_frame
  (fun s h => [ rx ]_ s = va /\ [ ry ]_ s = vb /\ [a0 ]_ s = slen /\
    sgZ (s2Z slen) = 0 /\ (var_e rx |--> slen :: ptr :: nil) s h)
  (fun s h => [ rX ]_s = ptr /\ u2Z [ rk ]_s = Z_of_nat nk /\
    (var_e ry |--> B ** var_e rX |--> A) s h)
  (fun s h => [ rX ]_s = ptr /\ u2Z [ rk ]_s = Z_of_nat nk /\
    (var_e ry |--> B ** var_e rX |--> B) s h)).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.

apply copy_u_u_triple => //; by Uniq_uniq r0.
move=> s h [ [[Ha [Hb [Hk [HX [Ha0 [a1_slen [Ha1' mem]]]]]]] _] Ha1].
rewrite conAE in mem.
case: mem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
exists h2, h1.
split; first by heap_tac_m.Disj.
split; first by heap_tac_m.Equal.
repeat (split => //).
rewrite conCE.
move: Hh2; apply monotony => // h'; exact: mapstos_ext.
rewrite /= in Ha1.
move/eqP/u2Z_inj in Ha1.
rewrite store.get_r0 in Ha1.
by rewrite -a1_slen Ha1 s2Z_u2Z_pos' // Z2uK.

move=> s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
case: Hh2 => [Ha [Hb [Ha0 [Ha1' Hh2]]]].
case: Hh1 => Hx [Hk Hh1].
repeat (split => //).
rewrite conAE.
exists h2, h1.
split; first by heap_tac_m.Disj.
split; first by heap_tac_m.Equal.
repeat (split => //).
rewrite conCE.
move: Hh1; apply monotony => h' //; exact: mapstos_ext.

(** addiu a3 r0 zero16 *)

apply hoare_addiu with (fun s h =>
  [ rx ]_ s = va /\ [ ry ]_ s = vb /\ u2Z [ rk ]_ s = Z_of_nat nk /\
  [ rX ]_ s = ptr /\ [a0 ]_ s = slen /\ [a3]_s = zero32 /\
  sgZ (s2Z slen) = 0 /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> B) ** var_e ry |--> B) s h).

move=> s h [Ha [Hb [Hk [HX [Ha0 [Ha1 mem]]]]]].
rewrite /wp_addiu.
repeat Reg_upd; repeat (split => //).
by rewrite add0i sext_Z2u.
by Assert_upd.

(** sw rk zero16 a *)

apply hoare_sw_back'.
move=> s h [Ha [Hb [Hk [HX [Ha0 [Ha3 [Hslen mem]]]]]]].
exists (int_e slen).
rewrite !conAE /= in mem.
move: mem; apply monotony => // h'.
apply mapsto_ext => //; by rewrite /= sext_Z2u // addi0.
apply currying => h'' Hh''.
exists B, (Z2s 32 (Z_of_nat nk)).
repeat (split => //).

rewrite Z2sK //; last lia.
rewrite (proj2 (Zsgn_pos (Z_of_nat nk))); lia.

rewrite Z2sK //; last lia.
rewrite Hslen /= (proj2 (Zsgn_pos (Z_of_nat nk))); last lia.
by rewrite (proj2 (Zsgn_pos (\S_{ nk } B))).

rewrite conCE in Hh''.
rewrite /= !conAE.
move: Hh''; apply monotony => // h'''.
apply mapsto_ext => /=.
by rewrite sext_Z2u // addi0.
apply u2Z_inj.
rewrite Hk u2Z_Z2s_pos //.
split; by [lia | apply: @ltZ_leZ_trans; [exact: Hnk' | ]].
by rewrite Ha3 Z2uK.
rewrite Z2sK //; last lia.
rewrite (proj2 (Zsgn_pos (Z_of_nat nk))); last lia.
by rewrite mul1Z Hslen /= Ha3 Z2uK // mul0Z addZ0.

(** addiu a3 r0 one16; *)

apply hoare_addiu with (fun s h => [ rx ]_ s = va /\ [ ry ]_ s = vb /\ u2Z [ rk ]_ s = Z_of_nat nk /\
  [ rX ]_ s = ptr /\ [a0 ]_ s = slen /\ sgZ (s2Z [a1 ]_ s) = sgZ (s2Z slen) /\
  s2Z [a1]_s = 1 /\ [a3]_s = one32 /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e ry |--> B) s h).

rewrite /wp_addiu => s h [[[Ha [Hb [Hk [HX [Ha0 [Ha1 [Ha1'' mem]]]]]]] Ha1'''] Ha1'].
repeat Reg_upd.
rewrite /= in Ha1' Ha1'''.
move/leZP in Ha1'''.
rewrite store.get_r0 Z2uK // in Ha1'.
move/eqP in Ha1'.
repeat (split => //).
case: Ha1'' => [Ha1'' | [ // | Ha1'']].
rewrite (_ : 0 = s2Z zero32) in Ha1''; last by rewrite s2Z_u2Z_pos' Z2uK.
move/s2Z_inj in Ha1''.
by rewrite Ha1'' Z2uK in Ha1'.
lia.
by rewrite add0i sext_Z2u.
by Assert_upd.

(** multi_add_u_u rk a3 ry rX rX a0 a1 a2 *)

apply while.hoare_seq with (fun s h => exists A' slen', size A' = nk /\
  [ rx ]_ s = va /\ [ ry ]_ s = vb /\ s2Z slen' = sgZ (s2Z slen') * Z_of_nat nk /\
  ((var_e rx |--> slen' :: ptr :: nil ** int_e ptr |--> A') ** var_e ry |--> B) s h /\
  u2Z (store.lo s) <= 1 /\
  sgZ (s2Z slen') = sgZ (sgZ (s2Z slen) * \S_{ nk } A + \S_{ nk } B) /\
  sgZ (s2Z slen') * (\S_{ nk } A' + u2Z (store.lo s) * \B^nk) =
  sgZ (s2Z slen) * \S_{ nk } A + \S_{ nk } B).

have : uniq(rk, a3, ry, rX, a0, a1, a2, r0) by Uniq_uniq r0.
move/multi_add_u_u_triple.
move/(_ nk vb ptr ptr_fit _ _ len_B len_A) => Htmp.

apply (before_frame
  (fun s h => sgZ (s2Z slen) = 1 /\ [ rx ]_ s = va /\ (var_e rx |--> slen :: ptr :: nil) s h)
  (fun s h =>
    ([a3]_s = one32 /\ [ ry ]_ s = vb /\ [ rX ]_ s = ptr /\ u2Z ([ rk ]_ s) = Z_of_nat nk /\
      (var_e rX |--> A ** var_e ry |--> B) s h) /\
    [ rx ]_ s = va /\ [a0 ]_ s = slen /\ 0 <= sgZ (s2Z slen) /\ eval_b (bgez a1) s)
  (fun s h => exists A',
    size A' = nk /\ [ ry ]_s = vb /\ [ rX ]_ s = ptr /\ (var_e ry |--> B ** var_e rX |--> A') s h /\
    u2Z (store.lo s) <= 1 /\ \S_{ nk } A' + u2Z (store.lo s) * \B^nk = \S_{ nk } A + \S_{ nk } B)).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.
eapply while.hoare_conseq; last exact: Htmp.
by rewrite addZC.

rewrite /while.entails => s h [[Hone [Hb [HX [Hk Hmem]]]] [Ha [Ha0 [HZsgn Ha1]]]].
move/leZP in Ha1.
by rewrite conCE in Hmem.

rewrite /while.entails => s h [Ha [Hb [Hk [HX [Ha0 [Hsgn [Hsgn' [Ha3 Hmem]]]]]]]].
rewrite conAE in Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
exists h2, h1.
split; first by heap_tac_m.Disj.
split; first by heap_tac_m.Equal.
repeat (split => //).
move: Hh2; apply monotony => h' //; exact: mapstos_ext.
rewrite -Hsgn; by rewrite Hsgn'.
rewrite /=; apply/leZP; lia.
by rewrite -Hsgn Hsgn'.

rewrite /while.entails => s h [h1 [h2 [h1_d_h2 [h1_U_h2 [[A' [A'_nk [r_b [HX [Hh1 [Hlo Hsum]]]]]] [Hsgn [r_a Hh2]]]]]]].
exists A', slen.
repeat (split => //).
rewrite conAE.
exists h2, h1.
split; first by heap_tac_m.Disj.
split; first by heap_tac_m.Equal.
split; first by [].
rewrite conCE.
move: Hh1; apply monotony => h' //; exact: mapstos_ext.
rewrite Hsgn mul1Z (proj2 (Zsgn_pos (\S_{ nk } A + \S_{ nk } B))) //.
move: (min_lSum nk A) => ?; lia.
by rewrite Hsgn 2!mul1Z.

(** mflo a3 *)

apply hoare_mflo'.

rewrite /while.entails => s h [A' [slen' [len_A' [r_a [r_b [slen'_nk [Hmem [Hlo [Hsgn Hsum]]]]]]]]].
rewrite /wp_mflo.
exists A', slen'.
repeat Reg_upd; repeat (split => //).
move: Hmem; apply inde_upd_store; by Inde.

(** multi_lt rk ry rX a0 a1 a5 a2 a3 a4 ; *)

apply while.hoare_seq with (fun s h =>
  ([ rx ]_ s = va /\ [ ry ]_ s = vb /\ u2Z ([ rk ]_ s) = Z_of_nat nk /\
    [ rX ]_ s = ptr /\ sgZ (s2Z slen) = -1 /\
    ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e ry |--> B) s h) /\
  ((\S_{ nk } B < \S_{ nk } A /\ [a5]_s = one32 /\ [a2]_s = zero32 ) \/
   (\S_{ nk } B > \S_{ nk } A /\ [a5]_s = zero32 /\ [a2]_s = one32 ) \/
   (\S_{ nk } B = \S_{ nk } A /\ [a5]_s = zero32 /\ [a2]_s = zero32))).

apply (before_frame
  (fun s h => [ rx ]_ s = va /\ sgZ (s2Z slen) = -1 /\ (var_e rx |--> slen :: ptr :: nil) s h)
  (fun s h => u2Z [ rk ]_s = Z_of_nat nk /\
    [ ry ]_s = vb /\ [ rX ]_s = ptr /\ (var_e ry |--> B ** var_e rX |--> A) s h)
  (fun s h => u2Z ([ rk ]_ s) = Z_of_nat nk /\ [ ry ]_ s = vb /\ [ rX ]_ s = ptr /\
    ((\S_{ nk } B < \S_{ nk } A /\ ([a5 ]_ s) = one32 /\ [a2]_s = zero32) \/
      (\S_{ nk } B > \S_{ nk } A /\ ([a5 ]_ s) = zero32 /\ [a2]_s = one32) \/
      (\S_{ nk } B = \S_{ nk } A /\ ([a5 ]_ s) = zero32 /\ [a2]_s = zero32)) /\
    (var_e ry |--> B ** var_e rX |--> A) s h)).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.
apply multi_lt_triple => //; by Uniq_uniq r0.

rewrite /while.entails => s h [[Ha [Hb [Hk [HX [Ha0 [HZgn [Hsgn' Hmem]]]]]]] Ha1].
rewrite conAE in Hmem.
case : Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h2 h1.
repeat (split => //).
rewrite conCE.
move: Hh2; apply monotony => // h'; exact: mapstos_ext.
repeat (split => //).
rewrite /= in Ha1.
move/leZP in Ha1.
case: Hsgn' => Hsgn'; first lia.
case: Hsgn' => Hsgn'; first lia.
by rewrite -HZgn Hsgn'.

rewrite /while.entails => s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
case: Hh1 => Hk [Hb [hX [Hsum Hh1]]].
case: Hh2 => Ha [Hsgn Hh2].
split.
- repeat (split => //).
  rewrite conAE.
  Compose_sepcon h2 h1 => //.
  rewrite conCE.
  move: Hh1; apply monotony => // h'; exact: mapstos_ext.
- case: Hsum => Hsum.
  left; tauto.
  by right.

(** If_beq a5,r0 Then *)

apply while.hoare_ifte.

(** If_beq a2,r0 Then *)

apply while.hoare_ifte.

(** addiu a3 r0 zero16 ; *)

apply hoare_addiu with (fun s h => [ rx ]_ s = va /\ [ ry ]_ s = vb /\
  u2Z [ rk ]_ s = Z_of_nat nk /\ [ rX ]_ s = ptr /\ [a3]_s = zero32 /\
  sgZ (s2Z slen) = -1 /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e ry |--> B) s h  /\
  \S_{ nk } B = \S_{ nk } A).

move=> s h [ [[ [Ha [Hb [Hk [HX [Hslen mem]]] ]] Hsum] Ha5] Ha2].
rewrite /wp_addiu.
repeat Reg_upd; repeat (split => //).
by rewrite add0i sext_Z2u.
by Assert_upd.
rewrite /= in Ha5 Ha2.
move/eqP/u2Z_inj in Ha5.
move/eqP/u2Z_inj in Ha2.
case: Hsum => Hsum.
- rewrite Ha5 store.get_r0 in Hsum.
  case: Hsum => _ [Hsum _].
  by apply Z2u_dis in Hsum.
- case: Hsum => Hsum; last tauto.
  case: Hsum => _ [_ Hsum].
  rewrite Ha2 store.get_r0 in Hsum.
  by apply Z2u_dis in Hsum.

(** sw r0 zero16 rx *)

apply hoare_sw_back'.
move=> s h [Ha [Hb [Hk [HX [Ha3 [Hslen [mem Hsum]]]]]]].
exists (int_e slen).
rewrite !conAE /= in mem.
move: mem; apply monotony => // h'.
apply mapsto_ext => //=; by rewrite sext_Z2u // addi0.
apply currying => h'' Hh''.
exists A (*NB: whatever*), (Z2s 32 0).
repeat (split => //).
by rewrite Z2sK.

by rewrite Z2sK //= Hslen Hsum addZC mulN1Z addZN.
rewrite conCE in Hh''.
rewrite !conAE /=.
move: Hh''; apply monotony => // h'''.
apply mapsto_ext => /=.
by rewrite sext_Z2u // addi0.
rewrite store.get_r0.
apply u2Z_inj.
by rewrite Z2uK // u2Z_Z2s_pos.
by rewrite Ha3 Z2uK.
rewrite Z2sK //= Hslen Hsum; ring.

(** multi_sub_u_u rk ry rX rX a0 a1 a2 a3 a4 a5 ; *)

apply hoare_prop_m.hoare_stren with (fun s h => \S_{ nk } B > \S_{ nk } A /\
  (([ rx ]_ s = va /\ [ ry ]_ s = vb /\ u2Z ([ rk ]_ s) = Z_of_nat nk /\
    [ rX ]_ s = ptr /\ sgZ (s2Z slen) = -1 /\
    ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e ry |--> B) s h))).

rewrite /while.entails => s h [[[[Ha [Hb [Hk [HX [Hsgn Hmem]]]]] Hsum] Ha5] Ha2].
repeat (split => //).
rewrite /= store.get_r0 Z2uK // in Ha5.
move/eqP in Ha5.
case: Hsum => Hsum.
- case: Hsum => _ [Hsum _].
  by rewrite Hsum Z2uK in Ha5.
- rewrite /= in Ha2.
  move/eqP in Ha2.
  case: Hsum => Hsum; first by tauto.
  case: Hsum => _ [_ Hsum].
  by rewrite Hsum Z2uK // store.get_r0 // Z2uK in Ha2.

apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => HAB.

apply while.hoare_seq with (fun s h => exists A', size A' = nk /\
  [ rx ]_ s = va /\ [ ry ]_ s = vb /\ s2Z slen = sgZ (s2Z slen) * Z_of_nat nk /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A') ** var_e ry |--> B) s h /\
  [a3]_s = zero32 /\ sgZ (s2Z slen) = -1 /\
  - sgZ (s2Z slen) * (\S_{ nk } A' - u2Z ([a3 ]_ s) * \B^nk) =
  sgZ (s2Z slen) * \S_{ nk } A + \S_{ nk } B).

apply (before_frame
  (fun s h => [ rx ]_ s = va /\ sgZ (s2Z slen) = -1 /\ (var_e rx |--> slen :: ptr :: nil) s h)
  (fun s h => [ ry ]_s = vb /\ [ rX ]_ s = ptr /\ u2Z ([ rk ]_ s) = Z_of_nat nk /\
    (var_e ry |--> B ** var_e rX |--> A) s h)
  (fun s h => exists A', size A' = nk /\
    [ ry ]_s = vb /\ [ rX ]_ s = ptr /\ u2Z ([ rk ]_ s) = Z_of_nat nk /\ [a3]_s = zero32 /\
    (var_e ry |--> B ** var_e rX |--> A') s h /\ \S_{ nk } A' = \S_{ nk } B - \S_{ nk } A)).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.

apply multi_sub_u_u_R_triple_B_le_A => //.
by Uniq_uniq r0.
lia.

rewrite /while.entails => s h [Ha [Hb [Hk [HX [Hsgn Hmem]]]]].
rewrite conAE in Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h2 h1; last by [].
repeat (split => //).
rewrite conCE.
move: Hh2; apply monotony => h' //; exact: mapstos_ext.

rewrite /while.entails => s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 [Hva [Hsgn Hh2]]]]]]].
case: Hh1 => A' [len_A' [Hb [HX [Hk [Ha3 [Hh1 Hsum]]]]]].
exists A'.
repeat (split => //).
rewrite conAE.
Compose_sepcon h2 h1 => //.
rewrite conCE.
move: Hh1; apply monotony => // h'; exact: mapstos_ext.
rewrite Hsgn mulNZ mulN1Z oppZK Hsum Ha3 Z2uK // mul0Z subZ0; ring.

apply (hoare_prop_m.extract_exists extract_exists0) => A'.

(** multi_negate rx a0 *)

apply (before_frame (fun s h => size A' = nk /\ [ rx ]_ s = va /\ [ ry ]_ s = vb /\
  s2Z slen = sgZ (s2Z slen) * Z_of_nat nk /\
  (var_e ry |--> B) s h /\ [a3 ]_ s = zero32 /\ sgZ (s2Z slen) = -1 /\
  - sgZ (s2Z slen) * (\S_{ nk } A' - u2Z [a3 ]_ s * \B^nk) = sgZ (s2Z slen) * \S_{ nk } A + \S_{ nk } B)
(var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A')
(var_e rx |--> cplt2 slen :: ptr :: nil ** int_e ptr |--> A')).

apply frame_rule_R.
- apply multi_negate_triple; by Uniq_uniq r0.
- Inde_frame.
  rewrite /inde => s h x v /= [] // ?; subst x; by Reg_upd.
- move=> ?; by Inde_mult.

rewrite /while.entails => s h [lenA' [r_a [r_b [slen'_nk [Hmem [Ha3 [Hsgn HSum]]]]]]].
move: Hmem; exact: monotony.

rewrite /while.entails => s h Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh2 => A'_nk [slen_nk_ [r_a [r_b [Hh2 [Ha3 [HZsgn HSum]]]]]].
exists (cplt2 slen).
rewrite s2Z_cplt2; last first.
  rewrite weirdE2 slen_no_weird HZsgn; lia.
rewrite Ha3 Z2uK // mul0Z subZ0 in HSum.
rewrite Ha3 Z2uK // mul0Z addZ0 Zsgn_Zopp.
repeat (split => //).

have Htmp : - sgZ (s2Z slen) = 1 by rewrite HZsgn.
rewrite !Htmp HZsgn in HSum *.
rewrite r_b HZsgn; ring.

have Htmp : - sgZ (s2Z slen) = 1 by rewrite HZsgn.
rewrite !Htmp HZsgn in HSum *.
rewrite mul1Z in HSum.
rewrite -HSum (proj2 (Zsgn_pos (\S_{ nk } A'))) //.
move: (min_lSum nk A) => ?.
rewrite HSum mulN1Z; lia.
by Compose_sepcon h1 h2.

(** multi_sub_u_u k rX b rX a0 a1 a5 a3 a2 a4 *)

apply hoare_prop_m.hoare_stren with (fun s h => \S_{ nk } B < \S_{ nk } A /\
  ([ rx ]_ s = va /\ [ ry ]_ s = vb /\ u2Z ([ rk ]_ s) = Z_of_nat nk /\ [ rX ]_ s = ptr /\
    sgZ (s2Z slen) = -1 /\
    ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e ry |--> B) s h)).

rewrite /while.entails => s h [[[Ha [Hb [Hk [HX [Hslen Hmem]]]]] Hsum] Ha5].
case: Hsum => Hsum; first by tauto.
rewrite /= in Ha5.
move/eqP in Ha5.
rewrite store.get_r0 in Ha5.
case: Hsum.
case=> _ [Hsum _].
by rewrite Hsum Z2uK in Ha5.
case=> _ [Hsum _].
by rewrite Hsum Z2uK in Ha5.

apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => HAB.

apply (before_frame
  (fun s h => [ rx ]_ s = va /\ sgZ (s2Z slen) = -1 /\ (var_e rx |--> slen :: ptr :: nil) s h)
  (fun s h => [ rX ]_s = ptr /\
  [ ry ]_s = vb /\ u2Z ([ rk ]_ s) = Z_of_nat nk /\ (var_e rX |--> A ** var_e ry |--> B) s h)
  (fun s h => exists A', size A' = nk /\
    [ rX ]_s = ptr /\ [ ry ]_s = vb /\ u2Z ([ rk ]_ s) = Z_of_nat nk /\ [a3]_s = zero32 /\
    (var_e rX |--> A' ** var_e ry |--> B) s h /\ \S_{ nk } A' = \S_{ nk } A - \S_{ nk } B)).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.

apply multi_sub_u_u_L_triple_B_le_A => //.
by Uniq_uniq r0.
exact/ltZW.

rewrite /while.entails => s h [Ha [Hb [Hk [HX [Hslen Hmem]]]]].
rewrite conAE in Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h2 h1; last by [].
repeat (split => //).
move: Hh2; apply monotony => // h'; exact: mapstos_ext.

rewrite /while.entails => s h Hmem.
case: Hmem =>  h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh1 => A' [len_A' [HX [Hb [Hk [Ha3 [Hh1 Hsum]]]]]].
case: Hh2 => Ha [Hsgn Hh2].
exists A', slen.
repeat (split => //).
rewrite Hsgn (proj2 (Zsgn_neg (-1 * \S_{ nk } A + \S_{ nk } B))) // addZC mulN1Z addZNE; lia.
rewrite conAE.
Compose_sepcon h2 h1; first by [].
move: Hh1; apply monotony => // h'.
exact: mapstos_ext.
by rewrite Ha3 Z2uK.
rewrite Hsgn 2!mulN1Z Hsum Ha3 Z2uK // mul0Z; ring.
Qed.

Lemma multi_add_s_u_triple_gen rk rx ry a0 a1 a2 a3 a4 a5 rX :
  uniq(rk, rx, ry, a0, a1, a2, a3, a4, a5, rX, r0) ->
  forall k va vb ptr, k <> O -> Z_of_nat k < 2 ^^ 31 ->
    u2Z ptr + 4 * Z_of_nat k < \B^1 -> u2Z vb + 4 * Z_of_nat k < \B^1 ->
  forall X Y, size X = k -> size Y = k ->
  forall slen, s2Z slen = sgZ (s2Z slen) * Z_of_nat k ->
    sgZ (s2Z slen) = sgZ (sgZ (s2Z slen) * \S_{ k } X) ->
{{ fun s h => [ rx ]_s = va /\ [ ry ]_s = vb /\
    u2Z [ rk ]_s = Z_of_nat k /\
    ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> X) ** var_e ry |--> Y) s h }}
 multi_add_s_u rk rx ry a0 a1 a2 a3 a4 a5 rX
 {{ fun s h => exists X' slen', size X' = k /\
   [ rx ]_s = va /\ [ ry ]_s = vb /\ s2Z slen' = sgZ (s2Z slen') * Z_of_nat k /\
   sgZ (s2Z slen') = sgZ (sgZ (s2Z slen) * \S_{ k } X + \S_{ k } Y) /\
   ((var_e rx |--> slen' :: ptr :: nil ** int_e ptr |--> X') ** var_e ry |--> Y) s h /\
   u2Z ([a3]_ s) <= 1 /\
   sgZ (s2Z slen') * (\S_{ k } X' + u2Z ([a3]_ s) * \B^k) =
   sgZ (s2Z slen) * \S_{ k } X + \S_{ k } Y }}.
Proof.
move=> Hregs nk va vb ptr Hnk Hnk' ptr_fit vb_fit A B
  len_A len_B slen slen_no_weird slen_A.
rewrite /multi_add_s_u.

(** multi_is_zero_u rk ry a0 a1 a2 ; *)

apply while.hoare_seq with (fun s h => [ rx ]_s = va /\ [ ry ]_s = vb /\
  u2Z [ rk ]_s = Z_of_nat nk /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e ry |--> B) s h /\
  ((0 = \S_{ nk } B -> [a2]_s = one32) /\ (0 < \S_{ nk } B -> [a2]_s = zero32))).

apply (before_frame(fun s h => [ rx ]_ s = va /\
  (var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) s h)
  (fun s h => u2Z [ rk ]_s = Z_of_nat nk /\ [ ry ]_s = vb /\ (var_e ry |--> B) s h)
  (fun s h => u2Z [ rk ]_s = Z_of_nat nk /\ [ ry ]_s = vb /\ (var_e ry |--> B) s h  /\
    ((0 = \S_{ nk } B -> [a2]_s = one32) /\   (0 < \S_{ nk } B -> [a2]_s = zero32)))).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.
  apply multi_is_zero_u_triple => //.
  by Uniq_uniq r0.

move=> s h [Ha [Hb [Hk mem]]].
case: mem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h2 h1.
by repeat (split => //).
by repeat (split => //).
move => s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
repeat (split; first by tauto).
split; last by tauto.
Compose_sepcon h2 h1; tauto.

(** If_bne a2,r0 Then *)

apply while.hoare_ifte.

(** addiu a3 r0 zero16 *)

apply hoare_addiu'.
move=> s h [ [Ha [Hb [Hk [mem Ha5]]]] Ha2].
rewrite /= in Ha2.
move/eqP in Ha2.
move: (min_lSum nk B).
case/Z_le_lt_eq_dec => Hsum.
apply (proj2 Ha5) in Hsum.
by rewrite Hsum Z2uK // store.get_r0 Z2uK in Ha2.
exists A, slen.
repeat Reg_upd; repeat (split => //).
rewrite -Hsum addZ0; exact slen_A.
by Assert_upd.
by rewrite sext_Z2u // addi0 Z2uK.
rewrite sext_Z2u // addi0 Z2uK // mul0Z addZ0 -Hsum; ring.

(** multi_add_s_u0 rk rx ry a0 a1 a2 a3 a4 a5 rX *)

apply hoare_prop_m.hoare_stren with
  (!(fun s => 0 < \S_{ nk } B) **
    (fun s h => [ rx ]_ s = va /\ [ ry ]_ s = vb /\ u2Z [ rk ]_ s = Z_of_nat nk /\
      ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e ry |--> B) s h)).

move=> s h [[Ha [Hb [Hk [mem Ha2']]]] Ha2].
rewrite /= negbK in Ha2.
move/eqP/u2Z_inj in Ha2.
move: (min_lSum nk B).
case/Z_le_lt_eq_dec => Hsum; last first.
   apply (proj1 Ha2') in Hsum.
   rewrite Hsum store.get_r0 in Ha2.
   by apply Z2u_dis in Ha2.
by Compose_sepcon heap.emp h.

apply pull_out_bang => nk_B.
exact: multi_add_s_u'_triple.
Qed.

Lemma multi_add_s_u_triple rk rx ry a0 a1 a2 a3 a4 a5 rX :
  uniq(rk, rx, ry, a0, a1, a2, a3, a4, a5, rX, r0) ->
  forall k, 0 < Z_of_nat k < 2 ^^ 31 -> (* not the weird number *)
  forall vx vy X Y,
{{ fun s h => [rx]_s = vx /\ [ry]_s = vy /\
    u2Z [rk]_s = Z_of_nat k /\
    (var_signed k rx X ** var_unsign k ry Y) s h }}
 multi_add_s_u rk rx ry a0 a1 a2 a3 a4 a5 rX
 {{ fun s h => exists X' l' ptr, size X' = k /\
   [rx]_s = vx /\ [ry]_s = vy /\ s2Z l' = sgZ (s2Z l') * Z_of_nat k /\
   sgZ (s2Z l') = sgZ (X + Y) /\
   ((var_e rx |--> l' :: ptr :: List.nil ** int_e ptr |--> X') **
     var_unsign k ry Y) s h /\
   u2Z ([a3]_ s) <= 1 /\
   sgZ (s2Z l') * (\S_{ k } X' + u2Z ([a3]_ s) * \B^k) = X + Y }}.
Proof.
move=> Hvars nk nk_0_max va vb A B.
apply hoare_prop_m.hoare_stren with (fun s h => exists slen ptr A0,
      u2Z va + 4 * 2 < \B^1 /\
      0 <= B < \B^nk /\
      sgZ (s2Z slen) = sgZ A /\
      u2Z ptr + 4 * Z_of_nat nk < \B^1 /\
      u2Z vb + 4 * Z_of_nat nk < \B^1 /\
      s2Z slen = sgZ (s2Z slen) * Z_of_nat nk /\
      A = sgZ (s2Z slen) * \S_{ nk } A0 /\
      size A0 = nk /\
      [rx]_s = va /\ [ry]_s = vb /\
      u2Z [rk ]_ s = Z_of_nat nk /\
      ((fun st h0 =>
        ((var_e rx |--> slen :: (ptr :: Datatypes.nil)%list **
          int_e ptr |--> A0) st h0)) **
       (fun st h0 =>
        (var_e ry |--> Z2ints 32 nk B) st h0))
        s h).
  move=> s h H.
  case: H => k_nk [a_va [b_vb [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]]]].
  case: Hh1 => slen ptr A0 a_fit encodingA ptr_fit Hmem.
  case: Hh2 => b_fit B_over G_mem.
  exists slen, ptr, A0; repeat (split => //).
  by subst va.
  by case: encodingA => *.
  by subst vb.
  by case: encodingA => *.
  by case: encodingA => *.
  by case: encodingA => *.
  by exists h1, h2.
apply mips_contrib.pull_out_exists => slen.
apply mips_contrib.pull_out_exists => ptr.
apply mips_contrib.pull_out_exists => A0.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => ?.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => ?.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => slen_A.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => ptr_fit.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => vb_fit.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => slen_nk.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => A_A0.
apply (hoare_prop_m.pull_out_conjunction' mips_contrib.hoare0_false) => A0_nk.
apply while.hoare_conseq with
  (P' := fun s h => [rx]_s = va /\ [ry]_s = vb /\ u2Z [rk]_s = Z_of_nat nk /\
    ((var_e rx |--> slen :: ptr :: List.nil **
      int_e ptr |--> A0) ** var_e ry |--> Z2ints 32 nk B) s h)
  (Q':= fun s h => exists A' slen', size A' = nk /\
    [rx]_s = va /\ [ry]_s = vb /\ s2Z slen' = sgZ (s2Z slen') * Z_of_nat nk /\
    sgZ (s2Z slen') = sgZ (sgZ (s2Z slen) * \S_{ nk } A0 + \S_{ nk } (Z2ints 32 nk B)) /\
    ((var_e rx |--> slen' :: ptr :: List.nil ** int_e ptr |--> A') **
      var_e ry |--> Z2ints 32 nk B) s h /\
    u2Z ([a3]_ s) <= 1 /\
   sgZ (s2Z slen') * (\S_{ nk } A' + u2Z ([a3]_ s) * \B^nk) =
   sgZ (s2Z slen) * \S_{ nk } A0 + \S_{ nk } (Z2ints 32 nk B)).
- move=> s h H.
  case: H => A' [slen' [A'_nk [a_va [b_vb [slen'_nk [slen'_A_B [Hmem [Ha3 HA']]]]]]]].
  exists A', slen', ptr.
  repeat (split => //).
  + rewrite slen'_A_B.
    rewrite lSum_Z2ints; last by rewrite Z.abs_eq; tauto.
    rewrite A_A0.
    rewrite Z.abs_eq; tauto.
  + move: Hmem; apply assert_m.monotony => // h' Hh'.
    apply mkVarUnsign => //.
    congruence.
  + rewrite lSum_Z2ints in HA'; last by rewrite Z.abs_eq; tauto.
    rewrite HA' -A_A0 Z.abs_eq; tauto.
- move=> s h [a_va [b_vb [k_nk H]]].
  case: H => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
  repeat (split; first by []).
  by exists h1, h2.
- apply multi_add_s_u_triple_gen => //.
  lia.
  by case: nk_0_max.
  by rewrite size_Z2ints.
  by rewrite -A_A0.
Qed.

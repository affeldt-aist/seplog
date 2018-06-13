(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int multi_int uniq_tac.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_frame mips_tactics.
Import expr_m.
Import assert_m.
Require Import multi_sub_s_u_prg multi_add_s_u_triple pick_sign_triple.
Require Import copy_u_u_triple multi_is_zero_u_triple multi_negate_triple.
Require Import multi_sub_u_u_L_triple multi_sub_u_u_R_triple.
Require Import multi_add_u_u_triple.

Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.
Local Open Scope heap_scope.
Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope mips_assert_scope.
Local Open Scope multi_int_scope.

(* TODO: rename registers *)
Lemma multi_sub_s_u0_triple k a b a0 a1 a2 a3 a4 ret X :
uniq(k, a, b, a0, a1, a2, a3, a4, ret, X, r0) ->
forall nk va vb ptr, nk <> O -> Z_of_nat nk < 2 ^^ 31 ->
  u2Z ptr + 4 * Z_of_nat nk < \B^1 ->
forall A B, size A = nk -> size B = nk -> 0 < \S_{ nk } B ->
forall slen, s2Z slen = sgZ (s2Z slen) * Z_of_nat nk ->
{{ fun s h => [ a ]_s = va /\ [ b ]_s = vb /\  u2Z [ k ]_s = Z_of_nat nk /\
   ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h }}
multi_sub_s_u0 k a b a0 a1 a2 a3 a4 ret X
{{ fun s h => exists A' slen', size A' = nk /\ [ a ]_s = va /\
  [ b ]_s = vb /\ s2Z slen' = sgZ (s2Z slen') * Z_of_nat nk /\
  sgZ (s2Z slen') = sgZ (sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B) /\
  ((var_e a |--> slen' :: ptr :: nil ** int_e ptr |--> A') ** var_e b |--> B ) s h /\
  u2Z ([ a3 ]_ s) <= 1 /\
  sgZ (s2Z slen') * (\S_{ nk } A' + u2Z ([ a3 ]_s) * \B^nk) =
    sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B }}.
Proof.
move=> Hregs nk va vb ptr Hnk Hnk' ptr_fit A B len_A len_B nk_B slen slen_not_weird.
rewrite /multi_sub_s_u0.

(** lw X four16 a *)

apply hoare_lw_back_alt'' with (fun s h => [a ]_ s = va /\ [b ]_ s = vb /\
  u2Z ([k ]_ s) = Z_of_nat nk /\ [X ]_s = ptr /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h).

rewrite /while.entails => s h [r_a [r_b [r_k Hmem]]].
exists ptr; split.
- rewrite conCE !conAE conCE !conAE
  conCE !conAE in Hmem.
  move: Hmem; apply monotony => // h'; apply mapsto_ext => //.
  by rewrite sext_Z2u.
- rewrite /update_store_lw.
  repeat Reg_upd; repeat (split => //).
  by Assert_upd.

(** pick_sign a a0 a1 *)

apply while.hoare_seq with (fun s h =>
  [a ]_ s = va /\ [b ]_ s = vb /\ u2Z ([k ]_ s) = Z_of_nat nk /\
  [X ]_s = ptr /\ [a0]_s = slen /\ sgZ (s2Z [a1 ]_ s) = sgZ (s2Z slen) /\
  (s2Z [ a1 ]_ s = 0 \/ s2Z [ a1 ]_ s = 1 \/ s2Z [ a1 ]_s = - 1) /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h).

eapply while.hoare_conseq; last first.
(* TODO: use machine_int notation *)
- apply (pick_sign_triple (fun s h =>
    [b ]_ s = vb /\ u2Z [k ]_ s = Z_of_nat nk /\
    [X ]_ s = ptr) (((var_e a \+ int_e four32 |~> int_e ptr **
      (fun st h0 => u2Z (([a ]_ st `+ four32) `+ four32) mod 4 = 0 /\
        emp st h0)) ** int_e ptr |--> A) ** var_e b |--> B) va slen).
  + by Uniq_uniq r0.
  + Inde.
    move=> s h x v /= [] //.
    move=> ?; subst a1; by Reg_upd.
    case=> // ?; subst a0; by Reg_upd.
  + by Inde.
- move=> s h /= [Ha [Hb [Hk [HX Hmem]]]].
  by rewrite !conAE in Hmem *.
- move=> s h [Ha [Ha0 [Ha1 [Ha1' [Hmem [Hb [Hk HX]]]]]]].
  by rewrite !conAE in Hmem *.

(** while.ifte (bgez a1) *)

apply while.hoare_ifte.

apply while.hoare_ifte.

apply while.hoare_seq with (fun s h =>
  [a ]_ s = va /\ [b ]_ s = vb /\ u2Z ([k ]_ s) = Z_of_nat nk /\
  [X ]_ s = ptr /\ 0 = sgZ (s2Z slen) /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> B) ** var_e b |--> B) s h).

(** copy k X b a2 a3 a4 *)

apply (before_frame
  (fun s h => [a ]_ s = va /\ [b ]_ s = vb /\ [a0 ]_ s = slen /\
    sgZ (s2Z slen) = 0 /\ (var_e a |--> slen :: ptr :: nil) s h)
  (fun s h => [X]_s = ptr /\ u2Z [k]_s = Z_of_nat nk /\
    (var_e b |--> B ** var_e X |--> A) s h)
  (fun s h => [X]_s = ptr /\ u2Z [k]_s = Z_of_nat nk /\
    (var_e b |--> B ** var_e X |--> B) s h)).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.
apply copy_u_u_triple => //; by Uniq_uniq r0.

move=> s h [ [ [Ha [Hb [Hk [HX [Ha0 [a1_slen [Ha1' mem]]]]]] _] Ha1] ].
rewrite conAE in mem.
case: mem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
exists h2, h1.
split; first by heap_tac_m.Disj.
split; first by heap_tac_m.Equal.
repeat (split => //).
rewrite conCE.
move: Hh2; apply monotony => // h'; exact: mapstos_ext.
rewrite /= in Ha1; move/eqP/u2Z_inj in Ha1.
rewrite store.get_r0 /= in Ha1.
rewrite -a1_slen Ha1 s2Z_u2Z_pos'; by rewrite Z2uK.

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

apply hoare_addiu with (fun s h => [a ]_ s = va /\ [b ]_ s = vb /\
  u2Z [k ]_ s = Z_of_nat nk /\ [X ]_ s = ptr /\ [a3]_s = zero32 /\
  0 = sgZ (s2Z slen) /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> B) ** var_e b |--> B) s h).
move=> s h [Ha [Hb [Hk [HX [Hslen mem]]]]].
rewrite /wp_addiu.
repeat Reg_upd.
repeat (split=> //).
by rewrite sext_Z2u // addi0.
by Assert_upd.

(** sw k zero16 a *)

apply hoare_sw_back'' with (fun s h => [a ]_ s = va /\ [b ]_ s = vb /\
 u2Z [k ]_ s = Z_of_nat nk /\ [X ]_ s = ptr /\ [a3 ]_ s = zero32 /\
 0 = sgZ (s2Z slen) /\
 ((var_e a |--> Z2s 32 (Z_of_nat nk) :: ptr :: nil ** int_e ptr |--> B) ** var_e b |--> B) s h).

move=> s h [Ha [Hb [Hk [HX [Ha3 [Hslen mem]]]]]].
exists (int_e slen).
rewrite !conAE /= in mem.
move: mem; apply monotony => // h'.
apply mapsto_ext => //; by rewrite /= sext_Z2u // addi0.
apply currying => h'' Hh''.
repeat (split => //).
rewrite conCE in Hh''.
rewrite /= !conAE.
move: Hh''; apply monotony => // h'''.
apply mapsto_ext => /=.
by rewrite sext_Z2u // addi0.
apply u2Z_inj.
rewrite Hk u2Z_Z2s_pos //.
split; by [apply Zle_0_nat |(apply: @ltZ_leZ_trans; [exact: Hnk'|])].

(** negate a a0 *)

apply hoare_prop_m.hoare_weak with (fun s h =>
  [a ]_ s = va /\ [b ]_ s = vb /\
  sgZ (- Z_of_nat nk) = sgZ (sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B) /\
  ((var_e a |--> Z2s 32 (- Z_of_nat nk) :: ptr :: nil ** int_e ptr |--> B) ** var_e b |--> B) s h /\
  u2Z [a3 ]_ s <= 1 /\ 0 = sgZ (s2Z slen) /\
  sgZ (- Z_of_nat nk) * (\S_{ nk } B + u2Z [a3 ]_ s * \B^nk) = sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B).
move=> s h [Ha [Hb [Hsgn [mem [Ha3 [Hslen HSum]]]]]].
exists B, (Z2s 32 (- Z_of_nat nk)).
repeat (split=> //).

rewrite Z2sK //; last omega.
rewrite (proj2 (Zsgn_neg (- Z_of_nat nk))) //; omega.
rewrite Z2sK //; omega.
rewrite Z2sK //; omega.

apply (before_frame
  (fun s h => [a ]_ s = va /\ [b ]_ s = vb /\ (var_e b |--> B) s h /\
    u2Z [a3 ]_ s <= 1 /\ 0 = sgZ (s2Z slen) /\
    - sgZ (Z_of_nat nk) * (\S_{ nk } B + u2Z [a3 ]_ s * \B^nk) =
    sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B)
  (var_e a |--> Z2s 32 (Z_of_nat nk) :: ptr :: nil ** int_e ptr |--> B)
  (var_e a |--> cplt2 (Z2s 32 (Z_of_nat nk)) :: ptr :: nil ** int_e ptr |--> B)).

apply frame_rule_R.
- apply multi_negate_triple => //; by Uniq_uniq r0.
  Inde_frame; rewrite /inde => s h x v /= [] // ?; subst x; by Reg_upd.
- move=> ?; by Inde_mult.

move=> s h [Ha [Hb [Hk [HX [Ha3 [Hsgn mem]]]]]].
case: mem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h1 h2; first by exact Hh1.
repeat (split=> //).
by rewrite Ha3 Z2uK.
rewrite -Hsgn mul0Z /= Ha3 Z2uK // mul0Z addZ0 (proj2 (Zsgn_pos (Z_of_nat nk))) //; omega.

move=> s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
case: Hh2 => [Ha [Hb [hSgn [Ha3 [Hslen HSum]]]]].
repeat (split => //).
rewrite -Hslen mul0Z /= in HSum *.
rewrite (proj2 (Zsgn_neg (- Z_of_nat nk))); last omega.
rewrite (proj2 (Zsgn_neg (- \S_{ nk } B))); omega.
Compose_sepcon h1 h2; last by [].
rewrite (_ : Z2s 32 (- Z_of_nat nk) = cplt2 (Z2s 32 (Z_of_nat nk))) //.
apply s2Z_inj.
rewrite s2Z_cplt2; last first.
  rewrite weirdE2 Z2sK; omega.
rewrite Z2sK; last omega.
rewrite Z2sK //; omega.
rewrite (proj2 (Zsgn_pos (Z_of_nat nk))) in HSum; last omega.
rewrite (proj2 (Zsgn_neg (- Z_of_nat nk))); last omega.
rewrite -HSum; ring.

(** multi_lt k X b a0 a1 ret a2 a3 a4 *)

apply while.hoare_seq with (fun s h =>
  [a ]_ s = va /\ [b ]_ s = vb /\ u2Z ([k ]_ s) = Z_of_nat nk /\
  [X ]_ s = ptr /\ sgZ (s2Z slen) = 1 /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h /\
  ((\S_{ nk } A < \S_{ nk } B /\ [ret]_s = one32 /\ [a2]_s = zero32) \/
   (\S_{ nk } A > \S_{ nk } B /\ [ret]_s = zero32 /\ [a2]_s = one32) \/
   (\S_{ nk } A = \S_{ nk } B /\ [ret]_s = zero32 /\ [a2]_s = zero32))).

eapply (before_frame
  (fun s h => [a ]_ s = va /\ sgZ (s2Z slen) = 1 /\ (var_e a |--> slen :: ptr :: nil) s h)
  (fun s h => u2Z ([k ]_ s) = Z_of_nat nk /\ [X ]_ s = ptr /\ [b ]_ s = vb /\
    (var_e X |--> A ** var_e b |--> B) s h )
  (fun s h =>u2Z ([k ]_ s) = Z_of_nat nk /\ [X ]_ s = ptr  /\ [b ]_ s = vb /\
    (((\S_{ nk } A < \S_{ nk } B /\ [ret]_s = one32 /\ [a2]_s = zero32) \/
      (\S_{ nk } A > \S_{ nk } B /\ [ret]_s = zero32 /\ [a2]_s = one32) \/
      (\S_{ nk } A = \S_{ nk } B /\ [ret]_s = zero32 /\ [a2]_s = zero32)) /\
    (var_e X |--> A ** var_e b |--> B) s h))).

apply frame_rule_R.
apply multi_lt_triple.multi_lt_triple => //; by Uniq_uniq r0.
by Inde_frame.
move=> ?; by Inde_mult.

rewrite /while.entails => s h [[[Ha [Hb [Hk [HX [Ha0 [HZsgn [Ha1 Hmem]]]]]]] Ha1''] Ha1'].
move/leZP in Ha1''. rewrite /= in Ha1'. move/eqP in Ha1'.
rewrite store.get_r0 Z2uK // in Ha1'.
case: Ha1 => Ha1.
  by rewrite s2Z_u2Z_pos // in Ha1.
case: Ha1 => Ha1; last first.
  rewrite Ha1 in Ha1''. by move/leZP : Ha1''.
rewrite conAE in Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h2 h1.
repeat (split=> //).
move: Hh2; apply monotony => // h'; exact: mapstos_ext.
repeat (split=> //).
by rewrite -HZsgn Ha1.

rewrite /while.entails => s h Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh1 => Hk [Hb [HX [HSum Hmem]]].
case: Hh2 => Ha [Hsgn Hh2].
repeat (split=> //).
rewrite conAE.
Compose_sepcon h2 h1; first by [].
move: Hmem. apply monotony => // h'; exact: mapstos_ext.

(** ifte_beq ret, r0 *)

apply while.hoare_ifte.

apply while.hoare_ifte.

apply hoare_addiu with (fun s h => [a ]_ s = va /\ [b ]_ s = vb /\
  u2Z [k ]_ s = Z_of_nat nk /\ [X ]_ s = ptr /\ [a3]_s = zero32 /\
  sgZ (s2Z slen) = 1 /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h /\
  \S_{ nk } A = \S_{ nk } B).

move=> s h [ [ [Ha [Hb [Hk [HX [Hslen [mem HSum]]]]]] Hret] Ha2].
rewrite /wp_addiu.
repeat Reg_upd.
repeat (split => //).
by rewrite sext_Z2u // addi0.
by Assert_upd.
rewrite /= in Hret Ha2.
move/eqP/u2Z_inj in Hret.
move/eqP/u2Z_inj in Ha2.
rewrite store.get_r0 in Hret Ha2.
case: HSum => Hsum.
  rewrite Hret Ha2 in Hsum.
  case: Hsum => _ [Hsum _].
  by apply Z2u_dis in Hsum.
case: Hsum => Hsum; last by tauto.
rewrite Ha2 in Hsum.
case: Hsum => _ [_ Hsum].
by apply Z2u_dis in Hsum.

(** sw r0 zero16 a *)

apply hoare_sw_back'.
move=> s h [Ha [Hb [Hk [HX [Ha3 [Hslen [mem HSum]]]]]]].
exists (int_e slen).
rewrite !conAE /= in mem.
move: mem; apply monotony => // h'.
apply mapsto_ext => //=; by rewrite sext_Z2u // addi0.
apply currying => h'' Hh''.
exists A (* NB: whatever *), (Z2s 32 0).
repeat (split => //).

by rewrite Z2sK.

by rewrite Z2sK //= Hslen mul1Z HSum subZZ.

rewrite conCE in Hh''.
rewrite !conAE /=.
move: Hh''; apply monotony => // h3.
apply mapsto_ext => /=.
by rewrite sext_Z2u // addi0.
rewrite store.get_r0.
apply u2Z_inj.
by rewrite u2Z_Z2s_pos // Z2uK.
by rewrite Ha3 Z2uK.
by rewrite Z2sK //= Hslen Zmult_1_l HSum subZZ.

(** multi_sub k X b X a0 a1 a2 a3 a4 ret *)

apply hoare_prop_m.hoare_stren with (fun s h => \S_{ nk } A > \S_{ nk } B /\
  [a ]_ s = va /\ [b ]_ s = vb /\ u2Z ([k ]_ s) = Z_of_nat nk /\
  [X ]_ s = ptr /\ sgZ (s2Z slen) = 1 /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h).

rewrite /while.entails => s h [[[Ha [Hb [Hk [HX [HZsgn [Hmem HSum]]]]]] Hret] Ha2].
rewrite /= store.get_r0 Z2uK // in Hret.
move/eqP in Hret.
case: HSum => HSum.
  case: HSum => _ [HSum _].
  by rewrite HSum Z2uK in Hret.
split; last by [].
rewrite /= in Ha2.
move/eqP in Ha2.
rewrite store.get_r0 Z2uK // in Ha2.
case: HSum => HSum; first by tauto.
case: HSum => _ [_ HSum].
by rewrite HSum Z2uK in Ha2.

(** multi_sub k X b X a0 a1 a2 a3 a4 ret *)

apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => HAB.

apply (before_frame
  (fun s h => [a ]_ s = va /\ sgZ (s2Z slen) = 1 /\
    (var_e a |--> slen :: ptr :: nil) s h )
  (fun s h => [X ]_ s = ptr /\ [b ]_ s = vb /\ u2Z ([k ]_ s) = Z_of_nat nk/\
    (var_e X |--> A ** var_e b |--> B) s h)
  (fun s h => exists A', size A' = nk /\
    [X ]_ s = ptr /\ [b ]_ s = vb /\ u2Z ([k ]_ s) = Z_of_nat nk/\
    [a3]_s = zero32 /\
    (var_e X |--> A' ** var_e b |--> B) s h /\
    \S_{ nk } A' = \S_{ nk } A - \S_{ nk } B)).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.
apply multi_sub_u_u_L_triple_B_le_A => //.
by Uniq_uniq r0.
omega.

rewrite /while.entails => s h [Ha [Hb [Hk [HX [HZsgn Hmem]]]]].
rewrite conAE in Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h2 h1; last by [].
repeat (split => //).
move: Hh2. apply monotony => // h'; exact:  mapstos_ext.

rewrite /while.entails => s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
case: Hh1 => A' [A'_nk [Hb [HX [Hk [Ha3 [Hh1 HSum]]]]]].
case: Hh2 => [Ha [HZsgn Hh2]].
exists A', slen.
rewrite Ha3 Z2uK // HZsgn !mul1Z mul0Z addZ0.
repeat (split => //).

rewrite slen_not_weird HZsgn; ring.

rewrite (proj2 (Zsgn_pos (\S_{ nk } A - \S_{ nk } B))) //; omega.
rewrite conAE.
Compose_sepcon h2 h1; first by [].
move: Hh1. apply monotony => // h'; exact: mapstos_ext.

(** multi_sub k b X X a0 a1 a2 a3 a4 ret; *)

apply hoare_prop_m.hoare_stren with (fun s h => \S_{ nk } A < \S_{ nk } B /\
  [a ]_ s = va /\ [b ]_ s = vb /\ u2Z ([k ]_ s) = Z_of_nat nk /\
  [X ]_ s = ptr /\ sgZ (s2Z slen) = 1 /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h).

rewrite /while.entails => s h [[Ha [Hb [Hk [HX [HZsgn [Hmem HSum]]]]]] Hret].
rewrite /= store.get_r0 Z2uK // in Hret.
move/eqP in Hret.
case: HSum => HSum; last first.
  have {HSum}HSum : [ret ]_ s = zero32 by tauto.
  by rewrite HSum Z2uK in Hret.
split; by [tauto | ].

apply (hoare_prop_m.pull_out_conjunction' hoare0_false) => HAB.

apply while.hoare_seq with (fun s h => exists A', size A' = nk /\
  [a ]_ s = va /\ [b ]_ s = vb /\ u2Z ([k ]_ s) = Z_of_nat nk /\
  [X ]_ s = ptr /\ sgZ (s2Z slen) = 1 /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A') ** var_e b |--> B) s h /\
  \S_{ nk } A < \S_{ nk } B /\ [a3]_s = zero32 /\
  \S_{ nk } A' = \S_{ nk } B - \S_{ nk } A).

apply (before_frame
  (fun s h => [a ]_ s = va /\ sgZ (s2Z slen) = 1 /\
    (var_e a |--> slen :: ptr :: nil) s h )
  (fun s h => ([b ]_ s) = vb /\ ([X ]_ s) = ptr  /\ u2Z ([k ]_ s) = Z_of_nat nk/\
    (var_e b |--> B ** var_e X |--> A) s h)
  (fun s h => exists A', size A' = nk /\
    [b ]_ s = vb /\ [X ]_ s = ptr /\ u2Z ([k ]_ s) = Z_of_nat nk/\
    [a3]_s = zero32 /\
    (var_e b |--> B ** var_e X |--> A') s h /\
    \S_{ nk } A' = \S_{ nk } B - \S_{ nk } A)).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.
apply multi_sub_u_u_R_triple_B_le_A => //.
by Uniq_uniq r0.
exact/ltZW.

move=> s h [Ha [Hb [Hk [HX [HZsgn Hmem]]]]].
rewrite conAE in Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h2 h1; last by [].
repeat (split => //).
rewrite conCE.
move: Hh2; apply monotony => h' //; exact: mapstos_ext.

move=> s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
case: Hh1 => A' [A'_nk [Hb [HX [Hk [Ha3 [Hh1 HSum]]]]]].
case: Hh2 => Ha [HZsgn Hh2].
exists A'; repeat (split => //).
rewrite conAE.
Compose_sepcon h2 h1; first by [].
rewrite conCE.
move: Hh1; apply monotony => h' //; exact: mapstos_ext.

apply (hoare_prop_m.extract_exists extract_exists0) => A'.

(** multi_negate_prg.negate a a0 *)

apply (before_frame
  (fun s h => size A' = nk /\ [a ]_ s = va /\ [b ]_ s = vb /\
    u2Z ([k ]_ s) = Z_of_nat nk /\ [X ]_ s = ptr /\ sgZ (s2Z slen) = 1 /\
    (var_e b |--> B) s h /\ \S_{ nk } B > \S_{ nk } A /\
    ([a3 ]_ s) = zero32 /\ \S_{ nk } A' = \S_{ nk } B - \S_{ nk } A)
  (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A')
  (var_e a |--> cplt2 slen :: ptr :: nil ** int_e ptr |--> A')).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.
apply multi_negate_triple; by Uniq_uniq r0.

move=> s h [A'_nk [Ha [Hb [Hk [HX [Hsgn [Hmem [B_A [Ha3 HSum]]]]]]]]].
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h1 h2; first by [].
repeat (split => //).
exact: Zlt_gt.

move=> s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
case : Hh2 => A'_nk [Ha [Hb [Hk [HX [HZsgn [Hh2 [B_A [Ha3 HSum']]]]]]]].
exists (cplt2 slen).
rewrite s2Z_cplt2; last first.
  rewrite weirdE2 slen_not_weird HZsgn; omega.
rewrite Zsgn_Zopp Ha3 Z2uK // mul0Z addZ0.
repeat (split => //).
rewrite slen_not_weird HZsgn Zmult_1_l (proj2 (Zsgn_pos (Z_of_nat nk))) //; omega.
rewrite HZsgn Zmult_1_l (proj2 (Zsgn_neg (\S_{ nk } A - \S_{ nk } B))) //; omega.
by Compose_sepcon h1 h2.
rewrite HZsgn Zmult_1_l HSum'; ring.

(** addiu a3 r0 one16; *)

apply hoare_addiu with (fun s h => [a ]_ s = va /\ [b ]_ s = vb /\
  u2Z [k ]_ s = Z_of_nat nk /\ [X ]_ s = ptr /\ [a0 ]_ s = slen /\
  sgZ (s2Z slen) = - 1 /\ [a3]_s = one32 /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h).

move=> s h /= [[Ha [Hb [Hk [HX [Ha0 [Ha1' [Ha1'' Hmem]]]]]]] Ha1].
move/leZP in Ha1.
rewrite /wp_addiu.
repeat Reg_upd; repeat (split => //).
case: Ha1'' => Ha1''.
omega.
case: Ha1'' => Ha1''.
omega.
by rewrite -Ha1' Ha1''.
by rewrite add0i sext_Z2u.
Assert_upd.
move=> s' h' x v /= [] // ?; subst a3; by Reg_upd.

(** multi_add k a3 b X X a0 a1 a2 *)

apply while.hoare_seq with (fun s h => exists A' slen',
  size A' = nk /\ [a]_s = va /\ [b]_s = vb /\ s2Z slen' = sgZ (s2Z slen') * Z_of_nat nk /\
  sgZ (s2Z slen') = sgZ (sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B) /\
  ((var_e a |--> slen' :: ptr :: nil ** int_e ptr |--> A') ** var_e b |--> B) s h /\
  u2Z (store.lo s) <= 1 /\
  sgZ (s2Z slen') * (\S_{ nk } A' + u2Z (store.lo s) * \B^nk) =
  sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B).

apply (before_frame
  (fun s h => [a ]_ s = va /\ sgZ (s2Z slen) = -1 /\
    (var_e a |--> slen :: ptr :: List.nil) s h)
  (fun s h => [a3]_s = one32 /\ [b ]_ s = vb /\ [X ]_ s = ptr /\
    u2Z ([k ]_ s) = Z_of_nat nk /\ (var_e b |--> B ** var_e X |--> A) s h)
  (fun s h => exists A', size A' = nk /\ [b ]_ s = vb /\ [X ]_ s = ptr /\
    (var_e b |--> B ** var_e X |--> A') s h/\ u2Z (store.lo s) <= 1 /\
    \S_{ nk } A' + u2Z (store.lo s) * \B^nk = \S_{ nk } B + \S_{ nk } A)).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.
apply multi_add_u_u_triple => //; by Uniq_uniq r0.

move=> s h /= [Ha [Hb [Hk [HX [Ha0 [Ha1' [Ha3 Hmem]]]]]]].
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh1 => h11 [h12 [h11_d_h12 [h11_U_h12 [Hh11 Hh12]]]].
Compose_sepcon (h12 \U h2) h11.
repeat (split=> //).
Compose_sepcon h2 h12; first by [].
exact: assert_m.mapstos_ext Hh12.
by [].

move=> s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
case: Hh1 => A' [A'_nk [r_b [HX [Hh1 [Hm HSum]]]]].
case: Hh2 => Ha [HZsgn Hh2].
exists A', slen; repeat (split => //).
rewrite HZsgn mulN1Z (proj2 (Zsgn_neg (- \S_{ nk } A - \S_{ nk } B))) //.
move: (min_lSum nk A) => ?; omega.
rewrite conAE .
Compose_sepcon h2 h1; first by [].
rewrite conCE.
move: Hh1; apply assert_m.monotony => // h'; exact: assert_m.mapstos_ext.
rewrite HZsgn HSum; ring.

(** mflo a3 *)

apply hoare_mflo'.
move=> s h /= [A' [slen' [A'_nk [r_a [r_b [slen'_nk [HZsgn [Hmem [Hlo HSum]]]]]]]]].
rewrite /wp_mflo.
exists A', slen'.
repeat Reg_upd.
repeat (split => //).
Assert_upd.
move=> s' h' x v /= [] // ?; subst a3; by Reg_upd.
Qed.

Lemma multi_sub_s_u_triple : forall k a b a0 a1 a2 a3 a4 ret X,
uniq(k, a, b, a0, a1, a2, a3, a4, ret, X, r0) ->
forall nk va vb ptr, nk <> O -> Z_of_nat nk < 2 ^^ 31 ->
  u2Z ptr + 4 * Z_of_nat nk < \B^1 -> u2Z vb + 4 * Z_of_nat nk < \B^1 ->
forall A B, size A = nk -> size B = nk ->
forall slen, s2Z slen = sgZ (s2Z slen) * Z_of_nat nk ->
    sgZ (s2Z slen) = sgZ (sgZ (s2Z slen) * \S_{ nk } A) ->
{{ fun s h => [ a ]_s = va /\ [ b ]_s = vb /\ u2Z [ k ]_s = Z_of_nat nk /\
   ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h }}
multi_sub_s_u k a b a0 a1 a2 a3 a4 ret X
{{ fun s h => exists A', exists slen', size A' = nk /\ [a]_s = va /\ [b]_s = vb /\
  s2Z slen' = sgZ (s2Z slen') * Z_of_nat nk /\
  sgZ (s2Z slen') = sgZ (sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B) /\
  ((var_e a |--> slen' :: ptr :: nil ** int_e ptr |--> A') ** var_e b |--> B ) s h /\
  u2Z ([a3]_ s) <= 1 /\
  sgZ (s2Z slen') * (\S_{ nk } A' + u2Z ([a3]_s) * \B^nk) =
  sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B }}.
Proof.
(* NB: similar to multi_add_s_u_triple *)
move=> k a b a0 a1 a2 a3 a4 ret X Hregs nk va vb ptr Hnk Hnk' ptr_fit vb_fit A B
  len_A len_B slen slen_no_weird valid_A.
rewrite /multi_sub_s_u.

(** multi_is_zero k b a0 a1 a2 *)

apply while.hoare_seq with (fun s h => [a]_s = va /\ [b]_s = vb /\
  u2Z [k]_s = Z_of_nat nk /\
  ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h /\
  ((0 = \S_{ nk } B -> [a2]_s = one32) /\ (0 < \S_{ nk } B -> [a2]_s = zero32))).

apply (before_frame
  (fun s h => [a ]_ s = va /\ (var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) s h)
  (fun s h => u2Z [ k ]_s = Z_of_nat nk /\ [b]_s = vb /\ (var_e b |--> B) s h)
  (fun s h => u2Z [ k ]_s = Z_of_nat nk /\ [b]_s = vb /\ (var_e b |--> B) s h  /\
    ((0 = \S_{ nk } B -> [a2]_s = one32) /\ (0 < \S_{ nk } B -> [a2]_s = zero32)))).

apply frame_rule_R; last 2 first.
  by Inde_frame.
  move=> ?; by Inde_mult.
  apply multi_is_zero_u_triple => //; by Uniq_uniq r0.

move=> s h [Ha [Hb [Hk mem]]].
case: mem =>  h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
by Compose_sepcon h2 h1.

move => s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
repeat (split; first by tauto).
split; last by tauto.
Compose_sepcon h2 h1; tauto.

(** ifte (bne a2 r0) *)

apply while.hoare_ifte.

(** addiu a3 r0 zero16 *)

apply hoare_addiu'.
move=> s h [ [Ha [Hb [Hk [mem Hret]]]] Ha2].
rewrite /= in Ha2.
move/eqP in Ha2.
move: (min_lSum nk B).
case/Z_le_lt_eq_dec => Hsum.
apply (proj2 Hret) in Hsum.
by rewrite Hsum Z2uK // store.get_r0 Z2uK // in Ha2.
exists A, slen.
repeat Reg_upd; repeat (split => //).
rewrite -Hsum subZ0; exact valid_A.
by Assert_upd.
by rewrite sext_Z2u // addi0 Z2uK.
rewrite sext_Z2u // addi0 Z2uK // mul0Z addZ0 -Hsum; ring.

(** multi_sub_s_u0 k a b a0 a1 a2 a3 a4 ret X *)

apply hoare_prop_m.hoare_stren with (!(fun s => 0 < \S_{ nk } B) **
  (fun s h => [a ]_ s = va /\[b ]_ s = vb /\ u2Z [k ]_ s = Z_of_nat nk /\
    ((var_e a |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e b |--> B) s h)).

move=> s h [[Ha [Hb [Hk [mem Hret]]]] Ha2].
rewrite /= negbK in Ha2.
move/eqP/u2Z_inj in Ha2.
move: (min_lSum nk B).
case/Z_le_lt_eq_dec => Hsum; last first.
 apply (proj1 Hret) in Hsum.
 rewrite Hsum store.get_r0 in Ha2.
 by apply Z2u_dis in Ha2.
by Compose_sepcon heap.emp h.

apply pull_out_bang => nk_B.
exact: multi_sub_s_u0_triple.
Qed.

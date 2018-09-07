(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int uniq_tac multi_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_tactics mips_frame.
Import expr_m.
Import assert_m.
Require Import multi_sub_s_s_prg pick_sign_triple multi_add_s_u_triple.
Require Import multi_sub_s_u_triple.

Local Open Scope zarith_ext_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope machine_int_scope.
Local Open Scope multi_int_scope.

Lemma multi_sub_s_s_triple rk rx ry a0 a1 a2 a3 a4 ret X Y :
  uniq(rk, rx, ry, a0, a1, a2, a3, a4, ret, X, Y, r0) ->
  forall nk vx vy ptr ptrB, nk <> O -> Z_of_nat nk < 2 ^^ 31 ->
    u2Z ptr + 4 * Z_of_nat nk < \B^1 -> u2Z ptrB + 4 * Z_of_nat nk < \B^1 ->
  forall A B, size A = nk -> size B = nk -> forall slen slenB,
    s2Z slen = sgZ (s2Z slen) * Z_of_nat nk -> s2Z slenB = sgZ (s2Z slenB) * Z_of_nat nk ->
    sgZ (s2Z slen) = sgZ (sgZ (s2Z slen) * \S_{ nk } A) ->
    sgZ (s2Z slenB) = sgZ (sgZ (s2Z slenB) * \S_{ nk } B) ->
{{ fun s h => [rx]_s = vx /\ [ry]_s = vy /\ u2Z [rk]_s = Z_of_nat nk /\
    ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) **
      var_e ry |--> slenB :: ptrB :: nil ** int_e ptrB |--> B) s h }}
 multi_sub_s_s rk rx ry a0 a1 a2 a3 a4 ret X Y
 {{ fun s h => exists A' slen', size A' = nk /\
   s2Z slen' = sgZ (s2Z slen') * Z_of_nat nk /\
   sgZ (s2Z slen') = sgZ (sgZ (s2Z slen) * \S_{ nk } A - sgZ (s2Z slenB) * \S_{ nk } B) /\
   ((var_e rx |--> slen' :: ptr :: nil ** int_e ptr |--> A') **
    var_e ry |--> slenB :: ptrB :: nil ** int_e ptrB |--> B) s h /\
   u2Z ([a3]_ s) <= 1 /\
   sgZ (s2Z slen') * (\S_{ nk } A' + u2Z ([a3]_ s) * \B^nk) =
   sgZ (s2Z slen) * \S_{ nk } A - sgZ (s2Z slenB) * \S_{ nk } B }}.
Proof.
move=> Hregs nk vx vy ptr ptrB Hnk Hnk' Hptr HptrB A B len_A len_B
  slen slenB Hslen HslenB valid_A valid_B.
rewrite /multi_sub_s_s.

(** lw Y four16 ry *)

apply hoare_lw_back_alt'' with (fun s h => [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\ [Y ]_s = ptrB /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) **
    var_e ry |--> slenB :: ptrB :: nil ** int_e ptrB |--> B) s h).

move=> s h [r_x [r_y [r_k mem]]].
exists ptrB; split.
- rewrite conAE conCE in mem.
  rewrite -mapsto2_mapstos in mem.
  rewrite conCE conAE in mem.
  rewrite conCE 2!conAE in mem.
  rewrite conCE 2!conAE in mem.
  rewrite conCE 2!conAE in mem.
  move: mem. apply monotony => h' //; apply mapsto_ext => //; by rewrite sext_Z2u.
- rewrite /update_store_lw.
  repeat Reg_upd; repeat (split => //).
  by Assert_upd.

(** pick_sign ry a0 a1 *)

apply while.hoare_seq with (fun s h => [rx ]_ s = vx /\ [ry ]_ s = vy /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  [Y ]_s = ptrB /\ [a0]_s = slenB /\ sgZ (s2Z [a1]_s) = sgZ (s2Z slenB) /\
  (s2Z [a1]_s = 0 \/ s2Z [a1]_s = 1 \/ s2Z [a1]_s = -1) /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) **
   var_e ry |--> slenB :: ptrB :: nil ** int_e ptrB |--> B) s h).

eapply while.hoare_conseq; last first.

apply (pick_sign_triple
  (fun s h => [rx ]_ s = vx /\ u2Z [rk ]_ s = Z_of_nat nk /\ [Y ]_s = ptrB)
  (((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) **
    var_e ry \+ int_e four32 |--> ptrB :: nil ** int_e ptrB |--> B)) vy slenB).
by Uniq_uniq r0.
by Inde.
by Inde.

move=> s h /= [Hrx [Hry [Rk [HY mem]]]].
rewrite !conAE in mem *.
repeat (split=> //).
by assoc_comm mem.

move=> s h /= [Hry [Ha0 [Ha1 [Ha1' [mem [Hrx [Hrk HY]]]]]]].
rewrite !conAE in mem *.
repeat (split=> //).
by assoc_comm mem.

(** while.ifte (bgez a1) *)

apply while.hoare_ifte.

(** ifte_beq a1, r0 *)

apply while.hoare_ifte.

(** addiu a3 r0 zero16 *)

apply hoare_addiu'.

move=> s h [[[r_x [r_y [r_k [r_Y [r_A0 [r_a1 [a0_a1 mem]]]]]]] _] Ha1].
rewrite /= in Ha1.
move/eqP/u2Z_inj in Ha1.
rewrite store.get_r0 in Ha1.
rewrite Ha1 s2Z_u2Z_pos' in r_a1; last by rewrite Z2uK.
rewrite Z2uK //= in r_a1.
rewrite /wp_addiu.
exists A, slen.
repeat Reg_upd.
rewrite -r_a1 mul0Z subZ0.
repeat (split => //).
by Assert_upd.
by rewrite add0i sext_Z2u // Z2uK.
by rewrite add0i sext_Z2u // Z2uK // mul0Z addZ0.

(** multi_sub_s_u rk rx Y a0 a1 a2 a3 a4 ret X *)

apply (before_frame
  (fun s h => [ry ]_ s = vy /\ sgZ (s2Z slenB) = 1 /\
  (var_e ry |--> slenB :: ptrB :: nil) s h )
  (fun s h => [rx ]_ s = vx /\ [Y ]_ s = ptrB /\ u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e Y |--> B) s h)
  (fun s h => exists A' slen', size A' = nk /\
    [rx ]_ s = vx /\ [Y ]_ s = ptrB /\ s2Z slen' = sgZ (s2Z slen') * Z_of_nat nk /\
   sgZ (s2Z slen') = sgZ (sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B) /\
   ((var_e rx |--> slen' :: ptr :: nil ** int_e ptr |--> A') ** var_e Y |--> B ) s h /\
   u2Z ([a3]_ s) <= 1 /\
   sgZ (s2Z slen') * (\S_{ nk } A' + u2Z ([a3]_s) * \B^nk) =
   sgZ (s2Z slen) * \S_{ nk } A - \S_{ nk } B)).

apply frame_rule_R.
  apply multi_sub_s_u_triple => //.
  by Uniq_uniq r0.
  by Inde_frame.
  move=> ?; by Inde_mult.

move=> s h [[[r_x [r_y [r_k [r_Y [r_A0 [r_a1 [a0_a1 mem]]]]]]] Ha1'] Ha1].
rewrite /= in Ha1'.
move/leZP in Ha1'.
rewrite /= in Ha1.
move/eqP in Ha1.
rewrite store.get_r0 Z2uK // in Ha1.
rewrite -conAE conCE -conAE conCE in mem.
case: mem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h2 h1.
repeat (split=> //).
rewrite conCE.
move: Hh2; apply monotony => // h'; by apply mapstos_ext.
repeat (split => //).
case: a0_a1 => a0_a1.
rewrite (_ : 0 = s2Z (Z2s 32 0)) in a0_a1; last by rewrite Z2sK.
apply s2Z_inj in a0_a1.
by rewrite a0_a1 u2Z_Z2s_pos in Ha1.
case: a0_a1 => a0_a1.
by rewrite -r_a1 a0_a1.
rewrite a0_a1 in Ha1'; omega.

move=> s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
case: Hh1 => [A' [slen' [len_A' [r_x [r_Y [slen'_nk [HZsgn [mem [Ha3 HSum]]]]]]]]].
case: Hh2 => [r_y [Zsgn_slenB Hh2]].
exists A', slen'.
repeat (split => //).
rewrite HZsgn Zsgn_slenB. f_equal. f_equal. ring.
rewrite -conAE conCE -2!conAE.
Compose_sepcon h1 h2; last by done.
rewrite conAE conCE.
move: mem; apply monotony => // h'.
by apply mapstos_ext.
rewrite HSum Zsgn_slenB. f_equal. ring.

(** multi_add_s_u rk rx Y a0 a1 a2 a3 a4 ret X *)

apply (before_frame
  (fun s h => [ry ]_ s = vy /\ sgZ (s2Z slenB) = -1 /\
  (var_e ry |--> slenB :: ptrB :: nil) s h )
  (fun s h => [rx ]_ s = vx /\ [Y ]_ s = ptrB /\ u2Z [rk ]_ s = Z_of_nat nk /\
  ((var_e rx |--> slen :: ptr :: nil ** int_e ptr |--> A) ** var_e Y |--> B) s h)
  (fun s h => exists A' slen', size A' = nk /\ [rx ]_ s = vx /\ [Y ]_ s = ptrB /\
    s2Z slen' = sgZ (s2Z slen') * Z_of_nat nk /\
    sgZ (s2Z slen') = sgZ (sgZ (s2Z slen) * \S_{ nk } A + \S_{ nk } B) /\
    ((var_e rx |--> slen' :: ptr :: nil ** int_e ptr |--> A') ** var_e Y |--> B ) s h /\
    u2Z ([a3]_ s) <= 1 /\
    sgZ (s2Z slen') * (\S_{ nk } A' + u2Z ([a3]_s) * \B^nk) =
    sgZ (s2Z slen) * \S_{ nk } A + \S_{ nk } B)).

apply frame_rule_R.
  apply multi_add_s_u_triple_gen => //.
  by Uniq_uniq r0.
  by Inde_frame.
  move=> ?; by Inde_mult.

move=> s h [[r_x [r_y [r_k [r_Y [r_A0 [r_a1 [a0_a1 mem]]]]]]] Ha1].
rewrite /= in Ha1.
move/leZP in Ha1.
case: a0_a1 => a0_a1.
rewrite a0_a1 in Ha1.
by move: (Ha1 (leZZ _)).
case: a0_a1 => a0_a1.
rewrite a0_a1 in Ha1.
exfalso; omega.
rewrite -conAE conCE -conAE in mem.
case: mem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
Compose_sepcon h1 h2.
repeat (split=> //).
rewrite conCE in Hh1.
move: Hh1; apply monotony => // h'; exact: mapstos_ext.
repeat (split => //).
by rewrite -r_a1 a0_a1.

move=> s h [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
case: Hh1 => [A' [slen' [len_A' [r_x [r_Y [slen'_nk [HZsgn [mem [Ha3 HSum]]]]]]]]].
case: Hh2 => [r_y [Zsgn_slenB Hh2]].
exists A', slen'; repeat (split => //).
rewrite Zsgn_slenB HZsgn; f_equal. ring.

rewrite -conAE conCE -conAE.
Compose_sepcon h1 h2; last by [].
rewrite conCE.
move: mem; apply monotony => // h'.
exact: mapstos_ext.
rewrite Zsgn_slenB HSum; ring.
Qed.

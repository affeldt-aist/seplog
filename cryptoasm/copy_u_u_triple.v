(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext uniq_tac machine_int.
Require Import multi_int.
Import MachineInt.
Require Import mips_seplog mips_tactics mips_contrib mapstos.
Require Import copy_u_u_prg.
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

Lemma copy_u_u_triple rk rx ry tmp ytmp i : uniq(rk, ry, rx, tmp, ytmp, i, r0) ->
  forall X Y nk, size X = nk -> size Y = nk ->
    forall ny, u2Z ny + 4 * Z_of_nat nk < Zbeta 1 ->
  {{ fun s h =>
    [ry]_s = ny /\
    u2Z [rk]_s = Z_of_nat nk /\
    (var_e rx |--> X ** var_e ry |--> Y) s h }}
  copy_u_u rk ry rx tmp ytmp i
  {{ fun s h =>
    [ry]_s = ny /\
    u2Z [rk]_s = Z_of_nat nk /\
    (var_e rx |--> X ** var_e ry |--> X) s h }}.
Proof.
move=> Hset X Y nk len_X len_Y ny Hfit; rewrite /copy_u_u.

(** addiu ytmp ry zero16 ; *)

apply mips_contrib.hoare_addiu with (fun s h =>
  [ry]_s = ny /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  [ytmp]_s = [ry]_s /\
  (var_e rx |--> X ** var_e ry |--> Y) s h).

move=> s h [r_y [r_k mem]].
rewrite /mips_seplog.wp_addiu.
repeat Reg_upd; repeat (split; trivial).
by rewrite sext_Z2u // addi0.
by Assert_upd.

(** addiu i r0 zero16 ; *)

apply mips_contrib.hoare_addiu with (fun s h =>
  [ry]_s = ny /\
  u2Z ([rk ]_ s) = Z_of_nat nk /\
  [ytmp]_s = [ry]_s /\
  [i]_s = zero32 /\
  (var_e rx |--> X ** var_e ry |--> Y) s h).

move=> s h [r_y [r_k [r_ytmp mem]]].
rewrite /mips_seplog.wp_addiu.
repeat Reg_upd; repeat (split => //).
by rewrite sext_Z2u // addi0.
by Assert_upd.

(** While bne i rk {{ *)

apply mips_seplog.hoare_prop_m.hoare_while_invariant with (fun s h =>
  [ry]_s = ny /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  u2Z [ytmp]_s = u2Z [ry]_s + u2Z [i]_s * 4 /\
  u2Z [i]_s <= Z_of_nat nk /\
  (var_e rx |--> X ** var_e ry |-->
    take '|u2Z [i]_s| X ++ drop '|u2Z [i]_s| Y) s h).

move=> s h [r_y [r_k [r_ytmp [r_i mem]]]].
repeat (split; trivial).
by rewrite r_i Z2uK // mul0Z addZ0 r_ytmp.
rewrite r_i Z2uK //; exact/Zle_0_nat.
by rewrite r_i Z2uK // take0 drop0.

move=> s h [[r_y [r_k [r_ytmp [r_i mem]]]] i_k].
repeat (split; trivial).
move/negPn : i_k. move/eqP/u2Z_inj => /= i_k.
rewrite i_k r_k Zabs2Nat.id in mem.
rewrite take_oversize in mem; last by rewrite len_X.
rewrite drop_oversize // ?cats0 // in mem; by rewrite len_Y.

(** lwxs tmp i rx ; *)

apply mips_contrib.hoare_lwxs_back_alt'' with (fun s h =>
  [ry]_s = ny /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  u2Z [ytmp]_s = u2Z [ry]_s + u2Z [i]_s * 4 /\
  u2Z [i]_s < Z_of_nat nk /\
  [tmp]_s = X `32_ '|u2Z [i ]_ s| /\
  (var_e rx |--> X **
    var_e ry |--> take '|u2Z [i ]_ s| X ++ drop '|u2Z [i ]_ s| Y) s h).

move=> s h [[r_y [r_k [r_ytmp [i_k' mem]]]] i_k].
move/eqP : i_k => /= i_k.
exists (X `32_ '|u2Z [i ]_ s|); split.
Decompose_32 X '|u2Z ([i ]_ s)| X1 X2 HlenX1 HX'; last first.
  apply/ltP/Nat2Z.inj_lt.
  rewrite Z_of_nat_Zabs_nat //.
  - by rewrite len_X ltZ_neqAle -{1}r_k.
  - exact/min_u2Z.
rewrite {1}HX' in mem.
rewrite (mapstos.decompose_equiv _ _ _ _ _ HlenX1) in mem.
rewrite !assert_m.conAE assert_m.conCE !assert_m.conAE in mem.
move: mem; apply assert_m.monotony => h' //.
apply assert_m.mapsto_ext => //.
rewrite /=.
f_equal.
apply u2Z_inj.
have Htmp : u2Z ([i ]_ s) < 2 ^^ 30.
  apply (@leZ_ltZ_trans (Z_of_nat nk)) => //.
  apply (@ltZ_pmul2l 4) => //.
  rewrite (_ : 4 = 2 ^^ 2) // -ZpowerD //.
  rewrite -Zbeta1E [_ ^^ _]/=.
  move: (min_u2Z ([ry]_s)); rewrite r_y => ?; lia.
rewrite Z2uK; last first.
  split; first exact: Zle_0_nat.
  rewrite inj_mult. simpl Z_of_nat.
  rewrite {2}(_ : 32 = 2 + 30)%nat // ZpowerD.
  simpl (2 ^^ 2).
  apply/ltZ_pmul2l => //.
  rewrite Z_of_nat_Zabs_nat //; exact: min_u2Z.
rewrite (@u2Z_shl _ 32 _ 30) //; last first.
  rewrite inj_mult. simpl Z_of_nat.
  rewrite Z_of_nat_Zabs_nat; last exact: min_u2Z.
  simpl expZ; ring.

rewrite /mips_contrib.update_store_lwxs.
repeat Reg_upd; repeat (split => //).
- lia.
- by Assert_upd.

(** sw tmp zero16 ytmp ; *)

apply mips_contrib.hoare_sw_back'' with (fun s h =>
  [ry]_s = ny /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  u2Z [ytmp]_s = u2Z [ry]_s + u2Z [i]_s * 4 /\
  u2Z [i]_s < Z_of_nat nk /\
  (var_e rx |--> X **
    var_e ry |--> take '|u2Z [i ]_ s + 1| X ++
      drop '|u2Z [i ]_ s + 1| Y) s h).

move=> s h [r_y [r_k [r_ytmp [r_i [r_tmp mem]]]]].
set ni := '|u2Z ([i]_s)| in mem.
exists (int_e ((drop ni Y) `32_ 0)).

Decompose_32 (take ni X ++ drop ni Y) '|u2Z ([i ]_ s)| XY1 XY2 HlenXY1 HXY'; last first.
  rewrite size_cat size_takel //; last first.
    apply/leP/Nat2Z.inj_le.
    rewrite Z_of_nat_Zabs_nat; [lia | exact/min_u2Z].
  rewrite size_drop len_Y addnBA; last first.
    apply/leP/Nat2Z.inj_le.
    rewrite Z_of_nat_Zabs_nat; [lia | exact/min_u2Z].
  rewrite addnC addnK.
  apply/ltP/Nat2Z.inj_lt.
  rewrite Z_of_nat_Zabs_nat //; exact/min_u2Z.

have Htmp : [var_e ry \+ int_e (Z2u 32 (Z_of_nat (4 * ni))) ]e_ s =
   [var_e ytmp \+ int_e (Z2u (16 + 16) 0) ]e_ s.
  rewrite /=.
  apply u2Z_inj.
  rewrite addi0 r_ytmp u2Z_add_Z2u //; last 2 first.
    exact: Zle_0_nat.
    rewrite inj_mult [Z_of_nat _]/= Z_of_nat_Zabs_nat //; last exact/min_u2Z.
    rewrite r_y -Zbeta1E; lia.
  rewrite inj_mult [Z_of_nat _]/= Z_of_nat_Zabs_nat //; [ring | exact/min_u2Z].

rewrite HXY' /= in mem.
rewrite (mapstos.decompose_equiv _ _ _ _ _ HlenXY1) in mem.
do 2 rewrite assert_m.conCE !assert_m.conAE in mem.
move: mem.
apply assert_m.monotony => // h'.
apply assert_m.mapsto_ext => //.
by rewrite sext_Z2u //.

rewrite nth_cat size_takel; last first.
  apply/leP/Nat2Z.inj_le.
  rewrite /ni Z_of_nat_Zabs_nat; by [lia | apply min_u2Z].
by rewrite ltnn subnn.

apply assert_m.currying => h'' Hh''.
repeat (split => //).
rewrite !assert_m.conAE assert_m.conCE !assert_m.conAE in Hh''.
move: Hh''; apply assert_m.monotony => h''' //.
have -> : '|u2Z ([i ]_ s) + 1| =  S ni.
  rewrite Zabs_nat_Zplus //.
  by rewrite plus_comm.
  exact/min_u2Z.
rewrite (take_nth zero32); last first.
  rewrite len_X.
  apply/ltP/Nat2Z.inj_lt.
  rewrite /ni Z_of_nat_Zabs_nat //; exact/min_u2Z.
rewrite -cats1.
rewrite -catA (mapstos.decompose_equiv _ ni); last first.
  rewrite size_takel //.
  apply/leP/Nat2Z.inj_le.
  rewrite /ni Z_of_nat_Zabs_nat; [lia | exact: min_u2Z].
move/eqP : HXY'.
rewrite eqseq_cat; last first.
  rewrite size_takel // len_X.
  apply/leP/Nat2Z.inj_le.
  rewrite /ni Z_of_nat_Zabs_nat; [lia | exact: min_u2Z].
case/andP => /eqP H1 /eqP H2.
apply assert_m.monotony => h4 //.
  by rewrite -H1.
apply assert_m.monotony => h5r //.
  apply assert_m.mapsto_ext => //.
  by rewrite /= sext_Z2u // addi0.

suff : XY2 = drop (S ni) Y by move=> ->.
by rewrite dropS H2 /= drop0.

(** addiu i i one16 ; *)

apply mips_contrib.hoare_addiu with (fun s h =>
  [ry]_s = ny /\
  u2Z [rk ]_ s = Z_of_nat nk /\
  u2Z [ytmp]_s = u2Z [ry]_s + (u2Z [i]_s - 1) * 4 /\
  u2Z [i]_s <= Z_of_nat nk /\
  (var_e rx |--> X **
    var_e ry |--> take '|u2Z [i ]_ s| X ++ drop '|u2Z [i ]_ s| Y) s h).

move=> s h [r_y [r_k [r_ytmp [r_i mem]]]].
rewrite /mips_seplog.wp_addiu.
repeat Reg_upd; repeat (split; trivial).
rewrite r_ytmp.
f_equal.
rewrite sext_Z2u // u2Z_add_Z2u //.
ring.
rewrite -Zbeta1E.
  move: (min_u2Z ([ry]_s)); rewrite r_y => ?; lia.
rewrite sext_Z2u // u2Z_add_Z2u //.
lia.
rewrite -Zbeta1E.
  move: (min_u2Z ([ry]_s)); rewrite r_y => ?; lia.
rewrite sext_Z2u // u2Z_add_Z2u //; last first.
rewrite -Zbeta1E.
  move: (min_u2Z ([ry]_s)); rewrite r_y => ?; lia.
by Assert_upd.

(** addiu ytmp ytmp four16 *)

apply mips_contrib.hoare_addiu'.

move=> s h [r_y [r_k [r_ytmp [i_k mem]]]].
rewrite /mips_seplog.wp_addiu.
repeat Reg_upd; repeat (split; trivial).
rewrite sext_Z2u // u2Z_add_Z2u //; last first.
  rewrite r_ytmp r_y -Zbeta1E -{2}(mul1Z 4) -addZA -mulZDl mulZC; lia.
rewrite r_ytmp; ring.
by Assert_upd.
Qed.

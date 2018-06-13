(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext uniq_tac.
Require Import machine_int multi_int.
Import MachineInt.
Require Import mapstos.
Require Import mips_seplog mips_contrib mips_tactics multi_is_even_u_prg.
Require Import multi_is_zero_u_prg.
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

Lemma multi_is_zero_u_triple k x ret a0 k0 : uniq(k, x, k0, a0, ret, r0) ->
  forall nk X vx, size X = nk ->
    u2Z vx + 4 * Z_of_nat nk < \B^1 ->
  {{ fun s h => u2Z [ k ]_s = Z_of_nat nk /\ [x]_s = vx /\ (var_e x |--> X) s h }}
  multi_is_zero_u k x k0 a0 ret
  {{ fun s h => u2Z [ k ]_s = Z_of_nat nk /\ [x]_s = vx /\ (var_e x |--> X) s h  /\
    ((0 = \S_{ nk } X -> [ret]_s = one32) /\
     (0 < \S_{ nk } X -> [ret]_s = zero32))}}.
Proof.
move=> Hregs nk X vx X_nk vx_fit.
rewrite /multi_is_zero_u.

(** addiu k0 r0 zero16 ; *)

NextAddiu.
move=> s h [Hk [Hx mem]].
rewrite /wp_addiu.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.

(** addiu ret r0 one16 ; *)

NextAddiu.
move=> s h [[Hk [Hx mem]] Hk0].
rewrite /wp_addiu.
repeat Reg_upd.
repeat (split => //).
by Assert_upd.

(** while.while (bne k0 k) ( *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists i,
  u2Z [ k ]_s = Z_of_nat nk /\ [x]_s = vx /\
  u2Z [k0]_s = Z_of_nat i /\
  (i <= nk)%nat /\
  (var_e x |--> X) s h /\
  (0 = \S_{ i } X -> [ret]_s = one32) /\
  (0 < \S_{ i } X -> [ret]_s = zero32)).

move=> s h /= H.
case: H => H Hret.
case: H => H Hk0.
case: H => Hk [Hx mem].
exists O.
repeat (split => //).
by rewrite Hk0 sext_Z2u // addi0 store.get_r0 Z2uK.
move=> _.
apply u2Z_inj.
by rewrite Hret store.get_r0 add0i sext_Z2u.

move=> s h [[i [Hk [Hx [Hk0 [i_nk [mem Hret]]]]]] Hk0'].
rewrite /= negbK in Hk0'.
move/eqP/u2Z_inj in Hk0'.
rewrite Hk0' in Hk0.
rewrite Hk0 in Hk.
apply Z_of_nat_inj in Hk.
by subst i.

(** lwxs a0 k0 x ; *)

apply hoare_lwxs_back_alt'' with (fun s h => exists i,
  u2Z [k ]_ s = Z_of_nat nk /\
  [x ]_ s = vx /\
  u2Z [k0 ]_ s = Z_of_nat i /\
  (i < nk)%nat /\
  [a0]_s = X `32_ i /\
  (var_e x |--> X) s h /\
  (0 = \S_{ i } X -> [ret ]_ s = one32) /\
  (0 < \S_{ i } X -> [ret ]_ s = zero32)).

move=> s h [[i [Hk [Hx [Hk0 [i_nk [mem Hret]]]]]] Hk0'].
rewrite /= in Hk0'.
move/eqP in Hk0'.
rewrite Hk Hk0 in Hk0'.
apply Z_of_nat_inj_neq in Hk0'.
exists (X `32_ i); split.
- Decompose_32 X i X1 X2 HlenX1 HX'; last by ssromega.
  rewrite HX' (decompose_equiv _ _ _ _ _ HlenX1) in mem.
  rewrite conCE !conAE in mem.
  move: mem; apply monotony => // h'.
  apply mapsto_ext => //.
  by rewrite /= shl_Z2u inj_mult Hk0 [Zmult]lock /= -lock mulZC.
- rewrite /update_store_lwxs.
  exists i.
  repeat Reg_upd; repeat (split; trivial).
  ssromega.
  by Assert_upd.

(** movn ret r0 a0 ; *)

apply hoare_movn with (fun s h => exists i,
  u2Z [k ]_ s = Z_of_nat nk /\
  [x ]_ s = vx /\
  u2Z [k0 ]_ s = Z_of_nat i /\
  (i < nk)%nat /\
  [a0 ]_ s = X `32_ i /\
  (var_e x |--> X) s h /\
  (0 = \S_{i.+1} X -> [ret ]_ s = one32) /\
  (0 < \S_{i.+1} X -> [ret ]_ s = zero32)).

move=> s h [i [Hk [Hx [Hk0 [i_nk [Ha0 [mem Hret]]]]]]].
rewrite /wp_movn.
repeat Reg_upd.
split; move=> Ha0'.
exists i.
repeat (split => //).
by Assert_upd.
move=> H; symmetry in H.
apply lSum_0_inv_first in H; last by rewrite X_nk.
rewrite (take_nth zero32) in H; last by rewrite X_nk.
rewrite nseqS cats1 in H.
move/eqP : H; rewrite eqseq_rcons => /andP [_ /eqP H].
rewrite /nth' H in Ha0.
rewrite Ha0 /zero32 in Ha0'; tauto.

exists i.
repeat Reg_upd.
repeat (split => //).
move=> H.
apply (proj1 Hret).
symmetry in H.
apply lSum_0_inv_first in H; last by rewrite X_nk.
rewrite (take_nth zero32) in H; last by rewrite X_nk.
rewrite nseqS cats1 in H.
move/eqP : H; rewrite eqseq_rcons => /andP [/eqP H _].

rewrite -lSum_take; last by rewrite X_nk ltnW.
by rewrite H lSum_nseq_0.
move=> H.
apply (proj2 Hret).
rewrite /nth' /zero32 in Ha0.
by rewrite lSum_remove_last -Ha0 Ha0' Z2uK // mulZ0 addZ0 in H.

(** addiu k0 k0 one16 *)

apply hoare_addiu'.
move=> s h [i [Hk [Hx [Hk0 [i_nk [Ha0 [mem Hret]]]]]]].
rewrite /wp_addiu.
repeat Reg_upd.
exists i.+1; repeat (split => //).
- rewrite sext_Z2u // u2Z_add_Z2u //.
  + by rewrite Z_S Hk0.
  + rewrite Hk0 -Zbeta1E.
    move: (min_u2Z vx) => ?; ssromega.
- by Assert_upd.
Qed.

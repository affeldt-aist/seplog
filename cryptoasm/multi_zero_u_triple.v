(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_tactics mips_contrib mapstos multi_zero_u_prg.
Import expr_m.
Import assert_m.

Local Open Scope heap_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.

Section multi_zero_u.

Variables k z ext Z_ : reg.

Lemma multi_zero_u_triple : uniq(k, z, ext, Z_, r0) ->
  forall nk Z vz, size Z = nk -> u2Z vz + 4 * Z_of_nat nk < \B^1 ->
  {{ fun s h => [z]_s = vz /\ u2Z [k]_s = Z_of_nat nk /\ (var_e z |--> Z) s h }}
    multi_zero_u k z ext Z_
  {{ fun s h => [z]_s = vz /\ u2Z [k]_s = Z_of_nat nk /\
   (var_e z |--> nseq nk zero32) s h }}.
Proof.
move=> Hset nk Z vz HlenZ Hnz.
rewrite /multi_zero_u.

(** addiu Z_ z zero16 *)

NextAddiu.
move=> s h [r_z [r_k Hmem]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** addiu ext k zero16 *)

NextAddiu.
move=> s h [[r_z [r_k Hmem]] r_ext].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(** while (bne ext r0) ( *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists Z next,
  size Z = next /\ u2Z [ext]_s = Z_of_nat next /\ u2Z [k]_s = Z_of_nat nk /\
  (next <= nk)%nat /\ u2Z [Z_]_s = u2Z [z]_s + 4 * Z_of_nat (nk - next) /\
  [z]_s = vz /\ (var_e z |--> nseq (nk - next) zero32 ++ Z) s h).

move=> s h [[[r_z [r_k Hmem]] r_Z] r_ext].
exists Z, nk; repeat (split; trivial).
by rewrite r_ext sext_0 addi0.
by rewrite subnn mulZ0 r_Z sext_0 addi0 Zplus_0_r.
by rewrite subnn.

move=> {Z HlenZ} s h [[Z [next [len_Z [Hnext [r_k [Hextnk [r_Z [r_z Hmem]]]]]]]] Hext]; rewrite /= in Hext.
repeat (split; trivial).
have {}Hext : next = O.
  move/negPn/eqP : Hext.
  rewrite Hnext store.get_r0 /zero32 Z2uK //; exact/Z_of_nat_0.
subst next.
destruct Z; last by [].
by rewrite Hext subn0 cats0 in Hmem.

clear Z HlenZ.

(**     sw r0 zero16 Z_ ; *)

apply (hoare_prop_m.hoare_stren (fun s h => exists Z next,
  size Z = next /\ (0 < next /\ next <= nk)%nat /\ u2Z [ext]_s = Z_of_nat next /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [Z_]_s = u2Z [z]_s + 4 * Z_of_nat (nk - next) /\
  [z]_s = vz /\ (var_e z |--> nseq (nk - next) zero32 ++ Z) s h)).

move=> s h [[Z [next [HlenZ [Hnext [r_k [r_Z [Hextnk [r_z Hmem]]]]]]]] Hext]; rewrite /= in Hext.
have {}Hext : (O < next)%nat.
  rewrite ltnNge leqn0; apply/negP => /eqP abs.
  move/eqP : Hext.
  rewrite Hnext store.get_r0 /zero32 Z2uK //.
  by rewrite abs.
by exists Z, next; repeat (split; trivial).

apply hoare_sw_back'' with (fun s h => exists Z next,
  size Z = (next - 1)%nat /\ (O < next /\ next <= nk)%nat /\ u2Z [ext]_s = Z_of_nat next /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [Z_]_s = u2Z [z]_s + 4 * Z_of_nat (nk - next) /\
  [z]_s = vz /\ (var_e z |--> nseq (nk.+1 - next) zero32 ++ Z) s h).

move=> s h [Z [next [HlenZ [[Hnext1 Hnext2] [r_ext [r_k [r_Z [r_z Hmem]]]]]]]].

destruct Z as [|hd tl].
rewrite -HlenZ //= in Hnext1.

have Htmp : [ var_e Z_ \+ int_e (sext 16 zero16) ]e_ s = [ var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * (nk - next)))) ]e_ s.
  rewrite /= sext_0 addi0; apply u2Z_inj.
  rewrite u2Z_add_Z_of_nat.
  by rewrite inj_mult.
  rewrite -Zbeta1E inj_mult inj_minus1 //; last exact/leP.
  rewrite mulZDr [Zmult]lock /= -lock r_z; move: (min_u2Z vz) => ?; omega.

exists (int_e hd).

rewrite (decompose_equiv _ _ _ _ _ (size_nseq _ _)) // assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // ht.
exact: mapsto_ext.
apply currying => h' H'.
exists tl, next; repeat (split; trivial).
by rewrite -HlenZ /= subSS subn0.

rewrite subSn // nseqS -catA (decompose_equiv _ _ _ _ _ (size_nseq _ _)).
assoc_comm H'.
move: H'; apply mapsto_ext => //.
by rewrite /= store.get_r0.

(**    addiu Z_ Z_ four16 ; *)

apply hoare_addiu with (fun s h => exists Z next,
  size Z = (next - 1)%nat /\ (O < next /\ next <= nk)%nat /\ u2Z [ext]_s = Z_of_nat next /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [Z_]_s = u2Z [z]_s + 4 * Z_of_nat (nk.+1 - next) /\
  [z]_s = vz /\ (var_e z |--> nseq (nk.+1 - next) zero32 ++ Z) s h).

move=> s h [Z [next [HlenZ [Hnext [r_ext [r_k [r_Z [r_z Hmem]]]]]]]].
rewrite /wp_addiu; repeat Reg_upd.
exists Z, next; repeat (split; trivial).
rewrite sext_Z2u // u2Z_add_Z2u //.
- rewrite subSn; last by case: Hnext.
  rewrite Z_S r_Z; ring.
- rewrite -Zbeta1E r_Z inj_minus1; last by case: Hnext => _ /leP.
  rewrite r_z.
  have ? : 0 < Z<=nat next by apply Z_of_nat_lt0; case: Hnext.
  omega.
by Assert_upd.

(**    addiu ext ext mone16). *)

apply hoare_addiu'.
move=> s h [Z [next [len_Z [[Hnext1 Hnext2] [r_ext [r_k [r_Z [r_z Hmem]]]]]]]].

rewrite /wp_addiu; exists Z, (next - 1)%nat; repeat Reg_upd.
rewrite (_ : nk - (next - 1) = nk.+1 - next)%nat; last by rewrite subnBA // addn1.
repeat (split; trivial).

rewrite sext_Z2s // u2Z_add_Z2s //.
  rewrite inj_minus1; last exact/leP.
  by rewrite r_ext.
suff ? : 0 < Z<=u [ext]_s by omega.
rewrite r_ext.
exact/Z_of_nat_lt0.
by rewrite subn1 (leq_trans _ Hnext2) // leq_pred.
by Assert_upd.
Qed.

End multi_zero_u.

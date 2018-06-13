(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ZArith_ext uniq_tac machine_int multi_int.
Import MachineInt.
Require Import mips_seplog mips_contrib mips_tactics.
Require Import multi_is_even_u_prg.
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

Lemma multi_is_even_u_triple k a ret : uniq(k, a, ret, r0) ->
  forall nk A va, size A = nk ->
  {{ fun s h => u2Z [ k ]_s = Z_of_nat nk /\ [a]_s = va /\ (var_e a |--> A) s h }}
  multi_is_even_u k a ret
  {{ fun s h => 
    u2Z [ k ]_s = Z_of_nat nk /\ [a]_s = va /\ (var_e a |--> A) s h /\
    (Zeven (\S_{ nk } A) -> [ret]_s = one32) /\ (Zodd (\S_{ nk } A) -> [ret]_s = zero32) }}.
Proof.
move=> Hset nk A va HlenA.
rewrite /multi_is_even_u.

(** ifte_beq k, r0 thendo *)

apply while.hoare_ifte.

(** addiu ret r0 one16 *)

apply hoare_addiu'.
rewrite /wp_addiu => s h [[Hk [Hva Hmem]] /= Hk'].
destruct nk; last by rewrite Hk store.get_r0 Z2uK in Hk'.
repeat Reg_upd; repeat (split => //).
by Assert_upd.
move=> _; by rewrite sext_Z2u // add0i.
 
(** lw ret zero16 a *)

apply hoare_lw_back_alt'' with (fun s h => u2Z [k ]_ s = Z_of_nat nk /\ [a ]_ s = va /\
  (var_e a |--> A) s h /\ [ret]_s = head zero32 A).

move=> [s m] h [[Hk [Hva Hpre]] Hk'].
exists (List.hd zero32 A); split.
- rewrite sext_0.
  destruct A as [|hdA tlA].
  + destruct nk => //.
    by rewrite /= Hk Z2uK in Hk'.
  + rewrite /= in Hpre *.
    case: Hpre => h1 [h2 [Hdisj [Hunion [Hh1 Hh2]]]].
    exists h1, h2; split; first by done.
    split; first by done.
    split; last by done.
    move: Hh1; apply mapsto_ext; last by done.
    by rewrite /= addi0.
- rewrite /update_store_lw; repeat Reg_upd; repeat (split; trivial).
  by Assert_upd.

(** andi ret ret one16 *)

apply hoare_andi with (fun s h => 
  u2Z [k ]_ s = Z_of_nat nk /\ [a ]_ s = va /\ (var_e a |--> A) s h /\
  (Zeven (\S_{ nk } A) -> [ret]_s = zero32) /\ (Zodd (\S_{ nk } A) ->  [ret]_s = one32)).

move => sm h [Hh [Hva [mem Hret]]].
rewrite /wp_andi; repeat Reg_upd.
repeat (split; trivial).
- by Assert_upd.
- move => Hparity.
  have {Hparity}Hparity : Zeven (u2Z [ret]_sm).
    destruct nk => //.
    + rewrite Hret.
      destruct A => //.
      by rewrite Z2uK.
    + apply Zeven_lSum in Hparity => //.
      by rewrite Hret -nth0.
  apply int_even_and_1 in Hparity.
  by rewrite zext_Z2u.
- move=> Hparity.
  have {Hparity}Hparity : Zodd (u2Z [ret]_sm).
    apply Zodd_lSum in Hparity.
    by rewrite Hret -nth0.
  apply int_odd_and_1 in Hparity.
  by rewrite zext_Z2u.

(** xori ret ret one16 *)

apply hoare_xori'.

move=> sm h [Hk [Ha [mem [Hpre1 Hpre2]]]].
rewrite /wp_xori; repeat Reg_upd; repeat (split; trivial).
- by Assert_upd.
- move/Hpre1 => ->; by rewrite int_xorC int_xor_0 zext_Z2u.
- move/Hpre2 => ->; by rewrite zext_Z2u // int_xor_self.
Qed.

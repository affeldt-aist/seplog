(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Init_ext ZArith_ext uniq_tac machine_int multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_zero_u_prg multi_zero_u_triple multi_zero_u_termination.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.

Lemma multi_zero_u_safe_termination a0 a1 rx x rk d : uniq(rk, rx, a0, a1, r0) ->
  safe_termination
  (state_mint (x |=> unsign rk rx \U+ d)) (multi_zero_u rk rx a0 a1).
Proof.
move=> Hset.
rewrite /safe_termination => st s h st_s_h.
set code := multi_zero_u _ _ _ _.
move: (multi_zero_u_termination s h _ _ _ _ Hset) => [x0 Htermi].
have H1 : (u2Z ([ rx ]_ s) + 4 * Z_of_nat (Z.abs_nat (u2Z ([rk ]_ s))) < Zbeta 1)%asm_expr.
  apply state_mint_head_unsign_fit with x d st h.
  by apply st_s_h.
have H2 : (size (Z2ints 32 (Z.abs_nat (u2Z ([ rk ]_ s))) ([ x ]_st)%pseudo_expr) =
  Z.abs_nat (u2Z ([rk ]_ s)))%asm_expr.
  by rewrite size_Z2ints.
move: (multi_zero_u_triple _ _ _ _ Hset _ _ _ H2 H1) => triple_hoare.
apply constructive_indefinite_description'.
apply (mips_syntax.triple_exec_precond _ _ _ triple_hoare _ _ _ Htermi (List.seq
      (Z.abs_nat (u2Z ([rx ]_ s) / 4)) (Z.abs_nat (u2Z ([rk ]_ s))))%asm_expr).
split; first done.
split.
- rewrite Z_of_nat_Zabs_nat //; by apply min_u2Z.
- apply (state_mint_var_mint _ _ _ _ x (unsign rk rx)) in st_s_h; last by assoc_get_Some.
  by apply st_s_h.
Qed.

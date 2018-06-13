(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Epsilon.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Init_ext ssrZ ZArith_ext seq_ext machine_int multi_int.
Require Import encode_decode integral_type uniq_tac.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_double_u_prg multi_double_u_triple multi_double_u_termination.

Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope asm_expr_scope.
Local Open Scope asm_cmd_scope.

Lemma multi_double_u_safe_termination a0 a1 a2 a3 rx x rk d :
  uniq(rk, rx, a0, a1, a2, a3, r0) ->
  safe_termination (state_mint (x |=> unsign rk rx \U+ d))
  (multi_double_u rk rx a0 a1 a2 a3).
Proof.
move=> Hset.
rewrite /safe_termination.
move=> st s h st_s_h.
case/(multi_double_u_termination s h) : (Hset) => x0 exec_mips.
apply constructive_indefinite_description'.
have H1 : u2Z ([ rx ]_ s) + 4 * Z_of_nat '|u2Z ([rk ]_ s)| < Zbeta 1.
  eapply state_mint_head_unsign_fit; by apply st_s_h.
have H3 : size (Z2ints 32 '|u2Z ([rk ]_ s)| ([ x ]_ st)%pseudo_expr) =
  '|u2Z ([rk ]_ s)|.
  by rewrite size_Z2ints.
move: (multi_double_u_triple _ _ _ _ _ _ Hset _ _ H1 _ H3) => Htriple.
move: (triple_exec_precond _ _ _ Htriple _ _ _ exec_mips
  (iota '|u2Z ([rx ]_ s) / 4| '|u2Z ([rk ]_ s)|)).
apply.
split; first by [].
split.
- rewrite Z_of_nat_Zabs_nat //; exact/min_u2Z.
- apply (state_mint_var_mint _ _ _ _ x (unsign rk rx)) in st_s_h; last by assoc_get_Some.
  rewrite /var_mint in st_s_h; case: st_s_h; tauto.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Epsilon.
Require Import Init_ext ssrZ ZArith_ext seq_ext uniq_tac machine_int.
Require Import multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_one_u_prg multi_one_u_triple multi_zero_u_safe_termination.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope zarith_ext_scope.

Lemma safe_termination_one_u a0 a1 rx x rk d : uniq(rk, rx, a0, a1, r0) ->
  safe_termination
  (fun st s h => state_mint (x |=> unsign rk rx \U+ d) st s h /\
                 (0 < '|u2Z ([rk ]_ s)|)%nat)
  (multi_one_u rk rx a0 a1).
Proof.
move=> Hset.
rewrite /safe_termination.
move=> st s h st_s_h.
set code := multi_one_u _ _ _ _.
have [x0 Htermi] : {x0 | Some (s, h) -- code ---> x0}.
  have [sf Htermi] : {x0 | Some (s, h) -- code ---> x0 /\ forall s, x0 = Some s -> True}.
    rewrite /code /multi_one_u.
    apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
      apply constructive_indefinite_description.
      move: (multi_zero_u_safe_termination a0 a1 rx x rk d Hset).
      case/(_ _ _ _ (proj1 st_s_h)) => sf Htermi_zero_u.
      by exists (Some sf).
    destruct si as [[sti hi]|].
    move=> HP.
    eapply exists_addiu_seq_P.
    repeat Reg_upd.
    rewrite add0i.
    exists_sw1 l_idx H_l_idx z_idx H_z_idx => //.
    move=> HP.
    exists None.
    split=> //; exact: while.exec_none.
  exists sf.
  by case: Htermi.
have H1 : u2Z ([ rx ]_ s) + 4 * Z_of_nat '|u2Z ([rk ]_ s)| < \B^1.
  apply state_mint_head_unsign_fit with x d st h.
  by apply st_s_h.
have H3 : size (Z2ints 32 '|u2Z ([ rk ]_ s)| ([ x ]_st)%pseudo_expr) =
  '|u2Z ([rk ]_ s)|.
  by rewrite size_Z2ints.
have Hnk : (0 < '|u2Z ([ rk ]_ s)|)%nat by tauto.
move: (multi_one_u_triple _ _ _ _ Hset _ _ _ Hnk H3 H1) => triple_hoare.
apply constructive_indefinite_description'.
apply (triple_exec_precond _ _ _ triple_hoare _ _ _ Htermi
  (seq.iota '|u2Z ([rx ]_ s) / 4| '|u2Z ([rk ]_ s)|)).
split; first by [].
split.
- rewrite Z_of_nat_Zabs_nat //; exact: min_u2Z.
- case: st_s_h => st_s_h _.
  apply (state_mint_var_mint _ _ _ _ x (unsign rk rx)) in st_s_h; last by assoc_get_Some.
  by apply st_s_h.
Qed.

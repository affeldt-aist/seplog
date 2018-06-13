(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Init_ext ZArith_ext seq_ext uniq_tac.
Require Import machine_int multi_int encode_decode integral_type.
Import MachineInt.
Require Import mips_bipl mips_seplog mips_tactics mips_syntax mips_mint.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.
Require Import multi_zero_s_prg multi_zero_s_triple.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope assoc_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_cmd_scope.

Lemma multi_zero_s_safe_termination nk rx x d : uniq(rx, r0) ->
  safe_termination (state_mint (x |=> signed nk rx \U+ d))
  (multi_zero_s rx).
Proof.
move=> Hset.
rewrite /safe_termination.
move=> s st h s_st_h.
have Htermi : {x0 | Some (st, h) -- multi_zero_s rx  ---> x0}.
  have Htermi : {x0 | Some (st, h) -- multi_zero_s rx ---> x0 /\ (forall s, x0 = Some s -> True)}.
    rewrite /multi_zero_s.
    by exists_sw1 l_idx H_l_idx z_idx H_z_idx.
  case: Htermi => sf [] ? ?.
  by exists sf.
case: Htermi => sf Htermi.
move: (multi_zero_s_triple _ Hset).
move: (proj1 s_st_h x (signed nk rx)).
rewrite assoc.get_union_sing_eq.
case/(_ refl_equal) => len ptr A rx_fit encoding ptr_fit Hmem.
move/(_ A ptr len) => triple_hoare.
apply constructive_indefinite_description'.
move: (triple_exec_precond _ _ _ triple_hoare _ _ _ Htermi (heap.dom (heap_mint (signed nk rx) st h))).
apply.
suff : h |P| heap.dom (heap_mint (signed nk rx) st h) = heap_mint (signed nk rx) st h.
  by move=> ->.
rewrite -heap.incluE; by apply heap_inclu_heap_mint_signed.
Qed.

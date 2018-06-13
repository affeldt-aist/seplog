(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Max Omega List ZArith EqNat.
Require Import seplog.
Require Import expr_b_dp.
Require Import frag_list_triple.
Require Import frag_list_entail.

Import seplog_Z_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope frag_list_scope.

Local Close Scope Z_scope.

(** with bigtoe *)

Lemma max3_verif :
  {{{ (true_b, frag_list_entail.emp) }}}
  If var_e 1 \>= var_e 2 Then
    If var_e 1 \>= var_e 3 Then
      0 <- var_e 1
    Else
      0 <- var_e 3
  Else
    If var_e 2 \>= var_e 3 Then
      0 <- var_e 2
    Else
      0 <- var_e 3
  {{{ (var_e 0 \= var_e 1 \|| var_e 0 \= var_e 2 \|| var_e 0 \= var_e 3, frag_list_entail.emp) }}}.
Proof.
eapply tritra_use.
simpl.
eapply refl_equal.
Tritra.
(*  eapply tritra_if.
  eapply tritra_if.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  eapply tritra_if.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  Show Proof.*)
  (* proof size = 568 *)
Qed.

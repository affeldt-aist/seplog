(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect eqtype.
Require Import List Max Omega ZArith EqNat.
Require Import bipl seplog.
Require Import expr_b_dp.
Import seplog_Z_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.
Require Import frag_list_triple frag_list_entail.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope frag_list_scope.
Local Close Scope Z_scope.

(** initialize some field of an array of data-structure*)

Definition ptr : var.v := 1.
Definition startl : var.v := 2.
Definition size: var.v := 3.
Definition idx: var.v := 4.
Definition init_val: var.v := 5.

Fixpoint init_body (n: nat) {struct n} : @while.cmd cmd0 expr_b :=
  match n with
    0 => skip
    | S n' =>
      (var_e ptr \+ var_e idx) *<- var_e init_val;
       ptr <- var_e ptr \+ var_e size;
       init_body n'
   end.

Definition init (n: nat) : @while.cmd cmd0 expr_b :=
    ptr <- var_e startl;
    init_body n.

Fixpoint init_precond_sigma (n: nat) {struct n} : Sigma :=
  match n with
    0 => frag_list_entail.emp
    | S n' => star
        (cell (var_e startl \+ var_e idx \+ var_e size \* cst_e (Z_of_nat n')))
	(init_precond_sigma n')
end.

Definition init_precond (n: nat) : assrt :=
  (var_e startl \> cst_e 0%Z, init_precond_sigma n).

Fixpoint init_postcond_sigma (n: nat) {struct n}: Sigma :=
  match n with
    0 => frag_list_entail.emp
    | S n' => star
	(singl (var_e startl \+ var_e idx \+ var_e size \* cst_e (Z_of_nat n')) (var_e init_val))
	(init_postcond_sigma n')
end.

Definition init_postcond (n: nat) : assrt :=
  (var_e startl \> cst_e 0%Z, init_postcond_sigma n).

Lemma init_verif_bigtoe_12 : forall n, n = 12 ->
  {{{ init_precond n }}} init n {{{ init_postcond n }}}.
Proof.
intros; subst n.
rewrite /init; simpl init_body.
rewrite /init_precond; simpl init_precond_sigma.
rewrite /init_postcond; simpl init_postcond_sigma.
rewrite /ptr /startl /size /idx /init_val.
eapply tritra_use.
simpl; intuition.
Tritra.
Qed.

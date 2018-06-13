(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import List ZArith EqNat.
From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import bipl seplog.
Require Import frag_list_entail frag_list_triple frag_list_vcg.

Require Import expr_b_dp.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.

Local Close Scope Z_scope.

(** an initialization of a field for an array of structure *)

Definition ptr : var.v := 1.
Definition startl : var.v := 2.
Definition size: var.v := 3.
Definition idx: var.v := 4.
Definition init_val: var.v := 5.

Fixpoint init_body (n : nat) : @while.cmd cmd0 expr_b :=
  match n with
    | 0 => skip
    | S n' =>
      (var_e ptr \+ var_e idx) *<- var_e init_val;
      ptr <- (var_e ptr) \+ (var_e size);
      init_body n'
   end.

Definition init (n : nat) : @while.cmd cmd0 expr_b :=
  ptr <- var_e startl ;
  init_body n.

Fixpoint init_precond_sigma (n : nat) : Sigma :=
  match n with
    | 0 => frag_list_entail.emp
    | S n' => star
      (cell (var_e startl \+ var_e idx \+ var_e size \* cst_e (Z_of_nat n')))
      (init_precond_sigma n')
  end.

Definition init_precond (n : nat) : assrt :=
  (var_e startl \> cst_e 0%Z, init_precond_sigma n).

Fixpoint init_postcond_sigma (n : nat) : Sigma :=
  match n with
    | 0 => frag_list_entail.emp
    | S n' => star
      (singl
        (var_e startl \+ var_e idx \+ var_e size \* cst_e (Z_of_nat n'))
        (var_e init_val))
      (init_postcond_sigma n')
  end.

Definition init_postcond (n : nat) : assrt :=
  (var_e startl \> cst_e 0%Z, init_postcond_sigma n).

Lemma init_verif : forall n, n = 3 ->
  {{ assrt_interp (init_precond n) }}
  init n
  {{ Assrt_interp (init_postcond n :: nil) }}.
Proof.
intros; subst n.
rewrite /init; simpl init_body.
rewrite /init_precond; simpl init_precond_sigma.
rewrite /init_postcond; simpl init_postcond_sigma.
rewrite /ptr /startl /size /idx /init_val.
eapply tritra_use.
simpl; reflexivity.
Tritra.
Qed.

Local Open Scope frag_list_vc_scope.

Lemma init_verif' : forall n, n = 2 ->
  {{ Assrt_interp (init_precond n :: nil) }}
  init n
  {{ Assrt_interp (init_postcond n :: nil) }}.
Proof.
intros; subst n.
rewrite /init; simpl init_body.
rewrite /init_precond; simpl init_precond_sigma.
rewrite /init_postcond; simpl init_postcond_sigma.
rewrite /ptr /startl /size /idx /init_val.
match goal with
|- {{ _ }} ?C {{ _ }} =>
replace C with (frag_list_vcg.proj_cmd
  (1 <- var_e 2 ;
  (var_e 1 \+ var_e 4 *<- var_e 5 ;
  (1 <- var_e 1 \+ var_e 3 ;
  (var_e 1 \+ var_e 4 *<- var_e 5 ;
  (1 <- var_e 1 \+ var_e 3) ;
  skip'')))))
end.
apply bigtoe_fun_correct.
vm_compute; reflexivity.
reflexivity.
Qed.

Local Close Scope frag_list_vc_scope.

Lemma test1 : {{ assrt_interp (true_b, frag_list_entail.emp) }}
  If (var_e 1 \>= var_e 2) Then
    If (var_e 1 \>= var_e 3) Then
      (0 <- var_e 1)
    Else
      (0 <- var_e 3)
  Else
    If (var_e 2 \>= var_e 3) Then
      (0 <- var_e 2)
    Else
      (0 <- var_e 3)
  {{ Assrt_interp ((true_b,frag_list_entail.emp) :: nil) }}.
Proof.
eapply tritra_use.
simpl; reflexivity.
Tritra.
Qed.

Lemma test2 :
  {{ Assrt_interp ((true_b, frag_list_entail.emp) :: nil) }}
  If (var_e 1 \>= var_e 2) Then
    If (var_e 1 \>= var_e 3) Then
      (0 <- var_e 1)
    Else
      (0 <- var_e 3)
  Else
    If (var_e 2 \>= var_e 3) Then
      (0 <- var_e 2)
    Else
      (0 <- var_e 3)
  {{ Assrt_interp ((var_e 0 \= var_e 1 \|| var_e 0 \= var_e 2 \|| var_e 0 \= var_e 3, frag_list_entail.emp)::nil) }}.
Proof.
Local Open Scope frag_list_vc_scope.
match goal with
  |- {{ _ }} ?C {{ _ }} =>
    replace C with
      (frag_list_vcg.proj_cmd (ifte'' (var_e 1 \>= var_e 2)
        (ifte'' (var_e 1 \>= var_e 3) (0 <- var_e 1) (0 <- var_e 3))
        (ifte'' (var_e 2 \>= var_e 3) (0 <- var_e 2) (0 <- var_e 3))))
end.
Local Close Scope frag_list_vc_scope.
apply bigtoe_fun_correct.
compute; reflexivity.
reflexivity.
Qed.

Lemma test3 :
  {{ assrt_interp (true_b, frag_list_entail.emp) }}
  If (var_e 1 \>= var_e 2) Then
    If (var_e 1 \>= var_e 3) Then
      (0 <- var_e 1)
    Else
      (0 <- var_e 3)
  Else
    If (var_e 2 \>= var_e 3) Then
      (0 <- var_e 2)
    Else
      (0 <- var_e 3)
  {{ Assrt_interp ((var_e 0 \= var_e 1 \|| var_e 0 \= var_e 2 \|| var_e 0 \= var_e 3, frag_list_entail.emp)::nil) }}.
Proof.
eapply tritra_use.
simpl; reflexivity.
Tritra.
Qed.

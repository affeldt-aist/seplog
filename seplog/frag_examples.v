(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import EqNat ZArith List Lia.

Require Import bipl seplog frag expr_b_dp.

Import seplog_Z_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_hoare_scope.

(* TODO Definition i : var.v := 1%nat.
Definition j : var.v := 2%nat.
Definition x : var.v := 4%nat.
Definition y : var.v := 3%nat.
Definition vx : var.v := 5%nat.
Definition vy : var.v := 6%nat.*)

(** initialization of a field for an array of structure *)

Definition ptr : var.v := 1%nat.
Definition startl : var.v := 2%nat.
Definition size: var.v := 3%nat.
Definition idx: var.v := 4%nat.
Definition init_val: var.v := 5%nat.

Fixpoint init_body (n : nat) : @while.cmd cmd0 expr_b :=
  match n with
    | O => skip
    | S n' =>
      (var_e ptr \+ var_e idx) *<- var_e init_val;
      ptr <- var_e ptr \+ var_e size;
      init_body n'
  end.

Definition init (n : nat) : @while.cmd cmd0 expr_b :=
  ptr <- var_e startl;
  init_body n.

Fixpoint init_precond_sigma (n : nat) {struct n} : Sigma :=
  match n with
    | O => epsi
    | S n' => star
      (cell (var_e startl \+ var_e idx \+ var_e size \* cst_e (Z_of_nat n')) )
	(init_precond_sigma n')
end.

Definition init_precond (n : nat) : assrt :=
  (var_e startl \> cst_e 0%Z, init_precond_sigma n).

Fixpoint init_postcond_sigma (n : nat) : Sigma :=
  match n with
    | O => epsi
    | S n' => star
      (singl (var_e startl \+ var_e idx \+ var_e size \* cst_e (Z_of_nat n')) (var_e init_val))
      (init_postcond_sigma n')
  end.

Definition init_postcond (n : nat) : assrt :=
  (var_e startl \> cst_e 0%Z, init_postcond_sigma n).

Lemma init_verif : forall n, n = 2%nat ->
  {{ assrt_interp (init_precond n) }}
  init n
  {{ assrt_interp (init_postcond n) }}.
Proof.
move=> n Hn; subst n.
rewrite /init /init_body /init_precond /init_precond_sigma /init_postcond /init_postcond_sigma
  /ptr /startl /size /idx /init_val.
eapply LWP_use.
simpl; reflexivity.
LWP_Resolve.
Qed.

Require Import integral_type.
Module Import ZIT_prop_m := IntegralType_Prop ZIT.

Lemma init_verif_step_by_step : forall n, n = 2%nat ->
  {{ assrt_interp (init_precond n) }}
  init n
  {{ assrt_interp (init_postcond n) }}.
Proof.
move=> n Hn; subst n.
rewrite /init /init_body /init_precond /init_precond_sigma /init_postcond /init_postcond_sigma
  /ptr /startl /size /idx /init_val.
eapply LWP_use.
simpl; reflexivity.

Rotate_LWP_sig_lhs.
match goal with
    | |- LWP ?L (wpSubst ?l (wpMutation ?e1 ?e2 ?L')) =>
      eapply LWP_subst_mutation; simpl; idtac
end.
match goal with
    | |- LWP (?pi1, star ?sig1 (cell ?e1)) (wpMutation ?e3 ?e4 ?L') =>
      (apply LWP_mutation'; [do 2 intro; omegab | LWP_resolve] || Rotate_LWP_sig_lhs; idtac)
end.
match goal with
    | |- LWP (?pi1, star ?sig1 (cell ?e1)) (wpMutation ?e3 ?e4 ?L') =>
      (apply LWP_mutation'; [idtac | LWP_resolve] )
end.
(intros || idtac); eval_b2Prop_hyps(*Eval_b_hyp_clean*); eval_b2Prop_goal (*Eval_b_goal*);
(try tauto || lia || ((repeat open_integral_type_hyp);open_integral_type_goal);
  unfold integral_type.ZIT.t in |- * ;
    idtac).
lia.

LWP_Resolve.

Qed.

Lemma init_verif_refl : forall n, n = 5%nat ->
  {{ assrt_interp (init_precond n) }}
  init n
  {{ assrt_interp (init_postcond n) }}.
Proof.
intros; subst n.
rewrite /init; simpl init_body.
rewrite /init_precond; simpl init_precond_sigma.
rewrite /init_postcond; simpl init_postcond_sigma.
rewrite /ptr /startl /size /idx /init_val.
apply frag_hoare_correct.
compute; reflexivity.
Qed.

Local Open Scope nat_scope.

Lemma test_tactic :
  {{ assrt_interp (true_b, epsi) }}
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
  {{ assrt_interp (true_b, epsi) }}.
Proof.
eapply LWP_use.
simpl; intuition.
LWP_Resolve.
Qed.

Lemma test_refl :
  {{ assrt_interp (true_b, epsi) }}
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
  {{ assrt_interp ((var_e 0 \= var_e 1 \|| var_e 0 \= var_e 2 \|| var_e 0 \= var_e 3, epsi)) }}.
Proof.
apply frag_hoare_correct.
compute; reflexivity.
Qed.

Lemma test2_refl :
  {{ assrt_interp (true_b, epsi) }}
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
  {{ assrt_interp (var_e 0 \= var_e 1 \|| var_e 0 \= var_e 2 \|| var_e 0 \= var_e 3, epsi) }}.
Proof.
eapply LWP_use.
simpl; intuition.
LWP_Resolve.
Qed.

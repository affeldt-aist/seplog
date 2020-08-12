(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import List ZArith EqNat.
Require Import bipl.
Require Import seplog.
Require Import frag_list_entail.
Require Import frag_list_triple.
Require Import frag_list_vcg.
Require Import expr_b_dp.

Require Import integral_type.

Import seplog_Z_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_hoare_scope.
Local Open Scope frag_list_vc_scope.

Import ZIT.

Coercion nat_e : nat >-> expr.

Local Close Scope Z_scope.

Definition next := 0%Z.
Definition data := 1%Z.
Definition i := 2.
Definition j := 3.
Definition k := 4.

Definition reverse_list_precond := (true_b, lst (var_e i) 0) :: nil.

Definition reverse_list_postcond := (true_b, lst (var_e j) 0) :: nil.

Definition invariant :=
  (var_e i \= 0 , lst (var_e j) 0) ::
  (var_e i \!= 0, star (lst (var_e i) 0) (lst (var_e j) 0)) ::
  nil.

Definition invariant_auto :=
  ((var_e i \!= 0) \&& (var_e j \= 0), lst (var_e i) 0) ::
  ((var_e j \!= 0) \&& (var_e i \= k), star (lst (var_e k) 0) (lst (var_e j) 0)) ::
  nil.

Definition invariant2 := (true_b, star (lst (var_e i) 0) (lst (var_e j) 0)) :: nil.

Definition reverse_list : cmd'' :=
  (j <- 0);
  while'' (var_e i \!= 0) invariant2 (
    (k <-* (i -.> next));
    (i -.> next) *<- var_e j ;
    (j <- var_e i);
    (i <- var_e k)
  ).

Lemma reverse_list_verif_frag :
  {{ Assrt_interp reverse_list_precond }} frag_list_vcg.proj_cmd reverse_list {{ Assrt_interp reverse_list_postcond }}.
Proof.
apply frag2_hoare_correct.
vm_compute.
reflexivity.
Qed.

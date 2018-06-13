(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import EqNat.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ZArith_ext uniq_tac.
Require Import bipl seplog.
Require Import integral_type.

Module seplog_Z_m := Seplog ZIT.
Import seplog_Z_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.
Local Open Scope Z_scope.

(** structure ProcContextPtr *)

Definition pcp_tf_gs := 0.
Definition pcp_tf_fs := 1.
Definition pcp_tf_es := 2.
Definition pcp_tf_ds := 3.
Definition pcp_tf_trapno := 4.
Definition pcp_tf_edi := 5.
Definition pcp_tf_esi := 6.
Definition pcp_tf_ebp := 7.
Definition pcp_tf_temp_esp := 8.
Definition pcp_tf_ebx := 9.
Definition pcp_tf_edx := 10.
Definition pcp_tf_ecx := 11.
Definition pcp_tf_eax := 12.
Definition pcp_tf_err := 13.
Definition pcp_tf_eip := 14.
Definition pcp_tf_cs := 15.
Definition pcp_tf_eflags := 16.
Definition pcp_tf_esp := 17.
Definition pcp_tf_ss := 18.

(** structure Thread *)

Definition th_contextPtr := 0.
Definition th_id := 1.
Definition th_name := 2.
Definition th_parentId := 3.
Definition th_stackStart := 4.
Definition th_stackEnd := 5.
Definition th_msgQueue := 6.
Definition th_schedInfo := 7.
Definition th_stat := 8.

Local Close Scope Z_scope.
Local Close Scope positive_scope.

Definition USER : Z := 1%Z.
Definition KERNEL : Z := 0%Z.

Axiom sizeof_Message : nat.
Axiom exitCodeLength : nat.
Axiom MAXNAMESIZE : nat.
Axiom STATUS_INT_ENABLE_USER_PREV : nat.
Axiom STATUS_INT_ENABLE_KERNEL_PREV : nat.

Local Open Scope vc_scope.

Definition skip : cmd' := (0) <- (var_e 0).

(** Subroutines *)

(*
void stringNCopy(char* target, char* source, unsigned long int size)
{
  while ((( *target++ = *source++) != '\0') && ((--size) > 1)) ;
  *target = '\0';
}
*)

Local Open Scope Z_scope.

(** tmp serves as a temporary buffer variable *)
Definition stringNCopy (tmp target source size : nat) :=
  tmp <-* var_e source;
  var_e target *<- var_e tmp;
  size <- var_e size \- cst_e 1%Z;
  while' (var_e tmp \= cst_e 0 \&& var_e size \!= cst_e 0) (TT) (
    tmp <-* var_e source;
    var_e target *<- var_e tmp;
    size <- var_e size \- cst_e 1
  ).

(** Initialization of fields for registers *)

Definition tmSetMachineDependentRegisters (context_ptr space : nat) :=
  ifte' (var_e space \= cst_e USER) 
  ( (context_ptr -.> pcp_tf_cs) *<- cst_e 3;
    (context_ptr -.> pcp_tf_ds) *<- cst_e 3;
    (context_ptr -.> pcp_tf_es) *<- cst_e 3;
    (context_ptr -.> pcp_tf_fs) *<- cst_e 3;
    (context_ptr -.> pcp_tf_gs) *<- cst_e 3;
    (context_ptr -.> pcp_tf_ss) *<- cst_e 3  )
  ( (context_ptr -.> pcp_tf_cs) *<- cst_e 0;
    (context_ptr -.> pcp_tf_ds) *<- cst_e 0;
    (context_ptr -.> pcp_tf_es) *<- cst_e 0;
    (context_ptr -.> pcp_tf_fs) *<- cst_e 0;
    (context_ptr -.> pcp_tf_gs) *<- cst_e 0;
    (context_ptr -.> pcp_tf_ss) *<- cst_e 0  ).

Definition precond (cs0 ds0 es0 fs0 gs0 ss0 : expr) (context_ptr space : var.v) := fun s h => 
  [ var_e space ]e_ s = USER /\ (
    (context_ptr -.> pcp_tf_cs |~> cs0) **
    (context_ptr -.> pcp_tf_ds |~> ds0) **
    (context_ptr -.> pcp_tf_es |~> es0) **
    (context_ptr -.> pcp_tf_fs |~> fs0) **
    (context_ptr -.> pcp_tf_gs |~> gs0) **
    (context_ptr -.> pcp_tf_ss |~> ss0)) s h.

Definition postcond (context_ptr space : var.v) := 
  (context_ptr -.> pcp_tf_cs |~> cst_e 3) **
  (context_ptr -.> pcp_tf_ds |~> cst_e 3) **
  (context_ptr -.> pcp_tf_es |~> cst_e 3) **
  (context_ptr -.> pcp_tf_fs |~> cst_e 3) **
  (context_ptr -.> pcp_tf_gs |~> cst_e 3) **
  (context_ptr -.> pcp_tf_ss |~> cst_e 3) .

Definition threadBuild 
(** variables for stringNCopy *)
  (stringNCopy_source stringNCopy_target stringNCopy_size : nat)
(** buffer variable *)
  (tmp : nat)
(** local variables *)
  (sp mode_ : nat)
(** parameters *)
  (id parentId name contextPtr stackBaseAddress stackSize mainFunction parameter space threadPtr priority : nat) :=
  (threadPtr -.> th_id) *<- var_e id;
  (threadPtr -.> th_parentId) *<- var_e parentId;
  ifte' (var_e name \!= cst_e 0) 
  ( stringNCopy_source <-* (threadPtr -.> th_name);
    stringNCopy_target <- var_e name;
    stringNCopy_size <- cst_e (Z_of_nat MAXNAMESIZE);
    stringNCopy tmp stringNCopy_source stringNCopy_target stringNCopy_size )
  ( stringNCopy_source <-* (threadPtr -.> th_name);
    stringNCopy tmp stringNCopy_source stringNCopy_target stringNCopy_size ) ;
(* initMsgQueue*)
  ifte' (var_e space \= cst_e USER) 
  ( skip;
    mode_ <- cst_e (Z_of_nat STATUS_INT_ENABLE_USER_PREV) ) 
  ( skip;
    mode_ <- cst_e (Z_of_nat STATUS_INT_ENABLE_KERNEL_PREV) );
  (threadPtr -.> th_stackStart) *<- var_e stackBaseAddress \+ var_e stackSize \- cst_e 4 ;
  (threadPtr -.> th_stackEnd) *<- var_e stackBaseAddress ;
  (threadPtr -.> th_contextPtr) *<- var_e contextPtr ;
(* tmSetMachineDependentRegisters *)
  tmp <-* (threadPtr -.> th_stackStart) ;
  sp <- var_e tmp \- cst_e (Z_of_nat sizeof_Message) \- cst_e (Z_of_nat exitCodeLength)
(* tmSetStackPointer *).

Local Close Scope vc_scope.

Lemma tmSetMachineDependentRegisters_Lemma (cs0 ds0 es0 fs0 gs0 ss0 : expr)
  (context_ptr space : var.v) : uniq (context_ptr :: space :: nil) ->
    {{ (precond cs0 ds0 es0 fs0 gs0 ss0) context_ptr space }}
    proj_cmd (tmSetMachineDependentRegisters context_ptr space)
    {{ postcond context_ptr space }}.
Proof.
move=> H.
rewrite /tmSetMachineDependentRegisters /=.
(** ifte var_e space =e cst_e USER *)
apply while.hoare_ifte.
- apply (hoare_prop_m.hoare_stren (precond cs0 ds0 es0 fs0 gs0 ss0 context_ptr space)).
    rewrite /while.entails; by intuition.
  rewrite /precond /postcond.
  apply (hoare_prop_m.hoare_stren ((context_ptr -.> pcp_tf_cs |~> cs0) **
    (context_ptr -.> pcp_tf_ds |~> ds0) **
    ((context_ptr -.> pcp_tf_es) |~> es0) **
    ((context_ptr -.> pcp_tf_fs) |~> fs0) **
    ((context_ptr -.> pcp_tf_gs) |~> gs0) **
    ((context_ptr -.> pcp_tf_ss) |~> ss0))).
  rewrite /while.entails; intros; by intuition.
  eapply while.hoare_seq.
    apply frame_rule_R; last exact: inde_nil.
    apply hoare_mutation_local.
  eapply while.hoare_seq.
    rewrite assert_m.conCE !assert_m.conAE.
    apply frame_rule_R; last exact: inde_nil.
    apply hoare_mutation_local.
  eapply while.hoare_seq.
    rewrite assert_m.conCE !assert_m.conAE.
    apply frame_rule_R; last exact: inde_nil.
    apply hoare_mutation_local.
  eapply while.hoare_seq.
    rewrite assert_m.conCE assert_m.conAE.
    apply frame_rule_R; last exact: inde_nil.
    apply hoare_mutation_local.
  eapply while.hoare_seq.
    rewrite assert_m.conCE !assert_m.conAE.
    apply frame_rule_R; last exact: inde_nil.
    apply hoare_mutation_local.
  do 1 rewrite [X in while.hoare _ _ _ _ _ _ X _ _]assert_m.conCE !assert_m.conAE.
  do 5 rewrite [X in while.hoare _ _ _ _ _ _ _ _ X]assert_m.conCE !assert_m.conAE.
  apply frame_rule_R; last exact: inde_nil.
  apply hoare_mutation_local.
- rewrite /precond /=.
  apply hoare_prop_m.hoare_stren with FF.
  + move=> s h [[H3 H4]] /eqP H2; contradiction.
  + exact: hoare_false.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ssreflect.
From mathcomp Require Import eqtype.
Require Import bipl ZArith.
Require Import expr_b_dp.
Require Import topsy_hm.

Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.

Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.

(*
 65 Error hmInit(Address addr)
 66 {
 67     start = (HmEntry)addr;
 68     start->next = (HmEntry)((unsigned long)addr + KERNELHEAPSIZE +
 69                                                             sizeof(HmEntryDesc));
 70     start->status = HM_FREED;
 71
 72     end = start->next;
 73     end->next = NULL;
 74     end->status = HM_ALLOCATED;
 75
 76     hmLock = &hmLockDesc;
 77     lockInit( hmLock);
 78
 79     return HM_INITOK;
 80 }
*)

(** global variable *)
Definition hmEnd : var.v := 1%nat.

Definition hmInit (adr sz : nat) :=
  hmStart <- nat_e adr ;
  hmStart -.> next *<- nat_e adr \+ nat_e sz \- cst_e 2%Z ;
  hmStart -.> status *<- Free ;
  hmEnd <-* hmStart -.> next ;
  hmEnd -.> next *<- cst_e 0%Z ;
  hmEnd -.> status *<- Allocated.

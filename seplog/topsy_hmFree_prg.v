(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ssreflect.
From mathcomp Require Import eqtype.
Require Import ZArith bipl.
Require Import expr_b_dp.
Require Import topsy_hm.

Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.

Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope Z_scope.

(*
113 Error hmFree(Address address)
114 {
115     HmEntry  entry, addressEntry;
116
117     /* check first if pointer is inside the heap */
118     if (((unsigned long)start > (unsigned long)address) ||
119          ((unsigned long)address >= ((unsigned long)end - LEFTOVER))) {
120         WARNING("hmFree got non-heap pointer");
121         return HM_FREEFAILED;
122     }
123
124     /*** here we enter a critical section */
125     lock(hmLock);
126
127     entry = start;
128     addressEntry = (HmEntry)((unsigned long)address - sizeof(HmEntryDesc));
129     while (entry != NULL) {
130         if (entry == addressEntry) break;
131         entry = entry->next;
132     }
133     if (entry == NULL) {
134         unlock( hmLock);
135         return HM_FREEFAILED;
136     }
137     entry->status = HM_FREED;
138
139     unlock( hmLock);
140     return HM_FREEOK;
141 }
*)
Definition HM_FREEFAILED := cst_e 0.
Definition HM_FREEOK := cst_e 1.

Definition hmFree (address : nat) (entry addressEntry tmp result : var.v) :=
  entry <- var_e hmStart;
  addressEntry <- (nat_e address \- cst_e 2);
  While var_e entry \!= null \&& var_e entry \!= var_e addressEntry {{
     tmp <-* entry -.> next;
     entry <- var_e tmp
  }} ;
  If var_e entry \!= null Then
    tmp <-* entry -.> next;
    If var_e tmp \!= null Then
      entry -.> status *<- Free;
      result <- HM_FREEOK
    Else
      (result <- HM_FREEFAILED)
  Else
    result <- HM_FREEFAILED.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ssreflect.
From mathcomp Require Import eqtype.
Require Import bipl.
Require Import expr_b_dp.
Require Import topsy_hm.
Require Import ZArith.

Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.

Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope Z_scope.

(*
140 #define ENTRYSIZE(ptr) ((unsigned long)(ptr->next) - \
141                         (unsigned long)ptr - sizeof(HmEntryDesc))
142
*)
Definition ENTRYSIZE (x tmp : var.v) :=
  tmp <-* x -.> next ;
  tmp <- var_e tmp \- var_e x \- cst_e 2;
  If (nat_e 0 \> var_e tmp) Then
    tmp <- nat_e 0
  Else
    skip.

(*
144 static HmEntry findFree(unsigned long size)
145 {
146     HmEntry entry = start;
147
148     while (entry != NULL) {
149         if (entry->status == HM_FREED && ENTRYSIZE(entry) >= size) break;
150         entry = entry->next;
151     }
152     return entry;
153 }
*)
Definition findFree (size : nat) (entry fnd sz stts : var.v) :=
  entry <- var_e hmStart;
  stts <-* (entry -.> status);
  fnd <- cst_e 0;
  while.while (var_e entry \!= null \&& var_e fnd \!= cst_e 1) (
    stts <-* (entry -.> status);
    ENTRYSIZE entry sz;
    If (var_e stts \= Free \&& var_e sz \>= nat_e size) Then
      (fnd <- cst_e 1)
    Else
      (entry <-* (entry -.> next))).

(*
170 static void compact(HmEntry at)
171 {
172     HmEntry atNext;
173
174     while (at != NULL) {
175         atNext = at->next;
176         while ((at->status == HM_FREED) && (atNext != NULL)) {
177             if (atNext->status != HM_FREED) break;
178             at->next = atNext->next;     /* collapse two free entries into one */
179             atNext = atNext->next;
180         }
181         at = at->next;
182     }
183 }
184
*)

(** original version *)
Definition compact' (cptr nptr brk tmp cstts nstts : var.v) :=
  while.while (var_e cptr \!= null) (
    nptr <-* (cptr -.> next) ;
    brk <- nat_e 1 ;
    cstts <-* (cptr -.> status) ;
    while.while (var_e cstts \= Free \&& var_e nptr \!= null \&& var_e brk \= nat_e 1) (
       nstts <-* (nptr -.> status) ;
       If (var_e nstts \!= Free) Then (
          brk <- nat_e 0
       ) Else (
	 tmp <-* nptr -.> next;
         cptr -.> next *<- var_e tmp ;
(*         nptr <-* nptr -.> next*)
         nptr <- (var_e tmp)
       )
    ) ;
    cptr <-* (cptr -.> next)
  ).

(** optimized version *)
Definition compact (cptr nptr stts : var.v) :=
  while.while (var_e cptr \!= null) (
    stts <-* (cptr -.> status) ;
    (If (var_e stts \=  Free) Then (
      nptr <-* (cptr -.> next) ;
      stts <-* (nptr -.> status) ;
      while.while (var_e stts \= Free) (
        stts <-* (nptr -.> next);
        (cptr -.> next) *<- var_e stts ;
        nptr <- var_e stts ;
        stts <-* (nptr -.> status)))
    Else
      skip) ;
      cptr <-* (cptr -.> next)).

(** constant *)
Definition LEFTOVER : nat := 8%nat.

(*
156 static void split(HmEntry entry, unsigned long int size)
157 {
158     HmEntry new;
159
160     if (ENTRYSIZE(entry) >= (size + sizeof(HmEntryDesc) + LEFTOVER)) {
161         new = (HmEntry)((unsigned long)(entry) + sizeof(HmEntryDesc) + size);
162         new->next = entry->next;
163         new->status = HM_FREED;
164         entry->next = new;
165     }
166     entry->status = HM_ALLOCATED;
167 }
168
*)

(** entry contains the address of a free entry, size is the size we want to allocate *)
Definition split (entry : var.v) (size : nat) (cptr sz : var.v) :=
  ENTRYSIZE entry sz;
  (If (var_e sz \>= (nat_e size \+ nat_e LEFTOVER \+ nat_e 2)) Then (
    cptr <- var_e entry \+ nat_e 2 \+ nat_e size ;
    sz <-* (entry -.> next) ;
    (cptr -.> next) *<- var_e sz ;
    (cptr -.> status) *<- Free ;
    (entry -.> next) *<- var_e cptr)
   Else
     skip)
  ;
  (entry -.> status) *<- Allocated.

(*
162 Error hmAlloc(Address* addressPtr, unsigned long int size)
163 {
164     HmEntry entry;
165
166     if (size == 4)
167       WARNING("Four bytes allocated. Possible pointer problem?");
168
169     size = size + (ALIGN - size % ALIGN);   /* round up to multiple of words */
170     entry = start;
171     *addressPtr = NULL;
172
173     /*** here we enter a critical section */
174     lock(hmLock);
175
176     /* try to find a free piece of memory */
177     entry = findFree(size);
178     if (entry == NULL) {
179         /* compact and try again */
180         compact(start);
181         entry = findFree(size);
182     }
183     if (entry == NULL) {
184         unlock( hmLock);
185         return HM_ALLOCFAILED;
186     }
187     split(entry, size);
188     *addressPtr = (Address)((unsigned long)entry + sizeof(HmEntryDesc));
189
190     unlock(hmLock);
191     return HM_ALLOCOK;
192 }
*)

(** constants *)
Definition HM_ALLOCFAILED := cst_e 0.
Definition HM_ALLOCOK := cst_e 1.

  (** alignment calculus ignored (not relevant to verification) *)
Definition hmAlloc (result : var.v) (size : nat) (entry cptr fnd stts nptr sz : var.v) :=
  (* entry <- var_e hmStart;*) (* useless insn *)
  result <- null;
  findFree size entry fnd sz stts;
  (If (var_e entry \= null) Then (
    cptr <- var_e hmStart;
    compact cptr nptr stts;
    findFree size entry fnd sz stts
  ) Else
    skip)
  ;
  If (var_e entry \= null) Then (
    result <- HM_ALLOCFAILED
  ) Else (
    split entry size cptr sz;
    result <- var_e entry \+ nat_e 2
  ).

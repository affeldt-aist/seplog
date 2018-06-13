(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq.
Require Import ZArith_ext String_ext ssrnat_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_seplog C_pp.

Local Open Scope C_types_scope.
Local Open Scope string_scope.

Module pointer_test.

Module C_Env <: CENV.
Definition g := \wfctxt{ \O \}.
Definition sigma : g.-env := ("i", ityp: uint) :: ("p" , :* (ityp: uint)) :: 
  ("q" , :* (ityp: uchar)) :: nil. 
Definition uniq_vars : uniq (unzip1 sigma) := Logic.eq_refl.
End C_Env.

Module Import C_m := C_Seplog_f C_Env.
Local Open Scope C_cmd_scope.

Check ("i" <-* %"p").

End pointer_test.

Module struct_test.

Definition tg := mkTag "a".
Definition flds : Ctxt.v :=
  ("f", ityp uchar) :: ("g", ityp ulong) :: ("h", ptyp (ptyp (styp tg))) :: nil.
Definition g := \wfctxt{ "a" |> flds \, \O \}.
Definition a := g.-typ: styp tg.
Definition an_array_type := g.-typ: atyp 42 Logic.eq_refl tg.

Eval compute in (sizeof a).
Eval compute in (sizeof an_array_type).

Definition sigma : g.-env := @get_fields g tg.
Eval compute in (field_address 0 "f" (ityp: uchar) sigma Logic.eq_refl).
Eval compute in (field_address 0 "g" (ityp: ulong) sigma Logic.eq_refl).
Eval compute in (field_address 0 "h" (:* (:* (g.-typ: styp tg))) sigma Logic.eq_refl).

(* *)

End struct_test.

Module array_in_struct.

Definition tg := mkTag "a".
Definition bad_flds := ("f", atyp 5 (refl_equal _) tg) :: nil.
(*Definition g := \wfctxt \{ "a" |> bad_flds \, \O \}.*)

Definition boxed_int_tg := mkTag "bint".
Definition boxed_int_fld := ("bint_", ityp sint) :: nil.
Definition flds := ("f", atyp 5 Logic.eq_refl boxed_int_tg) :: nil.
Definition g := \wfctxt{ "a" |> flds \, "bint" |> boxed_int_fld \, \O \}.
Definition astruct := g.-typ: styp tg.

Eval compute in (sizeof astruct).

End array_in_struct.

Module two_self_referential_structs.

(**

example p.151 from "C A Reference Manual" 5th Edition, Samuel P. Harbison III, Guy L. Steele Jr. 2002

{ struct cell ;
  struct header { struct cell   *first; ...};
  struct cell   { struct header *head;  ...};
}

*)

Definition cell_tg := mkTag "cell".
Definition header_tg := mkTag "header".
Definition cell_flds := ("data", ityp uchar) :: ("head", ptyp (styp header_tg)) :: nil.
Definition header_flds := ("first", ptyp (styp cell_tg)) :: nil.
Definition g := \wfctxt{ "cell" |> cell_flds \, "header" |> header_flds \, \O \}.
(* NB: \wfctxt will fail without pointers *)
Definition cell := g.-typ: styp cell_tg.
Definition header := g.-typ: styp header_tg.

Time Eval compute in sizeof cell.
Time Eval compute in sizeof header.

Goal (sizeof cell = 1 + 3 + 4)%nat. by []. Qed.
Goal (sizeof header = 4)%nat. by []. Qed.

Eval compute in (typ_to_string (styp cell_tg) "" "").
Eval compute in (typ_to_string_rec g cell "" "").

End two_self_referential_structs.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
Require Import Init_ext ZArith_ext String_ext seq_ext.
Require Import C_types C_types_fp C_value C_expr C_tactics C_pp POLAR_ssl_ctxt.

Require Import POLAR_library_functions.

Local Open Scope C_types_scope.
Local Open Scope string_scope.

Axiom pp_cmd_ssl_fetch_input :
  forall (n : nat) (H : cover g ssl_context) (x : string_eqType)
         (H0 : env_get x sigma = |_ g.-ityp: sint _|)
         (e1 : exp sigma (:* Ctyp.mk g _ H)) (e2 : exp sigma (g.-ityp: sint)) (tl : string),
  pp_cmd' n (ssl_fetch_input H x H0 e1 e2) tl =
  x ++ " = ssl_fetch_input(" ++ pp_exp g sigma _ e1 (", " ++ pp_exp g sigma _ e2 (");" ++ newline ++ tl)).

Axiom pp_cmd_memcpy :
  forall (n : nat) (x : string_eqType) (H : env_get x sigma = |_ void_p _|)
         (e1 e2 : exp sigma void_p) (e3 : exp sigma size_t) (tl : string),
  pp_cmd' n (memcpy x H e1 e2 e3) tl =
  x ++ " = memcpy(" ++ (pp_exp g sigma _ e1 (", " ++ pp_exp g sigma _ e2 (", " ++ pp_exp g sigma _ e3 (");" ++ newline ++ tl)))).

Axiom pp_cmd_memset :
  forall (n : nat) (x : string_eqType) (H : assoc_get x sigma = |_ void_p _|)
         (e1 : exp sigma void_p) (e2 : exp sigma (g.-ityp: sint)) (e3 : exp sigma size_t) (tl : string),
  pp_cmd' n (memset x H e1 e2 e3) tl =
  x ++ " = memset(" ++ (pp_exp g sigma _ e1 (", " ++ pp_exp g sigma _ e2 (", " ++ pp_exp g sigma _ e3 (");" ++ newline ++ tl)))).

Axiom pp_cmd_md5_update :
  forall (n : nat) (H : cover g (ptyp md5_context)) (e1 : exp sigma (Ctyp.mk g _ H))
         (e2 : exp sigma void_p) (e3 : exp sigma (g.-ityp: sint)) (tl : string),
  pp_cmd' n (md5_update H e1 e2 e3) tl =
  "md5_update(" ++ pp_exp g sigma _ e1 (", " ++ pp_exp g sigma _ e2 (", " ++ pp_exp g sigma _ e3 (");" ++ newline ++ tl))).

Axiom pp_cmd_sha1_update :
  forall (n : nat) (H : cover g (ptyp sha1_context)) (e1 : exp sigma (Ctyp.mk g _ H))
         (e2 : exp sigma void_p) (e3 : exp sigma (g.-ityp: sint)) (tl : string),
  pp_cmd' n (sha1_update H e1 e2 e3) tl =
  "sha1_update(" ++ pp_exp g sigma _ e1 (", " ++ pp_exp g sigma _ e2 (", " ++ pp_exp g sigma _ e3 (");" ++ newline ++ tl))).

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import Init_ext ZArith_ext String_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_pp POLAR_ssl_ctxt.

Module Import C_LittleOp_m := C_Pp_f parse_client_env.
Export C_LittleOp_m.

Local Open Scope C_types_scope.

(** int ssl_fetch_input( ssl_context *ssl, int nb_want ) *)

Axiom ssl_fetch_input : forall (H : cover g ssl_context)
  ret, env_get ret sigma = |_ g.-ityp: sint _| ->
  exp sigma (:* (Ctyp.mk g _ H)) ->  exp sigma (g.-ityp: sint) -> cmd.

Notation "ret '<-ssl_fetch_input(' e , c ')'" :=
  (ssl_fetch_input Logic.eq_refl ret Logic.eq_refl e c) (at level 50) : POLAR_scope.

Definition size_t : g.-typ := ityp: uint.

Definition void_p : g.-typ := :* (ityp: uchar).

(** void *memcpy( void *to, const void *from, size_t count ); *)

Axiom memcpy : forall ret, env_get ret sigma = |_ void_p _| ->
  exp sigma void_p -> exp sigma void_p -> exp sigma size_t -> cmd.

Notation "ret '<-memcpy(' e , f , c ')'" :=
  (memcpy ret Logic.eq_refl e f c) (at level 50) : POLAR_scope.

(** void *memset( void *buffer, int ch, size_t count ); *)

Axiom memset : forall ret, env_get ret sigma = |_ void_p _| ->
  exp sigma void_p -> exp sigma (g.-ityp: sint) -> exp sigma size_t -> cmd.

Notation "ret '<-memset(' e , ch , c ')'" :=
  (memset ret Logic.eq_refl e ch c) (at level 50) : POLAR_scope.

(** file md5.c: void md5_update( md5_context *ctx, const unsigned char *input, int ilen ) *)

Axiom md5_update : forall (H : cover g (ptyp md5_context)),
  exp sigma (Ctyp.mk g _ H) -> exp sigma void_p -> exp sigma (g.-ityp: sint) -> cmd.

Notation "'md5_update(' c , inp , len ')'" :=
  (md5_update Logic.eq_refl c inp len) (at level 50) : POLAR_scope.

(** file sha1.c: void sha1_update( sha1_context *ctx, const unsigned char *input, int ilen ) *)

Axiom sha1_update : forall (H : cover g (ptyp sha1_context)),
  exp sigma (Ctyp.mk g _ H)-> exp sigma void_p -> exp sigma (g.-ityp: sint) -> cmd.

Notation "'sha1_update(' c , inp , len ')'" :=
  (sha1_update Logic.eq_refl c inp len) (at level 50) : POLAR_scope.

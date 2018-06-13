(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import ssrZ ZArith_ext.
Require Import machine_int multi_int.
Import MachineInt.
Require Import mips_bipl.

Import expr_m.
Import assert_m.

Local Open Scope mips_assert_scope.
Local Open Scope mips_expr_scope.
Local Open Scope zarith_ext_scope.

Inductive var_unsign k rx val s h : Prop :=
| mkVarUnsign : u2Z ([ rx ]_s)%mips_expr + 4 * Z_of_nat k < Zbeta 1  ->
  0 <= val < Zbeta k ->
  (var_e rx |--> Z2ints 32 k val) s h ->
  var_unsign k rx val s h.

Inductive SignMagn (sz : int 32) k (X : list (int 32)) val : Prop :=
| mkSignMagn : size X = k ->
  s2Z sz = sgZ (s2Z sz) * Z_of_nat k ->
  sgZ (s2Z sz) = sgZ val ->
  val = sgZ (s2Z sz) * lSum k X ->
  SignMagn sz k X val.

Inductive var_signed k rx val s h : Prop :=
| mkVarSigned : forall l p X,
  u2Z [ rx ]_ s + 4 * 2 < Zbeta 1 ->
  SignMagn l k X val ->
  u2Z p + 4 * Z_of_nat k < Zbeta 1 ->
  (var_e rx |--> l :: p :: nil ** int_e p |--> X)%SEQ s h ->
  var_signed k rx val s h.

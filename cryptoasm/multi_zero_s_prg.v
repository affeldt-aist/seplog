(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.
Import expr_m.
Require Import multi_zero_u_prg.

Local Open Scope mips_cmd_scope.

Definition multi_zero_s' rx a0 a1 a2 a3 :=
  lw a0 zero16 rx ;
  lw a1 four16 rx ;
  multi_zero_u a0 a1 a2 a3.

Definition multi_zero_s rx :=
  sw r0 zero16 rx.

  

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.

Local Open Scope mips_cmd_scope.

Definition multi_negate X a0 := 
  lw a0 zero16 X ; 
  subu a0 r0 a0 ; 
  sw a0 zero16 X.

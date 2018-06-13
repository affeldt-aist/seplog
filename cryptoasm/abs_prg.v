(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.

Local Open Scope mips_cmd_scope.

Definition abs (rx a0 : reg) :=
  addu a0 r0 rx ;
  sra a0 rx (Z2u 5 31) ;
  xor rx rx a0 ;
  subu rx rx a0.
(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.

Local Open Scope mips_cmd_scope.

Definition pick_sign rx a0 a1 :=
  lw a0 zero16 rx ;
  If_beq a0 , r0 Then
    addiu a1 r0 zero16
  Else
   srl a1 a0 (Z2u 5 31) ;
   If_beq a1 , r0 Then
     addiu a1 r0 one16
   Else
     addiu a1 r0 mone16.

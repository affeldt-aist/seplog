(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Require Import multi_is_zero_u_prg copy_u_u_prg multi_zero_s_prg.

Local Open Scope mips_cmd_scope.

Definition copy_s_u rk rd rs a0 a1 a2 a3 :=
  multi_is_zero_u rk rs a0 a1 a2 ;
  If_beq a2 , r0 Then
    lw a0 four16 rd ;
    copy_u_u rk a0 rs a1 a2 a3 ;
    sw rk zero16 rd
  Else
    multi_zero_s rd.

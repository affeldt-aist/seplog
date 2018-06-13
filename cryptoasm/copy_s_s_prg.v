(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Require Import multi_zero_s_prg copy_s_u_prg pick_sign_prg.

Local Open Scope mips_cmd_scope.

Definition copy_s_s rk rd rs a0 a1 a2 a3 a4 :=
  pick_sign rs a0 a1 ;
  If_beq a1, r0 Then
    multi_zero_s rd
  Else
    lw a2 four16 rs; 
    copy_s_u rk rd a2 a0 a1 a3 a4 ;
    lw a0 zero16 rs ;
    sw a0 zero16 rd.
  

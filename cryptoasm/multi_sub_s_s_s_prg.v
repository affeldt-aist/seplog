(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Require Import pick_sign_prg multi_add_s_s_u_prg multi_sub_s_s_u_prg copy_s_s_prg.

Local Open Scope mips_cmd_scope.

(** z <- x - y with z, x, y signed *)
Definition multi_sub_s_s_s rk rz rx ry a0 a1 a2 a3 a4 a5 rX rY rZ :=
  lw rY four16 ry ;
  pick_sign ry a0 a1 ;
  If_bgez a1 Then (* 0 <= y ? *)
    If_beq a1 , r0 Then (* y = 0 ? *)
       copy_s_s rk rz rx a0 a1 a2 a3 a4 ;
       addiu a3 r0 zero16 (* no overflow *)
    Else (* 0 < y *)
       multi_sub_s_s_u rk rz rx rY a0 a1 a2 a3 a4 a5 rX rZ
  Else (* y < 0 *)
    multi_add_s_s_u rk rz rx rY a0 a1 a2 a3 a4 a5 rX rZ.

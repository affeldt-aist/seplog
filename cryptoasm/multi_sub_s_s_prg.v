(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Require Import pick_sign_prg multi_add_s_u_prg multi_sub_s_u_prg.

Local Open Scope mips_cmd_scope.

Section multi_sub_s_s_sect.

Variables rk rx ry a0 a1 a2 a3 a4 a5 rX rY : reg.

(** x <- x - y with x and y signed, expect x and y to be rk words long *)
Definition multi_sub_s_s :=
  lw rY four16 ry ;
  pick_sign ry a0 a1 ;
  If_bgez a1 Then (* 0 <= y ? *)
    If_beq a1 , r0 Then (* y = 0 ? *)
       addiu a3 r0 zero16 (* no overflow *)
    Else (* 0 < y *)
       multi_sub_s_u rk rx rY a0 a1 a2 a3 a4 a5 rX
  Else (* y < 0 *)
    multi_add_s_u rk rx rY a0 a1 a2 a3 a4 a5 rX.

End multi_sub_s_s_sect.

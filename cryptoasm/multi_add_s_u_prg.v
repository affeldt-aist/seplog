(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Import expr_m.
Require Import pick_sign_prg multi_lt_prg multi_add_u_u_prg multi_sub_u_u_prg.
Require Import multi_negate_prg copy_u_u_prg multi_is_zero_u_prg.

Local Open Scope mips_cmd_scope.

(** x <- x + y with x signed and y unsigned, non-zero; the number of words in x
    and y's payloads is supposed to be stored in rk *)

Section multi_add_s_u0_sect.

Variables rk rx ry a0 a1 a2 a3 a4 a5 rX : reg.

Definition multi_add_s_u0 :=
  lw rX four16 rx ; (* payload of X *)
  pick_sign rx a0 a1 ;
  If_bgez a1 Then (* 0 <= x ? *)
    If_beq a1 , r0 Then (* x = 0 ? *)
      copy_u_u rk rX ry a2 a3 a4 ;
      addiu a3 r0 zero16 ; (* no overflow *)
      sw rk zero16 rx (* fix length *)
    Else (* x != 0 *)
      addiu a3 r0 one16 ;
      multi_add_u_u rk a3 ry rX rX a0 a1 a2 ;
      mflo a3 (* overflow *)
  Else (* x < 0 *)
    multi_lt rk ry rX a0 a1 a5 a2 a3 a4 ;
    If_beq a5 , r0 Then (* x <= y ? *)
      If_beq a2 , r0 Then (* x = y ? *)
        addiu a3 r0 zero16 ; (* no overflow *)
        sw r0 zero16 rx  (* fix length *)
      Else (* x < y *)
        multi_sub_u_u rk ry rX rX a0 a1 a2 a3 a4 a5 ;
        multi_negate rx a0
    Else (* x > y *)
      multi_sub_u_u rk rX ry rX a0 a1 a5 a3 a2 a4.

End multi_add_s_u0_sect.

Section multi_add_s_u_sect.

(** same as above except that y can be 0 *)

Variables rk rx ry a0 a1 a2 a3 a4 a5 rX : reg.

Definition multi_add_s_u :=
  multi_is_zero_u rk ry a0 a1 a2 ;
  If_bne a2 , r0 Then (* y = 0 ? *)
    addiu a3 r0 zero16 (* no overflow *)
  Else (* y != 0 *)
    multi_add_s_u0 rk rx ry a0 a1 a2 a3 a4 a5 rX.

End multi_add_s_u_sect.

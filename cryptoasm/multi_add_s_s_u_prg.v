(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Import expr_m.
Require Import pick_sign_prg multi_lt_prg multi_add_u_u_prg multi_sub_u_u_prg.
Require Import multi_negate_prg copy_s_u_prg multi_is_zero_u_prg abs_prg.
Require Import multi_zero_s_prg copy_s_s_prg.

Local Open Scope mips_cmd_scope.

(** z <- x + y with z, x signed and y unsigned *)
Definition multi_add_s_s_u0 rk rz rx ry a0 a1 a2 a3 a4 ret X Z : while.cmd :=
   lw Z four16 rz ;
   lw X four16 rx ;
   pick_sign rx a0 a1 ;
   If_bgez a1 Then (* 0 <= x ? *)
     If_beq a1, r0 Then (* x = 0 ? *)
       copy_s_u rk rz ry a0 a1 a2 a3 ;
       addiu a3 r0 zero16
     Else (* 0 < x *) (* NB: a1 = 1 *)
       multi_add_u_u rk a1 ry X Z a2 a3 a4 ;
       mflo a3;
       sw rk zero16 rz (* fix size *)
   Else (* x < 0 *)
   (multi_lt rk ry X a0 a1 ret a2 a3 a4 ; 
    If_beq ret, r0 Then (* ry >= X ? *)
      If_beq a2, r0 Then (* Y = X *)
        multi_zero_s rz ; (* fix size *)
        addiu a3 r0 zero16 (* no overflow *)
      Else (* Y > X *)
        multi_sub_u_u rk ry X Z a0 a1 a2 a3 a4 ret;
        sw rk zero16 rz (* fix size *)
    Else (* ry < X *)
     (multi_sub_u_u rk X ry Z a0 a1 ret a3 a2 a4;
      subu a0 r0 rk ;
      sw a0 zero16 rz
     )).

Definition multi_add_s_s_u rk rz rx ry a0 a1 a2 a3 a4 ret X Z :=
  multi_is_zero_u rk ry a0 a1 a2 ;
  If_bne a2 , r0 Then (* y = 0 ? *)
    copy_s_s rk rz rx a0 a1 a2 a3 a4 ;
    addiu a3 r0 zero16 (* no overflow *)
  Else (* y <> 0 *) 
    multi_add_s_s_u0 rk rz rx ry a0 a1 a2 a3 a4 ret X Z.
  
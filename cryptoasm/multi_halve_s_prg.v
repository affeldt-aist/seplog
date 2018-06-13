(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Local Open Scope mips_cmd_scope.
Import expr_m.

Require Import abs_prg multi_is_zero_u_prg multi_zero_u_prg multi_is_even_u_prg.
Require Import multi_halve_u_prg multi_zero_s_prg multi_incr_u_prg.

Definition multi_halve_s_noneucl rx a0 a1 a2 a3 a4 rk :=
  lw rk zero16 rx ;
  If_beq rk, r0 Then
    addiu a3 r0 zero16
  Else
    abs rk a0 ;
    lw a0 four16 rx ;
    multi_halve_u rk a0 a1 a2 a3 a4 ;
    multi_is_zero_u rk a0 a1 a2 a4 ;
    If_bne a4 , r0 Then
      multi_zero_s rx
    Else
      nop. 

Definition multi_halve_s rx a0 a1 a2 a3 a4 rk :=
  lw rk zero16 rx ;
  If_beq rk, r0 Then
    addiu a3 r0 zero16
  Else
    lw a0 four16 rx ;
    If_bgtz rk Then
      multi_halve_u rk a0 a1 a2 a3 a4 ;
      multi_is_zero_u rk a0 a1 a2 a4 ;
      If_bne a4 , r0 Then
        multi_zero_s rx
      Else
        nop
    Else
      abs rk a1 ;
      multi_is_even_u rk a0 a2 ;
      If_bne a2 , r0 Then
        multi_halve_u rk a0 a1 a2 a3 a4
      Else
        multi_halve_u rk a0 a1 a2 a3 a4 ;
        addiu a4 r0 one16 ;
        multi_incr_u rk a4 a0 a1 a2 a3 ;
        sll a3 a4 (Z2u 5 31).
       

    

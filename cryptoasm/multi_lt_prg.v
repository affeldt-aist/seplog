(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.

Local Open Scope mips_cmd_scope.
Import expr_m.

Definition multi_lt (k a b i flag ret ret2 atmp btmp : reg) : while.cmd :=
  addiu i k zero16 ;
  addiu flag r0 one16 ;
  If_beq i , r0 Then
    addiu ret r0 zero16 ;
    addiu ret2 r0 zero16
  Else
    While (bne flag r0) {{
      addiu i i mone16 ;
      lwxs atmp i a ;
      lwxs btmp i b ;
      sltu ret atmp btmp ;
      movn flag r0 ret ; (* flag = 0 if atmp < btmp *)
      sltu ret2 btmp atmp ;
      movn flag r0 ret2 ; (* flag = 0 if btmp < atmp *)
      movz flag r0 i (* if atmp = btmp, flag <> 0 *) }}.

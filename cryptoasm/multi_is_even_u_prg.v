(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.
Import expr_m.

Local Open Scope mips_cmd_scope.

Definition multi_is_even_u k a ret :=
  If_beq k , r0 Then
    addiu ret r0 one16
  Else
    lw ret zero16 a ;
    andi ret ret one16 ;
    xori ret ret one16.

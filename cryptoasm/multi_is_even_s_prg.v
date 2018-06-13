(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.
Import expr_m.
Require Import multi_is_even_u_prg pick_sign_prg abs_prg.

Local Open Scope mips_cmd_scope.

Definition multi_is_even_s rx rk a0 a1 :=
  pick_sign rx a0 a1 ;
  If_beq a1, r0 Then
    addiu a1 r0 one16
  Else
    (lw rk zero16 rx ;
     abs rk a0 ;
     lw a0 four16 rx ;
     multi_is_even_u rk a0 a1).

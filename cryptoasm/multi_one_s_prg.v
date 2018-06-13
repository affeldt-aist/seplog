(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.
Require Import multi_zero_s_prg multi_negate_prg.
Import expr_m.

Local Open Scope mips_cmd_scope.

(* NB: we assume that the payload of the pointed mint is of length rk *)
Definition multi_one_s rx rk a0 a1 a2 a3 :=
  lw a0 zero16 rx ;			(* load the length *)
  (If_beq a0 , r0 Then			(* if the length is 0 update it to rk *)
    sw rk zero16 rx
  Else
    If_bltz a0 Then			(* if the length is < 0, negate *)
      multi_negate rx a0
    Else
      nop) ;
  multi_zero_s' rx a0 a1 a2 a3 ;	(* zero the payload *)
  lw a0 four16 rx ;			(* load the address of the beginning of the payload *)
  addiu a1 r0 one16 ;
  sw a1 zero16 a0.			(* store a one in msB position *)


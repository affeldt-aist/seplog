(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.

Local Open Scope mips_cmd_scope.
Import expr_m.

Definition multi_is_zero_u k z k0 a0 ret :=
  addiu k0 r0 zero16 ;
  addiu ret r0 one16;
  While (bne k0 k) {{
    lwxs a0 k0 z ;
    movn ret r0 a0 ;
    addiu k0 k0 one16 }}.


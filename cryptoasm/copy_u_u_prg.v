(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Import expr_m.

Local Open Scope mips_cmd_scope.

Definition copy_u_u rk ry rx tmp ytmp i :=
  addiu ytmp ry zero16 ;
  addiu i r0 zero16 ;
  While (bne i rk) {{
    lwxs tmp i rx ;
    sw tmp zero16 ytmp ;
    addiu i i one16 ;
    addiu ytmp ytmp four16 }}.

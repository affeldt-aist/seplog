(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.
Import expr_m.

Local Open Scope mips_cmd_scope.

Definition multi_zero_u k z ext Z_ :=
  addiu Z_ z zero16 ;
  addiu ext k zero16 ;
  While (bne ext r0) {{
    sw r0 zero16 Z_ ;
    addiu Z_ Z_ four16 ;
    addiu ext ext mone16 }}.

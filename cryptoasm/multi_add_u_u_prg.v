(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.
Import expr_m.

Local Open Scope mips_cmd_scope.

Section multi_add_u_u_sect.

Variables rk r1 rx ry rz rZ a0 rX : reg.

Definition multi_add_u_u :=
  addiu a0 r0 zero16 ;
  addiu rZ rz zero16 ;
  multu r0 r0 ;
  While (bne a0 rk) {{
    lwxs rX a0 rx ;
    maddu rX r1 ;
    lwxs rX a0 ry ;
    maddu rX r1 ;
    mflhxu rX ;
    sw rX zero16 rZ ;
    addiu rZ rZ four16 ;
    addiu a0 a0 one16 }}.

End multi_add_u_u_sect.

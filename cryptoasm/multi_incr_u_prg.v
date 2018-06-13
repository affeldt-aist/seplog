(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.
Import expr_m.

Local Open Scope mips_cmd_scope.

Definition multi_incr_u k one a t j atmp :=
  addiu j r0 zero16 ;
  addiu t a zero16 ;
  multu r0 r0 ;
  While (bne j k) {{
    lwxs atmp j a ;
    maddu atmp one ;
    (If_beq j, r0 Then
      addiu atmp one zero16
    Else
      addiu atmp r0 zero16) ;
    maddu atmp one ;
    mflhxu atmp ;
    sw atmp zero16 t ;
    addiu t t four16 ;
    addiu j j one16 }}.

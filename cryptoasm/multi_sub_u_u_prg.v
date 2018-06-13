(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.

Local Open Scope mips_cmd_scope.
Import expr_m.

Definition multi_sub_u_u (k a b c t j u bor atmp btmp : reg) :=
  addiu j r0 zero16 ;
  addiu t c zero16 ;
  addiu bor r0 zero16 ;
  While (bne j k) {{
    lwxs atmp j b ; 
    addu btmp atmp bor ;
    sltu u btmp atmp ;
    lwxs atmp j a ;
    (If_beq u, r0 Then
      addiu u r0 one16 ;
      multu atmp u ;
      msubu btmp u ;
      sltu bor atmp btmp ;
      mflhxu atmp
    Else
      nop) ;
    sw atmp zero16 t ;
    addiu t t four16 ;
    addiu j j one16 }}.

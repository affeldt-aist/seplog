(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.

Local Open Scope mips_cmd_scope.
Import expr_m.

Definition multi_mul_u_u (k one a b c z t i j l atmp btmp ctmp : reg) :=
  addiu i r0 zero16 ;
  addiu t c zero16 ;
  While (bne i k) {{
    addiu z t zero16 ;
    lwxs atmp i a ;
    addiu j r0 zero16 ;
    While (bne j k) {{
      lwxs btmp j b ;
      maddu atmp btmp ;
      addu l i j ;
      lwxs ctmp l c ;
      maddu ctmp one ;
      mflhxu ctmp ;
      sw ctmp zero16 z ;
      addiu z z four16 ;
      addiu j j one16 }} ;
    mflhxu ctmp ;
    sw ctmp zero16 z ;
    addiu t t four16 ;
    addiu i i one16 }}.

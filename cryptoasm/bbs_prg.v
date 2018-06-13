(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import mips_cmd.
Require Import machine_int.
Require Import mont_mul_strict_prg.

Local Open Scope mips_cmd_scope.
Import expr_m.

Definition bbs (i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C
 t s_ b2k B2K_ w' w : reg) : while.cmd :=
  addiu i r0 zero16 ;
  addiu L_ l zero16 ;
  While (bne i n) {{
    addiu j r0 zero16 ;
    addiu w r0 zero16 ;
    While (bne j thirtytwo) {{
      mont_mul_strict_init k alpha x x y m one ext int_ X_ B2K_ Y_ M_ quot C t s_;
      mont_mul_strict_init k alpha y b2k x m one ext int_ Y_ B2K_ X_ M_ quot C t s_;
      lw w' zero16 x;
      andi w' w' one16 ;
      sllv w' w' j ;
      cmd_or w w w' ;
      addiu j j one16 }} ;
    sw w zero16 L_ ;
    addiu L_ L_ four16 ;
    addiu i i one16 }}.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Local Open Scope mips_cmd_scope.
Import expr_m.

Definition multi_halve_u k a i tmp prev next :=
  addiu i k zero16 ;
  addiu prev r0 zero16 ;
  While (bne i r0) {{
    addiu i i mone16 ;
    lwxs tmp i a ;
    andi next tmp one16 ;
    srl tmp tmp one5 ; 
    cmd_or tmp tmp prev ;
    addiu prev next zero16 ;
    sll prev prev thirtyone5 ;
    sll next i two5 ;
    addu next a next ;
    sw tmp zero16 next }}.

    

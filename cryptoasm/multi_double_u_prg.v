(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.
Local Open Scope mips_cmd_scope.
Import expr_m.

Definition multi_double_u k a i tmp prev next :=
  addiu i r0 zero16 ;
  addiu prev r0 zero16 ;
  While (bne i k) {{
    lwxs tmp i a ;
    srl next tmp thirtyone5 ;
    sll tmp tmp one5 ;
    cmd_or tmp tmp prev ;
    addiu prev next zero16 ;
    sll next i two5 ;
    addu next a next ;
    sw tmp zero16 next ;
    addiu i i one16 }}.

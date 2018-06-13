(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import mips_cmd.
Require Import machine_int.
Require Import mont_mul_strict_prg.

Local Open Scope mips_cmd_scope.
Import expr_m.

Definition mont_exp (k alpha x a' x' i l a ei e one' m one ext int_ X_ Y_ M_ Z_ quot C t s_ : reg) :=
  mont_mul_strict_init k alpha x a' x' m one ext int_ X_ Y_ M_ Z_ quot C t s_ ;
  (addiu i l zero16 ;
   While (bgez i) {{
     mont_mul_strict_init k alpha a a a' m one ext int_ X_ Y_ M_ Z_ quot C t s_ ;
     srlv ei e i ;
     andi ei ei one16 ;
     (If_beq ei, r0 Then
       xor a a a' ;
       xor a' a a' ;
       xor a a a'
     Else
       mont_mul_strict_init k alpha a' x' a m one ext int_ X_ Y_ M_ Z_ quot C t s_) ;
     addiu i i mone16 }}) ;
   mont_mul_strict_init k alpha a one' a' m one ext int_ X_ Y_ M_ Z_ quot C t s_.

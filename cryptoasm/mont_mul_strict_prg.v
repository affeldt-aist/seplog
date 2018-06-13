(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ZArith_ext.
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Require Import multi_lt_prg multi_sub_u_u_prg multi_zero_u_prg mont_mul_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_cmd_scope.

Definition mont_mul_strict k alpha x y z m_ one ext int_ X_ Y_ M_ Z_ quot C t s_ :=
  montgomery k alpha x y z m_ one ext int_ X_ Y_ M_ Z_ quot C t s_ ;
  If_beq C , r0 Then
    multi_lt k z m_ X_ Y_ int_ ext Z_ M_ ;
    If_beq int_ , r0 Then
      multi_sub_u_u k z m_ z ext int_ quot C Z_ Y_
    Else
      nop
  Else
    addiu t t four16 ;
    sw C zero16 t ;
    addiu ext k one16 ;
    multi_sub_u_u ext z m_ z M_ int_ quot C Z_ Y_.

Definition mont_mul_strict_init k alpha x y z m_ one ext int_ X_ Y_ M_ Z_ quot C t s_ :=
  multi_zero_u k z ext Z_ ;
  (mflhxu r0 ;
  mthi r0 ;
  mtlo r0) ; (* NB: replace this sequence by multu r0 r0? *)
  mont_mul_strict k alpha x y z m_ one ext int_ X_ Y_ M_ Z_ quot C t s_.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import multi_is_even_u_prg.
Require Import mips_cmd simu.
Require Import multi_is_even_s_prg.

Local Open Scope mips_cmd_scope.

Definition multi_is_even_s_and rx ry a0 a1 a2 a3 :=
  multi_is_even_s rx a0 a1 a2 ;
  multi_is_even_s ry a0 a1 a3 ;
  cmd_and a0 a2 a3.

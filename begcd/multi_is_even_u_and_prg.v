(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import multi_is_even_u_prg.
Require Import mips_cmd simu.

Local Open Scope mips_cmd_scope.

Definition multi_is_even_u_and rk rx ry a0 a1 :=
  multi_is_even_u rk rx a0 ;
  multi_is_even_u rk ry a1 ;
  cmd_and a0 a0 a1.

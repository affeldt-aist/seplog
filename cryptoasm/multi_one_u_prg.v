(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import machine_int.
Require Import mips_cmd.
Import expr_m.
Require Import multi_zero_u_prg.

Local Open Scope mips_cmd_scope.

Definition multi_one_u k z ext Z_ :=
  multi_zero_u k z ext Z_;
  addiu ext r0 one16 ;
  sw ext zero16 z.

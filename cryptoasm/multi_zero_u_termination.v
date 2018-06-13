(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import ssrZ ZArith_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib uniq_tac.
Import expr_m.
Require Import multi_zero_u_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.

Lemma multi_zero_u_termination s h k z ext M_ :
  uniq (k :: z :: ext :: M_ :: r0 :: nil) ->
  { si | Some (s, h) -- multi_zero_u k z ext M_ ---> si }.
Proof.
move=> Hset; rewrite /multi_zero_u.
apply exists_addiu_seq.
rewrite sext_0 addi0.
apply exists_addiu_seq.
rewrite sext_0 addi0.
repeat Reg_upd.
set s0 := store.upd _ _ _.
have [next Hext] : { kext | u2Z [ext]_s0 = Z_of_nat kext }.
  have [zext Hext] : { zext | u2Z ([ext]_s0) = zext} by eapply exist; reflexivity.
  have : 0 <= zext by rewrite -Hext; apply min_u2Z.
  case/Z_of_nat_complete_inf => next Hzext.
  by exists next; rewrite -Hzext.
move: next s0 Hext h; elim.
- move=> s0 Hext h.
  eapply exist.
  apply while.exec_while_false => /=.
  by rewrite negbK store.get_r0 Z2uK // Hext.
- move=> next IH s0 Hext h; apply exists_while.
  + by rewrite /= store.get_r0 Z2uK // Hext.
  + apply exists_seq_P2 with (fun st => u2Z [ext]_(fst st) = Z_of_nat next).
    * exists_sw_P l Hl z0 Hz0.
      apply exists_addiu_seq_P.
      apply exists_addiu_P.
      rewrite /=.
      repeat Reg_upd.
      rewrite sext_Z2s // u2Z_add_Z2s // Hext Z_S -addZA /= addZC //=; by apply Zle_0_nat.
    * move=> [ si hi ] Hsi.
      by apply IH.
Qed.

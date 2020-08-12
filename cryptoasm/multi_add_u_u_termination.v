(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Require Import multi_add_u_u_prg.
Import expr_m.

Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope machine_int_scope.
Local Open Scope uniq_scope.

(* NB: no hypothesis about a0 (could be =ry) *)
Lemma multi_add_u_u_termination s h a0 rk one rx ry a1 a2 a3 :
  uniq(rk, one, rx, ry, a1, a2, a3, r0) ->
  { si | Some (s, h) -- multi_add_u_u rk one rx ry a0 a1 a2 a3 ---> si }.
Proof.
move=> Hset; rewrite /multi_add_u_u.
apply exists_addiu_seq.
repeat Reg_upd.
rewrite add0i.
apply exists_addiu_seq.
repeat Reg_upd.
rewrite sext_Z2u // addi0.
apply exists_multu_seq.
repeat Reg_upd.
rewrite umul_0.
set s0 := store.multu_op _ _.
have [k Hk] : { k | u2Z [rk]_s0 - u2Z [a2]_s0 = Z_of_nat k}.
  have [k Hk] : { k | u2Z [rk]_s0 - u2Z [a2]_s0 = k} by eapply exist; reflexivity.
  have : 0 <= k.
    rewrite -Hk /s0. repeat Reg_upd. rewrite Z2uK // subZ0; exact: min_u2Z.
  case/Z_of_nat_complete_inf => k' H.
  exists k'; by rewrite -H.
move: k s0 Hk h.
elim.
- move=> s0 Hk h.
  eapply exist.
  apply while.exec_while_false.
  rewrite /= in Hk *.
  apply/negPn/eqP; lia.
- move=> k IH s0 Hk h.
  apply exists_while.
  + rewrite /=; apply/eqP; omegaz. (*rewrite Z_S in Hk; lia *)
  + apply exists_seq_P2 with (fun s => u2Z [rk]_(fst s) - u2Z [a2]_(fst s) = Z_of_nat k).
    * exists_lwxs l_m_ H_l_m_ z_m_ H_z_m_.
      apply exists_maddu_seq_P.
      repeat Reg_upd.
      exists_lwxs l Hl z Hz.
      apply exists_maddu_seq_P.
      repeat Reg_upd.
      apply exists_mflhxu_seq_P.
      exists_sw_P l' Hl' x' Hx'.
      repeat Reg_upd.
      apply exists_addiu_seq_P.
      repeat Reg_upd.
      apply exists_addiu_P.
      repeat Reg_upd.
      simpl.
      repeat Reg_upd.
      rewrite Z_S in Hk.
      rewrite sext_Z2u // u2Z_add_Z2u //; last first.
        move: (min_u2Z [a2]_s0) (min_u2Z [rk]_s0) (max_u2Z [a2]_s0) (max_u2Z [rk]_s0) => ? ? ? ?; lia.
      lia.
    * move=> [si hi] Hi.
      exact: IH.
Qed.

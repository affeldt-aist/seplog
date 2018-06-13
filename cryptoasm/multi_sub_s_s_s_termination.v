(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext seq_ext machine_int uniq_tac.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import multi_sub_s_s_s_prg pick_sign_termination.
Require Import multi_add_s_s_u_termination multi_sub_s_s_u_termination.
Require Import copy_s_s_termination.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma multi_sub_s_s_s_termination st h rz rx rk ry a0 a1 a2 a3 a4 ret rX rY rZ :
  uniq(rk, rz, rx, ry, a0, a1, a2, a3, a4, ret, rX, rY, rZ, r0) ->
  {s' | Some (st, h) -- multi_sub_s_s_s rk rz rx ry a0 a1 a2 a3 a4 ret rX rY rZ ---> s'}.
Proof.
move=> Hregs.
set c := multi_sub_s_s_s _ _ _ _ _ _ _ _ _ _ _ _ _.
have : {s' | (Some (st, h) -- c ---> s') /\ (forall s, s' = Some s -> True)}.
  rewrite /c /multi_sub_s_s_s.
  exists_lw ly Hly zy Hzy.
  apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
  have : uniq(ry, a0, a1, r0) by Uniq_uniq r0.
  case/(pick_sign_termination (store.upd rY zy st) h) => s1' h1'.
  by exists s1'.
  move=> [[s1 h1]|] H1; last first.
    exists None; split => //; by apply while.exec_none.
  apply exists_ifte_P.
    apply exists_ifte_P.
      apply exists_seq_P with (fun s => forall s', s = Some s' -> True).
        have : uniq(rk, rz, rx, a0, a1, a2, a3, a4, r0) by Uniq_uniq r0.
        case/(copy_s_s_termination s1 h1) => si hi.
        by exists si.
      move=> [[si hi]|] Hsi; last first.
        exists None; split => //.
        by apply while.exec_none.
      by apply exists_addiu_P.
    have : uniq(rk,rz,rx,rY,a0,a1,a2,a3,a4,ret,rX,rZ,r0) by Uniq_uniq r0.
    case/(multi_sub_s_s_u_termination s1 h1) => si hi.
    by exists si.
  have : uniq(rk,rz,rx,rY,a0,a1,a2,a3,a4,ret,rX,rZ,r0) by Uniq_uniq r0.
  case/(multi_add_s_s_u_termination s1 h1) => si hi.
   by exists si.
case=> s2 H2.
exists s2; tauto.
Qed.

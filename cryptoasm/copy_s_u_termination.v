(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ZArith_ext seq_ext machine_int uniq_tac.
Import MachineInt.
Require Import mips_cmd.
Import expr_m.
Require Import copy_s_u_prg multi_is_zero_u_termination copy_u_u_termination.
Require Import multi_zero_s_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma copy_s_u_termination st h rk ru rx a0 a1 a2 a3 :
  uniq(rk, ru, rx, a0, a1, a2, a3, r0) ->
  {si | Some (st, h) -- copy_s_u rk ru rx a0 a1 a2 a3 ---> si}.
Proof.
move=> Hregs.
rewrite /copy_s_u.
have : uniq(rk, rx, a0, a1, a2, r0) by Uniq_uniq r0.
case/(multi_is_zero_u_termination st h) => si Hsi.
apply constructive_indefinite_description.
apply exists_seq.
exists si; split => //.
apply constructive_indefinite_description'.
destruct si as [[si hi]|]; last first.
  exists None.
  by apply while.exec_none.
apply exists_ifte.
  (* TODO: multiply lemma to avoid this detour *)
  have : {s' : option (store.t * heap.t) |
   (Some (si, hi) --
    (lw a0 four16 ru ;
     copy_u_u_prg.copy_u_u rk a0 rx a1 a2 a3 ;
     sw rk zero16 ru) ---> s') /\ forall st, s' = Some st -> True}.
    exists_lw l_idx H_l_idx z_idx H_z_idx.
    have : uniq(rk, a0, rx, a1, a2, a3, r0) by Uniq_uniq r0.
    case/(copy_u_u_termination (store.upd a0 z_idx si) hi) => si2 Hsi2.
    apply exists_seq_P with (fun s => True).
      by exists si2.
    move=> [[si3 hi3]|] _.
    by exists_sw1 l2_idx H_l2_idx z2_idx H_z2_idx.
    exists None; split => //.
    by apply while.exec_none.
  case=> x Hx.
  exists x; tauto.
rewrite /multi_zero_s.
have : {s' | Some (si, hi) -- sw r0 zero16 ru ---> s' /\
   forall st, s' = Some st -> True}.
  by exists_sw1 l2_idx H_l2_idx z2_idx H_z2_idx.
case=> x Hx.
exists x; tauto.
Qed.

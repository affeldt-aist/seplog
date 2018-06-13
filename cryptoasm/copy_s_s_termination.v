(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ZArith_ext seq_ext machine_int uniq_tac.
Import MachineInt.
Require Import mips_cmd.
Import expr_m.
Require Import copy_s_s_prg copy_s_u_termination.
Require Import pick_sign_termination.
Require Import multi_zero_s_termination.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma copy_s_s_termination st h rk ru rx a0 a1 a2 a3 a4 :
  uniq(rk, ru, rx, a0, a1, a2, a3, a4, r0) ->
  {si | Some (st, h) -- copy_s_s rk ru rx a0 a1 a2 a3 a4 ---> si}.
Proof.
move=> Hregs.
rewrite /copy_s_s.
have : uniq(rx, a0, a1, r0) by Uniq_uniq r0.
case/(pick_sign_termination st h) => si Hsi.
destruct si as [[si hi]|]; last first.
  exists None.
  apply while.exec_seq with None => //; by apply while.exec_none.
apply constructive_indefinite_description.
eapply exists_seq.
eexists; split; first by apply Hsi.
apply constructive_indefinite_description'.
apply exists_ifte.
  by apply multi_zero_s_termination.
(* TODO: hen *)
set tmp := (fun s' : option (prod store.t heap.t) =>
      while.exec store.t heap.t cmd0 exec0 expr_b
        (fun (eb : expr_b) (st0 : prod store.t heap.t) =>
         eval_b eb (@fst store.t heap.t st0))
        (Some (si, hi))
        (@while.seq cmd0 expr_b (cmd_cmd0_coercion (lw a2 four16 rx))
           (@while.seq cmd0 expr_b
              (copy_s_u_prg.copy_s_u rk ru a2 a0 a1 a3 a4)
              (@while.seq cmd0 expr_b (cmd_cmd0_coercion (lw a0 zero16 rx))
                 (cmd_cmd0_coercion (sw a0 zero16 ru))))) s').
have : {s' | tmp s' /\ forall st, s' = Some st -> True}.
  rewrite /tmp {tmp}.
  exists_lw l H_l z H_z.
  apply exists_seq_P with (fun s => True).
    have : uniq(rk, ru, a2, a0, a1, a3, a4, r0) by Uniq_uniq r0.
    set s0 := store.upd _ _ _.
    case/(copy_s_u_termination s0 hi) => ? ?; by eexists; eauto.
  move=> [[si0 hi0]|] _; last first.
    exists None; split => //; exact/while.exec_none.
  exists_lw l0 H_l0 z0 H_z0.
  by exists_sw1 l_idx H_l_idx z_idx H_z_idx.
case=> s' Hs'; exists s'; tauto.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac machine_int.
Import MachineInt.
Require Import mips_cmd mips_tactics mips_contrib.
Import expr_m.
Require Import multi_is_zero_u_prg.

Local Open Scope machine_int_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope uniq_scope.

Lemma multi_is_zero_u_termination s h k z ext M_ ret :
  uniq(k, z, ext, M_, ret, r0) ->
  { si | Some (s, h) -- multi_is_zero_u k z ext M_ ret ---> si }.
Proof.
move=> Hregs.
rewrite /multi_is_zero_u.
apply exists_addiu_seq.
rewrite sext_Z2u // addi0.
apply exists_addiu_seq.
rewrite !store.get_r0 add0i.
set s0 := store.upd _ _ _.
(* TODO: factoriser cette etape dans les differentes preuves de terminaison? *)
have [kext Hkext] : { kext | u2Z [k]_s0 - u2Z [ext]_s0 = Z_of_nat kext}.
  have [kext Hkext] : { kext | u2Z [k]_s0 - u2Z [ext]_s0 = kext} by eapply exist; reflexivity.
  have : 0 <= kext. rewrite -Hkext /s0. repeat Reg_upd. rewrite Z2uK // subZ0; exact: min_u2Z.
  case/Z_of_nat_complete_inf => kext' H.
  exists kext'; by rewrite -H.
move: kext s0 Hkext h.
elim.
- move=> s0 Hkext h.
  eapply exist.
  apply while.exec_while_false.
  rewrite /= in Hkext *.
  apply/negPn/eqP; lia.
- move=> kext IH s0 Hext h.
  apply exists_while.
  + rewrite /=; apply/eqP; rewrite Z_S in Hext; lia.
  + apply exists_seq_P2 with (fun s => u2Z [k ]_ (fst s) - u2Z [ext ]_ (fst s) = Z_of_nat kext)%mips_expr.
    * exists_lwxs l_z H_l_z z_z H_z_z.
      exists_movn H.
      - apply exists_movn_false_seq_P => //.
        apply exists_addiu_P.
        simpl fst.
        repeat Reg_upd.
        rewrite Z_S in Hext.
        rewrite sext_Z2u // u2Z_add_Z2u //; first lia.
        move: (min_u2Z [k ]_ s0) (max_u2Z [k ]_ s0) (min_u2Z [ext ]_ s0) (max_u2Z [ext ]_ s0) => ? ? ? ?; lia.
      - apply exists_movn_true_seq_P => //.
        apply exists_addiu_P.
        simpl fst.
        repeat Reg_upd.
        rewrite Z_S in Hext.
        rewrite sext_Z2u // u2Z_add_Z2u //; first lia.
        move: (min_u2Z [k ]_ s0) (max_u2Z [k ]_ s0) (min_u2Z [ext ]_ s0) (max_u2Z [ext ]_ s0) => ? ? ? ?; lia.
    * move=> [si hi] Hsi; exact: IH.
Qed.

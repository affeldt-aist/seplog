(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon.
From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import ZArith_ext seq_ext.
Require Import machine_int multi_int encode_decode integral_type uniq_tac.
Import MachineInt.
Require Import mips_bipl mips_tactics mips_syntax.
Import mips_bipl.expr_m.
Require Import simu.
Import simu.simu_m.

(** turn "~ In _ (assoc.dom ?D)" into "~ In _ list_from_D" *)

Ltac Not_In_dom2list :=
  match goal with
    | |- ~ List.In _ (assoc.dom ?D) =>
      let hypo := fresh in
      assoc.From_dom_to_list hypo ;
      (* hypo: Permutation.Permutation (List.map fst list_from_D) (assoc.dom D) *)
      simpl seq.map in hypo ;
      apply (Permutation_notin hypo) ;
      clear hypo
    | |- ~ List.In _ (assoc.cdom ?CD) =>
      let hypo := fresh in
      assoc.From_cdom_to_list hypo ;
      (* hypo: Permutation.Permutation (List.map fst list_from_CD) (assoc.dom CD) *)
      simpl seq.map in hypo ;
      apply (Permutation_notin hypo) ;
      clear hypo
  end.

Ltac Notin_dom :=
  match goal with
      | |- is_true (?mx \notin assoc.dom ?M) =>
        apply/seq_ext.inP ;
        Not_In_dom2list ;
        by Uniq_not_In
  end.

Ltac Notin_cdom :=
  match goal with
      | |- is_true (?mx \notin assoc.cdom ?M) =>
        apply/seq_ext.inP ;
        Not_In_dom2list ;
        apply not_In_mint_ptr ;
        simpl mint_ptr ;
        rewrite [seq.map _ _]/= ;
        by Uniq_not_In
  end.

Ltac Disj_f_cdom2list K :=
  match goal with
    | |- seq_ext.disj _ (?f (assoc.cdom _)) =>
      let hypo := fresh in
      assoc.From_cdom_to_list hypo ;
      simpl seq.cat in hypo (* hypo: Permutation.Permutation list (assoc.cdom _) *) ;
      apply Permutation_mints_regs in hypo (* hypo: Permutation.Permutation (f list) (f (assoc.cdom _)) *) ;
      apply (Permutation_disj_R hypo) ;
      clear hypo ;
      simpl f
    | |- seq_ext.disj (?f (assoc.cdom _)) _ =>
      let hypo := fresh in
      assoc.From_cdom_to_list hypo ;
      simpl seq.cat in hypo (* hypo: Permutation.Permutation list (assoc.cdom _) *) ;
      apply Permutation_mints_regs in hypo (* hypo: Permutation.Permutation (f list) (f (assoc.cdom _)) *) ;
      apply (Permutation_disj_L hypo) ;
      clear hypo ;
      simpl f
  end.

Ltac Disj_mints_regs :=
  match goal with
    | |- disj (mints_regs (assoc.cdom ?D)) ?L =>
      Disj_f_cdom2list Permutation_mints_regs ;
      rewrite /mints_regs [seq.flatten _]/= ;
      Disj_remove_dup ;
      apply: uniq_disj ;
      simpl seq.cat ;
      by Uniq_uniq r0
    | |- disj ?L (mints_regs (assoc.cdom ?D)) =>
      Disj_f_cdom2list Permutation_mints_regs ;
      rewrite /mints_regs [seq.flatten _]/= ;
      Disj_remove_dup ;
      apply: uniq_disj ;
      simpl seq.cat ;
      by Uniq_uniq r0
  end.

Local Open Scope zarith_ext_scope.

Definition uv_bound rk s u v st k :=
  0 < u2Z ([rk ]_ s)%asm_expr < 2 ^^ 31 /\
  k = Z.abs_nat (u2Z ([rk ]_ s)%asm_expr) /\
  0 < ([u ]_ st)%pseudo_expr < Zbeta (k - 1) /\
  0 < ([v ]_ st)%pseudo_expr < Zbeta (k - 1).

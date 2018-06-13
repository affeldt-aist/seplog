(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import ZArith_ext String_ext ssrnat_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_expr_ground C_seplog C_pp.

Local Open Scope C_types_scope.
Local Open Scope string_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.

Module C_swap_env <: CENV.
Definition g := \wfctxt{ \O \}.
Definition sigma : g.-env := ("x", :* (ityp: uint)) :: ("y", :* (ityp: uint)) ::
                             ("z", g.-ityp: uint) :: ("v", g.-ityp: uint) :: nil.
Definition uniq_vars : uniq (unzip1 sigma) := Logic.eq_refl.
End C_swap_env.

Definition g := C_swap_env.g.
Definition sigma := C_swap_env.sigma.

Module Import C_Seplog_m := C_Pp_f C_swap_env.

Local Open Scope C_cmd_scope.

Definition swap :=
  "z" <-* %"x" ;
  "v" <-* %"y" ;
  %"x" *<- %"v" ;
  %"y" *<- %"z".

Definition mk_cell := log_of_uint (g.-ityp: uint) Logic.eq_refl.

Local Notation "a |~> b" := (a |le~> mk_cell b) (at level 77).

Lemma swap_correct (a b : int 32) :
  {{ %"x" |~> a ** %"y" |~> b }}
              swap
  {{ %"x" |~> b ** %"y" |~> a }}.
Proof.
rewrite /swap.
pose za := `! \b %"z" \= [ a ]pc.
Hoare_seq_ext za.
  Hoare_frame_idx_tmp (O :: nil) (O :: 1%nat :: nil).
  eapply hoare_stren; last by apply hoare_lookup_stren, ent_id.
  apply ent_R_lookup_trans with ([ a ]p) (mk_cell a).
    by rewrite /phylog_conv /=.
    by apply ent_R_con_T.
  Ent_R_subst_con_distr.
  do 2 Ent_R_subst_apply => /=.
  by Ent_monotony0.

pose vb := `! \b %"v" \= [ b ]pc.
  Hoare_seq_ext vb.
  Hoare_frame_idx_tmp (2%nat :: nil) (O :: 3%nat :: nil).
  eapply hoare_stren; last by apply hoare_lookup_stren, ent_id.
  apply ent_R_lookup_trans with ([ b ]p) (mk_cell b).
    by rewrite /phylog_conv /=.
    by apply ent_R_con_T.
  Ent_R_subst_con_distr.
  do 2 Ent_R_subst_apply => /=.
  by rewrite bbang_eq_exx coneP.

set Hx_old := %"x" |le~> mk_cell a.
pose Hx_new := %"x" |le~> mk_cell b.
Hoare_seq_replace1 Hx_old Hx_new.
  Hoare_frame_idx_tmp (O :: 2%nat :: nil) (O :: 2%nat :: nil).
  apply hoare_mutation_subst_btyp with (str := "v") (Hstr := Logic.eq_refl) (e' := [ b ]pc).
    rewrite /vb.
    Ent_R_rewrite_eq_e O.
    Ent_R_subst_con_distr.
    do 2 Ent_R_subst_apply.
   rewrite /Hx_old.
   rewrite bbang_eq_exx coneP; by apply ent_R_T.
  rewrite /=.
  Hoare_frame_idx_tmp (1%nat :: nil) (1%nat :: nil).
  rewrite /Hx_old /Hx_new.
  set bpc := [ b ]pc.
  have He2 : vars bpc = nil by done.
  apply hoare_mutation_local_forward_ground_le with (He2 := He2); by rewrite/phylog_conv /=.

rewrite -/Hx_new.
set Hy_old := %"y" |le~> _.
set Hy_new := %"y" |le~> _.
Hoare_frame (vb :: za :: Hy_old :: nil) (Hy_new :: nil).
apply hoare_mutation_subst_btyp with (str := "z") (Hstr := Logic.eq_refl) (e' := [ a ]pc).
  rewrite /za.
  Ent_R_rewrite_eq_e O.
  Ent_R_subst_con_distr.
  do 2 Ent_R_subst_apply.
  rewrite bbang_eq_exx coneP; by apply ent_R_T.
rewrite /=.
Hoare_L_contract_bbang vb.
Hoare_L_contract_bbang za.
set apc := [ a ]pc.
have He2 : vars apc = nil by done.
apply hoare_mutation_local_forward_ground_le with (He2 := He2); by rewrite/phylog_conv /=.
Qed.

Eval compute in pp_ctxt.
Eval compute in (foldl
  (fun s p => s ++ typ_to_string (Ctyp.ty _ (snd p)) (fst p) (line ";"))
  "" sigma).
Eval compute in (pp_cmd 0 swap "").

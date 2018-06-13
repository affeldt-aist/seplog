(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
Require Import Init_ext ZArith_ext String_ext seq_ext.
Require Import ssrnat_ext seq_ext littleop.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_expr_equiv C_expr_ground C_seplog C_tactics.
Require Import C_reverse_list_header.
Import C_Seplog_m.

Local Open Scope string_scope.
Local Open Scope C_types_scope.
Local Open Scope C_value_scope.
Local Open Scope C_expr_scope.
Local Open Scope C_cmd_scope.

Lemma wp_assign_seplogClst_e str {t : g.-typ} (str_t : env_get str sigma = |_ t _|)
  (e' : exp sigma t) (e : exp sigma (:* Clst)) l :
  wp_assign str_t e' (seplogClst_e l e) <==> seplogClst_e l (subst_exp str str_t e' e).
Proof.
rewrite /seplogClst_e.
move => s h /=; split => [ | H].
- inversion_clear 1.
  move/(seplogClst_inde _ _ _ s) in H0.
  by rewrite -subst_exp_store_upd in H0.
- constructor.
  apply seplogClst_inde with s.
  by rewrite -subst_exp_store_upd.
Qed.

Lemma list_inv e l : seplogClst_e l e <==>
  (`! \b e \= NULL ** !!(l = nil)) \\//
  sepex hd, sepex tl, sepex next,
     `! \~b \b e \= NULL ** !!(l = hd :: tl) **
     e |le~> mk_cell hd (ptr<=phy next) ** seplogClst_e tl [ next ]c.
Proof.
move => s h; split.
- inversion 1; subst; clear H.
  + left.
    apply con_and_bang_R; split => //.
    split=> //.
    by rewrite beval_eq_p_eq -H2.
  + right.
    exists h0, t, p.
    apply conC, con_and_bang_R; split => //.
    rewrite -(hp.unioneh (h1 \U h2)).
    constructor => //.
    by map_tac_m.Disj.
    rewrite beval_neg_not beval_eq_p_eq; by apply/eqP.
- case.
  + case => h1 h2 h1h2 H1 H2.
    rewrite (proj1 H2) (proj2 H2) (proj2 H1) /seplogClst_e.
    case: H1 => H0 _.
    rewrite beval_eq_p_eq in H0.
    move/eqP in H0.
    rewrite H0 /= hp.unioneh.
    by constructor.
  + case => hd [] tl [] next.
    case => h1 h2 h1h2 H1.
    case => h21 h22 h21h22 H21.
    case => h31 h32 h31h32 H31 H32.
    rewrite (proj1 H21) (proj2 H21) (proj2 H1) !hp.unioneh.
    eapply list_cons.
    * by Disj.
    * case: H1 => e_0 _.
      rewrite beval_neg_not beval_eq_p_eq in e_0.
      by apply/eqP.
    * by apply H31.
    * done.
Qed.  

Lemma list_empty e : `! \b e \= NULL <==> seplogClst_e nil e.
Proof.
move => s h; split => [|H].
- case => H0 ->.
  rewrite beval_eq_p_eq in H0.
  move/eqP in H0.
  rewrite /seplogClst_e H0.
  by constructor.
- inversion H; subst; clear H.
  split; last by done.
  by rewrite beval_eq_p_eq -H0.
Qed.

Lemma list_suiv e l : (sepex hd, sepex tl, sepex next,
    `! \~b \b e \= NULL **
    !!(l = hd :: tl) ** (fun s h => (e |le~> mk_cell hd (ptr<=phy ([next]_ s))) s h) **
    seplogClst_e tl next) ===>  
  seplogClst_e l e.
Proof.
move => s h [] hd [] tl [] next.
case => h1 h2 h1h2 H1.
case => h21 h22 h21h21 H21.
case => h31 h32 h31h32 H31 H32.
rewrite /pure in H21; case: H21 => ? ?; subst.
rewrite /bbang /bang in H1.
case: H1 => H1 H0.
rewrite /emp in H0; subst h1.
rewrite !hp.unioneh /seplogClst_e.
econstructor => //=.
- rewrite beval_neg_not beval_eq_p_eq in H1; by apply/eqP.
- by apply H31.
- assumption.
Qed.

Local Open Scope nat_scope.

Lemma reverse_list_correct l :
  {{ seplogClst_e l __i }} reverse_list {{ seplogClst_e (rev l) __ret }}.
Proof.
rewrite /reverse_list.

(* "ret" <- NULL ; *)

apply hoare_assign_seq_stren with (seplogClst_e l __i ** `! \b __ret \= NULL).
  Ent_R_subst_con_distr.
  rewrite wp_assign_seplogClst_e /=.
  Ent_LR_subst_apply.
  rewrite bbang_eqpxx.
  rewrite conPe.
  by apply ent_id.

(* While \~b \b "i" \= NULL {{ *)

apply hoare_while_invariant_bang with (sepex l1, sepex l2, 
    !!(l = l1 ++ l2)%SEQ ** seplogClst_e (rev l1) __ret ** seplogClst_e l2 __i).
  - Ent_R_ex (@nil (int 32)).
    Ent_R_ex l.
    rewrite sbang_emp // coneP -list_empty.
    by Ent_permut.
  - Ent_L_ex l1.
    Ent_L_ex l2.
    Ent_L_sbang_all => ?; subst l.
    rewrite bnegK rev_cat (list_inv _ l2).
    Ent_L_or 0.
    + Ent_L_sbang_all => ?; subst l2 => /=.
      Ent_monotony.
      by do 2 Ent_L_contract_bbang 0.
    + Ent_L_ex h.
      Ent_L_ex t.
      Ent_L_ex next.
      Ent_L_sbang_all => ?; subst l2.
      by Ent_L_contradict_idx (0 :: 4 :: nil).

(* "rem" <-* "i" .-> next; *)

apply hoare_seq with (sepex l1, sepex hd, sepex l2, 
  !!(l = l1 ++ (hd :: l2))%SEQ ** 
  `! \~b \b __i \= NULL **
  seplogClst_e (rev l1) __ret **
  (fun s h => ([ __i ]_s  |lV~> mk_cell hd (ptr<=phy [ __rem ]_ s)) s h) **
  seplogClst_e l2 __rem).

  apply hoare_lookup_fldp_stren.
  Ent_L_ex l1.
  Ent_L_ex l2.
  Ent_L_sbang_all => ?; subst l.
  rewrite (list_inv _ l2).
  Ent_L_or 0.
  - by Ent_L_contradict_idx (0 :: 3 :: nil).
  - Ent_L_ex h.
    Ent_L_ex t.
    Ent_L_ex next.
    Ent_L_sbang_all => ?; subst l2.
    rewrite wp_lookup_fldp_ex; Ent_R_ex l1.
    rewrite wp_lookup_fldp_ex; Ent_R_ex h.
    rewrite wp_lookup_fldp_ex; Ent_R_ex t.
    apply ent_R_lookup_fldp_trans with (pv := next) (lvs := list_header h (ptr<=phy next)).
    + set imapsto := __i |le~> _.
      by Ent_monotony.
    + by rewrite /= -Eqdep.Eq_rect_eq.eq_rect_eq /phylog_conv /= ptr_of_phyK.
    + Ent_R_subst_con_distr.
      rewrite wp_assign_seplogClst_e /= wp_assign_seplogClst_e /=. 
      do 2 Ent_R_subst_apply.
      rewrite sbang_emp // coneP -/__ret.
      set Hnext := seplogClst_e _ _.
      Ent_monotony.
      rewrite (@wp_assign_store_upd _rem _ Logic.eq_refl [ next ]c).
      rewrite -> ent_bbang_contract.
      rewrite conPe.
      move=> s' h' imapsto /=.
      rewrite -2!subst_exp_store_upd /=.
      exact imapsto.

(* %"i" .-> next *<- %"ret" *)

apply hoare_seq with (sepex l1, sepex hd, sepex l2, 
    !!(l = l1 ++ (hd :: l2))%SEQ ** 
    `! \~b \b __i \= NULL **
    seplogClst_e (rev l1) __ret **
    (fun s h => ([ __i ]_s |lV~> mk_cell hd (ptr<=phy [ __ret ]_s )) s h) **
    seplogClst_e l2 (__rem )).
  Hoare_L_ex 0 l1.
  Hoare_L_ex 0 h_.
  Hoare_L_ex 0 l2.
  Hoare_L_sbang 0 => Hl.
  Hoare_R_ex 0 l1.
  Hoare_R_ex 0 h_.
  Hoare_R_ex 0 l2.
  Hoare_R_sbang 0; first by exact Hl.
  Hoare_frame_idx_tmp (2 :: nil) (2 :: nil).
  (* TODO: tactic to replace an expression by an existential constant *)
  apply hoare_stren with (sepex k, 
    (fun s h => k = [ __rem ]_ s /\ ([ __i ]_s  |lV~> mk_cell h_ (ptr<=phy [__rem]_s)) s h)).
    move => s h H; by exists ([ __rem ]_s).
  Hoare_L_ex 0 k.
  apply hoare_stren with (fun s h => ([ __i ]_s |lV~> mk_cell h_ (ptr<=phy k)) s h).
    by move => s h /= [] ->.
  eapply hoare_weak; last by apply hoare_mutation_fldp_local_forward.
  move=> s h /= H.
  have : [ __ret ]_ s |x| log_of_ptr _ _ Logic.eq_refl (ptr<=phy ([ __ret ]_ s)).
    by rewrite /phylog_conv /= ptr_of_phyK.
  move/H => {H}.
  by rewrite -Eqdep.Eq_rect_eq.eq_rect_eq.

(* "ret" <- "i"; *)

apply hoare_seq with (sepex l1, sepex hd, sepex l2, 
  !!(l = l1 ++ (hd :: l2))%SEQ **  `! \~b \b __i \= NULL **
  seplogClst_e (rev (rcons l1 hd)) __ret ** seplogClst_e l2 __rem).
  Hoare_L_ex 0 l1.
  Hoare_L_ex 0 h_.
  Hoare_L_ex 0 l2.
  Hoare_L_sbang 0 => Hl.
  Hoare_R_ex 0 l1.
  Hoare_R_ex 0 h_.
  Hoare_R_ex 0 l2.
  Hoare_R_sbang 0; first by exact Hl.
  set lhs := fun s h => log_mapsto _ _ _.
  apply hoare_assign_stren.
  Ent_R_subst_con_distr.
  rewrite 2!wp_assign_seplogClst_e /=.
  Ent_LR_subst_apply.
  rewrite -/__rem rev_rcons.
  rewrite <- (list_suiv __i (h_ :: rev l1)).
  Ent_R_ex h_.
  Ent_R_ex (rev l1).
  Ent_R_ex __ret.
  rewrite -/lhs sbang_emp // coneP.
  set b := \~b _.
  rewrite -> (bbang_dup b) at 1.
  Ent_permut.

(* "i" <- "rem" *)

Hoare_L_ex 0 l1.
Hoare_L_ex 0 h_.
Hoare_L_ex 0 l2.
Hoare_L_sbang 0 => Hl.
Hoare_R_ex 0 (rcons l1 h_).
Hoare_R_ex 0 l2.
Hoare_R_sbang 0; first by rewrite cat_rcons.
apply hoare_assign_stren.
Ent_R_subst_con_distr.
rewrite 2!wp_assign_seplogClst_e /=.
rewrite -> ent_bbang_contract.
by Ent_monotony.
Qed.

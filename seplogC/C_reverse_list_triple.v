(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq tuple.
Require Import ZArith_ext String_ext ssrnat_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_seplog.
Require Import C_reverse_list_header.
Import C_Seplog_m.

Local Open Scope string_scope.
Local Open Scope C_types_scope.
Local Open Scope C_value_scope.
Local Open Scope C_cmd_scope.

(** reverse_list using lemmas from the library (no tactics) *)

Lemma reverse_list_correct l :
  {{ seplogClst_e l  __i }} reverse_list {{ seplogClst_e (rev l) __ret }}.
Proof.
rewrite /reverse_list.

(** << _ret <- NULL; >> *)

apply hoare_assign_seq_stren with (fun s h => seplogClst l ([ __i ]_ s) s h /\ [ __ret ]_s = pv0).
  move=> s h H.
  apply wp_assign_c.
  rewrite eval_store_upd_notin //.
  split; first by move: H; apply seplogClst_inde.
  by rewrite -subst_exp_store_upd.

(** << While \~b \b __i \= NULL {{ >> *)

apply hoare_while_invariant with (fun s h => exists l1 l2, l = (l1 ++ l2)%SEQ /\
  (seplogClst (rev l1) [ __ret ]_s ** seplogClst l2 [ __i ]_s) s h).
  - move=> s h H.
    exists nil, l => /=.
    split => //.
    case: H => /= H Hret.
    rewrite -(hp.unioneh h).
    apply con_c => //.
    + by Disj.
    + rewrite Hret; by constructor. 
  - move=> s h [] [l1 [l2 [Hl Hmem]]].
    rewrite /C_definition.eval_b /C_StateBipl.eval_b /= beval_neg_not negbK beval_eq_p_eq.
    move/eqP => H.
    rewrite H in Hmem.
    case: Hmem => h1 h2 h1h2 H1 H2.
    inversion H2; clear H2; last by done.
    subst.
    by rewrite cats0 hp.unionhe.

(** << _rem <-* __i &-> _next; >> *)

apply hoare_seq with (fun s h => exists l1 hd l2, l = cat l1 (hd :: l2) /\
    [ __i ]_ s <> pv0 /\ (seplogClst (rev l1) ([ __ret ]_s) ** 
      ([ __i ]_s |lV~> mk_cell hd (ptr<=phy [ __rem ]_s)) **
      seplogClst l2 [ __rem ]_s) s h).
  apply hoare_lookup_fldp_stren => s h [] [] l1 [] l2 [] Hl Hh.
  rewrite /C_Semop0.eval_b /C_StateBipl.eval_b beval_neg_not => /negP H.
  have {H}H' : [ __i ]_s <> pv0.
    move => H'; apply H => {H} /=.
    Transparent beval eval.
    simpl. simpl in H'. rewrite H' eq_refl.
    Opaque beval eval.
    by apply not_is_zero_1.
  case: Hh => h1 h2 h1h2 H1 H2.
  move: H1; set i := [%"i"]_s => H1.
  inversion H2; subst; clear H2; first by rewrite H3 in H'.
  apply mkWpLookupFldpConv with (pv := p) (lvs := list_header h0 (ptr<=phy p)) (lv := log_of_ptr _ _ erefl (ptr<=phy p)).
  - by rewrite /= -Eqdep.Eq_rect_eq.eq_rect_eq.
  - by rewrite /phylog_conv /= ptr_of_phyK.
  - split.
    + rewrite (_ : h1 \U (h3 \U h4) = h3 \U (h1 \U h4)); last by Equal.
      apply con_c => //.
      rewrite hp.unionC //; by Disj.                       
    + apply wp_assign_c.
      exists l1, h0, t.
      split => //.
      split; first by rewrite eval_store_upd_notin.
      apply con_c => //.
      - rewrite eval_store_upd_notin //.
        by eapply seplogClst_inde; eauto.
      - rewrite -subst_exp_store_upd /=.
        apply con_c => //. 
        by rewrite eval_store_upd_notin.
        by eapply seplogClst_inde; eauto.

(** << __i &-> _next *<- __ret; >> *)

apply hoare_seq with (fun s h => exists l1 hd l2, l = (l1 ++ (hd :: l2))%SEQ /\
    [ __i ]_ s <> pv0 /\
    (seplogClst (rev (rcons l1 hd)) ([ __i ]_s) ** seplogClst l2 ([ __rem ]_s)) s h).
  apply hoare_L_ex => l1.
  apply hoare_L_ex => hd.
  apply hoare_L_ex => l2.
  apply hoare_R_ex; exists l1.
  apply hoare_R_ex; exists hd.
  apply hoare_R_ex; exists l2.
  apply hoare_pure_left; first by done.
  split; first by done.
  set c := __i &-> _next *<- __ret.
  set R := seplogClst_e l2 __rem.
  set P := fun s h => [ __i ]_ s <> pv0 /\
    (seplogClst (rev l1) [ __ret ]_ s ** [ __i ]_ s |lV~> mk_cell hd (ptr<=phy [ __rem ]_ s)) s h.
  set Q := fun s h => [ __i ]_ s <> pv0 /\ (seplogClst (rev (rcons l1 hd)) [ __i ]_ s) s h.
  suff PcQ : {{ P }} c {{ Q }}.
    have inde_R : inde_cmd c R by done.
    eapply hoare_conseq; last first.
    - by apply (frame_rule_R _ _ _ PcQ _ inde_R).
    - rewrite /P /R => s h /= [] Hneq H.
      case: H => h1 h2 h1h2 H1 H2.
      case: H2 h1h2 => h21 h22 h21h22 H21 H22 h1h2.
      rewrite (_ : h1 \U (h21 \U h22) = (h1 \U h21) \U h22); last by Equal.
      apply con_c => //; first by Disj.
      split => //.
      apply con_c => //; by Disj.                       
    - rewrite /Q /R => s h //= H.
      case: H => h1 h2 h1h2 [] H11 H12 H2.
      by econstructor.
  rewrite /P /Q {P Q R}.
  apply hoare_weak with (fun s h => [ __i ]_ s <> pv0 /\  
    ([ __i ]_ s |lV~> mk_cell hd (ptr<=phy [ __ret ]_ s) ** seplogClst (rev l1) [ __ret ]_ s ) s h ).
    move => s h //= [] Hneq.
    case=> h1 h2 h1h2 H1 H2.
    split; first by done.
    rewrite rev_rcons.
    econstructor => //=.
    by apply H1.
    exact H2.
  eapply hoare_stren with (fun s h => [ __i ]_ s <> pv0 /\  
    ([ __i ]_ s |lV~> mk_cell hd (ptr<=phy [ __rem ]_ s) ** seplogClst (rev l1) [ __ret ]_ s ) s h).
    move => s h //= [] Hneq H.
    inversion H; subst; clear H.
    split; first by done.
    rewrite hp.unionC; last by Disj.
    constructor => //; first by Disj.
  set P := fun s h => [ __i ]_ s <> pv0 /\ ([ __i ]_ s |lV~> mk_cell hd (ptr<=phy [ __rem ]_ s)) s h.
  set Q := fun s h => [ __i ]_ s <> pv0 /\ ([ __i ]_ s |lV~> mk_cell hd (ptr<=phy [ __ret ]_ s)) s h.
  set R := fun s h => [ __i ]_ s <> pv0 /\ (seplogClst (rev l1) [ __ret ]_ s) s h.
  suff PcQ : {{ P }} c {{ Q }}.
    have inde_R : inde_cmd c R by done.
    eapply hoare_conseq; last first.
      by apply (frame_rule_R _ _ _ PcQ _ inde_R).
      rewrite /P /R => s h //= [] Hneq [] h1 h2 h1h2 H1 H2.
      by econstructor.
    rewrite /Q /R  => s h //= [] h1 h2 h1h2 [] H11 H12 [] H21 H22.
    by econstructor.
  rewrite /P /Q {P Q R} /mk_cell.
  apply hoare_and_left.
    move => s h s' h' Hc.
    suff : [ __i ]_s = [ __i ]_s' by move=> ->.
    (* NB: tactic by reflection *)
    inversion Hc; subst; clear Hc.
    by inversion H1; subst; clear H1.
  apply hoare_stren with (fun s h => exists k, k = [ __rem ]_ s /\
    ([ __i ]_ s |lV~> log_of_styp Clst _ Logic.eq_refl (list_header hd (ptr<=phy [ __rem ]_ s))) s h).
    move => s h /= H; by exists ([ __rem ]_ s).
  apply hoare_L_ex => k.
  apply hoare_stren with (fun s h =>
     ([ __i ]_ s |lV~> log_of_styp Clst _ Logic.eq_refl (list_header hd (ptr<=phy k))) s h).
    by move => s h /= [] ->.
  eapply hoare_weak; last by apply hoare_mutation_fldp_local_forward.
  move=> s h /= H.
  have : [ __ret ]_ s |x| (log_of_ptr _ _ erefl (ptr<=phy ([ __ret ]_ s))).
    by rewrite /phylog_conv /= ptr_of_phyK.
  move/(H _).
  by rewrite -Eqdep.Eq_rect_eq.eq_rect_eq.

(** << _ret <- __i >> *)

apply hoare_seq with (fun s h =>
  exists l1 hd l2, l = (l1 ++ (hd :: l2))%list /\
    (seplogClst (rev (rcons l1 hd)) ([ __ret ]_s) ** seplogClst l2 ([ __rem ]_s)) s h).
  apply hoare_assign_stren => s h [] l1 [] hd [] l2 [] Hl [] Heq.
  case => h1 h2 h1h2 H1 H2.
  apply wp_assign_c.
  exists l1, hd, l2.
  split; first by done.
  apply con_c => //; rewrite -subst_exp_store_upd /=; eapply seplogClst_inde; eauto.

(** << _i <- __rem >> *)

apply hoare_assign_stren => s h [] l1 [] hd [] l2 [] Hl.
case => h1 h2 h1h2 H1 H2.
apply wp_assign_c.
exists (rcons l1 hd), l2.
split; first by rewrite cat_rcons.
apply con_c => //; rewrite -subst_exp_store_upd /=; eapply seplogClst_inde; eauto.
Qed.

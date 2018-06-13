(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import div.
Require Import Init_ext ssrZ ZArith_ext String_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_expr_equiv C_expr_ground.
Require Import C_seplog.

Local Open Scope C_types_scope.
Local Open Scope C_expr_scope.
Local Open Scope machine_int_scope.

Require Import while_bipl.
From mathcomp Require Import seq.

Module C_Contrib_f (C_Env : CENV).

Definition g := C_Env.g.
Definition sigma := C_Env.sigma.

Module Import C_seplog_m := C_Seplog_f C_Env.
Export C_seplog_m.

Local Open Scope C_types_scope.

Local Open Scope zarith_ext_scope.

(** wp_assign *)

Set Implicit Arguments.
Unset Strict Implicit.

Section wp_assign_sect.

Variable (str : string) (t : g.-typ).
Hypothesis str_t : assoc_get str sigma = |_ t _|.

Lemma wp_assign_con e P0 P1 : wp_assign str_t e (P0 ** P1) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1.
Proof.
move => s h; split.
- inversion 1; subst; clear H.
  inversion H0; subst; clear H0.
  by constructor.
- inversion 1; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H2; subst; clear H2.
  by constructor.
Qed.

Lemma wp_assign_assert (e' : exp sigma t) {t' : g.-typ} (e : exp sigma t') P :
  wp_assign str_t e' (fun s h => P ([ e ]_ s) h) <==>
  (fun s h => P ([subst_exp str str_t e' e]_ s) h).
Proof.
move=> s h; split.
- inversion_clear 1.
  by rewrite -subst_exp_store_upd in H0.
- move=> H; apply wp_assign_c.
  by rewrite -subst_exp_store_upd.
Qed.

Lemma wp_assign_bbang (e' : exp sigma t) (b : bexp sigma) :
  wp_assign str_t e' (`! b) <==> `! @subst_bexp g _ str t str_t e' b.
Proof.
rewrite /bbang /bang => s h; split.
- inversion_clear 1.
  case: H0 => H1 H2; split => //.
  rewrite subst_bexp_store_upd; tauto.
- case => H1 H2.
  apply wp_assign_c; split=> //.
  by rewrite -subst_bexp_store_upd.
Qed.

Lemma wp_assign_sbang e P : wp_assign str_t e (!!( P )) <==> !!( P ).
Proof. move => s h; split=> //; by inversion 1. Qed.

Lemma wp_assign_emp e : wp_assign str_t e emp <==> emp.
Proof. move => s h; split => //; by inversion 1. Qed.

Lemma wp_assign_T e : wp_assign str_t e TT <==> TT.
Proof. done. Qed.

Lemma wp_assign_F e : wp_assign str_t e FF <==> FF.
Proof. move=> s h; split; by [case=> {s h} s h [] | case]. Qed.

Lemma wp_assign_ex (e : exp sigma t) {A} (P : A -> assert) :
  (wp_assign str_t e (sepex x, P x)) <==> sepex y, wp_assign str_t e (P y).
Proof.
move=> s h; split.
- inversion_clear 1.
  inversion_clear H0.
  exists x; constructor; tauto.
- inversion_clear 1.
  inversion_clear H0.
  constructor.
  by exists x.
Qed.

Lemma wp_assign_mapsto_le (e : exp sigma t) {t' : Ctyp.t g} (e' : exp sigma (:* t')) (val : log t'):
  wp_assign str_t e (e' |le~> val) <==> subst_exp str str_t e e' |le~> val.
Proof.
move => s h; split.
- inversion_clear 1.
  by rewrite -subst_exp_store_upd in H0.
- econstructor.
  by rewrite -subst_exp_store_upd.
Qed.

Lemma wp_assign_mapsto_lV (e : exp sigma t) {t' : g.-typ} (e' : (:* t').-phy) (val : log t') :
  wp_assign str_t e (e' |lV~> val) <==> e' |lV~> val.
Proof.
move => s h; split.
- by inversion_clear 1.
- by constructor.
Qed.

Lemma wp_assign_mapstos (e : exp sigma t) {t': g.-typ} : forall  (l : seq (t'.-phy)) (e' : exp _ (:* t')),
  (wp_assign str_t e (e' |--> l)) <==> (subst_exp str str_t e e') |--> l.
Proof.
elim => //=.
- by move => e'; rewrite wp_assign_emp.
- move => hd tl Hind e' s h; split.
  + inversion_clear 1.
    inversion H0; subst; clear H0.
    rewrite -subst_exp_store_upd in H1.
    constructor => //=.
    rewrite (_ : subst_exp str str_t e e' \+ [ 1 ]sc = subst_exp str str_t e (e' \+ [ 1 ]sc)) //.
    apply (proj1 (Hind _ s h2)).
    by constructor.
  + econstructor.
    inversion H; subst; clear H.
    constructor => //=.
      by rewrite -subst_exp_store_upd.
    rewrite (_ : _ \+ _ = subst_exp str str_t e (e' \+ [ 1 ]sc)) // in H2.
    move: (proj2 (Hind _ s h2) H2).
    by inversion_clear 1.
Qed.

Lemma wp_assign_fit (e : exp sigma t) (ty' : g.-typ) (l : seq (ty'.-phy)) (e' : exp sigma (:* ty')) :
   wp_assign str_t e !(fun s =>
     (u2Z (ptr<=phy [ e' ]_s) + Z_of_nat (sizeof ty' * size l) <
     2 ^^ ptr_len)%Z) <==>
   !(fun s => (u2Z (ptr<=phy [ subst_exp str str_t e e' ]_s) +
              Z_of_nat (sizeof ty' * size l) < 2 ^^ ptr_len)%Z).
Proof.
move=> s h; split.
  case=> s' h' [] H; rewrite /emp => ?; subst h'.
  split => //.
  by rewrite subst_exp_store_upd.
case=> H; rewrite /emp => ?; subst h.
apply wp_assign_c; split => //.
by rewrite -subst_exp_store_upd.
Qed.

Lemma wp_assign_mapstos_fit (e : exp sigma t) {t' : g.-typ} :
  forall (l : seq (t'.-phy)) (e': exp _ (:* t')),
    wp_assign str_t e (e' |---> l) <==> (subst_exp str str_t e e') |---> l.
Proof.
move=> l e'.
rewrite /mapstos_fit wp_assign_con wp_assign_mapstos.
apply con_congr => //.
apply wp_assign_fit.
Qed.

Lemma wp_assign_store_upd (e : exp sigma t) (Q : assert) :
  wp_assign str_t e Q <==> (fun s h => Q (store_upd str_t ([ e ]_s) s) h).
Proof.
move => s h; split.
by inversion_clear 1.
by constructor.
Qed.

Lemma wp_assign_or e P Q :
  wp_assign str_t e (P \\// Q) <==> wp_assign str_t e P \\// wp_assign str_t e Q.
Proof.
move => s h; split.
- inversion 1; subst; clear H.
  inversion_clear H0; by [left | right].
- inversion 1; inversion H0; subst; clear H; constructor; [by left | by right].
Qed.

Lemma wp_assign_inde e P : inde_cmd (assign str_t e) P -> wp_assign str_t e P <==> P.
Proof.
move => Hinde s h.
have Hin : (str, t) \in modified_vars (assign str_t e) by rewrite in_cons eq_refl.
split.
- inversion_clear 1.
  apply (Hinde s h str t ([ e ]_ s) Hin).
  set X := assoc_get_subset_in _ _ _.
  by have -> : X = str_t by apply eq_irrelevance.
- constructor.
  move: (proj1 (Hinde s h str t ([ e ]_ s) Hin) H).
  set X := assoc_get_subset_in _ _ _.
  by have -> : X = str_t by apply eq_irrelevance.
Qed.

End wp_assign_sect.

Unset Implicit Arguments.
Set Strict Implicit.

(** lookup for fields *)

Section wp_lookup_sect.

Variables (t : g.-typ) (str : string).
Hypothesis str_t : env_get str sigma = |_ :* t _|.
Variable e'' : exp sigma (:* t).
Variable (t' : g.-typ) (str' : string).
Hypothesis str't : env_get str' sigma = |_ t' _|.
Variable tg : tag.
Hypothesis t'tg : styp tg = t.
Variable fld : string.
Hypothesis fld_t' : assoc_get fld (get_fields g tg) = |_ t' _|.
Variable e : exp sigma (:* t).

Lemma hoare_lookup_fldp_subst P Q :
  P ===> (`! \b var_e _ _ (:* t) str_t \= e'' ) ** TT ->
  {{ P }} lookup str't (fldp _ fld (subst_exp _ str_t e'' e) t'tg fld_t') {{ Q }} ->
  {{ P }} lookup str't (fldp _ fld e t'tg fld_t') {{ Q }}.
Proof.
Transparent eval.
move=> HP Hoare.
apply hoare_complete => s h HPsh.
case: (soundness _ _ _ Hoare s h HPsh) => Hsem1 Hsem2.
have He': forall e', [subst_exp str str_t e'' e']_ s = [e']_ s.
  move => c e'.
  rewrite subst_exp_store_upd.
  have : (`! \b var_e _ _ _ str_t \= e'') s hp.emp.
    move: (HP _ _ HPsh) => H'.
    inversion H'; subst; clear H'.
    split; last by done.
    by apply (proj1 H0).
  move/bbang_eqp_store_get => <-.
  by rewrite store_upd_get_eq.
split.
- move => H'.
  apply Hsem1.
  inversion_clear H'.
  inversion H; subst; clear H.
  apply exec_cmd0, exec_lookup_err => //=.
  rewrite /a in H1.
  apply Eqdep.EqdepTheory.inj_pair2 in H5; subst e1.
  rewrite He'; exact H1.
- move => s' h' Hsem.
  apply Hsem2.
  inversion_clear Hsem.
  inversion H; subst; clear H.
  rewrite /a in H1.
  apply Eqdep.EqdepTheory.inj_pair2 in H5; subst e1.
  (have: Hstr0 = str't by apply eq_irrelevance) => ?; subst Hstr0.
  (have: Hstr1 = str't by apply eq_irrelevance) => ?; subst Hstr1.
  apply exec_cmd0, exec_lookup => //=.
  rewrite He'; exact H1.
Opaque eval.
Qed.

End wp_lookup_sect.

CoInductive wp_lookup_fldp
  str {t' : g.-typ} (str_t' : assoc_get str sigma = Some t')
  {t : g.-typ} (e : exp sigma (:* t)) tg (tgt : styp tg = t)
  f (f_t : assoc_get f (get_fields g tg) = Some t')
  (P : assert) : assert :=
| mkWpLookupFldpConv : forall s h (lvs : logs _) (pv : _.-phy) (lv : _.-log),
    values_get f _ _ lvs (assoc_get_in f_t) = lv ->
    pv |x| lv ->
    ([e]_ s |lV~> log_of_styp _ _ tgt lvs ** TT) s h /\
    (wp_assign str_t' [ pv ]c P) s h ->
    wp_lookup_fldp _ str_t' e _ tgt _ f_t P s h.

Notation "P '`{' x '<-' e '.->' f '}''" := (wp_lookup_fldp x _ e _ _ f _ P) (at level 5, x, e at next level, format "'[hv ' P  '/  ' `{  x  <-  e  .->  f }' ']'") : C_assert_scope.

Notation "P '`{' x '<-' e '.->' f '}''" := (wp_lookup_fldp x erefl e _ erefl f erefl P) (at level 5, x, e at next level, format "'[hv ' P  '/  ' `{  x  <-  e  .->  f }' ']'", only parsing) : C_assert_scope.

Section ent_R_lookup_trans_sect.

Variable str : string.
Variable t : g.-typ.
Hypothesis str_t : assoc_get str sigma = Some t.
Variable e : exp sigma (:* t).

Lemma ent_R_lookup_trans (pv : t.-phy) (lv : t.-log) (P R : assert) :
  pv |x| lv ->
  R ===> (e |le~> lv) ** TT ->
  R ===> wp_assign str_t [ pv ]c P ->
  R ===> wp_lookup str_t e P.
Proof.
move=> pv_lv H' H s h Hh.
move: (H' _ _ Hh) => {H'}H'.
case: H' Hh => h1 h2 h1dh2 H1 H2 Hh.
rewrite /phylog_conv in pv_lv.
move/log_mapsto_heap_get_conv : (H1).
move/(_ _ pv_lv) => H1'.
apply wp_lookup_c with pv.
  by apply heap_get_value_union_L.
by case: (H _ _ Hh).
Qed.

End ent_R_lookup_trans_sect.

Section wp_lookup_fldp_sect.

Variable str : string.
Variable t' : g.-typ.
Hypothesis str_t' : assoc_get str sigma = Some t'.
Variable t : g.-typ.
Variable e : exp sigma (:* t).
Variable tg : tag.
Hypothesis tgt : styp tg = t.
Variable f : string.
Hypothesis f_t' : assoc_get f (get_fields g tg) = |_ t' _|.

Lemma wp_lookup_fldp_ex (A : Type) (P : A -> assert) :
  wp_lookup_fldp _ str_t' e _ tgt _ f_t' (sepex  x, P x) <==>
  sepex y, wp_lookup_fldp _ str_t' e _ tgt _ f_t' (P y).
Proof.
move => s h; split.
- inversion_clear 1.
  case: H2 => H2 H3.
  inversion_clear H3.
  case: H => a H.
  exists a.
  rewrite -H0 in H1.
  econstructor.
  + reflexivity.
  + exact H1.
  + done.
- case => a.
  inversion_clear 1.
  rewrite -H in H0.
  econstructor.
  + reflexivity.
  + exact H0.
  + case: H1 => H11 H12.
    split => //.
    apply wp_assign_ex; by exists a.
Qed.

Lemma ent_R_lookup_fldp_trans (pv : t'.-phy) lvs (P : assert) R :
  R ===> (fun s h => ([e]_ s |lV~> log_of_styp _ _ tgt lvs) s h) ** TT ->
  pv |x| values_get f _ _ lvs (assoc_get_in f_t') ->
  R ===> wp_assign str_t' [ pv ]c P ->
  R ===> wp_lookup_fldp _ str_t' e _ tgt _ f_t' P.
Proof.
move=> H1 H2 H3.
econstructor.
- reflexivity.
- by apply H2.
- split.
  + move: (H1 _ _ H).
    inversion 1; subst.
    by constructor.
  + by apply H3.
Qed.

Lemma ent_R_lookup_fldp (pv : t'.-phy) lvs (P : assert) :
  pv |x| values_get f _ _ lvs (assoc_get_in f_t') ->
  (fun s h => ([e]_ s |lV~> log_of_styp _ _ tgt lvs) s h) ===>
    wp_assign str_t' [ pv ]c P ->
  (fun s h => ([e]_ s |lV~> log_of_styp _ _  tgt lvs) s h) ===>
    wp_lookup_fldp _ str_t' e _ tgt _ f_t' P.
Proof.
move=> H1 H2.
eapply ent_R_lookup_fldp_trans; eauto.
by apply ent_R_con_T.
Qed.

Lemma hoare_lookup_fldp (P : assert) :
  {{ wp_lookup_fldp _ str_t' e _ tgt _ f_t' P }} lookup str_t' (fldp sigma f e tgt f_t') {{ P }}.
Proof.
Transparent eval.
apply hoare_stren with (wp_lookup str_t' (fldp _ f e tgt f_t') P); last by apply hoare_hoare0, hoare0_lookup.
rewrite /entails => s h HP; inversion HP; subst; clear HP.
case: H1 => H H1.
inversion H1; subst; clear H1.
econstructor; last by apply H2.
inversion_clear H.
apply heap_get_value_union_L; first by map_tac_m.Disj.
rewrite /=.
inversion H3; subst; clear H3 => //=.
apply Eqdep.EqdepTheory.inj_pair2 in H7.
subst vs0.
move: (@log_mapstos_mapsto g _ _ _ _ _ (assoc_get_in f_t') _ H11) => [] h1' [] h2' [] Hdisj [] Heq /= Hmapsto'.
set new_addr := (_ + _)%nat in Hmapsto'.
rewrite Heq.
rewrite -hp.unionA.
apply heap_get_value_union_L.
  apply hp.disjhU => //.
  suff : h0 # pad.
    rewrite Heq => ?; by map_tac_m.Disj.
  move/log_mapstos_inv_heap_dom : (H11) => H11'.
  by rewrite hp.disjE H15 H11' size_iota dis_iota.
apply phy_mapsto_heap_get => //=.
move: (proj2 (phylog_mapsto_conv _ _ _ H0 h1' (field_address new_addr _ _ (get_fields _ _) (assoc_get_in f_t'))) Hmapsto') => Hequiv.
apply (phy_mapsto_eq Hequiv) => //=.
rewrite -value_phy_shift_pointer.
  have padd_is_zero : padd '|u2Z (ptr<=phy ([e ]_ s))|
      (align (seq.head (f, t') (get_fields g tg)).2) = O.
    apply padd_0; first by apply align_gt0.
    eapply dvdn_trans; last by apply H8.
    rewrite -nth0.
    apply align_get_fields => //.
      by apply assoc_get_in.
    rewrite -has_predT.
    apply/hasP.
    exists (f, t') => //; by apply assoc_get_in.
  rewrite /new_addr padd_is_zero addn0.
  move: (log_mapstos_inv2 _ _ _ _ _ _ (assoc_get_in f_t') H11) => H11_inv.
  rewrite padd_is_zero addn0 in H11_inv.
  rewrite field_address_slide0 // => i Hi str_dummy ty_dummy Hdummy.
  eapply dvdn_trans; last by apply H8.
  by apply align_get_fields.
move: (phy_mapsto_overflow Hequiv) => Hoverflow.
apply: (leZ_ltZ_trans _ Hoverflow).
rewrite (field_address_slide0 _ new_addr); last first.
  move=> i Hi str_dummy ty_dummy Hdummy.
  rewrite /new_addr padd_0; last 2 first.
    exact/align_gt0.
    eapply dvdn_trans; last by apply H8.
    rewrite -nth0.
    apply align_get_fields => //.
    by apply assoc_get_in.
    by apply leq_ltn_trans with i.
  rewrite addn0.
  eapply dvdn_trans; last by apply H8.
  by apply align_get_fields.
rewrite inj_plus /new_addr inj_plus Z_of_nat_Zabs_nat; last exact/min_u2Z.
rewrite -2!addZA; apply leZ_add2l.
apply Zle_plus_trans; first exact: Zle_0_nat.
rewrite addZC.
apply Zle_plus_trans; by [apply Zle_0_nat | apply leZZ].
Opaque eval.
Qed.

Lemma hoare_lookup_fldp_stren (P Q : assert) :
  P ===> wp_lookup_fldp _ str_t' e _ tgt _ f_t' Q ->
  {{ P }} lookup str_t' (fldp _ f e tgt f_t') {{ Q }}.
Proof. move/hoare_stren; apply. apply hoare_lookup_fldp. Qed.

End wp_lookup_fldp_sect.

(** lookup mapstos *)

CoInductive wp_lookup_mapstos str {t : g.-typ} (str_t : assoc_get str sigma = Some t)
  (l : seq (t.-phy)) (ei : exp sigma (:* t)) (e : exp sigma (:* t)) (i : nat) (P : assert) : assert :=
| mkWpLookupMapstos : forall s h,
  (size l > i)%nat ->
  (`! \b ei \= e \+ [Z_of_nat i]sc ** (e |--> l) ** TT) s h ->
  (wp_assign str_t [ nth pv0 l i ]c P) s h ->
  wp_lookup_mapstos _ str_t l ei e i P s h.

Notation "P '`{' x '<-' l '{' ei ',' e ',' i '}' '}''" := (wp_lookup_mapstos x _ l ei e i P) (at level 5, x, e at next level, format "'[hv ' P  '/  ' `{  x  <-  l  {  ei  ,  e  ,  i  }  }' ']'") : C_assert_scope.

Section wp_lookup_mapstos_sect.

Variable str : string.
Variable t : g.-typ.
Hypothesis str_t : assoc_get str sigma = Some t.
Variable l : seq (t.-phy).
Variables ei e : exp sigma (:* t).
Variable i : nat.

Lemma hoare_lookup_mapstos (Q : assert) :
  Z_of_nat (size l * sizeof t) < 2 ^^ 31 ->
  {{ wp_lookup_mapstos _ str_t l ei e i Q }} lookup str_t ei {{ Q }}.
Proof.
move=> l_ub.
apply hoare_stren with (@wp_lookup_back_TT _ _ str_t ei Q); last by apply hoare_lookup_back_TT.
move=> s_ h_ [] s h i_sz_l H1 Hh {s_ h_}.
move eqnh1 : h => h'.
case: H1 (eqnh1) => h1 h2 _ Hei Hh2; subst h'.
case: Hei => Hei; rewrite /emp => ?; subst h1.
rewrite hp.unioneh => ?; subst h2.
move eqnh : h => h'.
case: Hh2 (eqnh) => h1 h0 h1h0 Hh1 _ eqnh'; subst h' h.
rewrite (@nth_decomp _ pv0 l i i_sz_l) in Hh1.
have {Hh1}Hh1 : (e |--> take i l **
                (e \+ [Z_of_nat i]sc) |pe~> nth pv0 l i **
                (e \+ [Z_of_nat i.+1]sc) |--> drop i.+1 l) s h1.
  clear h1h0 Hei Hh.
  apply (mapstos_cat i) in Hh1; last 2 first.
    by rewrite size_take i_sz_l.
    rewrite size_cat size_take i_sz_l [size _]/= size_drop (_ : _ + _ = size l)%nat //.
    rewrite subnS prednK; last by rewrite subn_gt0.
    by rewrite subnKC // ltnW.
  move: Hh1; apply monotony_L.
  rewrite mapstos_cons.
  apply monotony_L, add_pe_n_1.
  by rewrite size_drop subnKC.
move eqnh1 : h1 => h1'.
case: Hh1 (eqnh1) => h11 h12 h11h12 Hh11 Hh12 eqnh1'; subst h1' h1.
move eqnh12 : h12 => h12'.
case : Hh12 (eqnh12) => h121 h122 h121h122 Hh121 Hh122 eqnh12'; subst h12' h12.
econstructor; last by apply Hh.
rewrite (_ : _ \U _ = h121 \U (h11 \U h122 \U h0)); last by Equal.
constructor => //.
- by Disj.
- move: Hei.
  rewrite beval_eq_p_eq.
  by move/eqP => ->.
Qed.

Lemma hoare_lookup_mapstos_stren (P Q : assert) :
  Z_of_nat (size l * sizeof t) < 2 ^^ 31 ->
  P ===> wp_lookup_mapstos _ str_t l ei e i Q ->
  {{ P }} lookup str_t ei {{ Q }}.
Proof.
move=> Hfit H.
eapply hoare_stren; first by apply H.
by apply hoare_lookup_mapstos.
Qed.

Lemma ent_R_lookup_mapstos_trans (P R : assert) : (size l > i)%nat ->
  R ===> `! \b ei \= e \+ [ Z<=nat i ]sc ** ( e |--> l) ** TT ->
  R ===> wp_assign str_t [nth pv0 l i]c P ->
  R ===> wp_lookup_mapstos _ str_t l ei e i P.
Proof.
move=> Hl H1 H2 s h HR.
move: {H1}(H1 _ _ HR) => H1.
move: {H2 HR}(H2 _ _ HR) => H2.
by constructor.
Qed.

End wp_lookup_mapstos_sect.

(** lookup mapstos_fit *)

CoInductive wp_lookup_mapstos_fit str {t : g.-typ} (str_t : assoc_get str sigma = Some t)
  (l : seq (t.-phy)) (ei : exp sigma (:* t))  (e : exp sigma (:* t)) (i : nat)
  (P : assert) : assert :=
| mkWpLookupMapstosFit: forall s h,
  (size l > i)%nat ->
  (`! \b ei \= e \+ [Z_of_nat i]sc ** ( e |---> l) ** TT) s h ->
  (wp_assign str_t [nth pv0 l i]c P) s h ->
  wp_lookup_mapstos_fit _ str_t l ei e i P s h.

Notation "P '`{' x '<fit-' l '{' ei ',' e ',' i '}' '}''" := (wp_lookup_mapstos_fit x _ l ei e i P) (at level 5, x, e at next level, format "'[hv ' P  '/  ' `{  x  <fit-  l  {  ei  ,  e  ,  i  }  }' ']'") : C_assert_scope.

Section wp_lookup_mapstos_fit_sect.

Variable str : string.
Variable t : g.-typ.
Hypothesis str_t : assoc_get str sigma = Some t.
Variable l : seq (t.-phy).
Variables ei e : exp sigma (:* t).
Variable i : nat.

Lemma hoare_lookup_mapstos_fit (Q : assert) :
  Z_of_nat (size l * sizeof t) < 2 ^^ 31 ->
  {{ wp_lookup_mapstos_fit _ str_t l ei e i Q }} lookup str_t ei {{ Q }}.
Proof.
move=> l_ub.
apply hoare_stren with (wp_lookup_mapstos _ str_t l ei e i Q); last first.
  by apply hoare_lookup_mapstos.
move=> s h [] s' h' il H H'.
apply mkWpLookupMapstos => //.
apply conA, conC in H.
apply conA, conC.
move: H; apply monotony_L, monotony_L.
rewrite /mapstos_fit.
eapply ent_trans; first by apply equiv_imp, con_and_bang_R.
by move=> s_ h_ [].
Qed.

Lemma hoare_lookup_mapstos_fit_stren (P Q : assert) :
  Z_of_nat (size l * sizeof t) < 2 ^^ 31 ->
  P ===> wp_lookup_mapstos_fit _ str_t l ei e i Q ->
  {{ P }} lookup str_t ei {{ Q }}.
Proof.
move => Hfit H.
eapply hoare_stren; first by apply H.
by apply hoare_lookup_mapstos_fit.
Qed.

Lemma ent_R_lookup_mapstos_fit_trans (P : assert) R :
  (size l > i)%nat ->
  R ===> `! \b ei \= e \+ [Z_of_nat i]sc ** e |---> l ** TT ->
  R ===> wp_assign str_t [nth pv0 l i]c P ->
  R ===> wp_lookup_mapstos_fit _ str_t l ei e i P.
Proof.
move => Hl H1 H2 s h HR.
move: {H1}(H1 _ _ HR) => H1.
move: {H2 HR}(H2 _ _ HR) => H2.
by constructor.
Qed.

End wp_lookup_mapstos_fit_sect.

Local Open Scope C_cmd_scope.

Section hoare_mutation_subst_sect.

Variable t : g.-typ.
Variable e1 : exp  sigma (:* t).
Variable e2 : exp sigma t.

Lemma hoare_mutation_local_forward_ground_le (lv lv' : t.-log) He2 :
  ground_exp e2 He2 |x| lv' ->
  {{ e1 |le~> lv }} e1 *<- e2 {{ e1 |le~> lv' }}.
Proof.
move=> e2_x_lv'.
eapply hoare_stren; last by apply hoare_hoare0, hoare0_mutation.
move=> s h P.
case: (log_mapsto_heap_get_ex lv ('| (Z<=u (ptr<=phy ([ e1 ]_s))) |) h P) => pv Hpv.
apply wp_mutation_c with pv => //.
apply log_mapsto_heap_upd with lv => //.
suff -> : [ e2 ]_s = ground_exp _ He2 by assumption.
by apply ground_exp_sem.
Qed.

Lemma hoare_mutation_subst_btyp t' str Hstr (e' : exp sigma (g.-ityp: t')) P Q :
  P ===> `! \b @var_e g _ str _ Hstr \= e' ** TT ->
  {{ P }} subst_exp str Hstr e' e1 *<- subst_exp str Hstr e' e2 {{ Q }} ->
  {{ P }} e1 *<- e2 {{ Q }}.
Proof.
move=> H1 H2.
apply hoare_complete => s h Psh.
case: (soundness _ _ _ H2 s h Psh) => Hsem1 Hsem2.
have He' : forall e_, [ subst_exp str Hstr e' e_ ]_s = [ e_ ]_s.
  move=> r_ e_.
  case: (H1 _ _ Psh) => h1 h2 h1dh2 H4 _.
  apply bbang_eqi_store_get in H4.
  by rewrite subst_exp_store_upd -H4 store_upd_get_eq.
split.
- move=> abs.
  apply Hsem1.
  inversion_clear abs.
  inversion H; subst; clear H.
  rewrite /a in H3.
  apply Eqdep.EqdepTheory.inj_pair2 in H6; subst e4.
  apply Eqdep.EqdepTheory.inj_pair2 in H7; subst e5.
  apply exec_cmd0, exec_mutation_err.
  set pv1 := [ _ ]_ s.
  set pv2 := [ _ ]_ s in H3.
  suff -> : pv1 = pv2 by assumption.
  rewrite /pv1 /pv2.
  by rewrite He'.
- move=> s' h' H.
  inversion_clear H.
  inversion H0; subst; clear H0.
  rewrite /a0 in H3 *.
  apply Eqdep.EqdepTheory.inj_pair2 in H6; subst e4.
  apply Eqdep.EqdepTheory.inj_pair2 in H7; subst e5.
  apply Hsem2.
  apply exec_cmd0.
  rewrite -(He' _ e1) -(He' _ e2).
  apply exec_mutation with v.
  by rewrite -(He' _ e1) in H3.
Qed.

End hoare_mutation_subst_sect.

(** mutation backward-reasoning form (MUBR) *)

CoInductive wp_mutation_backward {t : g.-typ} (e : exp sigma (:* t)) (e' : exp sigma t)
  (Q : assert) : assert :=
| mkWpMutationBackward : forall s h (old new : log t),
    ([ e' ]_ s) |x| new ->
    ([ e ]_ s |lV~> old ** ([ e ]_ s |lV~> new -* Q)) s h ->
    wp_mutation_backward e e' Q s h.

Lemma hoare_mutation_backward {t : g.-typ} (e1 : exp sigma (:* t)) (e2 : exp sigma t) Q :
  {{ wp_mutation_backward e1 e2 Q }} e1 *<- e2 {{ Q }}.
Proof.
apply hoare_stren with (wp_mutation e1 e2 Q); last by apply hoare_hoare0, hoare0_mutation.
move => s h HP.
inversion HP; subst; clear HP.
case: H0 => h1 h2 h1dh2 H1 H2.
case: (log_mapsto_heap_get_ex _ _ _ H1) => old' Hold'.
econstructor.
apply heap_get_value_union_L; first by map_tac_m.Disj.
apply Hold'.
rewrite heap_upd_union_L => //=.
- have Hdisj: (heap_upd t '|u2Z (ptr<=phy [e1 ]_ s)| [e2 ]_ s h1) # h2 by apply disj_heap_upd.
  apply (H2 (heap_upd t '|u2Z (ptr<=phy [e1 ]_ s)| [e2 ]_ s h1) Hdisj).
  by apply log_mapsto_heap_upd with old.
- by rewrite (log_mapsto_inv_heap_dom _ _ _ H1) seq_ext.inc_refl.
Qed.

Section hoare_mutation_fldp_local_foward_sect.

Variable f : string.
Variable tg : tag.
Variables t t' : g.-typ.
Hypothesis tgt' : styp tg = t'.
Hypothesis f_t : assoc_get f (get_fields g tg) = Some t.
Variable e2 : exp sigma t.

Lemma hoare_mutation_fldp_local_forward (e1 : exp sigma (:* t')) (lvs : logs _) :
  {{ fun s h => ([ e1 ]_ s |lV~> log_of_styp _ _ tgt' lvs) s h }}
  fldp _ _ e1 tgt' f_t *<- e2
  {{ fun s h => forall lv, ([ e2 ]_ s) |x| lv ->
     ([ e1 ]_ s |lV~>
     log_of_styp _ _ tgt' (values_set _ _ lv _ lvs (assoc_get_in f_t))) s h }}.
Proof.
apply hoare_stren with
  (wp_mutation (fldp _ _ e1 tgt' f_t) e2 (fun s h =>
    forall val, ([ e2 ]_ s) |x| val ->
    ([ e1 ]_ s |lV~> log_of_styp _ _ tgt'
                     (values_set _ _ val _ lvs (assoc_get_in f_t))) s h)); last by apply hoare_hoare0, hoare0_mutation.
move => s h //= HP.
inversion HP; subst => //=.
simpl in tgt'.
apply Eqdep.EqdepTheory.inj_pair2 in H2.
subst vs0.
move: (log_mapstos_mapsto _ _ _ _ _ (assoc_get_in f_t) _ H6) => [] h1' [] h2' [] Hdisj [] Heq Hmapsto'.
move: (log_mapsto_heap_get_ex _ _ _ Hmapsto') => [] x Hx.
rewrite padd_0 in Hmapsto'; last 2 first.
  by apply align_gt0.
  eapply dvdn_trans; last by apply H3.
  rewrite -nth0.
  apply align_get_fields => //.
  by apply assoc_get_in.
  rewrite -has_predT.
  apply/hasP.
  exists (f, t) => //.
  by apply: assoc_get_in.
rewrite addn0 in Hmapsto'.
have Htmp' : h0 # pad.
  clear Hx.
  apply log_mapstos_inv_heap_dom in H6.
  by rewrite hp.disjE H6 H10 dis_iota // H6 size_iota.
have Htmp : Z_of_nat (field_address 0 _ _ (get_fields g tg) (assoc_get_in f_t)) <=
      Z_of_nat (size (hp.dom h0)) +
      Z_of_nat
      (padd ('|u2Z (ptr<=phy ([ e1 ]_ s))| + size (hp.dom h0))
        (align t')).
  have H1': (field_address 0 _ _ (get_fields g tg) (assoc_get_in f_t) < sizeof t')%nat.
    by eapply lt_field_address0_sizeof; eauto.
  have H2': size (hp.dom (h0 \U pad)) = sizeof t'.
    apply log_mapsto_inv_heap_dom in HP.
    by rewrite HP size_iota.
  have H3' : (size (hp.dom (h0 \U pad)) = size (hp.dom h0) + size (hp.dom pad))%nat.
    by rewrite hp_prop_m.size_dom_union.
  have H5_: size (hp.dom pad) = padd ('|u2Z (ptr<=phy ([ e1 ]_ s))| + size (hp.dom h0)) (align t').
    by rewrite H10 size_iota.
  rewrite -H5_ -inj_plus plusE -H3' H2'.
  apply inj_le.
  apply/leP.
  apply ltnW.
  exact H1'.
apply wp_mutation_c with (v := x).
- apply heap_get_value_union_L => //.
  rewrite Heq.
  apply heap_get_value_union_L; first by map_tac_m.Disj.
  rewrite -value_phy_shift_pointer.
  + rewrite padd_0 in Hx; last 2 first.
      by apply align_gt0.
      eapply dvdn_trans; last by apply H3.
      rewrite -nth0.
      apply align_get_fields => //.
      by apply assoc_get_in.
      rewrite -has_predT.
      apply/hasP.
      exists (f, t) => //.
      by apply: assoc_get_in.
    rewrite addn0 in Hx.
    rewrite -field_address_slide0 // => i Hi str_dummy ty_dummy Hdummy.
    eapply dvdn_trans; last by apply H3.
    by apply align_get_fields.
  + apply: (leZ_ltZ_trans _ H4).
    rewrite inj_plus Z_of_nat_Zabs_nat; last exact/min_u2Z.
    rewrite -addZA; apply leZ_add2l.
    exact Htmp.
- move => val Hval /=.
  rewrite -value_phy_shift_pointer.
  + by apply values_set_heap_upd.
  + apply: (leZ_ltZ_trans _ H4).
    rewrite inj_plus Z_of_nat_Zabs_nat; last exact/min_u2Z.
    rewrite -addZA; apply leZ_add2l.
    exact Htmp.
Qed.

Lemma hoare_mutation_fldp_local_forward_ground_le
  (e1 : exp sigma (:* t')) (He2 : vars e2 = nil) val lvs :
  ground_exp e2 He2 |x| val ->
  {{ e1 |le~> log_of_styp _ _ tgt' lvs }}
  fldp _ _ e1 tgt' f_t *<- e2
  {{ e1 |le~> log_of_styp _ _ tgt' (values_set _ _ val _ lvs (assoc_get_in f_t)) }}.
Proof.
move=> Hequiv.
eapply hoare_weak; last by apply hoare_mutation_fldp_local_forward.
move=> s h //=.
apply.
by rewrite ground_exp_sem.
Qed.

Lemma hoare_mutation_fldp_local_forward_ground_lV (v1 : (:* t').-phy) He2 val lvs :
  (ground_exp e2 He2) |x| val ->
  {{ v1 |lV~> log_of_styp _ _ tgt' lvs }}
  fldp _ _ [ v1 ]c tgt' f_t *<- e2
  {{ v1 |lV~> log_of_styp _ _ tgt' (values_set _ _ val _ lvs (assoc_get_in f_t)) }}.
Proof.
move=> Hequiv.
eapply hoare_weak; last by apply hoare_mutation_fldp_local_forward with (e1 := [ v1 ]c).
move => s h //=.
apply.
by rewrite ground_exp_sem.
Qed.

End hoare_mutation_fldp_local_foward_sect.

Section hoare_mutation_fldp_subst_sect.

Variable f : string.
Variable tg : tag.
Variable t t' : g.-typ.
Hypothesis tgt' : styp tg = t'.
Hypothesis f_t : assoc_get f (get_fields g tg) = Some t.
Variable e1 : exp  sigma (:* t').
Variable e2 : exp sigma t.

Lemma hoare_mutation_fldp_subst_ityp str (t'' : integral) Hstr (e : exp sigma (ityp: t'')) P Q :
  P ===> `! \b @var_e g _ str (ityp: t'') Hstr \= e ** TT ->
  {{ P }}
    fldp _ _ (subst_exp str Hstr e e1) tgt' f_t *<- subst_exp str Hstr e e2
  {{ Q }} ->
  {{ P }} fldp _ _ e1 tgt' f_t *<- e2 {{ Q }}.
Proof.
move => HP Hoare.
apply hoare_complete => s h HPsh.
move: (soundness _ _ _ Hoare s h HPsh) => [] Hsem1 Hsem2.
have He': forall e', [subst_exp _ Hstr e e']_ s = [e']_ s.
  move => c e'.
  have Hb : (`! \b var_e _ str (ityp: t'') Hstr \= e) s hp.emp.
    move: (HP _ _ HPsh) => H'.
    inversion H'; subst; clear H'.
    split; last by done.
    by apply (proj1 H0).
  rewrite subst_exp_store_upd.
  by rewrite -(bbang_eqi_store_get _ _ _ _ _ _ Hb) store_upd_get_eq.
split.
- move => H'.
  apply Hsem1.
  Transparent eval.
  inversion_clear H'; inversion H; subst; clear H.
  constructor; eapply exec_mutation_err => //=.
  unfold a in *.
  apply Eqdep.EqdepTheory.inj_pair2 in H4; subst e4.
  apply Eqdep.EqdepTheory.inj_pair2 in H5; subst e5.
  rewrite He'; exact H1.
- move => s' h' Hsem.
  apply Hsem2.
  inversion_clear Hsem.
  inversion H; subst; clear H.
  rewrite -(He' _ e5).
  unfold a0 in *.
  apply Eqdep.EqdepTheory.inj_pair2 in H4; subst e4.
  apply Eqdep.EqdepTheory.inj_pair2 in H5; subst e5.
  rewrite /= -(He' _ e1).
  constructor; eapply exec_mutation => //=.
  rewrite /= in H1.
  rewrite (He' _ e1); exact H1.
  Opaque eval.
Qed.

(**  P => str = e'' -> { P } e1{e''/str}.f *<- e2{e''/str} { Q }  ->  { P } e1.f *<- e2 { Q }  *)
Lemma hoare_mutation_fldp_subst_ptr str (t'' : g.-typ) Hstr (e'' : exp sigma (:* t'')) P Q :
  P ===> `! \b @var_e g _ str (:* t'') Hstr \= e'' ** TT ->
  {{ P }}
    fldp _ _ (subst_exp str Hstr e'' e1) tgt' f_t *<- subst_exp str Hstr e'' e2
  {{ Q }} ->
  {{ P }} fldp _ _ e1 tgt' f_t *<- e2 {{ Q }}.
Proof.
Transparent eval.
move => HP Hoare.
apply hoare_complete => s h HPsh.
move: (soundness _ _ _ Hoare s h HPsh) => [] Hsem1 Hsem2.
have He' : forall e', [subst_exp str Hstr e'' e']_ s = [ e' ]_ s.
  move => c e'.
  have Hb : (`! \b var_e _ str (:* t'') Hstr \= e'') s hp.emp.
    move: (HP _ _ HPsh) => H'.
    inversion H'; subst; clear H'.
    split; last by done.
    by apply (proj1 H0).
  by rewrite subst_exp_store_upd -(bbang_eqp_store_get _ _ _ _ _ _ Hb) store_upd_get_eq.
split.
- move => H'.
  apply Hsem1.
  inversion_clear H'; inversion H; subst; clear H.
  constructor; eapply exec_mutation_err => //=.
  unfold a in *.
  apply Eqdep.EqdepTheory.inj_pair2 in H4; subst e4.
  apply Eqdep.EqdepTheory.inj_pair2 in H5; subst e5.
  rewrite He'; exact H1.
- move => s' h' Hsem.
  apply Hsem2.
  inversion_clear Hsem.
  inversion H; subst; clear H.
  rewrite -(He' _ e5).
  apply Eqdep.EqdepTheory.inj_pair2 in H5; subst e5.
  rewrite He'.
  unfold a0 in *.
  apply Eqdep.EqdepTheory.inj_pair2 in H4; subst e4.
  rewrite -(He' _ e2) /= -(He' _ e1).
  constructor; eapply exec_mutation => //=.
  rewrite (He' _ e1); exact H1.
Opaque eval.
Qed.

End hoare_mutation_fldp_subst_sect.

(** Conditional branching *)

Lemma hoare_ifte_bang P Q b c d :
  {{ P ** `! b }} c {{ Q }} -> {{ P ** `! \~b b }} d {{ Q }} ->
  {{ P }} ifte b c d {{ Q }}.
Proof.
move => H1 H2.
apply hoare_ifte.
- eapply hoare_stren; last by apply H1.
  rewrite /bbang /bang /eval_b /C_Semop0.eval_b /emp /= => s h HPre; inversion HPre; subst; clear HPre.
  rewrite -(hp.unionhe h).
  constructor => //=; by Disj.
- eapply hoare_stren; last by apply H2.
  rewrite /bbang /bang /eval_b /C_Semop0.eval_b /emp /= => s h HPre; inversion HPre; subst; clear HPre.
  rewrite -(hp.unionhe h).
  constructor => //=; by Disj.
Qed.

Lemma hoare_ifte_left_bang P Q b c d : P ===> `! b ->
  {{ P }} c {{ Q }} -> {{ P }} ifte b c d {{ Q }}.
Proof.
move => HP Hhoare.
apply hoare_ifte_bang.
  apply hoare_stren with P  => //=.
  move => s h H; inversion H; subst; clear H.
  rewrite /bbang /bang in H2; inversion_clear H2.
  by rewrite H3 hp.unionhe.
eapply hoare_stren; last by apply hoare_L_F.
move => s h H; inversion H; subst; clear H.
case: H2 => H2 H3.
case: (HP _ _ H1) => H' _.
rewrite beval_neg_not in H2.
rewrite /bbang /bang /= in H'.
move/negP in H2; contradiction.
Qed.

Lemma hoare_ifte_right_bang P Q b c d : P ===> `! \~b b ->
  {{ P }} d {{ Q }} -> {{ P }} ifte b c d {{ Q }}.
Proof.
move => HP Hhoare.
apply hoare_ifte_bang.
- eapply hoare_stren; last by apply hoare_L_F.
  move => s h H; inversion H; subst; clear H.
  inversion_clear H2.
  move: (HP _ _ H1).
  inversion_clear 1.
  move: H2.
  rewrite beval_neg_not.
  move/negP.
  contradiction.
- apply hoare_stren with P  => //=.
  move => s h; inversion 1; subst; clear H.
  rewrite /bbang /bang in H2; inversion_clear H2.
  by rewrite H3 hp.unionhe.
Qed.

(** Hoare triples about while-loops *)

Lemma hoare_while_invariant_bang (P : assert) (t : bexp sigma) (c : cmd) (Q Inv : assert) :
  P ===> Inv ->
  Inv ** `! \~b t ===> Q ->
  {{ Inv ** `! t }} c {{ Inv }} ->
  {{ P  }} while t c {{ Q }}.
Proof.
move=> H1 H2 H3.
move: (hoare_while_invariant P t c Q Inv H1).
rewrite /eval_b //=.
apply.
  eapply ent_trans; last by apply H2.
  move => s h [] H4 H5.
  rewrite -(hp.unionhe h).
  constructor => //=; by map_tac_m.Disj.
eapply hoare_stren; last by apply H3.
move => s h //= [] H4 H5.
rewrite -(hp.unionhe h).
constructor => //=;  by map_tac_m.Disj.
Qed.

Definition forloop c1 pre_test test c2 body :=
  c1 ;
  pre_test ;
  While \b test {{
    body ;
    c2 ;
    pre_test
  }}.

Notation "'For(' c1 '\;' pretest '\,' test '\;' c2 '){{' c '}}' " :=
  (forloop c1 pretest test c2 c)
  (at level 200, format
"'[v' 'For('  c1  '\;' '//'  pretest '\,' '//' test '\;' '//'  c2  '){{' '//'   '[' c ']' '//' '}}' ']'") : whilesemop_scope.

Notation "'For(' c1 '\;' test '\;' c2 '){{' c '}}' " :=
  (forloop c1 skip test c2 c)
  (at level 200, format
"'[v' 'For('  c1  '\;' '//'  test '\;' '//'  c2  '){{' '//'   '[' c ']' '//' '}}' ']'") : whilesemop_scope.

Lemma hoare_forloop c1 pre_test test c2 body (P Q : assert) :
  {{ Q }} c1 {{ P }} ->
  {{ P }} pre_test {{ P }} ->
  {{ `! \b test ** P }} body ; c2 ; pre_test {{ P }} ->
  {{ Q }} forloop c1 pre_test test c2 body {{ `! \~b \b test ** P}}.
Proof.
move=> Hc1 Hpre_test H.
rewrite /forloop.
apply hoare_seq with P => //.
apply hoare_seq with P => //.
apply hoare_while_invariant_bang with P => //.
rewrite conC; by apply ent_id.
by rewrite conC.
Qed.

Lemma hoare_forloop2 c1 pre_test test c2 body (P Q inv : assert) :
  (* entry *)
  {{ P }} c1; pre_test {{ inv }} ->
  (* exit *)
  `! \~b \b test ** inv ===> Q ->
  (* loop body *)
  {{ `! \b test ** inv }} body ; c2; pre_test {{ inv }} ->
  {{ P }} forloop c1 pre_test test c2 body {{ Q }}.
Proof.
move=> H1 H2 H3.
apply hoare_seq_assoc', hoare_seq with inv => //.
apply hoare_while_invariant with inv => //.
- eapply ent_trans; last by apply H2.
  rewrite conC /C_definition.eval_b /C_StateBipl.eval_b /=.
  by apply equiv_imp2, con_and_bang_R.
- eapply hoare_stren; last by apply H3.
  rewrite conC /C_definition.eval_b /C_StateBipl.eval_b /=.
  by apply equiv_imp2, con_and_bang_R.
Qed.

Set Implicit Arguments.
Unset Strict Implicit.

Section wp_assign_con_variants.

Variable (str : string) (t : g.-typ).
Hypothesis str_t : assoc_get str sigma = Some t.
Variable e : exp sigma t.
Variables P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 : assert.

Lemma wp_assign_con2 : wp_assign str_t e (P0 ** P1 ** P2) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con3 : wp_assign str_t e (P0 ** P1 ** P2 ** P3) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con4 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con5 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con6 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con7 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7.
Proof.
by do 7 rewrite wp_assign_con.
Qed.

Lemma wp_assign_con8 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con9 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con10 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9 ** P10) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9 ** wp_assign str_t e P10.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con11 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9 ** P10 ** P11) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9 ** wp_assign str_t e P10 ** wp_assign str_t e P11.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con12 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9 ** P10 ** P11 ** P12) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9 ** wp_assign str_t e P10 ** wp_assign str_t e P11 **
  wp_assign str_t e P12.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con13 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9 ** P10 ** P11 ** P12 ** P13) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9 ** wp_assign str_t e P10 ** wp_assign str_t e P11 **
  wp_assign str_t e P12 ** wp_assign str_t e P13.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con14 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9 ** P10 ** P11 ** P12 ** P13 ** P14) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9 ** wp_assign str_t e P10 ** wp_assign str_t e P11 **
  wp_assign str_t e P12 ** wp_assign str_t e P13 ** wp_assign str_t e P14.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con15 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9 ** P10 ** P11 ** P12 ** P13 ** P14 ** P15) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9 ** wp_assign str_t e P10 ** wp_assign str_t e P11 **
  wp_assign str_t e P12 ** wp_assign str_t e P13 ** wp_assign str_t e P14 **
  wp_assign str_t e P15.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con16 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9 ** P10 ** P11 ** P12 ** P13 ** P14 ** P15 ** P16) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9 ** wp_assign str_t e P10 ** wp_assign str_t e P11 **
  wp_assign str_t e P12 ** wp_assign str_t e P13 ** wp_assign str_t e P14 **
  wp_assign str_t e P15 ** wp_assign str_t e P16.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con17 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9 ** P10 ** P11 ** P12 ** P13 ** P14 ** P15 ** P16 ** P17) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9 ** wp_assign str_t e P10 ** wp_assign str_t e P11 **
  wp_assign str_t e P12 ** wp_assign str_t e P13 ** wp_assign str_t e P14 **
  wp_assign str_t e P15 ** wp_assign str_t e P16 ** wp_assign str_t e P17.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con18 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9 ** P10 ** P11 ** P12 ** P13 ** P14 ** P15 ** P16 ** P17 ** P18) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9 ** wp_assign str_t e P10 ** wp_assign str_t e P11 **
  wp_assign str_t e P12 ** wp_assign str_t e P13 ** wp_assign str_t e P14 **
  wp_assign str_t e P15 ** wp_assign str_t e P16 ** wp_assign str_t e P17 **
  wp_assign str_t e P18.
Proof.
by do ! rewrite wp_assign_con.
Qed.

Lemma wp_assign_con19 : wp_assign str_t e (P0 ** P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 ** P8 ** P9 ** P10 ** P11 ** P12 ** P13 ** P14 ** P15 ** P16 ** P17 ** P18 ** P19) <==>
  wp_assign str_t e P0 ** wp_assign str_t e P1 ** wp_assign str_t e P2 **
  wp_assign str_t e P3 ** wp_assign str_t e P4 ** wp_assign str_t e P5 **
  wp_assign str_t e P6 ** wp_assign str_t e P7 ** wp_assign str_t e P8 **
  wp_assign str_t e P9 ** wp_assign str_t e P10 ** wp_assign str_t e P11 **
  wp_assign str_t e P12 ** wp_assign str_t e P13 ** wp_assign str_t e P14 **
  wp_assign str_t e P15 ** wp_assign str_t e P16 ** wp_assign str_t e P17 **
  wp_assign str_t e P18 ** wp_assign str_t e P19.
Proof.
by do ! rewrite wp_assign_con.
Qed.

End wp_assign_con_variants.

Ltac count_sepcons P :=
  match P with
    | (?P1 ** ?P2) => let n1 := count_sepcons P1 in
                      let n2 := count_sepcons P2 in
                      constr: ((1 + n1 + n2)%nat)
    | _ => O
  end.

Ltac easy_Ent_monotony_R new_goal H :=
  apply ent_trans with new_goal;
  [ clear H | repeat (apply monotony_R || apply monotony_L); exact H].

Ltac easy_Ent_monotony_L new_goal H :=
  apply ent_trans with new_goal;
  [ repeat (apply monotony_R || apply monotony_L); exact H | clear H ].

Ltac Ent_R_subst_con_distr_generic_helper ctxt wp_assign_con_lemma :=
  let H := fresh in
  generalize (equiv_imp2 _ _ wp_assign_con_lemma); intro H ;
  match goal with
    | H : ?Hsubst ===> _ |- _ =>
      let new_goal := context ctxt [ Hsubst ] in
      easy_Ent_monotony_R new_goal H
  end.

Ltac Ent_R_subst_con_distr_generic :=
  match goal with
    | |- _ ===> ?rhs =>
      match rhs with
        | context ctxt' [wp_assign ?H ?expr (?P ** ?Q)] =>
          let n := count_sepcons (P ** Q) in
          let n' := eval compute in (n <= 19)%nat in
          match n' with
          | true =>

match rhs with
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10 ** ?P11 ** ?P12 ** ?P13 ** ?P14 ** ?P15 ** ?P16 ** ?P17 ** ?P18 ** ?P19 ** ?P20)] =>
    let tmp := constr: (@wp_assign_con19 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P15 P16 P17 P18 P19 P10) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10 ** ?P11 ** ?P12 ** ?P13 ** ?P14 ** ?P15 ** ?P16 ** ?P17 ** ?P18 ** ?P19)] =>
    let tmp := constr: (@wp_assign_con18 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P15 P16 P17 P18 P19) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10 ** ?P11 ** ?P12 ** ?P13 ** ?P14 ** ?P15 ** ?P16 ** ?P17 ** ?P18)] =>
    let tmp := constr: (@wp_assign_con17 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P15 P16 P17 P18) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10 ** ?P11 ** ?P12 ** ?P13 ** ?P14 ** ?P15 ** ?P16 ** ?P17)] =>
    let tmp := constr: (@wp_assign_con16 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P15 P16 P17) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10 ** ?P11 ** ?P12 ** ?P13 ** ?P14 ** ?P15 ** ?P16)] =>
    let tmp := constr: (@wp_assign_con15 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P15 P16) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10 ** ?P11 ** ?P12 ** ?P13 ** ?P14 ** ?P15)] =>
    let tmp := constr: (@wp_assign_con14 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P15) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10 ** ?P11 ** ?P12 ** ?P13 ** ?P14)] =>
    let tmp := constr: (@wp_assign_con13 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10 ** ?P11 ** ?P12 ** ?P13)] =>
    let tmp := constr: (@wp_assign_con12 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10 ** ?P11 ** ?P12)] =>
    let tmp := constr: (@wp_assign_con11 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10 ** ?P11)] =>
    let tmp := constr: (@wp_assign_con10 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9 ** ?P10)] =>
    let tmp := constr: (@wp_assign_con9 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8 ** ?P9)] =>
    let tmp := constr: (@wp_assign_con8 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8 P9) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7 ** ?P8)] =>
    let tmp := constr: (@wp_assign_con7 _ _ H expr P1 P2 P3 P4 P5 P6 P7 P8) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6 ** ?P7)] =>
    let tmp := constr: (@wp_assign_con6 _ _ H expr P1 P2 P3 P4 P5 P6 P7) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5 ** ?P6)] =>
    let tmp := constr: (@wp_assign_con5 _ _ H expr P1 P2 P3 P4 P5 P6) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4 ** ?P5)] =>
    let tmp := constr: (@wp_assign_con4 _ _ H expr P1 P2 P3 P4 P5) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3 ** ?P4)] =>
    let tmp := constr: (@wp_assign_con3 _ _ H expr P1 P2 P3 P4) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P1 ** ?P2 ** ?P3)] =>
    let tmp := constr: (@wp_assign_con2 _ _ H expr P1 P2 P3) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | context ctxt [wp_assign ?H ?expr (?P ** ?Q)] =>
    let tmp := constr: (@wp_assign_con _ _ H expr P Q) in
    Ent_R_subst_con_distr_generic_helper ctxt tmp
  | _ => fail "Ent_R_subst_con_distr: shouldn't happen"
end

          | false => idtac "Ent_R_subst_con_distr: rewrite !wp_assign_con" ; fail
          end
      end
  end.

Ltac Ent_R_subst_con_distr :=
match goal with
  | |- _ ===> ?rhs =>
    match rhs with
      | wp_assign ?H ?expr (?P ** ?Q) =>
        let n := count_sepcons (P ** Q) in
        let n' := eval compute in n in
        match n' with
         | 1%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con _ _ _ _))
         | 2%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con2 _ _ _ _ _))
         | 3%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con3 _ _ _ _ _ _))
         | 4%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con4 _ _ _ _ _ _ _))
         | 5%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con5 _ _ _ _ _ _ _ _))
         | 6%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con6 _ _ _ _ _ _ _ _ _))
         | 7%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con7 _ _ _ _ _ _ _ _ _ _))
         | 8%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con8 _ _ _ _ _ _ _ _ _ _ _))
         | 9%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con9 _ _ _ _ _ _ _ _ _ _ _ _))
         | 10%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con10 _ _ _ _ _ _ _ _ _ _ _ _ _))
         | 11%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con11 _ _ _ _ _ _ _ _ _ _ _ _ _ _))
         | 12%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
         | 13%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
         | 14%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
         | 15%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con15 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
         | 16%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
         | 17%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con17 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
         | 18%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con18 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
         | 19%nat => eapply ent_trans; last by apply (equiv_imp2 _ _ (wp_assign_con19 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
         | _ => fail "Ent_R_subst_con_distr: not yet supported"
        end
      | context ctxt [wp_assign ?H ?expr (?P ** ?Q)] => Ent_R_subst_con_distr_generic
      | _ => fail "Ent_R_subst_con_distr: use rewrite !wp_assign_con"
    end
end.

(* triple lemmas *)

Lemma hoare_pullout_sbang_postcond (P : assert) (c : cmd) (Q : assert) (R : Prop) :
  R -> {{P}}c {{Q}} -> {{ P }} c {{ !!(R) ** Q}}.
Proof.
move => r Hoare.
apply hoare_weak with Q; last by [].
move => s h HQ.
rewrite -(hp.unioneh h).
constructor; by [map_tac_m.Disj | |].
Qed.

(* ground bang *)

Lemma ground_bbang_sbang (b : bexp sigma) (H : bvars b = nil) :
  `! b <==> sbang (ground_bexp b H).
Proof.
move => s h; rewrite /bbang /bang /sbang; split; split.
- case: H0 => H1 H2.
  by rewrite -(ground_bexp_sem s _ H).
- by case: H0.
- rewrite (ground_bexp_sem s _ H); tauto.
- tauto.
Qed.

(* sepex *)

Lemma entail_exists_left_intro {A : Type} (P : A -> assert) Q:
  (forall x, P x ===> Q) -> (sepex  x, P x) ===> Q.
Proof. move => H s h [] x Hx; by apply (H x). Qed.

Lemma entail_exists_right_intro {A : Type} (P : A -> assert) Q:
  (exists x, Q ===> P x) -> Q ===> (sepex x, P x).
Proof. move => [] x Hx s h H; by exists x; apply Hx. Qed.

Lemma exists_left_prenex {A : Type} (P : A -> assert) Q :
  (sepex x, P x) ** Q <==> sepex  x, P x ** Q.
Proof.
split.
- case=> h1 h2 h1dh2 [x Hh1] Hh2; by exists x.
- case=> x [h1 h2 h1dh2 Hh1 Hh2]; apply con_c => //; by exists x.
Qed.

(** independence of assertion w.r.t. variables *)

Section only_dep_sect.

(* only_dep l Hl P : l is the domain of P *)
Definition only_dep (l : g.-env) (Hl : {subset l <= sigma}) (P : assert) :=
  forall s h,
    (forall x ty v (H : (x, ty) \notin l) (H0 : (x, ty) \in sigma),
      (P s h <->
       P (store_upd (assoc_get_subset_in uniq_sigma (fun _ => id) H0) v s) h)).

Lemma only_dep_equiv (l : g.-env) (Hl : {subset l <= sigma}) (P Q : assert) :
  (P <==> Q) -> (only_dep Hl P <-> only_dep Hl Q).
Proof.
move=> Hequiv; split => H; move => s h x ty v H0 H1;
  split => H2; by apply/Hequiv/(H s h x ty v H0 H1)/Hequiv.
Qed.

Lemma only_dep_contraction P (l' : g.-env) (H' : {subset l' <= sigma})
  (l : g.-env) (H : {subset l <= sigma}) : l =i l' ->
  only_dep H' P -> only_dep H P.
Proof.
move => ll' Hsub s h str ty v H1 H2.
by apply Hsub; rewrite -ll'.
Qed.

Lemma only_dep_inde_cmd c P l Hl : @only_dep l Hl P ->
  forall l', l' = unzip1 l ->
    (all (fun s => s \notin l') (unzip1 (modified_vars c))) ->
    inde_cmd c P.
Proof.
move => Hdep l' Hl' Hbool s h x ty v H.
move: {Hdep}(Hdep s h x ty v) => Hdep.
have Hnotin: (x, ty) \notin l.
  move/allP in Hbool.
  subst l'.
  apply notin_unzip1_notin, Hbool.
  by apply/mapP; exists (x, ty).
have Hin : (x, ty) \in sigma by apply (modified_vars_subset_type_store c).
move : (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _)
  (Hdep Hnotin Hin) => ob ob1.
by have ->: ob = ob1 by apply/eq_irrelevance.
Qed.

Lemma sepex_only_dep {A} lP HlP (P : A -> assert):
  (forall x, @only_dep lP HlP (P x)) -> @only_dep lP HlP (sepexists P).
Proof.
move => H s h x ty v H0 H1; split.
- inversion_clear 1.
  exists x0.
  exact/(H x0 s h x ty v H0 H1).
- inversion_clear 1.
  exists x0.
  exact/(H x0 s h x ty v H0 H1).
Qed.

Lemma bbang_only_dep b : only_dep (bvars_subset_sigma b) (`! b).
Proof.
move => s h x ty v H0 H1; split; case=> H2 H3.
- split => //.
  rewrite beval_store_upd_notin //.
  by apply (uniq_subset_notin uniq_sigma (bvars_subset_sigma b) H0 H1).
- split => //.
  rewrite beval_store_upd_notin // in H2.
  by apply (uniq_subset_notin uniq_sigma (bvars_subset_sigma b) H0 H1).
Qed.

Lemma mapstos_store_upd_notin {ty : g.-typ} s
  (ty' : g.-typ) y (H : env_get y sigma = Some ty') pval:
  forall (l : seq (ty.-phy)) (e : exp sigma (:* ty)) (Hnotin: y \notin (unzip1 (vars e))),
    (forall h, (e |--> l) s h <-> (e |--> l) (store_upd H pval s) h).
Proof.
elim => //= hd tl Hind; split.
- move => Hcon; inversion Hcon; subst; clear Hcon.
  constructor => //=.
    by rewrite eval_store_upd_notin.
  apply/Hind => //=; by rewrite cats0.
- move => Hcon; inversion Hcon; subst; clear Hcon.
  constructor => //=.
    by rewrite eval_store_upd_notin in H1.
  apply/Hind => //=; by rewrite cats0.
Qed.

Lemma mapstos_only_dep (t : g.-typ) (e : exp sigma (:* t)) l :
  only_dep (vars_in_ts e) (e |--> l).
Proof.
move => s h x ty' v H0 H1.
apply mapstos_store_upd_notin, (uniq_subset_notin uniq_sigma (vars_in_ts e) H0 H1).
Qed.

Lemma log_mapsto_only_dep (ty : g.-typ) (p : (:* ty).-phy) (l : log ty) :
  only_dep (@subset_nil _ sigma) (p |lV~> l).
Proof. by []. Qed.

Lemma log_mapsto_e_only_dep (ty : g.-typ) (e : exp sigma (:* ty)) (l : log ty):
  only_dep (vars_in_ts e) (e |le~> l).
Proof.
move => s h x ty' v H0 H1.
rewrite /= eval_store_upd_notin //.
apply (uniq_subset_notin uniq_sigma (vars_in_ts e) H0 H1).
Qed.

Lemma sbang_only_dep (b : Prop) : only_dep (@subset_nil _ sigma) (!!( b )).
Proof. by []. Qed.

Lemma con_only_dep P Q lP HlP lQ HlQ :
  @only_dep lP HlP P -> @only_dep lQ HlQ Q ->
  @only_dep (lP ++ lQ) (subset_cat HlQ HlP) (P ** Q).
Proof.
move => HP HQ s h x ty v H0 H1.
move: H0 (H0) => H0' H0; move: H0'.
rewrite mem_cat negb_or; case/andP => HnotinP HnotinQ.
split; case => h1 h2 H2 H3 H4; by constructor => //;
  [ apply (HP s h1 x ty v HnotinP H1) |
    apply (HQ s h2 x ty v HnotinQ H1) ].
Qed.

Lemma sepor_only_dep P Q lP HlP lQ HlQ:
  @only_dep lP HlP P -> @only_dep lQ HlQ Q ->
  @only_dep (lP ++ lQ) (subset_cat HlQ HlP) (P \\// Q).
Proof.
move => HP HQ s h x ty v H0 H1.
move: H0 (H0) => H0' H0; move: H0'.
rewrite mem_cat negb_or; case/andP => HnotinP HnotinQ.
split; by case => H;[ left; apply (HP s h x ty v HnotinP H1) |
                      right; apply (HQ s h x ty v HnotinQ H1) ].
Qed.

Lemma bang_only_dep k b {ty} (e : exp sigma (:* ty)) :
  @only_dep (vars e) (vars_in_ts e) (!(fun s =>
    (u2Z (ptr<=phy [ e ]_s) + k < b)%Z)).
Proof.
rewrite /only_dep => s h str tu' v H1 H2.
rewrite /bang eval_store_upd_notin; first by tauto.
apply (uniq_subset_notin uniq_sigma (vars_in_ts e) H1 H2).
Qed.

Lemma mapstos_fit_only_dep {ty : g.-typ} (e : exp  sigma (:* ty)) l :
  only_dep (vars_in_ts e) (e |---> l).
Proof.
rewrite /mapstos_fit.
suff : @only_dep (vars e ++ vars e) (vars_in_ts (e \= e))
     (e |--> l ** !(fun s => (Z<=u (ptr<=phy [e ]_ s) +
         Z<=nat (sizeof ty * size l) < 2 ^^ ptr_len)%Z)).
  apply only_dep_contraction => i; by rewrite mem_cat orb_idl.
eapply con_only_dep; by [apply mapstos_only_dep | apply bang_only_dep].
Qed.

End only_dep_sect.

Local Close Scope Z_scope.

Local Open Scope machine_int_scope.

Lemma mod_1_even e : `! \b e \% 1 \= ([ 0 ]sc : exp _ (ityp: sint)) ===>
   (sepex k, `! \b e \= [ zext 1 (k : int 31) `<< 1 ]pc).
Proof.
move=> s h [] H H'; rewrite /emp in H'; subst h.
Transparent eval beval.
move: H => /=.
move He : ( [ e ]_s) => [he Hhe].
set H' := eq_ind_r _ _ _.
have -> : H' = Hhe by apply eq_irrelevance.
rewrite /= !i8_of_i32K.
case: ifP; last by rewrite is_zero_0.
rewrite not_is_zero_1.
move/eqP/s2Z_inj => H _.
rewrite Z2s_Z2u_k // in H.
set lhs := _ `% 32 in H.
have {H}H : u2Z lhs = u2Z zero32 by rewrite H.
rewrite /lhs {lhs} u2Z_rem' in H; last first.
  apply (@ltZ_trans (2 ^^ 1)%Z) => //; exact/max_u2Z.
exists ((i32<=i8 he Hhe `>> 1) `% 31); split => //=.
rewrite He -/H'.
set H'' := eq_ind_r _ _ _.
rewrite i8_of_i32K.
case: ifP; first by rewrite not_is_zero_1.
have -> : H' = Hhe by apply eq_irrelevance.
rewrite is_zero_0 /= => <-.
apply/eqP.
congr (Z<=s).
have -> : zext 1 ((i32<=i8 he Hhe `>> 1) `% 31) = (i32<=i8 he Hhe `>> 1).
  rewrite shrl_rem.
  apply u2Z_inj.
  by rewrite u2Z_eq_rect.
symmetry.
apply shrl_shl.
rewrite Z2uK // (_ : 0%Z = u2Z (Z2u 1 0)) in H; last by rewrite Z2uK.
by move/u2Z_inj: H.
Opaque eval beval.
Qed.

Local Close Scope machine_int_scope.

Lemma b_le_trans_L a b (c : exp sigma (ityp: sint)) :
  (- 2 ^^ 31 <= b <= a)%Z -> (a < 2 ^^ 31)%Z ->
  `! \b [ a ]sc \<= c ===> `! \b [ b ]sc \<= c.
Proof.
move=> Hba Ha s h [] H1.
rewrite /emp => ?; subst h.
split => //.
Transparent eval beval.
move: H1 => /=.
move Hc : ( [ c ]_s ) => [hc Hhc].
rewrite 2!i8_of_i32K Z2sK; last omega.
rewrite Z2sK; last omega.
case: ifP => [H1 _ | ]; last by rewrite is_zero_0.
case: ifP; first by rewrite not_is_zero_1.
move/leZP/Znot_le_gt => H2.
exfalso.
move/leZP in H1; omega.
Opaque eval beval.
Qed.

Lemma b_le_trans_R a b (c : exp sigma (ityp: sint)) :
  (- 2 ^^ 31 <= a <= b)%Z -> (b < 2 ^^ 31)%Z ->
  `! \b c \<= [ a ]sc ===> `! \b c \<= [ b ]sc.
Proof.
move=> Hab Ha s h [] H1.
rewrite /emp => ?; subst h.
split => //.
Transparent eval beval.
move: H1 => /=.
move Hc : ( [ c ]_s ) => [hc Hhc].
rewrite 2!i8_of_i32K Z2sK; last omega.
rewrite Z2sK; last omega.
case: ifP => [H1 _ | ]; last by rewrite is_zero_0.
case: ifP; first by rewrite not_is_zero_1.
move/leZP/Znot_le_gt => H2.
exfalso.
move/leZP in H1; omega.
Opaque eval beval.
Qed.

End C_Contrib_f.

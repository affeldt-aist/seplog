(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ZArith EqNat Classical.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrnat_ext.
Require Import integral_type seplog frag.
Require Import topsy_hm topsy_hmInit_prg.

Require Import expr_b_dp.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.

Local Close Scope Z_scope.
Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_hoare_scope.

(** This file contains the verification of hmInit in two flavors:
  (1) semi-automatic using the "frag" tactic, (2) manual. *)

Definition hmInit_specif := forall p sz, sz >= 4 ->
  {{ Array p sz }} hmInit p sz {{ Heap_List ((sz - 4, topsy_hm.free) :: nil) p }}.

Definition hmInit_precond (adr sz : nat) :=
  (true_b, star
    (star (cell (nat_e adr)) (cell (nat_e adr \+ cst_e 1%Z)))
    (star (cell (nat_e adr \+ nat_e sz \- cst_e 2%Z)) (cell (nat_e adr \+ nat_e sz \- cst_e 1%Z)))).

Definition hmInit_postcond (adr sz : nat):=
  (true_b, star
    (star (singl (nat_e adr) Free) (singl (nat_e adr \+ cst_e 1%Z) (nat_e adr \+ nat_e sz \- cst_e 2%Z)))
    (star (singl (nat_e adr \+ nat_e sz \- cst_e 2%Z) Allocated)
      (singl (nat_e adr \+ nat_e sz \- cst_e 1%Z) (nat_e 0)))).

Lemma frag_precond startp sizep : sizep >= 4 ->
  Array startp sizep ===> assrt_interp (hmInit_precond startp sizep) ** Array (startp + 2) (sizep - 4).
Proof.
move=> H.
rewrite /while.entails => s h H0.
TArray_concat_split_l_l 2 H; clear H0.
case_sepcon H1.
TArray_concat_split_l_r 2 H1_h2; clear H1_h2.
case_sepcon H0.
Compose_sepcon (h1 \U h22) h21.
rewrite /=; split; first by done.
Compose_sepcon h1 h22.
simpl in H1_h1.
case_sepcon H1_h1.
case_sepcon H1_h1_h12.
Compose_sepcon h11 h121; auto.
case: H1_h1_h12_h121 => x ?; exists x; by Mapsto.
simpl in H0_h22.
case_sepcon H0_h22.
case_sepcon H0_h22_h222.
Compose_sepcon h221 h2221; auto.
case: H0_h22_h221 => x ?; exists x; by Mapsto.
case: H0_h22_h222_h2221 => x ?; exists x; by Mapsto.
by Array_equiv.
Qed.

Lemma frag_postcond startp sizep : sizep >= 4 ->
  assrt_interp (hmInit_postcond startp sizep) ** Array (startp + 2) (sizep - 4) ===>
  Heap_List ((sizep - 4, true) :: nil) startp.
Proof.
move=> H s h H0.
case_sepcon H0.
rewrite /= in H0_h1; case H0_h1 => _ H5.
case_sepcon H5.
Compose_sepcon (h11 \U h2) h12.
eapply hl_Free with (h1 := h11 \U h2) (h2 := heap.emp); [by map_tac_m.Disj | by map_tac_m.Equal | auto | intuition | idtac | idtac].
case_sepcon H5_h11.
Compose_sepcon h11 h2; [idtac | by Array_equiv].
simpl; Compose_sepcon h111 h112; first by done.
Compose_sepcon h112 heap.emp; by [Mapsto | red; auto].
by apply hl_last.
case_sepcon H5_h12.
simpl; Compose_sepcon h121 h122.
by Mapsto.
Compose_sepcon h122 assert_m.heap.emp; by [Mapsto | red; auto].
Qed.

Lemma hmInit_verif_auto : hmInit_specif.
Proof.
rewrite /hmInit_specif /hmInit.
move=> p size H.
eapply hoare_prop_m.hoare_weak.
- by apply (frag_postcond p size H).
- eapply hoare_prop_m.hoare_stren.
  by apply (frag_precond p size H).
  Frame_rule (Array (p + 2) (size - 4)); [idtac | eapply Array_inde_list].
  rewrite /hmInit_precond /hmInit_postcond /hmStart /hmEnd /next /status /Allocated /Free.
  eapply LWP_use.
  + rewrite /=; reflexivity.
  + by LWP_Resolve.
Qed.

Lemma hmInit_verif_manual : hmInit_specif.
Proof.
rewrite /hmInit_specif /hmInit => p sz H.

(**
<<
hmStart <- nat_e p;
>>
*)

Step (fun s h => Array p sz s h /\ [ var_e hmStart \= nat_e p ]b_s).

rewrite /wp_assign.
Resolve_topsy.
by Array_equiv.

(**
<<
hmStart -.> next *<- (nat_e p \+ nat_e size) \- cst_e 2%Z;
>>
*)

Step (fun s h => (Array p 1 **
  (var_e hmStart \+ nat_e 1 |~> nat_e p \+ nat_e sz \- cst_e 2%Z) **
  Array (p + 2) (sz - 2)) s h /\ [ var_e hmStart \= nat_e p ]b_s).

case : H0 => H1 H2.
TArray_concat_split_l_l 2 H2.
case_sepcon H0.
rewrite /= in H0_h1; case_sepcon H0_h1.
case_sepcon H0_h1_h12.
case : H0_h1_h12_h121 => x H0_h1_h12_h121.
exists (cst_e x).
Compose_sepcon h121 (h2 \U h11).
- rewrite /next; by Mapsto.
- rewrite /imp => h121' [X1 X2] h' Hh'.
  split; last by assumption.
  rewrite -conAE.
  Compose_sepcon (h11 \U h121') h2; last by assumption.
  Compose_sepcon h11 h121'; last by assumption.
  by Compose_sepcon h11 heap.emp.

(**
<<
hmStart -.> status *<- Free;
>>
*)

Step (fun s h => (var_e hmStart |~> Free **
    var_e hmStart \+ nat_e 1 |~> nat_e p \+ nat_e sz \- cst_e 2%Z **
    Array (p + 2) (sz - 2)) s h /\ [ var_e hmStart \= nat_e p ]b_s).

case : H0 => H1 H2.
rewrite -conAE in H1.
case_sepcon H1.
case_sepcon H1_h1.
rewrite /= in H1_h1_h11; case_sepcon H1_h1_h11.
case : H1_h1_h11_h111 => x H1_h1_h11_h111.
exists (cst_e x).
Compose_sepcon h111 (h12 \U h2).
- rewrite /status; by Mapsto.
- rewrite /imp => h111' [X1 X2] h' Hh'.
  split; last by assumption.
  rewrite -conAE.
  Compose_sepcon (h111' \U h12) h2; last by assumption.
  Compose_sepcon h111' h12; last by assumption.
  rewrite /status in X2; by Mapsto.

(**
<<
hmEnd <-* hmStart -.> next;
>>
*)

Step (fun s h => (var_e hmStart |~> Free **
    var_e hmStart \+ nat_e 1 |~> nat_e p \+ nat_e sz \- cst_e 2%Z **
    Array (p + 2) (sz - 2)) s h /\ [ var_e hmStart \= nat_e p ]b_s /\
  [ var_e hmEnd \= nat_e p \+ nat_e sz \- cst_e 2%Z ]b_s).

case : H0 => H1 H2.
rewrite -conAE in H1.
case_sepcon H1.
case_sepcon H1_h1.
exists ((nat_e p \+ nat_e sz) \- cst_e 2%Z).
Compose_sepcon h12 (h11 \U h2).
- rewrite /next; by Mapsto.
- rewrite /imp => h12' [X1 X2] h' Hh'.
  rewrite /wp_assign; split.
  + rewrite -conAE.
    Compose_sepcon (h11 \U h12') h2.
    Compose_sepcon h11 h12'; apply mapsto_store_upd_subst => /=; by Mapsto.
    by Array_equiv.
  + by Resolve_topsy.

(**
<<
hmEnd -.> next *<- cst_e 0%Z;
>>
*)

Step (fun s h => (var_e hmStart |~> Free **
  var_e hmStart \+ nat_e 1 |~> nat_e p \+ nat_e sz \- cst_e 2%Z **
    Array (p + 2) (sz - 4) ** Array (p + sz - 2) 1 **
    (var_e hmEnd \+ nat_e 1|~> cst_e 0%Z)) s h /\
  [ var_e hmStart \= nat_e p ]b_s /\
  [ var_e hmEnd \= nat_e p \+ nat_e sz \- cst_e 2%Z ]b_s ).

case: H0 => H1 [H3 H4].
rewrite -conAE in H1.
case_sepcon H1.
case_sepcon H1_h1.
TArray_concat_split_l_l (sz - 4) H6.
case_sepcon H0.
rewrite (_ : sz - 2 - (sz - 4) = 2) /= in H0_h22; last by ssromega.
case_sepcon H0_h22.
case_sepcon H0_h22_h222.
case: H0_h22_h222_h2221 => x H0_h22_h222_h2221.
exists (cst_e x).
Compose_sepcon h2221 (h221 \U h21 \U h1).
- rewrite /next; by Mapsto.
- rewrite /imp => h2221' [X1 X2] h' Hh'.
  split.
    rewrite -3!conAE.
    Compose_sepcon (h221 \U h21 \U h1) h2221'; last by Mapsto.
    Compose_sepcon (h21 \U h1) h221.
    Compose_sepcon h1 h21.
    Compose_sepcon h11 h12; by Mapsto.
    by Array_equiv.
  rewrite /=; Compose_sepcon h221 heap.emp; last by done.
  case: H0_h22_h221 => x0 H0_h22_h221.
  exists x0; by Mapsto.
  by Resolve_topsy.

(**
<<
hmEnd -.> status *<- Allocated
>>
*)

Step TT.

rewrite /while.entails => s h [H1 [H3 h4]].
rewrite -3!conAE in H1.
case_sepcon H1.
case_sepcon H1_h1.
case_sepcon H1_h1_h11.
case_sepcon H1_h1_h11_h111.
rewrite /= in H1_h1_h12; case_sepcon H1_h1_h12.
case: H1_h1_h12_h121 => x H1_h1_h12_h121.
exists (cst_e x).
Compose_sepcon h121 (h122 \U h11 \U h2).
- rewrite /status; by Mapsto.
- rewrite /imp => h121' [X1 X2] h' Hh'.
  Compose_sepcon (h11 \U h122) (h121' \U h2).
  + eapply hl_Free with (h1 := h11 \U h122) (h2 := heap.emp).
    * by map_tac_m.Disj.
    * by map_tac_m.Equal.
    * reflexivity.
    * reflexivity.
    * Compose_sepcon (h1111 \U h1112) h112; last by assumption.
      Compose_sepcon h1111 h1112; first by Mapsto.
      Compose_sepcon h1112 heap.emp; [by Mapsto | done].
    * by apply hl_last.
  + rewrite /mapstos /=.
    Compose_sepcon h121' h2.
    rewrite /status in X2; by Mapsto.
    Compose_sepcon h2 heap.emp; [by Mapsto | done].
Qed.

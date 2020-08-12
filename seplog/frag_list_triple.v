(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import List Classical.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ZArith_ext Max_ext ssrnat_ext seq_ext.
Require Import bipl seplog.
Require Import frag_list_entail.

Local Close Scope Z_scope.
Local Close Scope positive_scope.
Require Import integral_type.

Require Import expr_b_dp.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_hoare_scope.

Inductive wpAssrt : Type :=
| wpElt : Assrt -> wpAssrt
| wpSubst : list (var.v * expr) -> wpAssrt -> wpAssrt
| wpLookup : var.v -> expr -> wpAssrt -> wpAssrt
| wpMutation : expr -> expr -> wpAssrt -> wpAssrt
| wpIf : expr_b -> wpAssrt -> wpAssrt -> wpAssrt.

Fixpoint wpAssrt_interp (a: wpAssrt) : assert :=
  match a with
    wpElt a1 => Assrt_interp a1
    | wpSubst l L => wp_assigns l (wpAssrt_interp L)
    | wpLookup x e L => (fun s h => exists e0, (e |~> e0 ** (e |~> e0 -* (wp_assign x e0 (wpAssrt_interp L)))) s h)
    | wpMutation e1 e2 L => (fun s h => exists e0, (e1 |~> e0 ** (e1 |~> e2 -* (wpAssrt_interp L))) s h)
    | wpIf b L1 L2 =>
      (fun s h => ([ b ]b_ s -> wpAssrt_interp L1 s h) /\
                  (~~ [ b ]b_ s -> wpAssrt_interp L2 s h))
  end.

Local Open Scope entail_scope.

Fixpoint subst_Sigma (a : Sigma) (x : var.v) (e : expr) {struct a} : Sigma :=
  match a with
    | singl e1 e2 => singl (subst_e e1 (var_e x) e) (subst_e e2 (var_e x) e)
    | frag_list_entail.emp => frag_list_entail.emp
    | s1 \** s2 => subst_Sigma s1 x e \** subst_Sigma s2 x e
    | cell e1 => cell (subst_e e1 (var_e x) e)
    | lst e1 e2 => lst (subst_e e1 (var_e x) e) (subst_e e2 (var_e x) e)
  end.

Definition subst_assrt (a : assrt) (x : var.v) (e : expr) : assrt :=
  match a with
    (pi, sigm) => (subst_b pi (var_e x) e, subst_Sigma sigm x e)
  end.

Fixpoint subst_Assrt (a : Assrt) (x : var.v) (e : expr) {struct a} : Assrt :=
  match a with
    | nil => nil
    | hd :: tl => subst_assrt hd x e :: subst_Assrt tl x e
  end.

Fixpoint subst_assrt_lst (l : list (var.v * expr)) (a : assrt) {struct l} : assrt :=
  match l with
    | nil => a
    | (x, e) :: tl => subst_assrt_lst tl (subst_assrt a x e)
  end.

Fixpoint subst_Assrt_lst (l : list (var.v * expr)) (a : Assrt) {struct l} : Assrt :=
  match l with
    | nil => a
    | (x, e) :: tl => subst_Assrt_lst tl (subst_Assrt a x e)
  end.

(** properties of substitution functions *)

Lemma subst_Sigma2store_update : forall sigm s h x v,
  Sigma_interp (subst_Sigma sigm x v) s h ->
  Sigma_interp sigm (store.upd x (eval v s) s) h.
Proof.
induction sigm; simpl; intros; auto.
- case : H => H0 H1.
  split.
  Mapsto; by rewrite -!eval_upd_subst.
  by rewrite !eval_upd_subst.
  case: H => H0 H1.
  split.
  case: H0 => x0 H.
  exists x0.
  Mapsto; by rewrite -!eval_upd_subst.
  by rewrite !eval_upd_subst.
- case_sepcon H.
  Compose_sepcon h1 h2.
  by apply IHsigm1.
  by apply IHsigm2.
- eapply Lst_equiv'.
  apply H.
  by rewrite -!eval_upd_subst.
  by rewrite -!eval_upd_subst.
Qed.

Lemma subst_Sigma2store_update': forall sigm s h x v,
  Sigma_interp sigm (store.upd x (eval v s) s) h ->
  Sigma_interp (subst_Sigma sigm x v) s h.
Proof.
induction sigm; simpl; intros; auto.
- inversion_clear H.
  split.
  Mapsto; by rewrite -!eval_upd_subst.
  by rewrite -!eval_upd_subst.
- case : H => H0 H1.
  case : H0 => x0 H.
  split.
  exists x0.
  Mapsto; by rewrite !eval_upd_subst.
  by rewrite -!eval_upd_subst.
- case_sepcon H.
  Compose_sepcon h1 h2.
  by apply IHsigm1.
  by apply IHsigm2.
- eapply Lst_equiv'.
  apply H.
  by rewrite -!eval_upd_subst.
  by rewrite !eval_upd_subst.
Qed.

Lemma subst_Assert2store_update : forall A s h x v,
  Assrt_interp (subst_Assrt A x v) s h ->
  Assrt_interp A (store.upd x (eval v s) s) h.
Proof.
induction A; simpl; auto.
intros.
inversion_clear H.
left.
destruct a.
simpl; simpl in H0.
inversion_clear H0.
split.
by rewrite eval_b_upd_subst.
by apply subst_Sigma2store_update.
right.
by apply IHA.
Qed.

Lemma wp_assigns_assrt_interp: forall l s h pi sigm,
  assrt_interp (subst_assrt_lst l (pi, sigm)) s h ->
  wp_assigns l (assrt_interp (pi, sigm)) s h.
Proof.
induction l; simpl; intros; auto.
induction a; simpl.
move: (IHl _ _ _ _ H) => H0.
rewrite (_ :  wp_assign a b
  (fun s0 (h0 : assert_m.heap.t) =>
    [ pi ]b_ s0 /\ Sigma_interp sigm s0 h0) =
  assrt_interp (subst_b pi (var_e a) b, subst_Sigma sigm a b)) //.
rewrite /wp_assign /=.
apply assert_m.assert_ext => s0 h0; split => [ [H1 H2] | [H1 H2] ].
- rewrite eval_b_upd_subst in H1.
  split; first by [].
  by apply subst_Sigma2store_update'.
- rewrite -eval_b_upd_subst in H1.
  split; first by [].
  by apply subst_Sigma2store_update.
Qed.

Lemma wp_assigns_Assrt_interp: forall l A s h,
  Assrt_interp (subst_Assrt_lst l A) s h ->
  wp_assigns l (Assrt_interp A) s h.
Proof.
induction l; simpl; intros; auto.
induction a; simpl.
move: (IHl _ _ _ H) => H0.
eapply entails_wp_assigns; [idtac | eapply H0].
rewrite/while.entails /wp_assign; intros.
by apply subst_Assert2store_update.
Qed.

(* a module for fresh variables (w.r.t. syntactic constructs) *)
Module Type FRESH.

Parameter fresh_Sigma : var.v -> Sigma -> bool.

Parameter fresh_assrt : var.v -> assrt -> bool.

Parameter fresh_wpAssrt : var.v -> wpAssrt -> bool.

Parameter fresh_cmd : var.v -> @while.cmd cmd0 expr_b -> bool.

Parameter fresh_wpAssrt_inde: forall L x , fresh_wpAssrt x L ->
  inde (x::nil) (wpAssrt_interp L).

End FRESH.

Module Fresh <: FRESH.

Fixpoint var_max_Sigma (s: Sigma) : var.v :=
  match s with
    | singl e1 e2 => max (max_lst (vars e1)) (max_lst (vars e2))
    | frag_list_entail.emp => 0
    | s1 \** s2 => max (var_max_Sigma s1) (var_max_Sigma s2)
    | cell e1 => max_lst (vars e1)
    | lst e1 e2 => max (max_lst (vars e1)) (max_lst (vars e2))
  end.

Definition var_max_assrt (a: assrt) : var.v :=
  match a with
    (pi, sigm) => max (max_lst (vars_b pi)) (var_max_Sigma sigm)
  end.

Fixpoint var_max_Assrt (a: Assrt) : var.v :=
  match a with
    | nil => 0
    | hd::tl => max (var_max_assrt hd) (var_max_Assrt tl)
  end.

Fixpoint var_max_wpAssrt (a: wpAssrt) : var.v :=
  match a with
    wpElt a1 => var_max_Assrt a1
    | wpSubst l L => max (var_max_lst l) (var_max_wpAssrt L)
    | wpLookup x e L=> max (max x (max_lst (vars e))) (var_max_wpAssrt L)
    | wpMutation e1 e2 L => max (max (max_lst (vars e1)) (max_lst (vars e2))) (var_max_wpAssrt L)
    | wpIf b L1 L2 => max (max (var_max_wpAssrt L1) (var_max_wpAssrt L2)) (max_lst (vars_b b))
  end.

Fixpoint var_max_cmd (c: @while.cmd cmd0 expr_b) : var.v :=
  match c with
    skip => 0
    | assign x e => max (max_lst (vars e)) x
    | lookup x e => max (max_lst (vars e)) x
    | mutation e1 e2 => max (max_lst (vars e1)) (max_lst (vars e2))
    | malloc x e => max (max_lst (vars e)) x
    | free e => max_lst (vars e)
    | while.while b c' => max (max_lst (vars_b b)) (var_max_cmd c')
    | while.seq c1 c2 => max (var_max_cmd c1) (var_max_cmd c2)
    | while.ifte b c1 c2 => max (max (var_max_cmd c1) (var_max_cmd c2)) (max_lst (vars_b b))
  end.

Definition fresh_Sigma x s := var_max_Sigma s < x.

Definition fresh_assrt x a := var_max_assrt a < x.

Definition fresh_Assrt x a := var_max_Assrt a < x.

Definition fresh_wpAssrt x L := var_max_wpAssrt L < x.

Definition fresh_cmd x c := var_max_cmd c < x.

Ltac open_fresh_frag_list :=
  open_fresh_frag_list_hypo; open_fresh_frag_list_goal
with
  open_fresh_frag_list_hypo := match goal with
    | H: is_true (fresh_e _ _) |- _ => unfold fresh_e in H; simpl in H; open_fresh_frag_list_hypo
    | H: is_true (fresh_b _ _)  |- _ => unfold fresh_b in H; simpl in H; open_fresh_frag_list_hypo
    | H: is_true (fresh_Sigma _ _) |- _ => unfold fresh_Sigma in H; simpl in H; open_fresh_frag_list_hypo
    | H: is_true (fresh_assrt _ _) |- _ => unfold fresh_assrt in H; simpl in H; open_fresh_frag_list_hypo
    | H: is_true (fresh_lst _ _) |- _ => unfold fresh_lst in H; simpl in H; open_fresh_frag_list_hypo
    | H: is_true (fresh_wpAssrt _ _) |- _ => unfold fresh_wpAssrt in H; simpl in H; open_fresh_frag_list_hypo
    | H: context [ var_max_assrt _ ] |- _ => unfold var_max_assrt  in H; simpl in H; open_fresh_frag_list_hypo
    | |- _ =>  idtac
  end
with
  open_fresh_frag_list_goal :=
  match goal with
    | |- is_true (fresh_e _ _) => rewrite /fresh_e /=; open_fresh_frag_list_goal
    | |- is_true (fresh_b _ _) => rewrite /fresh_b /=; open_fresh_frag_list_goal
    | |- is_true (fresh_Sigma _ _) => rewrite /fresh_Sigma /=; open_fresh_frag_list_goal
    | |- is_true (fresh_assrt _ _) => rewrite /fresh_assrt /=; open_fresh_frag_list_goal
    | |- is_true (fresh_lst _ _) => rewrite /fresh_lst /=; open_fresh_frag_list_goal
    | |- is_true (fresh_wpAssrt _ _) => rewrite /fresh_wpAssrt /=; open_fresh_frag_list_goal
    | |- context [var_max_assrt _ ] => rewrite /var_max_assrt /=; open_fresh_frag_list_goal
    | |- _ => idtac
  end.

Ltac Max_inf_resolve := open_fresh_frag_list; Resolve_lt_max.

(** relations between freshness predicates and the independence predicate ("inde") *)

Lemma var_max_Sigma_inde : forall sigm x, fresh_Sigma x sigm ->
  inde (x :: nil) (Sigma_interp sigm).
Proof.
elim.
- move=> e e0 x H; rewrite /inde => s h x0 v; rewrite mem_seq1 => /eqP ?; subst x0; split => /= H1.
  + case : H1 => [[x1 H1] H3]; split.
    * exists x1.
      rewrite fresh_e_eval; last by Max_inf_resolve.
      rewrite fresh_e_eval //; by Max_inf_resolve.
    * rewrite fresh_e_eval //; by Max_inf_resolve.
  + case : H1 => [[x1 [H2 H4]] H3]; split.
    * exists x1.
      rewrite fresh_e_eval // in H2; last by Max_inf_resolve.
      rewrite fresh_e_eval // in H4; by Max_inf_resolve.
    * rewrite fresh_e_eval // in H3; by Max_inf_resolve.
- intros; red; simpl; split; intros; rewrite mem_seq1 in H0; move/eqP in H0; subst x0.
  + case : H1 => [ [x1 [x2 [H2 H4]] ] H3]; split.
    * exists x1, x2.
      rewrite fresh_e_eval //; by Max_inf_resolve.
    * rewrite fresh_e_eval //; by Max_inf_resolve.
  + case : H1 => [ [x1 [ x2 H2] ] H3]; split.
    * exists x1, x2.
      rewrite fresh_e_eval // in H2; by Max_inf_resolve.
    * rewrite fresh_e_eval // in H3; by Max_inf_resolve.
- intros; red; simpl; split; intros.
  + red in H1; by rewrite H1.
  + by rewrite H1.
- move=> s1 IH1 s2 IH2 x H; rewrite /inde => s h x0 v; rewrite mem_seq1 => /eqP ?; subst x0; split => /= H1.
  + case_sepcon H1.
    Compose_sepcon h1 h2.
    * have /IH1 : fresh_Sigma x s1 by Max_inf_resolve.
      move/(_ s h1 x v); rewrite mem_seq1 eqxx => /(_ isT); tauto.
    * have /IH2 : fresh_Sigma x s2 by Max_inf_resolve.
      move/(_ s h2 x v); rewrite mem_seq1 eqxx => /(_ isT); tauto.
  + case_sepcon H1.
    Compose_sepcon h1 h2.
    * have /IH1 : fresh_Sigma x s1 by Max_inf_resolve.
      move/(_ s h1 x v); rewrite mem_seq1 eqxx => /(_ isT); tauto.
    * have /IH2 : fresh_Sigma x s2 by Max_inf_resolve.
      move/(_ s h2 x v); rewrite mem_seq1 eqxx => /(_ isT); tauto.
- intros; red; simpl; split; intros; rewrite mem_seq1 in H0; move/eqP in H0; subst x0.
  + rewrite /fresh_Sigma /= in H.
    eapply Lst_equiv'.
    by apply H1.
    rewrite fresh_e_eval //; by Max_inf_resolve.
    rewrite fresh_e_eval //; by Max_inf_resolve.
  + rewrite /fresh_Sigma /= in H.
    eapply Lst_equiv'.
    by apply H1.
    rewrite fresh_e_eval //; by Max_inf_resolve.
    rewrite fresh_e_eval //; by Max_inf_resolve.
Qed.

Lemma fresh_assrt_inde: forall a x , fresh_assrt x a ->
  inde (x::nil) (assrt_interp a).
Proof.
case => a b /= x H.
have H0 : fresh_b x a by Max_inf_resolve.
have H1 : fresh_Sigma x b by Max_inf_resolve.
red; simpl; split.
- intros. case : H3 => H4 H5; split.
  case: (fresh_b_inde a x true H0 s h x0 v H2) => H3 _; by apply H3.
  case: (var_max_Sigma_inde b x H1 s h x0 v H2) => H3 _; by apply H3.
- intros. case : H3 => H4 H5; split.
  case: (fresh_b_inde a x true H0 s h x0 v H2) => H3; by apply.
  case: (var_max_Sigma_inde b x H1 s h x0 v H2) => H3; by apply.
Qed.

Lemma fresh_Assrt_inde : forall a x, fresh_Assrt x a ->
  inde (x::nil) (Assrt_interp a).
Proof.
induction a; simpl; intros; auto.
- red in H; red; split; simpl; intros; contradiction.
- rewrite /fresh_Assrt /= in H.
  red; simpl; split; intros; rewrite mem_seq1 in H0; move/eqP in H0; subst x0.
  + inversion_clear H1.
    * left.
      have H1 : fresh_assrt x a by Max_inf_resolve.
      apply (fresh_assrt_inde a x H1 s h x) => //; by rewrite mem_seq1.
    * right.
      have H1 : fresh_Assrt x a0 by rewrite /fresh_Assrt /=; Max_inf_resolve.
      apply (IHa x H1 s h x v) => //; by rewrite mem_seq1.
  - case : H1 => H2.
    * left.
      have H1 : fresh_assrt x a by rewrite /fresh_Assrt /=; by Max_inf_resolve.
      apply (fresh_assrt_inde a x H1 s h x v) => //; by rewrite mem_seq1.
    * right.
      have H0 : fresh_Assrt x a0 by rewrite /fresh_Assrt /=; by Max_inf_resolve.
      apply (IHa x H0 s h x v) => //; by rewrite mem_seq1.
Qed.

Lemma fresh_wpAssrt_inde: forall L x , fresh_wpAssrt x L ->
  inde (x::nil) (wpAssrt_interp L).
Proof.
induction L.
- simpl.
  red; simpl; split; intros.
  move: (fresh_Assrt_inde a x H s h x0 v H0); by intuition.
  move: (fresh_Assrt_inde a x H s h x0 v H0); by intuition.
- red; simpl; split; intros.
  have H2 : inde (x::nil) (wpAssrt_interp L) by apply IHL; Max_inf_resolve.
  have H3 : fresh_lst x l by Max_inf_resolve.
  case: (fresh_lst_inde _ _ _ H2 H3 s h x0 v H0); by intuition.
  have H2 : inde (x::nil) (wpAssrt_interp L) by apply IHL; Max_inf_resolve.
  have H3 : fresh_lst x l by Max_inf_resolve.
  case: (fresh_lst_inde _ _ _ H2 H3 s h x0 v H0); by intuition.
- red; simpl; split; intros; rewrite mem_seq1 in H0; move/eqP in H0; subst x0.
  inversion_clear H1.
  case_sepcon H0.
  exists (cst_e (eval x0 s0)).
  Compose_sepcon h1 h2.
  Mapsto.
  rewrite fresh_e_eval //; by Max_inf_resolve.
  move=> h1' [X1 X2] h' Hh'.
  red in H0_h2.
  have H8 : h2 # h1' /\ (e |~> x0) s0 h1'.
    split => //.
    Mapsto.
    rewrite fresh_e_eval //; by Max_inf_resolve.
  generalize (H0_h2 h1' H8 _ Hh') => H1.
  rewrite /wp_assign in H1 *.
  rewrite /= store.upd_upd; last by Max_inf_resolve.
  have H10 : fresh_wpAssrt x L by Max_inf_resolve.
  move: (IHL _ H10 (store.upd s (eval x0 s0) s0) h' x v) => X; apply X => //.
  by rewrite mem_seq1.
  case : H1 => x1 H2.
  case_sepcon H2.
  exists (cst_e (eval x1 (store.upd x v s0))).
  Compose_sepcon h1 h2.
  Mapsto.
  rewrite fresh_e_eval //; by Max_inf_resolve.
  move=> h1' [X1 X2] h' Hh'.
  red in H2_h2.
  have H8 : h2 # h1' /\ (e |~> x1) (store.upd x v s0) h1'.
    split; first by [].
    Mapsto.
    rewrite fresh_e_eval //; by Max_inf_resolve.
  generalize (H2_h2 h1' H8 _ Hh') => H1.
  rewrite /wp_assign in H1 *.
  rewrite /=.
  rewrite store.upd_upd in H1; last by Max_inf_resolve.
  have H10 : fresh_wpAssrt x L by Max_inf_resolve.
  move: (IHL _ H10 (store.upd s (eval x1 (store.upd x v s0)) s0) h' x v) => X; apply X => //.
  by rewrite mem_seq1.
- red; simpl; split; intros; rewrite mem_seq1 in H0; move/eqP in H0; subst x0.
  inversion_clear H1.
  case_sepcon H0.
  exists (cst_e (eval x0 s)).
  Compose_sepcon h1 h2.
  Mapsto.
  rewrite fresh_e_eval //; by Max_inf_resolve.
  move=> h1' [X1 X2] h' Hh'.
  red in H0_h2.
  have H8 : h2 # h1' /\ (e |~> e0) s h1'.
    split; first by [].
    Mapsto.
    rewrite fresh_e_eval //; by Max_inf_resolve.
    rewrite fresh_e_eval //; by Max_inf_resolve.
  generalize (H0_h2 _ H8 _ Hh'); intro H1.
  have H10 : fresh_wpAssrt x L by Max_inf_resolve.
  apply (IHL _ H10 s h' x v) => //; by rewrite mem_seq1.
  inversion_clear H1.
  case_sepcon H0.
  exists (cst_e (eval x0 (store.upd x v s))).
  Compose_sepcon h1 h2.
  Mapsto.
  rewrite fresh_e_eval //; by Max_inf_resolve.
  move=> h1' [X1 X2] h' Hh'.
  red in H0_h2.
  have H8 : h2 # h1' /\ (e |~> e0) (store.upd x v s) h1'.
    split; first by [].
    Mapsto.
    rewrite fresh_e_eval //; by Max_inf_resolve.
    rewrite fresh_e_eval //; by Max_inf_resolve.
  generalize (H0_h2 _ H8 _ Hh') => H1.
  have H10 : fresh_wpAssrt x L by Max_inf_resolve.
  move: (IHL _ H10 s h' x v) => X; apply X => //.
  by rewrite mem_seq1.
- red; simpl; split; intros; rewrite mem_seq1 in H0; move/eqP in H0; subst x0.
    case : H1 => H2 H3.
    split.
    intros.
    have H4 : fresh_wpAssrt x L1 by Max_inf_resolve.
    move: (IHL1 _ H4 s h x v) => H5; apply H5 => //.
    by rewrite mem_seq1.
    apply H2.
    have H7 : fresh_b x e by Max_inf_resolve.
    move: (fresh_b_inde e x true H7 s h x v) => X.
    apply X => //.
    by rewrite mem_seq1.
    have H4 : fresh_wpAssrt x L2 by Max_inf_resolve.
    move: (IHL2 _ H4 s h x v) => H5 H6.
    apply H5 => //.
    by rewrite mem_seq1.
    apply H3.
    have H7 : fresh_b x e by Max_inf_resolve.
    move: (fresh_b_inde e x false H7 s h x v) => X.
    apply/negbT/X.
    by rewrite mem_seq1.
    by apply/negbTE.
  case : H1 => H2 H3.
  split.
  intros.
  have H4 : fresh_wpAssrt x L1 by Max_inf_resolve.
  move: (IHL1 _ H4 s h x v) => H5.
  apply H5 => //.
  by rewrite mem_seq1.
  apply H2.
  have H7 : fresh_b x e by Max_inf_resolve.
  move: (fresh_b_inde e x true H7 s h x v) => H6; apply H6 => //.
  by rewrite mem_seq1.
  intros.
  have H4 : fresh_wpAssrt x L2 by Max_inf_resolve.
  move: (IHL2 _ H4 s h x v) => H5.
  apply H5.
  by rewrite mem_seq1.
  apply H3.
  have H7 : fresh_b x e by Max_inf_resolve.
  move: (fresh_b_inde e x false H7 s h x v) => X.
  apply/negbT/X => //.
  by rewrite mem_seq1.
  by apply/negbTE.
Qed.

End Fresh.

Import Fresh.

(** replace a substitution (e/x) by two substitutions (x/x')(e/x') with x' fresh *)
Lemma intro_fresh_var : forall l x x' e s h L,
  fresh_lst x' l -> fresh_wpAssrt x' L -> fresh_e x' (var_e x) ->
  wp_assigns
  l (fun s' h' => wpAssrt_interp L (store.upd x (eval (var_e x') s') s') h') (store.upd x' (eval e s) s) h ->
  wp_assigns
  l (fun s' h' => wpAssrt_interp L (store.upd x (eval e s) s') h') s h.
Proof.
intros.
apply intro_fresh_var' with x' => //.
by apply fresh_wpAssrt_inde.
Qed.

Definition triple_fresh (P : assrt) (L : wpAssrt) (x : var.v) : Prop := fresh_assrt x P /\ fresh_wpAssrt x L.

(** weakest pre-condition generator and its soudness *)

Fixpoint wp_frag (Q: option wpAssrt) (c: @while.cmd cmd0 expr_b) {struct c}: option wpAssrt :=
  match c with
    | skip => match Q with
                | None => None
                | Some Q' => Some Q'
              end
    | assign v e => match Q with
                      | None => None
                      | Some Q' => Some (wpSubst ((v, e) :: nil) Q')
                    end
    | lookup v e => match Q with
                      | None => None
                      | Some Q' => Some (wpLookup v e Q')
		    end
    | mutation e1 e2 => match Q with
                          | None => None
                          | Some Q' => Some (wpMutation e1 e2 Q')
			end
    | while.seq c1 c2 => wp_frag (wp_frag Q c2) c1
    | while.ifte b c1 c2 => match wp_frag Q c1 with
                                      | None => None
                                      | Some Q1 => match (wp_frag Q c2) with
                                                     None => None
                                                     | Some Q2 => Some (wpIf b Q1 Q2)
                                                   end
                                    end
    | while.while a c => None
    | malloc v e => None
    | free e => None
  end.

Lemma wp_frag_None_is_None : forall c, wp_frag None c = None.
Proof. elim=> //; first by case. by move=> c H c' /= ->. by move=> e c /= ->. Qed.

Lemma wp_frag_soudness : forall c Q Q',
  wp_frag (Some Q) c = Some Q' -> {{ wpAssrt_interp Q' }} c {{ wpAssrt_interp Q }}.
Proof.
induction c => //=.
- induction c => //=; intros.
  + case: H => H; subst Q'.
    by apply while.hoare_hoare0, hoare0_skip.
  + case : H => H /=; subst Q'.
    by apply while.hoare_hoare0, hoare0_assign.
  + case : H => H /=; subst Q'.
    by apply hoare_lookup_back.
  + case : H => H /=; subst Q'.
    by apply hoare_mutation_backwards.
- intros.
  have H0 : (exists v, wp_frag (Some Q) c2 = Some v) \/ wp_frag (Some Q) c2 = None.
    elim wp_frag.
    intros; left; exists a.
    auto.
    by right.
  inversion_clear H0.
  + inversion_clear H1.
    rewrite H0 in H.
    apply while.hoare_seq with (wpAssrt_interp x).
    by apply IHc1.
    by apply IHc2.
  + rewrite H1 in H.
    rewrite wp_frag_None_is_None in H.
    by inversion H.
- move=> Q Q' H.
  have [H1 | H1] : (exists v, wp_frag (Some Q) c1 = Some v) \/ wp_frag (Some Q) c1 = None.
    elim wp_frag.
    intros; left; by exists a.
    by right.
  + case: H1 => x H0.
    rewrite H0 in H.
    have [H2 | H2] : (exists v, wp_frag (Some Q) c2 = Some v) \/ wp_frag (Some Q) c2 = None.
      elim wp_frag.
      intros; left; by exists a.
      by right.
    * case : H2 => x0 H1.
      rewrite H1 in H.
      case : H => H; subst Q'.
      apply while.hoare_ifte.
      - apply hoare_prop_m.hoare_stren with (wpAssrt_interp x).
        red => /=; tauto.
        by apply IHc1.
      - apply hoare_prop_m.hoare_stren with (wpAssrt_interp x0).
        red => /=; tauto.
        by apply IHc2.
    * by rewrite H2 in H.
  + by rewrite H1 in H.
Qed.

Local Open Scope entail_scope.

Inductive tritra : assrt -> wpAssrt -> Prop :=
  | tritra_incons : forall pi sig Q,
    (forall s h, (assrt_interp (pi, sig) s h) -> False) ->
    tritra (pi, sig) Q

  | tritra_entail : forall P Q,
    assrt_interp P ===> Assrt_interp Q ->
    tritra P (wpElt Q)

  | tritra_precond_stre : forall L1 L1' L2,
    assrt_interp L1 ===> assrt_interp L1' ->
    tritra L1' L2 ->
    tritra L1 L2

  | tritra_if : forall pi1 sig1 L1 L2 b,
    tritra (pi1 \&& b, sig1)  L1 ->
    tritra (pi1 \&& (neg_b b), sig1) L2 ->
    tritra (pi1, sig1) (wpIf b L1 L2)

  | tritra_mutation : forall pi1 sig1 e1 e2 e3 e4 L,
    (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s ) ->
    tritra (pi1, sig1 \** singl e1 e4) L ->
    tritra (pi1, sig1 \** singl e1 e2) (wpMutation e3 e4 L)

  | tritra_mutation' : forall pi1 sig1 e1 e3 e4 L,
    (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s ) ->
    tritra (pi1, sig1 \** singl e1 e4) L ->
    tritra (pi1, sig1 \** cell e1) (wpMutation e3 e4 L)

  | tritra_lookup : forall pi1 sig1 e1 e2 e x L,
    (forall s, [ pi1 ]b_ s -> eval_b (e1 \= e) s ) ->
    tritra (pi1, sig1 \** singl e1 e2) (wpSubst ((x, e2) :: nil) L) ->
    tritra (pi1, sig1 \** singl e1 e2) (wpLookup x e L)

  | tritra_lookup' : forall pi1 sig1 e1 e x L x',
    (forall s, eval_b pi1 s -> [ e1 \= e ]b_ s ) ->
    fresh_assrt x' (pi1, sig1 \** cell e1) ->
    fresh_wpAssrt x' (wpLookup x e L) ->
    tritra (pi1, sig1 \** (singl e1 (var_e x'))) (wpSubst ((x,var_e x')::nil) L) ->
    tritra (pi1, sig1 \** cell e1) (wpLookup x e L)

  | tritra_subst_elt : forall pi1 sig1 l L,
    tritra (pi1, sig1) (wpElt (subst_Assrt_lst l L)) ->
    tritra (pi1, sig1) (wpSubst l (wpElt L))

  | tritra_subst_subst : forall pi1 sig1 l1 l2 L,
    tritra (pi1, sig1) (wpSubst (l2 ++ l1) L) ->
    tritra (pi1, sig1) (wpSubst l1 (wpSubst l2 L))

  | tritra_subst_lookup : forall pi1 sig1 e1 e2 e x x' l L,
    (forall s, eval_b pi1 s -> [ e1 \= subst_e_lst l e ]b_ s ) ->
    fresh_lst x' l ->
    fresh_wpAssrt x' L ->
    fresh_e x' (var_e x) ->
    tritra (pi1, sig1 \** singl e1 e2) (wpSubst ((x, var_e x') :: l ++ ((x', e2) :: nil)) L) ->
    tritra (pi1, sig1 \** singl e1 e2) (wpSubst l (wpLookup x e L))

  | tritra_subst_lookup' : forall pi1 sig1 e1 e x x' l L x'',
    (forall s, eval_b pi1 s -> [ e1 \= subst_e_lst l e ]b_ s ) ->
    fresh_lst x' l ->
    fresh_wpAssrt x' L ->
    fresh_e x' (var_e x) ->
    fresh_wpAssrt x'' (wpSubst l (wpLookup x e L)) ->
    fresh_assrt x'' (pi1, sig1 \** cell e1) ->
    tritra (pi1, sig1 \** singl e1 (var_e x'')) (wpSubst ((x, var_e x') :: l ++ ((x', var_e x'')::nil)) L) ->
    tritra (pi1, sig1 \** cell e1) (wpSubst l (wpLookup x e L))

  | tritra_subst_mutation : forall pi1 sig1 e1 e2 l L,
    tritra (pi1, sig1) (wpMutation (subst_e_lst l e1) (subst_e_lst l e2) (wpSubst l L)) ->
    tritra (pi1, sig1) (wpSubst l (wpMutation e1 e2 L))

  | tritra_subst_if : forall pi1 sig1 l b L1 L2,
    tritra (pi1, sig1) (wpIf (subst_b_lst l b) (wpSubst l L1) (wpSubst l L2)) ->
    tritra (pi1, sig1) (wpSubst l (wpIf b L1 L2))

  (* regle generale pour prouver de maniere plus simple les 4 du dessous *)

  | tritra_destruct_lst : forall pi1 sig1 e1 e2 L x',
    (forall s, [ pi1 ]b_ s -> [ e1 \!= e2 ]b_ s ) ->
    fresh_assrt x' (pi1, sig1 \** lst e1 e2) ->
    fresh_wpAssrt x' L ->
    tritra (pi1 \&& e1 \!= var_e x' \&& var_e x' \= nat_e 0,
      sig1 \** ((singl e1 (var_e x') \** (cell (e1 \+ nat_e 1))) \** (lst (var_e x') e2))) L ->
    tritra (pi1 \&& e1 \!= var_e x' \&& var_e x' \!= nat_e 0,
      sig1 \** ((singl e1 (var_e x') \** cell (e1 \+ nat_e 1)) \** lst (var_e x') e2)) L ->
    tritra (pi1, sig1 \** lst e1 e2) L.

Local Close Scope entail_scope.

Lemma tritra_soundness P Q : tritra P Q -> assrt_interp P ===> wpAssrt_interp Q.
Proof.
induction 1.
- rewrite /while.entails => s h; by move/H.
- rewrite /=; exact H.
- by apply (hoare_prop_m.entails_trans _ _ _ H IHtritra).
- rewrite /while.entails /= in IHtritra1 IHtritra2 *; intros.
  split=> [X|H2].
  + apply IHtritra1; by rewrite X andbC.
  + apply IHtritra2; split; [by rewrite (proj1 H1) /= H2 | exact (proj2 H1)].
- rewrite /while.entails /= => s h [pi1_true H3].
  case_sepcon H3.
  case : H3_h2 => H3_h2 H3_h2'.
  exists e2.
  move: {H}(H _ pi1_true) => H.
  Compose_sepcon h2 h1.
  by Mapsto.
  rewrite /imp => h2' [X1 X2] h' Hh'.
  apply IHtritra.
  split; first by exact pi1_true.
  Compose_sepcon h1 h2'; first by [].
  split; [by Mapsto | exact H3_h2'].
- rewrite /while.entails /= in IHtritra * => s h [pi1_true H3].
  case_sepcon H3.
  move: {H}(H _ pi1_true) => e1_e3.
  case : H3_h2 => [ [ v Hv] H3_h2].
  exists (cst_e v).
  Compose_sepcon h2 h1.
  by Mapsto.
  rewrite /imp => h2' [X1 X2] h' Hh'.
  apply IHtritra; split; first by exact pi1_true.
  Compose_sepcon h1 h2'; first by assumption.
  split; [by Mapsto | exact H3_h2].
- rewrite /while.entails /= in IHtritra * => s h [H2 H3].
  move: {H}(H _ H2) => H.
  case_sepcon H3.
  case : H3_h2 => H3_h2 H3_h2'.
  exists e2.
  Compose_sepcon h2 h1.
  by Mapsto.
  rewrite /imp => h2' [X1 X2] h' Hh'.
  apply IHtritra; split; first by [].
  Compose_sepcon h1 h2'; first by [].
  split; [by Mapsto | exact H3_h2'].
- rewrite /while.entails /= => s h [H4 H5].
  rewrite /while.entails in IHtritra.
  case_sepcon H5.
  case : H5_h2 => [ [x0 H5_h2] H5_h2'].
  have H7 : assrt_interp (pi1, star sig1 (singl e1 (var_e x'))) (store.upd x' x0 s) h.
    rewrite /=.
    split.
    + have Hx' : fresh_b x' pi1 by Max_inf_resolve.
      have : x' \in x'::nil by rewrite mem_seq1.
      case/(fresh_b_inde pi1 _ true Hx' s h x' x0) => X _; by apply X.
    + Compose_sepcon h1 h2.
      have Hx' : fresh_Sigma x' sig1 by Max_inf_resolve.
      have : x' \in x' :: nil by rewrite mem_seq1.
      case/(var_max_Sigma_inde sig1 _ Hx' s h1 x' x0)=> X _; by apply X.
      have Hx' : fresh_e x' e1 by Max_inf_resolve.
      split.
      Mapsto; by rewrite fresh_e_eval.
      by rewrite fresh_e_eval.
  move: (IHtritra _ _ H7) => /= H10.
  exists (cst_e (eval (var_e x') (store.upd x' x0 s))) => /=.
  Store_upd.
  Compose_sepcon h2 h1.
  + move: (H s H4) => H3; by Mapsto.
  + rewrite /imp => h' [X1 X2] h'' Hh''.
    rewrite /wp_assign /= in H10 *.
    rewrite store.get_upd' store.upd_upd in H10.
    have Hx' : fresh_wpAssrt x' L by Max_inf_resolve.
    have H12 : x' \in x' :: nil by rewrite mem_seq1.
    apply (proj2 (fresh_wpAssrt_inde L _ Hx' (store.upd x x0 s) h'' x' x0 H12)).
    have ? : h' = h2.
      apply (singl_equal _ _ _ _ _ _ _ X2 H5_h2) => //.
      move: (H s H4) => ?; by omegab.
    subst h'.
    by rewrite (_ : h'' = h); last by map_tac_m.Equal.
    by Max_inf_resolve.
- (* case tritra_subst_elt *) eapply hoare_prop_m.entails_trans; first by apply IHtritra.
  move=> s h; by move/ wp_assigns_Assrt_interp.
- (* case tritra_subst_subst *) rewrite /while.entails /= in IHtritra * => s h.
  move/IHtritra. by move/wp_assigns_app.
- (* case tritra_subst_lookup *) rewrite /while.entails /= in IHtritra * => s h [H7 H8].
  move: {IHtritra}(IHtritra _ _ (conj H7 H8)) => IHtritra.
  case_sepcon H8.
  case : H8_h2 => H8_h2 H8_h2'.
  apply (wp_assigns_exists l
    (fun e0 s h => (e |~> e0 ** (e |~> e0 -* wp_assign x e0 (wpAssrt_interp L))) s h)
    s h).
  exists (cst_e (eval e2 s)).
  have -> : (fun s0 h0 =>
    (e |~> cst_e (eval e2 s) ** (e |~> cst_e (eval e2 s) -* wp_assign x (cst_e (eval e2 s)) (wpAssrt_interp L))) s0 h0)
    =
    (e |~> cst_e (eval e2 s) ** (e |~> cst_e (eval e2 s) -* wp_assign x (cst_e (eval e2 s)) (wpAssrt_interp L))).
    apply assert_m.assert_ext.
    by intuition.
  apply wp_assigns_sepcon.
  move: (H _  H7) => H6.
  Compose_sepcon h2 h1.
  + apply wp_assigns_mapsto.
    Mapsto.
    by rewrite subst_e_lst_cst_e.
  + apply wp_assigns_sepimp.
    rewrite /imp => h2' [X1 X2] h' Hh'.
    rewrite /wp_assign /=.
    have ? : h2 = h2'.
      apply (singl_equal _ _ _ _ _ _ _ H8_h2 (wp_assigns_mapsto_inv _ _ _ _ _ X2)).
      by omegab.
      by rewrite subst_e_lst_cst_e.
    subst h2'.
    have <- : h = h' by map_tac_m.Equal.
    move/wp_assigns' : IHtritra => IHtritra.
    by apply intro_fresh_var with x'.
- (** case tritra_subst_lookup' *) rewrite /while.entails in IHtritra * => s h [H7 H8].
  rewrite /= in H8; case_sepcon H8.
  case : H8_h2 => [ [x0 H8_h2] H8_h2'].
  have H10 : assrt_interp (pi1, star sig1 (singl e1 (var_e x''))) (store.upd x'' x0 s) h.
    simpl.
    split.
    have H10 : fresh_b x'' pi1 by Max_inf_resolve.
    have H13 : x'' \in x'' :: nil by rewrite mem_seq1.
    by rewrite <- (fresh_b_inde pi1 x'' true H10 s h x'' x0 H13).
    Compose_sepcon h1 h2.
    have H10 : fresh_Sigma x'' sig1 by Max_inf_resolve.
    have H13 : x'' \in x'' :: nil by rewrite mem_seq1.
    by rewrite <- (var_max_Sigma_inde sig1 x'' H10 s h1 x'' x0 H13).
    have H10 : fresh_e x'' e1 by Max_inf_resolve.
    have H123 : In x'' (x''::nil) by left.
    split.
    Mapsto; by rewrite fresh_e_eval.
    by rewrite fresh_e_eval.
  move/IHtritra : H10 => H13.
  cut (wpAssrt_interp (wpSubst l (wpLookup x e L)) (store.upd x'' x0 s) h).
    move=> H10.
    have H14 : x'' \in x'' :: nil by rewrite mem_seq1.
    by rewrite -> (fresh_wpAssrt_inde (wpSubst l (wpLookup x e L)) x'' H3 s h x'' x0 H14).
  simpl.
  apply (wp_assigns_exists l
    (fun e0 s h => (e |~> e0 ** (e |~> e0 -* wp_assign x e0 (wpAssrt_interp L))) s h)
    (store.upd x'' x0 s) h).
  exists (cst_e x0).
  have -> : (fun s0 h0 =>
      (e |~> cst_e x0 ** (e |~> cst_e x0 -* wp_assign x (cst_e x0) (wpAssrt_interp L))) s0 h0)
    =
      (e |~> cst_e x0 ** (e |~> cst_e x0 -* wp_assign x (cst_e x0) (wpAssrt_interp L))).
    apply assert_m.assert_ext.
    by intuition.
  apply wp_assigns_sepcon.
  Compose_sepcon h2 h1.
  have H10 : inde (x''::nil) (e |~> cst_e x0).
    rewrite /inde; intros.
    rewrite mem_seq1 in H6; move/eqP in H6; subst x1.
    split; intros; Mapsto.
    rewrite fresh_e_eval //; by Max_inf_resolve.
    rewrite fresh_e_eval //; by Max_inf_resolve.
  have H14 : fresh_lst x'' l by Max_inf_resolve.
  have H15 : x'' \in x'' :: nil by rewrite mem_seq1.
  apply (proj1 (fresh_lst_inde l (e |~> cst_e x0) x'' H10 H14 s h2 x'' x0 H15)).
  apply wp_assigns_mapsto.
  move: (H s H7) => H16.
  Mapsto; by rewrite subst_e_lst_cst_e.
  apply wp_assigns_sepimp.
  rewrite /imp => h2' [X1 X2] h' Hh'.
  rewrite /wp_assign /=.
  have ? : h2 = h2'.
    have H16 : (e1 |~> cst_e x0) (store.upd x'' x0 s) h2.
      Mapsto.
      rewrite fresh_e_eval //; by Max_inf_resolve.
    apply (singl_equal _ _ _ _ _ _ _ H16 (wp_assigns_mapsto_inv _ _ _ _ _ X2)).
    rewrite fresh_e_eval; last by Max_inf_resolve.
    rewrite subst_e_lst_eval; last 2 first.
      by Max_inf_resolve.
      by Max_inf_resolve.
    generalize (H s H7) => ?; by omegab.
    by rewrite subst_e_lst_cst_e.
  subst h2'.
  have <- : h = h' by map_tac_m.Equal.
  rewrite /= in H13.
  move/wp_assigns' : H13 => H15.
  rewrite /wp_assign /= store.get_upd' in H15.
  suff : wp_assigns l
    (fun s0 h0 => wpAssrt_interp L (store.upd x ([ cst_e x0 ]e_ (store.upd x'' x0 s)) s0) h0)
    (store.upd x'' x0 s) h by [].
  by apply intro_fresh_var with x'.
- (** case tritra_subst_mutation *) rewrite /while.entails /= in IHtritra * => s h.
  move/IHtritra. by apply wp_assigns_lookup.
- (** case tritra_subst_if *) rewrite /while.entails /= in IHtritra * => s h.
  case/IHtritra => H2 H3.
  apply (wp_assigns_and l
    (fun s h => [ b ]b_ s  -> wpAssrt_interp L1 s h)
    (fun s h => ~~ [ b ]b_ s -> wpAssrt_interp L2 s h) s h).
  split.
  apply (wp_assigns_imp l (fun s h => eval_b b s) (fun s h => wpAssrt_interp L1 s h) s h) => H0.
  move: (H2 (wp_assigns_subst_b_lst true _ _ _ _ H0)) => H4.
  suff <- : wpAssrt_interp L1 = (fun s => fun h => wpAssrt_interp L1 s h) by [].
  apply assert_m.assert_ext; rewrite /while.equiv /=; tauto.
  apply (wp_assigns_imp l (fun s h => ~~ eval_b b s) (fun s h => wpAssrt_interp L2 s h) s h) => H0.
  move: (H3 (wp_assigns_subst_b_lst false _ _ _ _ H0)) => H4.
  suff <- : wpAssrt_interp L2 = (fun s => fun h => wpAssrt_interp L2 s h) by [].
  apply assert_m.assert_ext; rewrite /while.equiv /=; tauto.
- (** case regle generale *) rewrite /while.entails /= => s h {H2 H3} [H2 H3].
  case_sepcon H3.
  destruct H3_h2.
    move: (H _ H2) => H5; by omegab.
  case/boolP : (eval e2 s == 0%Z) => [/eqP X1|X1].
  + rewrite /assrt_interp /= in IHtritra1.
    cut (wpAssrt_interp L (store.upd x' (eval e2 s) s) h).
      move=> H13.
      have H14 : x' \in x' :: nil by rewrite mem_seq1.
      by apply (proj2 (fresh_wpAssrt_inde L x' H1 s h x' (eval e2 s) H14)).
    apply IHtritra1; split.
    have H13 : fresh_b x' pi1 by Max_inf_resolve.
    have H14 : x' \in x' :: nil by rewrite mem_seq1.
    apply/andP; split.
    apply/andP; split.
    by apply (proj1 (fresh_b_inde pi1 x' true H13 s h x' (eval e2 s) H14)).
    rewrite fresh_e_eval; last by Max_inf_resolve.
    rewrite store.get_upd'.
    have H15 : eval e1 s <> eval e2 s.
      destruct H3_h2.
      rewrite X1 //.
      case_sepcon H8.
      case_sepcon H16.
      apply (singl_disj_neq _ _ _ _ _ _ _ H8_h21 H16_h41); by map_tac_m.Disj.
    exact/eqP.
    Store_upd.
    by rewrite X1; apply/eqP.
    Compose_sepcon h1 h0.
    * have H13 : fresh_Sigma x' sig1 by Max_inf_resolve.
      have H14 : x' \in x' :: nil by rewrite mem_seq1.
      by apply (proj1 (var_max_Sigma_inde sig1 _ H13 s h1 x' (eval e2 s) H14)).
    * Compose_sepcon h2 h3.
      - case_sepcon H8.
        Compose_sepcon h21 h22.
        + split.
          * Mapsto; rewrite fresh_e_eval //; by Max_inf_resolve.
          * rewrite fresh_e_eval //; by Max_inf_resolve.
        + split.
          * exists (eval e4 s).
            Mapsto; rewrite fresh_e_eval //; by Max_inf_resolve.
          * rewrite fresh_e_eval //; by Max_inf_resolve.
        apply (Lst_equiv' _ _ _ _ H3_h2).
        rewrite /=; by Store_upd.
        rewrite fresh_e_eval //; by Max_inf_resolve.
  + rewrite /while.entails /= in IHtritra2.
    cut (wpAssrt_interp L (store.upd x' ([ e2 ]e_ s) s) h).
      move=> H13.
      have H14 : x' \in x' :: nil by rewrite mem_seq1.
      by apply (proj2 (fresh_wpAssrt_inde L x' H1 s h x' (eval e2 s) H14)).
    apply IHtritra2; split.
    have H13 : fresh_b x' pi1 by Max_inf_resolve.
    have H14 : x' \in x' :: nil by rewrite mem_seq1.
    apply/andP; split.
    apply/andP; split.
    by apply (proj1 (fresh_b_inde pi1 x' true H13 s h x' (eval e2 s) H14)).
    rewrite fresh_e_eval; last by Max_inf_resolve.
    rewrite store.get_upd'.
    have H15 : eval e1 s <> eval e2 s.
      destruct H3_h2.
      by rewrite H9.
      case_sepcon H8.
      case_sepcon H16.
      apply (singl_disj_neq _ _ _ _ _ _ _ H8_h21 H16_h41); by map_tac_m.Disj.
    exact/eqP.
    rewrite store.get_upd' //.
    Compose_sepcon h1 h0.
    have H13 : fresh_Sigma x' sig1 by Max_inf_resolve.
    have H14 : x' \in x' :: nil by rewrite mem_seq1.
    by apply (proj1 (var_max_Sigma_inde sig1 _ H13 s h1 x' (eval e2 s) H14)).
    Compose_sepcon h2 h3.
    * case_sepcon H8.
      Compose_sepcon h21 h22.
      - split.
        + Mapsto; rewrite fresh_e_eval //; by Max_inf_resolve.
        + rewrite fresh_e_eval //; by Max_inf_resolve.
      - split.
        + exists (eval e4 s).
          Mapsto; rewrite fresh_e_eval //; by Max_inf_resolve.
        + rewrite fresh_e_eval //; by Max_inf_resolve.
    * apply (Lst_equiv' _ _ _ _ H3_h2).
      by rewrite /= store.get_upd'.
      rewrite fresh_e_eval //; by Max_inf_resolve.
Qed.

Definition triple_vfresh (a : assrt) (L : wpAssrt) := (max (var_max_assrt a) (var_max_wpAssrt L)) + 1.

Lemma tritra_lookup_lst pi1 sig1 e1 e2 e x L x' :
  (forall s, eval_b pi1 s -> (eval_b (e1 \= e) s /\ eval_b (e1 \!= e2) s)) ->
  x' = triple_vfresh  (pi1, star sig1 (lst e1 e2)) (wpLookup x e L) ->
  tritra (pi1 \&& e1 \!= var_e x' \&& var_e x' \= nat_e 0,
    star (star sig1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))) (wpLookup x e L) ->
  tritra (pi1 \&& e1 \!= var_e x' \&& var_e x' \!= nat_e 0,
    star (star sig1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))) (wpLookup x e L) ->
  tritra (pi1, star sig1 (lst e1 e2)) (wpLookup x e L).
Proof.
move=> H H0 H1 H2.
unfold triple_vfresh in H0.
apply tritra_destruct_lst with (x' := x').
- move=> s; by case/H.
- rewrite /fresh_assrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- rewrite /fresh_wpAssrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- eapply tritra_precond_stre; [idtac | by apply H1].
  rewrite /while.entails => s h [H4 H5].
  split; first by [].
  simpl in H5; case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h212 \U h22 \U h1) h211; auto.
  Compose_sepcon h1 (h212 \U h22); auto.
  by Compose_sepcon h22 h212.
- eapply tritra_precond_stre; [idtac | by apply H2].
  rewrite /while.entails => s h [H4 H5].
  split; first by [].
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h212 \U h22 \U h1) h211; last by [].
  Compose_sepcon h1 (h212 \U h22); first by [].
  by Compose_sepcon h22 h212.
Qed.

Lemma tritra_lookup_lst' : forall pi1 sig1 e1 e2 e x L x',
  (forall s, eval_b pi1 s -> (eval_b (e1 \+ nat_e 1 \= e) s  /\ [ e1 \!= e2 ]b_ s )) ->
  x' = triple_vfresh  (pi1, star sig1 (lst e1 e2)) (wpLookup x e L) ->
  tritra (pi1 \&& e1 \!= var_e x' \&& (var_e x' \= nat_e 0),
    star (star sig1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))) (wpLookup x e L) ->
  tritra (pi1 \&& (e1 \!= var_e x') \&& (var_e x' \!= nat_e 0),
    star (star sig1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))) (wpLookup x e L) ->
  tritra (pi1, star sig1 (lst e1 e2)) (wpLookup x e L).
Proof.
intros.
unfold triple_vfresh in H0.
apply tritra_destruct_lst with (x' := x').
- move=> s; by case/H.
- rewrite /fresh_assrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- rewrite /fresh_wpAssrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- eapply tritra_precond_stre; last by apply H1.
  rewrite /while.entails => s h [H4 H5].
  split; first by [].
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h212 \U h22 \U h1) h211; auto.
  Compose_sepcon h1 (h212 \U h22); auto.
  by Compose_sepcon h22 h212.
- eapply tritra_precond_stre; [idtac | by apply H2].
  rewrite /while.entails => s h [H4 H5].
  split; auto.
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h212 \U h22 \U h1) h211; last by [].
  Compose_sepcon h1 (h212 \U h22); first by [].
  by Compose_sepcon h22 h212.
Qed.

Local Open Scope entail_scope.

Lemma tritra_subst_lookup_lst : forall pi1 sig1 e1 e2 e x L l x',
  (forall s, eval_b pi1 s  -> (eval_b (e1 \= (subst_e_lst l e)) s /\ [ e1 \!= e2 ]b_ s )) ->
  x' = triple_vfresh  (pi1, star sig1 (lst e1 e2)) (wpSubst l (wpLookup x e L)) ->
  tritra (pi1 \&& e1 \!= var_e x' \&& var_e x' \= nat_e 0,
    (star sig1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) \** singl e1 (var_e x')) (wpSubst l (wpLookup x e L)) ->
  tritra (pi1 \&& e1 \!= var_e x' \&& var_e x' \!= nat_e 0,
    (star sig1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) \** singl e1 (var_e x')) (wpSubst l (wpLookup x e L)) ->
  tritra (pi1, star sig1 (lst e1 e2)) (wpSubst l (wpLookup x e L)).
Proof.
intros.
unfold triple_vfresh in H0.
eapply tritra_destruct_lst with (x' := x').
- move=> s; by case/H.
- rewrite /fresh_assrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- rewrite /fresh_wpAssrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- eapply tritra_precond_stre; [idtac | by apply H1].
  rewrite /while.entails => s h [H4 H5].
  split; first by [].
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h212 \U h22 \U h1) h211; last by [].
  Compose_sepcon h1 (h212 \U h22); first by [].
  by Compose_sepcon h22 h212.
- eapply tritra_precond_stre; [idtac | by apply H2].
  rewrite /while.entails => s h [H4 H5].
  split; first by [].
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h212 \U h22 \U h1) h211; last by [].
  Compose_sepcon h1 (h212 \U h22); first by [].
  by Compose_sepcon h22 h212.
Qed.

Lemma tritra_subst_lookup_lst' : forall pi1 sig1 e1 e2 e x L l x',
  (forall s, eval_b pi1 s -> eval_b (e1 \+ nat_e 1 \= (subst_e_lst l e)) s /\ eval_b (e1 \!= e2) s ) ->
  x' = triple_vfresh  (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpLookup x e L)) ->
  tritra (pi1 \&& e1 \!= var_e x' \&& var_e x' \= nat_e 0,
    star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 \+ nat_e 1))) (wpSubst l (wpLookup x e L)) ->
  tritra (pi1 \&& (e1 \!= var_e x') \&& (var_e x' \!= nat_e 0),
    star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 \+ nat_e 1))) (wpSubst l (wpLookup x e L)) ->
  tritra (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpLookup x e L)).
Proof.
intros.
unfold triple_vfresh in H0.
apply tritra_destruct_lst with (x' := x').
- move=> s; by case/H.
- rewrite /fresh_assrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- rewrite /fresh_wpAssrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- eapply tritra_precond_stre; [idtac | by apply H1].
  rewrite /while.entails => s h [H4 H5].
  split; first by [].
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h211 \U h22 \U h1) h212; last by [].
  Compose_sepcon h1 (h211 \U h22); first by [].
  by Compose_sepcon h22 h211.
- eapply tritra_precond_stre; [idtac | by apply H2].
  rewrite /while.entails => s h [H4 H5].
  split; first by [].
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h211 \U h22 \U h1) h212; last by [].
  Compose_sepcon h1 (h211 \U h22); first by [].
  by Compose_sepcon h22 h211.
Qed.

Lemma tritra_mutation_lst : forall pi1 sig1 e1 e2 e3 e4 L x',
  (forall s, eval_b pi1 s -> (eval_b (e1 \= e3) s  /\ eval_b (e1 \!= e2) s )) ->
  x' = triple_vfresh (pi1, star sig1 (lst e1 e2)) (wpMutation e3 e4 L) ->
  tritra (pi1 \&& (e1 \!= var_e x') \&& (var_e x' \= nat_e 0),
    star (star sig1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))) (wpMutation e3 e4 L) ->
  tritra (pi1 \&& (e1 \!= var_e x') \&& (var_e x' \!= nat_e 0),
    star (star sig1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))) (wpMutation e3 e4 L) ->
  tritra (pi1,star sig1 (lst e1 e2)) (wpMutation e3 e4 L).
Proof.
intros.
unfold triple_vfresh in H0.
apply tritra_destruct_lst with (x' := x').
- move=> s; by case/H.
- rewrite /fresh_assrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- rewrite /fresh_wpAssrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- eapply tritra_precond_stre; [idtac | by apply H1].
  rewrite /while.entails => s h [H4 H5].
  split; auto.
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h212 \U h22 \U h1) h211; auto.
  Compose_sepcon h1 (h212 \U h22); auto.
  by Compose_sepcon h22 h212.
- eapply tritra_precond_stre; last by apply H2.
  rewrite /while.entails => s h [H4 H5].
  split; first by [].
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h212 \U h22 \U h1) h211; auto.
  Compose_sepcon h1 (h212 \U h22); auto.
  by Compose_sepcon h22 h212.
Qed.

Lemma tritra_mutation_lst' : forall pi1 sig1 e1 e2 e3 e4 L x',
  (forall s, eval_b pi1 s -> (eval_b (e1 \+ nat_e 1 \= e3) s /\ eval_b (e1 \!= e2) s )) ->
  x' = triple_vfresh (pi1, star sig1 (lst e1 e2)) (wpMutation e3 e4 L) ->
  tritra (pi1 \&& e1 \!= var_e x' \&& var_e x' \= nat_e 0,
    star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 \+ nat_e 1))) (wpMutation e3 e4 L) ->
  tritra (pi1 \&& (e1 \!= var_e x') \&& (var_e x' \!= nat_e 0),
    star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 \+ nat_e 1))) (wpMutation e3 e4 L) ->
  tritra (pi1, star sig1 (lst e1 e2)) (wpMutation e3 e4 L).
Proof.
intros.
unfold triple_vfresh in H0.
apply tritra_destruct_lst with (x' := x').
- move=> s; by case/H.
- rewrite /fresh_assrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- rewrite /fresh_wpAssrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- eapply tritra_precond_stre; [idtac | by apply H1].
  rewrite /while.entails => s h [H4 H5].
  split; auto.
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h211 \U h22 \U h1) h212; auto.
  Compose_sepcon h1 (h211 \U h22); auto.
  by Compose_sepcon h22 h211.
- eapply tritra_precond_stre; [idtac | by apply H2].
  rewrite /while.entails => s h [H4 H5].
  split; auto.
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h211 \U h22 \U h1) h212; last by [].
  Compose_sepcon h1 (h211 \U h22); first by [].
  by Compose_sepcon h22 h211.
Qed.

Lemma tritra_subst_mutation_lst : forall pi1 sig1 e1 e2 e3 e4 L l x',
  (forall s, eval_b pi1 s  -> (eval_b (e1 \= (subst_e_lst l e3)) s  /\ eval_b (e1 \!= e2) s )) ->
  x' = triple_vfresh (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpMutation e3 e4 L))->
  tritra (pi1 \&& (e1 \!= var_e x') \&& (var_e x' \= nat_e 0),
    star (star sig1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))) (wpSubst l (wpMutation e3 e4 L)) ->
  tritra (pi1 \&& (e1 \!= var_e x') \&& (var_e x' \!= nat_e 0),
    star (star sig1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))) (wpSubst l (wpMutation e3 e4 L)) ->
  tritra (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpMutation e3 e4 L)).
Proof.
intros.
unfold triple_vfresh in H0.
apply tritra_destruct_lst with (x' := x').
- move=> s; by case/H.
- rewrite /fresh_assrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- rewrite /fresh_wpAssrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- eapply tritra_precond_stre; last by apply H1.
  rewrite /while.entails => s h [H4 H5].
  split; auto.
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h212 \U h22 \U h1) h211; auto.
  Compose_sepcon h1 (h212 \U h22); auto.
  by Compose_sepcon h22 h212.
- eapply tritra_precond_stre; last by apply H2.
  rewrite /while.entails => s h [H4 H5].
  split; auto.
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h212 \U h22 \U h1) h211; auto.
  Compose_sepcon h1 (h212 \U h22); auto.
  by Compose_sepcon h22 h212.
Qed.

Lemma tritra_subst_mutation_lst' : forall pi1 sig1 e1 e2 e3 e4 L l x',
  (forall s, eval_b pi1 s -> (eval_b ((e1 \+ nat_e 1) \= (subst_e_lst l e3)) s  /\ eval_b (e1 \!= e2) s )) ->
  x' = triple_vfresh (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpMutation e3 e4 L)) ->
  tritra (pi1 \&& (e1 \!= var_e x')  \&& (var_e x' \= nat_e 0),
    star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 \+ nat_e 1))) (wpSubst l (wpMutation e3 e4 L)) ->
  tritra (pi1 \&& (e1 \!= var_e x')  \&& (var_e x' \!= nat_e 0),
    star (star sig1 (star (lst (var_e x') e2) (singl e1 (var_e x')))) (cell (e1 \+ nat_e 1))) (wpSubst l (wpMutation e3 e4 L)) ->
  tritra (pi1,star sig1 (lst e1 e2)) (wpSubst l (wpMutation e3 e4 L)).
Proof.
intros.
unfold triple_vfresh in H0.
apply tritra_destruct_lst with (x' := x').
- move=> s; by case/H.
- rewrite /fresh_assrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- rewrite /fresh_wpAssrt.
  subst x'.
  simpl.
  by Resolve_le_max.
- eapply tritra_precond_stre; [idtac | by apply H1].
  rewrite /while.entails => s h [H4 H5].
  split; auto.
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h211 \U h22 \U h1) h212; auto.
  Compose_sepcon h1 (h211 \U h22); auto.
  by Compose_sepcon h22 h211.
- eapply tritra_precond_stre; [idtac | by apply H2].
  rewrite /while.entails => s h [H4 H5].
  split; auto.
  simpl in H5.
  case_sepcon H5.
  case_sepcon H5_h2.
  case_sepcon H5_h2_h21.
  simpl.
  Compose_sepcon (h211 \U h22 \U h1) h212; auto.
  Compose_sepcon h1 (h211 \U h22); auto.
  by Compose_sepcon h22 h211.
Qed.

(** Tactics to resolve tritra goals *)

(** Resolution tactic *)

Lemma tritra_use: forall c P Q R, wp_frag (Some (wpElt Q)) c = Some R ->
  tritra P R -> {{ assrt_interp P }} c {{ Assrt_interp Q }}.
Proof.
move=> c P Q R.
move/wp_frag_soudness => /= H1 H0.
apply hoare_prop_m.hoare_stren with (wpAssrt_interp R); [by apply tritra_soundness | done].
Qed.

(** the following lemma replaces the constructor tritra_subst_lookup in the tactic,
  the difference is that it introduces a way to compute fresh variables *)
Lemma tritra_subst_lookup2 : forall pi1 sig1 e1 e2 e x x' l L,
  (forall s, eval_b pi1 s -> (eval_b (e1 \= (subst_e_lst l e))) s) ->
  x' = triple_vfresh (pi1,star sig1 (singl e1 e2)) (wpSubst l (wpLookup x e L)) ->
  tritra (pi1,star sig1 (singl e1 e2)) (wpSubst ((x,(var_e x'))::l ++ ((x',e2)::nil)) L) ->
  tritra (pi1,star sig1 (singl e1 e2)) (wpSubst l (wpLookup x e L)).
Proof.
intros.
unfold triple_vfresh in H0.
apply tritra_subst_lookup with x'.
exact H.
rewrite /fresh_lst H0 /=; by Resolve_le_max.
rewrite /fresh_wpAssrt H0 /=; by Resolve_le_max.
rewrite /fresh_e H0 /= /max_lst /max_list /=.
by Resolve_le_max.
assumption.
Qed.

Ltac Rotate_tritra_sig_lhs :=
  match goal with
    | |- tritra (?pi,?sig) ?L' =>
      eapply tritra_precond_stre with (
        (pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp))
      ); [apply entail_soundness; simpl; Entail| simpl]
  end.

Lemma Decompose_Assrt_interp : forall a hd tl,
  (assrt_interp a ===> assrt_interp hd) \/ (assrt_interp a ===> Assrt_interp tl) ->
  (assrt_interp a ===> Assrt_interp (hd :: tl)).
Proof.
rewrite /while.entails /=; intros; by intuition.
Qed.

Ltac Resolve_entails :=
  eapply Decompose_Assrt_interp; ((left; apply entail_soundness; Entail) || (right; Resolve_entails)).

Ltac tritra_resolve :=
  match goal with
    | |- tritra (?pi1, ?sig1) ?L => eapply tritra_entail; Resolve_entails

    | |- tritra (?pi1, star ?sig1 (singl ?e1 ?e2)) (wpMutation ?e3 ?e4 ?L') =>
      (apply tritra_mutation; [(do 2 intro; omegab) | tritra_resolve] || Rotate_tritra_sig_lhs; idtac)

    | |- tritra (?pi1, star ?sig1 (cell ?e1)) (wpMutation ?e3 ?e4 ?L') =>
      (eapply tritra_mutation'; [(do 2 intro; omegab) | tritra_resolve] || Rotate_tritra_sig_lhs; idtac)

    | |- tritra (?pi1, star ?sig1 (singl ?e1 ?e2)) (wpLookup ?x ?e ?L') =>
      (apply tritra_lookup; [(do 2 intro; omegab) | tritra_resolve] || Rotate_tritra_sig_lhs; idtac)

    | |- tritra ?L (wpSubst ?l (wpElt ?L')) => eapply tritra_subst_elt; simpl; idtac
    | |- tritra ?L (wpSubst ?l (wpSubst ?l' ?L')) => eapply tritra_subst_subst; simpl; idtac

    | |- tritra ?L (wpSubst ?l (wpLookup ?x ?e ?L')) =>
      (eapply tritra_subst_lookup2;
        [(do 2 intro; omegab) | simpl; intuition | tritra_resolve] ||
         Rotate_tritra_sig_lhs; idtac)

    | |- tritra ?L (wpSubst ?l (wpMutation ?e1 ?e2 ?L')) => eapply tritra_subst_mutation; simpl; idtac
    | |- tritra ?L (wpSubst ?l (wpIf ?b ?L1 ?L2)) => eapply tritra_subst_if; simpl; idtac
    | |- tritra ?L (wpIf ?b ?L1 ?L2) => eapply tritra_if; simpl; idtac
  end.

Ltac Tritra := Rotate_tritra_sig_lhs; repeat tritra_resolve.

(** pi,sig is the pre-condition
   A is the current post-condition
   the result is a list of pre/post-conditions left to be proved *)
Definition tritra_step' (pi : expr_b) (sig : Sigma) (A : wpAssrt) : option (list ((expr_b * Sigma) * wpAssrt)) :=
  match A with
    | wpElt L =>
      match entail_fun (pi, sig) L nil with
        | Good => Some nil
        | Error _ => None
      end
    | wpSubst l L =>
      match L with
        | wpElt L' => Some (((pi, sig), wpElt (subst_Assrt_lst l L')) :: nil)
        | wpSubst l' L' => Some (((pi, sig), wpSubst (l' ++ l) L') :: nil)
        | wpLookup x e L' =>
          match sig with
            | star s1 (singl e1 e2) =>
              if expr_b_dp (pi =b> (e1 \= subst_e_lst l e)) then
                let x' := (max (max (var_max_lst l) (var_max_wpAssrt L')) x) + 1 in
                  Some (((pi, sig), wpSubst ((x, var_e x') :: l ++ ((x', e2) :: nil)) L') :: nil)
                else
                  Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)), A) :: nil)
            | star s1 (cell e1) =>
              if expr_b_dp (pi =b> (e1 \= subst_e_lst l e)) then
                let x' := (max (max (var_max_lst l) (var_max_wpAssrt L')) x) + 1 in
                  let x'' := (max (var_max_assrt (pi,sig)) (var_max_wpAssrt A)) + 1 in
                    Some (((pi, star s1 (singl e1 (var_e x''))), wpSubst ((x, var_e x')::l ++ ((x', var_e x'') :: nil)) L')::nil)
                else
                  Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)),A)::nil)
            | star s1 (lst e1 e2) =>
              if expr_b_dp (pi =b> ((e1 \!= e2) \&& (e1 \= subst_e_lst l e))) then
                let x' := triple_vfresh (pi,sig) A in
                  Some ((pi \&& (e1 \!= var_e x') \&& (var_e x' \= nat_e 0),
                    star (star s1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x')), A)::
                      (pi \&& (e1 \!= var_e x') \&& (var_e x' \!= nat_e 0),
                        star (star s1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x')), A)::
                      nil)
                else
              if expr_b_dp (pi =b> ((e1 \!= e2) \&& ((e1 \+ nat_e 1) \= subst_e_lst l e))) then
                let x' := triple_vfresh (pi,sig) A in
                  Some (
                       (((pi \&& (e1 \!= var_e x')) \&& (var_e x' \= nat_e 0),
                       star (star s1 (star (lst (var_e x') e2) (singl e1 (var_e x'))))
                       (cell (e1 \+ nat_e 1))), A)::
                       (((pi \&& (e1 \!= var_e x')) \&& (var_e x' \!= nat_e 0),
                       star (star s1 (star (lst (var_e x') e2) (singl e1 (var_e x'))))
                       (cell (e1 \+ nat_e 1))), A)::
                      nil)
                else
                  Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)), A)::nil)
            | (singl e1 e2) => Some ((pi, star frag_list_entail.emp sig, A)::nil)
            | (cell e1) => Some ((pi, star frag_list_entail.emp sig, A)::nil)
            | (lst e1 e2) => Some ((pi, star frag_list_entail.emp sig, A)::nil)
            | _ => Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)), A)::nil)
          end
        | wpMutation e1 e2 L' =>
          Some (((pi,sig), wpMutation (subst_e_lst l e1) (subst_e_lst l e2) (wpSubst l L'))::nil)
        | wpIf b L1 L2 =>
          Some (((pi,sig), wpIf (subst_b_lst l b) (wpSubst l L1) (wpSubst l L2))::nil)
      end
    (* *)
    | wpIf b L1 L2 => Some (((pi \&& b, sig), L1) :: ((pi \&& (\~ b), sig), L2) :: nil)
    (* *)
    | wpLookup x e L =>
      match sig with
        | star s1 (singl e1 e2) =>
          if expr_b_dp (pi =b> (e1 \= e)) then
            Some (((pi, sig), wpSubst ((x, e2) :: nil) L) :: nil)
            else
              Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)), A) :: nil)
        | star s1 (cell e1) =>
          if expr_b_dp (pi =b> (e1 \= e)) then
            let x' := (max (var_max_assrt (pi, sig)) (var_max_wpAssrt A)) + 1 in
               Some (((pi, star s1 (singl e1 (var_e x'))), wpSubst ((x, var_e x') :: nil) L) :: nil)
            else
              Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)), A) :: nil)
        | star s1 (lst e1 e2) =>
          if expr_b_dp (pi =b> ((e1 \!= e2) \&& (e1 \= e))) then
            let x' := triple_vfresh (pi,sig) A in
              Some (((pi \&& (e1 \!= var_e x') \&& (var_e x' \= nat_e 0),
                star (star s1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))), A) ::
              ((pi \&& (e1 \!= var_e x') \&& (var_e x' \!= nat_e 0),
                star (star s1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))), A) ::
                  nil)
            else
          if expr_b_dp (pi =b> ((e1 \!= e2) \&& ((e1 \+ nat_e 1) \= e))) then
            let x' := triple_vfresh (pi,sig) A in
              Some (((pi \&& (e1 \!= var_e x') \&& (var_e x' \= nat_e 0),
                star (star s1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))), A)::
                  ((pi \&& (e1 \!= var_e x') \&& (var_e x' \!= nat_e 0),
                    star (star s1 (star (lst (var_e x') e2) (cell (e1 \+ nat_e 1)))) (singl e1 (var_e x'))), A)::
                  nil)
            else Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)),A)::nil)
        | (singl e1 e2) => Some ((pi, star frag_list_entail.emp sig, A)::nil)
        | (cell e1) => Some ((pi, star frag_list_entail.emp sig, A)::nil)
        | (lst e1 e2) => Some ((pi, star frag_list_entail.emp sig, A)::nil)
        | _ => Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)), A)::nil)
      end
      (**)
    | wpMutation e1 e2 L =>
      match sig with
        | star s1 (cell e3) =>
          if expr_b_dp (pi =b> (e1 \= e3)) then
            Some (((pi, star s1 (singl e3 e2)),L)::nil)
            else
              Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)), A)::nil)
        | star s1 (singl e3 e4) =>
          if expr_b_dp (pi =b> (e1 \= e3)) then
            Some (((pi, star s1 (singl e3 e2)), L) :: nil)
            else
              Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)), A)::nil)
        | star s1 (lst e3 e4) =>
              if expr_b_dp (pi =b> ((e1 \= e3) \&& (e3 \!= e4))) then
                let x' := triple_vfresh (pi,sig) A in
                  Some (
                  (((pi \&& (e3 \!= var_e x')) \&& (var_e x' \= nat_e 0),
                  star (star s1 (star (lst (var_e x') e4) (cell (e3 \+ nat_e 1))))
                  (singl e3 (var_e x'))), A)::
                  (((pi \&& (e3 \!= var_e x')) \&& (var_e x' \!= nat_e 0),
                  star (star s1 (star (lst (var_e x') e4) (cell (e3 \+ nat_e 1))))
                  (singl e3 (var_e x'))),A)::
                  nil)
                else if expr_b_dp (pi =b> (((e3 \+ (nat_e 1)) \= e1) \&& (e3 \!= e4))) then
                  let x' := triple_vfresh (pi,sig) A in
                    Some (
                    (((pi \&& (e3 \!= var_e x')) \&& (var_e x' \= nat_e 0),
                    star (star s1 (star (lst (var_e x') e4) (singl e3 (var_e x'))))
                    (cell (e3 \+ nat_e 1))), A)::
                    (((pi \&& (e3 \!= var_e x')) \&& (var_e x' \!= nat_e 0),
                    star (star s1 (star (lst (var_e x') e4) (singl e3 (var_e x'))))
                    (cell (e3 \+ nat_e 1))), A)::
                    nil)
                else Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)), A)::nil)
        | (singl e1 e2) => Some ((pi, star frag_list_entail.emp sig, A)::nil)
        | (cell e1) => Some ((pi, star frag_list_entail.emp sig, A)::nil)
        | (lst e1 e2) => Some ((pi, star frag_list_entail.emp sig, A)::nil)
        | _ => Some (((pi, remove_empty_heap pi (star_assoc_left (star_com sig) frag_list_entail.emp)), A)::nil)
      end

  end.

Opaque entail_fun.
Opaque remove_empty_heap.
Opaque star_assoc_left.

Lemma tritra_step'_correct : forall A pi sig l,
  tritra_step' pi sig A = Some l ->
  (forall pi' sig' A', In ((pi', sig'), A') l -> tritra (pi', sig') A') ->
  tritra (pi, sig) A.
Proof.
destruct A; simpl; intros.
- (* wpElt *) generalize (entail_fun_correct a (pi, sig) nil); intros.
  destruct (entail_fun (pi, sig) a nil); try discriminate.
  injection H; clear H; intros; subst l.
  eapply tritra_entail.
  by apply H1; auto.
- (* wpSubst *) destruct A.
  + (* wpElt *) injection H; clear H; intros; subst l0.
    eapply tritra_subst_elt.
    eapply H0; simpl; left; auto.
  + (* wpSubst *)injection H; clear H; intros; subst l0.
    eapply tritra_subst_subst.
    eapply H0; simpl; left; auto.
  + (* wpLookup *) destruct sig.
    * eapply tritra_precond_stre with
        (pi, star frag_list_entail.emp (singl e0 e1)).
      eapply entail_soundness; Entail.
      eapply H0.
      injection H; intros; subst l0.
      simpl; left; auto.
    * eapply tritra_precond_stre with
        (pi, star frag_list_entail.emp (cell e0)).
      eapply entail_soundness; Entail.
      eapply H0.
      injection H; intros; subst l0.
      simpl; left; auto.
    * apply tritra_precond_stre with (pi,
        remove_empty_heap pi (star_assoc_left (star_com frag_list_entail.emp) frag_list_entail.emp)).
      done.
      apply H0.
      case : H => H; subst l0.
      by left.
    * destruct sig2.
      - move: (expr_b_dp_correct (pi =b> e0 \= subst_e_lst l e)) => H1.
        destruct (expr_b_dp (pi =b> e0 \= subst_e_lst l e)).
        case: H => ?; subst l0.
        apply tritra_subst_lookup with (x' := (max (max (var_max_lst l) (var_max_wpAssrt A)) s + 1)).
        move=> s0 H; move: (H1 (refl_equal _) s0) => H2; by omegab.
        rewrite /fresh_lst /=; by Resolve_le_max.
        rewrite /fresh_wpAssrt /=; by Resolve_le_max.
        rewrite /fresh_e /= /max_lst /max_list /=; by Resolve_le_max.
        apply H0; by left.
        clear H1.
        apply tritra_precond_stre with (pi,
          remove_empty_heap pi (star_assoc_left (star_com (star sig1 (singl e0 e1))) frag_list_entail.emp)).
        rewrite /while.entails => s0 h [H2 H3].
        split; first by [].
        apply remove_empty_heap_correct' => //.
        apply star_assoc_left_correct'.
        Compose_sepcon h assert_m.heap.emp; last by [].
        by apply star_com_correct'.
        apply H0.
        case: H => ?; subst l0.
        by left.
      - move: (expr_b_dp_correct (pi =b> e0 \= subst_e_lst l e)) => H1.
        destruct (expr_b_dp (pi =b> e0 \= subst_e_lst l e)).
        + case : H => ?; subst l0.
          apply tritra_subst_lookup' with (x' := (max (max (var_max_lst l) (var_max_wpAssrt A)) s + 1)) (x'' := (max
            (max (max_lst (vars_b pi))
              (var_max_Sigma (star sig1 (cell e0))))
            (max (var_max_lst l) (var_max_wpAssrt (wpLookup s e A))) +
            1)).
          intros; move: (H1 (refl_equal _) s0) => H2; by omegab.
          rewrite /fresh_lst /=; by Resolve_le_max.
          rewrite /fresh_wpAssrt /=; by Resolve_le_max.
          rewrite /fresh_e /= /max_lst /max_list /=; by Resolve_le_max.
          rewrite /fresh_wpAssrt /=; by Resolve_le_max.
          rewrite /fresh_assrt /=; by Resolve_le_max.
          apply H0 => /=; by left.
        + clear H1.
          apply tritra_precond_stre with (pi,
            remove_empty_heap pi(star_assoc_left (star_com (star sig1 (cell e0))) frag_list_entail.emp)).
          rewrite /while.entails => s0 h [H2 H3].
          split; auto.
          apply remove_empty_heap_correct' => //.
          apply star_assoc_left_correct'.
          Compose_sepcon h assert_m.heap.emp; last by [].
          by apply star_com_correct'.
          apply H0.
          case : H => ?; subst l0.
          by left.
      - apply tritra_precond_stre with (pi,
        remove_empty_heap pi (star_assoc_left (star_com (star sig1 frag_list_entail.emp)) frag_list_entail.emp)).
        + rewrite /while.entails => s0 h [H2 H3].
          split; auto.
          apply remove_empty_heap_correct' => //.
          apply star_assoc_left_correct'.
          Compose_sepcon h assert_m.heap.emp; last by [].
          by apply star_com_correct'.
        + apply H0.
          case : H => ?; subst l0.
          by left.
      - apply tritra_precond_stre with (pi,
        remove_empty_heap pi (star_assoc_left (star_com (star sig1 (star sig2_1 sig2_2))) frag_list_entail.emp)).
        + rewrite /while.entails => s0 h [H2 H3].
          split; auto.
          apply remove_empty_heap_correct' => //.
          apply star_assoc_left_correct'.
          Compose_sepcon h assert_m.heap.emp; last by [].
          by apply star_com_correct'.
        + apply H0.
          case : H => ?; subst l0.
          by left.
      - move: (expr_b_dp_correct (pi =b> (e0 \!= e1) \&& (e0 \= subst_e_lst l e))) => H1.
        destruct (expr_b_dp (pi =b> (e0 \!= e1) \&& (e0 \= subst_e_lst l e))).
        + eapply tritra_subst_lookup_lst with (x' :=
            triple_vfresh (pi, star sig1 (lst e0 e1)) (wpSubst l (wpLookup s e A))).
          intros; generalize (H1 (refl_equal _) s0); intros.
          split; by omegab.
          reflexivity.
          apply H0.
          case : H => ?; subst l0.
          rewrite /=; by left.
          apply H0.
          case : H => ?; subst l0.
          rewrite /=; by right; left.
        + move: (expr_b_dp_correct (pi =b> (e0 \!= e1) \&& ((e0 \+ nat_e 1) \= subst_e_lst l e))) => {}H1.
          destruct (expr_b_dp (pi =b> (e0 \!= e1) \&& ((e0 \+ nat_e 1) \= subst_e_lst l e))); try discriminate.
          * apply tritra_subst_lookup_lst' with (x' :=
              triple_vfresh (pi, star sig1 (lst e0 e1)) (wpSubst l (wpLookup s e A))).
            intros; move: (H1 (refl_equal _) s0) => H3; split; by omegab.
            reflexivity.
            apply H0.
            case : H => ?; subst l0.
            rewrite /=; by left.
            apply H0.
            case : H => ?; subst l0.
            rewrite /=; by right; left.
          * clear H1.
            apply tritra_precond_stre with (pi,
              remove_empty_heap pi (star_assoc_left (star_com (star sig1 (lst e0 e1))) frag_list_entail.emp)).
            - rewrite /while.entails => s0 h [H2 H3].
              split; auto.
              apply remove_empty_heap_correct' => //.
              apply star_assoc_left_correct'.
              Compose_sepcon h assert_m.heap.emp; last by [].
              by apply star_com_correct'.
            - apply H0.
              case : H => ?; subst l0.
              by left.
    * apply tritra_precond_stre with (pi, star frag_list_entail.emp (lst e0 e1)).
      apply entail_soundness; by Entail.
      case: H => ?; subst l0.
      apply H0; by left.
  + (* wpMutation *)apply tritra_subst_mutation.
    case: H => ?; subst l0.
    apply H0 => /=; by left.
  + (* wpIf *) apply tritra_subst_if.
    case: H => ?; subst l0.
    apply H0 => /=; by left.
- (* wpLookup *) destruct sig.
  + eapply tritra_precond_stre with
      (pi, star frag_list_entail.emp (singl e0 e1)).
    eapply entail_soundness; Entail.
    eapply H0.
    injection H; intros; subst l.
    simpl; by left.
  + eapply tritra_precond_stre with
      (pi, star frag_list_entail.emp (cell e0)).
    eapply entail_soundness; Entail.
    eapply H0.
    injection H; intros; subst l.
    by left.
  + simpl in H.
    eapply tritra_precond_stre with (pi,
      remove_empty_heap pi (star_assoc_left frag_list_entail.emp frag_list_entail.emp)).
    rewrite /while.entails => s0 h [H2 H3].
    split; auto.
    apply H0.
    case : H => H; subst l.
    by left.
  + destruct sig2.
    * move: (expr_b_dp_correct (pi =b> (e0 \= e))) => H1.
      destruct (expr_b_dp (pi =b> (e0 \= e))).
      - apply tritra_lookup.
        move=> s0 H2; move: (H1 (refl_equal _) s0) => H3.
        by omegab.
        apply H0.
        case: H => ?; subst l.
        rewrite /=; by left.
      - clear H1.
        apply tritra_precond_stre with (pi,
          remove_empty_heap pi (star_assoc_left (star_com (star sig1 (singl e0 e1))) frag_list_entail.emp)).
       rewrite /while.entails => s0 h [H2 h3]; split; first by [].
       apply remove_empty_heap_correct' => //.
       apply star_assoc_left_correct'.
       Compose_sepcon h assert_m.heap.emp; last by [].
       by apply star_com_correct'.
       apply H0.
       case: H => ?; subst l.
       by left.
    * move: (expr_b_dp_correct (pi =b> e0 \= e)) => H1.
      destruct (expr_b_dp (pi =b> e0 \= e)).
      - case: H => ?; subst l.
        apply tritra_lookup' with (max (max (max_lst (vars_b pi))
            (max (var_max_Sigma sig1) (max_lst (vars e0))))
          (max (max s (max_lst (vars e))) (var_max_wpAssrt A)) + 1).
        move=> s0 H; move: (H1 (refl_equal _) s0) => H2; by omegab.
        rewrite /fresh_assrt /=; by Resolve_le_max.
        rewrite /fresh_wpAssrt /=; by Resolve_le_max.
        apply H0 => /=; by left.
      - clear H1.
        apply tritra_precond_stre with (pi,
          remove_empty_heap pi (star_assoc_left (star_com (star sig1 (cell e0))) frag_list_entail.emp)).
        rewrite /while.entails => s0 h [H2 H3].
        split; first by [].
        apply remove_empty_heap_correct' => //.
        apply star_assoc_left_correct'.
        Compose_sepcon h assert_m.heap.emp; last by [].
        by apply star_com_correct'.
        case: H => ?; subst l.
        apply H0; by left.
    * apply tritra_precond_stre with (pi,
       remove_empty_heap pi (star_assoc_left (star_com (star sig1 frag_list_entail.emp)) frag_list_entail.emp)).
      rewrite /while.entails => s0 h [H2 H3].
      split; first by [].
      apply remove_empty_heap_correct' => //.
      apply star_assoc_left_correct'.
      Compose_sepcon h assert_m.heap.emp; last by [].
      by apply star_com_correct'.
      case: H => ?; subst l.
      apply H0; by left.
    * apply tritra_precond_stre with (pi,
        remove_empty_heap pi (star_assoc_left (star_com (star sig1 (star sig2_1 sig2_2))) frag_list_entail.emp)).
      rewrite /while.entails => s0 h [H2 H3].
      split; first by [].
      apply remove_empty_heap_correct' => //.
      apply star_assoc_left_correct'.
      Compose_sepcon h assert_m.heap.emp; last by [].
      by apply star_com_correct'.
      case : H => ?; subst l.
      apply H0; by left.
    * move: (expr_b_dp_correct (pi =b> (e0 \!= e1) \&& (e0 \= e))) => H1.
      destruct (expr_b_dp (pi =b> (e0 \!= e1) \&& (e0 \= e))).
      - case: H => ?; subst l.
        eapply tritra_lookup_lst.
        move=> s0 H2; move: (H1 (refl_equal _) s0) => H3.
        split; by omegab.
        reflexivity.
        apply H0 => /=; by left.
        apply H0 => /=; by right; left.
      - move: (expr_b_dp_correct (pi =b> (e0 \!= e1) \&& ((e0 \+ nat_e 1) \= e))) => {}H1.
        destruct (expr_b_dp (pi =b> (e0 \!= e1) \&& ((e0 \+ nat_e 1) \= e))).
        + case: H => ?; subst l.
          eapply tritra_lookup_lst'.
          move=> s0 H2; move: (H1 (refl_equal _) s0) => H3.
          split; by omegab.
          reflexivity.
          apply H0 => /=; by left.
          apply H0 => /=; by right; left.
        + clear H1.
          apply tritra_precond_stre with (pi,
            remove_empty_heap pi (star_assoc_left (star_com (star sig1 (lst e0 e1))) frag_list_entail.emp)).
          rewrite /while.entails => s0 h [H2 H3].
          split; first by [].
          apply remove_empty_heap_correct' => //.
          apply star_assoc_left_correct'.
          Compose_sepcon h assert_m.heap.emp; last by [].
          by apply star_com_correct'.
          case: H => ?; subst l.
          apply H0; by left.
  + apply tritra_precond_stre with (pi, star frag_list_entail.emp (lst e0 e1)).
    * apply entail_soundness; by Entail.
    * case : H => ?; subst l.
      apply H0; by left.
- (* wpMutation *) destruct sig.
  + apply tritra_precond_stre with (pi, star frag_list_entail.emp (singl e1 e2)).
    eapply entail_soundness; by Entail.
    case : H => ?; subst l.
    apply H0; by left.
  + eapply tritra_precond_stre with (pi, star frag_list_entail.emp (cell e1)).
    eapply entail_soundness; by Entail.
    case : H => ?; subst l.
    apply H0; by left.
  + apply tritra_precond_stre with (pi,
      remove_empty_heap pi (star_assoc_left (star_com frag_list_entail.emp) frag_list_entail.emp)) => //.
    case : H => ?; subst l.
    apply H0; by left.
  + destruct sig2.
    * move: (expr_b_dp_correct (pi =b> (e \= e1))) => H1.
      destruct (expr_b_dp (pi =b> (e \= e1))).
      - apply tritra_mutation.
        move=> s H2; move: (H1 (refl_equal _) s) => H3.
        have : [ e \= e1 ]b_s by omegab.
        move/eqP => H4.
        exact/eqP.
        case: H => ?; subst l.
        apply H0 => /=; by left.
      - clear H1.
        apply tritra_precond_stre with (pi,
          remove_empty_heap pi
          (star_assoc_left (star_com (star sig1 (singl e1 e2))) frag_list_entail.emp)).
        rewrite /while.entails => s h [H2 H3].
        split; first by [].
        apply remove_empty_heap_correct' => //.
        apply star_assoc_left_correct'.
        Compose_sepcon h assert_m.heap.emp; last by [].
        by apply star_com_correct'.
        case : H => ?; subst l.
        apply H0; by left.
    * move: (expr_b_dp_correct (pi =b> (e \= e1))) => H1.
      destruct (expr_b_dp (pi =b> (e \= e1))).
      - apply tritra_mutation'.
        move=> s H2; move: (H1 (refl_equal _) s) => H3.
        have : [ e \= e1 ]b_s by omegab.
        move/eqP => H4.
        exact/eqP.
        case: H => ?; subst l.
        apply H0 => /=; by left.
      - apply tritra_precond_stre with (pi, remove_empty_heap pi
          (star_assoc_left (star_com (star sig1 (cell e1))) frag_list_entail.emp)).
        rewrite /while.entails => s h [H3 H4].
        split; first by [].
        apply remove_empty_heap_correct' => //.
        apply star_assoc_left_correct'.
        Compose_sepcon h assert_m.heap.emp; last by [].
        by apply star_com_correct'.
        case: H => ?; subst l.
        apply H0; by left.
    * apply tritra_precond_stre with (pi,
        remove_empty_heap pi
        (star_assoc_left (star_com (star sig1 frag_list_entail.emp)) frag_list_entail.emp)).
      rewrite /while.entails => s h [H2 H3].
      split; first by [].
      apply remove_empty_heap_correct' => //.
      apply star_assoc_left_correct'.
      Compose_sepcon h assert_m.heap.emp; last by [].
      by apply star_com_correct'.
      case: H => ?; subst l.
      apply H0; by left.
    * apply tritra_precond_stre with (pi,
        remove_empty_heap pi
        (star_assoc_left (star_com (star sig1 (star sig2_1 sig2_2))) frag_list_entail.emp)).
      rewrite /while.entails => s h [H2 H3].
      split; first by [].
      apply remove_empty_heap_correct' => //.
      apply star_assoc_left_correct'.
      Compose_sepcon h assert_m.heap.emp; last by [].
      by apply star_com_correct'.
      case: H => ?; subst l.
      apply H0; by left.
    * move: (expr_b_dp_correct (pi =b> (e \= e1) \&& (e1 \!= e2))) => H1.
      destruct (expr_b_dp (pi =b> (e \= e1) \&& (e1 \!= e2))).
      - case : H => ?; subst l.
        eapply tritra_mutation_lst.
        move=> s H2; move: (H1 (refl_equal _) s) => H3; split; last by omegab.
        have : [ e \= e1 ]b_s by omegab.
        move/eqP => H4.
        exact/eqP.
        reflexivity.
        apply H0 => /=; by left.
        apply H0 => /=; by right; left.
      - move: (expr_b_dp_correct (pi =b> ((e1 \+ nat_e 1) \= e) \&& (e1 \!= e2))) => {}H1.
        destruct (expr_b_dp (pi =b> ((e1 \+ nat_e 1) \= e) \&& (e1 \!= e2))).
        + case : H => ?; subst l.
          eapply tritra_mutation_lst'.
          move=> s H2; move: (H1 (refl_equal _) s) => H3; split; by omegab.
          reflexivity.
          apply H0 => /=; by left.
          apply H0 => /=; by right; left.
        + clear H1.
          apply tritra_precond_stre with (pi,
            remove_empty_heap pi
            (star_assoc_left (star_com (star sig1 (lst e1 e2))) frag_list_entail.emp)).
          rewrite /while.entails => s h [H2 H3].
          split; first by [].
          apply remove_empty_heap_correct' => //.
          apply star_assoc_left_correct'.
          Compose_sepcon h assert_m.heap.emp; last by [].
          by apply star_com_correct'.
          case: H => ?; subst l.
          apply H0; by left.
  * apply tritra_precond_stre with (pi, star frag_list_entail.emp (lst e1 e2)).
    + apply entail_soundness; by Entail.
    + case: H => ?; subst l.
      apply H0 => /=; by left.
- (* wpIf *) case: H => ?; subst l.
  apply tritra_if; apply H0 => /=; by [left | right; left].
Qed.

Definition tritra_step (pi : expr_b) (sig : Sigma) (A : wpAssrt) : option (list ((expr_b * Sigma) * wpAssrt)) :=
  if expr_b_dp (\~ pi) then
    Some nil
  else
    tritra_step' pi sig A.

Lemma tritra_step_correct: forall A pi sig l,
  tritra_step pi sig A = Some l ->
  (forall pi' sig' A', In ((pi', sig'), A') l -> tritra (pi', sig') A') ->
  tritra (pi, sig) A.
Proof.
move=> A pi sig l H H0.
rewrite /tritra_step in H.
move: (expr_b_dp_correct (\~ pi)) => H1.
destruct (expr_b_dp (\~ pi)).
- apply tritra_incons => s h [H3 h4].
  move: (H1 (refl_equal _) s).
  by rewrite /= H3.
- clear H1.
  by apply tritra_step'_correct with l.
Qed.

Fixpoint tritra_list (l : list ((expr_b * Sigma) * wpAssrt)) : option (list ((expr_b * Sigma) * wpAssrt)) :=
  match l with
    | nil => Some nil
    | ((pi, sg), A) :: tl =>
      match tritra_step pi sg A with
        | None => None
        | Some l' =>
          match tritra_list tl with
            | None => None
            | Some l'' => Some (l' ++ l'')
          end
      end
  end.

Lemma tritra_list_correct : forall l l', tritra_list l = Some l' ->
  (forall pi sig A, In ((pi, sig), A) l' -> tritra (pi, sig) A) ->
  (forall pi sig A, In ((pi, sig), A) l -> tritra (pi, sig) A).
Proof.
induction l; simpl; intros; auto.
- contradiction.
- destruct a.
  destruct p as [p s].
  generalize (tritra_step_correct w p s); intros.
  destruct (tritra_step p s w); try discriminate.
  generalize (H2 l0 (refl_equal _)); clear H2; intros.
  destruct (tritra_list l); try discriminate.
  generalize (IHl l1 (refl_equal _)); clear IHl; intros.
  injection H; clear H; intros; subst l'.
  case : H1.
  + case => ? ? ?; subst p s w.
    apply H2 => pi' sig' A' H.
    apply H0, in_or_app; by left.
  + apply H3 => pi0 sig0 A0 H.
    apply H0, in_or_app; by right.
Qed.

Fixpoint tritra_list_rec (l: list ((expr_b * Sigma) * wpAssrt)) (size:nat) {struct size} : option (list ((expr_b * Sigma) * wpAssrt)) :=
  match size with
    | 0 => Some l
    | S size' =>
      match tritra_list l with
        | None => None
        | Some l' =>
          match l' with
            | nil => Some nil
            | _ =>  tritra_list_rec l' size'
          end
      end
  end.

Lemma tritra_list_rec_correct : forall n l l',
  tritra_list_rec l n = Some l' ->
  (forall pi sig A, In ((pi, sig), A) l' -> tritra (pi, sig) A) ->
  (forall pi sig A, In ((pi, sig), A) l -> tritra (pi, sig) A).
Proof.
induction n; simpl; intros; auto.
case : H => ?; subst l.
intuition.
move: (tritra_list_correct l) => H2.
destruct (tritra_list l); try discriminate.
destruct l0.
- apply (H2 _ (refl_equal _)).
  intros.
  simpl in H3; contradiction.
  assumption.
- apply (H2 _ (refl_equal _)); last by assumption.
  move=> pi0 sig0 A0 H3; by apply (IHn _ _ H H0).
Qed.

Lemma tritra_list_rec_correct': forall n l, tritra_list_rec l n = Some nil ->
  (forall pi sig A, In ((pi, sig), A) l ->
    assrt_interp (pi, sig) ===> wpAssrt_interp A).
Proof.
move=> n l H pi sig A H0; by apply tritra_soundness, (tritra_list_rec_correct _ _ _ H).
Qed.

Fixpoint wpAssrt_size (A : wpAssrt) : nat :=
  match A with
    | wpElt P => 2
    | wpSubst l P => 2 + wpAssrt_size P
    | wpLookup x e P => 2 + wpAssrt_size P
    | wpMutation e1 e2 P  => 2 + wpAssrt_size P
    | wpIf b L1 L2 => 2 + wpAssrt_size L1 + wpAssrt_size L2
  end.

Definition triple_transformation_complexity (pi: expr_b) (sig: Sigma) (L: wpAssrt) : nat :=
  (Expr_B_size pi) * (sigma_size sig) * (wpAssrt_size L).

(** entry point *)
Fixpoint triple_transformation (P: Assrt) (Q: wpAssrt) {struct P} : option (list ((expr_b * Sigma) * wpAssrt)) :=
  match P with
    | nil => Some nil
    | (pi, sig) :: tl =>
      match tritra_list_rec
        (((compute_constraints (cell_loc_not_null pi sig) sig, sig), Q) :: nil)
        (triple_transformation_complexity pi sig Q) with
        | Some l =>
          match triple_transformation tl Q with
            | Some l' => Some (l ++ l')
            | None => None
          end
        | None =>
          match triple_transformation tl Q with
            | Some l' => Some (((pi, sig), Q) :: l')
            | None => None
          end
      end
  end.

Lemma triple_transformation_correct: forall P Q,
  triple_transformation P Q = Some nil  ->
  Assrt_interp P ===> wpAssrt_interp Q.
Proof.
induction P; rewrite /= /while.entails; intros; try contradiction.
destruct a as [p s0].
move: (tritra_list_rec_correct' (triple_transformation_complexity p s0 Q) ((compute_constraints (cell_loc_not_null p s0) s0, s0, Q) :: nil)) => H1.
destruct (tritra_list_rec ((compute_constraints (cell_loc_not_null p s0) s0, s0, Q) :: nil) (triple_transformation_complexity p s0 Q)); try discriminate.
- move: (IHP Q) => H2.
  rewrite /while.entails {IHP} in H2.
  destruct (triple_transformation P Q); try discriminate.
  destruct l; destruct l0; try discriminate.
  case: H0 => H3.
  + red in H1; eapply H1.
    reflexivity.
    simpl; by left.
    apply compute_constraints_correct.
    by apply cell_loc_not_null_correct.
  + by eapply H2; auto.
- move: (IHP Q) => H2.
  rewrite /while.entails {IHP} in H2.
  by destruct (triple_transformation P Q).
Qed.

(*
Fixpoint triple_transformation (P: Assrt) (Q: wpAssrt) {struct P} : option (list ((Pi * Sigma) * wpAssrt)) :=
  match P with
    | nil => Some nil
    | (pi,sig)::tl =>
      match (tritra_list_rec (((pi,sig),Q)::nil) (triple_transformation_complexity pi sig Q)) with
        | Some l =>
          match triple_transformation tl Q with
            | Some l' => Some (l ++ l')
            | None => None
          end
        | None =>
          match triple_transformation tl Q with
            | Some l' => Some (((pi,sig),Q)::l')
            | None => None
          end

      end
  end.

Lemma triple_transformation_correct: forall P Q,
  triple_transformation P Q = Some nil  ->
  (Assrt_interp P) ===> (wpAssrt_interp Q).
  induction P; simpl; red; intros; try contradiction.
  destruct a.
  generalize (tritra_list_rec_correct' (triple_transformation_complexity p s0 Q) ((p, s0, Q) :: nil)); intros.
  destruct (tritra_list_rec ((p, s0, Q) :: nil) (triple_transformation_complexity p s0 Q)); try discriminate.
  generalize (IHP Q); intros.
  red in H2.
  clear IHP.
  destruct (triple_transformation P Q); try discriminate.
  destruct l; destruct l0; try discriminate.
  inversion_clear H0.
  red in H1; eapply H1.
  auto.
  simpl; left; auto.
  auto.
  eapply H2; auto.
  generalize (IHP Q); intros.
  red in H2.
  clear IHP.
  destruct (triple_transformation P Q); try discriminate.
Qed.
*)

Fixpoint triple_transformation2 (P : Assrt) (Q : wpAssrt) {struct P} : bool :=
  match P with
    | nil => true
    | (pi, sig) :: tl =>
      match tritra_list_rec (((pi, sig), Q) :: nil) (triple_transformation_complexity pi sig Q) with
        | Some nil =>
          triple_transformation2 tl Q
        | _ => false
      end
  end.

Lemma triple_transformation2_correct : forall P Q, triple_transformation2 P Q ->
  Assrt_interp P ===> wpAssrt_interp Q.
Proof.
induction P; rewrite /= /while.entails; intros; try contradiction.
destruct a as [p s0].
move: (tritra_list_rec_correct' (triple_transformation_complexity p s0 Q) ((p, s0, Q) :: nil)) => H1.
destruct (tritra_list_rec ((p, s0, Q) :: nil) (triple_transformation_complexity p s0 Q)); try discriminate.
destruct l; try discriminate.
case : H0 => H0.
- eapply (H1 (refl_equal _)); last by apply H0.
  by left.
- by apply IHP.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext.
Require Import integral_type seplog.
Require Import expr_b_dp.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.

Local Close Scope Z_scope.
Local Close Scope positive_scope.
Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_assert_scope.

(** Definition and properties of lists *)
(* TODO: put in another file? *)

Inductive Lst : expr -> expr -> assert :=
| Lst_end: forall e1 e2 s h,
  [ e1 ]e_s = [ e2 ]e_s ->
  assert_m.emp s h ->
  Lst e1 e2 s h
| Lst_next: forall e1 e2 e3 e4 s h h1 h2,
  h1 # h2 -> h = h1 \U h2 ->
  [ e1 ]e_s <> [ e3 ]e_s ->
  [ e1 ]e_s <> 0%Z ->
  [ e1 \+ nat_e 1 ]e_s <> 0%Z ->
  (e1 |~> e2 ** (e1 \+ nat_e 1 |~> e4)) s h1 ->
  Lst e2 e3 s h2 ->
  Lst e1 e3 s h.

Lemma Lst_equiv' s h e1 e2 : Lst e1 e2 s h ->
  forall e1' e2' s', [ e1 ]e_s = [ e1' ]e_s' -> [ e2 ]e_s = [ e2' ]e_s' ->
    Lst e1' e2' s' h.
Proof.
elim; clear s h e1 e2.
- move=> e1 e2 s h H1 H2 e1' e2' s' H11' H22'.
  apply Lst_end => //.
  by rewrite -H11' H1 H22'.
- move=> e1 e2 e3 e4 s h h1 h2 Hdisj Hunion H1 H2 H3 H4 H5 IH e1' e2' s' H11' H22'.
  apply Lst_next with (cst_e [ e2 ]e_s) (cst_e [ e4 ]e_s) h1 h2 => //.
  by rewrite -H11' -H22'.
  by rewrite -H11'.
  by rewrite /= -H11'.
  case_sepcon H4.
  Compose_sepcon h11 h12.
  by Mapsto.
  by Mapsto.
  by apply IH.
Qed.

Lemma Lst_equiv s h e1 e2 : Lst e1 e2 s h ->
  forall e1' e2', [ e1 ]e_ s = [ e1' ]e_ s -> [ e2 ]e_ s = [ e2']e_  s ->
    Lst e1' e2' s h.
Proof. move=> H e1' e2' H11' H22'. eapply Lst_equiv'; eauto. Qed.

Lemma Lst_app e1 e2 s h1 :  Lst e1 e2 s h1 ->
  forall e3 h2 h3 h, Lst e2 e3 s h2 ->
    (exists v, (e3 |~> cst_e v) s h3) ->
    h1 # h2 -> h1 # h3 -> h = h1 \U h2  ->
    Lst e1 e3 s h.
Proof.
move=> H.
induction H.
- move=> e3 h2 h3 h0 H1 H2 H3 H4 H5.
  red in H0.
  subst h.
  rewrite assert_m.heap.unioneh in H5.
  subst h2.
  clear H3 H4.
  by apply Lst_equiv with e2 e3.
- intros.
  apply Lst_next with (h1 := h1) (h2 := h2 \U h0) (e2 := e2) (e4 := e4); auto.
  by map_tac_m.Disj.
  by map_tac_m.Equal.
  case_sepcon H4.
  inversion_clear H7.
  eapply singl_disj_neq.
  by apply H4_h11.
  by apply H4.
  by map_tac_m.Disj.
  eapply IHLst.
  apply H6.
  apply H7.
  by map_tac_m.Disj.
  by map_tac_m.Disj.
  by map_tac_m.Equal.
Qed.

Lemma Lst_app' e1 e2 s h1 : Lst e1 e2 s h1 ->
  forall e3 h2 h, Lst e2 e3 s h2 ->
    h1 # h2 ->
    h = h1 \U h2  ->
    [ e3 ]e_ s = 0%Z ->
    Lst e1 e3 s h.
Proof.
move=> H.
induction H; intros.
- red in H0.
  subst h.
  rewrite assert_m.heap.unioneh in H3.
  subst h2.
  clear H2.
  by apply Lst_equiv with e2 e3.
- apply Lst_next with (h1 := h1) (h2 := h2 \U h0) (e2 := e2) (e4 := e4); auto.
  by map_tac_m.Disj.
  by map_tac_m.Equal.
  by rewrite H9.
  eapply IHLst; eauto.
  by map_tac_m.Disj.
Qed.

(** a Sigma formula is a spatial formula composed of the following connectives *)
Inductive Sigma : Type :=
| singl : expr -> expr -> Sigma
| cell : expr -> Sigma
| emp : Sigma
| star : Sigma -> Sigma -> Sigma
| lst : expr -> expr -> Sigma.

Fixpoint Sigma_interp (a : Sigma) : assert :=
  match a with
    | singl e1 e2 => fun s h => (e1 |~> e2) s h /\ [ e1 ]e_ s <> 0%Z
    | emp => assert_m.emp
    | star s1 s2 => Sigma_interp s1 ** Sigma_interp s2
    | cell e => fun s h => (exists v, (e |~> cst_e v) s h) /\ [ e ]e_ s <> 0%Z
    | lst e1 e2 => Lst e1 e2
  end.

(** an assrt is a pair of an expr_b and a Sigma formula *)
Definition assrt := (expr_b * Sigma)%type.

Definition assrt_interp (a : assrt) : assert :=
  match a with
    | (pi, sigm) => fun s h => [ pi ]b_ s /\ Sigma_interp sigm s h
  end.

(** an Assrt is a disjunction of assrts *)
Definition Assrt := list assrt.

Fixpoint Assrt_interp (l : Assrt) : assert :=
  match l with
    | nil => fun s h => False
    | hd :: tl => fun s h => assrt_interp hd s h \/ Assrt_interp tl s h
  end.

Notation "{{{ P }}} c {{{ Q }}}" := (while.hoare store.t heap.t cmd0 expr_b
(fun eb s => eval_b eb (fst s)) hoare0 (assrt_interp P) c (Assrt_interp (Q :: nil))) (at level 80) : frag_list_scope.
Local Open Scope frag_list_scope.

(** A proof system for assrt entailment *)

Notation "s \** t" := (star s t) (at level 80) : entail_scope.
Local Open Scope entail_scope.

Inductive entail : assrt -> assrt -> Prop :=
(** final rules *)
| entail_incons : forall pi1 pi2 sig1 sig2,
  (forall s, [ pi1 ]b_s -> False) ->
  entail (pi1, sig1) (pi2, sig2)

| entail_tauto : forall pi1 pi2,
  (forall s, [ pi1 ]b_s -> [ pi2 ]b_s) ->
  entail (pi1, emp) (pi2, emp)
(** structural rules *)
| entail_coml : forall pi1 sig1 sig2 L,
  entail (pi1, sig2 \** sig1) L -> entail (pi1, sig1 \** sig2) L

| entail_comr : forall pi1 sig1 sig2 L,
  entail L (pi1, sig2 \** sig1)  -> entail L (pi1, sig1 \** sig2)

| entail_assocl : forall pi1 sig1 sig2 sig3 L,
  entail (pi1, (sig1 \** sig2) \** sig3) L ->
  entail (pi1, sig1 \** (sig2 \** sig3)) L

| entail_assocr : forall pi1 sig1 sig2 sig3 L,
  entail L (pi1, (sig1 \** sig2) \** sig3)  ->
  entail L (pi1, sig1 \** (sig2 \** sig3))

| entail_empeliml : forall pi1 sig1 L,
  entail (pi1, sig1) L -> entail (pi1, sig1 \** emp) L

| entail_empelimr : forall pi1 sig1 L,
  entail L (pi1, sig1) -> entail L (pi1, sig1 \** emp)

| entail_empintrol : forall pi1 sig1 L,
  entail (pi1, sig1 \** emp) L -> entail (pi1, sig1) L

| entail_empintror : forall pi1 sig1 L,
  entail L (pi1, sig1 \** emp) -> entail L (pi1, sig1)
(** elimination rules for list *)
| entail_lstnilelimr : forall pi1 sig1 pi2 sig2 e1 e2,
  (forall s, [ pi1 ]b_ s -> [ e1 \= e2 ]b_ s) ->
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1) (pi2, sig2 \** (lst e1 e2))

| entail_lstnileliml : forall pi1 sig1 pi2 sig2 e1 e2,
  (forall s, [ pi1 ]b_ s -> [ e1 \= e2 ]b_ s) ->
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1 \** (lst e1 e2)) (pi2, sig2)

| entail_lstsamelst : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s) ->
  (forall s, [ pi1 ]b_ s -> [ e2 \= e4 ]b_ s) ->
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1 \** (lst e1 e2)) (pi2, sig2 \** (lst e3 e4))

| entail_lstelim : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s) ->
  entail (pi1, sig1 \** cell e4) (pi2, sig2 \** (lst e2 e4)) ->
  entail (pi1, (sig1 \** cell e4) \** lst e1 e2) (pi2, sig2 \** lst e3 e4)

| entail_lstelim_v2 : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4 sig1',
  (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s = true) ->
  entail (pi1, sig1) (pi1, sig1' \** cell e4) ->
  entail (pi1, sig1' \** cell e4) (pi2, sig2 \** lst e2 e4) ->
  entail (pi1, sig1 \** lst e1 e2) (pi2, sig2 \** lst e3 e4)

| entail_lstelim' : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4 e5,
  (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s ) ->
  (forall s, [ pi1 ]b_ s -> [ e4 \!= e5 ]b_ s ) ->
  entail (pi1, sig1 \** lst e4 e5) (pi2, sig2 \** lst e2 e4) ->
  entail (pi1, (sig1 \** lst e4 e5) \** lst e1 e2) (pi2, sig2 \** lst e3 e4)

| entail_lstelim'_v2 : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4 e5 sig1',
  (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s ) ->
  entail (pi1, sig1) (pi1, sig1' \** lst e4 e5) ->
  (forall s, [ pi1 ]b_ s  -> [e4 \!= e5]b_ s ) ->
  entail (pi1, sig1' \** lst e4 e5) (pi2, sig2 \** lst e2 e4) ->
  entail (pi1, sig1 \** lst e1 e2) (pi2, sig2 \** lst e3 e4)

| entail_lstelim'' : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, [ pi1 ]b_s -> [ e1 \= e3 ]b_ s ) ->
  (forall s, [ pi1 ]b_s -> [ e4 \= cst_e 0%Z ]b_ s ) ->
  entail (pi1, sig1) (pi2, sig2 \** lst e2 e4) ->
  entail (pi1, sig1 \** lst e1 e2) (pi2, sig2 \** lst e3 e4)

| entail_lstelim''' : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s ) ->
  (forall s, [ pi1 ]b_ s -> [ e1 \!= e4 ]b_ s ) ->
  (forall s, [ pi1 ]b_ s -> [ e1 \!= cst_e 0%Z ]b_ s ) ->
  entail (pi1, sig1) (pi2, sig2 \** (cell (e1 \+ nat_e 1) \** lst e2 e4)) ->
  entail (pi1, sig1 \** singl e1 e2) (pi2, sig2 \** lst e3 e4)
(** rule to eliminate mapstos *)
| entail_star_elim : forall pi1 pi2 sig1 sig2 e1 e2 e3 e4,
  (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s) ->
  (forall s, [ pi1 ]b_ s -> [ e2 \= e4 ]b_ s) ->
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1 \** (singl e1 e2)) (pi2, sig2 \** singl e3 e4)

| entail_star_elim' : forall pi1 pi2 sig1 sig2 e1 e2 e3,
  (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s ) ->
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1 \** singl e1 e2) (pi2, sig2 \** (cell e3))

| entail_star_elim'' : forall pi1 pi2 sig1 sig2 e1 e3,
  (forall s, [ pi1 ]b_ s -> [ e1 \= e3 ]b_ s) ->
  entail (pi1, sig1) (pi2, sig2) ->
  entail (pi1, sig1 \** cell e1) (pi2, sig2 \** (cell e3))
(** rule to generate constraints *)
| entail_star_neq : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  entail (pi1 \&& (e1 \!= e3), sig1 \** (singl e1 e2 \** singl e3 e4)) (pi2, sig2) ->
  entail (pi1, sig1 \** (singl e1 e2 \** singl e3 e4)) (pi2, sig2)

| entail_star_neq' : forall pi1 sig1 pi2 sig2 e1 e2 e3,
  entail (pi1 \&& (e1 \!= e3), sig1 \** (singl e1 e2 \** cell e3)) (pi2, sig2) ->
  entail (pi1, sig1 \** ((singl e1 e2) \** cell e3)) (pi2, sig2)

| entail_star_neq'' : forall pi1 sig1 pi2 sig2 e1 e3,
  entail (pi1 \&& (e1 \!= e3), sig1 \** (cell e1 \** cell e3)) (pi2, sig2) ->
  entail (pi1, sig1 \** (cell e1 \** cell e3)) (pi2, sig2)

| entail_star_neq''' : forall pi1 sig1 pi2 sig2 e1 e2 e3,
  (forall s, [ pi1 ]b_ s -> [ e1 \!= e2 ]b_ s) ->
  entail (pi1 \&& (e1 \!=e3), sig1 \** (lst e1 e2 \** cell e3)) (pi2, sig2) ->
  entail (pi1, sig1 \** (lst e1 e2 \** cell e3)) (pi2, sig2)

| entail_star_neq'''' : forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, [ pi1 ]b_ s  -> [ e1 \!= e2 ]b_ s ) ->
  entail (pi1 \&& (e1 \!= e3), sig1 \** (lst e1 e2 \** singl e3 e4)) (pi2, sig2) ->
  entail (pi1, sig1 \** (lst e1 e2 \** singl e3 e4)) (pi2, sig2)

| entail_star_neq''''': forall pi1 sig1 pi2 sig2 e1 e2 e3 e4,
  (forall s, [ pi1 ]b_ s -> [ e1 \!= e2 ]b_ s) ->
  (forall s, [ pi1 ]b_ s -> [ e3 \!= e4 ]b_ s) ->
  entail (pi1 \&& (e1 \!= e3), sig1 \** (lst e1 e2 \** lst e3 e4)) (pi2, sig2) ->
  entail (pi1, sig1 \** (lst e1 e2 \** lst e3 e4)) (pi2, sig2)

| entail_singl_not_null : forall pi1 sig1 pi2 sig2 e1 e2,
  entail (pi1 \&& (e1 \!= (nat_e 0)), sig1 \** singl e1 e2) (pi2, sig2) ->
  entail (pi1, sig1 \** singl e1 e2) (pi2, sig2)

| entail_cell_not_null : forall pi1 sig1 pi2 sig2 e1,
  entail (pi1 \&& (e1 \!= nat_e 0), sig1 \** (cell e1)) (pi2, sig2) ->
  entail (pi1, sig1 \** cell e1) (pi2, sig2)

| entail_lst_not_null : forall pi1 sig1 pi2 sig2 e1 e2,
  (forall s, [ pi1 ]b_ s -> [ e2 \!= nat_e 0 ]b_ s ) ->
  entail (pi1 \&& e1 \!= nat_e 0, sig1 \** lst e1 e2) (pi2, sig2) ->
  entail (pi1, sig1 \** lst e1 e2) (pi2, sig2)
(* NB: is entail_monotony really useful? *)
| entail_monotony : forall pi1 pi2 sig11 sig12 sig21 sig22,
  entail (pi1, sig11) (pi2, sig21) ->
  entail (pi1, sig12) (pi2, sig22) ->
  entail (pi1, sig11 \** sig12) (pi2, sig21 \** sig22)

| entail_destructlist: forall pi1 pi2 sig1 sig2 e1 e2,
  (entail (pi1 \&& e1 \= e2, sig1 \** lst e1 e2) (pi2, sig2)) ->
  (entail (pi1 \&& e1 \!= e2, sig1 \** lst e1 e2) (pi2, sig2)) ->
  entail (pi1, star sig1 (lst e1 e2)) (pi2, sig2).

Notation "s '|--' t" := (entail s t) (at level 80) : entail_scope.

(** derived rules *)

Lemma entail_id : forall sig pi, (pi, sig) |-- (pi, sig).
Proof.
induction sig; intros.
- apply entail_empintror.
  apply entail_empintrol.
  apply entail_coml.
  apply entail_comr.
  apply entail_star_elim.
  move=> *; exact/eqP.
  move=> *; exact/eqP.
  by apply entail_tauto; auto.
- apply entail_empintror.
  apply entail_empintrol.
  apply entail_coml.
  apply entail_comr.
  apply entail_star_elim''.
  move=> *; exact/eqP.
  by apply entail_tauto; auto.
- by apply entail_tauto; auto.
- by apply entail_monotony; auto.
- apply entail_empintror.
  apply entail_empintrol.
  apply entail_coml.
  apply entail_comr.
  apply entail_lstsamelst.
  move=> *; exact/eqP.
  move=> *; exact/eqP.
  by apply entail_tauto; auto.
Qed.

Lemma entail_star_elim_lst pi1 sig1 pi2 sig2 e1 e2 :
  (pi1, sig1) |-- (pi2, sig2) ->
  (pi1, sig1 \** lst e1 e2) |-- (pi2, sig2 \** lst e1 e2).
Proof.
move=> H.
apply entail_lstsamelst; auto.
  move=> *; exact/eqP.
  move=> *; exact/eqP.
Qed.

Lemma entail_star_elim_star : forall s pi1 sig1 pi2 sig2,
  (pi1, sig1) |-- (pi2, sig2) -> (pi1, sig1 \** s) |-- (pi2, sig2 \** s).
Proof.
induction s; intros.
- apply entail_star_elim; last by [].
  move=> *; exact/eqP.
  move=> *; exact/eqP.
- apply entail_star_elim''; last by [].
  move=> *; exact/eqP.
- apply entail_empeliml.
  by apply entail_empelimr.
- apply entail_assocr, entail_assocl.
  by apply IHs2, IHs1.
- apply entail_lstsamelst; last by [].
  move=> *; exact/eqP.
  move=> *; exact/eqP.
Qed.

(** Soundness of the proof system *)

Lemma entail_soundness P Q : P |-- Q -> assrt_interp P ===> assrt_interp Q.
Proof.
induction 1; rewrite /while.entails; simpl; intros.
- move: (H s); tauto.
- move: (H s); tauto.
- apply IHentail; by rewrite /= assert_m.conCE.
- rewrite assert_m.conCE; exact: IHentail.
- apply IHentail; by rewrite /= assert_m.conAE.
- rewrite -assert_m.conAE; exact: IHentail.
- apply IHentail => /=.
  split; first tauto.
  apply assert_m.con_emp; tauto.
- move: (IHentail s h H0) => /= H1.
  split; first tauto.
  apply assert_m.con_emp'; tauto.
- apply IHentail => /=.
  split; first tauto.
  apply assert_m.con_emp'; tauto.
- move: (IHentail s h H0) => /= H1.
  split; first tauto.
  apply assert_m.con_emp; tauto.
- move: (IHentail s h H1) => /= H2.
  split; first tauto.
  Compose_sepcon h assert_m.heap.emp.
  tauto.
  apply Lst_end; last by [].
  apply/eqP/(H s); tauto.
- apply IHentail => /=.
  split; first by tauto.
  case: H1 => H2 H3.
  case_sepcon H3.
  destruct H3_h2.
  + rewrite /assert_m.emp in H3; subst h0.
    rewrite assert_m.heap.unionhe in h1_U_h2; by subst h1.
  + have ? : [ e1 ]e_ s = [ e3 ]e_ s by apply/eqP/H.
    contradiction.
- case : H2 => H3 H4.
  case_sepcon H4.
  case: (IHentail _ _ (conj H3 H4_h1)) => H8 H9.
  split; first by [].
  Compose_sepcon h1 h2; first by [].
  eapply Lst_equiv.
  + by apply H4_h2.
  + exact/eqP/(H s).
  + exact/eqP/(H0 s).
- case: H1 => H2 H3.
  case_sepcon H3.
  case: {IHentail}(IHentail _ _ (conj H2 H3_h1)) => /= H7 H8.
  case_sepcon H8.
  split; first by exact H7.
  Compose_sepcon h11 (h12 \U h2); first by [].
  case_sepcon H3_h1.
  eapply Lst_app.
  + eapply Lst_equiv.
    exact: H3_h2.
    exact/eqP/(H s).
    reflexivity.
  + exact: H8_h12.
  + by apply H3_h1_h3.
  + by map_tac_m.Disj.
  + by map_tac_m.Disj.
  + by map_tac_m.Equal.
- case: H2 => H3 H4.
  case_sepcon H4.
  case: (IHentail1 _ _ (conj H3 H4_h1)) => /= _ H9.
  case: (IHentail2 _ _ (conj H3 H9)) => /= H8 H10.
  split; first by [].
  case_sepcon H10.
  Compose_sepcon h11 (h12 \U h2); first by [].
  case_sepcon H9.
  eapply Lst_app.
  eapply Lst_equiv.
  by apply H4_h2.
  exact/eqP/(H s).
  reflexivity.
  by apply H10_h12.
  by apply H9_h3.
  by map_tac_m.Disj.
  by map_tac_m.Disj.
  by map_tac_m.Equal.
- case : H2 => H3 H4.
  case_sepcon H4.
  case: (IHentail _ _ (conj H3 H4_h1)) => /= H8 H9.
  split; first by [].
  case_sepcon H9.
  Compose_sepcon h11 (h12 \U h2); first by [].
  case_sepcon H4_h1.
  inversion H4_h1_h3.
  + generalize (H0 s H3).
    by rewrite /= H2 => /eqP.
  + case_sepcon H9.
    eapply Lst_app with (h3 := h51).
    eapply Lst_equiv.
    by apply H4_h2.
    move: (H s H3) => /= H28; exact/eqP.
    reflexivity.
    by apply H9_h12.
    exists ([ e6 ]e_ s).
    by Mapsto.
    by map_tac_m.Disj.
    by map_tac_m.Disj.
    by map_tac_m.Equal.
- case : H3 => H4 H5.
  case_sepcon H5.
  move/IHentail1 : (conj H4 H5_h1) => /= H7.
  case/IHentail2 : (H7) => /= H10 H11.
  split; first by [].
  case_sepcon H11.
  case: H7 => H13 H15.
  case_sepcon H15.
  rewrite h1_U_h2 h11_U_h12.
  Compose_sepcon h11 (h12 \U h2); first by [].
  inversion_clear H15_h3.
  - generalize (H1 s H4) => ?; by omegab.
  - case_sepcon H9.
    eapply Lst_app with (h3 := h51).
    eapply Lst_equiv.
    by apply H5_h2.
    generalize (H s H4) => ?; by omegab.
    reflexivity.
    by apply H11_h12.
    exists ([ e6 ]e_ s).
    by Mapsto.
    by map_tac_m.Disj.
    by map_tac_m.Disj.
    by map_tac_m.Equal.
- case: H2 => H3 H4.
  case_sepcon H4.
  case: (IHentail _ _ (conj H3 H4_h1)) => /= H8 H9.
  split; first by [].
  case_sepcon H9.
  Compose_sepcon h11 (h12 \U h2); auto.
  eapply Lst_app'.
  eapply Lst_equiv.
  by apply H4_h2.
  generalize (H s H3) => ?; by omegab.
  reflexivity.
  by apply H9_h12.
  by map_tac_m.Disj.
  by map_tac_m.Equal.
  move: (H0 s H3) => ?; by omegab.
- case: H3 => H4 H5.
  case_sepcon H5.
  case : H5_h2 => H5_h2 H5_h2'.
  case: (IHentail s h1 (conj H4 H5_h1)) => /= H10 H11.
  case_sepcon H11.
  case_sepcon H11_h12.
  inversion_clear H11_h12_h121 as [H3 H5].
  case : H3 => x H3.
  split; first by [].
  Compose_sepcon h11 (h12 \U h2).
  assumption.
  eapply Lst_next with (h1 := (h2 \U h121)) (h2 := h122) (e4 := (cst_e x)).
  by map_tac_m.Disj.
  by map_tac_m.Equal.
  move: (H s H4); move: (H0 s H4); move/eqP => ?; by move/eqP => <-.
  move: (H s H4); move: (H1 s H4); move/eqP => ?. by move/eqP => <-.
  move: (H s H4); move: (H s H4); move/eqP => H19; by move/eqP => /= <-.
  Compose_sepcon h2 h121.
  Mapsto.
  generalize (H s H4) => ?; by omegab.
  Mapsto.
  generalize (H s H4); by move/eqP => ->.
  assumption.
- case: H2 => H3 H4.
  case_sepcon H4.
  case : H4_h2 => H4_h2 H4_h2'.
  case: (IHentail s h1 (conj H3 H4_h1)) =>/=  H7 H9.
  split; first by [].
  Compose_sepcon h1 h2.
  assumption.
  move: (H s H3) (H0 s H3) => H10 H11.
  split.
  Mapsto.
  by move/eqP : H10 => <-.
- case: H1 => H2 H3.
  case_sepcon H3.
  case : H3_h2 => H3_h2 H3_h2'.
  case: (IHentail s h1 (conj H2 H3_h1)) => /= H6 H8.
  split; first by [].
  Compose_sepcon h1 h2.
  assumption.
  generalize (H s H2) => H9.
  split.
  exists ([ e2 ]e_ s).
  by Mapsto.
  by move/eqP : H9 => <-.
- case: H1 => H2 H3.
  case_sepcon H3.
  case : H3_h2 => [ [x H3_h2] H3_h2'].
  case: (IHentail s h1 (conj H2 H3_h1)) => /= H6 H9.
  split; first by [].
  Compose_sepcon h1 h2.
  assumption.
  generalize (H s H2) => H8.
  split.
  exists x.
  by Mapsto.
  by move/eqP : H8 => <-.
- apply IHentail => /=.
  case: H0 => H1 H2.
  split.
  rewrite H1 /=.
  case_sepcon H2.
  case_sepcon H2_h2.
  apply/eqP.
  eapply singl_disj_neq.
  exact: (proj1 H2_h2_h21).
  exact: (proj1 H2_h2_h22).
  done.
  assumption.
- apply IHentail => /=.
  case: H0 => H1 H2.
  split.
  rewrite H1 /=.
  case_sepcon H2.
  case_sepcon H2_h2.
  case: H2_h2_h22 => [ [x H2_h2_h22] H2_h2_h22'].
  apply/eqP.
  eapply singl_disj_neq.
  exact: (proj1 H2_h2_h21).
  exact: H2_h2_h22.
  done.
  assumption.
- apply IHentail => /=.
  case: H0 => H1 H2.
  split; last by exact H2.
  rewrite H1 /=.
  case_sepcon H2.
  case_sepcon H2_h2.
  case : H2_h2_h21 => [ [x H2_h2_h21] H2_h2_h21'].
  case : H2_h2_h22 => [ [x0 H2_h2_h22] H2_h2_h22'].
  apply/eqP.
  by apply (singl_disj_neq _ (cst_e x) _  (cst_e x0) h21 h22).
- apply IHentail => /=.
  case : H1 => H2 H3.
  split; last by exact H3.
  rewrite H2 /=.
  case_sepcon H3.
  case_sepcon H3_h2.
  case : H3_h2_h22 => [ [x H3_h2_h22] H3_h2_h22'].
  move: (H s H2) => H1.
  destruct H3_h2_h21; first by omegab.
  apply/eqP.
  case_sepcon H8.
  eapply singl_disj_neq.
  by apply H8_h31.
  by apply H3_h2_h22.
  by map_tac_m.Disj.
- apply IHentail => /=.
  case : H1 => H2 H3.
  split; last by exact H3.
  rewrite H2 /=.
  case_sepcon H3.
  case_sepcon H3_h2.
  move: (H s H2) => H1.
  destruct H3_h2_h21; first by omegab.
  apply/eqP.
  case_sepcon H8.
  eapply singl_disj_neq.
  by apply H8_h31.
  by apply (proj1 H3_h2_h22).
  by map_tac_m.Disj.
- apply IHentail => /=.
  case : H2 => H3 H4.
  split; last by exact H4.
  rewrite H3 /=.
  case_sepcon H4.
  case_sepcon H4_h2.
  generalize (H s H3) => H9.
  generalize (H0 s H3) => H11.
  destruct H4_h2_h21; first by omegab.
  destruct H4_h2_h22; first by omegab.
  apply/eqP.
  move/eqP : H11 => /= H11.
  case_sepcon H16.
  case_sepcon H8.
  eapply singl_disj_neq.
  by apply H8_h31.
  by apply H16_h61.
  by map_tac_m.Disj.
- apply IHentail => /=.
  case : H0 => H1 H2.
  split; last by [].
  case_sepcon H2.
  rewrite H1 /=.
  case : H2_h2 => H2_h2 H2_h2'.
  exact/eqP.
- apply IHentail => /=.
  case : H0 => H1 H2.
  split; last by [].
  case_sepcon H2.
  rewrite H1 /=.
  case : H2_h2 => [ [ x H2_h2] H2_h2'].
  exact/eqP.
- apply IHentail => /=.
  case : H1 => H2 H3.
  split; last by [].
  case_sepcon H3.
  rewrite H2; simpl.
  generalize (H _ H2) => /= H1.
  inversion_clear H3_h2.
  rewrite H3.
  assumption.
  exact/eqP.
- case: H1 => H2 H3.
  case_sepcon H3.
  move: (IHentail1 _ _ (conj H2 H3_h1)); move: (IHentail2 _ _ (conj H2 H3_h2)); move=>/=  [H8 H9] [H5 H10].
  split; first by [].
  by Compose_sepcon h1 h2.
- case/boolP : ([ e1 ]e_ s == [ e2 ]e_ s) => H3.
  apply IHentail1 => /=.
  case : H1 => H2 H4.
  split; [by rewrite H2 | exact H4].
  case : H1 => H2 h4.
  apply IHentail2 => /=.
  split; by [rewrite H2|].
Qed.

Lemma entail_to_Sigma_impl sig1 sig2 :
  (true_b, sig1) |-- (true_b, sig2) -> Sigma_interp sig1 ===> Sigma_interp sig2.
Proof.
move/entail_soundness.
rewrite /while.entails /= => H0 s h H1.
by case: (H0 _ _ (conj refl_equal H1)).
Qed.

Local Close Scope entail_scope.

(** tactics to prove a entail goal *)

(** Tactic that turn the left/right hand side of entailment and that add an empty is there is only one subheap*)
Ltac Entail_turnl :=
  match goal with
    | |- entail (?Pi, cell ?e) ?L => eapply entail_empintrol; eapply entail_coml; repeat eapply entail_assocl
    | |- entail (?Pi, singl ?e1 ?e2) ?L => eapply entail_empintrol; eapply entail_coml; repeat eapply entail_assocl
    | |- entail (?Pi, lst ?e1 ?e2) ?L => eapply entail_empintrol; eapply entail_coml; repeat eapply entail_assocl
    | |- entail (?Pi, star ?e1 ?e2) ?L => eapply entail_coml; repeat eapply entail_assocl
    | _ => eapply entail_empintrol; eapply entail_coml; repeat eapply entail_assocl
  end.

Ltac Entail_turnr :=
  match goal with
    | |- entail ?L (?Pi, cell ?e) => eapply entail_empintror; eapply entail_comr; repeat eapply entail_assocr
    | |- entail ?L (?Pi, singl ?e1 ?e2) => eapply entail_empintror; eapply entail_comr; repeat eapply entail_assocr
    | |- entail ?L (?Pi, lst ?e1 ?e2) => eapply entail_empintror; eapply entail_comr; repeat eapply entail_assocr
    | |- entail ?L (?Pi, star ?e1 ?e2) => eapply entail_comr; repeat eapply entail_assocr
    | _ => eapply entail_empintror; eapply entail_comr; repeat eapply entail_assocr
  end.

(** Eliminate left most subheap from lhs and rhs *)

Ltac Elim_subheap := repeat eapply entail_assocl; repeat eapply entail_assocr;
  match goal with
    | |- entail (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, star ?sig2 (singl ?e3 ?e4)) =>
      apply entail_star_elim;
        [ (do 2 intro; omegab) | (do 2 intro; omegab) | idtac]

    | |- entail (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, star ?sig2 (cell ?e3)) =>
      apply entail_star_elim'; [ (do 2 intro; omegab) | idtac]

    | |- entail (?pi1, star ?sig1 (cell ?e1)) (?pi2, star ?sig2 (cell ?e3)) =>
      apply entail_star_elim'' ; [ (do 2 intro; omegab) | idtac]

    | |- entail (?pi1, star ?sig1 (lst ?e1 ?e2)) (?pi2, star ?sig2 (lst ?e3 ?e4)) =>
      (apply entail_lstsamelst; [ (do 2 intro; omegab) | (do 2 intro; omegab) | idtac])  ||
      (apply entail_lstelim''; [ (do 2 intro; omegab) | (do 2 intro; omegab) | idtac])

    | |- entail (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, star ?sig2 (lst ?e3 ?e4)) =>
      apply entail_lstelim''';
        [ (do 2 intro; omegab) | (do 2 intro; omegab) | (do 2 intro; omegab) | idtac]

    | |- entail (?pi1, star ?sig1 ?s) (?pi2, star ?sig2 ?s) =>
      eapply entail_star_elim_star

  end.

(** Prove simpl goal (= that does not need subheap elimination) *)

Ltac Entail_arith_impl :=
  match goal with
    | |- entail (?pi, ?sig) (?pi, ?sig) =>
      eapply entail_id
    | |- entail (?pi1, emp) (?pi2, emp) => eapply entail_tauto; [do 2 intro; omegab]
    | |- entail (?pi1, emp) (?pi2, emp) => eapply entail_incons; [do 2 intro; omegab]
  end.

(** eliminate every empty subheap *)

Ltac Entail_elim_emp :=
  match goal with
    | |- entail (?pi1, star ?sig1 emp) (?pi2, ?sig2) => eapply entail_empeliml; Entail_elim_emp
    | |- entail (?pi1, ?sig1) (?pi2, star ?sig2 emp) => eapply entail_empelimr; Entail_elim_emp
    | |- _ => idtac
  end.

(** add location not null constraints *)

Ltac Entail_not_nul_constraint :=
  match goal with
    | |- entail (?pi1, star ?sig1 (cell ?e)) (?pi2, ?sig2) =>
      eapply entail_cell_not_null; idtac
    | |- entail (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, ?sig2) =>
      eapply entail_singl_not_null; idtac
    | |- entail (?pi1, star ?sig1 (lst ?e1 ?e2)) (?pi2, ?sig2) =>
      apply entail_lst_not_null;   [ (do 2 intro; omegab)  |  idtac ]
    | |- _ => idtac
  end.

(** compute the number of subheaps *)

Ltac Entail_count_subheap sig :=
  match sig with
    | star ?sig1 ?sig2 =>
      let x := Entail_count_subheap sig1 in
        let y := Entail_count_subheap sig2 in
          constr:(x + y)
    | _ =>
      constr:(1)
  end.

(* debugging *)
(*Ltac Printt x := assert (x = x).*)

(** Turn the rhs at most m time until an elimination could be performed *)

Ltac Entail_elim_right n m :=
  let y := constr:((n > m)%nat) in
    match (eval compute in y) with
      | true => idtac
      | false =>
        Entail_turnr; (Elim_subheap || (
        let x := (constr:(S n)) in Entail_elim_right x m))
    end.

(** try to solve the goal or try to eliminate the left most subheap of lhs *)

Ltac Entail_elim_left := Entail_not_nul_constraint;
  match goal with
    | |- entail (?pi1, ?sig1) (?pi2, ?sig2) =>
      Entail_elim_emp; Entail_arith_impl
    | |- entail (?pi1, ?sig1) (?pi2, ?sig2) =>
      let x := Entail_count_subheap sig2 in (
        let vx := eval compute in x in
          Entail_elim_right 0 vx
      ); Entail_turnl
  end.

Ltac Entail := repeat Entail_elim_left.

(** Example in the PPL 2007 draft *)

Module examples.

Definition nil : expr := nat_e 0.
Definition e : expr := var_e 0.
Definition e' : expr := var_e 1.
Definition e'' : expr := var_e 2.

Goal entail
(true_b,
star (lst e e') (
star (singl e' e'') (
star (cell (e' \+ (nat_e 1))) (
lst e'' (nat_e 0)
))))
(true_b, lst e (nat_e 0)).
unfold e; unfold e'; unfold e''; unfold nil.
Entail.
Qed.

Definition null : expr := nat_e 0.
Definition v1 : expr := var_e 4.
Definition v2 : expr := var_e 5.
Definition x1 : expr := var_e 0.
Definition x2 : expr := var_e 1.
Definition x3 : expr := var_e 2.
Definition x4 : expr := var_e 3.
Definition x5 : expr := var_e 4.
Definition x6 : expr := var_e 5.

Definition P := (x3 \!= null \&& x5 \!= null \&& x6 \= null \&& x3 \!= x5,
  (star (lst x1 x3)
    (star (singl x3 x5)
      (star (cell (x3 \+ nat_e 1))
        (lst x5 x6))))).

Definition Q' := ( true_b, star (lst x1 x5) (lst x5 x6) ).

Definition Q := ( true_b, (lst x1 x6) ).

Ltac Print h :=
  let y := (eval compute in h) in assert (y = y); auto.

Ltac Nb_sig_elt sig :=
  match sig with
    | singl ?e1 ?e2 =>
      constr:(1)
    | cell ?e1 =>
      constr:(1)
    | emp =>
      constr:(1)
    | star ?sig1 ?sig2 =>
      let x := (Nb_sig_elt sig1) in
        let y := (Nb_sig_elt sig2) in
          constr:(x + y)
    | lst ?e1 ?e2 =>
      constr:(1)
  end.

Ltac Nb_sig_elt_entail_right :=
  match goal with
    | |- entail (?pi1,?sig1) (?pi2,?sig2) =>
      Nb_sig_elt sig2
  end.

Ltac Nb_sig_elt_entail_left :=
  match goal with
    | |- entail (?pi1,?sig1) (?pi2,?sig2) =>
      Nb_sig_elt sig1
  end.

Goal (assrt_interp P) ===> (assrt_interp Q).
  apply entail_soundness.
Proof.
unfold P, Q, x1, x2, x3, x4, x5, x6, null.
by Entail.
Qed.

Goal (assrt_interp P) ===> (assrt_interp Q').
Proof.
apply entail_soundness.
unfold P, Q', x1, x2, x3, x4, x5, x6, null.

Entail_turnl.
Entail_turnr.
eapply entail_lstelim'_v2.
intros; by omegab.
Entail_turnl.
Entail_turnl.
eapply entail_star_elim_lst.
eapply entail_id.
intros; by omegab.

Entail_turnr.
Entail_turnl.
Entail_turnl.
Entail_turnl.
eapply entail_lstsamelst.
intros; by omegab.
intros; by omegab.

Entail_turnr.
Entail_turnl.
eapply entail_lstelim'''.
intros; by omegab.
intros; by omegab.
intros; by omegab.

Entail_turnr.
Entail_turnl.
Entail_turnr.
eapply entail_lstnilelimr.
intros; by omegab.

Entail.
Qed.

End examples.

(** load the decision procedure for expr_b *)

Fixpoint remove_empty_heap (pi : expr_b) (sig : Sigma) {struct sig} : Sigma :=
  match sig with
    | star sig1 sig2 =>
      match remove_empty_heap pi sig1 with
        | emp => remove_empty_heap pi sig2
        | sig1' => match remove_empty_heap pi sig2 with
                   | emp => sig1'
                   | sig2' => star sig1' sig2'
                 end
      end
    | lst e1 e2 => if expr_b_dp (pi =b> (e1 \= e2)) then emp else sig
    | _ => sig
  end.

Lemma remove_empty_heap_correct : forall sig pi s, [ pi ]b_s ->
  forall h, Sigma_interp (remove_empty_heap pi sig) s h -> Sigma_interp sig s h.
Proof.
induction sig; simpl; intros; auto.
- move: {IHsig1}(IHsig1 pi) => IHsig1.
  move: {IHsig2}(IHsig2 pi) => IHsig2.
  destruct (remove_empty_heap pi sig1); destruct (remove_empty_heap pi sig2); simpl in H0; simpl; simpl in IHsig1; simpl in IHsig2;
    (try (
      (case_sepcon H0; Compose_sepcon h1 h2; [apply (IHsig1 _ H); tauto | apply (IHsig2 _ H); tauto])
      || (Compose_sepcon h assert_m.heap.emp; [apply (IHsig1 _ H); tauto | apply (IHsig2 _ H); simpl; red; tauto])
        || (Compose_sepcon assert_m.heap.emp h; [apply (IHsig1 _ H); simpl; red; tauto | apply (IHsig2 _ H); tauto])
          || (red in H0; Compose_sepcon assert_m.heap.emp assert_m.heap.emp; [apply (IHsig1 _ H); simpl; red; tauto | apply (IHsig2 _ H); simpl; red; tauto])
    )).
  move: (expr_b_dp_correct (pi =b> e \= e0)) => H1.
  destruct (expr_b_dp (pi =b> e \= e0)); simpl in H.
  + move: (H1 refl_equal s) => H2.
    apply Lst_end => //.
    by omegab.
  + by auto.
Qed.

Lemma remove_empty_heap_correct' : forall sig pi s, [ pi ]b_s ->
  forall h, Sigma_interp sig s h -> Sigma_interp (remove_empty_heap pi sig) s h.
Proof.
induction sig; simpl; intros; auto.
generalize (IHsig1 pi); clear IHsig1; intro IHsig1.
generalize (IHsig2 pi); clear IHsig2; intro IHsig2.
destruct (remove_empty_heap pi sig1); destruct (remove_empty_heap pi sig2); simpl in H0; simpl;
  (try (
    (case_sepcon H0; Compose_sepcon h1 h2; [apply IHsig1; tauto | apply IHsig2; tauto])
    || (case_sepcon H0; move: (IHsig2 _ H _ H0_h2) => X; rewrite /= in X; red in X; subst h2;
        assert (h = h1); [map_tac_m.Equal | subst h1; apply (IHsig1 _ H); tauto])
      || (case_sepcon H0; move: (IHsig1 _ H _ H0_h1) => X; rewrite /= in X; red in X; subst h1;
          assert (h = h2); [map_tac_m.Equal | subst h2; apply IHsig2; tauto])
  )).
move: (expr_b_dp_correct (pi =b> e \= e0)) => H1.
destruct (expr_b_dp (pi =b> e \= e0)).
+ move: (H1 refl_equal s) => H2.
  destruct H0.
  simpl; red in H3; auto.
  by omegab.
+ by auto.
Qed.

(** returns true if <env,sig> contains (cell e), (singl e _), or (lst e _) <>e emp *)
Fixpoint cell_in_sigma (pi : expr_b) (sig : Sigma) (e : expr) {struct sig} : bool :=
  match sig with
    | singl e1 e2 => expr_b_dp (pi =b> (e1 \= e))
    | cell e1 => expr_b_dp (pi =b> (e1 \= e))
    | lst e1 e2 => andb
      (expr_b_dp (pi =b> (e1 \= e)))
      (expr_b_dp (pi =b> (e1 \!= e2)))
    | star s1 s2 => orb (cell_in_sigma pi s1 e ) (cell_in_sigma pi s2 e)
    | _ => false
  end.

Lemma cell_in_sigma_correct: forall sig e pi, cell_in_sigma pi sig e  ->
  forall s h, [ pi ]b_s ->
    Sigma_interp sig s h -> ((Sigma_interp (cell e)) ** TT) s h.
Proof.
induction sig; simpl; intros; try discriminate.
- generalize (expr_b_dp_correct _ H s); intros.
  Compose_sepcon h assert_m.heap.emp; last by [].
  inversion_clear H1.
  split.
  exists ([ e0 ]e_ s).
  by Mapsto.
  red; intros; eapply H4.
  cutrewrite ([ e ]e_ s = [ e1 ]e_ s).
  assumption.
  by omegab.
- generalize (expr_b_dp_correct _ H s); intros.
  Compose_sepcon h assert_m.heap.emp; last by [].
  inversion_clear H1.
  inversion_clear H3.
  split.
  exists x; Mapsto.
  cutrewrite ([ e0 ]e_ s = [ e ]e_ s).
  by omegab.
  symmetry.
  by omegab.
- generalize (IHsig1 e pi); generalize (IHsig2 e pi); clear IHsig1 IHsig2; intros.
  destruct (cell_in_sigma pi sig1 e); destruct (cell_in_sigma pi sig2 e); simpl in H; try discriminate.
  case_sepcon H1.
  move: {H2}(H2 refl_equal _ _ H0 H1_h2) => H2.
  move: {H3}(H3 refl_equal _ _ H0 H1_h1) => H3.
  case_sepcon H2.
  simpl in H2_h21.
  case : H2_h21 => H1 H2.
  by Compose_sepcon h21 (h1 \U h22).
  case_sepcon H1.
  move: {H3}(H3 refl_equal _ _ H0 H1_h1) => H3.
  case_sepcon H3.
  simpl in H3_h11; case : H3_h11 => H1 H3.
  by Compose_sepcon h11 (h12 \U h2).
  case_sepcon H1.
  move: {H2}(H2 refl_equal _ _ H0 H1_h2) => H2.
  case_sepcon H2.
  simpl in H2_h21; case: H2_h21 => H1 H2.
  by Compose_sepcon h21 (h22 \U h1).
- case/andP : H => H2 H3.
  move: (expr_b_dp_correct _ H3 s) => {H3} H.
  move: {H2}(expr_b_dp_correct _ H2 s) => H2.
  destruct H1.
  + by omegab.
  + case_sepcon H7.
    Compose_sepcon h11 (h12 \U h2); last by [].
    split.
    exists ([ e2 ]e_ s); by Mapsto.
    rewrite (_ : [ e1 ]e_ s = [ e0 ]e_ s); last by symmetry; omegab. (* TODO: *)
    assumption.
Qed.

Opaque remove_empty_heap.

(** returns true if two sigmas are the two same singl, cell ou lst *)
Definition sigma_eq (pi : expr_b) (sig1 sig2 : Sigma)  : bool :=
  match (sig1, sig2) with
    | (emp, emp) => true
    | (singl e1 e2, singl e3 e4) => andb (expr_b_dp (pi =b> (e1 \= e3))) (expr_b_dp (pi =b> (e2 \= e4)))
    | (singl e1 e2, cell e3) => expr_b_dp (pi =b> (e1 \= e3))
    | (cell e1, cell e3) => expr_b_dp (pi =b> (e1 \= e3))
    | (lst e1 e2, lst e3 e4) => andb (expr_b_dp (pi =b> (e1 \= e3))) (expr_b_dp (pi =b> (e2 \= e4)))
    | (_, _) => false
  end.

Lemma sigma_eq_correct: forall sig1 sig2 pi, sigma_eq pi sig1 sig2 ->
  forall s h,
    [ pi ]b_s ->
    (Sigma_interp sig1 s h -> Sigma_interp sig2 s h).
Proof.
destruct sig1; destruct sig2; simpl; intros; try discriminate.
- case: H1 => H6 H7.
  rewrite /sigma_eq in H.
  case/andP : (H) => H2 H3.
  move: (expr_b_dp_correct _ H2 s) => H4.
  move: (expr_b_dp_correct _ H3 s) => H5.
  split.
    by Mapsto.
  rewrite (_ : [ e1 ]e_ s = [ e ]e_ s) //.
  symmetry; by omegab. (* TODO: symmetry before omegab? *)
- case: H1 => H6 H7.
  split.
    exists ([ e0 ]e_ s).
    rewrite /sigma_eq in H.
    move: (expr_b_dp_correct _ H s) => H1.
    by Mapsto.
  move: (expr_b_dp_correct _ H s) => H1.
  rewrite (_ : [ e1 ]e_ s = [ e ]e_ s) //.
  symmetry; by omegab. (* TODO *)
- case : H1; case=> [x H1] H3.
  move: (expr_b_dp_correct _ H s) => H2.
  split.
  exists x.
  by Mapsto.
  rewrite (_ : [ e0 ]e_ s = [ e ]e_ s) //.
  symmetry; by omegab.
- assumption.
- rewrite /sigma_eq in H.
  case/andP : H => H2 H3.
  move: (expr_b_dp_correct _ H2 s) => H4.
  move: (expr_b_dp_correct _ H3 s) => H5.
  eapply Lst_equiv.
  by apply H1.
  by omegab.
  by omegab.
Qed.

(** remove the cell sig of the heap (sig ** sig1) from the heap sig2 *)
Fixpoint elim_common_cell (pi : expr_b) (sig1 remainder sig2 : Sigma)  {struct sig2} : option (Sigma * Sigma) :=
  match sig2 with
    | star sig21 sig22 =>
      match elim_common_cell pi sig1 remainder sig21 with
        | None =>
          match elim_common_cell pi sig1 remainder sig22 with
            | None => None
            | Some (sig1', sig2') => Some (sig1', remove_empty_heap pi (star sig21 sig2'))
          end
        | Some (sig1', sig2') => Some (sig1', remove_empty_heap pi (star sig2' sig22))
      end
    | _ =>
      if sigma_eq  pi sig1 sig2 then Some (emp, emp) else
        match (sig1, sig2) with
          | (lst e11 e12, lst e21 e22) =>
            if andb
              (expr_b_dp (pi =b> (e11 \= e21)))
              (orb
                (expr_b_dp (pi =b> (e22 \= nat_e 0)))
                (cell_in_sigma pi remainder e22) (* cell l22 is contained in remainder *))
              then Some (emp, lst e12 e22) (* sig1 is the prefix-list of sig2 *)
              else None
          | (singl e1 e2, lst e3 e4) =>
            if andb (expr_b_dp (pi =b> (e1 \= e3)))
              (andb (expr_b_dp (pi =b> (e1 \!= e4)))
                (expr_b_dp (pi =b> (e1 \!= nat_e 0))))
              then Some (emp, (star (cell (e1 \+ nat_e 1)) (lst e2 e4)))
                (* sig1 is the leading node of list sig2 *)
              else None
          | (emp, lst e3 e4) =>
            if expr_b_dp (pi =b> (e3 \= e4))
              then Some (emp, emp)
              else Some (emp, sig2)
          | (emp, _) => Some (emp, sig2)
          | _ => None
        end
  end.

Lemma elim_common_cell_mp : forall sig2 sig1 remainder pi sig1' sig2',
  elim_common_cell pi sig1 remainder sig2 = Some (sig1', sig2') ->
  (Sigma_interp sig1 ===> (Sigma_interp sig1' -* Sigma_interp sig1) ** Sigma_interp sig1').
Proof.
induction sig2; simpl; intros.
- destruct (sigma_eq pi sig1 (singl e e0)).
  + case : H => ? ?; subst sig1' sig2'.
    rewrite /while.entails => s h H0.
    Compose_sepcon h assert_m.heap.emp; [by apply emp_imp | done].
  + destruct sig1 => //.
    case: H => ? ?; subst sig1' sig2'.
    rewrite /while.entails /= => s h H0.
    Compose_sepcon assert_m.heap.emp assert_m.heap.emp; [by apply emp_imp | done].
- destruct (sigma_eq pi sig1 (cell e)).
  + case : H => ? ?; subst sig1' sig2'.
    rewrite /while.entails => s h H0.
    Compose_sepcon h assert_m.heap.emp; [by apply emp_imp | done].
  + destruct sig1 => //.
    case : H => ? ?; subst sig1' sig2'.
    rewrite /while.entails /= => s h H0.
    Compose_sepcon assert_m.heap.emp assert_m.heap.emp; [by apply emp_imp | done].
- destruct (sigma_eq pi sig1 emp).
  + case : H => ? ?; subst sig1' sig2'.
    rewrite /while.entails => s h H0.
    Compose_sepcon h assert_m.heap.emp; [by apply emp_imp | done].
  + destruct sig1 => //.
    injection H; intros; subst sig1' sig2'.
    rewrite /while.entails /= => s h H0.
    Compose_sepcon assert_m.heap.emp assert_m.heap.emp; [by apply emp_imp | done].
- move: {IHsig2_1}(IHsig2_1 sig1 remainder pi) => H0.
  destruct (elim_common_cell pi sig1 remainder sig2_1).
  + clear IHsig2_2.
    destruct p.
    case:H => X Y; subst sig1' sig2'.
    by move: {H0}(H0 _ _ refl_equal).
  + clear H0.
    move: {IHsig2_2}(IHsig2_2 sig1 remainder pi) => H0.
    destruct (elim_common_cell pi sig1 remainder sig2_2) => //.
    destruct p.
    case: H => X Y; subst sig1' sig2'.
    by move: {H0}(H0 _ _ refl_equal).
- destruct (sigma_eq pi sig1 (lst e e0)).
  + case : H => ? ?; subst sig1' sig2'.
    rewrite /while.entails /= => s h H.
    Compose_sepcon h assert_m.heap.emp; [by apply emp_imp | done].
  + destruct sig1; try discriminate.
    * destruct (expr_b_dp (pi =b> e1 \= e)); destruct (expr_b_dp (pi =b> e1 \!= e0)); destruct (expr_b_dp (pi =b> e1 \!= nat_e 0)); simpl in H; try discriminate.
      injection H; clear H; intros; subst sig1' sig2'.
      rewrite /while.entails /= => s h H.
      Compose_sepcon h assert_m.heap.emp; [by apply emp_imp | done].
    * destruct (expr_b_dp (pi =b> e \= e0)); simpl in H; try discriminate.
      + case : H => ? ?; subst sig1' sig2'.
        rewrite /while.entails /= => s h H.
        Compose_sepcon h assert_m.heap.emp; [by apply emp_imp | done].
      + case : H => ? ?; subst sig1' sig2'.
        rewrite /while.entails /= => s h H.
        Compose_sepcon h assert_m.heap.emp; [by apply emp_imp | done].
    * destruct (expr_b_dp (pi =b> e1 \= e)); simpl in H; try discriminate.
      destruct (expr_b_dp  (pi =b> e0 \= nat_e 0)); simpl in H; try discriminate.
      + case : H => ? ?; subst sig1' sig2'.
        rewrite /while.entails /= => s h H.
        Compose_sepcon h assert_m.heap.emp; [by apply emp_imp | done].
      + destruct (cell_in_sigma pi remainder e0); simpl in H; try discriminate.
        case: H => ? ?; subst sig1' sig2'.
        rewrite /while.entails /= => s h H.
        Compose_sepcon h assert_m.heap.emp; [by apply emp_imp | done].
Qed.

Lemma elim_common_cell_correct : forall sig2 sig1 remainder pi sig1' sig2',
  elim_common_cell pi sig1 remainder sig2 = Some (sig1', sig2') ->
  forall s, [ pi ]b_s ->
    forall h1 h2 h3 h,
      Sigma_interp sig2' s h1 ->
      (Sigma_interp sig1' -* Sigma_interp sig1) s h2 ->
      Sigma_interp remainder s h3 ->
      h = h1 \U h2 ->
      h1 # h2 ->
      h2 # h3 ->
      Sigma_interp sig2 s h.
Proof.
induction sig2; simpl; intros.
- move: (sigma_eq_correct sig1 (singl e e0) pi) => H7.
  destruct (sigma_eq pi sig1 (singl e e0)).
  + case : H => ? ?; subst sig1' sig2'.
    apply H7; auto.
    apply H2 with h1.
    split; by [map_tac_m.Disj | auto].
    by map_tac_m.Equal.
  + clear H7.
    destruct sig1 => //.
    case : H => ? ?; subst sig1' sig2'.
    simpl in H2; simpl in H1.
    apply emp_imp_inv in H2.
    rewrite /assert_m.emp in H2; subst h2.
    suff : h = h1 by move=> ->.
    by map_tac_m.Equal.
- move: (sigma_eq_correct sig1 (cell e) pi) => H7.
  destruct (sigma_eq pi sig1 (cell e)).
  + case : H => ? ?; subst sig1' sig2'.
    apply H7; auto.
    apply H2 with h1.
    split; by [map_tac_m.Disj | auto].
    by map_tac_m.Equal.
  + clear H7.
    destruct sig1 => //.
    case : H => ? ?; subst sig1' sig2'.
    simpl in H2; simpl in H1.
    apply emp_imp_inv in H2.
    rewrite /assert_m.emp in H2; subst h2.
    suff : h = h1 by move=> ->.
    by map_tac_m.Equal.
- move: (sigma_eq_correct sig1 emp pi) => H7.
  destruct (sigma_eq pi sig1 emp).
  + case : H => ? ?; subst sig1' sig2'.
    apply H7; auto.
    apply H2 with (h' := h1).
    split; by [map_tac_m.Disj | auto].
    by map_tac_m.Equal.
  + clear H7.
    destruct sig1 => //.
    case : H => ? ?; subst sig1' sig2'.
    simpl in H2; simpl in H1.
    apply emp_imp_inv in H2.
    rewrite /assert_m.emp in H2; subst h2.
    suff : h = h1 by move=> ->.
    by map_tac_m.Equal.
- move: (IHsig2_1 sig1 remainder pi); clear IHsig2_1 => H7.
  destruct (elim_common_cell pi sig1 remainder sig2_1) => //.
  + destruct p.
    case : H => ? ?; subst sig1' sig2'.
    have H : Sigma_interp (star s1 sig2_2) s h1.
      eapply remove_empty_heap_correct.
      by apply H0.
      assumption.
    clear H1.
    simpl in H.
    case_sepcon H.
    Compose_sepcon (h11 \U h2) h12.
    apply (H7 _ _ refl_equal _ H0 _ _ _ _ H_h11 H2 H3) => //.
    by map_tac_m.Disj.
    exact H_h12.
  + clear H7.
    move: (IHsig2_2 sig1 remainder pi); clear IHsig2_2 => H7.
    destruct (elim_common_cell pi sig1 remainder sig2_2) => //.
    destruct p.
    case : H => ? ?; subst sig1' sig2'.
    have H : Sigma_interp (star sig2_1 s1) s h1.
      eapply remove_empty_heap_correct.
      by apply H0.
      assumption.
    clear H1.
    simpl in H.
    case_sepcon H.
    Compose_sepcon h11 (h12 \U h2).
    assumption.
    apply (H7 _ _ refl_equal _ H0 _ _ _ _ H_h12 H2 H3) => //.
    by map_tac_m.Disj.
- move: (sigma_eq_correct sig1 (lst e e0) pi) => H7.
  destruct (sigma_eq pi sig1 (lst e e0)).
  + case : H => ? ?; subst sig1' sig2'.
    apply H7; auto.
    apply H2 with (h' := h1).
    split; by [map_tac_m.Disj | auto].
    by map_tac_m.Equal.
  + clear H7.
    destruct sig1=> //.
    + move: (expr_b_dp_correct (pi =b> e1 \= e)) => H7.
      destruct (expr_b_dp (pi =b> e1 \= e)); simpl in H; try discriminate.
      move: (expr_b_dp_correct (pi =b> e1 \!= e0)) => H8.
      destruct (expr_b_dp (pi =b> e1 \!= e0)); simpl in H; try discriminate.
      move: (expr_b_dp_correct (pi =b> e1 \!= nat_e 0)) => H9.
      destruct (expr_b_dp (pi =b> e1 \!= nat_e 0)); simpl in H; try discriminate.
      generalize (H7 refl_equal s); generalize (H8 refl_equal s); generalize (H9 refl_equal s); clear H7 H8 H9 => H7 H8 H9.
      case: H => ? ?; subst sig1' sig2'.
      simpl in H2; simpl in H1.
      case_sepcon H1.
      case : H1_h11 => [ [v H1_h11] H1_h11'].
      eapply Lst_next with (h1 := (h2 \U h11)) (h2 := h12) (e2 := e2) (e4 := cst_e v).
      by map_tac_m.Disj.
      by map_tac_m.Equal.
      rewrite (_ : [ e ]e_ s = [ e1 ]e_ s); last by symmetry; omegab. (*TODO: symmetry before omegab *)
      by omegab.
      rewrite (_ : [ e ]e_ s = [ e1 ]e_ s); last by symmetry; omegab.
      by omegab.
      rewrite /= (_ : [ e ]e_ s = [ e1 ]e_ s); last by symmetry; omegab.
      by omegab.
      Compose_sepcon h2 h11.
      have H11 : (e1 |~> e2) s h2.
        have H : h2 # assert_m.heap.emp /\ assert_m.emp s assert_m.heap.emp.
          split; last by [].
          by map_tac_m.Disj.
        have H1 : h2 = h2 \U assert_m.heap.emp by map_tac_m.Equal.
        by apply (proj1 (H2 assert_m.heap.emp H h2 H1)).
      by Mapsto.
      Mapsto.
      rewrite (_ : [ e ]e_ s = [ e1 ]e_ s); last by symmetry; omegab.
      by omegab.
      assumption.
    + move: (expr_b_dp_correct (pi =b> e \= e0)) => H7.
      destruct (expr_b_dp (pi =b> e \= e0)); simpl in H; try discriminate.
      * generalize (H7 refl_equal s); clear H7; intros.
        case : H => ? ?; subst sig1' sig2'.
        apply emp_imp_inv in H2.
        rewrite /= /assert_m.emp in H2; subst h2.
        rewrite /= /assert_m.emp in H1; subst h1.
        apply Lst_end.
        by omegab.
        by rewrite H4 heap.unioneh.
      * clear H7.
        case : H => ? ?; subst sig1' sig2'.
        apply emp_imp_inv in H2.
        rewrite /= /assert_m.emp in H2; subst h2.
        suff : h = h1 by move=> ->.
        by map_tac_m.Equal.
    + move: (expr_b_dp_correct (pi =b> e1 \= e)) => H7.
      destruct (expr_b_dp (pi =b> e1 \= e)); simpl in H; try discriminate.
      move: (H7 refl_equal s)=> {H7} H7.
      move: (expr_b_dp_correct (pi =b> e0 \= nat_e 0)) => H8.
      destruct (expr_b_dp (pi =b> e0 \= nat_e 0)); simpl in H.
      * move: (H8 refl_equal s) => {H8} H8.
        case : H => ? ?;subst sig1' sig2'.
        simpl in H2; simpl in  H1.
        eapply Lst_equiv.
        eapply Lst_app'.
        apply H2 with (h' := assert_m.heap.emp).
        split; [by map_tac_m.Disj | done].
        by intuition.
        eapply H1.
        by map_tac_m.Disj.
        by map_tac_m.Equal.
        by omegab.
        by omegab.
        reflexivity.
      * move: (cell_in_sigma_correct remainder e0 pi) => {H8} H8.
        destruct (cell_in_sigma pi remainder e0); try discriminate.
        move: (H8 refl_equal s) => {H8}H8.
        case : H => ? ?; subst sig1' sig2'.
        simpl in H8; simpl in H2; simpl in H1.
        move: {H8}(H8 _ H0 H3) => H.
        case_sepcon H.
        eapply Lst_equiv.
        eapply Lst_app.
        apply H2 with (h' := assert_m.heap.emp).
        split; [by map_tac_m.Disj | red; by auto].
        reflexivity.
        by apply H1.
        by apply (proj1 H_h31).
        by map_tac_m.Disj.
        by map_tac_m.Disj.
        by map_tac_m.Equal.
        by omegab.
        reflexivity.
Qed.

(** try to match sig1 with sig2, remainder is that part of sig1 that is left aside *)
Fixpoint elim_common_subheap (pi : expr_b) (sig1 sig2 remainder : Sigma) {struct sig1} : option (Sigma * Sigma) :=
  match sig1 with
    | star sig11 sig12 =>
      match elim_common_subheap pi sig11 sig2 (star sig12 remainder) with
        | None => None
        | Some (sig11', sig12') => Some (remove_empty_heap pi (star sig11' sig12), sig12')
      end
    | _ => elim_common_cell pi sig1 remainder sig2
  end.

Lemma elim_common_subheap_correct: forall sig1 sig2 remainder pi sig1' sig2',
  elim_common_subheap pi sig1 sig2 remainder = Some (sig1', sig2') ->
  forall s, [ pi ]b_s ->
    (forall h, Sigma_interp (star remainder sig1') s h -> Sigma_interp sig2' s h) ->
    (forall h, Sigma_interp (star sig1 remainder) s h -> Sigma_interp sig2 s h).
Proof.
induction sig1; simpl; intros.
- generalize (elim_common_cell_mp sig2 _ remainder pi sig1' sig2' H) => H3.
  case_sepcon H2.
  case : H2_h1 => H2_h1 H2_h2'.
  move: {H3 H2_h1 H2_h2'}(H3 _ _ (conj H2_h1 H2_h2')); intro H2.
  case_sepcon H2.
  eapply (elim_common_cell_correct sig2 _ remainder pi sig1' sig2' H _ H0).
  eapply H1.
  have H2 : (Sigma_interp remainder ** Sigma_interp sig1') s (h2 \U h12) by Compose_sepcon h2 h12.
  by apply H2.
  by apply H2_h11.
  by apply H2_h2.
  by map_tac_m.Equal.
  by map_tac_m.Disj.
  by map_tac_m.Disj.
- case_sepcon H2.
  move: (elim_common_cell_mp sig2 _ remainder pi sig1' sig2' H) => H3.
  rewrite /= /while.entails in H3.
  move/H3 : H2_h1 => H2_h1.
  case_sepcon H2_h1.
  eapply (elim_common_cell_correct sig2 _ remainder pi sig1' sig2' H _ H0).
  eapply H1.
  have H2 : (Sigma_interp remainder ** Sigma_interp sig1') s (h2 \U h12) by Compose_sepcon h2 h12.
  by apply H2.
  by apply H2_h1_h11.
  by apply H2_h2.
  by map_tac_m.Equal.
  by map_tac_m.Disj.
  by map_tac_m.Disj.
- case_sepcon H2.
  move: (elim_common_cell_mp sig2 _ remainder pi sig1' sig2' H) => H5.
  rewrite /= /while.entails in H5.
  move/H5 : H2_h1 => H2_h1.
  case_sepcon H2_h1.
  eapply (elim_common_cell_correct sig2 _ remainder pi sig1' sig2' H _ H0).
  eapply H1.
  have H2 : (Sigma_interp remainder ** Sigma_interp sig1') s (h2 \U h12) by Compose_sepcon h2 h12.
  by apply H2.
  by apply H2_h1_h11.
  by apply H2_h2.
  by map_tac_m.Equal.
  by map_tac_m.Disj.
  by map_tac_m.Disj.
- generalize (IHsig1_1 sig2 (star sig1_2 remainder) pi); clear IHsig1_1; intro H3.
  destruct (elim_common_subheap pi sig1_1 sig2 (star sig1_2 remainder)); try discriminate.
  destruct p; case: H => ? ?; subst sig1' sig2'.
  apply (H3 _ _ refl_equal _ H0); clear H3.
  move=> /= h0 H.
  eapply H1.
  case_sepcon H.
  case_sepcon H_h01.
  Compose_sepcon h012 (h011 \U h02); first by [].
  apply remove_empty_heap_correct'.
  by apply H0.  simpl.
  simpl.
  by Compose_sepcon h02 h011.
  case_sepcon H2.
  case_sepcon H2_h1.
  rewrite /=.
  Compose_sepcon h11 (h12 \U h2); first by [].
  by Compose_sepcon h12 h2.
- move: (elim_common_cell_mp sig2 _ remainder pi sig1' sig2' H) => H3.
  rewrite /= /while.entails in H3.
  case_sepcon H2.
  move/H3 : H2_h1 => H2_h1.
  case_sepcon H2_h1.
  eapply (elim_common_cell_correct sig2 _ remainder pi sig1' sig2' H _ H0 ); intros.
  have H2 : Sigma_interp sig2' s (h2 \U h12) by eapply H1; Compose_sepcon h2 h12.
  by apply H2.
  by apply H2_h1_h11.
  by apply H2_h2.
  by map_tac_m.Equal.
  by map_tac_m.Disj.
  by map_tac_m.Disj.
Qed.

Fixpoint star_assoc_left (sig1 sig2 : Sigma) {struct sig1} : Sigma :=
  match sig1 with
    | star sig11 sig12 => star_assoc_left sig12 (star sig2 sig11)
    | _ => match sig2 with
             | emp => sig1
             | _ => star sig2 sig1
           end
  end.

Lemma star_assoc_left_correct: forall sig1 sig2,
  Sigma_interp (star_assoc_left sig1 sig2) ===> Sigma_interp (star sig1 sig2).
Proof.
induction sig1; induction sig2; simpl star_assoc_left; intros; auto.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- move=> s h; move/IHsig1_2 => H.
  eapply entail_to_Sigma_impl; [idtac | by apply H].
  Entail.
- move=> s h; move/IHsig1_2 => H.
  eapply entail_to_Sigma_impl; [idtac | by apply H].
  Entail.
- move=> s h; move/IHsig1_2 => H.
  eapply entail_to_Sigma_impl; [idtac | by apply H].
  Entail.
- move=> s h; move/IHsig1_2 => H.
  eapply entail_to_Sigma_impl; [idtac | by apply H].
  Entail.
- move=> s h; move/IHsig1_2 => H.
  eapply entail_to_Sigma_impl; [idtac | by apply H].
  Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
Qed.

Lemma star_assoc_left_correct' : forall sig1 sig2,
  Sigma_interp (star sig1 sig2) ===> Sigma_interp (star_assoc_left sig1 sig2).
Proof.
induction sig1; induction sig2; simpl star_assoc_left; intros; auto.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- rewrite /while.entails; intros.
  apply IHsig1_2.
  eapply entail_to_Sigma_impl; [idtac | by apply H].
  Entail.
- rewrite /while.entails; intros.
  apply IHsig1_2.
  eapply entail_to_Sigma_impl; [idtac | by apply H].
  Entail.
- rewrite /while.entails; intros.
  apply IHsig1_2.
  eapply entail_to_Sigma_impl; [idtac | by apply H].
  Entail.
- rewrite /while.entails; intros.
  apply IHsig1_2.
  eapply entail_to_Sigma_impl; [idtac | by apply H].
  Entail.
- rewrite /while.entails; intros.
  apply IHsig1_2.
  eapply entail_to_Sigma_impl; [idtac | by apply H].
  Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
Qed.

Definition star_com (sig : Sigma) : Sigma :=
  match sig with
    | star sig1 sig2 => star sig2 sig1
    | _ => sig
  end.

Lemma star_com_correct : forall sig,
  Sigma_interp (star_com sig) ===> Sigma_interp sig.
Proof.
destruct sig; intros; simpl star_com; auto.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
Qed.

Lemma star_com_correct' : forall sig,
  Sigma_interp sig ===> Sigma_interp (star_com sig).
Proof.
destruct sig; intros; simpl star_com; auto.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
- apply entail_to_Sigma_impl; Entail.
Qed.

Definition rearrange_elim_common_subheap (pi : expr_b) (sig1 sig2 : Sigma) : Sigma * Sigma :=
  match elim_common_subheap pi sig1 sig2 emp with
    | None => (remove_empty_heap pi (star_com (star_assoc_left sig1 emp)), sig2)
    | Some s => s
  end.

Lemma rearrange_elim_common_subheap_correct : forall sig1 sig2 pi sig1' sig2',
  rearrange_elim_common_subheap pi sig1 sig2 = (sig1', sig2') ->
  forall s, [ pi ]b_s ->
    (forall h, Sigma_interp sig1' s h -> Sigma_interp sig2' s h) ->
    forall h, Sigma_interp sig1 s h -> Sigma_interp sig2 s h.
Proof.
simpl; intros.
unfold rearrange_elim_common_subheap in H.
generalize (elim_common_subheap_correct sig1 sig2 emp pi); intros.
destruct (elim_common_subheap pi sig1 sig2 emp).
- destruct p.
  eapply H3.
  by rewrite H; intuition.
  exact H0.
  move=> h0 H4.
  simpl in H4.
  case_sepcon H4.
  rewrite /assert_m.emp in H4_h01.
  subst h01.
  cutrewrite (h0 = h02); last by map_tac_m.Equal.
  by apply H1.
  simpl.
  by Compose_sepcon h assert_m.heap.emp.
- clear H3.
  case : H => ? ?; subst sig1' sig2'.
  apply H1.
  apply remove_empty_heap_correct'.
  exact H0.
  apply star_com_correct', star_assoc_left_correct' => /=.
  by Compose_sepcon h assert_m.heap.emp.
Qed.

Fixpoint elim_common_subheap_iterate (pi : expr_b) (sig1 sig2 : Sigma) (step : nat) {struct step} : Sigma * Sigma :=
  match step with
    | 0 => (sig1, sig2)
    | S n =>
      match rearrange_elim_common_subheap pi sig1 sig2 with
        | (sig1', sig2') => elim_common_subheap_iterate pi sig1' sig2' n
      end
  end.

Lemma elim_common_subheap_iterate_correct: forall n sig1 sig2 pi sig1' sig2',
  elim_common_subheap_iterate pi sig1 sig2 n = (sig1',sig2') ->
  forall s,[ pi ]b_s ->
    (forall h, Sigma_interp sig1' s h -> Sigma_interp sig2' s h) ->
    forall h, Sigma_interp sig1 s h -> Sigma_interp sig2 s h.
Proof.
induction n; simpl; intros.
- case : H => ? ?; subst sig1' sig2'; by auto.
- generalize (rearrange_elim_common_subheap_correct sig1 sig2 pi) => H3.
  destruct (rearrange_elim_common_subheap pi sig1 sig2); try discriminate.
  apply (H3 _ _ refl_equal _ H0).
  move=> h0 H4.
  by apply (IHn _ _ _ _ _ H).
  exact H2.
Qed.

Transparent remove_empty_heap.

Fixpoint sigma_size (sig : Sigma) : nat :=
  match sig with
    | singl e1 e2 => 1
    | cell e1 => 1
    | lst e1 e2 => 3
    | star s1 s2 => sigma_size s1 + sigma_size s2
    | emp => 1
  end.

Inductive resul (A : Type) : Type :=
  | Good : resul A
  | Error : A -> resul A.

Arguments Good [A].
Arguments Error [A].

Definition sigma_impl (pi : expr_b) (sig1 sig2 : Sigma) : resul (Sigma * Sigma) :=
  match elim_common_subheap_iterate pi sig1 sig2 ((sigma_size sig1 + sigma_size sig2) * 2) with
    | (emp, emp) => Good
    | e => Error e
  end.

Lemma sigma_impl_correct: forall sig1 sig2 pi, sigma_impl pi sig1 sig2 = Good ->
  forall s, [ pi ]b_s ->
    forall h, Sigma_interp sig1 s h -> Sigma_interp sig2 s h.
Proof.
intros.
unfold sigma_impl in H.
generalize (elim_common_subheap_iterate_correct ((sigma_size sig1 + sigma_size sig2) * 2) sig1 sig2 pi); intros.
destruct (elim_common_subheap_iterate pi sig1 sig2 ((sigma_size sig1 + sigma_size sig2) * 2)); simpl in H; try discriminate.
apply (H2 _ _ refl_equal _ H0); clear H2; auto.
intros.
destruct s0; destruct s1; simpl in H; try discriminate; auto.
Qed.

Definition frag_entail_fun (a1 a2 : assrt) : resul (assrt * assrt) :=
  let (pi1, sig1) := a1 in
    let (pi2, sig2) := a2 in
      if expr_b_dp (\~ pi1) then (* verifying if the lhs logical part is not a contradiction *)
        (*Error ((pi1, emp), (pi2, emp)) *)
        Good
        else
          match sigma_impl pi1 sig1 sig2 with (* else try to prove the implication of abstract heaps*)
            | Good => if expr_b_dp (pi1 =b> pi2) then (* and implication of logical parts *)
              Good
              else
                Error ((pi1, emp), (pi2, emp))
            | Error (s1, s2) => Error ((pi1, s1), (pi2, s2))
          end.

Lemma frag_entail_fun_correct: forall a1 a2,
  frag_entail_fun a1 a2 = Good -> assrt_interp a1 ===> assrt_interp a2.
Proof.
destruct a1 as [p s] ; destruct a2 as [p0 s0]; rewrite /while.entails /frag_entail_fun /=; intros.
generalize (expr_b_dp_correct (\~ p)); intros.
destruct (expr_b_dp (\~ p)); simpl in H; try discriminate.
- inversion_clear H0.
  move: (H1 refl_equal s1) => H0.
  by omegab.
- clear H1.
  split.
  + destruct (sigma_impl p s s0).
    * inversion_clear H0.
      move: (expr_b_dp_correct (p =b> p0)) => H0.
      destruct (expr_b_dp (p =b> p0)); simpl in H; try discriminate.
      generalize (H0 refl_equal s1); intros.
      by omegab.
    * destruct p1; try discriminate.
  + inversion_clear H0.
    apply (sigma_impl_correct s s0 p) => //.
    destruct (sigma_impl p s s0); try discriminate; auto.
    destruct p1; try discriminate.
Qed.

(*
   Ici ajouter une fonction pour rajouter les contraintes implicites
*)
(*
Pour plus tard: simplifier les expr_b

Fixpoint simpl_expr_b (pi: expr_b) : epxr_b :=
  match pi with
    | pi1 &e pi2 =>
      match (simpl_expr_b pi1, simpl_expr_b pi2) with
        | (!true_b,_) =>
        |


    | _ => if (expr_b_dp pi) then
              true_b else if
                if (expr_b_dp (!pi)) then
                  (! true_b)
  end.
*)

Definition compute_constraint_cell (pi : expr_b) (sig1 sig2 : Sigma) : expr_b :=
  match (sig1,sig2) with
    | (singl e1 e2, singl e3 e4) =>
      if expr_b_dp (pi =b> (e1 \!= e3)) then pi else
        pi \&& e1 \!= e3
    | (singl e1 e2, cell e3) =>
      if expr_b_dp (pi =b> (e1 \!= e3)) then pi else
        pi \&& (e1 \!= e3)
    | (cell e1, singl e3 e4) =>
      if expr_b_dp (pi =b> (e1 \!= e3)) then pi else
        pi \&& (e1 \!= e3)
    | (cell e1, cell e3) =>
      if expr_b_dp (pi =b> (e1 \!= e3)) then pi else
        pi \&& e1 \!= e3
    | (singl e1 e2, lst e3 e4) =>
      if expr_b_dp (pi =b> (e3 \!= e4)) then
        if expr_b_dp (pi =b> (e1 \!= e3)) then pi else
          pi \&& (e1 \!= e3)
        else pi
    | (lst e1 e2, singl e3 e4) =>
      if expr_b_dp (pi =b> (e1 \!= e2)) then
        if expr_b_dp (pi =b> (e1 \!= e3)) then pi else
          pi \&& (e1 \!= e3)
        else pi
    | (cell e1, lst e3 e4) =>
      if expr_b_dp (pi =b> (e3 \!= e4)) then
        if expr_b_dp (pi =b> (e1 \!= e3)) then pi else
          pi \&& (e1 \!= e3)
        else pi
    | (lst e1 e2, cell e3) =>
      if expr_b_dp (pi =b> (e1 \!= e2)) then
        if expr_b_dp (pi =b> (e1 \!= e3)) then pi else
          pi \&& (e1 \!= e3)
        else pi
    | (lst e1 e2, lst e3 e4) =>
      if expr_b_dp (pi =b> (e1 \!= e2)) && expr_b_dp (pi =b> (e3 \!= e4)) then
        if expr_b_dp (pi =b> (e1 \!= e3)) then pi else
          pi \&& (e1 \!= e3)
        else pi
    | (_, _) => pi
  end.

Lemma compute_constraint_cell_correct : forall sig1 sig2 pi,
  assrt_interp (pi, star sig1 sig2) ===> assrt_interp (compute_constraint_cell pi sig1 sig2, star sig1 sig2).
Proof.
destruct sig1; destruct sig2; rewrite /while.entails /=; intros; auto; rewrite /compute_constraint_cell; inversion_clear H; split.
- case: ifP => //= H.
  apply/andP; split; first by [].
  apply/eqP.
  case_sepcon H1.
  eapply singl_disj_neq.
  exact: (proj1 H1_h1).
  exact: (proj1 H1_h2).
  assumption.
- assumption.
- case: ifP => //= H.
  apply/andP; split; first by [].
  apply/eqP.
  case_sepcon H1.
  case: H1_h2 => [[x H1] H2].
  eapply singl_disj_neq.
  exact: (proj1 H1_h1).
  exact: H1.
  assumption.
- assumption.
- case: ifP => //= H.
  case_sepcon H1.
  destruct H1_h2.
  + apply expr_b_dp_correct with (s := s) in H.
    move: H.
    by rewrite /= H1 /ZIT.eqb eqxx orbF H0.
  + case: ifP => //= H7.
    apply/andP; split; first by [].
    apply/eqP.
    case_sepcon H6.
    eapply singl_disj_neq.
    by apply (proj1 H1_h1).
    by apply H6_h21.
    by map_tac_m.Disj.
- assumption.
- case: ifP => //= H.
  apply/andP; split; first by [].
  apply/eqP.
  case_sepcon H1.
  case: H1_h1 => [[v H1] H2].
  eapply singl_disj_neq.
  by apply H1.
  by apply (proj1 H1_h2).
  by map_tac_m.Disj.
- assumption.
- case: ifP => //= H.
  apply/andP; split; first by [].
  apply/eqP.
  case_sepcon H1.
  case: H1_h1 => [[v H1] H2].
  case: H1_h2 => [[v0 H3] H4].
  eapply singl_disj_neq.
  by apply H1.
  by apply H3.
  by map_tac_m.Disj.
- assumption.
- case: ifP => //= H.
  case_sepcon H1.
  inversion_clear H1_h1.
  case : H1 => v H1.
  destruct H1_h2.
  + apply expr_b_dp_correct with (s := s) in H.
    by rewrite /= H3 /ZIT.eqb eqxx //= orbF H0 in H.
  + case: ifP => //= H9.
    apply/andP; split; first by [].
    apply/eqP.
    case_sepcon H8.
    eapply singl_disj_neq.
    by apply H1.
    by apply H8_h21.
    by map_tac_m.Disj.
- assumption.
- case: ifP => //= H.
  case_sepcon H1.
  destruct H1_h1.
  + apply expr_b_dp_correct with (s := s) in H.
    by rewrite /= H1 /ZIT.eqb eqxx //= orbC /= H0 in H.
  + case: ifP => //= H7.
    apply/andP; split; first by [].
    apply/eqP.
    case_sepcon H6.
    eapply singl_disj_neq.
    by apply H6_h11.
    by apply (proj1 H1_h2).
    by map_tac_m.Disj.
- assumption.
- case: ifP => //= H.
  case_sepcon H1.
  case : H1_h2 => [[v H1] H2].
  destruct H1_h1.
  + apply expr_b_dp_correct with (s := s) in H.
    by rewrite /= H3 /ZIT.eqb eqxx //= orbC /= H0 in H.
  + case: ifP => //= H9.
    apply/andP; split; first by [].
    apply/eqP.
    case_sepcon H8.
    eapply singl_disj_neq.
    by apply H8_h11.
    by apply H1.
    by map_tac_m.Disj.
- assumption.
- case: ifP => //.
  case/andP => H2 H3.
  case: ifP => // H4.
  case_sepcon H1.
  destruct H1_h1.
  + apply expr_b_dp_correct with (s := s) in H2.
    by rewrite /= H /ZIT.eqb /= eqxx //= orbC /= H0 in H2.
  + destruct H1_h2.
  + apply expr_b_dp_correct with (s := s) in H3.
    by rewrite /= /ZIT.eqb H9 eqxx //= orbC /= H0 in H3.
- simpl; apply/andP.
  split; first by [].
  apply/eqP.
  case_sepcon H8.
  case_sepcon H14.
  eapply singl_disj_neq.
  by apply H8_h11.
  by apply H14_h41.
  by map_tac_m.Disj.
- assumption.
Qed.

Fixpoint compute_constraint_cell_sigma (pi : expr_b) sig1 sig2 : expr_b :=
  match sig2 with
    | star sig21 sig22 => compute_constraint_cell_sigma  (compute_constraint_cell_sigma pi sig1 sig21) sig1 sig22
    | _ => compute_constraint_cell pi sig1 sig2
  end.

Lemma compute_constraint_cell_sigma_correct : forall sig2 sig1 pi,
  assrt_interp (pi, star sig1 sig2) ===> assrt_interp (compute_constraint_cell_sigma pi sig1 sig2, star sig1 sig2).
Proof.
induction sig2; simpl compute_constraint_cell_sigma; intros; try (eapply compute_constraint_cell_correct).
rewrite /= /while.entails in IHsig2_1 IHsig2_2 *; move=> s h [H0 H1].
split; last by [].
case_sepcon H1.
case_sepcon H1_h2.
have [H8 _]: [ compute_constraint_cell_sigma pi sig1 sig2_1 ]b_s  /\
              (Sigma_interp sig1 ** Sigma_interp sig2_1) s (h1 \U h21) .
  eapply IHsig2_1.
  split; first by [].
  Compose_sepcon h1 h21; assumption.
have [H9 _] : [ compute_constraint_cell_sigma (compute_constraint_cell_sigma pi sig1 sig2_1) sig1 sig2_2 ]b_s /\
  (Sigma_interp sig1 ** Sigma_interp sig2_2) s (h1 \U h22).
  eapply IHsig2_2.
  split; first by [].
  Compose_sepcon h1 h22; assumption.
exact H9.
Qed.

Fixpoint compute_constraints' (pi : expr_b) (sig : Sigma) {struct sig} : expr_b :=
  match sig with
    | star sig1 sig2 => compute_constraints' (compute_constraint_cell_sigma pi sig2 sig1) sig1
    | _ => pi
  end.

Lemma compute_constraints'_correct : forall sig pi,
  assrt_interp (pi, sig) ===> assrt_interp (compute_constraints' pi sig, sig).
Proof.
induction sig; simpl compute_constraints'; intros; rewrite /while.entails => s h [H0 H1] //=.
split; last by [].
simpl in H1.
case_sepcon H1.
assert (assrt_interp ((compute_constraint_cell_sigma pi sig2 sig1), star sig2 sig1) s h).
  apply compute_constraint_cell_sigma_correct => /=.
  split; first by [].
  by Compose_sepcon h2 h1.
inversion_clear H.
assert (assrt_interp (compute_constraints' (compute_constraint_cell_sigma pi sig2 sig1) sig1 , sig1) s h1).
  red in IHsig1; by apply IHsig1.
by case: H.
Qed.

Definition compute_constraints (pi : expr_b) (sig : Sigma) : expr_b :=
  compute_constraints' pi (star_assoc_left sig emp).

Lemma compute_constraints_correct : forall pi sig,
  assrt_interp (pi,sig) ===> assrt_interp (compute_constraints pi sig, sig).
Proof.
unfold compute_constraints.
rewrite /while.entails; intros.
generalize compute_constraints'_correct; intros.
red in H0.
cut (assrt_interp (compute_constraints' pi (star_assoc_left sig emp), (star_assoc_left sig emp)) s h); last first.
  apply H0 => //.
  case : H => H1 H2 /=.
  split; first by [].
  apply star_assoc_left_correct' => /=.
  by Compose_sepcon h assert_m.heap.emp.
move=> [H2 H3].
split; first by [].
move: (star_assoc_left_correct _ _ _ _ H3) => H4.
simpl in H4.
case_sepcon H4.
rewrite /assert_m.emp in H4_h2; subst h2.
rewrite (_ : h = h1) //; by map_tac_m.Equal.
Qed.

Fixpoint cell_loc_not_null (pi : expr_b) (sig : Sigma)  {struct sig} : expr_b :=
  match sig with
    | emp => pi
    | lst e1 e2 => pi
    | cell e1 =>
      if expr_b_dp (pi =b> (e1 \!= nat_e 0)) then pi else
          pi \&& (e1 \!= nat_e 0)
    | singl e1 e2 =>
      if expr_b_dp (pi =b> (e1 \!= nat_e 0)) then pi else
          pi \&& (e1 \!= nat_e 0)
    | star s1 s2 =>
      cell_loc_not_null (cell_loc_not_null pi s1) s2
  end.

Lemma cell_loc_not_null_correct: forall sig pi,
  assrt_interp (pi,sig) ===> assrt_interp ((cell_loc_not_null pi sig), sig).
Proof.
induction sig; rewrite /= /while.entails; intros; auto.
- case: H => H0 [H2 H3].
  move: (expr_b_dp_correct (pi =b> e \!= nat_e 0)) => H.
  case: ifP => // {H}H.
  split; last by [].
  by omegab.
- case: H => H0 [H2 H3].
  move: (expr_b_dp_correct (pi =b> e \!= nat_e 0)) => H.
  case: ifP => // {H}H.
  split; last by [].
  by omegab.
- case : H => H0 H1.
  split; last by [].
  case_sepcon H1.
  rewrite /while.entails in IHsig1.
  red in IHsig2.
  have [H1 H2] : assrt_interp (cell_loc_not_null pi sig1, sig1) s h1 by apply IHsig1.
  have H : assrt_interp (cell_loc_not_null pi sig1, sig2) s h2 by [].
  by apply (proj1 (IHsig2 (cell_loc_not_null pi sig1) _ _ H)).
Qed.

Definition assrt_entail_fun (a1 a2 : assrt) : resul (assrt * assrt) :=
  let (pi1,sig1) := a1 in frag_entail_fun (compute_constraints (cell_loc_not_null pi1 sig1) sig1, sig1) a2.

Lemma assrt_entail_fun_correct : forall a1 a2, assrt_entail_fun a1 a2 = Good ->
  assrt_interp a1 ===> assrt_interp a2.
Proof.
rewrite /while.entails /assrt_entail_fun; intros.
destruct a1 as [p s0].
generalize (frag_entail_fun_correct) => H1.
apply (H1 (compute_constraints (cell_loc_not_null p s0) s0, s0) a2 H).
by apply compute_constraints_correct, cell_loc_not_null_correct.
Qed.

(*
Goal   (assrt_interp P) ===> (assrt_interp Q).
  eapply frag_impl_correct.
  unfold P; unfold Q; unfold x1; unfold x2; unfold x3; unfold x4 ; unfold x5; unfold x6; unfold null.
  auto.
  simpl.
Qed.
*)


(*

Our goal here is to verify entailments of the form:

 <P | S> |- \/i <Pi | Si>

To achieve such goal we have a decision procedure for arithmetic (expr_b_dp),
and a decision procedure (assrt_entail_fun) for entailments of the form:

<P|S> |- <P'|S'>

We propose the two following rules :

*)

(*

rule 1 is intuitive:

\/i <P|S> |- <Pi |Si>
-------------------------- (rule 1)
<P|S> |- \/i <Pi | Si>

orassrt_impl_Assrt1 try to prove (\/i <P|S> |- <Pi |Si>)

and give the subgoals that were not resolved

*)

Fixpoint orassrt_impl_Assrt1 (a : assrt) (A : Assrt) (l:list (assrt * assrt)) {struct A} : resul (list (assrt * assrt)) :=
  match A with
    | nil => Error l
    | hd :: tl =>
      match assrt_entail_fun a hd with
        | Good => Good
        | Error e => orassrt_impl_Assrt1 a tl (e :: l)
      end
  end.

(** This lemma prove that the rule 1 is correct *)

Lemma orassrt_impl_Assrt1_correct: forall A a l,
  orassrt_impl_Assrt1 a A l = Good -> assrt_interp a ===> Assrt_interp A.
Proof.
induction A; rewrite /while.entails /=; intros => //.
move: (assrt_entail_fun_correct a0 a) => H1.
destruct (assrt_entail_fun a0 a).
- left.
  by intuition.
- clear H1.
  right.
  by apply (IHA _ _ H _ _ H0).
Qed.

(*

However rule 1 is sometime too weak to solve some entailments.

For example:

<True | x |~> e> |- <e =e 0| x |~> 0> \/ <e <>e 0 | x |~> e>

(such disjunctions may appear in loops invariants)

To solve such goals we proposed the folowing rule:



P -> \/i Pi               /\i <P /\ Pi | S> |- <true, Si>
---------------------------------------------------------- (rule 2)
                 <P | S> |- \/i <Pi | Si>

*)


(* orpi compute the term \/i Pi *)

Fixpoint orpi (l : list assrt) : expr_b :=
  match l with
    | nil => neg_b true_b
    | (pi, sig) :: tl => pi \|| (orpi tl)
  end.

(* orassrt_impl_Assrt2 try to prove  ( /\i <P /\ Pi | S> |- <true, Si>)
   and give the subgoals that were not resolved
*)

Fixpoint orassrt_impl_Assrt2 (a : assrt) (A : Assrt) (l : list (assrt * assrt)) {struct A} : resul (list (assrt * assrt)) :=
  match A with
    | nil => Error l
    | (pi, sig) :: tl =>
      match a with
        | (pi', sig') =>
          match sigma_impl (pi' \&& pi) sig' sig  with
            | Error (s1, s2) => Error (((pi', s1), (pi, s2)) :: l)
            | Good =>
              match tl with
                | nil => Good
                | _ => orassrt_impl_Assrt2 a tl l
              end
          end
      end
  end.

(** This lemma prove that the rule 2 is correct *)

Lemma orassrt_impl_Assrt2_correct: forall A pi sig l,
  orassrt_impl_Assrt2 (pi, sig) A l = Good -> (* /\i <P /\ Pi | S> |- <true, Si> *)
  forall s h,
    [ pi =b> (orpi A) ]b_s ->  (* P -> \/i Pi *)
    ((assrt_interp (pi,sig)) s h -> (Assrt_interp A) s h). (* <P | S> |- \/i <Pi | Si> *)
Proof.
induction A; intros; try discriminate.
simpl.
destruct a as [p s0].
simpl in H1; simpl orpi in H0.
inversion_clear H1.
simpl in H.
generalize (sigma_impl_correct sig s0 (pi \&& p)) => H1.
destruct (sigma_impl (pi \&& p) sig s0).
- have H4 : [ p \|| orpi A ]b_s by omegab.
  have [H6 | H6] : [ p ]b_s \/ [ orpi A ]b_s.
    simpl in H4; simpl.
    destruct ([ p ]b_ s); destruct ( [ orpi A ]b_ s); simpl in H4; try discriminate; auto.
  + left; simpl; split.
    exact H6.
    apply H1 => //.
    by omegab.
  + destruct A.
    * by simpl in H6.
    * right.
      apply (IHA _ _ _ H) => //.
      by omegab.
- by destruct p0.
Qed.

(** entry point *)

Definition entail_fun (a : assrt) (A : Assrt) (l : list (assrt * assrt)) : resul (list (assrt * assrt)) :=
  match a with
    | (pi, sig) =>
      if expr_b_dp (pi =b> (orpi A)) then (* if P -> \/i Pi *)
        match orassrt_impl_Assrt2 a A nil with (* then try rule 2*)
          | Good => Good
          | Error e => orassrt_impl_Assrt1 a A nil (* if rule 2 failed then try rule 1 fi*)
        end
        else
          orassrt_impl_Assrt1 a A nil (* else try directly rule 1 fi *)
  end.

Lemma entail_fun_correct A a l : entail_fun a A l = Good ->
  (assrt_interp a ===> Assrt_interp A).
Proof.
move=> H.
rewrite /while.entails => s h H0.
unfold entail_fun in H.
destruct a as [p s0].
move: (expr_b_dp_correct (p =b> orpi A)) => H1.
destruct (expr_b_dp (p =b> orpi A)).
- move: (orassrt_impl_Assrt2_correct A p s0 nil) => H2.
  destruct (orassrt_impl_Assrt2 (p, s0) A nil).
  + apply H2 => //.
    by apply H1.
  + clear H2 H1.
    eapply orassrt_impl_Assrt1_correct.
    by apply H.
    assumption.
- clear H1.
  eapply orassrt_impl_Assrt1_correct.
  by apply H.
  assumption.
Qed.

(** This function is only used by bigtoe, to provide verification of entailments  *)

Fixpoint Assrt_entail_Assrt_dp (A1 A2 : Assrt) (l : list (assrt * assrt)) {struct A1} : resul (list (assrt * assrt)) :=
  match A1 with
    | nil => Good
    | hd :: tl =>
      match entail_fun hd A2 nil with
        | Good => Assrt_entail_Assrt_dp tl A2 l
        | Error e => Error (e ++ l)
      end
  end.

Lemma Assrt_entail_Assrt_dp_correct : forall A1 A2 l,
  Assrt_entail_Assrt_dp A1 A2 l = Good ->
  Assrt_interp A1 ===> Assrt_interp A2.
Proof.
induction A1; rewrite /while.entails /=; intros => //.
move: (entail_fun_correct A2 a nil) => H1.
destruct (entail_fun a A2); try discriminate.
case: H0 => H2.
- exact: (H1 refl_equal s h H2).
- exact: (IHA1 _ _ H s h H2).
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)

(* file outline:
 * 1. definition of syntactic constructs and proofs of their properties
 * 2. a module for fresh variables (w.r.t. syntactic constructs)
 * 3. definition of LWP and its soundness
 * 4. weakest pre-condition generator and its soudness
 * 5. Resolution tactic
 *)

Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool seq eqtype ssrnat.
Require Import Max_ext ssrnat_ext.
Require Import bipl seplog integral_type.
Require Import expr_b_dp.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.
Import BinNums.

Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.

(** definition of syntactic constructs *)

Inductive Sigma : Type :=
| singl : expr -> expr -> Sigma
| cell : expr -> Sigma
| epsi : Sigma
| star : Sigma -> Sigma -> Sigma.

Fixpoint Sigma_interp (a : Sigma) : assert :=
  match a with
    | singl e1 e2 => e1 |~> e2
    | epsi => emp
    | star s1 s2 => Sigma_interp s1 ** Sigma_interp s2
    | cell e => fun s h => exists v, (e |~> cst_e v) s h
  end.

Definition assrt := (expr_b * Sigma)%type.

Definition assrt_interp (a : assrt) : assert :=
  match a with
    | (pi, sigm) => fun s h => [ pi ]b_ s /\ Sigma_interp sigm s h
  end.

(** A proof system for assrt entailment *)

Inductive ps1 : assrt -> assrt -> Prop :=
| ps1_incons : forall pi1 pi2 sig1 sig2,
  (forall s, [ pi1 ]b_ s -> False) ->
  ps1 (pi1, sig1) (pi2, sig2)

| ps1_tauto : forall pi1 pi2,
  (forall s, [ pi1 ]b_ s -> [ pi2 ]b_ s) ->
  ps1 (pi1, epsi) (pi2, epsi)

| ps1_coml : forall pi1 sig1 sig2 L,
  ps1 (pi1, star sig2 sig1) L -> ps1 (pi1, star sig1 sig2) L

| ps1_comr : forall pi1 sig1 sig2 L,
  ps1 L (pi1, star sig2 sig1)  -> ps1 L (pi1, star sig1 sig2)

| ps1_assocl : forall pi1 sig1 sig2 sig3 L,
  ps1 (pi1, star (star sig1 sig2) sig3) L ->
  ps1 (pi1, star sig1 (star sig2 sig3)) L

| ps1_assocr : forall pi1 sig1 sig2 sig3 L,
  ps1 L (pi1, star (star sig1 sig2) sig3)  ->
  ps1 L (pi1, star sig1 (star sig2 sig3))

| ps1_epseliml : forall pi1 sig1 L,
  ps1 (pi1, sig1) L ->
  ps1 (pi1, star sig1 epsi) L

| ps1_epselimr : forall pi1 sig1 L,
  ps1 L (pi1, sig1) ->
  ps1 L (pi1, star sig1 epsi)

| ps1_epsintrol : forall pi1 sig1 L,
  ps1 (pi1, star sig1 epsi) L ->
  ps1 (pi1, sig1) L

| ps1_epsintror : forall pi1 sig1 L,
  ps1 L (pi1, star sig1 epsi) ->
  ps1 L (pi1, sig1)

| ps1_star_elim : forall pi1 pi2 sig1 sig2 e1 e2 e3 e4,
  (forall s, eval_b pi1 s -> [ e1 \= e3 ]b_ s) ->
  (forall s , eval_b pi1 s -> [ e2 \= e4 ]b_ s) ->
  ps1 (pi1, sig1) (pi2, sig2) ->
  ps1 (pi1, star sig1 (singl e1 e2)) (pi2, star sig2 (singl e3 e4))

| ps1_star_elim' : forall pi1 pi2 sig1 sig2 e1 e2 e3,
  (forall s, eval_b pi1 s -> [ e1 \= e3 ]b_ s) ->
  ps1 (pi1, sig1) (pi2, sig2) ->
  ps1 (pi1, star sig1 (singl e1 e2)) (pi2, star sig2 (cell e3))

| ps1_star_elim'' : forall pi1 pi2 sig1 sig2 e1 e3,
  (forall s, eval_b pi1 s -> [ e1 \= e3 ]b_ s) ->
  ps1 (pi1, sig1) (pi2, sig2) ->
  ps1 (pi1, star sig1 (cell e1)) (pi2, star sig2 (cell e3)).

(** Soundness of the proof system *)

Lemma ps1_soundness P Q : ps1 P Q -> assrt_interp P ===> assrt_interp Q.
Proof.
induction 1; rewrite /while.entails /=.
- intros.
  generalize (H s (proj1 H0)); contradiction.
- intros.
  generalize (H s (proj1 H0)); intuition.
- intros.
  red in IHps1.
  apply IHps1.
  simpl.
  inversion_clear H0.
  split; [auto | rewrite assert_m.conCE; auto].
- intros.
  rewrite /while.entails /= in IHps1.
  rewrite assert_m.conCE.
  by apply IHps1.
- intros.
  rewrite /while.entails /= in IHps1.
  rewrite <- assert_m.conAE in H0.
  by intuition.
- intros.
  rewrite /while.entails /= in IHps1.
  rewrite -assert_m.conAE.
  by apply IHps1.
- intros.
  rewrite /while.entails /= in IHps1.
  apply IHps1.
  split; [apply (proj1 H0)| eapply (assert_m.con_emp (Sigma_interp sig1) s h); apply (proj2 H0)].
- intros.
  rewrite /while.entails /= in IHps1.
  generalize (IHps1 s h H0); intros.
  split; [apply (proj1 H1)| eapply (assert_m.con_emp' (Sigma_interp sig1) s h); apply (proj2 H1)].
- intros.
  rewrite /while.entails /= in IHps1.
  apply IHps1.
  split; [apply (proj1 H0)| eapply (assert_m.con_emp' (Sigma_interp sig1) s h); apply (proj2 H0)].
- intros.
  rewrite /while.entails /= in IHps1.
  generalize (IHps1 s h H0); intros.
  split; [apply (proj1 H1)| eapply (assert_m.con_emp (Sigma_interp sig1) s h); apply (proj2 H1)].
- intros.
  rewrite /while.entails /= in IHps1.
  case: H2 => H3 H4.
  case_sepcon H4.
  case: (IHps1 s h1 (conj H3 H4_h1)) => H2 H4.
  split; first by assumption.
  Compose_sepcon h1 h2; first by assumption.
  generalize (H s H3); generalize (H0 s H3); intros.
  by Mapsto.
- intros.
  rewrite /while.entails /= in IHps1.
  case: H1 => H2 H3.
  case_sepcon H3.
  case: (IHps1 s h1 (conj H2 H3_h1)) => H1 H3.
  split; first by exact H1.
  Compose_sepcon h1 h2; first by exact H3.
  generalize (H s H2); intros.
  exists (eval e2 s).
  by Mapsto.
- intros.
  rewrite /while.entails /= in IHps1.
  case: H1 => H2 H3.
  case_sepcon H3.
  case: (IHps1 s h1 (conj H2 H3_h1)) => H1 H3.
  split; first by assumption.
  Compose_sepcon h1 h2; first by assumption.
  generalize (H s H2); intros.
  case: H3_h2 => x H3_h2.
  exists x.
  by Mapsto.
Qed.

(** Tactics to prove a ps1 goal *)

Ltac ps1_turnl :=
  match goal with
    | |- ps1 (?Pi, cell ?e) ?L => apply ps1_epsintrol; apply ps1_coml; repeat apply ps1_assocl
    | |- ps1 (?Pi, singl ?e1 ?e2) ?L => apply ps1_epsintrol; apply ps1_coml; repeat apply ps1_assocl
    | |- ps1 (?Pi, star ?e1 ?e2) ?L => apply ps1_coml; repeat apply ps1_assocl
  end.

Ltac ps1_turnr :=
  match goal with
    | |- ps1 ?L (?Pi, cell ?e) => apply ps1_epsintror; apply ps1_comr; repeat apply ps1_assocr
    | |- ps1 ?L (?Pi, singl ?e1 ?e2) => apply ps1_epsintror; apply ps1_comr; repeat apply ps1_assocr
    | |- ps1 ?L (?Pi, star ?e1 ?e2) => apply ps1_comr; repeat apply ps1_assocr
  end.

Ltac ps1_resolve := repeat apply ps1_assocr; repeat apply ps1_assocl;
  match goal with
    | |- ps1 (?pi1, star ?sig1 epsi) ?L => ps1_turnl; idtac
    | |- ps1 ?L (?Pi, cell ?e) => ps1_turnr; idtac
    | |- ps1 ?L (?Pi, singl ?e1 ?e2) => ps1_turnr; idtac
    | |- ps1 (?Pi, cell ?e) ?L => ps1_turnl; idtac
    | |- ps1 (?Pi, singl ?e1 ?e2) ?L => ps1_turnl; idtac

(*    | |- ps1 (?pi1, epsi) (?pi2, epsi) => apply ps1_tauto; [intros; Omega_exprb]*)
    | |- ps1 (?pi1, epsi) (?pi2, epsi) => apply ps1_tauto; do 2 intro; omegab
    | |- ps1 (?pi1, epsi) (?pi2, epsi) => apply ps1_incons; do 2 intro; omegab
                                                             (*[intros; Omega_exprb]*)
(*****)
    | |- ps1 (?pi1, star ?e epsi) ?L => apply ps1_epseliml; idtac
    | |- ps1 ?L (?pi2, star ?e epsi) => apply ps1_epselimr; idtac
(*****)
    | |- ps1 (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, star ?sig2 (singl ?e3 ?e4)) =>
      (apply ps1_star_elim; [ (do 2 intro; omegab) |
        (do 2 intro; omegab) | idtac] || ps1_turnl; idtac)

    | |- ps1 (?pi1, star ?sig1 (singl ?e1 ?e2)) (?pi2, star ?sig2 (cell ?e3)) =>
      (apply ps1_star_elim'; [ (do 2 intro; omegab) | idtac] || ps1_turnl; idtac)

    | |- ps1 (?pi1, star ?sig1 (cell ?e1)) (?pi2, star ?sig2 (cell ?e3)) =>
      (apply ps1_star_elim''; [ (do 2 intro; omegab) | idtac] || ps1_turnl; idtac)

    | |- ps1 (?pi2, star ?sig2 (cell ?e3)) (?pi1, star ?sig1 (singl ?e1 ?e2)) => ps1_turnl
   end.

Ltac ps1_Resolve := repeat ps1_resolve.

(* TODO: more examples taken from mery and/or calcagno *)

Lemma ps1_ex1: forall vy vx,
  ps1
  (true_b, star (singl (var_e 4%nat) (cst_e vx)) (singl (var_e 3%nat) (cst_e vy)))
  (true_b, star (singl (var_e 3%nat) (cst_e vy)) (singl (var_e 4%nat) (cst_e vx))).
Proof.
intros.
ps1_Resolve.
Qed.

Lemma ps1_ex2: forall startp sizep,
  (startp > 0)%nat -> (sizep > 4)%nat ->
  ps1
  (true_b,
    star
    (star (cell ((nat_e startp \+ nat_e sizep) \- cst_e 1%Z))
      (star (singl (nat_e startp) (cst_e 1%Z))
        (singl (nat_e startp \+ cst_e 1%Z)
          ((cst_e (Z_of_nat startp) \+ cst_e (Z_of_nat sizep)) \-
                 cst_e 2%Z))))
    (cell ((nat_e startp \+ nat_e sizep) \- cst_e 2%Z)))
  (true_b,
    star
    (star
      (star (cell ((nat_e startp \+ nat_e sizep) \- cst_e 2%Z))
        (cell ((nat_e startp \+ nat_e sizep) \- cst_e 1%Z)))
      (singl (nat_e startp) (cst_e 1%Z)))
    (singl (nat_e startp \+ cst_e 1%Z)
      ((cst_e (Z_of_nat startp) \+ cst_e (Z_of_nat sizep)) \- cst_e 2%Z))).
Proof.
intros.
ps1_Resolve.
Qed.

(** frag_decision is a certified decision procedure for entailment of assrt  *)

(*Require Import expr_b_dp.*)

Fixpoint Sigma_clean_epsi (t : Sigma) : Sigma :=
  match t with
    | star t1 t2 =>
      match Sigma_clean_epsi t1 with
        | epsi => Sigma_clean_epsi t2
        | t1' => match Sigma_clean_epsi t2 with
                   | epsi => t1'
                   | t2' => star t1' t2'
                 end
      end
    | _ => t
  end.

Definition Sigma_elt_eq (e1 e2 : Sigma) (env : expr_b) : bool :=
  match (e1, e2) with
    | (epsi, epsi) => true
    | (singl x1 x2, singl x3 x4) => expr_b_dp (env =b> (x1 \= x3)) && expr_b_dp (env =b> (x2 \= x4))
    | (singl x1 x2, cell x3) => expr_b_dp (env =b> (x1 \= x3))
    | (cell x1, cell x3) => expr_b_dp (env =b> (x1 \= x3))
    | (_, _) => false
  end.

Fixpoint Sigma_elt_term_extract (e t : Sigma) (env : expr_b) {struct t} : option Sigma :=
  match t with
    | star t1 t2 =>
      match Sigma_elt_term_extract e t1 env with
        | None => match Sigma_elt_term_extract e t2 env with
                    | None => None
                    | Some t2' => Some (Sigma_clean_epsi (star t1 t2'))
                  end
        | Some t1' => Some (Sigma_clean_epsi (star t1' t2))
      end
    | _ => if Sigma_elt_eq e t env then Some epsi else None
  end.

Fixpoint Sigma_elt_term_extract' (e t : Sigma) (env : expr_b) {struct t} : option Sigma :=
  match t with
    | star t1 t2 =>
      match Sigma_elt_term_extract' e t1 env with
        | None => match Sigma_elt_term_extract' e t2 env with
                    | None => None
                    | Some t2' => Some (Sigma_clean_epsi (star t1 t2'))
                  end
        | Some t1' => Some (Sigma_clean_epsi (star t1' t2))
      end
    | _ => if Sigma_elt_eq t e env then Some epsi else None
  end.

Fixpoint Sigma_term_term_eq (t1 t2 : Sigma) (env : expr_b) {struct t1} : option Sigma :=
  match t1 with
    | star t11 t12 =>
      match Sigma_term_term_eq t11 t2 env with
        | None => None 
        | Some t2' => match Sigma_term_term_eq t12 t2' env with
                        | None => None
                        | Some t2'' => Some t2''
                      end
      end
    | _ => match Sigma_elt_term_extract t1 t2 env with
             | None => None
             | Some t2' => Some t2'
           end
  end.

Fixpoint Sigma_get_cell_val (e : expr) (sig : Sigma) (env : expr_b) {struct sig} : option expr :=
  match sig with
    | epsi => None
    | singl e1 e2 => if expr_b_dp (env =b> (e1 \= e)) then Some e2 else None
    | cell e1 => None
    | star s1 s2 =>
      match Sigma_get_cell_val e s1 env with
        | None => Sigma_get_cell_val e s2 env
        | Some e2 => Some e2
      end
  end.

Definition frag_decision (P Q : expr_b * Sigma) : bool :=
  let (pi1, sig1) := P in
  let (pi2, sig2) := Q in
    if expr_b_dp (pi1 =b> pi2) then
      match Sigma_term_term_eq sig1 sig2 pi1 with
        | Some epsi => true
        | _ => false
      end
      else 
        false .

Lemma Sigma_clean_epsi_correct : forall t,
  Sigma_interp (Sigma_clean_epsi t) ===> Sigma_interp t.
Proof.
induction t; simpl; rewrite /while.entails; intros; auto.
destruct (Sigma_clean_epsi t1); destruct (Sigma_clean_epsi t2); simpl in H; simpl.
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by Compose_sepcon h assert_m.heap.emp; [apply IHt1; auto | apply IHt2; simpl; red; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by Compose_sepcon h assert_m.heap.emp; [apply IHt1; auto | apply IHt2; simpl; red; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by Compose_sepcon assert_m.heap.emp h; [apply IHt1; simpl; red; auto | apply IHt2; auto].
by Compose_sepcon assert_m.heap.emp h; [apply IHt1; simpl; red; auto | apply IHt2; auto].
by red in H; Compose_sepcon assert_m.heap.emp assert_m.heap.emp; 
  [apply IHt1; simpl; red; auto | apply IHt2; simpl; red; auto].
by Compose_sepcon assert_m.heap.emp h; [apply IHt1; simpl; red; auto | apply IHt2; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by Compose_sepcon h assert_m.heap.emp; [apply IHt1; auto | apply IHt2; simpl; red; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
Qed.

Lemma Sigma_clean_epsi_correct' : forall t,
  Sigma_interp t ===> Sigma_interp (Sigma_clean_epsi t).
Proof.
induction t; simpl; rewrite /while.entails; intros; auto.
destruct (Sigma_clean_epsi t1); destruct (Sigma_clean_epsi t2); simpl in H; simpl.
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; move: (IHt2 _ _ H_h2) => H; simpl in H; red in H; subst h2; 
  assert (h = h1); [map_tac_m.Equal | subst h1; apply IHt1; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; move: (IHt2 _ _ H_h2) => H; simpl in H; red in H;  subst h2;
  assert (h = h1); [map_tac_m.Equal | subst h1; apply IHt1; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; move: (IHt1 _ _ H_h1) => H; simpl in H; red in H; subst h1;
  assert (h = h2); [map_tac_m.Equal | subst h2; apply IHt2; auto].
by case_sepcon H; move: (IHt1 _ _ H_h1) => H; simpl in H; red in H; subst h1;
  assert (h = h2); [map_tac_m.Equal | subst h2; apply IHt2; auto].
red; auto.
case_sepcon H.
move: (IHt1 _ _ H_h1) => H.
move: (IHt2 _ _ H_h2) => H0.
simpl in H; simpl in H0.
red in H; red in H0.
subst h1 h2.
by map_tac_m.Equal.
by case_sepcon H; move: (IHt1 _ _ H_h1) => H; simpl in H; red in H; subst h1;
  assert (h = h2); [map_tac_m.Equal | subst h2; apply IHt2; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
by case_sepcon H; move: (IHt2 _ _ H_h2) => H; simpl in H; red in H; subst h2;
  assert (h = h1); [map_tac_m.Equal | subst h1; apply IHt1; auto].
by case_sepcon H; Compose_sepcon h1 h2; [apply IHt1; auto | apply IHt2; auto].
Qed.

Lemma Sigma_elt_eq_correct : forall e1 e2 env, Sigma_elt_eq e1 e2 env ->
  forall s h, [ env ]b_s -> Sigma_interp e1 s h -> Sigma_interp e2 s h.
Proof.
destruct e1; destruct e2; simpl; intros; try discriminate.
unfold Sigma_elt_eq in H.
case/andP : H => H2 H3.
move: (expr_b_dp_correct _ H2 s) => H.
move: (expr_b_dp_correct _ H3 s) => H4.
by Mapsto.
exists ([ e0 ]e_ s).
unfold Sigma_elt_eq in H.
move: (expr_b_dp_correct _ H s) => H2.
by Mapsto.
case: H1 => x H2.
exists x.
unfold Sigma_elt_eq in H.
move: (expr_b_dp_correct _ H s) => H1.
by Mapsto.
assumption.
Qed.

Opaque Sigma_clean_epsi.

Local Open Scope heap_scope.

Lemma Sigma_elt_term_extract_correct : forall e2 e1 env e2',
  Sigma_elt_term_extract e1 e2 env = Some e2' ->
  forall s h, [ env ]b_s ->
    Sigma_interp (star e1 e2') s h -> Sigma_interp e2 s h.
Proof.
induction e2; simpl; intros.
- move: (Sigma_elt_eq_correct e1 (singl e e0) env) => H2.
  destruct (Sigma_elt_eq e1 (singl e e0) env); try discriminate.
  case: H => ?; subst e2'.
  simpl in H1.
  case_sepcon H1.
  red in H1_h2.
  subst h2.
  assert (h = h1); [map_tac_m.Equal | subst h1].
  by apply (H2 refl_equal s h H0).
- move: (Sigma_elt_eq_correct e1 (cell e) env) => H2.
  destruct (Sigma_elt_eq e1 (cell e) env); try discriminate.
  case: H => ?; subst e2'.
  simpl in H1.
  case_sepcon H1.
  red in H1_h2.
  subst h2.
  assert (h = h1); [map_tac_m.Equal | subst h1].
  by apply (H2 refl_equal s h H0).
- move: (Sigma_elt_eq_correct e1 epsi env) => H2.
  destruct (Sigma_elt_eq e1 epsi env); try discriminate.
  case: H => ?; subst e2'.
  simpl in H1.
  case_sepcon H1.
  red in H1_h2.
  subst h2.
  assert (h = h1); [map_tac_m.Equal | subst h1].
  by apply (H2 refl_equal s h H0).
- move: (IHe2_1 e1 env) => H2.
  case_sepcon H1.
  clear IHe2_1.
  destruct (Sigma_elt_term_extract e1 e2_1 env).
  + case: H => ?; subst e2'.
    move: (Sigma_clean_epsi_correct _ _ _ H1_h2) => H.
    clear H1_h2.
    simpl in H.
    case_sepcon H.
    Compose_sepcon (h1 \U h21) h22; auto.
    apply (H2 s0 refl_equal s (h1 \U h21) H0).
    simpl.
    by Compose_sepcon h1 h21.
  + clear H2.
    move: (IHe2_2 e1 env) => H1.
    destruct (Sigma_elt_term_extract e1 e2_2 env); try discriminate.
    case: H => ?; subst e2'.
    move: (Sigma_clean_epsi_correct _ _ _ H1_h2) => H.
    clear H1_h2.
    simpl in H.
    case_sepcon H.
    Compose_sepcon h21 (h1 \U h22).
    exact H_h21.
    apply (H1 s0 refl_equal s (h1 \U h22) H0).
    simpl.
    by Compose_sepcon h1 h22.
Qed.

Lemma Sigma_elt_term_extract'_correct : forall e2 e1 env e2',
  Sigma_elt_term_extract' e1 e2 env = Some e2' ->
  forall s h, [ env ]b_s ->
    Sigma_interp e2 s h -> Sigma_interp (star e1 e2') s h.
Proof.
induction e2; simpl; intros.
- move: (Sigma_elt_eq_correct (singl e e0) e1  env) => H2.
  destruct (Sigma_elt_eq (singl e e0) e1 env); try discriminate.
  case : H => ?; subst e2'.
  simpl in H1.
  Compose_sepcon h assert_m.heap.emp; last by done.
  by apply H2.
- move: (Sigma_elt_eq_correct (cell e) e1  env) => H2.
  destruct (Sigma_elt_eq (cell e) e1 env); try discriminate.
  case : H => ?; subst e2'.
  simpl in H1.
  Compose_sepcon h assert_m.heap.emp; last by done.
  by apply H2.
- move: (Sigma_elt_eq_correct epsi e1 env) => H2.
  destruct (Sigma_elt_eq epsi e1 env); try discriminate.
  case : H => ?; subst e2'.
  Compose_sepcon h assert_m.heap.emp; last by done.
  by apply H2.
- move: (IHe2_1 e1 env) => H2.
  case_sepcon H1.
  clear IHe2_1.
  destruct (Sigma_elt_term_extract' e1 e2_1 env).
  + case: H => ?; subst e2'.
    move: (H2 s0 refl_equal s h1 H0 H1_h1) => H.
    simpl in H.
    case_sepcon H.
    Compose_sepcon h11 (h12 \U h2); first by done.
    apply Sigma_clean_epsi_correct'.
    by Compose_sepcon h12 h2.
  + clear H2.
    move: (IHe2_2 e1 env) => H1.
    destruct (Sigma_elt_term_extract' e1 e2_2 env); try discriminate.
    case: H => ?; subst e2'.
    move: (H1 s0 refl_equal s h2 H0 H1_h2) => H.
    simpl in H.
    case_sepcon H.
    Compose_sepcon h21 (h1 \U h22); first by done.
    apply Sigma_clean_epsi_correct'.
    by Compose_sepcon h1 h22.
Qed. 

Lemma Sigma_term_term_eq_correct :  forall t1 t2 env t1',
  Sigma_term_term_eq t1 t2 env = Some t1' ->
  forall s h, [ env ]b_s ->
    Sigma_interp (star t1 t1') s h -> Sigma_interp t2 s h.
Proof.
induction t1; simpl; intros.
- move: (Sigma_elt_term_extract_correct t2 (singl e e0) env) => H2.
  destruct (Sigma_elt_term_extract (singl e e0) t2 env); try discriminate.
  apply (H2 s0 refl_equal s h H0).
  case: H => ?; subst s0.
  exact H1.
- move: (Sigma_elt_term_extract_correct t2 (cell e) env) => H2.
  destruct (Sigma_elt_term_extract (cell e) t2 env); try discriminate.
  apply (H2 s0 refl_equal s h H0).
  case: H => ?; subst s0.
  exact H1.
- move: (Sigma_elt_term_extract_correct t2 epsi env) => H2.
  destruct (Sigma_elt_term_extract epsi t2 env); try discriminate.
  eapply (H2 s0 refl_equal s h H0).
  case: H => ?; subst s0.
  exact H1.
- case_sepcon H1.
  case_sepcon H1_h1.
  move: (IHt1_1 t2 env) => H1 {IHt1_1}.
  destruct (Sigma_term_term_eq t1_1 t2 env); try discriminate.
  apply (H1 s0 refl_equal s h H0).
  simpl.
  Compose_sepcon h11 (h2 \U h12); clear H1; auto.
  generalize (IHt1_2 s0 env); intros; clear IHt1_2.
  destruct (Sigma_term_term_eq t1_2 s0 env); try discriminate.
  apply (H1 s1 refl_equal s (h2 \U h12) H0).
  case: H => ?; subst s1.
  by Compose_sepcon h12 h2.
Qed.

Lemma Sigma_get_cell_val_correct : forall sig e env e',
  Sigma_get_cell_val e sig env = Some e' ->
  forall s h, [ env ]b_s ->
    Sigma_interp sig s h -> (Sigma_interp (singl e e') ** TT) s h.
Proof.
induction sig => //.
- simpl.
  intros.
  have [H3 | H3] : ~~ expr_b_dp (env =b> (e \= e1)) \/ expr_b_dp (env =b> (e \= e1)).
    destruct (expr_b_dp (env =b> (e \= e1))); intuition.
  + rewrite (negbTE H3) // in H.
  + rewrite H3 in H.  
    injection H; clear H; intros; subst e0.
    Compose_sepcon h assert_m.heap.emp; last by done.
    Mapsto.
    generalize (expr_b_dp_correct _ H3 s); intros.
    eval_b2Prop_hyps.
    tauto.
- simpl; intros.
  have [H3 | [x H2]] : Sigma_get_cell_val e sig1 env = None \/ 
    exists v, Sigma_get_cell_val e sig1 env = Some v.
    destruct (Sigma_get_cell_val e sig1 env).
    right; by exists e0.
    by left.
  + rewrite H3 in H.
    have [H4 | [x H2]] : Sigma_get_cell_val e sig2 env = None \/ exists v, Sigma_get_cell_val e sig2 env = Some v.
      destruct (Sigma_get_cell_val e sig2 env).
      right; by exists e0.
      by left.
    * rewrite H4 in H; discriminate.
    * case_sepcon H1.
      move: (IHsig2 _ _ _ H2 _ _ H0 H1_h2) => H1.
      case_sepcon H1.
      rewrite /= in H1_h21.
      Compose_sepcon h21 (h1 \U h22); last by done.
      Mapsto.
      by rewrite H2 in H; case: H => ?; subst x.
  + case_sepcon H1.
    rewrite H2 in H.
    case : H => ?; subst x.
    move: (IHsig1 _ _ _ H2 _ _ H0 H1_h1) => H.
    case_sepcon H.
    Compose_sepcon h11 (h12 \U h2); last by done.
    exact H_h11.
Qed.

Lemma frag_decision_correct : forall P Q,
  frag_decision P Q -> assrt_interp P ===> assrt_interp Q.
Proof.
intros.
rewrite /while.entails; intros.
destruct P as [p s0]; destruct Q as [p0 s1].
simpl; simpl in H0.
inversion_clear H0.
unfold frag_decision in H.
move: (expr_b_dp_correct (p =b> p0)) => H0.
destruct (expr_b_dp (p =b> p0)); simpl in H; try discriminate.
split.
+ move: (H0 refl_equal s) => H3; by omegab.
+ clear H0.
  move: (Sigma_term_term_eq_correct s0 s1 p) => H0.
  destruct (Sigma_term_term_eq s0 s1 p); simpl in H; try discriminate.
  apply (H0 s2 refl_equal s h H1); clear H0.
  destruct s2; simpl in H; try discriminate.
  simpl.
  by Compose_sepcon h assert_m.heap.emp.
Qed.

Transparent Sigma_clean_epsi.

(**  proof system for hoare triple using the fragment *)

Inductive wpAssrt : Type :=
| wpElt : assrt -> wpAssrt
| wpSubst : list (var.v * expr) -> wpAssrt -> wpAssrt
| wpLookup : var.v -> expr -> wpAssrt -> wpAssrt
| wpMutation : expr -> expr -> wpAssrt -> wpAssrt
| wpIf : expr_b -> wpAssrt -> wpAssrt -> wpAssrt.

Fixpoint wpAssrt_interp (a : wpAssrt) : assert :=
  match a with
    | wpElt a1 => assrt_interp a1
    | wpSubst l L => wp_assigns l (wpAssrt_interp L)
    | wpLookup x e L =>
      fun s h => exists e0, (e |~> e0 ** (e |~> e0 -* (wp_assign x e0 (wpAssrt_interp L)))) s h
    | wpMutation e1 e2 L =>
      fun s h => exists e0, (e1 |~> e0 ** (e1 |~> e2 -* (wpAssrt_interp L))) s h
    | wpIf b L1 L2 =>
      fun s h => ([ b ]b_ s -> wpAssrt_interp L1 s h) /\ (~~ [ b ]b_ s -> wpAssrt_interp L2 s h)
  end.

Fixpoint subst_Sigma (a : Sigma) (x : var.v) (e : expr) {struct a} : Sigma :=
  match a with
    | singl e1 e2 => singl (subst_e e1 (var_e x) e) (subst_e e2 (var_e x) e)
    | epsi => epsi
    | star s1 s2 => star (subst_Sigma s1 x e) (subst_Sigma s2 x e)
    | cell e1 => cell (subst_e e1 (var_e x) e)
  end.

Definition subst_assrt (a : assrt) (x : var.v) (e : expr) : assrt :=
  match a with
    | (pi, sigm) => (subst_b pi (var_e x) e, subst_Sigma sigm x e)
  end.

Fixpoint subst_assrt_lst (l : list (var.v * expr)) (a : assrt) {struct l} : assrt :=
  match l with 
    | nil => a
    | (x, e) :: tl => subst_assrt_lst tl (subst_assrt a x e)
  end.

(** properties of substitution functions *)

Lemma subst_Sigma2store_update : forall sigm s h x v,
  Sigma_interp (subst_Sigma sigm x v) s h -> 
  Sigma_interp sigm (store.upd x ([ v ]e_ s) s) h.
Proof.
induction sigm; simpl; intros; auto.
case: H => x0 H0.
exists x0.
by rewrite !eval_upd_subst.
case: H => x0 [x1 H].
exists x0, x1.
by rewrite !eval_upd_subst.
case_sepcon H.
Compose_sepcon h1 h2; by [apply IHsigm1 | apply IHsigm2].
Qed.

Lemma subst_Sigma2store_update' : forall sigm s h x v,
  Sigma_interp sigm (store.upd x ([ v ]e_ s) s) h -> 
  Sigma_interp (subst_Sigma sigm x v) s h.
Proof.
induction sigm; simpl; intros; auto.
inversion_clear H.
exists x0.
by rewrite -!eval_upd_subst.
case: H => x0 [x1 H0].
exists x0, x1.
by rewrite -!eval_upd_subst.
case_sepcon H.
Compose_sepcon h1 h2; by [apply IHsigm1 | apply IHsigm2].
Qed.

Lemma wp_assigns_assrt_interp : forall l s h pi sigm,
  assrt_interp (subst_assrt_lst l (pi, sigm)) s h ->
  wp_assigns l (assrt_interp (pi, sigm)) s h.
Proof.
elim => //.
case=> a b l IH /= s h pi sigm H.
move: (IH _ _ _ _ H) => H0.
rewrite (_ : wp_assign a b (fun s0 h0 => [ pi ]b_ s0 /\ Sigma_interp sigm s0 h0) =
  assrt_interp (subst_b pi (var_e a) b, subst_Sigma sigm a b)) //.
rewrite /wp_assign /=; apply assert_m.assert_ext; rewrite /while.equiv => s0 h0; split=> [[H2 H3]|[H2 H3]].
- rewrite eval_b_upd_subst in H2.
  split => //; by apply subst_Sigma2store_update'.
- rewrite -eval_b_upd_subst in H2.
  split => //; by apply subst_Sigma2store_update.
Qed.

(** a module for fresh variables (w.r.t. syntactic constructs) *)

Module Type FRESH.

Parameter fresh_Sigma : var.v -> Sigma -> bool.

Parameter fresh_assrt : var.v -> assrt -> bool.

Parameter fresh_wpAssrt : var.v -> wpAssrt -> bool.

Parameter fresh_wpAssrt_inde : forall L x , fresh_wpAssrt x L ->
  inde (x :: nil) (wpAssrt_interp L).

End FRESH.

Require Import Max.

Module Fresh <: FRESH.

Fixpoint var_max_Sigma (s : Sigma) : var.v :=
  match s with
    | singl e1 e2 => max (max_lst (vars e1)) (max_lst (vars e2))
    | epsi => O
    | star s1 s2 => max (var_max_Sigma s1) (var_max_Sigma s2)
    | cell e1 => max_lst (vars e1)
  end.

Definition var_max_assrt (a : assrt) : var.v :=
  match a with
    | (pi, sigm) => max (max_lst (vars_b pi)) (var_max_Sigma sigm)
  end.

Fixpoint var_max_wpAssrt (a : wpAssrt) : var.v :=
  match a with
    | wpElt a1 => var_max_assrt a1
    | wpSubst l L => max (var_max_lst l) (var_max_wpAssrt L)
    | wpLookup x e L=> max (max x (max_lst (vars e))) (var_max_wpAssrt L)
    | wpMutation e1 e2 L => max (max (max_lst (vars e1)) (max_lst (vars e2))) (var_max_wpAssrt L)
    | wpIf b L1 L2 => max (max (var_max_wpAssrt L1) (var_max_wpAssrt L2)) (max_lst (vars_b b))
  end.

Local Close Scope Z_scope.

Definition fresh_Sigma x s := (var_max_Sigma s < x)%nat.

Definition fresh_assrt x a := (var_max_assrt a < x)%nat.

Definition fresh_wpAssrt x L := (var_max_wpAssrt L < x)%nat.

Ltac open_fresh_frag :=
  open_fresh_frag_hypo; open_fresh_frag_goal
with          
  open_fresh_frag_hypo := match goal with
    | H: is_true (fresh_e _ _) |- _ => unfold fresh_e in H; simpl in H; open_fresh_frag_hypo
    | H: is_true (fresh_b _ _)  |- _ => unfold fresh_b in H; simpl in H; open_fresh_frag_hypo
    | H: is_true (fresh_Sigma _ _) |- _ => unfold fresh_Sigma in H; simpl in H; open_fresh_frag_hypo
    | H: is_true (fresh_assrt _ _) |- _ => unfold fresh_assrt in H; simpl in H; open_fresh_frag_hypo
    | H: is_true (fresh_lst _ _) |- _ => unfold fresh_lst in H; simpl in H; open_fresh_frag_hypo
    | H: is_true (fresh_wpAssrt _ _) |- _ => unfold fresh_wpAssrt in H; simpl in H; open_fresh_frag_hypo
    | H: context [ var_max_assrt _ ] |- _ => unfold var_max_assrt in H; simpl in H; open_fresh_frag_hypo
    | |- _ =>  idtac
  end
with
  open_fresh_frag_goal := match goal with
    | |- is_true (fresh_e _ _) => rewrite /fresh_e /=; open_fresh_frag_goal
    | |- is_true (fresh_b _ _) => rewrite /fresh_b /=; open_fresh_frag_goal
    | |- is_true (fresh_Sigma _ _) => rewrite /fresh_Sigma /=; open_fresh_frag_goal
    | |- is_true (fresh_assrt _ _) => rewrite /fresh_assrt /=; open_fresh_frag_goal
    | |- is_true (fresh_lst _ _) => rewrite /fresh_lst /=; open_fresh_frag_goal
    | |- is_true (fresh_wpAssrt _ _) => rewrite /fresh_wpAssrt /=; open_fresh_frag_goal
    | |- context [var_max_assrt _ ] => rewrite /var_max_assrt /=; open_fresh_frag_goal
    | |- _ => idtac
  end.

Ltac Max_inf_resolve := open_fresh_frag; Resolve_lt_max.

(** relations between freshness predicates and the independence predicate ("inde") *)

Lemma var_max_Sigma_inde : forall sigm x, fresh_Sigma x sigm ->
  inde (x :: nil) (Sigma_interp sigm).
Proof.
induction sigm => //=.
- rewrite /inde; split; intros; rewrite mem_seq1 in H0; move/eqP in H0.
  + rewrite /mapsto in H1 *.
    case: H1 => x1 [H2 H3].
    exists x1; split; rewrite fresh_e_eval //; by Max_inf_resolve.
  + rewrite /mapsto in H1 *.
    case: H1 => x1 [H2 H3].
    exists x1; split.
    * rewrite fresh_e_eval // in H2; by Max_inf_resolve.
    * rewrite fresh_e_eval // in H3; by Max_inf_resolve.
- rewrite /inde /=; split; intros; rewrite mem_seq1 in H0; move/eqP in H0.
  + case: H1 => x1 H2.
    exists x1.
    rewrite /mapsto in H2 *.
    case: H2 => x2 [H1 H2].
    exists x2.
    rewrite fresh_e_eval //; by Max_inf_resolve.
  + case: H1 => x1 H2.
    exists x1.
    rewrite /mapsto in H2 *.
    case : H2 => x2 [H1 H2].
    exists x2.
    rewrite fresh_e_eval // in H1; last by Max_inf_resolve.
- rewrite /inde /=; split; intros.
  + case_sepcon H1.
    Compose_sepcon h1 h2.
    * have /IHsigm1 : fresh_Sigma x sigm1 by Max_inf_resolve.
      by move/(_ s h1 _ v H0) => H2; apply H2.
    * have /IHsigm2 : fresh_Sigma x sigm2 by Max_inf_resolve.
      by move/(_ s h2 _ v H0) => H2; apply H2.
  + case_sepcon H1.
    Compose_sepcon h1 h2.
    * have /IHsigm1  : fresh_Sigma x sigm1 by Max_inf_resolve.
      by move/(_ s h1 _ v H0) => H2; apply H2.
    * have /IHsigm2 : fresh_Sigma x sigm2 by Max_inf_resolve.
      by move/(_ s h2 _ v H0) => H2; apply H2.
Qed.

Lemma fresh_assrt_inde : forall a x, fresh_assrt x a ->
  inde (x :: nil) (assrt_interp a).
Proof.
elim => /= a b x H.
have H0 : fresh_b x a by Max_inf_resolve.
have H1 : fresh_Sigma x b by Max_inf_resolve.
rewrite /inde /=; split; intros.
- case: H3 => H4 H5; split.
  * case : (fresh_b_inde a x true H0 s h _ v H2) => H3 _; by apply H3.
  * case : (var_max_Sigma_inde b x H1 s h _ v H2) => H3 _; by apply H3.
- case : H3 => H4 H5; split.
  * case : (fresh_b_inde a x true H0 s h _ v H2) => _; by apply.
  * case : (var_max_Sigma_inde b x H1 s h _ v H2) => _; by apply.
Qed.

Lemma fresh_wpAssrt_inde : forall L x, fresh_wpAssrt x L ->
  inde (x :: nil) (wpAssrt_interp L).
Proof.
elim => [a x|l L IHL x H|v e L IHL x H|e e0 L IHL x H s|e L IHL1 L0 IHL2 x].
- simpl.
  red; simpl; split; intros.
  move : (fresh_assrt_inde a x H s h x0 v H0); tauto.
  move : (fresh_assrt_inde a x H s h x0 v H0); tauto.
- red; simpl; split; intros.
  have H2 : inde (x::nil) (wpAssrt_interp L) by apply IHL; Max_inf_resolve.
  have H3 : fresh_lst x l by Max_inf_resolve.
  case : (fresh_lst_inde _ _ _ H2 H3 s h x0 v H0) => H4 _; by apply H4.
  have H2 : inde (x::nil) (wpAssrt_interp L) by apply IHL; Max_inf_resolve.
  have H3 : fresh_lst x l by Max_inf_resolve.
  case : (fresh_lst_inde _ _ _ H2 H3 s h x0 v H0) => H4; by apply.
- red; simpl; split; intros; rewrite mem_seq1 in H0; move/eqP in H0; subst x0.
  + case : H1 => x1 H2.
    case_sepcon H2.
    exists (cst_e ([ x1 ]e_ s)).
    Compose_sepcon h1 h2.
      Mapsto.
      rewrite fresh_e_eval //; by Max_inf_resolve.
    move=> h1' [X1 X2] h' Hh'.
    rewrite /imp in H2_h2.
    have H8 : (e |~> x1) s h1'.
      Mapsto.
      rewrite fresh_e_eval //; by Max_inf_resolve.
    move : (H2_h2 h1' (conj X1 H8) _ Hh') => H1.
    rewrite /wp_assign in H1 *.
    rewrite /= store.upd_upd; last by Max_inf_resolve.
    have H10 : fresh_wpAssrt x L by Max_inf_resolve.
    move: (IHL _ H10 (store.upd v (eval x1 s) s) h' x v0); rewrite mem_seq1 eqxx => /(_ isT) H2.
    by apply H2.
  + case : H1 => x1 H2.
    case_sepcon H2.
    exists (cst_e ([ x1 ]e_ (store.upd x v0 s))).
    Compose_sepcon h1 h2.
    * Mapsto.
      rewrite fresh_e_eval //; by Max_inf_resolve.
    * move=> h1' [X1 X2] h' Hh'.
      rewrite /imp in H2_h2.
      have H8 : (e |~> x1) (store.upd x v0 s) h1'.
        Mapsto.
        rewrite fresh_e_eval //; by Max_inf_resolve.
      move : (H2_h2 h1' (conj X1 H8) _ Hh') => H1.
      rewrite /wp_assign in H1 *.
      simpl.
      rewrite store.upd_upd in H1; last by Max_inf_resolve.
      have H10 : fresh_wpAssrt x L by Max_inf_resolve.
      move : (IHL _ H10 (store.upd v ([ x1 ]e_(store.upd x v0 s)) s) h' x v0); rewrite mem_seq1 eqxx => /(_ isT) H2; by apply H2.
- red; simpl; split; intros; rewrite mem_seq1 in H0; move/eqP in H0; subst x0.
  + case : H1 => x1 H2.
    case_sepcon H2.
    exists (cst_e (eval x1 s)).
    Compose_sepcon h1 h2.
    * Mapsto.
      rewrite fresh_e_eval //; by Max_inf_resolve.
    * move=> h1' [X1 X2] h' Hh'.
      rewrite /imp in H2_h2.
      have H8 : (e |~> e0) s h1'.
        Mapsto.
        rewrite fresh_e_eval //; by Max_inf_resolve.
        rewrite fresh_e_eval //; by Max_inf_resolve.
      move: (H2_h2 _ (conj X1 H8) _ Hh') => H9.
      have H10 : fresh_wpAssrt x L by Max_inf_resolve.
      move: (IHL _ H10 s h' x v); rewrite mem_seq1 eqxx => /(_ isT) X; by apply X.
  + case: H1 => x1 H2.
    case_sepcon H2.
    exists (cst_e (eval x1 (store.upd x v s))).
    Compose_sepcon h1 h2.
    * Mapsto.
      rewrite fresh_e_eval //; by Max_inf_resolve.
    * move=> h1' [X1 X2] h' Hh'.
      red in H2_h2.
      have H8 : (e |~> e0) (store.upd x v s) h1'.
        Mapsto.
        rewrite fresh_e_eval //; by Max_inf_resolve.
        rewrite fresh_e_eval //; by Max_inf_resolve.
      move: (H2_h2 _ (conj X1 H8) _ Hh') => H9.
      have H10 : fresh_wpAssrt x L by Max_inf_resolve.
      move: (IHL _ H10 s h' x v); rewrite mem_seq1 eqxx => /(_ isT) X; by apply X.
- red; simpl; split; intros; rewrite mem_seq1 in H0; move/eqP in H0; subst x0.
  + case: H1 => H2 H3; split => H1.
    * have H4 : fresh_wpAssrt x L by Max_inf_resolve.
      move: (IHL1 _ H4 s h x v); rewrite mem_seq1 eqxx => /(_ isT) H5.
      apply H5, H2.
      have H7 : fresh_b x e by Max_inf_resolve.
      move: (fresh_b_inde e x true H7 s h x v); rewrite mem_seq1 eqxx => /(_ isT) X; by apply X.
    * have H4 : fresh_wpAssrt x L0 by Max_inf_resolve.
      move: (IHL2 _ H4 s h x v); rewrite mem_seq1 eqxx => /(_ isT) H5.
      apply H5, H3.
      have H7 : fresh_b x e by Max_inf_resolve.
      move: (fresh_b_inde e x false H7 s h x v); rewrite mem_seq1 eqxx => /(_ isT) X.
      by apply/negbT/X/negbTE.
    + case : H1 => H2 H3; split => H1.
      * have H4 : fresh_wpAssrt x L by Max_inf_resolve.
        move: (IHL1 _ H4 s h x v); rewrite mem_seq1 eqxx => /(_ isT) H6.
        apply H6, H2.
        have H7 : fresh_b x e by Max_inf_resolve.
        move: (fresh_b_inde e x true H7 s h x v); rewrite mem_seq1 eqxx => /(_ isT) H8; by apply H8.
      * have H4 : fresh_wpAssrt x L0 by Max_inf_resolve.
        move: (IHL2 _ H4 s h x v); rewrite mem_seq1 eqxx => /(_ isT) H6.
        apply H6, H3.
        have H7 : fresh_b x e by Max_inf_resolve.
        move: (fresh_b_inde e x false H7 s h x v); rewrite mem_seq1 eqxx => /(_ isT) H8.
        by apply/negbT/H8/negbTE.
Qed.

End Fresh.

Import Fresh.

(** definition of LWP and its soundness *)
(* NB j'ai vire incons, mais faut rajouter un equiv *)

Inductive LWP : assrt -> wpAssrt -> Prop :=
| LWP_entail : forall pi1 pi2 sig1 sig2,
  assrt_interp (pi1, sig1) ===> assrt_interp (pi2, sig2) ->
  LWP (pi1, sig1) (wpElt (pi2, sig2))

| LWP_precond_stre : forall L1 L1' L2,
  assrt_interp L1 ===> assrt_interp L1' ->
  LWP L1' L2 ->
  LWP L1 L2

| LWP_if : forall pi1 sig1 L1 L2 b,
  LWP (pi1 \&& b, sig1)  L1 ->
  LWP (pi1 \&& (\~ b), sig1) L2 ->
  LWP (pi1, sig1) (wpIf b L1 L2)

| LWP_mutation : forall pi1 sig1 e1 e2 e3 e4 L,
  (forall s, [ pi1 ]b_s -> [ e1 \= e3 ]b_s) ->
  LWP (pi1, star sig1 (singl e1 e4)) L ->
  LWP (pi1, star sig1 (singl e1 e2)) (wpMutation e3 e4 L)

| LWP_mutation' : forall pi1 sig1 e1 e3 e4 L,
  (forall s, [ pi1 ]b_s -> [ e1 \= e3 ]b_s) ->
  LWP (pi1, star sig1 (singl e1 e4)) L ->
  LWP (pi1, star sig1 (cell e1)) (wpMutation e3 e4 L)

| LWP_lookup : forall pi1 sig1 e1 e2 e x L,
  (forall s, [ pi1 ]b_s -> [ e1 \= e ]b_s) ->
  LWP (pi1, star sig1 (singl e1 e2)) (wpSubst ((x, e2) :: nil) L) ->
  LWP (pi1, star sig1 (singl e1 e2)) (wpLookup x e L)

| LWP_subst_elt : forall pi1 pi2 sig1 sig2 l,
  LWP (pi1, sig1) (wpElt (subst_assrt_lst l (pi2, sig2))) ->
  LWP (pi1, sig1) (wpSubst l (wpElt (pi2, sig2)))

| LWP_subst_subst : forall pi1 sig1 l1 l2 L,
  LWP (pi1, sig1) (wpSubst (l2 ++ l1) L) ->
  LWP (pi1, sig1) (wpSubst l1 (wpSubst l2 L))

| LWP_subst_lookup : forall pi1 sig1 e1 e2 e x x' l L,
  (forall s, [ pi1 ]b_s -> [ e1 \= subst_e_lst l e ]b_ s) ->
  fresh_lst x' l ->
  fresh_wpAssrt x' L ->
  fresh_e x' (var_e x) ->
  LWP (pi1, star sig1 (singl e1 e2)) (wpSubst ((x, (var_e x')) :: l ++ ((x', e2) :: nil)) L) ->
  LWP (pi1, star sig1 (singl e1 e2)) (wpSubst l (wpLookup x e L))
  
| LWP_subst_mutation : forall pi1 sig1 e1 e2 l L, 
  LWP (pi1, sig1) (wpMutation (subst_e_lst l e1) (subst_e_lst l e2) (wpSubst l L)) ->
  LWP (pi1, sig1) (wpSubst l (wpMutation e1 e2 L))
    
| LWP_subst_if : forall pi1 sig1 l b L1 L2, 
  LWP (pi1, sig1)  (wpIf (subst_b_lst l b) (wpSubst l L1) (wpSubst l L2)) ->
  LWP (pi1, sig1) (wpSubst l (wpIf b L1 L2)).

(** replace a substitution (e/x) by two substitutions (x/x')(e/x') with x' fresh *)
Lemma intro_fresh_var : forall l x x' e s h L,
  fresh_lst x' l -> fresh_wpAssrt x' L -> fresh_e x' (var_e x) ->
  wp_assigns l (fun s' h' => wpAssrt_interp L (store.upd x ([ var_e x' ]e_ s') s') h')
    (store.upd x' ([ e ]e_ s) s) h ->
  wp_assigns l (fun s' h' => wpAssrt_interp L (store.upd x ([ e ]e_ s) s') h')
    s h.
Proof.
move=> l x x' e s h L H H0 H1 H2; apply intro_fresh_var' with x' => //.
by apply fresh_wpAssrt_inde.
Qed.

Import ZIT.

Lemma LWP_soundness: forall P Q, LWP P Q -> assrt_interp P ===> wpAssrt_interp Q.
Proof.
move=> P Q H.
induction H.
- rewrite /while.entails => /= s h H0.
  rewrite /= in H.
  by apply H.
- rewrite /while.entails => /= s h H1.
  by apply IHLWP, H.
- rewrite /while.entails => /= s h H1.
  rewrite /= in IHLWP1 IHLWP2.
  split => X.
  + case: H1 => H11 H12.
    apply IHLWP1.
    split => //.
    by rewrite H11 X.
  + apply IHLWP2.
    by case: H1 => -> H12.
- rewrite /while.entails => /= s h [H2 H3].
  case_sepcon H3.
  rewrite /= in IHLWP.
  exists e2.
  move: (H _ H2) => H5.
  Compose_sepcon h2 h1.
  by Mapsto.
  move=> h2' [X1 X2] h' Hh'.
  apply IHLWP.
  split; first by assumption.
  Compose_sepcon h1 h2'; [assumption | by Mapsto].
- rewrite /while.entails => /= s h [H2 H3].
  rewrite /= in IHLWP.
  case_sepcon H3.
  move: (H _ H2) => H5.
  case: H3_h2 => x H7.
  exists (cst_e x).
  Compose_sepcon h2 h1; first by Mapsto.
  move=> h2' [X1 X2] h' Hh'.
  apply IHLWP.
  split; first by assumption.
  Compose_sepcon h1 h2'; [assumption | by Mapsto].
- rewrite /while.entails => /= s h [H2 H3].
  rewrite /= in IHLWP.
  move: (H _ H2) => H1.
  case_sepcon H3.
  exists e2.
  Compose_sepcon h2 h1; first by Mapsto.
  move=> h2' [X1 X2] h' Hh'.
  apply IHLWP.
  split; first by assumption.
  Compose_sepcon h1 h2'; [assumption | by Mapsto].
- (* case LWP_subst_elt *) rewrite /while.entails => /= s h H0.
  rewrite /= in IHLWP.
  move: {H0}(IHLWP _ _ H0) => H1.
  apply (wp_assigns_and l (fun s h => [ pi2 ]b_ s) (fun s h => Sigma_interp sig2 s h) s h).
  move: (wp_assigns_assrt_interp l s h pi2 sig2 H1) => H2.
  by case: (wp_assigns_and_inv l (fun s h => [ pi2 ]b_ s) (fun s h => Sigma_interp sig2 s h) s h H2).
- (* case LWP_subst_subst *) rewrite /while.entails => /= s h H0.
  rewrite /= in IHLWP.
  move: {H0}(IHLWP _ _ H0) => H1.
  by apply wp_assigns_app.
- (* case LWP_subst_lookup *) rewrite /while.entails => /= s h H4.
  rewrite /= in IHLWP.
  move: (IHLWP _ _ H4) => H5.
  move: (H _  (proj1 H4)) => H6.
  case: H4 => H7 H8.
  case_sepcon H8.
  apply (wp_assigns_exists l 
    (fun e0 s h => (e |~> e0 ** (e |~> e0 -* wp_assign x e0 (wpAssrt_interp L))) s h) 
    s h).
  exists (cst_e ([ e2 ]e_ s)).
  have -> : (fun s0 h0 => 
    (e |~> cst_e (eval e2 s) ** (e |~> cst_e (eval e2 s) -* wp_assign x (cst_e (eval e2 s)) (wpAssrt_interp L))) 
    s0 h0)
    = 
    (e |~> cst_e (eval e2 s) ** (e |~> cst_e (eval e2 s) -* wp_assign x (cst_e (eval e2 s)) (wpAssrt_interp L))).
    apply assert_m.assert_ext.
    rewrite /while.equiv; by intuition.
  apply wp_assigns_sepcon.
  Compose_sepcon h2 h1.
  apply wp_assigns_mapsto.
  Mapsto.
  by rewrite subst_e_lst_cst_e.
  apply wp_assigns_sepimp.
  move=> h2' [X1 X2] h' Hh'.
  rewrite /wp_assign /=.
  have ? : h2 = h2'.
    eapply singl_equal.
    apply H8_h2.
    apply (wp_assigns_mapsto_inv _ _ _ _ _ X2).
    by omegab.
    by rewrite subst_e_lst_cst_e.
  subst h2'.
  have H14 : h = h' by map_tac_m.Equal.
  subst h'.
  rewrite -H14.
  move: (wp_assigns' _ _ _ _ _ _ H5) => H13.
  rewrite /wp_assign in H13.
  by apply intro_fresh_var with x'.
- (* case LWP_subst_mutation *) rewrite /while.entails => /= s h H0.
  move: (IHLWP _ _ H0) => H1.
  by apply wp_assigns_lookup.
- (* case LWP_subst_if *) rewrite /while.entails => /= s h H0.
  move: (IHLWP _ _ H0) => /= [H2 H3].
  apply (wp_assigns_and l (fun s0 h0 => [ b ]b_ s0 -> wpAssrt_interp L1 s0 h0) (fun s0 h0 => ~~ [ b ]b_ s0 -> wpAssrt_interp L2 s0 h0) s h).
  split.
  + apply (wp_assigns_imp l (fun s h => [ b ]b_ s) (fun s h => wpAssrt_interp L1 s h) s h) => H1.
    move: (H2 (wp_assigns_subst_b_lst true _ _ _ _ H1)) => H4.
    suff : wpAssrt_interp L1 = (fun s h => wpAssrt_interp L1 s h) by move=> <-.
    apply assert_m.assert_ext; rewrite /while.equiv /=; tauto.
  + apply (wp_assigns_imp l (fun s h => ~~ [ b ]b_ s) (fun s h => wpAssrt_interp L2 s h) s h) => H1.
    move: (H3 (wp_assigns_subst_b_lst false _ _ _ _ H1)) => H5.
    suff : wpAssrt_interp L2 = (fun s h => wpAssrt_interp L2 s h) by move <-.
    apply assert_m.assert_ext; rewrite /while.equiv /=; tauto.
Qed.

(** weakest pre-condition generator and its soudness *)
  
Fixpoint wp_frag (Q : option wpAssrt) (c : @while.cmd cmd0 expr_b) {struct c} : option wpAssrt :=
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
                                      | Some Q1 => match wp_frag Q c2 with 
                                                     | None => None
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
induction c => //=; intros.
- (* cmd0 *) induction c => //.
  + injection H; intros; subst Q'.
    by apply while.hoare_hoare0, hoare0_skip.
  + injection H; intros; subst Q'.
    by apply while.hoare_hoare0, hoare0_assign.
  + injection H; intros; subst Q'.
    by apply hoare_lookup_back.
  + injection H; intros; subst Q'.
    by apply hoare_mutation_backwards.
- (* seq *) have H0 : (exists v, wp_frag (Some Q) c2 = Some v) \/ wp_frag (Some Q) c2 = None.
    elim wp_frag.
    + intros; left; by exists a.
    + by right.
  case : H0 => H1.
  + case : H1 => x H0.
    rewrite H0 in H.
    apply while.hoare_seq with (wpAssrt_interp x); by [apply IHc1 | apply IHc2].
  + by rewrite H1 wp_frag_None_is_None in H.
- (* ifte *) have H0 : (exists v, wp_frag (Some Q) c1 = Some v) \/ wp_frag (Some Q) c1 = None.
    elim wp_frag.
    intros; left; exists a.
    reflexivity.
    by right.
  case : H0 => H1.
  + case : H1 => x H0.
    rewrite H0 in H.
    have [[x0 H1] | H2] : (exists v, wp_frag (Some Q) c2 = Some v) \/ wp_frag (Some Q) c2 = None.
      elim wp_frag.
      intros; left; by exists a.
      by right.
    + rewrite H1 in H.
      case: H => ?; subst Q'.
      apply while.hoare_ifte.
      * apply hoare_prop_m.hoare_stren with (wpAssrt_interp x).
        rewrite /while.entails /=; tauto.
        by apply IHc1.
      * apply hoare_prop_m.hoare_stren with (wpAssrt_interp x0).
        rewrite /while.entails /=.
        by intuition.
        by apply IHc2.
    + by rewrite H2 in H.
  + by rewrite H1 in H.
Qed.

(** Resolution tactic *)

Lemma LWP_use : forall c P Q R, 
  wp_frag (Some (wpElt Q)) c = Some R -> 
  LWP P R -> 
  {{ assrt_interp P }} c {{ assrt_interp Q }}.
Proof.
move=> x P Q R H H0; move: (wp_frag_soudness _ _ _ H) => H1.
rewrite /= in H1.
apply hoare_prop_m.hoare_stren with (wpAssrt_interp R); last by done.
by apply LWP_soundness.
Qed.

Local Close Scope Z_scope.

(* the following lemma replaces the constructor LWP_subst_lookup in the tactic,
  the difference is that it introduces a way to compute fresh variables *)
Lemma LWP_subst_lookup' : forall pi1 sig1 e1 e2 e x x' l L,
  (forall s, [ pi1 ]b_ s -> [ e1 \= (subst_e_lst l e) ]b_ s) ->                   
  x' = (max (max (var_max_lst l) (var_max_wpAssrt L)) x) + 1 ->
  LWP (pi1, star sig1 (singl e1 e2)) (wpSubst ((x, (var_e x')) :: l ++ ((x', e2) :: nil)) L) ->
  LWP (pi1, star sig1 (singl e1 e2)) (wpSubst l (wpLookup x e L)).
Proof.
intros.
apply LWP_subst_lookup with x'.
- by auto.
- rewrite /fresh_lst H0.
  have H2 : var_max_lst l <= max (max (var_max_lst l) (var_max_wpAssrt L)) x by Resolve_le_max.
  ssromega.
- rewrite /fresh_wpAssrt H0.
  have H2 : var_max_wpAssrt L <= max (max (var_max_lst l) (var_max_wpAssrt L)) x by Resolve_le_max.
  ssromega.
- rewrite /fresh_e H0 /= /max_lst /max_list /=.
  have H2 : x <= max (max (var_max_lst l) (var_max_wpAssrt L)) x by Resolve_le_max.
  ssromega.
- exact H1.
Qed.

(** Tactics to resolve LWP goals *)

Fixpoint Sigma_assoc_left (t t' : Sigma) {struct t} : Sigma :=
  match t with
    | star sig1 sig2 => Sigma_assoc_left (sig2) (star t' sig1)
    | _ => match t' with
             | epsi => t
             | _ => star t' t
           end
 end.

Definition Sigma_com (t : Sigma) : Sigma :=
  match t with
    | star sig1 sig2 => star sig2 sig1
    | _ => t
  end.

Ltac Rotate_LWP_sig_lhs :=
  match goal with
    | |- LWP (?pi, ?sig) ?L' =>
      apply LWP_precond_stre with ((pi, Sigma_clean_epsi (Sigma_assoc_left (Sigma_com sig) epsi))); 
        [apply ps1_soundness; simpl; ps1_Resolve| simpl]
  end.

Ltac LWP_resolve := 
  match goal with 
    | |- LWP (?pi1, ?sig1) (wpElt (?pi2, ?sig2)) => apply LWP_entail; [eapply ps1_soundness; ps1_Resolve]
      
    | |- LWP (?pi1, star ?sig1 (singl ?e1 ?e2)) (wpMutation ?e3 ?e4 ?L') => 
      apply LWP_mutation; [(do 2 intro; omegab) | LWP_resolve] || Rotate_LWP_sig_lhs; idtac
      
    | |- LWP (?pi1, star ?sig1 (cell ?e1)) (wpMutation ?e3 ?e4 ?L') => 
      apply LWP_mutation'; [(do 2 intro; omegab) | LWP_resolve] || Rotate_LWP_sig_lhs; idtac
      
    | |- LWP (?pi1, star ?sig1 (singl ?e1 ?e2)) (wpLookup ?x ?e ?L') => 
      apply LWP_lookup; [(do 2 intro; omegab) | LWP_resolve] || Rotate_LWP_sig_lhs; idtac
      
    | |- LWP ?L (wpSubst ?l (wpElt ?L')) => eapply LWP_subst_elt; simpl; idtac
    | |- LWP ?L (wpSubst ?l (wpSubst ?l' ?L')) => eapply LWP_subst_subst; simpl; idtac
      
    | |- LWP ?L (wpSubst ?l (wpLookup ?x ?e ?L')) => 
      eapply LWP_subst_lookup'; [(do 2 intro; omegab) | simpl; intuition | LWP_resolve] || Rotate_LWP_sig_lhs; idtac
      
    | |- LWP ?L (wpSubst ?l (wpMutation ?e1 ?e2 ?L')) => apply LWP_subst_mutation; simpl; idtac
    | |- LWP ?L (wpSubst ?l (wpIf ?b ?L1 ?L2)) => eapply LWP_subst_if; simpl; idtac
    | |- LWP ?L (wpIf ?b ?L1 ?L2) => eapply LWP_if; simpl; idtac
   end.

Ltac LWP_Resolve := Rotate_LWP_sig_lhs; repeat LWP_resolve.

Definition LWP_step (pi : expr_b) (sig : Sigma) (A : wpAssrt) : option (list ((expr_b * Sigma) * wpAssrt)) :=
  match A with
    | wpElt L => if frag_decision (pi, sig) L then Some nil else None
    | wpSubst l L =>
      match L with
        | wpElt L' => Some (((pi, sig), wpElt (subst_assrt_lst l L')) :: nil) 
        | wpSubst l' L' => Some (((pi, sig), wpSubst (l'++ l) L') :: nil)
        | wpLookup x e L' => 
          match Sigma_get_cell_val (subst_e_lst l e) sig pi with
            | None => None
            | Some e' => 
              let x' := (max (max (var_max_lst l) (var_max_wpAssrt L')) x) + 1 in
                Some (((pi, sig), wpSubst ((x, var_e x')::l ++ ((x', e')::nil)) L')::nil)
          end
        | wpMutation e1 e2 L' => 
          Some (((pi, sig), wpMutation (subst_e_lst l e1) (subst_e_lst l e2) (wpSubst l L')) :: nil)
        | wpIf b L1 L2 => 
          Some (((pi, sig), wpIf (subst_b_lst l b) (wpSubst l L1) (wpSubst l L2)) :: nil)
      end
    | wpLookup x e L =>       
      match Sigma_get_cell_val e sig pi with
        | None => None
        | Some e' => Some (((pi, sig), wpSubst ((x, e') :: nil) L) :: nil)
      end
    | wpMutation e1 e2 L => 
      match Sigma_elt_term_extract' (cell e1) sig pi with
        | None => None
        | Some sig' => Some (((pi, star (singl e1 e2) sig'), L) :: nil)
      end
    | wpIf b L1 L2 => 
      Some (((pi \&& b, sig), L1) :: ((pi \&& (\~ b), sig), L2) :: nil)
  end.

Fixpoint wpAssrt_size (A : wpAssrt) : nat :=
  match A with
    | wpElt P => 2
    | wpSubst l P => 2 + wpAssrt_size P
    | wpLookup x e P => 2 + wpAssrt_size P
    | wpMutation e1 e2 P  => 2 + wpAssrt_size P
    | wpIf b L1 L2 => 2 + wpAssrt_size L1 + wpAssrt_size L2
  end.

Fixpoint LWP_list (l : list ((expr_b * Sigma) * wpAssrt)) : option (list ((expr_b * Sigma) * wpAssrt)) :=
  match l with
    | nil => Some nil
    | ((pi, sig), A) :: tl =>
      match LWP_step pi sig A with
        | None => None
        | Some l' => 
          match LWP_list tl with
            | None => None
            | Some l'' => Some (l' ++ l'')
          end
      end
  end.

Fixpoint LWP_list_rec (l : list ((expr_b * Sigma) * wpAssrt)) (size : nat) {struct size} : option (list ((expr_b * Sigma) * wpAssrt)) :=
  match size with
    | 0 => Some l
    | S size' =>
      match LWP_list l with
        | None => None
        | Some l' => LWP_list_rec l' size'
      end
  end.

Definition frag_hoare (P Q : expr_b * Sigma) (c : @while.cmd cmd0 expr_b) : bool :=
  match wp_frag (Some (wpElt Q)) c with
    | None => false
    | Some L =>
      let (p, s) := P in
        match LWP_list_rec (((p, s), L) :: nil) (wpAssrt_size L) with
          | Some nil => true
          | _ => false
        end
  end.

Opaque frag_decision.

Lemma LWP_step_correct : forall pi sig A l,
  LWP_step pi sig A = Some l ->
  (forall pi' sig' A', List.In ((pi', sig'), A') l -> assrt_interp (pi',sig') ===> wpAssrt_interp A') ->
  assrt_interp (pi, sig) ===> wpAssrt_interp A.
Proof.
move=> pi sig A l H H0.
destruct A.
- (* wpElt *)
  destruct a as [p s].
  simpl in H.
  have [H2 | H2] : frag_decision (pi, sig) (p, s) \/ ~~ frag_decision (pi, sig) (p, s).
    destruct (frag_decision (pi, sig) (p, s)); by intuition.
  + rewrite /while.entails; intros.
    by apply (frag_decision_correct _ _ H2 _ _ H1).
  + by rewrite (negbTE H2) in H.
- (* wpSubst *)
  destruct A.
  + (* wpElt *) rewrite /= in H.
    rewrite /while.entails; case: H => ? s h H2; subst l.
    rewrite /= in H0.
    have H : (pi, sig, wpElt (subst_assrt_lst l0 a)) = (pi, sig, wpElt (subst_assrt_lst l0 a)) \/ False.
      by left.
    move: {H H0}(H0 _ _ _ H s h H2) => /=.
    destruct a.
    by apply wp_assigns_assrt_interp.
  + (* wpSubst *) rewrite /= in H.
    rewrite /while.entails; injection H; intros; subst l; clear H.
    simpl in H0.
    have H : (pi, sig, wpSubst (l1 ++ l0) A) = (pi, sig, wpSubst (l1 ++ l0) A) \/ False.
      by left.
    move: {H0 H}(H0 _ _ _ H s h H2) => /=.
    by apply wp_assigns_app.
  + (* wpLookup *)
    rewrite /= in H.
    rename s into v.
    rewrite /while.entails => s h H1 /=.
    have [H3|[x H2]] : Sigma_get_cell_val (subst_e_lst l0 e) sig pi = None \/ exists v, Sigma_get_cell_val (subst_e_lst l0 e) sig pi = Some v.
      destruct (Sigma_get_cell_val (subst_e_lst l0 e) sig pi).
      right; by exists e0.
      by left.
    by rewrite H3 in H.
    rewrite H2 in H.
    case: H => H; subst l.
    simpl in H0.
    assert ((pi, sig, wpSubst
      ((v, var_e (max (max (var_max_lst l0) (var_max_wpAssrt A)) v + 1))
        :: l0 ++
        (max (max (var_max_lst l0) (var_max_wpAssrt A)) v + 1, x) :: nil)
      A) = (pi, sig, wpSubst
        ((v, var_e (max (max (var_max_lst l0) (var_max_wpAssrt A)) v + 1))
          :: l0 ++
          (max (max (var_max_lst l0) (var_max_wpAssrt A)) v + 1, x) :: nil)
        A) \/ False).
    tauto.
    move: {H H0}(H0 _ _ _ H s h H1) => H.
    rewrite /= in H H1.
    move: (Sigma_get_cell_val_correct _ _ _ _ H2 _ _ (proj1 H1) (proj2 H1)) => H0.
    apply (wp_assigns_exists l0
      (fun e0 s h => (e |~> e0 ** (e |~> e0 -* wp_assign v e0 (wpAssrt_interp A))) s h) s h).
    exists (cst_e (eval x s)).
    apply (wp_assigns_sepcon l0 (e |~> cst_e (eval x s)) (e |~> cst_e (eval x s) -* wp_assign v (cst_e (eval x s)) (wpAssrt_interp A))).
    simpl in H0.
    case_sepcon H0.
    Compose_sepcon h1 h2.
    apply wp_assigns_mapsto.
    Mapsto.
    by rewrite subst_e_lst_cst_e.
    apply wp_assigns_sepimp.
    rewrite /imp; move=> h' [H8 H9] h'' H7.
    move/wp_assigns_mapsto_inv : H9 => H5.
    have ? : h' = h1.
      eapply singl_equal.
      apply H5.
      apply H0_h1.
      reflexivity.
      by rewrite subst_e_lst_cst_e.
    subst h'.
    have -> : h'' = h by map_tac_m.Equal.
    rewrite /wp_assign /=.
    move: (wp_assigns' _ _ _ _ _ _ H) => H10.
    rewrite /wp_assign in H10.
    apply intro_fresh_var with (max (max (var_max_lst l0) (var_max_wpAssrt A)) v + 1) => //.
    rewrite /fresh_lst.
    have H11 : var_max_lst l0 <= max (max (var_max_lst l0) (var_max_wpAssrt A)) v by Resolve_le_max.
    ssromega.
    rewrite /fresh_wpAssrt.
    have H11 : var_max_wpAssrt A <= max (max (var_max_lst l0) (var_max_wpAssrt A)) v by Resolve_le_max.
    ssromega.
    rewrite /fresh_e /= /max_lst /max_list /=.
    assert (v <= max (max (var_max_lst l0) (var_max_wpAssrt A)) v) by Resolve_le_max.
    ssromega.
  + (* wpMutation *)
    rewrite /= in H.
    rewrite /while.entails => s h H1.
    case: H => H; subst l.
    simpl in H0.
    have H : (pi, sig, wpMutation (subst_e_lst l0 e) (subst_e_lst l0 e0) (wpSubst l0 A)) = (pi, sig, wpMutation (subst_e_lst l0 e) (subst_e_lst l0 e0) (wpSubst l0 A)) \/ False.
      tauto.
    move: {H0 H}(H0 _ _ _ H s h H1) => H.
    simpl in H.
    case: H => x H0.
    case_sepcon H0.
    apply (wp_assigns_exists l0
      (fun e1 s h => (e |~> e1 ** (e |~> e0 -* wpAssrt_interp A)) s h)).
    exists (cst_e (eval x s)).
    apply (wp_assigns_sepcon l0 (e |~> cst_e (eval x s)) (e |~> e0 -* wpAssrt_interp A)).
    Compose_sepcon h1 h2.
    apply wp_assigns_mapsto.
    Mapsto.
    by rewrite subst_e_lst_cst_e.
    apply wp_assigns_sepimp.
    rewrite /imp => h' [H6 H7] h'' H5.
    eapply H0_h2.
    split.
    apply H6.
    by apply (wp_assigns_mapsto_inv _ _ _ _ _ H7).
    done.
  + (* wpIf *)
    simpl in H.
    rewrite /while.entails; injection H; intros; subst l; clear H.
    simpl in H0.
    have H : (pi, sig,wpIf (subst_b_lst l0 e) (wpSubst l0 A1) (wpSubst l0 A2)) = (pi, sig,wpIf (subst_b_lst l0 e) (wpSubst l0 A1) (wpSubst l0 A2)) \/ False.
      by left.
    generalize (H0 _ _ _ H s h); clear H H0; intros.
    generalize (H H2); clear H; intros.
    rewrite /= in H *.
    apply (wp_assigns_and l0
      (fun s h => [ e ]b_s -> wpAssrt_interp A1 s h)
      (fun s h => ~~ [ e ]b_s -> wpAssrt_interp A2 s h)).
    case: H => H0 H1; split.
    * apply (wp_assigns_imp l0 (fun s h => [ e ]b_s) (fun s h => wpAssrt_interp A1 s h)) => H.
      generalize (H0 (wp_assigns_subst_b_lst true _ _ _ _ H)); intros.
      eapply entails_wp_assigns; last by apply H3.
      by rewrite /while.entails.
    apply (wp_assigns_imp l0 (fun s h => ~~ [ e ]b_s) (fun s h => wpAssrt_interp A2 s h)) => H.
    generalize (H1 (wp_assigns_subst_b_lst false _ _ _ _ H)); intros.
    eapply entails_wp_assigns; last by apply H3.
    by rewrite /while.entails.
- (* wpLookup *)
  rename s into v.
  rewrite /while.entails => s h H1.
  rewrite /= in H H1 *.
  have [H3|[x H2]] : Sigma_get_cell_val e sig pi = None \/ exists v, Sigma_get_cell_val e sig pi = Some v.
    destruct (Sigma_get_cell_val e sig pi).
    right; by exists e0.
    by left.
  + by rewrite H3 in H.
  + rewrite H2 in H.
    case: H => ?; subst l.
    have H : (pi, sig, wpSubst ((v, x) :: nil) A) = (pi, sig, wpSubst ((v, x) :: nil) A) \/ False.
      tauto.
    move: {H H0}(H0 _ _ _ H _ _ H1) => H.
    move: (Sigma_get_cell_val_correct _ _ _ _ H2 _ _ (proj1 H1) (proj2 H1)) => /= H0.
    exists x; by apply mapsto_strictly_exact.
- (* wpMutation *) rewrite /while.entails; intros.
  simpl in H.
  have [H3|[x H2]] : Sigma_elt_term_extract' (cell e) sig pi = None \/
      exists v, Sigma_elt_term_extract' (cell e) sig pi = Some v.
    destruct (Sigma_elt_term_extract' (cell e) sig pi).
    right; by exists s0.
    by left.
  by rewrite H3 in H.
  rewrite H2 in H.
  case: H => ?; subst l.
  simpl in H0.
  simpl in H1.
  move: {H0}(H0 _ _ _ (or_introl False (refl_equal (pi, star (singl e e0) x, A)))) => H.
  simpl.
  move: (Sigma_elt_term_extract'_correct _ _ _ _ H2 _ _ (proj1 H1) (proj2 H1)) => H0.
  simpl in H0.
  case_sepcon H0.
  case: H0_h1 => x0 H0.
  exists (cst_e x0).
  Compose_sepcon h1 h2.
  exact H0.
  rewrite /imp => h' [H8 H9] h'' H7.
  apply H.
  split; first by case: H1.
  simpl.
  by Compose_sepcon h' h2.
- (* wpIf *) rewrite /while.entails => s h /= [H2 H3].
  rewrite /= in H; case: H => ?; subst l.
  rewrite /= in H0 *.
  split=> H; eapply H0.
  - left; by intuition.
    split; [ by omegab | done].
  - right; left; by intuition.
    split; [ by omegab | done].
Qed.

Transparent frag_decision.

Lemma LWP_list_correct : forall l l', LWP_list l = Some l' ->
  (forall pi sig A, List.In ((pi, sig), A) l' ->
    assrt_interp (pi, sig) ===> wpAssrt_interp A) ->
  forall pi sig A, List.In ((pi, sig), A) l -> assrt_interp (pi, sig) ===> wpAssrt_interp A.
Proof.
rewrite /while.entails.
induction l.
- simpl; intros.
  contradiction.
- destruct a as [p w].
  destruct p as [p s].
  simpl; intros.
  have [H4 | [x H3]] : LWP_step p s w = None \/ exists v, LWP_step p s w = Some v.
    destruct (LWP_step p s w). right; by exists l0. by left.
  + by rewrite H4 in H.
  +   rewrite H3 in H.
    have [H5 | [x0 H4]] : LWP_list l = None \/ exists v, LWP_list l = Some v.
      destruct (LWP_list l).
      right; by exists l0.
      by left.
    * rewrite H5 in H; discriminate.
    * rewrite H4 in H.
      case : H => ?; subst l'.
      case : H1 => H.
      + case : H => ? ? ?; subst p s A.
        eapply LWP_step_correct.
        by apply H3.
        rewrite /while.entails; intros.
        apply (H0 pi' sig') => //.
        apply List.in_or_app; by left.
        done.
      + eapply (IHl x0 H4).
        rewrite /assrt_interp.
        intros.
        apply (H0 pi0 sig0) => //.
        apply List.in_or_app; by right.
        by apply H.
        exact H2.
Qed.

Lemma LWP_list_rec_correct : forall a l l',
  LWP_list_rec l a = Some l' ->
  (forall pi sig A, List.In ((pi, sig), A) l' -> assrt_interp (pi, sig) ===> wpAssrt_interp A) ->
  forall pi sig A, List.In ((pi, sig), A) l -> assrt_interp (pi, sig) ===> wpAssrt_interp A.
Proof.
rewrite /while.entails.
induction a.
- move=> /= l l' [H] H0 pi sig A H1 s h H2; subst l'.
  eapply H0.
  by apply H1.
  exact H2.
- move=> /= l l' H H0 pi sig A H1 s h H2.
  have [H4 | [x H3]] : LWP_list l = None \/ exists v, LWP_list l = Some v.
    destruct (LWP_list l).
    right; exists l0; auto.
    by left.
  + by rewrite H4 in H.
  + rewrite H3 in H.
    eapply LWP_list_correct.
    by apply H3.
    rewrite /while.entails => pi0 sig0 A0 H4 s0 h0 H5.
    eapply (IHa _ _ H).
    move=> pi1 sig1 A1 H6 s1 h1 H7.
    apply (H0 pi1 sig1) => //.
    by apply H4.
    assumption.
    by apply H1.
    assumption.
Qed.

Lemma frag_hoare_correct : forall P Q c,
  frag_hoare P Q c -> {{ assrt_interp P }} c {{ assrt_interp Q }}.
Proof.
move=> P Q c H.
unfold frag_hoare in H.
have [H1 | H1] : wp_frag (Some (wpElt Q)) c = None \/ exists L, wp_frag (Some (wpElt Q)) c = Some L.
  destruct (wp_frag (Some (wpElt Q)) c).
  right; exists w; auto.
  left; auto.
- by rewrite H1 in H.
- case: H1 => x H0.
  rewrite (_ : assrt_interp Q = wpAssrt_interp (wpElt Q)) //.
  eapply hoare_prop_m.hoare_stren; [idtac | eapply wp_frag_soudness; apply H0]; auto.
  rewrite H0 in H.
  destruct P as [p s].
  have [H2 | H2] :
    LWP_list_rec ((p, s, x) :: nil) (wpAssrt_size x) = None \/
    exists v, LWP_list_rec ((p, s, x) :: nil) (wpAssrt_size x) = Some v.
    destruct (LWP_list_rec ((p, s, x) :: nil) (wpAssrt_size x)).
    right; by exists l.
    by left.
  + by rewrite H2 in H.
  + case: H2 => x0 H1.
    rewrite H1 in H.
    destruct x0 => // s0 h H2.
    eapply (LWP_list_rec_correct _ _ _ H1).
    move=> pi sig A H3.
    by rewrite /= in H2.
    by intuition.
    assumption.
Qed.

(*Recursive Extraction frag_hoare.*)

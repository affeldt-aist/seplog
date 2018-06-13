(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import Init_ext ZArith_ext seq_ext ssrnat_ext order finmap.
Require while.
Require Import bipl integral_type.

Module Seplog (A : IntegralType).

Module Import assert_m := Assert A.
Import assert_m.expr_m.

(** Syntax of the langage *)

Inductive cmd0 : Type :=
| skip : cmd0
| assign : var.v -> expr -> cmd0
| lookup : var.v -> expr -> cmd0
| mutation : expr -> expr -> cmd0
| malloc : var.v -> expr -> cmd0
| free : expr -> cmd0.

Notation "x <- e" := (assign x e) (at level 80) : seplog_cmd_scope.
Notation "x '<-*' e" := (lookup x e) (at level 80) : seplog_cmd_scope.
Notation "e '*<-' f" := (mutation e f) (at level 80) : seplog_cmd_scope.
Notation "x '<-malloc' e" := (malloc x e) (at level 80) : seplog_cmd_scope.
Local Open Scope seplog_cmd_scope.

(** states *)

Local Open Scope heap_scope.

Definition state := (store.t * heap.t)%type.

(** Operational semantics *)

Local Open Scope seplog_expr_scope.

(** NB: in exec0_malloc, the choice of address is indeterminate *)
Reserved Notation " s '--' c '---->' t " (at level 74, no associativity).
Inductive exec0 : option state -> cmd0 -> option state -> Prop :=
| exec0_skip:  forall s, |_ s _| -- skip ----> |_ s _|
| exec0_assign : forall s h x e,
  |_ s, h _| -- x <- e ----> |_ store.upd x ([ e ]e_ s) s, h _|
| exec0_lookup : forall s h x e (v : A.t),
  heap.get ([ e ]e_ s) h = |_ v _|->
  |_ s, h _| -- x <-* e ----> |_ store.upd x v s, h _|
| exec0_lookup_err : forall s h x e,
  heap.get ([ e ]e_s) h = None ->
  |_ s, h _| -- x <-* e ----> None
| exec0_mutation : forall s h e e' p v,
  [ e ]e_ s = p -> heap.get p h = |_ v _| ->
  |_ s, h _| -- e *<- e' ----> |_ s, heap.upd p ([ e' ]e_s) h _|
| exec0_mutation_err : forall s h e e' p,
  ([ e ]e_s) = p -> heap.get p h = None ->
  |_ s, h _| -- e *<- e' ----> None
| exec0_malloc : forall s h x e n,
  h # heap.sing n ([ e ]e_s) ->
  |_ s, h _| -- x <-malloc e ----> |_ store.upd x n s, h \U heap.sing n ([ e ]e_s) _|
| exec0_free : forall s h e v p,
  [ e ]e_s = p -> heap.get p h = |_ v _| ->
  |_ s, h _| -- free e ----> |_ s, h \d\ p _|
| exec0_free_err : forall s h e p,
  [ e ]e_s = p -> heap.get p h = None ->
  |_ s, h _| -- free e ----> None
where "s -- c ----> t" := (exec0 s c t) : seplog_cmd_scope.

(** inversion lemmas *)

Lemma from_none0 : forall s (c : cmd0), None -- c ----> s -> s = None.
Proof. by inversion 1. Qed.

Lemma exec0_assign_inv s h x e s' h' : |_ s, h _| -- x <- e ----> |_ s', h' _| ->
  h = h' /\ s' = store.upd x ([ e ]e_s) s.
Proof. by inversion 1. Qed.

Lemma exec0_lookup_not_None s h v e : ~ |_ s, h _| -- v <-* e ----> None ->
  exists p, [ e ]e_s = p /\ exists z, heap.get p h = |_ z _|.
Proof.
move=> H.
have [ // | [x [x0 H1]] ] : |_ s, h _| -- v <-* e ----> None \/
    exists s' h', |_ s, h _| -- v <-* e ----> |_ s', h' _|.
  have [H1| [x0 H0]] : heap.get ([ e ]e_s) h = None \/ exists z, heap.get ([ e ]e_s) h = |_ z _|.
    destruct (heap.get ([ e ]e_ s) h); intuition.
    right; exists s0; auto.
  - left. by eapply exec0_lookup_err; eauto.
  - right. exists (store.upd v x0 s); exists h.
    by eapply exec0_lookup; eauto.
inversion_clear H1.
exists ([ e ]e_ s); split => //. by exists v0.
Qed.

Module A_prop_m := IntegralType_Prop A.

Lemma cmd0_terminate : forall (c : cmd0) s, exists s', |_ s _| -- c ----> s'.
Proof.
elim=> //.
- move=> s; exists (Some s); apply exec0_skip.
- move=> v e [s h]; eapply ex_intro; by econstructor.
- move=> v e [s h].
  case: (Classical_Prop.classic (exists z, heap.get [ e ]e_ s h = Some z)).
  + case=> z Hz; eapply ex_intro; by econstructor; eauto.
  + move=> X; exists None.
    constructor.
    move: X; case: (heap.get _ _) => //; move=> {v e s h}.
    move=> s Hs; exfalso.
    apply Hs; eapply ex_intro; reflexivity.
- move=> v e [s h].
  case: (Classical_Prop.classic (exists z, heap.get [ v ]e_ s h = Some z)).
  + case=> z Hz; eapply ex_intro; by econstructor; eauto.
  + move=> X; exists None.
    eapply exec0_mutation_err; first by reflexivity.
    move: X; case: (heap.get _ _) => //; move=> {v e s h}.
    move=> s Hs; exfalso.
    apply Hs; eapply ex_intro; reflexivity.
- move=> v e [s h].
  have [n Hn] : exists n, disj (n :: nil) (heap.dom h).
    eapply ex_intro; by apply A_prop_m.my_max_list_disj.
  move: Hn.
  move/disP; move/(heap.disj_sing_R _ _ ([ e ]e_s)) => Hn.
  eapply ex_intro; econstructor; by apply Hn.
- move=> e [s h].
  case: (Classical_Prop.classic (exists z, heap.get [ e ]e_ s h = Some z)).
  - case=> z Hz; eapply ex_intro; by econstructor; eauto.
  - move=> X; exists None.
    eapply exec0_free_err; first by reflexivity.
    move: X; case: (heap.get _ _) => //; move=> {e s h}.
    move=> s Hs; exfalso.
    apply Hs; eapply ex_intro; reflexivity.
Qed.

Lemma exec0_mutation_not_None s h e e0 : ~ Some (s, h) -- e *<- e0 ----> None ->
  exists p, [ e ]e_s = p /\ exists z : heap.v, heap.get p h = Some z.
Proof.
move=> H.
have [// | [x [x0 H0]]] : |_ s, h _| -- e *<- e0 ----> None \/
    exists s' h', |_ s, h _| -- e *<- e0 ----> |_ s', h' _|.
  have [H1| [x H0]] : heap.get ([ e ]e_ s) h = None \/ exists z, heap.get ([ e ]e_ s) h = |_ z _|.
    destruct heap.get; by [auto | right; exists s0].
  - left. by eapply exec0_mutation_err; eauto.
  - right. exists s; exists (heap.upd ([ e ]e_ s) ([ e0 ]e_ s) h).
    by eapply exec0_mutation; eauto.
inversion_clear H0.
exists p; split; [assumption | by exists v].
Qed.

Lemma exec0_free_not_None s h e : ~ |_ s, h _| -- free e ----> None ->
  exists p, [ e ]e_s = p /\ exists z, heap.get p h = |_ z _|.
Proof.
move=> H.
have [// | [x [x0 H0]]] : |_ s, h _| -- free e ----> None \/ 
    exists s' h', |_ s, h _| -- free e ----> |_ s', h' _|.
  have [H1|[x H0]] : heap.get ([ e ]e_s) h = None \/ exists z, heap.get ([ e ]e_s) h = |_ z _|.
    destruct heap.get; by [ right; exists s0 | left ].
  - left. by eapply exec0_free_err; eauto.
  - right. exists s, (h \d\ [ e ]e_s). by eapply exec0_free; eauto.
inversion_clear H0.
exists p; split => //; by exists v.
Qed.

Module semop_m <: while.WHILE_SEMOP.

Definition store : Type := store.t.
Definition heap : Type := heap.t.
Definition state : Type := (store * heap)%type.

Definition cmd0 : Type := cmd0.
Definition exec0 : option state -> cmd0 -> option state -> Prop := exec0.
(*Notation "s -- c ----> t" := (exec0 s c t) (at level 74 , no associativity) : seplog_cmd_scope.*)
(*Local Open Scope goto_cmd_scope.*)

Definition from_none0 : forall s c, None -- c ----> s -> s = None := from_none0.
Definition cmd0_terminate : forall (c : cmd0) s, exists s', |_ s _| -- c ----> s' := cmd0_terminate.

Definition expr_b : Type := expr_b.
Definition neg : expr_b -> expr_b := neg_b.
Definition eval_b : expr_b -> state -> bool := fun e s => [ e ]b_ (fst s).
Lemma eval_b_neg : forall t s, eval_b (neg t) s = ~~ eval_b t s.
Proof. move=> t [s h]; rewrite /eval_b /=; by apply eval_b_neg. Qed.
Definition cmd := @while.cmd cmd0 expr_b.
Coercion cmd_cmd0_coercion := @while.cmd_cmd0 cmd0 expr_b.
Definition exec : option state -> cmd -> option state -> Prop :=
  @while.exec store heap cmd0 exec0 expr_b (fun eb s => eval_b eb s).

End semop_m.

Notation "c ; d" := (while.seq c d) (at level 81, right associativity) : seplog_cmd_scope.
Notation "'If' e 'Then' c1 'Else' c2" := (while.ifte e c1 c2)
  (at level 200, right associativity, format
"'[v' '[' 'If'  e  'Then' ']' '//'   '[' c1 ']' '//' '[' 'Else' ']' '//'   '[' c2 ']' '//' ']'") : seplog_cmd_scope.
Notation "'While' e '{{' c '}}' " := (while.while e c)
  (at level 200, format
"'[v' 'While'  e  '{{' '//'   '[' c ']' '//' '}}' ']'") : seplog_cmd_scope.
Notation "s -- c ---> t" := (while.exec store.t heap.t cmd0 exec0 expr_b
  (fun e st => [ e ]b_(fst st)) s c t) (at level 74) : seplog_cmd_scope.

Module semop_prop_m := while.While_Semop_Prop semop_m.

(** Separation logic *)

Definition wp_assign x e P : assert := fun s h => P (store.upd x ([ e ]e_ s) s) h.

Fixpoint wp_assigns (l : seq (var.v * expr)) (P : assert) {struct l} : assert :=
  match l with
    | nil => P
    | (x, e) :: tl => wp_assigns tl (wp_assign x e P)
  end.

Lemma wp_assigns_app : forall l2 l1 P s h,
  wp_assigns (l2 ++ l1) P s h -> wp_assigns l1 (wp_assigns l2 P) s h.
Proof. elim=> [//| [a b] l IH /= l1 P s h]; by move/IH. Qed.

Lemma wp_assigns' l x v s h P :
  wp_assigns (l ++ (x, v) :: nil) P s h -> wp_assign x v (wp_assigns l P) s h.
Proof. by move/wp_assigns_app. Qed.

(** relations between "wp_assigns" and logical connectives
  (entailment, /\, ->, exists, sepcon, sepimp, mapsto) *)

Local Open Scope seplog_assert_scope.

Lemma entails_wp_assigns: forall l P1 P2 s h, P1 ===> P2 ->
  wp_assigns l P1 s h -> wp_assigns l P2 s h.
Proof.
elim => [P1 P2 s h | [v e] l IH P1 P2 s h P1_P2 /=].
by apply.
apply IH => s0 h0; by apply P1_P2.
Qed.

Lemma wp_assigns_imp : forall l P1 P2 s h,
  (wp_assigns l P1 s h -> wp_assigns l P2 s h) ->
  wp_assigns l (fun s h => P1 s h -> P2 s h) s h.
Proof. elim=> [// | [a b] /= tl IH P1 P2 s h]; by move/IH. Qed.

Lemma wp_assigns_and_inv : forall l P1 P2 s h,
  wp_assigns l (fun s h => P1 s h /\ P2 s h) s h ->
  wp_assigns l P1 s h /\ wp_assigns l P2 s h.
Proof. elim=> [//| [a b] tl IH /= P1 P2 s h]; by move/IH. Qed.

Lemma wp_assigns_and : forall l P1 P2 s h,
  wp_assigns l P1 s h /\ wp_assigns l P2 s h ->
  wp_assigns l (fun s h => P1 s h /\ P2 s h) s h.
Proof. elim=> [//|[a b] tl IH P1 P2 s h]; by move/IH. Qed.

Lemma wp_assigns_exists : forall l (P: expr -> assert) s h,
  (exists x0, (wp_assigns l (P x0)) s h) ->
  wp_assigns l (fun s h => exists e0, P e0 s h) s h.
Proof. elim=> [//|[a b] tl IH /= P s h]; by move/IH. Qed.

Lemma wp_assigns_sepcon : forall l P1 P2 s h,
  ((fun s h => wp_assigns l P1 s h) ** (fun s h => wp_assigns l P2 s h)) s h ->
  wp_assigns l (P1 ** P2) s h.
Proof.
elim=> [// | [v e] l IH P1 P2 s h /=]; move/IH.
apply entails_wp_assigns => s0 h0 H.
case_sepcon H.
Compose_sepcon h01 h02; by [apply H_h01 | apply H_h02].
Qed.

Lemma wp_assigns_sepimp : forall l P1 P2 s h,
  ((fun s h => wp_assigns l P1 s h) -* (fun s h => wp_assigns l P2 s h)) s h ->
  wp_assigns l (P1 -* P2) s h.
Proof.
elim=> [// | [v e] l IH P1 P2 s h /=]; move/IH.
apply entails_wp_assigns => s0 h0 H0.
rewrite /imp => h' [h0_h' Hp1] h'' Hh''; by apply (H0 h').
Qed.

Lemma wp_assigns_mapsto : forall l e1 e2 s h,
  (subst_e_lst l e1 |~> subst_e_lst l e2) s h -> wp_assigns l (e1 |~> e2) s h.
Proof.
elim=> [// | [a b] tl IH /= e1 e2 s h]; move/IH.
apply (entails_wp_assigns _ (subst_e e1 (var_e a) b |~> subst_e e2 (var_e a) b)).
rewrite /while.entails /= => s0 h0 H0.
case: H0 => x [Hx Hh0].
exists x; split; by rewrite eval_upd_subst.
Qed.

Lemma wp_assigns_mapsto_inv : forall l e1 e2 s h,
  wp_assigns l (e1 |~> e2) s h -> (subst_e_lst l e1 |~> subst_e_lst l e2) s h.
Proof.
elim=> [// | [a b] tl IH e1 e2 s h /=].
have -> : wp_assign a b (e1 |~> e2) =
          (subst_e e1 (var_e a) b |~> subst_e e2 (var_e a) b).
  apply assert_m.assert_ext => s0 h0; split => H.
  - case: H => [x [H H1]].
    exists x; split; by rewrite -eval_upd_subst.
  - case : H => x [H H1].
    exists x; split; by rewrite eval_upd_subst.
by move/IH.
Qed.

Lemma wp_assigns_subst_b_lst : forall (b : bool) l e s h,
  wp_assigns l (fun s h => if b then [ e ]b_ s else ~~ [ e ]b_ s) s h ->
  (if b then [ subst_b_lst l e ]b_ s else ~~ [ subst_b_lst l e ]b_ s).
Proof.
move => bo.
elim => [ | [a b] tl IH e s h /= H].
  by destruct bo.
apply (IH _ _ h).
rewrite /wp_assign in H.
induction bo.
- rewrite (_ :
  (fun s0 (_ : heap.t) => [ subst_b e (var_e a) b ]b_ s0 = true) =
  fun s _ => [ e ]b_(store.upd a ([ b ]e_s) s)) //.
  apply assert_m.assert_ext => s0 h0; split => H0.
  by rewrite eval_b_upd_subst.
  by rewrite -eval_b_upd_subst.
- rewrite (_ :
  (fun s0 (_ : assert_m.heap.t) => ~~ ([ subst_b e (var_e a) b ]b_s0) = true) =
  (fun s _ => ~~ [ e ]b_(store.upd a ([ b ]e_s) s))) //.
  apply assert_m.assert_ext => s0 h0; split => H0.
  by rewrite eval_b_upd_subst.
  by rewrite -eval_b_upd_subst.
Qed.

Lemma wp_assigns_lookup : forall l e1 e2 s h P,
  (exists e0, 
    ((subst_e_lst l e1 |~> e0) ** 
      (subst_e_lst l e1 |~> subst_e_lst l e2 -* wp_assigns l P)) s h) ->
  wp_assigns l (fun s' h' => exists e0, (e1 |~> e0 ** (e1 |~> e2 -* P)) s' h') s h.
Proof.
elim=> [// | [a b] tl IH e1 e2 s h P /= H].
rewrite /wp_assign in H *.
move/IH : H => H.
apply entails_wp_assigns with (P1 := fun s0 h0 =>
  exists e0,
    (subst_e e1 (var_e a) b |~> e0 **
      (subst_e e1 (var_e a) b |~> subst_e e2 (var_e a) b -*
        (fun s h =>
          P (store.upd a ([ b ]e_ s) s) h))) s0 h0); last by done.
rewrite /while.entails /= => s0 h0 [x H1].
case_sepcon H1.
case: (abstract_subst_e x a b s0) => x0 H1.
exists x0; Compose_sepcon h01 h02.
- case : H1_h01 => x1 [H2 H3].
  exists x1; split.
  by rewrite eval_upd_subst.
  rewrite -eval_upd_subst in H1; by rewrite -H1.
- move=> h01' [X1 X2] h' Hh'.
  red in H1_h02.
  have H0 : (subst_e e1 (var_e a) b |~> subst_e e2 (var_e a) b) s0 h01'.
    case : X2 => x1 [H2 H3].
    exists x1; split; by rewrite -eval_upd_subst.
  by apply (H1_h02 h01' (conj X1 H0) _ Hh').
Qed.

Lemma fresh_lst_inde : forall l P x, inde (x :: nil) P -> fresh_lst x l ->
  inde (x :: nil) (wp_assigns l P).
Proof.
elim=> [//| [a b] l IHl P x H H0].
rewrite /inde /= => s h x0 v //; rewrite mem_seq1 => /eqP ?; subst x0; split=> H2.
- have H3 : inde (x :: nil) (wp_assign a b P).
    rewrite /inde /=; move=> s0 h0 x0 v0 //; rewrite mem_seq1 => /eqP ?; subst x0; split=> H3.
    + rewrite /wp_assign in H3 *.
      rewrite fresh_e_eval; last by maxinf_resolve.
      rewrite store.upd_upd; last first.
        apply/eqP; by maxinf_resolve.
      have : x \in x :: nil by rewrite mem_seq1.
      case/(H (store.upd a ([ b ]e_ s0) s0) h0 x v0) => ? ?; tauto.
    + rewrite /wp_assign in H3 *.
      rewrite fresh_e_eval in H3; last by maxinf_resolve.
      rewrite store.upd_upd in H3; last first.
        apply/eqP; by maxinf_resolve.
      have : x \in x :: nil by rewrite mem_seq1.
      case/(H (store.upd a ([ b ]e_ s0) s0) h0 x v0) => ? ?; tauto.
  have H4 : (x > var_max_lst l)%nat by maxinf_resolve.
  have : x \in x :: nil by rewrite mem_seq1.
  case/(IHl _ _ H3 H4 s h x v) => ? ?; tauto.
- have H1 : inde (x :: nil) (wp_assign a b P).
    rewrite /inde /=; move=> s0 h0 x0 v0 //; rewrite mem_seq1 => /eqP ?; subst x0; split=> H3.
    + rewrite /wp_assign in H3 *.
      rewrite fresh_e_eval; last by maxinf_resolve.
      rewrite store.upd_upd; last first.
          apply/eqP; by maxinf_resolve.
      have : x \in x :: nil by rewrite mem_seq1.
      case/(H (store.upd a ([ b ]e_ s0) s0) h0 x v0) => ? ?; tauto.
    + rewrite /wp_assign in H3 *.
      rewrite fresh_e_eval in H3; last by maxinf_resolve.
      rewrite store.upd_upd in H3; last first.
        apply/eqP; by maxinf_resolve.
      have : x \in x :: nil by rewrite mem_seq1.
      case/(H (store.upd a ([ b ]e_ s0) s0) h0 x v0) => ? ?; tauto.
  have H3 : (x > var_max_lst l)%nat by maxinf_resolve.
  have : x \in x :: nil by rewrite mem_seq1.
  case/(IHl _ _ H1 H3 s h x v) => ? ?; tauto.
Qed.

Lemma wp_assigns_fresh : forall l x' e s h P, fresh_lst x' l ->
   wp_assigns l P (store.upd x' ([ e ]e_ s) s) h ->
   wp_assigns l (fun s' h' => P (store.upd x' ([ e ]e_ s) s') h') s h.
Proof.
elim=> [// | [a b] /= tl IH x' e s h P H H0].
rewrite /wp_assign in H0 *.
apply entails_wp_assigns with
  (fun s' h' => (wp_assign a b P) (store.upd x' ([ e ]e_ s) s') h').
- rewrite /while.entails => s0 h0 H1.
  unfold wp_assign in H1.
  rewrite store.upd_upd; last first.
    by maxinf_resolve.
  suff : [ b ]e_ (store.upd x' ([ e ]e_ s) s0) = [ b ]e_ s0 by move=> <-.
    rewrite fresh_e_eval //.
    by maxinf_resolve.
- apply IH.
  by move/fresh_lst_inv : H => [_ [_ H]].
  move: H0; by apply entails_wp_assigns.
Qed.

Lemma wp_assigns_fresh' : forall l x' e s h P, fresh_lst x' l ->
  wp_assigns l (fun s' h' => P (store.upd x' ([ e ]e_s) s') h') s h ->
  wp_assigns l P (store.upd x' ([ e ]e_s) s) h.
Proof.
induction l => //.
induction a; simpl; intros.
rewrite /wp_assign in H0 *.
apply entails_wp_assigns with (wp_assign a b P); first by done.
- apply IHl.
  by move/fresh_lst_inv : H => [_ [_ H]].
- move: H0; apply entails_wp_assigns => s0 h0.
  rewrite /wp_assign /= => H0.
  rewrite store.upd_upd; last first.
    by maxinf_resolve.
  rewrite fresh_e_eval //.
  by maxinf_resolve.
Qed.

Lemma intro_fresh_var' l x x' e s h P :
  fresh_lst x' l -> fresh_e x' (var_e x) -> inde (x' :: nil) P ->
  wp_assigns l
  (fun s' h' => P (store.upd x ([ var_e x' ]e_ s') s') h') (store.upd x' ([ e ]e_ s) s) h ->
  wp_assigns l (fun s' h' => P (store.upd x ([ e ]e_ s) s') h') s h.
Proof.
move=> H H0 H1 H2.
apply entails_wp_assigns with
  (fun s0 h0 => P (store.upd x ([ e ]e_s) (store.upd x' ([ e ]e_s) s0)) h0).
- rewrite /while.entails => s0 h0 H3.
  rewrite store.upd_upd in H3; last first.
    by maxinf_resolve.
  have : x' \in x' :: nil by rewrite mem_seq1.
  case/(H1 (store.upd x ([ e ]e_s) s0) h0 _ ([ e ]e_s)) => _.
  exact.
- move: {H2}(wp_assigns_fresh _ _ _ _ _ _ H H2) => /= H2.
  move: H2; apply entails_wp_assigns => s0 h0.
  by rewrite store.get_upd'.
Qed.

Definition wp_lookup x e P : assert := fun s h =>
  exists z, heap.get ([ e ]e_s) h = Some z /\ P (store.upd x z s) h.

Definition wp_mutation e e' P : assert := fun s h =>
  exists z, heap.get ([ e ]e_s) h = Some z /\ P s (heap.upd ([ e ]e_s) ([ e' ]e_s) h).

Inductive hoare0 : assert -> cmd0 -> assert -> Prop :=
| hoare0_skip: forall P, hoare0 P skip P
| hoare0_assign : forall P x e, hoare0 (wp_assign x e P) (x <- e) P
| hoare0_lookup : forall P x e, hoare0 (wp_lookup x e P) (x <-* e) P
| hoare0_mutation : forall P e e', hoare0 (wp_mutation e e' P) (e *<- e') P
| hoare0_malloc : forall P x e,
  hoare0 (fun s h => forall n, (cst_e n |~> e -* wp_assign x (cst_e n) P) s h)
  (x <-malloc e) P
| hoare0_free : forall P e,
  hoare0 (fun s h => exists v, heap.get ([ e ]e_s) h = Some v /\ P s (h \d\ [ e ]e_s))
  (free e) P.

Definition wp_malloc x e Q :=
  fun s h => forall n, (cst_e n |~> e -* wp_assign x (cst_e n) Q) s h.

Definition wp_free e Q :=
  fun s h => exists v, heap.get ([ e ]e_s) h = Some v /\ Q s (h \d\ [ e ]e_s).

Definition wp0 (c : cmd0) (Q : assert) : assert :=
match c with
  | skip => Q
  | assign x e => wp_assign x e Q
  | lookup x e => wp_lookup x e Q
  | mutation e1 e2 => wp_mutation e1 e2 Q
  | malloc x e => wp_malloc x e Q
  | free e => wp_free e Q
end.

Lemma wp0_no_err s h c P : wp0 c P s h -> ~ (Some (s,h) -- c ----> None).
Proof.
move=> Hwp0 Hexec; inversion Hexec; subst.
- rewrite /= /wp_lookup in Hwp0.
  case: Hwp0 => z [Hz HP].
  by rewrite H2 in Hz.
- rewrite /= /wp_mutation in Hwp0.
  case: Hwp0 => z [Hz HP].
  by rewrite H3 in Hz.
- rewrite /= /wp_free in Hwp0.
  case: Hwp0 => z [Hz HP].
  by rewrite H3 in Hz.
Qed.

Lemma exec0_from_wp0 ST (c : cmd0) ST' : ST -- c ----> ST' ->
  forall P s h s' h', ST = Some (s, h) -> ST' = Some (s', h') ->
    wp0 c P s h -> P s' h'.
Proof.
elim => //; clear ST c ST'.
- move=> s P s1 h s' h' [] ?; subst s; case=> ? ?; by subst s' h'.
- move=> s h x e P s1 h1 s' h'; case=> ? ?; subst s1 h1; case=> ? ?; by subst s' h'.
- move=> s h x e z Hz P s1 h1 s' h'; case=> ? ?; subst s1 h1; case=> ? ?; subst s' h.
  rewrite /= /wp_lookup; case=> z' [Hz' HP].
  suff : z = z' by move=> ->.
  by rewrite Hz in Hz'; case: Hz'.
- move=> s h e e' p v Hp Hv P s1 h1 s' h' [] ? ? [] ? ?; subst s1 h1 s' h'.
  rewrite /= /wp_mutation; case=> z' [Hz' HP].
  by rewrite -Hp.
- move=> s h x e n Hn P s1 h1 s' h' [] ? ? [] ? ?; subst s1 h1 s' h'.
  rewrite /= /wp_malloc => H.
  move: (H n (heap.sing n [ e ]e_ s)).
  apply; last by reflexivity.
  split; first by assumption.
  by exists n.
- move=> s h e v p Hp Hv P s1 h1 s' h' [] ? ? [] ? ?; subst s1 h1 s' h'.
  rewrite /= /wp_free; case=> z [Hz HP].
  by rewrite -Hp.
Qed.

Lemma exec0_to_wp0 ST (c : cmd0) ST' : ST -- c ----> ST' ->
  forall (P : assert) s h s' h', ST = Some (s,h) -> ST' = Some (s',h') ->
    P s' h' -> wp0 c P s h.
Proof.
elim => //; clear ST c ST'.
- move=> s P s1 h1 s' h' [] ?; subst s. case=> ? ?; by subst s1 h1.
- move=> s h x e P s1 h1 s' h' [] ? ? [] ? ?; by subst s1 h1 s' h'.
- move=> s h x e v Hv P s1 h1 s' h' [] ? ? [] ? ? HP /=; subst s1 h1 s' h'.
  rewrite /wp_lookup.
  by exists v.
- move=> s h e e' p v Hp Hv P s1 h1 s' h' [] ? ? [] ? ? HP /=; subst s1 h1 s' h'.
  rewrite /wp_mutation Hp.
  by exists v.
- move=> s h x e n Hn P s1 h1 s' h' [] ? ? [] ? ? HP /=; subst s1 h1 s' h'.
  rewrite /wp_malloc => n'.
  red=> h' [Hh' [p [/= Hp1 Hp2]]] h'' Hh''; subst n'.
  rewrite /wp_assign /= Hh'' Hp2.
Abort.

(* as a consequence

Lemma exec0_wp0 : forall s h (c : cmd0) s' h', Some (s, h) -- c ----> Some (s', h') ->
  forall P, wp0 c P s h <-> P s' h'.
Proof.
move=> s h c s' h' H P; split=> H'.
eapply exec0_from_wp0; [by apply H | reflexivity | reflexivity | exact H'].
eapply exec0_to_wp0; [by apply H | reflexivity | reflexivity | exact H'].
Qed.

cannot be Qeded
*)

(** Definition of the semantics with the operationnal semantics *)

Notation "'hoare_semantics'" := (@while.hoare_semantics store.t heap.t _ exec0 _
(fun eb s => eval_b eb (fst s)))
  : seplog_hoare_scope.

Local Open Scope seplog_hoare_scope.
Delimit Scope seplog_hoare_scope with seplog_hoare.

Lemma soundness0 (P Q : assert) c :
  hoare0 P c Q -> hoare_semantics P (while.cmd_cmd0 c) Q.
Proof.
elim => //; clear P Q c; rewrite /hoare_semantics.
- (* skip *) move=> P s h HP; split=> [| s' h']; move/semop_prop_m.exec_cmd0_inv => abs.
  + by inversion abs.
  + by inversion abs; subst.
- (* assign *) move=> P x e s h HP; split=> [| s' h']; move/semop_prop_m.exec_cmd0_inv => abs.
  + by inversion abs.
  + by inversion abs; subst.
- (* lookup *) move=> P x e s h [z [H2 H3] ]; split=> [| s' h']; move/semop_prop_m.exec_cmd0_inv => abs.
  + inversion abs; subst.
    by rewrite H0 in H2.
  + inversion abs; subst.
    suff : v = z by move=> ->.
    rewrite H0 in H2; by case: H2.
- (* mutation *) move=> P e e' s h [z [H2 H3] ]; split=> [| s' h']; move/semop_prop_m.exec_cmd0_inv => abs.
  + inversion abs; subst.
    by rewrite H6 in H2.
  + inversion abs; by subst.
- (* malloc *) move=> P v e s h H; split=> [| s' h']; move/semop_prop_m.exec_cmd0_inv => abs.
  + by inversion abs.
  + inversion abs; subst.
    rewrite /wp_assign /= in H.
    eapply (H n); eauto.
    split; [exact H1 | by exists n].
- (* free *) move=> P e s h [z [H2 H3]]; split=> [| s' h']; move/semop_prop_m.exec_cmd0_inv => abs.
  + inversion abs; subst.
    by rewrite H5 in H2.
  + inversion abs; by subst.
Qed.

Notation "'wp_semantics'" := (@while.wp_semantics store.t heap.t _ exec0 _
  (fun eb s => eval_b eb (fst s))) : temp_seplog_hoare_scope.

Notation "{{ P }} c {{ Q }}" := (@while.hoare store.t heap.t cmd0 expr_b
  (fun eb s => eval_b eb (fst s)) hoare0 P c Q)
  (at level 82, no associativity) : temp_seplog_hoare_scope.

Local Open Scope temp_seplog_hoare_scope.

Lemma wp_semantics_sound0 : forall (c : cmd0) Q,
  {{ wp_semantics (while.cmd_cmd0 c) Q }} (while.cmd_cmd0 c) {{ Q }}.
Proof.
elim => [Q|v e Q|v e Q|e e0 Q|v e Q|e Q]; match goal with |- {{ ?P }} ?c {{ ?Q }} => eapply while.hoare_conseq with (Q' := Q); [done | idtac | do 3 constructor] end.
- move=> s h [H1 H2].
  apply H2.
  do 2 constructor.
- move=> s h [H1 H2]; rewrite /wp_assign.
  apply H2; do 2 constructor.
- move=> s h [H1 H2]; rewrite /wp_lookup.
  move/semop_prop_m.exec0_not_None_to_exec_not_None : H1 => H1.
  move: {H1}(exec0_lookup_not_None _ _ _ _ H1) => [p [ H1 [ z H1'] ] ].
  exists z; rewrite H1; split; first by done.
  apply H2.
  constructor.
  econstructor; eauto.
  by rewrite H1.
- move=> s h [H1 H2]; rewrite /wp_mutation.
  move/semop_prop_m.exec0_not_None_to_exec_not_None : H1 => H1.
  move: {H1}(exec0_mutation_not_None _ _ _ _ H1) => [p [ H1 [ z H1'] ] ].
  exists z; rewrite H1; split; first by done.
  apply H2; constructor; econstructor; eauto.
- move=> s h [H1 H2] n /=.
  move=> h' [Hdisj [p [Hn Hsing] ] ] h'' Hunion /=.
  subst.
  rewrite /wp_assign /=.
  by apply H2; constructor; econstructor; eauto.
- move=> s h [H1 H2] /=.
  move/semop_prop_m.exec0_not_None_to_exec_not_None : H1 => H1.
  move: {H1}(exec0_free_not_None _ _ _ H1) => [p [ H1 [ z H1'] ] ].
  exists z; rewrite H1; split; first by done.
  by apply H2; constructor; econstructor; eauto.
Qed.

Module hoare_m <: while.WHILE_HOARE.

Include semop_m.

Definition assert := store -> heap -> Prop.

Definition wp0 : cmd0 -> assert -> assert := wp0.
Definition wp0_no_err : forall s h c P,
  wp0 c P s h -> ~ (Some (s,h) -- c ----> None) := wp0_no_err.

Definition hoare0 : assert -> cmd0 -> assert -> Prop := hoare0.
Definition hoare : assert -> cmd -> assert -> Prop :=
  @while.hoare store heap cmd0 _ eval_b hoare0.

Definition soundness0 : forall P Q c, hoare0 P c Q -> hoare_semantics P c Q := soundness0.

Definition wp_semantics_sound0 : forall (c : cmd0) P, {{ wp_semantics c P }} c {{ P }} :=
  wp_semantics_sound0.

End hoare_m.

Local Close Scope temp_seplog_hoare_scope.

Notation "'wp_semantics'" := (@while.wp_semantics store.t heap.t _ exec0 _
  (fun eb s => eval_b eb (fst s))) : seplog_hoare_scope.

Notation "{{ P }} c {{ Q }}" := (while.hoare store.t heap.t cmd0 expr_b
  (fun eb s => eval_b eb (fst s)) hoare0 P c Q)
  (at level 82, no associativity) : seplog_hoare_scope.

Coercion cmd_cmd0_coercion_redefined := @while.cmd_cmd0 cmd0 expr_b.

Module hoare_prop_m := while.While_Hoare_Prop hoare_m.

Lemma hoare_false0 P : forall (c : cmd0), {{ FF }} c {{ P }}.
Proof.
elim => [|v e|v e|e e0|v e| e].
- apply while.hoare_conseq with P P => //.
  by apply while.hoare_hoare0, hoare0_skip.
- apply while.hoare_conseq with (wp_assign v e P) P => //.
  by apply while.hoare_hoare0, hoare0_assign.
- apply while.hoare_conseq with (wp_lookup v e P) P => //.
  by apply while.hoare_hoare0, hoare0_lookup.
- apply while.hoare_conseq with (wp_mutation e e0 P) P => //.
  by apply while.hoare_hoare0, hoare0_mutation.
- apply while.hoare_conseq with (fun s h => forall n,
    ((cst_e n |~> e) -* wp_assign v (cst_e n) P) s h) P => //.
  by apply while.hoare_hoare0, hoare0_malloc.
- apply while.hoare_conseq with (fun s h =>
    exists v, heap.get ([ e ]e_ s) h = Some v /\
      P s (heap.dif h ([ e ]e_ s))) P => //.
  by apply while.hoare_hoare0, hoare0_free.
Qed.

Lemma hoare_false c P : {{ FF }} c {{ P }}.
Proof. by apply (hoare_prop_m.hoare_false' hoare_false0). Qed.

Lemma soundness : forall P Q c, {{ P }} c {{ Q }} -> hoare_semantics P c Q.
Proof. exact hoare_prop_m.soundness. Qed.

Lemma wp_semantics_sound : forall c Q, {{ wp_semantics c Q }} c {{ Q }}.
Proof. exact hoare_prop_m.wp_semantics_sound. Qed.

Lemma hoare_complete : forall P Q c, hoare_semantics P c Q -> {{ P }} c {{ Q }}.
Proof. exact hoare_prop_m.hoare_complete. Qed.

Definition hoare_alternative (P : assert) (c : while.cmd) (Q : assert) : Prop :=
  forall s h, P s h ->
    forall s' h', Some (s, h) -- c ---> Some (s', h') -> Q s' h'.

Lemma soundness_alternative P Q c : {{ P }} c {{ Q }} -> hoare_alternative P c Q.
Proof.
move/hoare_prop_m.soundness => H.
rewrite /hoare_alternative => s h H0 s' h' H1.
case: (H s h H0) => _; by apply.
Qed.

(** Derived separation logic axioms *)

Lemma hoare_skip' P Q : P ===> Q -> {{ P }} skip {{ Q }}.
Proof.
move=> H; apply (hoare_prop_m.hoare_stren Q) => //.
by apply while.hoare_hoare0, hoare0_skip.
Qed.

Lemma hoare_assign' Q P x e : P ===> wp_assign x e Q -> {{ P }} x <- e {{ Q }}.
Proof.
intros.
apply (hoare_prop_m.hoare_stren (wp_assign x e Q)) => //.
by apply while.hoare_hoare0, hoare0_assign.
Qed.

Lemma hoare_assign R P Q x e c :
  P ===> wp_assign x e R -> {{ R }} c {{ Q }} -> {{ P }} x <- e ; c {{ Q }}.
Proof. intros. apply while.hoare_seq with R => //. by apply hoare_assign'. Qed.

Lemma forward_reasoning x e P :
  inde (x :: nil) P -> ~ x \in vars e ->
  {{ P }} x <- e {{ fun s h => P s h /\ [ var_e x ]e_s = [ e ]e_s }}.
Proof.
move=> H H0.
apply (hoare_prop_m.hoare_stren (fun s h => P s h /\ exists v, [ x ]_s = v)).
- split; first by done.
  eapply ex_intro; reflexivity.
- apply (hoare_prop_m.hoare_stren (wp_assign x e (fun s h => P s h /\ [ var_e x ]e_s = [ e ]e_s ))).
  + split.
    * have : x \in x :: nil by rewrite mem_seq1.
      case/(H s h x ([ e ]e_s)) => H3 _.
      case: H1 => H5 _.
      by apply H3.
    * case: H1 => H2 [x0 H1] /=.
      Store_upd.
      by rewrite eval_upd.
  + exact/while.hoare_hoare0/hoare0_assign.
Qed.

(* TODO: rename *)
Lemma hoare_lookup_simple R e e' x s h :
  ((e |~> e') ** TT) s h ->
  (wp_assign x e' R) s h ->
  exists e0, ((e |~> e0) ** ((e |~> e0) -* (wp_assign x e0 R))) s h.
Proof.
move=> H H0.
case_sepcon H.
exists e'.
Compose_sepcon h1 h2; first by done.
move=> h1' [X1 X2] h' Hh'.
have H : h1' = h1.
  eapply singl_equal; [apply X2 | apply H_h1 | auto | auto].
have H1 : h' = h.
  subst h1'; by map_tac_m.Equal.
by rewrite H1.
Qed.

Lemma hoare_lookup' Q P x e : P ===> wp_lookup x e Q -> {{ P }} x <-* e {{ Q }}.
Proof.
intros.
apply (hoare_prop_m.hoare_stren (wp_lookup x e Q)) => //.
by apply while.hoare_hoare0, hoare0_lookup.
Qed.

Lemma hoare_lookup'' R P Q x e c :
  P ===> wp_lookup x e R -> {{ R }} c {{ Q }} -> {{ P }} x <-* e ; c {{ Q }}.
Proof. intros. apply while.hoare_seq with (Q := R) => //. by apply hoare_lookup'. Qed.

Lemma hoare_lookup_back : forall x e P,
  {{ fun s h => exists e0, (e |~> e0 ** (e |~> e0 -* wp_assign x e0 P)) s h }}
  x <-* e {{ P }}.
Proof.
intros.
apply (hoare_prop_m.hoare_stren (wp_lookup x e P)).
do 3 intro.
case : H => x0 H0.
move: (assert_m.mp _ _ _ _ H0) => H.
rewrite /wp_assign in H.
rewrite /wp_lookup.
case_sepcon H0.
case : H0_h1 => [x1 [Hx1 Hh1]].
exists ([ x0 ]e_ s); split; last by done.
rewrite h1_U_h2.
apply heap.get_union_L => //.
by rewrite Hh1 Hx1 heap.get_sing.
by apply while.hoare_hoare0, hoare0_lookup.
Qed.

Lemma hoare_lookup_back' : forall P Q x e,
  P ===> (fun s h => exists e0, (e |~> e0 ** (e |~> e0 -* wp_assign x e0 Q)) s h) ->
  {{ P }} x <-* e {{ Q }}.
Proof.
intros.
apply (hoare_prop_m.hoare_stren (fun s h => exists f, (e |~> f ** (e |~> f -* wp_assign x f Q)) s h)) => //.
by apply hoare_lookup_back.
Qed.

Lemma hoare_lookup_back'' P Q R x e c : P ===> (fun s h =>
    exists e0, (e |~> e0 ** (e |~> e0 -* wp_assign x e0 R)) s h) ->
  {{ R }} c {{ Q }} -> {{ P }} x <-* e; c {{ Q }}.
Proof.
intros.
apply while.hoare_seq with (Q := R) => //.
apply (hoare_prop_m.hoare_stren (fun s h => exists e0, (e |~> e0 ** (e |~> e0 -* wp_assign x e0 R)) s h)) => //.
by apply hoare_lookup_back.
Qed.

Lemma hoare_lookup_back_alternative : forall x e P e0,
  {{ e |~> e0 ** (e |~> e0 -* wp_assign x e0 P) }} x <-* e {{ P }}.
Proof.
intros.
apply (hoare_prop_m.hoare_stren (fun s h => exists e0, (e |~> e0 ** (e |~> e0 -* wp_assign x e0 P)) s h)).
intros.
by exists e0.
by apply hoare_lookup_back.
Qed.

Lemma hoare_lookup_back_strictly_exact : forall P Q R x e c,
  P ===> (fun s h => exists e0, (e |~> e0 ** TT) s h /\ wp_assign x e0 R s h) ->
  {{ R }} c {{ Q }} -> {{ P }} x <-* e; c {{ Q }}.
Proof.
move=> P Q R x e c H H0.
apply hoare_lookup_back'' with R => //.
rewrite /while.entails => s h.
case/H => e' He'.
exists e'; by apply mapsto_strictly_exact.
Qed.

Lemma hoare_mutation_local : forall x v v', {{ x |~> v }} x *<- v' {{ x |~> v' }}.
Proof.
intros.
apply while.hoare_conseq with (P' := wp_mutation x v' (x |~> v'))
  (Q' := x |~> v') (c := mutation x  v'); first by done.
rewrite /while.entails; intros.
case: H => x0 [H H1].
rewrite /wp_mutation.
exists ([ v ]e_ s); split.
by rewrite H1 H heap.get_sing.
exists x0; split; first by done.
by rewrite H1 H heap.upd_sing.
by apply while.hoare_hoare0, hoare0_mutation.
Qed.

Lemma hoare_mutation' Q P e1 e2 : P ===> wp_mutation e1 e2 Q -> {{ P }} e1 *<- e2 {{ Q }}.
Proof.
intros.
apply (hoare_prop_m.hoare_stren (wp_mutation e1 e2 Q)) => //.
by apply while.hoare_hoare0, hoare0_mutation.
Qed.

Lemma hoare_mutation'' : forall R P Q c e1 e2,
  P ===> wp_mutation e1 e2 R -> {{ R }} c {{ Q }} -> {{ P }} e1 *<- e2 ; c {{ Q }}.
Proof. intros. apply while.hoare_seq with (Q := R) => //. by apply hoare_mutation'. Qed.

Lemma hoare_frame_rule_and'0 : forall P Q c, hoare0 P c Q ->
  forall P' Q' d, {{ P' }} d {{ Q' }} ->
    while.cmd_cmd0 c = d -> {{ P //\\ P' }} while.cmd_cmd0 c {{ Q //\\ Q' }}.
Proof.
move=> P Q c; induction 1.
- (* case skip *) move=> P' Q' d H H0; move: P H0.
  induction H => //; intros.
    case: H0 => H0.
    rewrite -H0 in H.
    inversion H; subst.
    constructor.
    by apply hoare0_skip.
  apply while.hoare_conseq with (P0 //\\ P') (P0 //\\ Q').
  rewrite /while.And => s h H3; split; [tauto | apply H; tauto].
  rewrite /while.And => s h H3; split; [tauto | apply H0; tauto].
  by apply IHhoare.
- (* case assign *) move=> P' Q' d H H0; move: P x e H0.
  induction H; intros; try discriminate.
    case: H0 => H0.
    rewrite -H0 in H.
    inversion H; subst.
    by apply hoare_assign'.
  apply while.hoare_conseq with ((wp_assign x e P0) //\\ P') (P0 //\\ Q').
  rewrite /while.And => s h H3; split; [tauto | apply H; tauto].
  rewrite /while.And => s h H3; split; [tauto | apply H0; tauto].
  by apply IHhoare.
- (* case lookup *) move=> P' Q' d H H0; move: P x e H0.
  induction H; intros; try discriminate.
    case: H0 => H0.
    rewrite -H0 in H.
    inversion H; subst.
    apply hoare_lookup'.
    rewrite /while.And /wp_lookup /while.entails => s h [[x0 [H1 H3]] [x1 [H2 H4]]].
    rewrite H1 in H2; case: H2 => H2; subst x1.
    by exists x0.
  apply while.hoare_conseq with ((wp_lookup x e P0) //\\ P') (P0 //\\ Q').
  rewrite /while.And => s h H3; split; [tauto | apply H; tauto].
  rewrite /while.And => s h H3; split; [tauto | apply H0; tauto].
  by apply IHhoare.
- (* case mutation *) move=> P' Q' d H H0; move: P e e' H0.
  induction H; intros; try discriminate.
    case: H0 => H0.
    rewrite -H0 in H.
    inversion H; subst.
    apply hoare_mutation'.
    rewrite /while.And /wp_mutation /while.entails => s h [[x0 [H1 H3]] [x1 [H2 H4]]].
    rewrite H1 in H2; case: H2 => H2; subst x0.
    by exists x1.
  apply while.hoare_conseq with ((wp_mutation e e' P0) //\\ P') (P0 //\\ Q').
  rewrite /while.And => s h H3; split; [tauto | apply H; tauto].
  rewrite /while.And => s h H3; split; [tauto | apply H0; tauto].
  by apply IHhoare.
- (* case malloc *) move=> P' Q' d H H0; move: P x e H0.
  induction H; intros; try discriminate.
    case: H0 => H0.
    rewrite -H0 in H.
    inversion H; subst.
    apply (hoare_prop_m.hoare_stren (fun s h => forall n, (cst_e n |~> e -* wp_assign x (cst_e n) (P0 //\\ Q)) s h)).
    rewrite /wp_assign /while.entails => s h [H1 H2].
    rewrite /imp => n h' H0 h'' H3.
    move: {H1}(H1 n) => H1.
    move: {H2}(H2 n) => H2.
    rewrite /imp in H1, H2.
    split.
    by apply H1 with h'.
    by apply H2 with h'.
    by apply while.hoare_hoare0, hoare0_malloc.
  apply while.hoare_conseq with
    ((fun s h => forall n, (cst_e n |~> e -* wp_assign x (cst_e n) P0) s h) //\\ P')
    (P0 //\\ Q').
  rewrite /while.And => s h H3; split; [tauto | apply H; tauto].
  rewrite /while.And => s h H3; split; [tauto | apply H0; tauto].
  by apply IHhoare; auto.
(* case free *)
- move=> P' Q' d H H0; move: P e H0.
  induction H; intros; try discriminate.
  + case: H0 => H0; rewrite -H0 in H; inversion H; subst.
    apply (hoare_prop_m.hoare_stren (fun s h =>
      exists v, heap.get ([ e ]e_s) h = Some v /\ (P0 //\\ Q) s (h \d\ [ e ]e_s))).
    rewrite /while.And /while.entails => s h [[x0 [H1 H3]] [x1 [H2 H4]]].
    rewrite H2 in H1; case: H1 => H1; subst x0.
    by exists x1.
    by apply while.hoare_hoare0, hoare0_free.
  + apply while.hoare_conseq with ((fun s h =>
    (exists v0, heap.get ([ e ]e_s) h = Some v0 /\
      P0 s (h \d\ [ e ]e_s))) //\\ P') (P0 //\\ Q').
    rewrite /while.And => s h H3; split; [tauto | apply H; tauto].
    rewrite /while.And => s h H3; split; [tauto | apply H0; tauto].
    by apply IHhoare.
Qed.

Lemma hoare_frame_rule_and0 P Q c : hoare0 P c Q ->
  forall P' Q', {{ P' }} c {{ Q' }} ->
  {{ P //\\ P' }} while.cmd_cmd0 c {{ Q //\\ Q' }}.
Proof. move=> P_c_Q P' Q' P'_c_Q'; by apply hoare_frame_rule_and'0 with c. Qed.

Lemma hoare_frame_rule_and c P Q P' Q' :
  {{ P }} c {{ Q }} -> {{ P' }} c {{ Q' }} ->
  {{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move=> P_c_Q P'_c_Q'; apply hoare_prop_m.hoare_frame_rule_and' => //; exact hoare_frame_rule_and0.
Qed.

(** Frame rule *)

Fixpoint modified_vars (c : @while.cmd cmd0 expr_b) {struct c} : seq var.v :=
  match c with
    | skip => nil
    | x <- e => x :: nil
    | x <-* e => x :: nil
    | e *<- f => nil
    | x <-malloc e => x :: nil
    | free e => nil
    | c1 ; c2 => modified_vars c1 ++ modified_vars c2
    | while.ifte a c1 c2 => modified_vars c1 ++ modified_vars c2
    | while.while a c1 => modified_vars c1
   end.

Fixpoint modified_loc_expr (c : @while.cmd cmd0 expr_b) {struct c} : seq expr :=
  match c with
    | skip => nil
    | x <- e => nil
    | x <-* e => nil
    | e *<- f => e :: nil
    | x <-malloc e => nil
    | free e => e :: nil
    | c1 ; c2 => modified_loc_expr c1 ++ modified_loc_expr c2
    | while.ifte a c1 c2 => modified_loc_expr c1 ++ modified_loc_expr c2
    | while.while a c1 => modified_loc_expr c1
  end.

Lemma inde_seq R c d : inde (modified_vars (c ; d)) R ->
  inde (modified_vars c) R /\ inde (modified_vars d) R.
Proof.
move=> H; split => s h x v H'; split => H''.
- by rewrite -H //= mem_cat H'.
- by rewrite (H _ _ x v) //= mem_cat H'.
- by rewrite -H //= mem_cat H' orbT.
- by rewrite (H _ _ x v) //= mem_cat H' orbT.
Qed.

Lemma inde_ifte R b c d : inde (modified_vars (If b Then c Else d)) R ->
  inde (modified_vars c) R /\ inde (modified_vars d) R.
Proof.
move=> H; split => s h x v H'; split => H''.
- by rewrite -H //= mem_cat H'.
- by rewrite (H _ _ x v) //= mem_cat H'.
- by rewrite -H //= mem_cat H' orbT.
- by rewrite (H _ _ x v) //= mem_cat H' orbT.
Qed.

Module map_prop_m := Map_Prop heap.

Lemma frame_rule0 P c Q : hoare0 P c Q ->
  forall R, inde (modified_vars c) R -> {{ P ** R }} c {{ Q ** R }}.
Proof.
elim; move=> {P} P.
- (* skip *) move=> R H; by apply while.hoare_hoare0, hoare0_skip.
- (* x <- e *) move=> x e R H.
  apply (hoare_prop_m.hoare_stren (wp_assign x e (P ** R))); last by apply while.hoare_hoare0, hoare0_assign.
  rewrite /while.entails => s h H0.
  case_sepcon H0.
  rewrite /wp_assign; exists h1, h2; repeat (split; trivial).
  by apply inde_upd_store.
- (* x <-* e *) move=> x e R H.
  apply (hoare_prop_m.hoare_stren (wp_lookup x e (P ** R))); last by apply while.hoare_hoare0, hoare0_lookup.
  rewrite /wp_lookup => s h H0.
  case_sepcon H0.
  case: H0_h1 => z [Hz HP].
  exists z; split.
  + rewrite h1_U_h2; by apply heap.get_union_L.
  + exists h1, h2; repeat (split; trivial); by apply inde_upd_store.
- (* e *<- e' *) move=> e e' R H.
  apply (hoare_prop_m.hoare_stren (wp_mutation e e' (P ** R))); last by apply while.hoare_hoare0, hoare0_mutation.
  rewrite /while.entails => s h H0.
  case_sepcon H0.
  rewrite /wp_mutation in H0_h1.
  case: H0_h1 => z [Hz HP].
  rewrite /wp_mutation; exists z; split.
  + rewrite h1_U_h2; by apply heap.get_union_L.
  + exists (heap.upd ([ e ]e_ s) ([ e' ]e_ s) h1), h2; split.
    by apply heap.disj_upd.
    split; last by done.
    rewrite h1_U_h2; by apply heap.upd_union_L with z.
- (* x <-malloc e *) move=> x e R H.
  apply (hoare_prop_m.hoare_stren (fun s h => forall n , (cst_e n |~> e -* wp_assign x (cst_e n) (P ** R)) s h));
    last by apply while.hoare_hoare0, hoare0_malloc.
  move=> s h [h1 [h2 [H1 [H2 [H3 H4]]]]] n h' [Hhh' Hn] h'' Hh''.
  rewrite /wp_assign.
  exists (h1 \U h'), h2; split; first by map_tac_m.Disj.
  split; first by map_tac_m.Equal.
  split.
  move: {H3}(H3 n) => H3.
  rewrite /imp /wp_assign in H3.
  apply (H3 h') => //.
  split; [by map_tac_m.Disj | exact Hn].
  by rewrite -(H s h2 x n) //= mem_seq1.
- (* free *) move=> e R H.
  apply (hoare_prop_m.hoare_stren (fun s h =>
      exists v, heap.get ([ e ]e_s) h = Some v /\ (P ** R) s (h \d\ [ e ]e_s))); last by apply while.hoare_hoare0, hoare0_free.
  move=> s h [x [x0 [H1 [H3 [[x2 [H4 H6]] H5]]]]].
  exists x2; split.
  + rewrite H3; by apply heap.get_union_L.
  + exists (x \d\ [ e ]e_ s), x0.
    have H0 : x0 = x0 \d\ [ e ]e_ s.
      symmetry.
      apply heap.dif_disj with x2.
      move: (map_prop_m.get_exists_sing x ([ e ]e_ s) x2 H4) => [x3 [H0 H8]].
      by map_tac_m.Disj.
    split.
    * rewrite H0; by apply heap.dif_disj'.
    * split; last by done.
      rewrite H3.
      apply trans_eq with ((x \d\ [ e ]e_ s) \U (x0 \d\ [ e ]e_ s)).
      - by apply heap.dif_union.
      - apply trans_eq with ((x0 \d\ [ e ]e_ s) \U (x \d\ [ e ]e_ s)).
        + by apply heap.unionC, heap.dif_disj'.
        + apply trans_eq with (x0 \U (x \d\ [ e ]e_ s)).
          * by rewrite -H0.
          * apply heap.unionC, heap.disj_sym.
            rewrite H0; by apply heap.dif_disj'.
Qed.

Lemma frame_rule_R P c Q : {{ P }} c {{ Q }} ->
  forall R, inde (modified_vars c) R -> {{ P ** R }} c {{ Q ** R }}.
Proof.
elim; clear P c Q.
- move=> P Q c H T Hinde; by apply frame_rule0.
- (* seq *) move=> Q P R c d Hc IHc Hd IHd R0 H.
  apply (while.hoare_seq _ _ _ _ _ _ (Q ** R0)).
  apply (hoare_prop_m.hoare_stren (P ** R0)) => //.
  apply IHc; exact (proj1 (inde_seq _ _ _ H)).
  apply IHd; exact (proj2 (inde_seq _ _ _ H)).
- (* hoare_conseq *) move=> P P' Q Q' c Q'Q PP' H IH R Hinde.
  apply (hoare_prop_m.hoare_stren (P' ** R)).
  rewrite /while.entails => s h H0.
  case_sepcon H0.
  exists h1, h2; by auto.
  apply (hoare_prop_m.hoare_weak (Q' ** R)).
  rewrite /while.entails => s h H0.
  case_sepcon H0.
  exists h1, h2; by auto.
  by apply IH.
- (* while true *) move=> P t c H IH R Hinde.
  apply (hoare_prop_m.hoare_weak (fun s h => (P ** R) s h /\ ~~ [ t ]b_ s)).
  rewrite /while.entails => s h [H1 H2].
  case_sepcon H1.
  by exists h1, h2.
  apply (hoare_prop_m.hoare_stren (P ** R)).
  by apply hoare_prop_m.entails_id.
  apply while.hoare_while with (P := P ** R).
  apply (hoare_prop_m.hoare_stren ((fun s0 h0 => P s0 h0 /\ eval_b t s0) ** R)).
  rewrite /while.entails => s h [H1 H2].
  case_sepcon H1.
  by exists h1, h2.
  by apply IH.
- (* hoare_ifte *) move=> P Q t c d Hc IHc Hd IHd R Hinde.
  apply while.hoare_ifte.
  + apply (hoare_prop_m.hoare_stren ((fun s h => P s h /\ [ t ]b_ s) ** R)).
    rewrite /while.entails => s h [H0 H1].
    case_sepcon H0.
    by exists h1, h2.
    apply IHc.
    exact (proj1 (inde_ifte _ _ _ _ Hinde)).
  + apply (hoare_prop_m.hoare_stren ((fun s h => P s h /\ ~~ [ t ]b_ s) ** R)).
    rewrite /while.entails => s h [H0 H1].
    case_sepcon H0.
    by exists h1, h2.
    apply IHd.
    exact (proj2 (inde_ifte _ _ _ _ Hinde)).
Qed.

(** More derived Separation logic axioms *)

Lemma hoare_free_global_backwards : forall e v P, {{ e |~> v ** P }} free e {{ assert_m.emp ** P }}.
Proof.
intros.
apply frame_rule_R.
apply (hoare_prop_m.hoare_stren (fun s h =>
    exists v0, heap.get ([ e ]e_s) h = Some v0 /\ assert_m.emp s (h \d\ [ e ]e_s))).
rewrite /while.entails; intros.
inversion_clear H.
inversion_clear H0.
exists ([ v ]e_s); split.
by rewrite H1 H heap.get_sing.
rewrite /emp.
apply trans_eq with (heap.sing x ([ v ]e_s) \d\ x).
by rewrite H1 H.
by apply heap.dif_sing.
by apply while.hoare_hoare0, hoare0_free.
by [].
Qed.

Lemma hoare_mutation_global P e e' :
  {{ (fun s h => exists e'', ((e |~> e'') s h)) ** P }}
  e *<- e'
  {{ (e |~> e') ** P }}.
Proof.
apply frame_rule_R => //.
apply (hoare_prop_m.hoare_stren (wp_mutation e e' (e |~> e'))); last first.
  by apply while.hoare_hoare0, hoare0_mutation.
rewrite /while.entails; intros.
case: H => x [x0 [H H1]].
rewrite /wp_mutation.
exists ([ x ]e_s); split.
  by rewrite H1 H heap.get_sing.
exists x0; split; auto.
by rewrite H1 H heap.upd_sing.
Qed.

Lemma hoare_mutation_global_alternative P e e' e'' :
  {{ (e |~> e'') ** P }} e *<- e' {{ (e |~> e') ** P }}.
Proof.
apply (hoare_prop_m.hoare_stren ((fun s h => exists e'', (e |~> e'') s h) ** P)).
rewrite /while.entails; intros.
case: H => x [x0 [H0 [H2 [H1 H4]]]].
exists x, x0.
split; first by done.
split; first by done.
split; last by done.
by exists e''.
by apply hoare_mutation_global.
Qed.

Lemma hoare_mutation_backwards P e e' :
  {{ fun s h => exists e'', (e |~> e'' ** (e|~>e' -* P)) s h }} e *<- e' {{ P }}.
Proof.
move: (hoare_mutation_global ((e |~> e') -* P) e e') => H.
apply hoare_prop_m.hoare_weak with ((e |~> e') ** ((e |~> e') -* P)).
by apply assert_m.mp.
apply (hoare_prop_m.hoare_stren ((fun s h => exists e'', (e |~> e'') s h) ** ((e |~> e') -* P))); last by done.
rewrite /while.entails => s h [x H1].
case_sepcon H1.
exists h1, h2.
split; first by done.
split; first by done.
split; last by done.
by exists x.
Qed.

Lemma hoare_mutation_backwards_alternative P e e' e'' :
  {{ (e |~> e'') ** ((e |~> e') -* P) }} e *<- e' {{ P }}.
Proof.
generalize (hoare_mutation_global_alternative ((e |~> e') -* P) e e' e''); intro.
apply hoare_prop_m.hoare_weak with ((e |~> e') ** ((e |~> e') -* P)) => //.
by apply assert_m.mp.
Qed.

Lemma hoare_mutation_backwards' Q P e1 e2 :
  P ===> (fun s h => exists e'', (e1 |~> e'' ** (e1 |~> e2 -* Q)) s h) ->
  {{ P }} e1 *<- e2 {{ Q }}.
Proof.
move=> H.
apply (hoare_prop_m.hoare_stren (fun s h => exists e'', (e1 |~> e'' ** (e1 |~> e2 -* Q)) s h)) => //.
by apply hoare_mutation_backwards.
Qed.

Lemma hoare_mutation_backwards'' : forall Q P R e1 e2 c,
  P ===> (fun s h => exists e'', (e1 |~> e'' ** (e1 |~> e2 -* R)) s h) ->
  {{ R }} c {{ Q }} -> {{ P }} e1 *<- e2 ; c {{ Q }}.
Proof. intros. apply while.hoare_seq with (Q := R) => //. by apply hoare_mutation_backwards'. Qed.

(** wp_assign, wp_mutation, etc. properties *)

Lemma wp_mutation_sep_con : forall x v P Q, wp_mutation x v P ** Q ===> wp_mutation x v (P ** Q).
Proof.
rewrite /wp_mutation => x v P Q s h H.
case: H => x0 [x1 [H0 [H2 [[x3 [H3 H5]] H4]]]].
exists x3; split.
- rewrite H2; by apply heap.get_union_L.
- exists (heap.upd ([ x ]e_ s) ([ v ]e_s) x0); exists x1; split.
  + by apply heap.disj_upd.
  + split; last by done.
    rewrite H2.
    by apply heap.upd_union_L with x3.
Qed.

Lemma wp_mutation_sep_con': forall P Q x1 x2 v1 v2,
  (wp_mutation x1 v1 P) ** (wp_mutation x2 v2 Q) ===>
  wp_mutation x1 v1 (wp_mutation x2 v2 (P**Q)).
Proof.
rewrite /while.entails; intros.
generalize (wp_mutation_sep_con x1 v1 P (wp_mutation x2 v2 Q)); intro.
rewrite /while.entails in H0.
generalize (H0 _ _ H); intro.
rewrite /wp_mutation in H1 *.
case: H1 => p [H1 H3].
exists p; split; first by exact H1.
rewrite assert_m.conCE.
apply (wp_mutation_sep_con x2 v2 Q P).
by rewrite assert_m.conCE.
Qed.

Lemma frame_rule' : forall P c Q, {{ P }} c {{ Q }} ->
  forall R1 R2, inde (modified_vars c) R1 -> R1 ===> R2 ->
    {{ P ** R1 }} c {{ Q ** R2 }}.
Proof.
move=> P c Q H R1 R2 H0 H1.
apply hoare_prop_m.hoare_weak with (Q ** R1).
by apply monotony'.
by apply frame_rule_R.
Qed.

Lemma frame_rule'' : forall c1 c2 P1 P2 Q1 Q2,
  {{ P1 }} c1 {{ Q1 }} -> {{ P2 }} c2 {{ Q2 }} ->
  inde (modified_vars c1) P2 -> inde (modified_vars c2) Q1 ->
  {{ P1 ** P2 }} c1 ; c2 {{ Q1 ** Q2 }}.
Proof.
intros.
move: (frame_rule_R P1 c1 Q1 H P2 H1) => H3.
move: (frame_rule_R P2 c2 Q2 H0 Q1 H2) => H4.
have H5 : ((Q1 ** P2) ===> (P2 ** Q1)) by apply assert_m.conC.
have H6 : ((Q2 ** Q1) ===> (Q1 ** Q2)) by apply assert_m.conC.
apply while.hoare_seq with (P2 ** Q1).
by apply hoare_prop_m.hoare_weak with (Q1 ** P2).
by apply hoare_prop_m.hoare_weak with (Q2 ** Q1).
Qed.

Lemma hoare_mutation_frame_rule : forall  x v c P Q v',
  {{ P }} c {{ Q }} ->
  inde (modified_vars c) (x |~> v) ->
  {{ x |~> v' ** P }} x *<- v ; c {{ x |~> v ** Q }}.
Proof.
intros.
apply while.hoare_seq with (x |~> v ** P).
apply hoare_mutation_global_alternative.
apply (hoare_prop_m.hoare_stren (P ** x |~> v)).
rewrite /while.entails; intros; by rewrite assert_m.conCE.
apply hoare_prop_m.hoare_weak with (Q ** (x |~> v)).
rewrite /while.entails; intros; by rewrite assert_m.conCE.
by apply frame_rule_R.
Qed.

(** definitions of arrays (contiguous areas of memory) and their properties *)

Local Open Scope nat_scope.

Fixpoint Array p (size : nat) {struct size} : assert :=
  match size with
    | O => assert_m.emp
    | S n =>
      (fun s h => exists y, (nat_e p |~> cst_e y) s h) ** Array (p + 1) n
  end.

Lemma Array_inde_store : forall m n s h, Array n m s h -> forall s', Array n m s' h.
Proof.
elim=> // m IH n s h /= H s'.
case_sepcon H.
exists h1, h2.
split; first by done.
split; first by done.
split.
case: H_h1 => y H_h1.
exists y.
by Mapsto.
by apply IH with s.
Qed.

(* TODO: move tactics to bipl.v (?) *)
Ltac Array_equiv :=
  match goal with
    | H: Array ?adr1 ?sz1 ?s1 ?h |-  Array ?adr2 ?sz2 ?s2 ?h =>
      let H1 := fresh in
      let H2 := fresh in
      assert (H1: adr2 = adr1); [ssromega |
        assert (H2: sz2 = sz1); [ssromega |
          (rewrite -> H1 || idtac); (rewrite -> H2 || idtac);
          eapply Array_inde_store; apply H
        ]
      ]
  end.

Lemma Array_inde : forall l adr size, inde l (Array adr size).
Proof.
elim=> // h t IH a sz.
rewrite /inde => s h0 x v /=; rewrite in_cons => /orP[/eqP ->|].
- split; intros; eapply Array_inde_store; by apply H.
- exact/IH.
Qed.

Lemma Array_inde_list: forall l st sz, inde l (Array st sz).
Proof.
elim=> // h t IH st sz.
rewrite /inde; intros.
split; intros; eapply Array_inde_store; by apply H0.
Qed.

Lemma Array_concat_split : forall size1 size2 adr,
  Array adr (size1 + size2) <==> (Array adr size1 ** Array (adr + size1) size2).
Proof.
induction size1.
- split.
  + intros.
    exists heap.emp, h.
    split; first by map_tac_m.Disj.
    split; first by map_tac_m.Equal.
    split; first by done.
    by rewrite add0n in H; rewrite addn0.
  + move=> [x [x0 H]].
    case: H => [H0 [H2 [H1 H4]]].
    rewrite /= /emp in H1; subst x.
    rewrite addn0 in H4; rewrite add0n.
    rewrite heap.unioneh in H2.
    by subst x0.
- split => H.
  + move=> /=.
    rewrite /= in H.
    case: H => x [x0 H].
    case: H => [H0 [H2 [[x1 H] H4]]].
    case: (IHsize1 size2 (adr + 1) s x0) => H1 H3.
    move: {H1 H3}(H1 H4) => [x2 [x3 H1]].
    case: H1 => [H3 [H6 [H5 H8]]].
    exists (x \U x2), x3.
    split; first by map_tac_m.Disj.
    split; first by map_tac_m.Equal.
    split.
    * exists x, x2.
      split; first by map_tac_m.Disj.
      split; first by map_tac_m.Equal.
      split; last by done.
      by exists x1.
    * by rewrite addn1 addSnnS in H8.
  + case_sepcon H.
    simpl in H_h1.
    case_sepcon H_h1.
    inversion_clear H_h1_h11.
    exists h11, (h12 \U h2).
    split; first by map_tac_m.Disj.
    split; first by map_tac_m.Equal.
    split.
    by exists x.
    case: (IHsize1 size2 (adr + 1) s (h12 \U h2)) => _; apply.
    exists h12, h2.
    split; first by map_tac_m.Disj.
    split; first by map_tac_m.Equal.
    split; first by done.
    by rewrite addn1 addSnnS.
Qed.

(* TODO: rename intermediate hypotheses *)

Ltac TArray_concat_split_r sz1 sz2:=
  match goal with
    | |- Array ?adr ?sz ?s ?h =>
      let H1 := fresh in
      let H11 := fresh in
      let H12 := fresh in
      let H2 := fresh in
      generalize (Array_concat_split sz1 sz2 adr s h); intro H1; inversion_clear H1 as [H11 H12];
        assert (H2: sz1 + sz2 = sz); [ssromega | (rewrite <- H2 || idtac); clear H2; apply H12; clear H11 H12]
  end.

Ltac TArray_concat_split_l_l sz H :=
  match goal with
    | H: Array ?adr ?size ?s ?h |- _ =>
      let H1 := fresh in 
      let H2 := fresh in 
      let H3 := fresh in 
      let H4 := fresh in 
      assert (H1: size = sz + (size - sz));
        [ssromega |
          rewrite -> H1 in H; clear H1;
            generalize (Array_concat_split sz (size - sz) adr s h); intro H2;
              inversion_clear H2 as [H3 H4]; generalize (H3 H); clear H4; clear H3; intro
        ]
  end.

Ltac TArray_concat_split_l_r sz H:=
  match goal with
    | H: Array ?adr ?size ?s ?h |- _ =>
      let H1 := fresh in 
      let H2 := fresh in
      let H21 := fresh in
      let H22 := fresh in
      assert (H1: size = (size - sz) + sz);
        [ssromega |
          rewrite -> H1 in H; clear H1;
            generalize (Array_concat_split (size - sz) sz adr s h); intro H2;
              inversion_clear H2 as [H21 H22]; generalize (H21 H); clear H22; clear H21; intro
        ]
  end.

(* test *)
Lemma Array_split : forall size' size,
  size' <= size ->
  forall adr s h, adr > 0 -> Array adr size s h ->
    (Array adr size' ** Array (adr+size') (size - size')) s h.
Proof.
intros.
by TArray_concat_split_l_l size' H1.
Qed.

Lemma Array_disj : forall size adr s h, adr > 0 -> Array adr size s h ->
  forall adr', adr' >= adr + size ->
    forall z, h # (heap.sing (A.of_nat adr') z).
Proof.
elim.
- simpl.
  move=> adr s h H H0 adr' H1 z.
  red in H0.
  subst h.
  by apply heap.disjeh.
- move=> n IH adr s h H0 /= H1 adr' H2 z.
  case_sepcon H1.
  have Hadr : (adr + 1 > 0) by ssromega.
  have Hadr' : (adr' >= (adr + 1) + n) by ssromega.
  move: {IH}(IH _ _ _ Hadr H1_h2 adr' Hadr') => IH.
  apply heap.disj_sym.
  rewrite h1_U_h2.
  apply heap.disjhU.
  + case : H1_h1 => y [x1 [Hx1 Hh1]].
    rewrite /= in Hx1; subst x1.
    rewrite Hh1.
    apply heap.disj_sing.
    apply/eqP => /A.of_nat_inj ?; ssromega.
  + apply heap.disj_sym; by apply IH.
Qed.

Lemma Array_concat : forall size adr s h, adr > 0 -> Array adr size s h ->
  forall z, Array adr (size + 1) s (h \U heap.sing (A.of_nat (adr+size)) z).
Proof.
induction size.
- move=> adr s h H H0 z.
  rewrite /Array /emp in H0.
  exists (heap.sing (A.of_nat (adr + 0)) z), heap.emp.
  split; first by apply heap.disjhe.
  split; first by Heap_emp_clean; map_tac_m.Equal.
  split; last by done.
  exists z.
  rewrite /mapsto.
  exists (A.of_nat adr) => /=.
  by rewrite addn0.
- move=> adr s h H H0 z.
  rewrite /= in H0.
  case_sepcon H0.
  have Hadr : (adr + 1) > 0 by ssromega.
  rewrite addSnnS.
  TArray_concat_split_r 1 (size + 1).
  move: {Hadr IHsize}(IHsize _ _ _ Hadr H0_h2 z) => IHsize.
  inversion_clear H0_h1.
  exists h1, (h2 \U heap.sing (A.of_nat ((adr + 1) + size)) z).
  split.
  + apply heap.disjhU; first by done.
    case: H0 => x0 [H0 H2]; subst x0.
    apply heap.disj_sym.
    rewrite H2.
    apply heap.disj_sing.
    apply/eqP => /A.of_nat_inj ?; ssromega.
  + split.
    * rewrite addnS -addSn -addn1.
      by map_tac_m.Equal.
    * split; last by done.
      case: H0 => x0 [H0 H2]; subst x0 => /=.
      Compose_sepcon h1 heap.emp; last by done.
      exists x.
      rewrite /mapsto /=.
      by exists (A.of_nat adr).
Qed.

Lemma mapstos_to_array : forall l x x' sz s h, (x |--> l) s h ->
  [ x ]e_s = A.of_nat x' -> sz = size l -> Array x' sz s h.
Proof.
induction l.
- by move=> /= x x' sz s h H H0 H1; subst sz.
- move=> x x' sz s h /= H H1 H2; subst sz.
  case: H => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]] /=.
  Compose_sepcon h1 h2.
  + exists ([ a ]e_s); by Mapsto.
  + eapply IHl => //.
    exact: Hh2.
    by rewrite /= addnC /= -(A.add1 x') A.addC H1.
Qed.

(** Definition of intialized arrays *)
Fixpoint ArrayI x (l : seq A.t) { struct l } : assert :=
  match l with
    | nil => assert_m.emp
    | hd :: tl => (fun s h => (nat_e x |~> cst_e hd) s h) ** ArrayI (x + 1) tl
  end.

Lemma ArrayI_inde_store : forall l n s h, ArrayI n l s h -> forall s', ArrayI n l s' h.
Proof.
elim => // hd tl IH n s h H s'.
rewrite /= in  H.
case_sepcon H.
rewrite /=.
Compose_sepcon h1 h2.
- move: H_h1; by apply mapsto_ext.
- by apply (IH _ _ _ H_h2).
Qed.

Lemma ArrayI_disj_heap: forall lst a h' e e' s h,
  ArrayI a lst s h -> (nat_e e |~> e') s h' -> e < a \/ e >= a + size lst -> h # h'.
Proof.
induction lst.
- move=> a h' e e' s h H /= H0 H1.
  rewrite /ArrayI /emp in H.
  rewrite H.
  by apply heap.disjeh.
- move=> a0 h' e e' s h H H0 H1.
  case: H1 => H2.
  + destruct a0.
    * by inversion H2.
    * simpl in H.
      case: H0 => x /= [H0 H3]; subst x.
      case_sepcon H.
      case : H_h1 => x1 /= [H H5].
      subst x1.
      rewrite h1_U_h2.
      apply heap.disj_sym; apply heap.disjhU.
      - rewrite H3 H5.
        apply heap.disj_sing.
        apply/eqP => /A.of_nat_inj ?; ssromega.
      - apply heap.disj_sym.
        eapply IHlst.
        apply H_h2.
        exists (A.of_nat e); split => /=.
        reflexivity.
        exact H3.
        ssromega.
  + case: H0 => x [H0 H3]; subst x.
    destruct a0 as [|a0].
    * simpl in H.
      case_sepcon H.
      case: H_h1 => x [/= H0 H1]; subst x.
      rewrite h1_U_h2.
      apply heap.disjUh.
      - rewrite H3 H1.
        apply heap.disj_sing.
        apply/eqP => /A.of_nat_inj ?; subst e.
        by rewrite add0n leqn0 in H2.
      - eapply IHlst.
        by apply H_h2.
        exists (A.of_nat e); split => /=.
        reflexivity.
        apply H3.
        rewrite /= in H2; ssromega.
    * simpl in H.
      case_sepcon H.
      case: H_h1 => x /= [H0 H1]; subst x.
      rewrite h1_U_h2.
      apply heap.disjUh.
      - rewrite H3 H1.
        apply heap.disj_sing.
        simpl in H2.
        apply/eqP => /A.of_nat_inj ?; ssromega.
      - eapply IHlst.
        apply H_h2.
        exists (A.of_nat e); split => /=.
        reflexivity.
        apply H3.
        rewrite /= in H2 *; ssromega.
Qed.

Lemma Data_destructive_upd_inv2 lx x h1 h2 e1 x1 s h :
  (ArrayI x lx ** TT) s h ->
  h1 # h2 -> h = h1 \U h2 ->
  (nat_e e1 |~> x1) s h1 ->
  e1 < x \/ e1 >= x + size lx ->
  (ArrayI x lx ** TT) s h2.
Proof.
intros.
case_sepcon H.
generalize (ArrayI_disj_heap lx x h1 e1 x1 s h0 H_h0 H2 H3); intros.
assert (h0 \U h3 = h1 \U h2). by rewrite -h0_U_h3.
auto.
case: (map_prop_m.disj_comp h0 h1 h2 h3 (heap.disj_sym _ _ H) H0 h0_d_h3 H4) => x0 H10.
inversion_clear H10.
by Compose_sepcon h0 x0.
Qed.

Lemma Data_destructive_upd_inv lx x h1 h2 e1 x1 x2 h'1 h' s h :
  (ArrayI x lx ** TT) s h ->
  h1 # h2 -> h = h1 \U h2 ->
  (nat_e e1 |~> x1) s h1 ->
  (nat_e e1 |~> x2) s h'1 ->
  h'1 # h2 ->
  h' = h'1 \U h2 ->
  e1 < x \/ e1 >= x + size lx ->
  (ArrayI x lx ** TT) s h'.
Proof.
intros.
move: (Data_destructive_upd_inv2 lx x h1 h2 e1 x1 s h H H0 H1 H2 H6) => H7.
case_sepcon H7.
by Compose_sepcon h21 (h22 \U h'1).
Qed.

Inductive cmd' : Type :=
| skip': cmd' 
| assign_var_e' : var.v -> expr -> cmd' 
(* TODO: rename *)
| assign_var_deref' : var.v -> expr -> cmd' 
| assign_deref_expr' : expr -> expr -> cmd' 
| malloc' : var.v -> expr -> cmd' 
| free' : expr -> cmd' 
| while' : expr_b -> assert -> cmd' -> cmd' 
| seq' : cmd' -> cmd' -> cmd'
| ifte' : expr_b -> cmd' -> cmd' -> cmd'.

Notation "c ; d" := (seq' c d) (at level 81, right associativity) : vc_scope.
Notation "x '<-' e" := (assign_var_e' x e) (at level 80) : vc_scope.
Notation "x '<-*' e" := (assign_var_deref' x e) (at level 80) : vc_scope.
Notation "e '*<-' f" := (assign_deref_expr' e f) (at level 80) : vc_scope.
Notation "x '<-malloc' e" := (malloc' x e) (at level 80) : vc_scope.

Local Open Scope vc_scope.

Fixpoint proj_cmd (c' : cmd') : @while.cmd cmd0 expr_b :=
  match c' with
    | skip' => skip
    | x <- e => assign x e
    | x <-* e => lookup x e
    | e *<- f => mutation e f
    | x <-malloc e => malloc x e
    | free' e => free e
    | while' b Q c'' => While b {{ proj_cmd c'' }}
    | seq' c1 c2 => while.seq (proj_cmd c1) (proj_cmd c2)
    | ifte' b c1 c2 => If b Then proj_cmd c1 Else proj_cmd c2
  end.

(** compute the weakest precondition under the assumption that 
while loops are annotated with invariants *)
Fixpoint wp (c : cmd') (P : assert) {struct c} : assert :=
  match c with
    | skip' => P
    | assign_var_e' x e => wp_assign x e P
    | assign_var_deref' x e => 
      fun s h => exists e0, (e |~> e0 ** (e |~> e0 -* wp_assign x e0 P)) s h
    | assign_deref_expr' e f =>  
      fun s h => exists x, ((e |~> x ** (e |~> f -* P)) s h)
    | (malloc' x e) => 
      fun s h => forall n, (cst_e n |~> e -* wp_assign x (cst_e n) P) s h
    | free' e => fun s h => 
	exists v, heap.get ([ e ]e_s) h = Some v /\ P s (h \d\ [ e ]e_s)
    | while' b Q c' => Q
    | seq' c1 c2 => wp c1 (wp c2 P)
    | ifte' b c1 c2 => fun s h =>
      ([ b ]b_s -> wp c1 P s h) /\ (~~ [ b ]b_ s -> wp c2 P s h)
  end.

(* condition on the goal *)
Fixpoint vc (c : cmd') (P : assert) {struct c} : assert :=
  match c with
    | skip' => TT
    | assign_var_e' x e => TT
    | assign_var_deref' x e => TT
    | assign_deref_expr' e f => TT
    | malloc' x e => TT
    | free' e => TT
    | while' b Q c' => fun s h =>
      (Q s h /\ ~~ [ b ]b_s -> P s h) /\
      (Q s h /\ [ b ]b_s -> wp c' Q s h) /\ (vc c' Q s h)
    | seq' c1 c2 => fun s h => vc c1 (wp c2 P) s h /\ vc c2 P s h
    | ifte' b c1 c2 => fun s h => vc c1 P s h /\ vc c2 P s h
  end.

Lemma vc_soundness : forall c' P, (forall s h, vc c' P s h) -> 
  {{ wp c' P }} proj_cmd c' {{ P }}.
Proof.
induction c'.
- intros. by apply while.hoare_hoare0, hoare0_skip.
- intros. by apply while.hoare_hoare0, hoare0_assign.
- intros. by apply hoare_lookup_back.
- intros. by apply hoare_mutation_backwards.
- intros. by apply while.hoare_hoare0, hoare0_malloc.
- intros. by apply while.hoare_hoare0, hoare0_free.
- intros => /=.
  apply (hoare_prop_m.hoare_weak (fun s h => a s h /\ ~~ [ e ]b_s)).
  move=> s h X. move: (H s h) => /=. by intuition.
  apply while.hoare_while.
  apply (hoare_prop_m.hoare_stren (wp c' a)).
  + move=> s h X. move: (H s h) => /=. by intuition.
  + apply IHc'. move: (IHc' a) => H0 s h. move: (H s h) => /=. by intuition.
- intros => /=.
  apply while.hoare_seq with (wp c'2 P).
  + apply IHc'1 => s h. move: (H s h) => /=. by intuition.
  + apply IHc'2 => s h. move: (H s h) => /=. by intuition.
- intros => /=.
  apply while.hoare_ifte.
  + apply (hoare_prop_m.hoare_stren (wp c'1 P)).
    * move=> s h /=; by intuition.
    * apply IHc'1 => s h. move: (H s h) => /=; by intuition.
  + apply (hoare_prop_m.hoare_stren (wp c'2 P)).
    * move=> s h /=; rewrite /while.entails; by intuition.
    * apply IHc'2 => s h. move: (H s h) => /=; by intuition.
Qed.

Lemma wp_vc_util c Q P : (forall s h, vc c Q s h) ->
  P ===> wp c Q -> {{ P }} proj_cmd c {{ Q }}.
Proof.
intros. exact: (hoare_prop_m.hoare_stren (wp c Q) P Q (proj_cmd c) H0 (vc_soundness c Q H)).
Qed.

End Seplog.

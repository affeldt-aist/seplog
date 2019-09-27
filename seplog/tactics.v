(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect eqtype ssrbool seq.
Require Import bipl seplog integral_type seq_ext.

Declare Scope tactics_scope.

(** Preliminary tests before implementing seplog tactics *)

Module Tactics (A : IntegralType).

Module Import seplog_m := Seplog A.
Import seplog_m.assert_m.expr_m.
Import seplog_m.assert_m.

Local Open Scope Z_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.

(* TODO: rename to bang, move *)
Definition pure (e : expr_b) : assert := fun s h => h = heap.emp /\ eval_b e s = true.

Notation "! e" := (pure e) (at level 80) : tactics_scope.
Local Open Scope tactics_scope.

Lemma hoare_drop_pure : forall P c Q e, {{ P }} c {{ Q }} -> {{ P ** ! e }} c {{ Q }}.
Proof.
move=> P c Q e H.
apply hoare_prop_m.hoare_stren with P => //.
move=> s h [h1 [h2 [Hdisj [Hunion [HP [Hh2 He]]]]]].
subst h2.
by rewrite Hunion heap.unionhe.
Qed.

Lemma hoare_assign_forward P v e :
  inde (v :: nil) P -> disj (vars e) (v :: nil) ->
  {{ P }} v <- e {{ P ** ! (var_e v \= e ) }}.
Proof.
move=> Hinde Hinter.
apply hoare_assign' => s h HP.
exists h, heap.emp.
split; first exact: heap.disjhe.
split; first by rewrite heap.unionhe.
split; first exact: inde_upd_store.
split; first by [].
rewrite /= store.get_upd' eval_upd; first exact/A.eqP.
apply/negP/inP; eapply disj_not_In; eauto.
by rewrite /=; auto.
Qed.

Lemma hoare_assign_lookup_forward e1 e2 v :
  disj (vars e1) (v :: nil) ->
  seq_ext.disj (vars e2) (v :: nil)  ->
  {{ e1 |~> e2 }} v <-* e1 {{ e1 |~> e2 ** ! (var_e v \= e2) }}.
Proof.
move=> He1 He2.
apply hoare_lookup' => s h [p [Hp Hh]].
exists ([ e2 ]e_s).
split; first by rewrite Hh Hp heap.get_sing.
exists h; exists heap.emp.
split; first by apply heap.disjhe.
split; first by rewrite heap.unionhe.
split.
  exists p.
  split.
    rewrite eval_upd //.
    apply/negP/inP; eapply disj_not_In; eauto.
    by rewrite /=; auto.
  rewrite eval_upd //.
  apply/negP/inP; eapply disj_not_In; eauto.
  by rewrite /=; auto.
split; first by [].
rewrite /= store.get_upd' eval_upd; first exact/A.eqP.
apply/negP/inP; eapply disj_not_In; eauto.
by rewrite /=; auto.
Qed.

Ltac Inde :=
  match goal with
    | |- inde _ TT =>
      apply inde_TT
    | |- inde _ (_ |~> _) =>
      apply inde_mapsto; (*inter subgoals*) [idtac | idtac]
    | |- _ =>
      fail "Inde: not supported"
  end.

Ltac forward1 :=
  match goal with
    | |- {{ ?P }} cmd_cmd0_coercion_redefined (?x <- ?e) {{ ?P ** ! (var_e ?x \= ?e )}} =>
      apply hoare_assign_forward; [Inde | idtac (* inter subgoal *) ]
    | |- {{ ?e |~> ?e' }} cmd_cmd0_coercion_redefined (?x <-* ?e) {{ ?e |~> ?e' ** ! (var_e ?x \= ?e') }} =>
      apply hoare_assign_lookup_forward; (* inter subgoals*) [idtac | idtac]
    | _ =>
      fail "forward1: not supported"
  end.

Ltac forward :=
  match goal with
    | |- hoare_m.hoare _ _ _ =>
      rewrite /hoare_m.hoare /hoare_m.store /hoare_m.heap
        /hoare_m.cmd0 /hoare_m.expr_b /hoare_m.eval_b /hoare_m.hoare0
    | _ => idtac
  end ;
  match goal with
    | |- {{ _ }} (_ ; _ ) ; _ {{ _ }} =>
      apply hoare_prop_m.hoare_seq_assoc; forward
    | |- {{ ?P }} cmd_cmd0_coercion_redefined (?x <- ?e) ; _ {{ _ }} =>
      apply while.hoare_seq with (P ** ! (var_e x \= e)); [forward1 | idtac]
    | |- {{ ?e |~> ?e' }} cmd_cmd0_coercion_redefined (?x <-* ?e) ; _ {{ _ }} =>
      apply while.hoare_seq with (e |~> e' ** ! (var_e x \= e')); [forward1 | idtac]
    | |- _ =>
      fail "forward: not supported"
  end.

End Tactics.

Module Import tactics_m := Tactics ZIT.
Import seplog_m.
Import seplog_m.assert_m.expr_m.
Import seplog_m.assert_m.

Local Open Scope Z_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.
Local Open Scope tactics_scope.

Lemma test0 : {{ TT }} O <- cst_e 1 {{ TT ** ! (var_e O \= cst_e 1) }}.
Proof. forward1. (* inter subgoal *) by apply disj_nil_L. Qed.

Lemma test1 : {{ cst_e 1 |~> cst_e 2 }} O <-* cst_e 1 {{ cst_e 1 |~> cst_e 2 ** ! (var_e O \= cst_e 2) }}.
Proof. forward1. (* inter subgoals *) by apply disj_nil_L. by apply disj_nil_L. Qed.

Lemma test2 :
  {{ cst_e 1 |~> cst_e 2 }}
  O <- cst_e 1 ; O <-* cst_e 1
  {{ cst_e 1 |~> cst_e 2 ** ! (var_e O \= cst_e 2) }}.
Proof.
forward.
exact: disj_nil_L.
exact: disj_nil_L.
exact: disj_nil_L.
apply hoare_drop_pure.
forward1.
exact: disj_nil_L.
exact: disj_nil_L.
Qed.

Lemma test3 :
  {{ cst_e 1 |~> cst_e 2 }}
  (O <- cst_e 1 ; O <-* cst_e 1) ; O <- cst_e 3
  {{ cst_e 1 |~> cst_e 2 ** ! (var_e O \= cst_e 3) }}.
Proof.
forward.
exact/disj_nil_L.
exact/disj_nil_L.
exact/disj_nil_L.
apply hoare_drop_pure.
forward.
exact/disj_nil_L.
exact/disj_nil_L.
apply hoare_drop_pure.
forward1.
exact/disj_nil_L.
exact/disj_nil_L.
exact/disj_nil_L.
Qed.

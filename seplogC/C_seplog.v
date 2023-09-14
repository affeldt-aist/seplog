(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import EqdepFacts Program.Basics.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
Require Import Init_ext ssrZ ZArith_ext String_ext seq_ext.
Require littleop.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_expr_equiv C_expr_ground.
Require Import while_bipl.

Declare Scope C_assert_scope.
Declare Scope C_cmd_scope.

Reserved Notation "P ** Q" (at level 80, right associativity).

Local Open Scope C_types_scope.
Local Open Scope C_expr_scope.

Module Type CENV.

Parameter g : wfctxt.
Parameter sigma : g.-env.
Parameter uniq_vars : uniq (unzip1 sigma).

End CENV.

Module C_Seplog_f (C_Env : CENV).

(* C programs environment *)

Definition g := C_Env.g.
Definition sigma := C_Env.sigma.
Definition uniq_sigma := C_Env.uniq_vars.

Notation "% i" := (@var_e _ sigma i _ erefl) (at level 4): C_expr_scope.

Module C_StateBipl <: StateBipl.

Definition store : Type := @C_expr.store g sigma.
Definition heap : Type := hp.t.
Definition state : Type := (store * heap)%type.

Definition expr_b : Type := @bexp g sigma.

Definition neg : expr_b -> expr_b := @bneg g sigma.

Definition eval_b : expr_b -> state -> bool := fun eb s => [ eb ]b_ (fst s).

Lemma eval_b_neg : forall t s, eval_b (neg t) s = ~~ eval_b t s.
Proof. by []. Qed.

Definition assert := store -> heap -> Prop.

End C_StateBipl.

Module C_Bipl <: Bipl C_StateBipl.

Local Open Scope heap_scope.

Include (StateBiplProp C_StateBipl).

Local Open Scope statebipl_scope.

Variant con' (P Q : assert) s : heap -> Prop :=
| con_c: forall h1 h2, h1 # h2 ->
  P s h1 -> Q s h2 -> con' P Q  s (h1 \U h2).
Definition con := nosimpl con'.
Notation "P ** Q" := (con P Q) : C_assert_scope.

Local Open Scope C_assert_scope.

Lemma conC (P Q : assert) : P ** Q <==> Q ** P.
Proof.
move => s h; split.
- case => h1 h2 h1dh2 H1 H2; rewrite hp.unionC //.
  apply con_c => //. by apply hp.disj_sym.
- case => h1 h2 h1dh2 H1 H2; rewrite hp.unionC //.
  apply con_c => //. by apply hp.disj_sym.
Qed.

Lemma conA : forall (P Q R: assert), P ** (Q ** R) <==> (P ** Q) ** R.
Proof.
move => P Q R s h; split.
- inversion 1; subst; clear H.
  inversion H2; subst; clear H2.
  rewrite hp.unionA.
  constructor => //; first by map_tac_m.Disj.
  constructor => //; first by map_tac_m.Disj.
- inversion 1; subst; clear H.
  inversion H1; subst; clear H1.
  rewrite -hp.unionA.
  constructor => //; first by map_tac_m.Disj.
  constructor => //; first by map_tac_m.Disj.
Qed.

Lemma conDl : forall P Q R, (P \\// Q) ** R <==> (P ** R) \\// (Q ** R).
Proof.
move=> P Q R s h; split.
move=> [h1 h2 h1dh2 [Hh1 | Hh1] Hh2]; [left | right]; by apply con_c.
case; move=> [h1 h2 h1dh2 Hh1 Hh2]; apply con_c => //; by [left | right].
Qed.

Lemma conDr : forall P Q R, R ** (P \\// Q) <==> (R ** P) \\// (R ** Q).
Proof.
move=> P Q R s h; split.
  case=> h1 h2 h1dh2 HR [].
    move=> HP; left; by constructor.
  move=> HQ; right; by constructor.
case.
  case=> h1 h2 h1dh2 HR HP.
  constructor => //; by left.
case=> h1 h2 h1dh2 HR HP.
constructor => //; by right.
Qed.

Lemma conFP : forall P, FF ** P <==> FF.
Proof. move=> P s h; split => //. by case. Qed.

Lemma conPF : forall P, P ** FF <==> FF.
Proof. move=> P s h; split => //. by case. Qed.

Lemma ent_R_con_T P : P ===> P ** TT.
Proof.
move=> s h HP.
rewrite -(hp.unionhe h).
constructor => //.
by apply hp.disjhe.
Qed.

Lemma con_congr : forall (P Q R S : assert), P <==> R -> Q <==> S -> P ** Q <==> R ** S.
Proof.
move => P Q R S HPR HQS s h; split => H; (
  inversion H; subst; clear H;
    constructor => //=; [ move: (HPR s h1); intuition | move: (HQS s h2); intuition]).
Qed.

Lemma monotony (P Q R S : assert) : P ===> Q -> R ===> S -> P ** R ===> Q ** S.
Proof.
move => PQ RS s h [] h1 h2 h1dh2 H1 H2.
constructor => //; by [apply PQ | apply RS].
Qed.

Lemma conCA P Q R : P ** Q ** R <==> Q ** P ** R.
Proof.
rewrite conA.
rewrite [in X in _ <==> X] conA.
apply con_congr => //.
exact: conC.
Qed.

Definition emp : assert := fun _ h => h = hp.emp.

Lemma conPe : forall (P : assert), P ** emp <==> P.
Proof.
move => P s h; split.
- inversion 1; subst; clear H.
  rewrite /emp in H2; subst h2.
  by rewrite (hp.unionhe h1).
- move=> Hp.
  rewrite -(hp.unionhe h).
  constructor => //; first by map_tac_m.Disj.
Qed.

Lemma coneP : forall (P : assert), emp ** P <==> P.
Proof. move=> P. rewrite conC. by apply conPe. Qed.

Definition imp (P Q : assert) : assert := fun s h =>
  forall h',  h' # h -> P s h' ->  Q s (h' \U h).
Notation "P -* Q" := (imp P Q) (at level 80) : C_assert_scope.

End C_Bipl.

(* inner modules setup *)

Module C_Semop0 <: WhileSemop0 C_StateBipl C_Bipl.

Include (BiplProp C_StateBipl C_Bipl).

Local Open Scope statebipl_scope.
Local Open Scope C_assert_scope.

Inductive cmd0' : Type :=
| skip : cmd0'
| assign : forall t str, env_get str sigma = |_ t _| -> exp sigma t -> cmd0'
| lookup : forall t str, env_get str sigma = |_ t _| -> exp sigma (:* t) -> cmd0'
| mutation : forall t, exp sigma (:* t) -> exp sigma t -> cmd0'.
Definition cmd0 := cmd0'.

Arguments assign [t] [str] _ _.
Arguments lookup [t] [str] _ _.
Arguments mutation [t] _ _.

Notation "'nop'" := skip (at level 80) : C_cmd_scope.
Notation "x '<-*' e" := (@lookup _ x erefl e) (at level 80) : C_cmd_scope.
Notation "x '<-' e" := (@assign _ x erefl e) (at level 80) : C_cmd_scope.
Notation "x '\+<-' e" := (@assign _ x erefl ((@var_e g sigma x _ erefl) \+ e)) (at level 80) : C_cmd_scope.
Notation "x '\++'" := (@assign _ x erefl ((@var_e g sigma x _ erefl) \+ [ 1 ]sc)) (at level 80) : C_cmd_scope.
Notation "e1 '*<-' e2" := (@mutation _ e1 e2) (at level 80) : C_cmd_scope.

Local Open Scope C_cmd_scope.

Reserved Notation " s '--' c '---->' t " (at level 74, no associativity).

Local Open Scope machine_int_scope.
Local Open Scope C_value_scope.

Inductive exec_cmd0 : option state -> cmd0 -> option state -> Prop :=
| exec_skip : forall s, |_ s _| -- skip ----> |_ s _|
| exec_assign : forall s h t str Hstr e,
  |_ s, h _| -- @assign t str Hstr e ----> |_ store_upd Hstr [ e ]_s s, h _|
| exec_lookup : forall s h t str Hstr e v,
  let a := nat<=u (ptr<=phy [ e ]_s) in
  heap_get t a h = |_ v _| ->
  |_ s, h _| -- @lookup _ str Hstr e ----> |_ store_upd Hstr v s, h _|
| exec_lookup_err : forall s h t str Hstr e,
  let a := nat<=u (ptr<=phy [ e ]_s) in
  heap_get t a h = None ->
  |_ s, h _| -- @lookup t str Hstr e ----> None
| exec_mutation : forall s h t e1 e2 v,
  let a := nat<=u (ptr<=phy [ e1 ]_s) in
  heap_get t a h = |_ v _| ->
  |_ s, h _| -- @mutation t e1 e2 ----> |_ s, heap_upd t a [ e2 ]_s h _|
| exec_mutation_err : forall s h t e1 e2,
  let a := nat<=u (ptr<=phy [ e1 ]_s) in
  heap_get t a h = None ->
  |_ s, h _| -- @mutation t e1 e2 ----> None
where "s -- c ----> t" := (exec_cmd0 s c t) : C_cmd_scope.

Definition exec0 := exec_cmd0.

Lemma from_none0 : forall (s : option state) c, None -- c ----> s -> s = None.
Proof. by inversion 1. Qed.

Lemma cmd0_terminate: forall (c : cmd0) s, exists s', Some s -- c ----> s'.
Proof.
elim.
- move=> s; exists (Some s); by apply exec_skip.
- move=> t str Hstr e [] s h.
  exists (Some (store_upd Hstr [ e ]_ s s, h)); by apply exec_assign.
- move => t str Hstr e [] s h.
  case: (option_dec (heap_get t (Z.abs_nat (u2Z (ptr<=phy [e]_s))) h)); last first.
    move=> H; exists None; by apply exec_lookup_err.
  case => val Hval.
  exists (Some (store_upd Hstr val s, h)); by apply exec_lookup.
- move => t e1 e2 [] s h.
  case: (option_dec (heap_get t (Z.abs_nat (u2Z (ptr<=phy [e1]_s))) h)); last first.
    move=> H; exists None.
    by eapply exec_mutation_err; eauto.
  case => val Hval.
  exists (Some (s, heap_upd t (Z.abs_nat (u2Z (ptr<=phy [e1]_s))) ([ e2 ]_s) h)).
  by eapply exec_mutation; eauto.
Qed.

End C_Semop0.

Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.

Module C_Hoare0 <: WhileSemax0 C_StateBipl C_Bipl C_Semop0.

Include (WhileSemaxSemantics C_StateBipl C_Bipl C_Semop0).

Import C_Semop0.

Local Open Scope C_value_scope.

Implicit Type P : assert.

Inductive wp_assign {str t} Hstr e P : assert :=
| wp_assign_c : forall s h, P (@store_upd _ _ str t Hstr [ e ]_s s) h ->
  wp_assign Hstr e P s h.

Inductive wp_lookup {str t} Hstr (e : exp sigma (:* t)) P : assert :=
| wp_lookup_c : forall s h pv,
  heap_get t (nat<=u (ptr<=phy [ e ]_ s)) h = |_ pv _| ->
  P (@store_upd _ _ str t Hstr pv s) h ->
  wp_lookup Hstr e P s h.

Inductive wp_mutation {t} (e1 : exp sigma (:* t)) e2 P : assert :=
| wp_mutation_c : forall s h v, let a := nat<=u (ptr<=phy [ e1 ]_s) in
  heap_get t a h = |_ v _| ->
  P s (heap_upd t a [ e2 ]_s h) ->
  wp_mutation e1 e2 P s h.

Notation "P '`{' x '<-' e '}''" := (@wp_assign x _ erefl e P)
  (at level 5, x, e at next level, format "'[hv ' P  '/  ' `{  x  <-  e  }' ']'") : C_assert_scope.

Notation "P '`{' x '<-*' e '}''" := (@wp_lookup _ x erefl e P)
  (at level 5, x, e at next level, format "'[hv ' P  '/  ' `{  x  <-*  e  }' ']'") : C_assert_scope.

Inductive hoare0' : assert -> cmd0 -> assert -> Prop :=
| hoare0_skip : forall P, hoare0' P skip P
| hoare0_assign : forall P t str Hstr e,
  hoare0' (wp_assign Hstr e P) (@assign t str Hstr e) P
| hoare0_lookup : forall P t str Hstr e,
  hoare0' (wp_lookup Hstr e P) (@lookup t str Hstr e) P
| hoare0_mutation : forall P t e1 e2,
  hoare0' (wp_mutation e1 e2 P) (@mutation t e1 e2) P.
Definition hoare0 := hoare0'.

Lemma soundness0 (P Q : assert) c : hoare0 P c Q -> hoare_semantics P (cmd_cmd0 c) Q.
Proof.
elim => //; clear P Q c; rewrite /hoare_semantics.
- move=> P s h P_s_h; split=> [|s' h' ]; move/exec_cmd0_inv => abs.
  + by inversion abs.
  + by inversion abs; subst.
- move=> Q ty v Hs e s h HQ; inversion HQ; subst.
  split=> [|s' h']; move/exec_cmd0_inv => abs; first by inversion abs.
  rewrite /exec0 in abs.
  inversion abs; subst.
  have ? : Hs = Hstr0 by apply eq_irrelevance. subst Hstr0.
  by rewrite (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H5).
- move=> Q ty v Hs e s h HQ; inversion HQ; subst.
  split=> [|s' h']; move/exec_cmd0_inv => abs.
  + inversion abs; subst.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H6) => {H6}Heq. subst e.
    by rewrite H2 in H.
  + inversion abs; subst.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H6) => {H6}Heq; subst e.
    rewrite H2 in H. case: H => ?; subst v0.
    have ? : Hs = Hstr0 by apply eq_irrelevance. by subst Hstr0.
- move=> Q ty e1 e2 s h HQ; inversion HQ; subst.
  split=> [|s' h']; move/exec_cmd0_inv => abs.
  + inversion abs; subst.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H6) => Heq; subst; clear H6.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H5) => Heq.
    rewrite /a0 in H2. subst e4. clear H5.
    by rewrite H in H2.
  + inversion abs.
    subst s0 h0 t.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H6) => Heq; subst e5; clear H6.
    rewrite /a1 /a in H2 H H0 H8 *.
    subst.
    move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H5) => Heq; subst; clear H5.
    by rewrite H in H2.
Qed.

End C_Hoare0.

Module C_Hoare <: WhileSemaxComplete0 C_StateBipl C_Bipl C_Semop0 C_Hoare0.

Include (WhileHoare C_StateBipl C_Bipl C_Semop0 C_Hoare0).
Import C_Semop0.
Import C_Hoare0.

Local Open Scope lang_scope.
Local Open Scope whilesemop_scope.
Local Open Scope whilehoare_scope.
Local Open Scope statebipl_scope.
Local Open Scope C_value_scope.

Definition wp0 (c: cmd0) (Q: assert) : assert :=
  match c with
    | skip => Q
    | assign t str Hstr e => wp_assign Hstr e Q
    | lookup t str Hstr e => wp_lookup Hstr e  Q
    | mutation t e1 e2 => wp_mutation e1 e2 Q
  end.

Lemma wp_semantics_sound0 : forall (c : cmd0) Q,
  {{ wp_semantics (cmd_cmd0 c) Q }} (cmd_cmd0 c) {{ Q }}.
Proof.
elim => //=.
- move => Q.
  eapply hoare_stren; last by econstructor; econstructor.
  rewrite /wp_semantics => s h [] H1 H2; apply H2.
  constructor; constructor.
- move => ty str e1 e2 Q.
  eapply hoare_stren; last by econstructor; econstructor.
  rewrite /wp_semantics => s h [] H1 H2.
  constructor; apply H2 => //=.
  constructor; constructor.
- move => t str Hstr e Q.
  eapply hoare_stren; last by econstructor; econstructor.
  rewrite /wp_semantics => s h [] H1 H2.
  case: (option_dec (heap_get t (Z.abs_nat (u2Z (ptr<=phy [ e ]_ s))) h)); last first => Hval.
    exfalso.
    apply H1.
    econstructor; by apply exec_lookup_err.
  destruct Hval.
  econstructor.
  by apply e0.
  apply H2.
  econstructor; econstructor. by [].
- move => t e1 e2 Q.
  eapply hoare_stren; last by econstructor; econstructor.
  rewrite /wp_semantics => s h [] H1 H2.
  case: (option_dec (heap_get t (Z.abs_nat (u2Z (ptr<=phy [ e1 ]_ s))) h)); last first => Hval.
  + exfalso.
    apply H1.
    by econstructor; eapply exec_mutation_err; eauto.
  + destruct Hval.
    econstructor. by apply e.
    apply H2. by econstructor; econstructor; eauto.
Qed.

Lemma wp0_no_err : forall s h c P, wp0 c P s h -> ~ (Some (s, h) -- c ----> None).
Proof.
move => s h; elim => //=.
- move => P HP Hexec.
  inversion Hexec.
- move => t str e e0 P Hwp_assign; by inversion 1.
- move => t str e e0 P Hwp_lookup Hexec.
  inversion Hwp_lookup; subst; clear Hwp_lookup.
  inversion Hexec; subst => //=.
  apply Eqdep.EqdepTheory.inj_pair2 in H6; subst e0.
  by rewrite H2 in H.
- move => t e e0 P Hwp_mutation Hexec.
  inversion Hwp_mutation; subst; clear Hwp_mutation.
  inversion Hexec; subst; clear Hexec.
  apply Eqdep.EqdepTheory.inj_pair2 in H6; subst e4.
  unfold a, a0 in *.
  apply Eqdep.EqdepTheory.inj_pair2 in H5; subst e3.
  by rewrite H in H2.
Qed.

End C_Hoare.

(* building outmost C language representation and reasoning  *)

Module C_definition := WhileSemaxComplete C_StateBipl C_Bipl C_Semop0 C_Hoare0 C_Hoare.
Import C_definition.
Export C_definition.

Open Scope lang_scope.
Open Scope whilesemop_scope.
Open Scope statebipl_scope.
Open Scope whilehoare_scope.

Import C_Semop0.
Export C_Semop0.

Import C_Hoare0.
Export C_Hoare0.

Module Import map_tac_m := finmap.Map_Tac hp.
Export map_tac_m.

(* base assertions *)

Open Scope C_value_scope.
Open Scope heap_scope.
Open Scope C_value_scope.
Open Scope C_assert_scope.
Open Scope C_expr_scope.

(* instances *)

Goal forall P Q T,
  Q ===> P ->
  Q ===> T.
move => P Q T HQP.
Fail setoid_rewrite HQP.
Abort.

#[global] Instance entail_partial : RelationClasses.PreOrder entails.
constructor.
abstract (move => P s h; by []).
abstract (move => x y z; apply ent_trans).
Defined.

Goal forall P Q T,
  Q ===> P ->
  Q ===> T.
move => P Q T HQP.
setoid_rewrite HQP.
Abort.

Goal forall P Q T,
  Q ===> P ->
  con Q Q ===> con P T.
move => P Q T HQP.
Fail setoid_rewrite HQP.
Abort.

#[global] Instance con_morphism : Morphisms.Proper (entails ++> entails ++> entails) con.
move => P P' HP Q Q' HQ s h; by apply monotony.
Qed.

Goal forall P Q T,
  Q ===> P ->
  T ===> P ->
  con Q Q ===> con P T.
move => P Q T HQP HTP.
setoid_rewrite HQP.
Fail setoid_rewrite HTP.
Abort.

#[global] Instance entails_morphism2: Morphisms.Proper (entails ++> entails --> flip impl) entails.
move => P P' HP Q Q' HQ.
move => HPQ.
move => s h H.
apply/HQ.
apply/HPQ.
by apply/HP.
Qed.

#[global] Instance entails_morphism3 : Morphisms.Proper (entails --> entails ++> impl) entails.
move=> P P' P'_P Q Q' Q_Q' P_Q s h H; by apply/Q_Q'/P_Q/P'_P.
Qed.

#[global] Instance entails_morphism: Morphisms.Proper (equiv ==> equiv ==> iff) entails.
constructor.
- move => H1 s h Hy.
  apply/H0.
  apply/H1.
  by apply/H.
- move => H1 s h Hy.
  apply/H0.
  apply/H1.
  by apply/H.
Qed.

#[global] Instance assert_abelean : littleop.Abelian con.
eapply littleop.Build_Abelian with (equiv := equiv) (zero := emp).
exact equiv_equivalence.
exact conPe.
exact conC.
exact conA.
abstract (move => P Q HPQ R S HRS; by apply con_congr).
Defined.

#[global] Instance is_true_true_morphism: Morphisms.Proper (eq ==> iff) is_true.
move => b1 b2 ->; by [].
Qed.

#[global] Instance triple_morphism: Morphisms.Proper (Morphisms.respectful equiv (Morphisms.respectful eq (Morphisms.respectful equiv iff))) hoare.
move => P P' HPP' c c' Hcc' Q Q' HQQ'.
subst c'.
split; eapply hoare_conseq.
by rewrite HQQ'.
by rewrite HPP'.
by rewrite HQQ'.
by rewrite HPP'.
Qed.

#[global] Instance triple_morphism2: Morphisms.Proper (Morphisms.respectful (flip entails) (Morphisms.respectful eq (Morphisms.respectful entails impl))) hoare.
move => P P' HPP' c c' Hcc' Q Q' HQQ'.
subst c'.
move => H.
eapply hoare_conseq.
apply HQQ'.
apply HPP'.
exact H.
Qed.

Local Open Scope C_types_scope.

#[global] Instance wp_assign_morphism {ty : g.-typ} str (Hstr : assoc_get str sigma = Some ty) e :
  Morphisms.Proper (equiv ==> equiv) (wp_assign Hstr e).
move=> R R' RR' s h; split; inversion_clear 1; by apply wp_assign_c, RR'.
Qed.

#[global] Instance Or_morphism: Morphisms.Proper (equiv ==> equiv ==> equiv) Or.
move => P P' HP Q Q' HQ s h; split.
- move => H.
  inversion_clear H.
  - by left; apply/HP.
  - by right; apply/HQ.
- move => H.
  inversion_clear H.
  - by left; apply/HP.
  - by right; apply/HQ.
Qed.

Notation "a '|lZ~>' v" := (fun _ : store => @log_mapsto _ _ v a) (at level 77, no associativity) : C_value_scope.

Notation "a '|lV~>' v" := (fun _ : store => log_mapsto v (Z.abs_nat (Z<=u (ptr<=phy a)))) (at level 77, no associativity) : C_value_scope.

Import C_Bipl.
Export C_Bipl.

(** bang *)

Definition bang (P : store -> Prop) : assert :=
  fun s h => P s /\ emp s h.
Notation "! P " := (bang P) (at level 4) : C_assert_scope.

Lemma con_and_bang_R (P : assert) (Q : store -> Prop) :
  P ** !(Q) <==> P //\\ (fun s _ => Q s).
Proof.
move=> s h; split.
- case=> h1 h2 h1_d_h2 Hh1 [HQ ->]. by rewrite hp.unionhe.
- case=> HP HQ.
  rewrite -(hp.unionhe h).
  apply con_c => //.
  exact: hp.disjhe.
Qed.

Lemma bang_dup p : !( p ) <==> !( p ) ** !( p ).
Proof.
move=> s h; split => /=.
  case=> Hp; rewrite /emp; move=> ->.
  rewrite -(hp.unioneh hp.emp).
  apply con_c => //; by apply hp.disjhe.
case=> h1 h2 _ [Hh1 H1] [Hh2 H2].
rewrite /emp in H1 H2; subst h1 h2.
by rewrite hp.unionhe.
Qed.

Lemma ent_bang_contract p : !( p ) ===> emp.
Proof. by move=> s h []. Qed.

Lemma bang_intro_con_R P Q : !(P) ===> !(Q) -> (fun s _ => P s) ===> !(Q) ** TT.
Proof.
move=> H s h HP.
rewrite -(hp.unioneh h).
apply con_c => //; by [apply hp.disjeh | apply H].
Qed.

Lemma ent_bang_bang (P Q : store -> Prop) : (forall s, P s -> Q s) -> !(P) ===> !(Q).
Proof.
move=> H s h [] HP; rewrite /bang => ->; split => //; by apply H.
Qed.

(** sbang *)

Definition sbang (P: Prop): assert := fun _ h => P /\ h = hp.emp.

Notation "!!( P )" := (sbang P) (at level 72) : C_assert_scope.

Lemma sbang_emp (P : Prop) : P -> !!( P ) <==> emp.
Proof.
move=> H s h; split; first by by case.
by rewrite /emp => ->.
Qed.

Lemma ent_sbang_sbang (P Q : Prop) : (P -> Q) -> !!( P ) ===> !!( Q ).
Proof. move=> *. by apply ent_bang_bang. Qed.

Lemma ent_R_sbang : forall P : Prop, P -> emp ===> !!( P ).
Proof. by []. Qed.

Lemma sbang_entails_FF P : ~ P -> !!( P ) ===> FF.
Proof. move=> H s h [] Psh _. by apply H. Qed.

Lemma sbang_dup (P : Prop) : !!(P) <==> !!(P) ** !!(P).
Proof. apply bang_dup. Qed.

Lemma sbang_dup2 {b} (P : assert) (Heq : P = !!(b)) : P <==> P ** P.
Proof. by rewrite !Heq; apply sbang_dup. Qed.

Lemma sbang_con P Q : !!( P ) ** !!( Q ) <==> !!( P /\ Q ).
Proof.
move=> s h; split.
- case=> h1 h2 _ [] HP -> [] HQ ->; by rewrite hp.unioneh.
- case; case=> HP HQ ->.
  rewrite -(hp.unioneh hp.emp).
  apply con_c => //.
  exact/hp.disjeh.
Qed.

Lemma ent_sbang_contract (P : Prop) : !!( P ) ===> emp.
Proof. apply ent_bang_contract. Qed.

Lemma ent_sbang_contract2 {b} (P : assert) (Heq : P = !!(b)) : P ===> emp.
Proof. by rewrite !Heq; apply ent_sbang_contract. Qed.

Lemma ent_R_sbang_con P (Q : Prop) R : Q -> P ===> R -> P ===> !!( Q ) ** R.
Proof.
move=> q PR; rewrite -(coneP P).
apply monotony; [by apply ent_R_sbang | exact PR].
Qed.

Lemma ent_sbang_L (Q : Prop) R : (Q -> emp ===> R) -> !!( Q ) ===> R.
Proof. move=> QPR s h [] HQ ->. by apply QPR. Qed.

Lemma ent_L_sbang_con P (Q : Prop) R : (Q -> P ===> R) -> !!( Q ) ** P ===> R.
Proof.
move=> QPR s h [] h1 h2 h1dh2 [] HQ' ->.
rewrite hp.unioneh.
by apply QPR.
Qed.

Lemma ent_L_sbang_con2 P (Q : Prop) R : (Q -> P ===> R) -> P ** !!( Q ) ===> R.
Proof. move=> H. rewrite conC. by apply ent_L_sbang_con. Qed.

Lemma con_sbang_L (P : Prop) Q : P -> !!( P ) ** Q <==> Q.
Proof.
move=> H s h; split => [|K].
  apply ent_L_sbang_con => _; by apply ent_id.
rewrite -(hp.unioneh h).
apply con_c => //; by apply hp.disjeh.
Qed.

Lemma con_sbang_R (P : Prop) Q : P -> Q ** !!( P ) <==> Q.
Proof. move=> H. rewrite conC. by apply con_sbang_L. Qed.

(** bbang *)

Definition bbang (b: @bexp g sigma) := bang (beval b).
Definition nosimpl_bbang := nosimpl bbang.
Notation "'`!' b" := (nosimpl_bbang b) (at level 72) : C_assert_scope.

Lemma bbang1 : `! \b [ 1 ]uc <==> emp.
Proof.
move=> s h; split.
  by move/proj2.
rewrite /emp => ->.
split; last by [].
Transparent beval.
by rewrite /= not_is_zero_1.
Opaque beval.
Qed.

Lemma bbang_0 : `! \b [ 0 ]uc <==> FF.
Proof.
Transparent beval eval.
move=> s h; split => //.
case.
by rewrite /= is_zero_0.
Opaque beval eval.
Qed.

Lemma ent_emp_bbang_pe {t} (a b : exp sigma (:* t)) :
  a =s b -> emp ===> `! \b a \= b.
Proof.
move=> a_b s h.
rewrite /emp => ->; split => //.
rewrite a_b beq_pxx ground_bexp_sem; by apply oneuc.
Qed.

Lemma ent_emp_bbang_re {t} (a b : exp sigma (g.-ityp: t)) :
  a =s b -> emp ===> `! \b a \= b.
Proof.
move=> a_b s h.
rewrite /emp => ->; split => //.
rewrite a_b beq_exx ground_bexp_sem; by apply oneuc.
Qed.

Lemma bbang_dup (b : bexp sigma) : `! b <==> `! b ** `! b.
Proof. apply bang_dup. Qed.

Lemma bbang_dup2 {b : bexp sigma} (P : assert) (Heq : P = `! b) : P <==> P ** P.
Proof. rewrite !Heq. apply bbang_dup. Qed.

Lemma ent_bbang_contract (b : bexp sigma) : `! b  ===> emp.
Proof. apply ent_bang_contract. Qed.

Lemma ent_bbang_contract2 {b : bexp sigma} (P : assert) (Heq : P = `! b) : P ===> emp.
Proof. rewrite !Heq. apply ent_bang_contract. Qed.

Lemma ent_L_bbang Q R : emp ===> R -> `! Q ===> R.
Proof. apply ent_trans, ent_bang_contract. Qed.

Lemma ent_L_bbang_con P Q R : P ===> R -> `! Q ** P ===> R.
Proof.
move=> H; rewrite -(coneP R).
apply monotony => //; apply ent_L_bbang, ent_id.
Qed.

Lemma ent_L_con_bbang P Q R : P ===> R -> P ** `! Q ===> R.
Proof. move=> H; rewrite conC; by apply ent_L_bbang_con. Qed.

Lemma bbang_contradict b : `! b ** `! \~b b <==> FF.
Proof.
apply equiv_def; split; last by apply ent_L_F.
move=> s h [] h1 h2 h1dh2 [H1 Hh1] [H2 Hh2].
by rewrite beval_neg_not H1 in H2.
Qed.

Lemma bbang_contradict' b : `! \~b b ** `! b <==> FF.
Proof. rewrite conC; apply bbang_contradict. Qed.

#[global] Instance bbang_morphism : Morphisms.Proper (bequiv ==> equiv) bbang.
move=> b1 b2 b12 s h; split; case=> H1 H2.
  split => //; by rewrite -b12.
split => //; by rewrite b12.
Qed.

Lemma bbang_eq_exx {t} (e : exp sigma (ityp: t)) : `! \b e \= e <==> emp.
Proof. by rewrite beq_exx bbang1. Qed.

Lemma bbang_eqpxx {t} (e : exp sigma (:* t)) : `! \b e \= e <==> emp.
Proof. by rewrite beq_pxx bbang1. Qed.

Lemma bbang_eqi_store_get str t s (e : exp sigma (ityp: t))
  (str_t : assoc_get str sigma = Some (ityp: t)) h :
  (`! \b var_e _ _ (ityp: t) str_t \= e ) s h ->
  store_get str_t s = [ e ]_ s.
Proof. case. rewrite beval_eq_e_eq. by move/eqP => <-. Qed.

Lemma bbang_eqp_store_get str (t : g.-typ) s (e : exp sigma (:* t))
  (str_t : assoc_get str sigma = Some (:* t)) h :
  ( `! \b var_e _ _ _ str_t \= e ) s h ->
  store_get str_t s = [ e ]_ s.
Proof. case. rewrite beval_eq_p_eq. by move/eqP => <-. Qed.

Lemma bbang_bneg_or1 (e1 e2 : exp sigma (ityp: uint)) :
  `! \~b \b e1 \|| e2 ===> `! \~b \b e1 ** `! \~b \b e2.
Proof.
move=> s h [] H.
rewrite /emp => ->.
rewrite -(hp.unioneh hp.emp).
move/negPn : H.
case/is_zero_or => H1 H2.
apply con_c.
Transparent beval.
- by apply hp.disjeh.
- split; last by [].
  simpl; by apply/negPn.
- split; last by [].
  simpl; exact/negPn.
Opaque beval.
Qed.

Lemma bbang_bneg_or2 (e1 e2 : exp sigma (ityp: uint)) :
  `! \~b \b e1 ** `! \~b \b e2 ===> `! \~b \b e1 \|| e2.
Proof.
move=> s h [] h1 h2 h1dh2 [] Hh1.
rewrite /emp => ->.
case=> Hh2.
rewrite /emp => ->.
rewrite hp.unioneh.
split; last by [].
rewrite beval_neg_not.
rewrite 2!beval_neg_not in Hh1 Hh2.
apply/negPn.
move/negPn in Hh1; move/negPn in Hh2.
by apply is_zero_or2.
Qed.

Lemma bbang_bneg_or (e1 e2 : exp sigma (ityp: uint)) :
  `! \~b \b e1 ** `! \~b \b e2 <==> `! \~b \b e1 \|| e2.
Proof. apply equiv_def; split; [apply bbang_bneg_or2 | apply bbang_bneg_or1]. Qed.

Lemma bbang_and (e1 e2 : exp sigma (ityp: uint)):
  `! \b e1 ** `! \b e2 <==> `! \b e1 \&& e2.
Proof.
apply equiv_def; split.
- move=> s h [] h1 h2 h1dh2 [H1 ->] [H2 ->].
  rewrite hp.unioneh.
  split => //.
  by rewrite beval_land_e H1 H2.
- move=> s h [H ->].
  rewrite -(hp.unioneh hp.emp).
  rewrite beval_land_e in H.
  case/andP : H => H1 H2.
  apply con_c => //.
  exact/hp.disjhe.
Qed.

Lemma bbang_sc_lt_e_sbang a b :
  - 2 ^^ 31 <= a < 2 ^^ 31 -> - 2 ^^ 31 <= b < 2 ^^ 31 ->
  `! \b [ a ]sc \< ([ b ]sc : exp sigma (ityp: sint)) <==> !!( a < b ).
Proof.
Transparent eval beval.
move=> Ha Hb s h; split.
  case=> H Hh.
  split => //.
  move: H.
  rewrite /= !i8_of_i32K !Z2sK //.
  case: ifP => //.
  by move/ltZP.
  by rewrite is_zero_0.
case=> H Hh.
split=> //.
rewrite /= !i8_of_i32K !Z2sK //.
case: ifP => //.
by rewrite not_is_zero_1.
by move/ltZP.
Opaque eval beval.
Qed.

Lemma bbang_sc_le_e_sbang a b :
  - 2 ^^ 31 <= a < 2 ^^ 31 -> - 2 ^^ 31 <= b < 2 ^^ 31 ->
  `! \b [ a ]sc \<= ([ b ]sc : exp sigma (ityp: sint)) <==> !!(a <= b).
Proof.
Transparent eval beval.
move=> Ha Hb s h; split.
  case=> H Hh.
  split => //.
  move: H.
  rewrite /= !i8_of_i32K !Z2sK //.
  case: ifP => //.
  by move/leZP.
  by rewrite is_zero_0.
case=> H Hh.
split=> //.
rewrite /= !i8_of_i32K !Z2sK //.
case: ifP => //.
by rewrite not_is_zero_1.
by move/leZP.
Opaque eval beval.
Qed.

(** mapstos *)

Fixpoint mapstos {t : g.-typ} (e : exp sigma (:* t))
  (l : seq (t.-phy)) : assert :=
  if l is hd :: tl then
    (e |pe~> hd ** mapstos (e \+ [ 1 ]sc) tl )
  else
    emp.

Notation "e '|-->' l" := (mapstos e l) (at level 77) : C_assert_scope.

Local Open Scope zarith_ext_scope.

Lemma mapstos_cons {t : g.-typ} (e : exp sigma (:* t)) : forall tl hd,
  e |--> hd :: tl <==> e |pe~> hd ** (e \+ [ 1 ]sc) |--> tl.
Proof. by []. Qed.

Lemma mapstos_ext0 {t : g.-typ} (e1 e2 : exp sigma (:* t)) s h (x : seq (t.-phy)) :
  [ e1 ]_ s = [ e2 ]_ s -> (e1 |--> x) s h -> (e2 |--> x) s h.
Proof.
elim: x e1 e2 s h => // hd tl IH e1 e2 s h e12 /=.
case=> h1 h2 h1dh2 Hh1 Hh2; apply con_c => //.
by rewrite -e12.
move: Hh2; apply IH.
Transparent eval.
rewrite /=.
Opaque eval.
by rewrite e12.
Qed.

Lemma mapstos_ext {t : g.-typ} (e1 e2 : exp sigma (:* t))
  (e12 : e1 =s e2) (x : seq (t.-phy)) : e1 |--> x <==> e2 |--> x.
Proof. move=> s h; split; by apply mapstos_ext0. Qed.

#[global] Instance plus_pointer_morphism_mapstos {ty : g.-typ} :
  Morphisms.Proper (sequiv ==> eq ==> equiv) (@mapstos ty).
rewrite /Morphisms.Proper.
rewrite /Morphisms.respectful.
move=> e1 e2 e12 x y xy; subst y.
exact/mapstos_ext.
Qed.

Lemma add_pe_n_1 {t : g.-typ} (e : exp sigma (:* t)) n (l : seq (t.-phy)) :
  Z_of_nat ((n.+1 + size l) * sizeof t) < 2 ^^ 31 ->
  e \+ [Z_of_nat n ]sc \+ [1 ]sc |--> l ===>
  e \+ [Z_of_nat n.+1 ]sc |--> l.
Proof.
move=> l1l2_ub.
have {}l1l2_ub : Z_of_nat n * Z_of_nat (sizeof t) +
  Z_of_nat (sizeof t) +
  Z_of_nat (size l) * Z_of_nat (sizeof t) < 2 ^^ 31.
  by rewrite inj_mult inj_plus [size _]/= Z_S 2!Zmult_plus_distr_l mul1Z in l1l2_ub.
rewrite CaddnpA //.
- rewrite sequiv_add_e_sc //.
  + by rewrite Z_S addZC.
  + split.
      apply (@leZ_trans 0) => //; exact: Zle_0_nat.
    apply: (leZ_ltZ_trans _ l1l2_ub).
    rewrite addZC; apply leZ_addl.
    * rewrite -inj_mult; by apply Zle_0_nat.
    * rewrite addZC; apply leZ_addl.
      - exact: Zle_0_nat.
      - apply Zle_scale; [exact: Zle_0_nat | exact/Z_of_nat_lt0/sizeof_gt0].
  + split.
      apply (@leZ_trans 0) => //.
      rewrite -Z_S; exact: Zle_0_nat.
    apply: leZ_ltZ_trans; last exact: l1l2_ub.
    rewrite [X in _ <= X]addZC; apply leZ_addl.
    * rewrite -inj_mult; exact: Zle_0_nat.
      apply leZ_add.
      - apply Zle_scale; first exact: Zle_0_nat.
        exact/Z_of_nat_lt0/sizeof_gt0.
      rewrite (_ : 1 = Z<=nat 1) //; exact/inj_le/leP/sizeof_gt0.
- split.
    rewrite -inj_mult; exact/Zle_0_nat.
  apply: leZ_ltZ_trans; last exact/l1l2_ub.
  rewrite -addZA addZC.
  apply leZ_addl.
    rewrite -inj_mult -inj_plus; exact/Zle_0_nat.
  by rewrite mulZC; apply leZZ.
- split.
    rewrite mulZ1; exact: Zle_0_nat.
  apply: (leZ_ltZ_trans _ l1l2_ub).
  rewrite addZC addZA.
  apply leZ_addl.
    rewrite -2!inj_mult -inj_plus; exact: Zle_0_nat.
  rewrite mulZ1; exact/leZZ.
- rewrite mulZ1.
  split.
    rewrite -inj_mult -inj_plus; exact: Zle_0_nat.
  apply: (leZ_ltZ_trans _ l1l2_ub).
  rewrite [X in _ <= X]addZC.
  apply leZ_addl.
    rewrite -inj_mult; exact: Zle_0_nat.
  rewrite mulZC; exact: leZZ.
Qed.

Lemma mapstos_cat {t : g.-typ} : forall n (l1 l2 : seq (t.-phy))
  (e : exp sigma (:* t)), size l1 = n ->
  Z_of_nat (size (l1 ++ l2) * sizeof t) < 2 ^^ 31 ->
  e |--> l1 ++ l2 ===> e |--> l1 ** e \+ [ Z_of_nat n ]sc |--> l2.
Proof.
elim.
  case=> // l2 e _ l2_ub.
  rewrite cat0s /= conC conPe.
  by setoid_rewrite -> sequiv_add_pe_0.
move=> n IH [|h1 t1] // l2 e [Hn] l1l2_ub.
rewrite cat_cons mapstos_cons mapstos_cons -conA.
apply monotony_L => s h H.
have l1l2_ub' : Z_of_nat (size (t1 ++ l2) * sizeof t) < 2 ^^ 31.
  rewrite size_cat inj_mult inj_plus [size _]/= Z_S 2!Zmult_plus_distr_l mul1Z in l1l2_ub.
  rewrite size_cat inj_mult inj_plus Zmult_plus_distr_l; lia.
move: (IH t1 l2 (e \+ [1]sc) Hn l1l2_ub' s h H); apply monotony_L.
rewrite eq_pC_const.
eapply add_pe_n_1; eauto.
by rewrite size_cat [size _]/= Hn in l1l2_ub.
Qed.

Lemma mapstos_upper_bound {t} hd tl (e : exp sigma (:* t)) s h :
  (e |--> hd :: tl) s h ->
  (u2Z (ptr<=phy ([ e ]_s)) < 2 ^^ ptr_len)%Z.
Proof.
move=> H.
rewrite /= in H.
case: H => h1 h2 h1dh2 Hh1 Hh2.
inversion Hh1; subst.
rewrite Z_of_nat_Zabs_nat in H1; last by apply min_u2Z.
move: H1.
set tmp := Z<=u _.
move=> ?; lia.
Qed.

(** mapstos_fit *)

Definition mapstos_fit {t : g.-typ} (e : exp sigma (:* t)) l : assert :=
  (e |--> l) **
  !(fun s => u2Z (ptr<=phy [ e ]_ s) + Z_of_nat (sizeof t * size l) < 2 ^^ ptr_len).
Notation "e '|--->' l" := (mapstos_fit e l) (at level 77) : C_assert_scope.

Lemma mapstos_fit_ext0 {ty : g.-typ} (e1 e2 : exp sigma (:* ty)) s h (x : seq (ty.-phy)) :
  [ e1 ]_ s = [ e2 ]_ s -> (e1 |---> x) s h -> (e2 |---> x) s h.
Proof.
move=> e12.
rewrite /mapstos_fit.
case=> h1 h2 h1dh2 Hh1 Hh2.
apply con_c => //.
by eapply mapstos_ext0; eauto.
case: Hh2 => Hh2 H; rewrite /emp in H; subst h2.
split=> //.
by rewrite e12 in Hh2.
Qed.

Lemma mapstos_fit_ext {ty : g.-typ} (e1 e2 : exp sigma (:* ty))
  (e12 : e1 =s e2) (x : seq (ty.-phy)) : e1 |---> x <==> e2 |---> x.
Proof. move=> s h; split; by apply mapstos_fit_ext0. Qed.

#[global] Instance plus_pointer_morphism_mapstos_fit {ty : g.-typ} :
  Morphisms.Proper (sequiv ==> eq ==> equiv) (@mapstos_fit ty).
rewrite /Morphisms.Proper.
rewrite /Morphisms.respectful.
move=> e1 e2 e12 x y xy; subst y.
exact/mapstos_fit_ext.
Qed.

Lemma mapstos_fit_nil_emp {t : g.-typ} (e : exp sigma (:* t)) :
  (e |---> nil) ===> emp.
Proof.
move=> s h.
case=> h1 h2 h1dh2 Hh1 Hh2.
rewrite Hh1.
case: Hh2 => _. rewrite /emp => ->.
by rewrite hp.unioneh.
Qed.

Lemma emp_mapstos_fit_nil {t : g.-typ} (e : exp sigma (:* t)) s h :
  u2Z (ptr<=phy [e ]_ s) < 2 ^^ ptr_len ->
  emp s h -> (e |---> nil) s h.
Proof.
move=> H.
rewrite /emp => ->.
rewrite -(hp.unioneh hp.emp).
apply con_c => //.
by apply hp.disjeh.
split => //.
by rewrite [size _]/= muln0 [Z_of_nat _]/= addZ0.
Qed.

Lemma mapstos_fit_mapstos_nil {t : g.-typ} (l : seq (t.-phy)) (e : exp sigma (:* t)) :
  e |---> l <==> e |---> nil ** e |---> l.
Proof.
split.
  case=> h1 h2 h1dh2 Hh1 [Hh2 H2]; rewrite /emp in H2; subst h2.
  rewrite hp.unionC; last by apply hp.disjhe.
  apply con_c => //.
  by apply hp.disj_sym.
  apply emp_mapstos_fit_nil => //.
  move: Hh2. set tmp := Z<=u _ => h2; lia.
  rewrite /mapstos_fit -(hp.unionhe h1); by apply con_c.
case=> h1 h2 h1dh2 Hh1 Hh2.
rewrite /mapstos_fit hp.unionC //; apply con_c => //.
by apply hp.disj_sym.
case: Hh2 => h21 h22 h21dh22 Hh21 Hh22.
case: Hh22 => Hh22 H; rewrite /emp in H; subst h22.
by rewrite hp.unionhe.
case: Hh1 => h11 h12 h11dh12 Hh11 Hh12.
case: Hh12 => Hh12 H; rewrite /emp in H; subst h12.
rewrite hp.unionhe.
split => //.
case: Hh2 => h21 h22 h21dh22 Hh21 Hh22.
case: Hh22 => Hh22 H; rewrite /emp in H; by subst h22.
Qed.

Lemma mapstos_fit_cons {t : g.-typ} (e : exp sigma (:* t)) hd tl :
  e |---> hd :: tl <==> e |---> hd :: nil ** e \+ [1 ]sc |---> tl.
Proof.
move=> s h; split.
  rewrite {1}/mapstos_fit.
  inversion 1 as [h1 h2 h1dh2 Hh1 Hh2 H1].
  rewrite /= in Hh1.
  inversion Hh1 as [h11 h12 h11dh12 Hh11 Hh12 H2].
  rewrite -hp.unionA.
  apply con_c=> //.
  - apply hp.disjhU => //.
    subst h1.
    by map_tac_m.Disj.
  - rewrite /mapstos_fit -(hp.unionhe h11).
    apply con_c => //.
      by apply hp.disjhe.
    rewrite /= -(hp.unionhe h11).
    apply con_c => //.
      by apply hp.disjhe.
    split=> //.
    case: Hh2 => Hh2 H'.
    rewrite [size _]/= mulnS inj_plus in Hh2.
    rewrite [size _]/= muln1; lia.
  - case: Hh2 => Hh2 H'. rewrite /emp in H'; subst h2.
    rewrite /mapstos_fit.
    apply con_c => //.
      by apply hp.disjhe.
    split=> //.
    rewrite [size _]/= mulnS inj_plus in Hh2.
    rewrite u2Z_ptyp2ptr_1; lia.
case=> h1 h2 h1dh2 Hh1 Hh2.
rewrite /mapstos_fit -(hp.unionhe (h1 \U h2)).
apply con_c => //=.
  by apply hp.disjhe.
  apply con_c => //.
    case: Hh1 => h11 h12 h11dh12 Hh11 Hh12.
    case: Hh12 => Hh12 H; rewrite /emp in H; subst h12.
    simpl in Hh11.
    case: Hh11 => h111 h112 h111dh112 Hh111 Hh112.
    rewrite /emp in Hh112; subst h112.
    by rewrite !hp.unionhe.
  case: Hh2 => h21 h22 h21dh22 Hh21 Hh22.
  case : Hh22 => Hh22 H; rewrite /emp in H; subst h22.
  by rewrite hp.unionhe.
split=> //.
case: Hh2 => h21 h22 h21dh22 Hh21 Hh22.
case : Hh22 => Hh22 H; rewrite /emp in H; subst h22.
rewrite [size _]/= mulnS inj_plus.
rewrite u2Z_ptyp2ptr_1 in Hh22; last first.
  case : Hh1 => h11 h12 h11dh12 Hh11 Hh12.
  case: Hh12 => Hh12 H.
  by rewrite [size _]/= muln1 in Hh12.
by rewrite addZA.
Qed.

Lemma mapstos_fit_con {t : g.-typ} : forall n (l1 l2 : seq (t.-phy))
  (e : exp sigma (:* t)), size l1 = n ->
  (Z<=nat (size (l1 ++ l2) * sizeof t) < 2 ^^ 30)%Z ->
  e |---> l1 ** e \+ [ Z_of_nat n ]sc |---> l2 ===> e |---> l1 ++ l2.
Proof.
elim.
  case=> // l2 e _ l2_ub.
  rewrite -> mapstos_fit_nil_emp.
  rewrite cat0s /= coneP => s h.
  apply mapstos_fit_ext => s'.
  by rewrite add_p_0.
move=> n IH [|hd1 tl1] // l2 e [Hn] l1l2_ub s h H.
case: H => h1 h2 h1dh2 Hh1 Hh2.
rewrite /mapstos_fit in Hh1.
case/con_and_bang_R : Hh1 => Hh1 Hh1_fit.
rewrite /= in Hh1.
inversion Hh1 as [h11 h12 h11dh12 Hh11 Hh12 h11Uh12].
rewrite -hp.unionA cat_cons.
apply (proj2 (mapstos_fit_cons _ _ _ _ _)).
have Hsize_ty_fit : (0 <= Z_of_nat (sizeof t) < 2 ^^ ptr_len)%Z.
  split.
    by apply Zle_0_nat.
  apply: leZ_ltZ_trans; last by apply Hh1_fit.
  rewrite /= inj_mult Z_S.
  move: (min_u2Z (ptr<=phy [e ]_ s)) => ?.
  rewrite Zmult_plus_distr_r mulZ1 addZA -inj_mult; lia.
move A2 : ([e ]_ s) => a2.
destruct a2 as [a2 Ha2] => /=.
have Ha2' : size a2 = sizeof_ptr by move: (Ha2); rewrite sizeof_ptyp.
apply con_c.
- apply hp.disjhU => //.
  rewrite -h11Uh12 in h1dh2.
  by case/hp.disj_sym/hp.disj_union_inv : h1dh2 => /hp.disj_sym.
- rewrite /mapstos_fit.
  apply con_and_bang_R; split.
  + rewrite /mapstos; by apply (equiv_imp2 _ _ (conPe _)).
  + rewrite (_ : size _ = 1%nat) // muln1.
    inversion Hh11.
    rewrite Z_of_nat_Zabs_nat // in H1; by apply min_u2Z.
apply IH => //.
- apply: leZ_ltZ_trans; last exact: l1l2_ub.
  rewrite /= 2!inj_mult.
  apply leZ_wpmul2r; first exact: Zle_0_nat.
  rewrite Z_S; lia.
- apply con_c => //.
  + rewrite -h11Uh12 in h1dh2.
    by case/hp.disj_sym/hp.disj_union_inv : h1dh2 => _ /hp.disj_sym.
  + apply con_and_bang_R; split; first exact Hh12.
    apply: leZ_ltZ_trans; last by apply Hh1_fit.
    apply Zeq_le.
    rewrite /= 2!inj_mult Z_S.
    set lhs := Z<=u _.
    suff : (lhs = u2Z (ptr<=phy [e ]_ s) + Z_of_nat (sizeof t))%Z by move=> ->; ring.
    rewrite /lhs {lhs}.
    apply u2Z_ptyp2ptr_1.
    clear -Hh1_fit Hn.
    rewrite inj_mult [size _]/= Hn Z_S in Hh1_fit.
    apply: leZ_ltZ_trans; last by apply Hh1_fit.
    apply leZ_add2l.
    rewrite mulZDr mulZ1.
    apply leZ_addl; last exact: leZZ.
    rewrite -inj_mult; exact: Zle_0_nat.
Transparent eval.
move: Hh2.
apply mapstos_fit_ext0.
rewrite [n.+1] lock /= -lock A2 3!i8_of_i32K.
case/optr_of_i8_Some : Ha2' => la2 Hla2.
rewrite (optr_of_i8_bij3 _ _ _ Hla2) [X in _ = X]/= i8_of_ptrK.
have Htmp :  (Z<=nat n.+1 < 2 ^^ 31)%Z.
  apply (@leZ_ltZ_trans (Z_of_nat (size ((hd1 :: tl1) ++ l2) * sizeof t))%Z).
    rewrite inj_mult -[X in (X <= _)%Z]Zmult_1_r.
    apply leZ_pmul => //.
      rewrite size_cat [size _]/= inj_plus Hn addZC.
      apply leZ_addl; by [apply Zle_0_nat | apply leZZ].
    rewrite (_ : 1%Z = Z_of_nat 1) //.
    apply/inj_le/leP; exact: sizeof_gt0.
  apply: ltZ_trans; eauto.
  by [].
have Htmp2 : s2Z (Z2s 32 (Z_of_nat n.+1)) = Z_of_nat n.+1 by rewrite Z2sK.
have Htmp3 : s2Z (Z2s 32 (Z_of_nat n)) = Z_of_nat n.
  rewrite Z2sK //; split.
    apply (@leZ_trans Z0) => //; by apply Zle_0_nat.
  apply: ltZ_trans; last by apply Htmp.
  rewrite Z_S; lia.
rewrite add_prodA.
- congr (phy<=ptr _ (add_prod _ _ _)).
  rewrite Htmp2 s2Z_add.
    by rewrite Z2sK // Htmp3 Z_S addZC.
  rewrite Htmp3 Z2sK //; split.
    apply (@leZ_trans Z0) => //; lia.
  apply: (leZ_ltZ_trans _ Htmp).
  rewrite Z_S addZC; exact/leZZ.
- by apply sizeof_gt0.
- rewrite Z2sK // Zmult_1_r; split; first by apply Zle_0_nat.
  apply (@leZ_ltZ_trans (2 ^^ 30)%Z) => //.
  apply: leZ_trans; last by apply ltZW, l1l2_ub.
  rewrite inj_mult -[X in (X <= _)%Z]mul1Z.
  apply leZ_wpmul2r; first exact: Zle_0_nat.
  rewrite size_cat [size _]/= Hn Z_S; lia.
- rewrite Htmp3; split.
    rewrite -inj_mult; exact: Zle_0_nat.
  apply (@leZ_ltZ_trans (2 ^^ 30)%Z) => //.
  apply: leZ_trans; last by apply ltZW, l1l2_ub.
  rewrite inj_mult mulZC.
  apply leZ_wpmul2r; first exact: Zle_0_nat.
  rewrite size_cat [size _]/= inj_plus Z_S Hn; lia.
- rewrite Z2sK // Htmp3 -Zmult_plus_distr_r mulZC addZC -Z_S; split.
    rewrite -inj_mult; exact: Zle_0_nat.
  apply (@leZ_ltZ_trans (2 ^^ 30)%Z) => //.
  apply: leZ_trans; last by apply ltZW, l1l2_ub.
  rewrite inj_mult size_cat [size _]/= Hn inj_plus.
  apply leZ_wpmul2r; first exact: Zle_0_nat.
  lia.
Opaque eval.
Qed.

Local Open Scope machine_int_scope.

Lemma mapstos_fit_cat {t : g.-typ} n (l1 l2 : seq (t.-phy)) (e : exp sigma (:* t)) :
  size l1 = n ->
  (Z_of_nat (size (l1 ++ l2) * sizeof t) < 2 ^^ 31)%Z ->
  e |---> l1 ++ l2 ===> e |---> l1 ** e \+ [ Z_of_nat n ]sc |---> l2.
Proof.
move=> l1n lub s h.
rewrite {1}/mapstos_fit.
case=> h1 h2 h1dh2 Hh1.
case => Hh2; rewrite /emp => ?; subst h2.
apply (@mapstos_cat t n) in Hh1 => //.
case: Hh1 => h11 h12 h11dh12 H11 H12.
rewrite -hp.unionA.
apply con_c => //.
  by rewrite hp.unionhe.
  rewrite /mapstos_fit -(hp.unionhe h11).
  apply con_c => //; first by apply hp.disjhe.
  split => //.
  rewrite size_cat inj_mult inj_plus Zmult_plus_distr_r in Hh2.
  apply: leZ_ltZ_trans; last by apply Hh2.
  rewrite addZA [X in (_ <= X)%Z]addZC -2!inj_mult.
  apply leZ_addl; by [apply Zle_0_nat | apply leZZ].
rewrite /mapstos_fit.
apply con_c => //; first exact: hp.disjhe.
split => //.
rewrite size_cat inj_mult inj_plus Zmult_plus_distr_r in Hh2.
apply: leZ_ltZ_trans; last exact: Hh2.
apply Zeq_le.
have Hn : - 2 ^^ 31 <= Z.of_nat n < 2 ^^ 31.
  split.
    apply: leZ_trans; last exact: Zle_0_nat.
    by [].
  apply: leZ_ltZ_trans; last exact: lub.
  rewrite inj_mult size_cat inj_plus l1n Zmult_plus_distr_l addZC.
  apply leZ_addl; first by rewrite -inj_mult; apply Zle_0_nat.
  apply Zle_scale; first exact: Zle_0_nat.
  apply Z_of_nat_lt0; exact: sizeof_gt0.
rewrite phy_add_pe; last first.
  rewrite si32_of_phy_sc Z2sK //; exact/leZP/Zle_0_nat.
have Hn' : 0 <= Z.of_nat (sizeof t) * Z.of_nat n < 2 ^^ ptr_len.
  split; first by rewrite -inj_mult; apply Zle_0_nat.
  apply: leZ_ltZ_trans; last exact/Hh2.
  apply leZ_addl; first exact/min_u2Z.
  rewrite addZC; apply leZ_addl.
  rewrite -inj_mult; exact/Zle_0_nat.
  rewrite l1n; exact: leZZ.
apply u2Z_add_new.
  apply: leZ_ltZ_trans; last by apply Hh2.
  rewrite si32_of_phy_sc Z2uK; last by rewrite Z2sK.
  rewrite Z2sK //.
  apply leZ_add2l.
  rewrite addZC; apply leZ_addl.
  by rewrite -inj_mult; apply Zle_0_nat.
  by rewrite l1n; apply leZZ.
move=> _.
apply u2Z_Z2u_new.
  by rewrite si32_of_phy_sc Z2sK.
move=> Htmp.
by rewrite si32_of_phy_sc Z2sK // Z.add_assoc l1n -2!inj_mult multE.
Qed.

Definition sepexists {A: Type} (P: A -> assert) : assert := fun s h => exists x:A, P x s h.

Notation "'sepex' x , p" := (sepexists (fun x => p))
  (at level 200, x name, right associativity) : C_assert_scope.

Lemma sepex_bbang_dup {A : Type} (p : A -> bexp sigma) :
  (sepex x, `! p x) <==> (sepex x, `! p x) ** (sepex x, `! p x).
Proof.
move=> s h; split.
- case=> a [] pas.
  rewrite /emp => ->.
  rewrite -(hp.unioneh hp.emp).
  apply con_c.
  by apply hp.disjeh.
  by exists a.
  by exists a.
- case=> h1 h2 _ [] a [] pas.
  rewrite /emp => ->.
  case=> a' [] pa's.
  rewrite /emp => ->.
  rewrite hp.unioneh; by exists a.
Qed.

Lemma sepex_bbang_dup2 {A : Type} {p : A -> bexp sigma} (P : assert) (Heq : P = sepex x, `! p x) :
  P <==> P ** P.
Proof. rewrite Heq. by apply sepex_bbang_dup. Qed.

Lemma sepex_pure_duplicate {A : Type} (P : A -> assert) :
  (forall x, P x ===> emp) ->
  (sepex x, P x) <==> (sepex x, P x) ** (sepex x, P x).
Proof.
move=> H.
apply equiv_def; split.
  move=> s h [] a Pa.
  rewrite (H _ _ _ Pa) -(hp.unioneh hp.emp).
  apply con_c => //.
  by apply hp.disjeh.
  exists a; by rewrite -(H _ _ _ Pa).
  exists a; by rewrite -(H _ _ _ Pa).
move=> s h [] h1 h2 h1dh2 [a H1] [a' H2].
rewrite (H _ _ _ H1) (H _ _ _ H2) hp.unioneh.
exists a; by rewrite -(H _ _ _ H1).
Qed.

Lemma ent_L_ex0 {A} (P : A -> assert) R :
  (forall x, P x ===> R) -> (sepex x, P x) ===> R.
Proof. move=> H s h [] x; by apply H. Qed.

Lemma ent_L_ex1 {A} (P : A -> assert) Q R :
  (forall x, P x ** Q ===> R) -> (sepex x, P x) ** Q ===> R.
Proof. move=> H s h [] h1 h2 h1sh2 [a H1] H2. by apply (H a), con_c. Qed.

Lemma ent_L_ex1' {A} (P : A -> assert) Q R :
  (forall x, Q ** P x ===> R) -> Q ** (sepex x, P x) ===> R.
Proof. move => H; rewrite conC; apply ent_L_ex1; intro a; rewrite conC; by apply H. Qed.

Lemma ent_L_ex2 {A} (P : A -> assert) Q R U :
  (forall x, U ** P x ** Q ===> R) -> U ** (sepex x, P x) ** Q ===> R.
Proof.
move=> H s h [] h1 h2 h1dh2 HU Htmp.
move: Htmp h1dh2 => [] h21 h22 h21dh22 H21 H22 h1dh2.
refine (ent_L_ex1 (fun x => U ** P x) Q _ _ s (h1 \U (h21 \U h22)) _); last first.
  rewrite hp.unionA.
  apply con_c => //.
    apply hp.disjUh => //.
    by case/hp.disj_union_inv : h1dh2.
  case: H21 => a H21; exists a.
  apply con_c => //.
  by case/hp.disj_union_inv : h1dh2.
move=> a.
rewrite -conA; by apply (H a).
Qed.

Lemma ent_R_ex0 {A} (P : A -> assert) R :
  (exists x, R ===> P x) -> R ===> (sepex x, P x).
Proof. case=> a H s h HR; exists a; by apply H. Qed.

Lemma ent_R_ex1 {A} (P : A -> assert) Q R :
  (exists x, R ===> P x ** Q) -> R ===> (sepex x, P x) ** Q.
Proof.
case=> a H; eapply ent_trans; first by apply H.
apply monotony_R, ent_R_ex0; by exists a.
Qed.

Definition sepforall {A: Type} (P: A -> assert) : assert := fun s h => forall x, P x s h.

Notation "'sepall' x , p" := (sepforall (fun x => p))
  (at level 200, x name, right associativity) : C_assert_scope.

(** Hoare triples *)

Lemma triple_post_conA P Q R S c :
  {{ S }} c {{ P ** (Q ** R) }} -> {{ S }} c {{ P ** Q ** R }}.
Proof. move=> H. eapply hoare_weak; last by apply H. by rewrite conA. Qed.

Lemma triple_post_conC P Q S c :
  {{ S }} c {{ P ** Q }} -> {{ S }} c {{ Q ** P }}.
Proof. move=> H. eapply hoare_weak; last by apply H. by rewrite conC. Qed.

Lemma triple_pre_conC P Q S c :
  {{ P ** Q }} c {{ S }} -> {{ Q ** P }} c {{ S }}.
Proof. move=> H. eapply hoare_stren; last by apply H. by rewrite conC. Qed.

Lemma hoare_R_or_1 (P Q R : C_definition.assert) (c : C_definition.cmd) :
   {{ P }}c {{ Q}} -> {{ P }}c {{ Q \\// R }}.
Proof. move=> H. apply hoare_weak with Q => //. by apply ent_R_or_1. Qed.

Lemma hoare_R_or_2 (P Q R : C_definition.assert) (c : C_definition.cmd) :
   {{ P }}c {{ R }} -> {{ P }}c {{ Q \\// R }}.
Proof. move=> H. apply hoare_weak with R => //. by apply ent_R_or_2. Qed.

Lemma hoare_pullout_sbang P c Q (R : Prop) : (R -> {{ P }} c {{ Q }}) ->
  {{ !!(R) ** P }} c {{ Q }}.
Proof.
move=> H; apply hoare_complete => s h [h1 h2 h1dh2 [H1 H2] Hh2].
rewrite H2 hp.unioneh; by apply (soundness _ _ _ (H H1)).
Qed.

Lemma hoare_stren_pull_out : forall P c Q a,
  (P ===> !!(a) ** TT) -> (a -> {{ P }} c {{ Q }}) ->
  {{ P }} c {{ Q }}.
Proof.
move => P c Q a HPa Ha.
eapply hoare_stren with (P ** !!(a)); last first.
  eapply hoare_stren; last by apply hoare_pullout_sbang, Ha.
  by rewrite conC.
move => s h HP.
have Ha' : a.
  move: (HPa _ _ HP) => H.
  inversion H; subst; clear H.
  by apply H1.
rewrite -(hp.unionhe h).
econstructor => //=.
Disj.
Qed.

Lemma hoare_stren_pull_out' : forall P P' c Q a,
  (P ===> P' ** TT) -> (P' ===> !!(a)) -> (a -> {{ P }} c {{ Q }}) ->
  {{ P }} c {{ Q }}.
Proof.
intros.
eapply hoare_stren_pull_out with a; last by [].
by rewrite -> H; rewrite -> H0.
Qed.

(** Hoare triple for skip *)

Definition def_cmd0_cmd (c : cmd0') : C_definition.cmd := cmd_cmd0 c.
Coercion def_cmd0_cmd : cmd0' >-> C_definition.cmd.

Lemma hoare0_FF P : forall c0 : cmd0 , {{ FF }} c0 {{ P }}.
Proof.
case.
- apply hoare_stren with P => //.
  by apply hoare_hoare0, hoare0_skip.
- move=> t str Hstr e.
  apply hoare_stren with (wp_assign Hstr e P) => //.
  by apply hoare_hoare0, C_Hoare0.hoare0_assign.
- move=> t s e H.
  eapply hoare_stren; last by apply hoare_hoare0, C_Hoare0.hoare0_lookup.
  by [].
- move=> t e1 e2.
  eapply hoare_stren; last by apply hoare_hoare0, C_Hoare0.hoare0_mutation.
  by [].
Qed.

Lemma skip_hoare P Q : P ===> Q -> {{ P }} skip {{ Q }}.
Proof.
move => H; eapply hoare_conseq.
by apply ent_id.
by apply H.
by do 2 constructor.
Qed.

(** Hoare triples for assign *)

Lemma hoare_assign_stren {t} (Q P : assert) str (Hstr : env_get str sigma = |_ t _|) (e : exp sigma t) :
  P ===> wp_assign Hstr e Q -> {{ P }} assign Hstr e {{ Q }}.
Proof.
move/hoare_stren; apply.
by apply hoare_hoare0, hoare0_assign.
Qed.

Definition def_cmd0_cmd2 (c : cmd0') : cmd := cmd_cmd0 c.
Coercion def_cmd0_cmd2 : cmd0' >-> cmd.

Lemma hoare_assign_seq_stren {t} (R P Q : assert) str (Hstr : env_get str sigma = |_ t _|) (e : exp sigma t) c :
  P ===> wp_assign Hstr e R ->
  {{ R }} c {{ Q }} -> {{ P }} assign Hstr e; c {{ Q }}.
Proof. intros. apply hoare_seq with R => //. by apply hoare_assign_stren. Qed.

(** Hoare triples for lookup *)

Lemma hoare_lookup_stren {t} (Q P : assert) str (Hstr : env_get str sigma = |_ t _|) (e : exp sigma (:* t)) :
  P ===> wp_lookup Hstr e Q -> {{ P }} lookup Hstr e {{ Q }}.
Proof. move/hoare_stren; apply. by apply hoare_hoare0, hoare0_lookup. Qed.

(** first backward-reasoning form (LKBR1) *)

Inductive wp_lookup_back {t} str (Hstr : env_get str sigma = |_ t _|) (e : exp sigma (:* t)) P : assert :=
| wp_lkbr1 : forall s h (v : t.-phy),
  ([ e ]_s |pV~> v **
    ([ e ]_ s |pV~> v -* wp_assign Hstr [ v ]c P)) s h ->
  wp_lookup_back str Hstr e P s h.

Lemma hoare_lookup_back {t} str Hstr (e : exp sigma (:* t)) P :
  {{ wp_lookup_back str Hstr e P }} lookup Hstr e {{ P }}.
Proof.
apply hoare_stren with (wp_lookup Hstr e P); last by apply hoare_hoare0, hoare0_lookup.
do 3 intro.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
move: {H2}(H2 h1 H H1) => H2.
inversion H2; subst; clear H2.
econstructor; last by apply H0.
apply heap_get_value_union_L => //=.
exact/phy_mapsto_heap_get.
Qed.

(** second backward-reasoning form (LKBR2) *)

Inductive wp_lookup_back_TT {t} str (Hstr : env_get str sigma = |_ t _|) (e : exp sigma (:* t)) (P : assert) : assert :=
| wp_lookup_back_TT_c : forall s h (v : t.-phy),
  ([ e ]_ s |pV~> v ** TT) s h -> wp_assign Hstr [ v ]c P s h ->
  wp_lookup_back_TT str Hstr e P s h.

Lemma hoare_lookup_back_TT {t} str (Hstr : env_get str sigma = |_ t _|) (e : exp sigma (:* t)) (P : assert) :
  {{ wp_lookup_back_TT str Hstr e P }} lookup Hstr e {{ P }}.
Proof.
apply hoare_stren with (wp_lookup Hstr e P); last by apply hoare_hoare0, hoare0_lookup.
do 3 intro.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
inversion H1; subst; clear H1.
inversion H2; subst; clear H2.
econstructor; last by apply H0.
apply heap_get_value_union_L => //=.
by apply phy_mapsto_heap_get.
Qed.

(** first backward-reasoning form, introduce logical *)

Inductive wp_lookup_back_conv {t} str (Hstr : env_get str sigma = |_ t _|) (e : exp sigma (:* t)) P : assert :=
| wp_lkbr1_conv : forall s h (pv : t.-phy) (lv : t.-log), pv |x| lv ->
  ([ e ]_ s |lV~> lv **
    ([ e ]_ s |lV~> lv -* wp_assign Hstr [ pv ]c P)) s h ->
  wp_lookup_back_conv _ Hstr e P s h.

Lemma entails_wp_lookup_back_conv : forall {t} x {Hs} (e : exp sigma (:* t)) P,
  wp_lookup_back_conv x Hs e P ===> wp_lookup_back x Hs e P.
Proof.
move => ty x Hs e P s h H.
inversion H; subst; clear H.
inversion H1; subst; clear H1.
apply (wp_lkbr1 x Hs e P s _ pv).
apply con_c => //=.
- by apply (proj2 (phylog_mapsto_conv _ _ _ H0 h1 _)).
- move => h' Hh' Hmapsto.
  apply H3 => //=.
  by apply: (proj1 (phylog_mapsto_conv _ _ _ H0 h' '|u2Z (ptr<=phy ([e ]_ s))|)).
Qed.

Lemma hoare_lookup_back_conv {t} str Hstr (e : exp sigma (:* t)) P :
  {{ wp_lookup_back_conv str Hstr e P }} lookup Hstr e {{ P }}.
Proof.
move: (@entails_wp_lookup_back_conv _ _ Hstr e P).
move/hoare_stren; apply.
apply hoare_lookup_back.
Qed.

(** second backward-reasoning form (LKBR2), introduce logical *)

Inductive wp_lookup_back_conv_TT {t} str (Hstr : env_get str sigma = |_ t _|) (e : exp  sigma (:* t)) (P : assert) : assert :=
| wp_lookup_back_conv_TT_c : forall s h (pv : t.-phy) lv, pv |x| lv ->
  ([ e ]_ s |lV~> lv ** TT) s h /\ wp_assign Hstr [ pv ]c P s h ->
  wp_lookup_back_conv_TT str Hstr e P s h.

Lemma entails_wp_lookup_back_conv_TT {t} x H (e : exp sigma (:* t)) P :
  wp_lookup_back_conv_TT x H e P ===> wp_lookup_back_TT x H e P.
Proof.
inversion_clear 1.
inversion_clear H2.
inversion H0.
apply (wp_lookup_back_TT_c x H e P s  _ pv).
apply con_c => //=.
- by apply (proj2 (phylog_mapsto_conv _ _ _ H1 h1 _)).
- congruence.
Qed.

Lemma hoare_lookup_back_conv_TT {t} x H (e : exp sigma (:* t)) P :
  {{ wp_lookup_back_conv_TT x H e P }} lookup H e {{ P }}.
Proof.
move: (entails_wp_lookup_back_conv_TT x H e P).
move/hoare_stren; apply.
apply hoare_lookup_back_TT.
Qed.

Lemma hoare_lookup_back_conv_TT_stren {t} x {Hs} e (P Q : assert) :
  P ===> @wp_lookup_back_conv_TT t x Hs e Q ->
  {{ P }} lookup Hs e {{ Q }}.
Proof.
move/hoare_stren; apply.
apply hoare_lookup_back_conv_TT.
Qed.

Local Open Scope zarith_ext_scope.

(** Frame rule *)

Fixpoint modified_vars (c : cmd) {struct c} : g.-env :=
  match c with
    | cmd_cmd0 c =>
      match c with
        | skip => nil
        | assign ty x Hs e => (x, ty) :: nil
        | lookup ty x Hs e => (x, ty) :: nil
        | mutation _ e f => nil
      end
    | cmd_seq c1 c2 => modified_vars c1 ++ modified_vars c2
    | ifte a c1 c2 => modified_vars c1 ++ modified_vars c2
    | while a c1 => modified_vars c1
  end.

Lemma modified_vars_subset_type_store : forall c, {subset (modified_vars c) <= sigma}.
Proof.
elim => //=.
- case => //=.
  move => ty str Hstr e.
  move => x Hx.
  rewrite in_cons in Hx; move/orP: Hx => [] //=; move/eqP => ?; subst x.
  by apply assoc_get_in.
- move => ty str Hstr e.
  move => x Hx.
  rewrite in_cons in Hx; move/orP: Hx => [] //=; move/eqP => ?; subst x.
  by apply assoc_get_in.
- move => c1 Hc1 c2 Hc2 x Hx.
  rewrite mem_cat in Hx; move/orP: Hx => [] //= Hx.
  + by apply Hc1.
  + by apply Hc2.
- move => _ c1 Hc1 c2 Hc2 x Hx.
  rewrite mem_cat in Hx; move/orP: Hx => [] //= Hx.
  + by apply Hc1.
  + by apply Hc2.
Qed.

Definition inde (l : g.-env) (Hl: {subset l <= sigma}) (P : assert) := forall s h,
  (forall x t v (H : (x, t) \in l),
   (P s h <-> P (store_upd (assoc_get_subset_in uniq_sigma Hl H) v s) h)).

Lemma inde_nil H P : inde nil H P.
Proof.
move=> s h str t pv H0.
exfalso.
by rewrite in_nil in H0.
Qed.

Definition inde_cmd c := inde (modified_vars c) (modified_vars_subset_type_store _).

#[global] Instance inde_cmd_morphism: Morphisms.Proper (eq ==> equiv ==> iff) inde_cmd.
move => c1 c2 Hc P Q HP.
subst; rewrite /inde_cmd /inde.
split => H s h x ty v H0; split => H1.
- apply/HP.
  apply/(H s h x ty v H0).
  by apply/HP.
- apply/HP.
  apply/(H s h x ty v H0).
  by apply/HP.
- apply/HP.
  apply/(H s h x ty v H0).
  by apply/HP.
- apply/HP.
  apply/(H s h x ty v H0).
  by apply/HP.
Qed.

Lemma inde_seq R c d : inde_cmd (c ; d) R -> inde_cmd c R /\ inde_cmd d R.
Proof.
move=> H; split => s h x //= v H'; split.
- have Hin : (x, v) \in modified_vars c ++ modified_vars d by rewrite mem_cat H0.
  rewrite (H s h x v H' Hin).
  move: (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _) => ob ob1.
  by have -> : ob1 = ob by apply eq_irrelevance.
- have Hin : (x, v) \in modified_vars c ++ modified_vars d by rewrite mem_cat H0.
  rewrite (H s h x v H' Hin).
  move: (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _) => ob ob1.
  by have -> : ob1 = ob by apply eq_irrelevance.
- have Hin : (x, v) \in modified_vars c ++ modified_vars d by rewrite mem_cat H0; apply orbT.
  rewrite (H s h x v H' Hin).
  move: (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _) => ob ob1.
  by have -> : ob = ob1 by apply eq_irrelevance.
- have Hin : (x, v) \in modified_vars c ++ modified_vars d by rewrite mem_cat H0; apply orbT.
  rewrite (H s h x v H' Hin).
  move: (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _) => ob ob1.
  by have -> : ob1 = ob by apply eq_irrelevance.
Qed.

Lemma inde_ifte : forall R b c d, inde_cmd (ifte b c d) R ->
  inde_cmd c R /\ inde_cmd d R.
Proof.
move=> R t c d H; split => s h x v H'; split.
- have Hin : (x, v) \in modified_vars c ++ modified_vars d by rewrite mem_cat H0.
  rewrite (H s h x v H' Hin).
  move: (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _) => ob ob1.
  by have -> : ob = ob1 by apply eq_irrelevance.
- have Hin : (x, v) \in modified_vars c ++ modified_vars d by rewrite mem_cat H0.
  rewrite (H s h x v H' Hin).
  move: (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _) => ob ob1.
  by have -> : ob1 = ob by apply eq_irrelevance.
- have Hin : (x, v) \in modified_vars c ++ modified_vars d by rewrite mem_cat H0; apply orbT.
  rewrite (H s h x v H' Hin).
  move: (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _) => ob ob1.
  by have -> : ob = ob1 by apply eq_irrelevance.
- have Hin : (x, v) \in modified_vars c ++ modified_vars d by rewrite mem_cat H0; apply orbT.
  rewrite (H s h x v H' Hin).
  move: (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _) => ob ob1.
  by have -> : ob = ob1 by apply eq_irrelevance.
Qed.

Lemma inde_while R b c : inde_cmd (while b c) R -> inde_cmd c R.
Proof.
move=> H; split.
- rewrite (H s h x t v H0).
  move: (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _) => ob ob1.
  by have -> : ob = ob1 by apply eq_irrelevance.
- rewrite (H s h x t v H0).
  move: (assoc_get_subset_in _ _ _) (assoc_get_subset_in _ _ _) => ob ob1.
  by have -> : ob = ob1 by apply eq_irrelevance.
Qed.

(*Lemma in_mem1 : forall {A : eqType} (a : A), a \in a :: nil.
Proof. move=> A a. by rewrite in_cons eqxx. Qed.*)

Definition inde_upd_tstore_statement := forall (P : assert) x z s h H,
  inde (x :: nil) H P ->
  P s h ->
  P (store_upd (assoc_get_subset_in uniq_sigma H (mem_head x nil)) z s) h.

Lemma inde_upd_tstore : inde_upd_tstore_statement.
Proof.
move=> P x z s h H H0 H1.
move: (assoc_get_subset_in _ _ _) => ob.
have Hin : (x.1 , x.2) \in x :: nil by destruct x; rewrite mem_head.
move: H1; rewrite (H0 s h x.1 x.2 z Hin).
move: (assoc_get_subset_in _ _ _) => ob1.
by have -> : ob1 = ob by apply eq_irrelevance.
Qed.

Lemma inde_upd_tstore2 : forall (P : assert) x ty z s h H H',
  inde ((x, ty) :: nil) H P -> P s h -> P (@store_upd _ _ x ty H' z s) h.
Proof.
move=> P x ty z s h H H' H0 H1.
have Hin: (x , ty) \in (x, ty)::nil by rewrite in_cons eq_refl.
move: H1; rewrite (H0 s h x ty z Hin).
move: (assoc_get_subset_in _ _ _) => ob.
by have -> : ob = H' by apply eq_irrelevance.
Qed.

Lemma inde_cmd_cons c P Q : inde_cmd c P /\ inde_cmd c Q -> inde_cmd c (P ** Q).
Proof.
move => [] HP HQ s h x ty v H0; split => H.
- inversion H; subst; clear H.
  constructor => //=.
  by apply/(HP s h1).
  by apply/(HQ s h2).
- inversion H; subst; clear H.
  constructor => //=.
  by move/(HP s h1) in H2.
  by move/(HQ s h2) in H3.
Qed.

Lemma inde_cmd_sepor c P Q : inde_cmd c P /\ inde_cmd c Q -> inde_cmd c (P \\// Q).
Proof.
move => [] HP HQ s h x ty v H0; split => [] [] H.
- by left; apply/(HP s h).
- by right; apply/(HQ s h).
- by left; apply/(HP s h x ty v H0).
- by right; apply/(HQ s h x ty v H0).
Qed.

Lemma frame_rule0 P c Q : hoare0 P c Q ->
  forall R, inde_cmd c R -> {{ P ** R }} c {{ Q ** R }}.
Proof.
elim.
- (* skip *) move=> {}P R Hinde; by apply hoare_hoare0, hoare0_skip.
- (* x <- e *) move=> {}P ty x Hs e R Hinde.
  apply hoare_stren with (wp_assign Hs e (P ** R)); last by apply hoare_hoare0, hoare0_assign.
  rewrite /entails => s h Hmem.
  inversion Hmem; subst; clear Hmem.
  constructor.
  constructor => //=.
  + by inversion H0; subst; clear H0.
  + by apply (inde_upd_tstore2 _ _ _ _ _ _ _ _ Hinde).
- move => {}P ty v Hs e R Hinde.
  apply hoare_stren with (wp_lookup Hs e (P ** R)); last by apply hoare_hoare0, hoare0_lookup.
  rewrite /entails => s h Hmem.
  inversion Hmem; subst; clear Hmem.
  inversion H0; subst; clear H0.
  econstructor.
  + apply heap_get_value_union_L => //; by apply H2.
  + econstructor => //.
    by apply (inde_upd_tstore2 _ _ _ _ _ _ _ _ Hinde).
- move => {}P ty e1 e2 R Hinde.
  apply hoare_stren with (wp_mutation e1 e2 (P ** R)); last by apply hoare_hoare0, hoare0_mutation.
  rewrite /entails => s h Hmem.
  inversion Hmem; subst; clear Hmem.
  inversion H0; subst; clear H0.
  econstructor.
  + by apply heap_get_value_union_L => //; apply H2.
  + rewrite heap_upd_union_L //; last first.
      by apply (heap_get_inc _ _ _ H2).
    econstructor => //=.
    by apply disj_heap_upd.
Qed.

Lemma frame_rule_R : forall P c Q, {{ P }} c {{ Q }} ->
  forall R, inde_cmd c R -> {{ P ** R }} c {{ Q ** R }}.
Proof.
  move=> P c Q; elim; clear P c Q.
  - move=> P Q c H R HR.
  by apply frame_rule0.
  - (* seq *) move=> Q P R c d P_c_Q Hc Q_d_R Hd R0 HR0.
  apply hoare_seq with (Q ** R0).
  + apply hoare_stren with (P ** R0) => //.
  apply Hc => //.
  by case/inde_seq : HR0.
  + apply Hd => //.
  by case/inde_seq : HR0.
  - (* hoare_conseq *) move=> P P' Q Q' c Q'_Q P_P' P'_c_Q' H R HR.
  apply hoare_stren with (P' ** R).
  rewrite /entails => s h Hh.
  inversion Hh; subst; clear Hh.
  econstructor => //=; by intuition.
  apply hoare_weak with (Q' ** R).
  rewrite /entails => s h Hh.
  inversion Hh; subst; clear Hh.
  econstructor => //=; by intuition.
  by apply H.
  - (* while true *) move=> P b c Hc H R HR.
  apply hoare_weak with (fun s h => (P ** R) s h /\ ~~ [ b ]b_ s).
  rewrite /entails => s h.
  case=> PR_h Hb.
  inversion PR_h; subst; clear PR_h.
  econstructor => //=; by intuition.
  apply hoare_stren with (fun s h => (P ** R) s h).
  rewrite /entails => s h PR_h.
  inversion PR_h; subst; clear PR_h.
  econstructor => //=; by intuition.
  apply hoare_while with (P:= fun s h => (P ** R) s h).
  have H1 : inde_cmd c R by apply (inde_while _ _ _ HR).
  apply hoare_stren with (fun s h =>
    ((fun s h => P s h /\ [ b ]b_ s) ** R) s h).
  rewrite /entails => s h [] PR_h Hb.
  inversion PR_h; subst; clear PR_h.
  econstructor => //=; by intuition.
  simpl in H.
  eapply hoare_conseq; last by apply H.
  done.
  done.
  - (* hoare_ifte *) move=> P Q t c d Hc H'c Hd H'd R H1.
  apply hoare_ifte.
  + have H : inde_cmd c R by case/inde_ifte : H1.
  apply hoare_stren with (fun s h =>
    ((fun s0 h0 => P s0 h0 /\ [ t ]b_ s0) ** R) s h); auto.
  rewrite /entails => s h [] PR_h Hb.
  inversion PR_h; subst; clear PR_h.
  econstructor => //=; by intuition.
  + have H2 : inde_cmd d R by case/inde_ifte : H1.
  apply hoare_stren with ((fun s0 h0 => P s0 h0 /\ ~~ [ t ]b_ s0) ** R) => //.
  move=> s h [] PR_h Hb.
  inversion PR_h; subst; clear PR_h.
  econstructor => //=; by intuition.
  eapply hoare_conseq; last by apply H'd.
  done.
  done.
Qed.

Lemma frame_rule_L P c Q : {{ P }} c {{ Q }} ->
  forall R, inde_cmd c R -> {{ R ** P }} c {{ R ** Q }}.
Proof.
move=> P_c_Q R HR.
by apply triple_pre_conC, triple_post_conC, frame_rule_R.
Qed.

End C_Seplog_f.

(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import FunctionalExtensionality ClassicalFacts Relations Permutation.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import Init_ext String_ext.
Require Import finmap.

(*******************************************************************************)
(* An extension of the modules in while.v with Separation-logic connectives.   *)
(* Support for parameter-less, recursive procedures follows Norbert Schirmer,  *)
(* Verification of Sequential Imperative Programs in Isabelle/HOL, PhD Thesis, *)
(* Institut f\ur Informatik, Technische Universit\at M\unchen, 2006            *)
(*******************************************************************************)

Declare Scope statebipl_scope.
Declare Scope seplog_scope.
Declare Scope lang_scope.
Declare Scope whilesemop_scope.
Declare Scope whilehoare_scope.

Module Type StateBipl.

(** A state is a pair of a store and a mutable memory. *)

Parameter gstore : Type.
Parameter heap : Type.
Parameter state : Type.
Parameter gstate : state -> gstore.
Parameter hstate : state -> heap.
Parameter mkState : gstore -> heap -> state.
Notation "s .+g" := (gstate s) (at level 2, left associativity, format "s .+g") : statebipl_scope.
Notation "s .+h" := (hstate s) (at level 2, left associativity, format "s .+h") : statebipl_scope.
Local Open Scope statebipl_scope.

Axiom gstate_mkState : forall a c, (mkState a c).+g = a.
Axiom hstate_mkState : forall a c, (mkState a c).+h = c.
Axiom mkState_eq : forall s, mkState s.+g s.+h = s.
(*Record state : Type := mkState {
  gstate : gstore ;
  lstate : store ;
  hstate : heap}.*)

(** Structured commands (if-then-else's and while-loops) are parameterized by a type
   for boolean expressions. *)

Parameter expr_b : Type.
Parameter neg : expr_b -> expr_b.
Parameter eval_b : expr_b -> state -> bool.
Parameter eval_b_neg : forall t s, eval_b (neg t) s = ~~ eval_b t s.

Definition assert : Type := state -> Prop.

End StateBipl.

Module Type StateBiplProp (ST : StateBipl).

Include ST.

Definition TT : assert := fun _ => True.
Definition FF : assert := fun _ => False.
Definition And (P Q : assert) : assert := fun s => P s /\ Q s.
Notation "P //\\ Q" := (And P Q) (at level 70, right associativity) : statebipl_scope.
Definition Or (P Q : assert) : assert := fun s => P s \/ Q s.
Notation "P \\// Q" := (Or P Q) (at level 80, right associativity) : statebipl_scope.
Definition Not (P : assert) : assert := fun s => ~ P s.
Notation "~~~ P" := (Not P) (at level 60, no associativity) : statebipl_scope.
Definition entails (P Q : assert) : Prop := forall s, P s -> Q s.
Notation "P ===> Q" := (entails P Q) (at level 89, no associativity) : statebipl_scope.
Definition equiv (P Q : assert) : Prop := forall s, P s <-> Q s.
Notation "P <==> Q" := (equiv P Q) (at level 89, no associativity) : statebipl_scope.

Local Open Scope statebipl_scope.

Lemma equiv_refl : forall (P : assert), P <==> P.
Proof. done. Qed.

Lemma equiv_sym (P Q : assert) : P <==> Q -> Q <==> P.
Proof. move=> HPQ s. by case: (HPQ s). Qed.

Lemma equiv_trans (P Q R : assert) : P <==> Q -> Q <==> R -> P <==> R.
Proof.
move=> HPQ HQR s.
move: (HPQ s) (HQR s).
by intuition.
Qed.

Instance equiv_equivalence : Classes.RelationClasses.Equivalence equiv.
constructor.
exact equiv_refl.
exact equiv_sym.
exact equiv_trans.
Qed.

Import Morphisms.ProperNotations.

Instance equiv_in_entails : Morphisms.Proper (equiv ==> equiv ==> iff) entails.
rewrite /Morphisms.Proper /Morphisms.respectful.
move=> P Q PQ P' Q' P'Q'; split; by [move=> PP' s /PQ/PP'/P'Q' | move=> QQ' s /PQ /QQ' /P'Q'].
Qed.

Lemma equiv_def P Q : (P <==> Q) <-> ((P ===> Q) /\ (Q ===> P)).
Proof.
split.
- move=> H.
  setoid_rewrite H.
  by split.
- case => H1 H2 s; split; by [apply H1 | apply H2].
Qed.

Lemma equiv1 {P Q} : P <==> Q -> P ===> Q.
Proof. move=> H. by setoid_rewrite H. Qed.

Lemma equiv2 {P Q} : P <==> Q -> Q ===> P.
Proof. move=> H. by setoid_rewrite H. Qed.

Lemma ent_id P : P ===> P. Proof. done. Qed.

Lemma ent_trans Q P R : P ===> Q -> Q ===> R -> P ===> R.
Proof. move=> H1 H2 s Ps; by apply H2, H1. Qed.

Lemma ent_L_F Q : FF ===> Q. Proof. done. Qed.

Lemma ent_R_T P : P ===> TT. Proof. done. Qed.

Lemma F_is_not_T : FF <==> Not TT. Proof. move=> s; split=> //; by apply. Qed.

Instance entail_partial : RelationClasses.PreOrder entails.
apply (RelationClasses.Build_PreOrder _ ent_id (fun a b c => ent_trans b a c)).
Defined.

Instance entails_in_entails_And : Morphisms.Proper (entails ==> entails ==> entails) And.
rewrite /Morphisms.Proper /Morphisms.respectful.
move=> x y xy a b ab s [H1 H2]; split; by [apply xy | apply ab].
Qed.

Instance entails_in_entails_Or : Morphisms.Proper (entails ==> entails ==> entails) Or.
rewrite /Morphisms.Proper /Morphisms.respectful.
move=> x y xy a b ab s [] H1; by [left; apply xy | right; apply ab].
Qed.

Lemma and_L_1 (P Q R : assert) : P ===> R -> P //\\ Q ===> R.
Proof. move=> H. setoid_rewrite H. by move=> s []. Qed.

Lemma False_lhs P Q : P ===> FF -> P ===> Q.
Proof. move=> H. setoid_rewrite H. exact: ent_L_F. Qed.

Lemma ent_R_or_1 (P Q R : assert) : P ===> R -> P ===> R \\// Q.
Proof. move=> H. setoid_rewrite H. by move=> s; left. Qed.

Lemma ent_R_or_2 (P Q R : assert) : P ===> Q -> P ===> R \\// Q.
Proof. move=> H. setoid_rewrite H. by move=> s; right. Qed.

Lemma ent_L_or (P Q R : assert) : ((R ===> P) /\ (Q ===> P)) <-> R \\// Q ===> P .
Proof.
split.
  case=> H1 H2.
  setoid_rewrite H1.
  setoid_rewrite H2.
  by move=> s [].
move=> H; split.
  apply: ent_trans _ H; by left.
apply: ent_trans _ H; by right.
Qed.

End StateBiplProp.

Module Type Bipl (S : StateBipl).

Include (StateBiplProp S).

Local Open Scope statebipl_scope.

Axiom con : assert -> assert -> assert.

Notation "P ** Q" := (con P Q) (at level 80, right associativity) : seplog_scope.
Local Open Scope seplog_scope.

Parameter conC : forall (P Q : assert), P ** Q <==> Q ** P.

Parameter conA : forall (P Q R : assert), P ** (Q ** R) <==> (P ** Q) ** R.

Parameter con_congr : forall (P Q R S : assert), P <==> R -> Q <==> S -> P ** Q <==> R ** S.

Parameter monotony : forall (P Q R S : assert),
  P ===> Q -> R ===> S -> P ** R ===> Q ** S.

Parameter conCA : forall P Q R, P ** (Q ** R) <==> Q ** (P ** R).

Parameter conDl : forall P Q R, (P \\// Q) ** R <==> (P ** R) \\// (Q ** R).

Parameter conDr : forall P Q R, R ** (P \\// Q) <==> (R ** P) \\// (R ** Q).

Parameter conFP : forall P, FF ** P <==> FF.

Parameter conPF : forall P, P ** FF <==> FF.

Parameter ent_R_con_T : forall P, P ===> P ** TT.

Axiom emp : assert.

Parameter conPe  : forall (P : assert), P ** emp <==> P.

Parameter coneP  : forall (P : assert), emp ** P <==> P.

Axiom imp : assert -> assert -> assert.

Notation "P -* Q" := (imp P Q) (at level 80) : seplog_scope.

End Bipl.

Module Type BiplProp (S : StateBipl) (B : Bipl S).

Include B.
Local Open Scope statebipl_scope.
Local Open Scope seplog_scope.

Lemma monotony_L P Q R : P ===> Q -> R ** P ===> R ** Q.
Proof. move=> H; apply monotony; [by apply ent_id |exact H]. Qed.

Lemma monotony_R P Q R : P ===> Q -> P ** R ===> Q ** R.
Proof. move=> H; apply monotony; [exact H | by apply ent_id]. Qed.

Import Morphisms.ProperNotations.

Instance con_morphism : Morphisms.Proper (entails ==> entails ==> entails) con.
rewrite /Morphisms.Proper /Morphisms.respectful.
move => P P' HP Q Q' HQ s; by apply monotony.
Qed.

Lemma monotony_R1 P R : P ===> emp -> P ** R ===> R.
Proof. move=> H. setoid_rewrite H. by setoid_rewrite coneP. Qed.

Lemma monotony_L1 P R : P ===> emp -> R ** P ===> R.
Proof. move=> H. setoid_rewrite H. by setoid_rewrite conPe. Qed.

Lemma monotony_R2 P R : emp ===> P -> R ===> P ** R.
Proof.
move=> H. apply ent_trans with (emp ** R); last by apply monotony_R.
by setoid_rewrite coneP.
Qed.

Lemma monotony_L2 P R : emp ===> P -> R ===> R ** P.
Proof.
move=> H. apply ent_trans with (R ** emp); last by apply monotony_L.
by setoid_rewrite conPe.
Qed.

End BiplProp.

Module Type WhileSemop0 (ST : StateBipl) (B : Bipl ST) (*uuu*).

Include ((*State*)BiplProp ST B).

(** We are given one-step, non-branching instructions: *)
Parameter cmd0 : Type.

(** One-step, non-branching instructions are given an appropriate operational semantics. We use
   an option type to model error-states. *)

Parameter exec0 : option state -> cmd0 -> option state -> Prop.
Notation "s '--' c '---->' t" := (exec0 s c t) (at level 74 , no associativity) : lang_scope.
Local Open Scope lang_scope.

Parameter from_none0 : forall s (c : cmd0), None -- c ----> s -> s = None.
Parameter cmd0_terminate : forall (c : cmd0) s, exists s', Some s -- c ----> s'.

End WhileSemop0.

(********************************************************)

Module Type WhileSemop (ST : StateBipl) (B : Bipl ST) (L: WhileSemop0 ST B).

Include L.

Local Open Scope lang_scope.

(** Using above types, we define the commands of %\while\%#While# languages. *)

Inductive cmd : Type :=
| cmd_cmd0 : 	cmd0 -> cmd
| cmd_seq : 	cmd -> cmd -> cmd
| ifte : 	expr_b -> cmd -> cmd -> cmd
| while : 	expr_b -> cmd -> cmd
| call :	string -> (* list exp -> *) cmd.
(*Coercion cmd_cmd0 : cmd0 >-> cmd.*)

Record procedure : Type := mkProcedure {
  name : string ;
(*  parameters : list string ;*)
(*  local_vars : list string ;*)
  body : cmd
}.

Parameter eq_cmd0 : cmd0 -> cmd0 -> bool.
Axiom eq_cmd0P : Equality.axiom eq_cmd0.
Parameter eq_expr_b : expr_b -> expr_b -> bool.
Axiom eq_expr_bP : Equality.axiom eq_expr_b.

Fixpoint eq_cmd (c1 c2 : cmd) : bool :=
match c1, c2 with
  | cmd_cmd0 c10, cmd_cmd0 c20 => eq_cmd0 c10 c20
  | cmd_seq c1 c2, cmd_seq d1 d2 => eq_cmd c1 d1 && eq_cmd c2 d2
  | ifte b1 c1 c2, ifte b2 d1 d2 => eq_expr_b b1 b2 && eq_cmd c1 d1 && eq_cmd c2 d2
  | while b1 c1, while b2 c2 => eq_expr_b b1 b2 && eq_cmd c1 c2
  | call s1, call s2 => s1 == s2
  | _, _ => false
end.

Lemma eq_cmdP : Equality.axiom eq_cmd.
Proof.
elim=> [ c1 | c Hc d Hd y | b c Hc d Hd y | b c Hc y | s y ].
- case=> [ c2 | c d | b c d | b c | s ]; try by apply ReflectF.
  move/iffP : (eq_cmd0P c1 c2); by apply => [-> | []].
- case: y => [ c0 | c1 c2 | b c1 c2 | b c' | ]; try by apply ReflectF.
  + apply: (iffP idP) => /=; by [case/andP => /Hc -> /Hd -> | case => /Hc -> /Hd ->].
  + move=> s; by apply ReflectF.
- case: y => [ c0 | c1 c2 | b' c1 c2 | b' c' | ]; try by apply ReflectF.
  + apply: (iffP idP) => /=.
    * by case/andP => /andP[] /eq_expr_bP <- /Hc -> /Hd ->.
    * by case => /eq_expr_bP -> /Hc -> /Hd ->.
  + move=> s; by apply ReflectF.
- case: y => [ c0 | c1 c2 | b' c1 c2 | b' c' | ]; try by apply ReflectF.
  + apply: (iffP idP) => /=; by [case/andP => /eq_expr_bP <- /Hc -> | case=> /eq_expr_bP -> /Hc ->].
  + move=> s; by apply ReflectF.
- case: y => [ c0 | c1 c2 | b' c1 c2 | b' c' | ]; try by apply ReflectF.
  move=> s' /=; by apply: (iffP idP) => [/eqP -> // | [] ->].
Qed.

Canonical Structure cmd_eqMixin := EqMixin eq_cmdP.
Canonical Structure cmd_eqType := Eval hnf in EqType _ cmd_eqMixin.

Module Cmd <: finmap.EQTYPE.
Definition A := [eqType of cmd_eqType].
End Cmd.

Module Procs := finmap.map order.StringOrder Cmd.
Definition procs := Procs.t.

(*Record procs := mkProcs {
  procs_seq :> seq procedure ;
  procs_uniq : uniq (map name procs_seq) }.*)

Notation "c ; d" := (cmd_seq c d) (at level 81, right associativity) : whilesemop_scope.

Notation "'If' e 'Then' c1 'Else' c2" := (ifte e c1 c2)
  (at level 200, right associativity, format
"'[v' '[' 'If'  e  'Then' ']' '//'   '[' c1 ']' '//' '[' 'Else' ']' '//'   '[' c2 ']' '//' ']'") : whilesemop_scope.

Notation "'While' e '{{' c '}}' " := (while e c)
  (at level 200, format
"'[v' 'While'  e  '{{' '//'   '[' c ']' '//' '}}' ']'") : whilesemop_scope.

Local Open Scope whilesemop_scope.

(** We now define the operational semantics of %\while\%#While# languages. Structured commands
   are given the textbook big-step operational semantics. *)

Reserved Notation "l '|~' s '>-' c '-^' n '->' t" (at level 70, s, c, n, t at next level, no associativity).

Inductive iexec (l : procs) : nat -> option state -> cmd -> option state -> Prop :=
| iexec_none : forall n c, l |~ None >- c -^ n -> None
| iexec_cmd0 : forall n s c s', s -- c ----> s' -> l |~ s >- (cmd_cmd0 c) -^ n -> s'
| iexec_seq : forall n s s' s'' c d,
  l |~ s >- c -^ n -> s' -> l |~ s' >- d -^ n -> s'' -> l |~ s >- c ; d -^ n -> s''
| iexec_ifte_true : forall n s s' t c d, eval_b t s ->
  l |~ Some s >- c -^ n -> s' ->
  l |~ Some s >- ifte t c d -^ n -> s'
| iexec_ifte_false : forall n s s' t c d, ~~ eval_b t s ->
  l |~ Some s >- d -^ n -> s' ->
  l |~ Some s >- ifte t c d -^ n -> s'
| iexec_while_true : forall n s s' s'' t c, eval_b t s ->
  l |~ Some s >- c -^ n -> s' ->
  l |~ s' >- while t c -^ n -> s'' -> l |~ Some s >- while t c -^ n -> s''
| iexec_while_false : forall n s t c,
  ~~ eval_b t s -> l |~ Some s >- while t c -^ n -> Some s
| iexec_call_Some : forall n s s' i pro,
   Procs.get i l = Some pro ->
   l |~ Some s >- pro -^ n -> Some s' ->
   l |~ Some s >- call i -^ n.+1 -> Some s'
| iexec_call_None : forall n s i pro,
   Procs.get i l = Some pro ->
   l |~ Some s >- pro -^ n -> None ->
   l |~ Some s >- call i -^ n.+1 -> None
| iexec_call_err : forall n s i,
    Procs.get i l = None ->
    l |~ Some s >- call i -^ n.+1 -> None
where "l '|~' s >- c '-^' n '->' t" := (iexec l n s c t) : whilesemop_scope.

Lemma iexec_cmd0_inv n l s c0 s' :
  l |~ |_ s _| >- cmd_cmd0 c0 -^ n -> s' -> |_ s _| -- c0 ----> s'.
Proof. by inversion 1. Qed.

Lemma iexec_seq_inv n l s s' c d :
  l |~ s >- c ; d -^ n -> s' ->
  exists s'', l |~ s >- c -^ n -> s'' /\ l |~ s'' >- d -^ n -> s'.
Proof.
inversion 1; subst.
  exists None; split; by apply iexec_none.
by exists s'0.
Qed.

Lemma iexecA n l s s' c0 c1 c2 :
  l |~ s >- c0 ; c1 ; c2 -^ n -> s' ->
  l |~ s >- (c0 ; c1) ; c2 -^ n -> s'.
Proof.
case/iexec_seq_inv => s0 [] Hc0.
case/iexec_seq_inv => s1 [] Hc1 Hc2.
apply iexec_seq with s1 => //.
by apply iexec_seq with s0.
Qed.

Lemma iwhile_seq' n s t : eval_b t s -> forall s' l c,
  l |~ Some s >- c ; while t c -^ n -> s' -> l |~ Some s >- while t c -^ n -> s'.
Proof.
move=> Hneq s' l c; inversion 1; subst.
by apply iexec_while_true with s'0.
Qed.

Lemma iexec_seq1_not_None n s l c1 c2 :
  ~ l |~ Some s >- c1 ; c2 -^ n -> None -> ~ l |~ Some s >- c1 -^ n -> None.
Proof.
move=> H; contradict H; apply iexec_seq with None=> //; apply iexec_none.
Qed.

Lemma iexec_seq2_not_None n s s' l c1 c2 :
  ~ l |~ Some s >- c1 ; c2 -^ n -> None -> l |~ Some s >- c1 -^ n -> Some s' ->
  ~ l |~ Some s' >- c2 -^ n -> None.
Proof.
move=> H H'. contradict H. by apply iexec_seq with (Some s').
Qed.

Lemma iexec_ifte1_not_None n s l c1 c2 t :
  ~ l |~ Some s >- ifte t c1 c2 -^ n -> None -> eval_b t s ->
  ~ l |~ Some s >- c1 -^ n -> None.
Proof. move=> H ?. contradict H. by apply iexec_ifte_true. Qed.

Lemma iexec_ifte2_not_None n s l c1 c2 t :
  ~ l |~ Some s >- ifte t c1 c2 -^ n -> None -> ~~ eval_b t s ->
  ~ l |~ Some s >- c2 -^ n -> None.
Proof. move=> H ?. contradict H. by apply iexec_ifte_false. Qed.

Lemma iexec_while1_not_None n s t l c :
  ~ l |~ Some s >- while t c -^ n -> None -> eval_b t s ->
  ~ l |~ Some s >- c -^ n -> None.
Proof.
move=> H ?. contradict H. apply iexec_while_true with None=> //. by apply iexec_none.
Qed.

Lemma iexec_while2_not_None n s l c t s0 :
  ~ l |~ Some s >- while t c -^ n -> None -> eval_b t s ->
  l |~ Some s >- c -^ n -> Some s0 -> ~ l |~ Some s0 >- while t c -^ n -> None.
Proof.
move=> H ? ?. contradict H. by apply iexec_while_true with (Some s0).
Qed.

Lemma iexec_S n l s prg s' : l |~ s >- prg -^ n -> s' ->
  forall m, n <= m -> l |~ s >- prg -^ m -> s'.
Proof.
elim; clear n prg s s'.
- move=> *; by constructor.
- move=> *; by constructor.
- intros.
  apply iexec_seq with s'; by auto.
- move=> n s s' t c1 c2 Ht H IH m Hm.
  apply iexec_ifte_true; by auto.
- move=> n s s' t c1 c2 Ht H IH m Hm.
  apply iexec_ifte_false; by auto.
- move=> n s s' s'' t c Ht H1 H2 H3 H4 m Hm.
  apply iexec_while_true with s'; by auto.
- move=> n s t c Ht m Hm.
  by apply iexec_while_false.
- move=> n s s' i pro Hfind H H1 [|m] // Hm.
  apply iexec_call_Some with pro => //; by auto.
- move=> n s i pro Hfind H H1 [|m] // Hm.
  apply iexec_call_None with pro => //; by auto.
- move=> n s i Hfint [|m] // Hm.
  by apply iexec_call_err.
Qed.

Reserved Notation "l |~ s >- c ---> t" (at level 70, s, c, t at next level, no associativity).

Inductive exec (l : procs) : option state -> cmd -> option state -> Prop :=
| exec_none : forall c, l |~ None >- c ---> None
| exec_cmd0 : forall s c s', s -- c ----> s' -> l |~ s >- (cmd_cmd0 c) ---> s'
| exec_seq : forall s s' s'' c d, l |~ s >- c ---> s' -> l |~ s' >- d ---> s'' -> l |~ s >- c ; d ---> s''
| exec_ifte_true : forall s s' t c d, eval_b t s -> l |~ Some s >- c ---> s' ->
  l |~ Some s >- ifte t c d ---> s'
| exec_ifte_false : forall s s' t c d, ~~ eval_b t s -> l |~ Some s >- d ---> s' ->
  l |~ Some s >- ifte t c d ---> s'
| exec_while_true : forall s s' s'' t c, eval_b t s -> l |~ Some s >- c ---> s' ->
  l |~ s' >- while t c ---> s'' -> l |~ Some s >- while t c ---> s''
| exec_while_false : forall s t c,
  ~~ eval_b t s -> l |~ Some s >- while t c ---> Some s
| exec_call_Some : forall s s' i pro,
    Procs.get i l = Some pro ->
    l |~ Some s >- pro ---> Some s' ->
    l |~ Some s >- call i ---> Some s'
| exec_call_None : forall s i pro,
    Procs.get i l = Some pro ->
    l |~ Some s >- pro ---> None ->
    l |~ Some s >- call i ---> None
| exec_call_err : forall s i,
    Procs.get i l = None ->
    l |~ Some s >- call i ---> None
where "l |~ s >- c ---> t" := (exec l s c t) : whilesemop_scope.

Lemma iexec_exec n l s c t : l |~ s >- c -^ n -> t -> l |~ s >- c ---> t.
Proof.
elim=> // {c s t} {}n => [* | * | | * | * | | * | | | * ].
- by apply exec_none.
- by apply exec_cmd0.
- move=> s s1 s2 c d _ Kc _ Kd; by apply exec_seq with s1.
- by apply exec_ifte_true.
- by apply exec_ifte_false.
- move=> s s1 s2 t c Ht _ Kc _ Kd; by apply exec_while_true with s1.
- by apply exec_while_false.
- move=> s s1 str pro Hfind _ Kpro; by apply exec_call_Some with pro.
- move=> s str pro Hfind _ Kpro; by apply exec_call_None with pro.
- by apply exec_call_err.
Qed.

Lemma iexec_from_None n l c s : l |~ None >- c -^ n -> s -> s = None.
Proof.
move Haux : (None) => aux H.
move: H Haux; elim=> // {n c s aux}.
- move=> _ s c s1 H ?; subst s; by apply from_none0 in H.
- move=> n s s1 s2 c d Hc IHc Hd IHd ?; subst s.
  move: (IHc Logic.eq_refl) => ?; subst s1; by apply IHd.
Qed.

Lemma iexec_incr  l n s s1 c :
  l |~ s >- c -^ n -> s1 ->
  forall m, n <= m ->
  l |~ s >- c -^ m -> s1.
Proof.
elim => // {n c s s1}.
- move=> n c m nm.
  by apply iexec_none.
- move=> n s c s1 Hc m nm.
  by apply iexec_cmd0.
- move=> n s s1 s2 c d Hc IHc Hd IHd m nm.
  apply iexec_seq with s1.
  by apply IHc.
  by apply IHd.
- move=> n s s1 t c d Ht Hc IHc m nm.
  apply iexec_ifte_true => //.
  by apply IHc.
- move=> n s s1 t c d Ht H IHd m nm.
  apply iexec_ifte_false => //.
  by apply IHd.
- move=> n s s1 s2 t c Ht Hc IHc Hwhile IHwhile m nm.
  apply iexec_while_true with s1 => //.
  by apply IHc.
  by apply IHwhile.
- move=> n s t c Ht m nm.
  by apply iexec_while_false.
- move=> n s s1 str pro Hfind Hpro IH [|m] // nm.
  apply iexec_call_Some with pro => //.
  by apply IH.
- move=> n s str pro Hfind Hpro IH [|m] // nm.
  apply iexec_call_None with pro => //.
  by apply IH.
- move=> n s1 str Hfind [|m] // nm.
  by apply iexec_call_err.
Qed.

Lemma iexec_seq_exists l n1 s s1 c :
  l |~ s >- c -^ n1 -> s1 ->
  forall n2 d s2,
  l |~ s1 >- d -^ n2 -> s2 ->
  exists n, l |~ s >- c; d -^ n -> s2.
Proof.
move=> Hc n2 d s2 Hd.
exists (maxn n1 n2).
apply iexec_seq with s1.
  apply iexec_incr with n1 => //.
  by rewrite leq_max leqnn.
apply iexec_incr with n2 => //.
by rewrite leq_max leqnn orbC.
Qed.

Lemma exec_iexec l s c t : l |~ s >- c ---> t -> exists n, l |~ s >- c -^ n -> t.
Proof.
elim=> // {c s t}.
- move=> x.
  exists O.
  by apply iexec_none.
- move=> s c s1 Hc.
  exists O.
  by apply iexec_cmd0.
- move=> s s1 s2 c d Hc [n1 Kc] Hd [n2 Kd].
  by eapply iexec_seq_exists; eauto.
- move=> s s1 t c d Ht Hc [n IH].
  exists n.
  by apply iexec_ifte_true.
- move=> s s1 t c d Ht Hd [n IH].
  exists n.
  by apply iexec_ifte_false.
- move=> s s1 s2 t c Ht Hc [n IH] Hwhile [m IHwhile].
  exists (maxn n m).
  apply iexec_while_true with s1 => //.
  apply iexec_incr with n => //.
  by rewrite leq_max leqnn.
  apply iexec_incr with m => //.
  by rewrite leq_max leqnn orbC.
- move=> s t c Ht.
  exists O.
  by apply iexec_while_false.
- move=> s s1 str pro Hfind Hpro [n IH].
  exists (n.+1).
  by apply iexec_call_Some with pro.
- move=> s str pro Hfind Hpro [n IH].
  exists (n.+1).
  by apply iexec_call_None with pro.
- move=> s str Hfind.
  exists 1.
  by apply iexec_call_err.
Qed.

Lemma from_none : forall l c s, l |~ None >- c ---> s -> s = None.
Proof.
move Hs0 : None => s0.
move=> l c s H; move: H Hs0; elim => //.
- destruct s1 => // c' s'.
  by move/from_none0.
- move=> s1 s' s'' _ _ _ H _ H' H''; subst.
  have {H}H'' : s' = None by apply H.
  subst; by apply H'.
Qed.

(** Inversion lemmas: *)

Lemma exec_cmd0_inv s l (c : cmd0) s' :
  l |~ |_ s _| >- (cmd_cmd0 c) ---> s' -> |_ s _| -- c ----> s'.
Proof. by inversion 1. Qed.

Lemma exec0_not_None_to_exec_not_None s l (c : cmd0) :
  ~ l |~ Some s >- cmd_cmd0 c ---> None -> ~ Some s -- c ----> None.
Proof. move=> H H'. by apply H, exec_cmd0. Qed.

Lemma exec_seq_inv l c d s s' : l |~ s >- c ; d ---> s' ->
  exists s'', l |~ s >- c ---> s'' /\ l |~ s'' >- d ---> s'.
Proof.
move=> H.
inversion H; subst.
- exists None; by split; apply exec_none.
- by exists s'0.
Qed.

Lemma exec_seq_inv_Some l c d s s' : l |~ Some s >- c ; d ---> Some s' ->
  exists s'', l |~ Some s >- c ---> Some s'' /\ l |~ Some s'' >- d ---> Some s'.
Proof.
move=> H.
inversion H as [ | | s0 s1 s2 c1 c2 Hc1 Hc2 Hs0 Htmp Hs2 | | | | | | | ]; subst.
destruct s1 as [s1|].
  by exists s1.
by move/from_none : Hc2.
Qed.

Lemma exec_while_inv_false b l c s s' :  ~~ eval_b b s ->
  l |~ Some s >- while b c ---> Some s' -> s = s'.
Proof. 
move=> H H'; inversion H'; subst.
by rewrite H3 in H.
by inversion H'.
Qed.

Lemma exec_while_inv_true : forall b s, eval_b b s ->
  forall l c s', l |~ Some s >- while b c ---> Some s' ->
  exists s'', l |~ Some s >- c ---> Some s'' /\
              l |~ Some s'' >- while b c ---> Some s'.
Proof.
move=> b s H l c s'.
inversion 1; subst.
  destruct s'0 as [s''|].
    by exists s''.
  by move/from_none : H7.
by rewrite H in H3.
Qed.

Lemma exec_ifte_true_inv : forall t l c1 c2 s s', eval_b t s ->
  l |~ Some s >- ifte t c1 c2 ---> s' -> l |~ Some s >- c1 ---> s'.
Proof.
move=> t l c1 c2 s s' Ht; inversion 1. by subst.
by rewrite Ht in H5.
Qed.

Lemma exec_ifte_false_inv : forall t l c1 c2 s s', ~~ eval_b t s ->
  l |~ Some s >- ifte t c1 c2 ---> s' -> l |~ Some s >- c2 ---> s'.
Proof.
move=> t l c1 c2 s s' Ht; inversion 1.
by rewrite H5 in Ht. by subst.
Qed.

Lemma exec_seq_assoc : forall s s' l c0 c1 c2,
  l |~ s >- (c0 ; c1) ; c2 ---> s' -> l |~ s >- c0 ; c1 ; c2 ---> s'.
Proof.
move=> s s' l c0 c1 c2.
case/exec_seq_inv => s'' [].
case/exec_seq_inv => s''' [H1 H2] H3.
apply exec_seq with s''' => //.
by apply exec_seq with s''.
Qed.

Lemma exec_seq_assoc' : forall s s' l c0 c1 c2,
  l |~ s >- c0 ; c1 ; c2 ---> s' -> l |~ s >- (c0 ; c1) ; c2 ---> s'.
Proof.
move=> s s' l c0 c1 c2.
case/exec_seq_inv => s'' [] H1.
case/exec_seq_inv => s''' [] H2 H3.
apply exec_seq with s''' => //.
by apply exec_seq with s''.
Qed.

Lemma while_seq : forall s t, eval_b t s -> forall s' l c,
  l |~ Some s >- while t c ---> s' -> l |~ Some s >- c ; while t c ---> s'.
Proof.
move=> s t Ht sigma' l c.
inversion 1 as [ | | | | | | | | | ]; subst.
- by apply exec_seq with s'.
- by rewrite Ht in H0.
Qed.

Lemma while_seq' : forall s t, eval_b t s -> forall s' l c,
  l |~ Some s >- c ; while t c ---> s' -> l |~ Some s >- while t c ---> s'.
Proof.
move=> s t Hneq s' l c; inversion 1; subst.
by apply exec_while_true with s'0.
Qed.

Lemma exec_seq1_not_None : forall s l c1 c2,
  ~ l |~ Some s >- c1 ; c2 ---> None -> ~ l |~ Some s >- c1 ---> None.
Proof.
move=> ? ? ? ? H; contradict H; apply exec_seq with None=> //; apply exec_none.
Qed.

Lemma exec_seq2_not_None : forall s s' l c1 c2,
  ~ l |~ Some s >- c1 ; c2 ---> None -> l |~ Some s >- c1 ---> Some s' ->
  ~ l |~ Some s' >- c2 ---> None.
Proof.
move=> s s' l c1 c2 H H'. contradict H. by apply exec_seq with (Some s').
Qed.

Lemma exec_ifte1_not_None : forall s l c1 c2 t,
  ~ l |~ Some s >- ifte t c1 c2 ---> None -> eval_b t s ->
  ~ l |~ Some s >- c1 ---> None.
Proof. move=> ? ? ? ? ? H ?. contradict H. by apply exec_ifte_true. Qed.

Lemma exec_ifte2_not_None : forall s l c1 c2 t,
  ~ l |~ Some s >- ifte t c1 c2 ---> None -> ~~ eval_b t s ->
  ~ l |~ Some s >- c2 ---> None.
Proof. move=> ? ? ? ? ? H ?. contradict H. by apply exec_ifte_false. Qed.

Lemma exec_while1_not_None : forall s t l c,
  ~ l |~ Some s >- while t c ---> None -> eval_b t s ->
  ~ l |~ Some s >- c ---> None.
Proof.
move=> ? ? ? ? H ?. contradict H. apply exec_while_true with None=> //. by apply exec_none.
Qed.

Lemma exec_while2_not_None s l c t s0 :
  ~ l |~ Some s >- while t c ---> None -> eval_b t s ->
  l |~ Some s >- c ---> Some s0 -> ~ l |~ Some s0 >- while t c ---> None.
Proof.
move=> H ? ?. contradict H. by apply exec_while_true with (Some s0).
Qed.

Lemma not_exec_seq_inv_Some l c d s : ~ l |~ Some s >- c ; d ---> None ->
  ~ l |~ Some s >- c  ---> None /\
  forall s', l |~ Some s >- c ---> Some s' -> ~ (l |~ Some s' >- d ---> None).
Proof.
move=> H; split.
- contradict H; apply exec_seq with None => //; by apply exec_none.
- move=> s' Hc H'; apply H; by apply exec_seq with (Some s').
Qed.

Lemma not_exec_ifte_inv_Some b l c d s :
  ~ l |~ Some s >- ifte b c d ---> None ->
  (eval_b b s -> ~ l |~ Some s >- c  ---> None) /\
  (~~ eval_b b s -> ~ l |~ Some s >- d  ---> None).
Proof.
move=> H.
case/boolP : (eval_b b s) => // Hb.
- split=> [_ H'| //].
  apply H; by constructor.
- split=> X H'.
  + by move/negP : Hb.
  + by apply H; apply exec_ifte_false.
Qed.

(*
TODO: note used anymore?
Lemma while_preserves : forall t l c (P : store -> Prop) s h s' h', P s ->
  l |~ Some (s, h) >- while t c ---> Some (s', h') ->
  (forall s h s' h', P s -> eval_b t (s, h) -> l |~ Some (s, h) >- c ---> Some (s', h') -> P s') ->
  P s'.
Proof.
move=> t l c P s h s' h' HP.
move HS : (Some (s, h)) => S.
move HS' : (Some (s', h')) => S'.
move HC : (while t c) => C Hexec.
move: Hexec s h HS s' h' HS' t c HC HP; elim => //.
- move=> [s h] s' s'' t c H H0 _ H2 H3 s0 h0 HS s'0 h'0 HS' t0 c0 HC HP H4.
  case: HS => ? ?; subst s0 h0.
  case: HC => ? ?; subst t0 c0.
  destruct s'' as [[s0 h0]|]; last by done.
  case: HS' => ? ?; subst s'0 h'0.
  destruct s' as [[s1 h1]|].
  + apply (H3 _ _ (refl_equal _) _ _ (refl_equal _) _ _ (refl_equal _)) => //.
    by apply (H4 _ _ _ _ HP H H0).
  + by move/from_none : H2.
- move=> [s h] t c H s0 h0 HS s' h' HS' t0 c0 HC HP H0.
  case: HS => ? ?; subst s0 h0.
  case: HS' => ? ?; by subst s' h'.
Qed.*)

Lemma while_condition_inv s s' b l c :
  l |~ Some s >- while b c ---> Some s' -> ~~ eval_b b s'.
Proof.
move HS : (Some s) => S.
move HS' : (Some s') => S'.
move HC : (while b c) => C Hexec.
move: Hexec s HS s' HS' b c HC; elim => //.
- move=> s s' s'' t c t_s exec_c _ exec_while_t_c IH s0.
  case=> ?; subst s0 => s'0.
  destruct s'' as [s''|] => //.
  case=> ?; subst s'0 => t0 c0.
  case=> ? ?; subst t0 c0.
  destruct s' as [s'|]; last first.
    by move/from_none : exec_while_t_c.
  by eapply IH; eauto.
- move=> s t c t_s s0 Hs s' Hs'h' t0 c0.
  case=> ? ?; subst t0 c0.
  rewrite -Hs in Hs'h'.
  case: Hs'h' => ?; subst s0.
  by case: Hs => ->.
Qed.

End WhileSemop.

(********************************************************)

Require Import Ensembles.

Module Type WhileSemaxSemantics (ST : StateBipl) (B : Bipl ST) (L: WhileSemop0 ST B).

Include (WhileSemop ST B L).

(** We now come to the formalization of textbook Hoare logic. Actually, we allow
   for an extension of Hoare logic with a notion of pointer and mutable memory (or heap for short) known
   as Separation logic. Assertions are shallow-encoded. *)

Local Open Scope lang_scope.
Local Open Scope whilesemop_scope.

Inductive triple := mkTriple :
  assert -> string -> assert -> triple.

Definition pre t := match t with mkTriple x _ _ => x end.
Definition callee t := match t with mkTriple _ x _ => x end.
Definition post t := match t with mkTriple _ _ x => x end.

Definition hoare_semantics_n n (P : assert) l (c : cmd) (Q : assert) : Prop :=
  forall s, P s -> ~ l |~ Some s >- c -^ n -> None /\
    (forall s', l |~ Some s >- c -^ n -> Some s' -> Q s').

Notation "l |= n {{ P }} c {{ Q }}" := (hoare_semantics_n n P l c Q) (at level 70, n, P, c, Q at next level,
format "l  |= n {{  P  }}  c  {{  Q  }}").

Lemma hoare_semantics_0 : forall P l i Q, l |= 0 {{ P }} call i {{ Q }}.
Proof.
rewrite /hoare_semantics_n => s hPsh.
split.
  by inversion 1.
move=> s'.
by inversion 1.
Qed.

Lemma hoare_semantics_Sn n P l prg Q : l |= n.+1 {{ P }} prg {{ Q }} ->
  l |= n {{ P }} prg {{ Q }}.
Proof.
rewrite /hoare_semantics_n.
move=> H s.
case/H => H1 H2.
split.
  contradict H1.
  by apply iexec_S with n.
move=> s' H'.
apply H2.
by apply iexec_S with n.
Qed.

Definition hoare_semantics (P : assert) l (c : cmd) (Q : assert) : Prop :=
  forall s, P s -> ~ l |~ Some s >- c ---> None /\
    (forall s', l |~ Some s >- c ---> Some s' -> Q s').

Notation "l |={{ P }} c {{ Q }}" := (hoare_semantics P l c Q) (at level 70, P, c, Q at next level,
  format "l  |={{  P  }}  c  {{  Q  }}").

Lemma hoare_semantics_n_semantics l P c Q :
  l |={{ P }} c {{ Q }} <-> forall n, l |= n {{ P }} c {{ Q }}.
Proof.
rewrite /hoare_semantics_n /hoare_semantics; split => H.
  move=> n s.
  case/H => H1 H2.
  split.
    contradict H1.
    by apply iexec_exec with n.
  move=> s1 Psh1.
  apply H2.
  by apply iexec_exec with n.
move=> s Psh.
split.
  case/exec_iexec => n H1.
  by case: (H n _ Psh).
move=> s1.
case/exec_iexec => n Psh1.
move: (H n _ Psh) => [] ? ?; by auto.
Qed.

Inductive ftriple := mkFTriple :
  (state -> Prop) -> string -> (state -> Prop) -> ftriple.

Definition fpre t := match t with mkFTriple x _ _ => x end.
Definition fcallee t := match t with mkFTriple _ x _ => x end.
Definition fpost t := match t with mkFTriple _ _ x => x end.

Definition hoare_sem_ctxt_n l' n P l c Q :=
  (forall t : ftriple, Ensembles.In _ l' t -> l |= n {{ (fpre t) }} call (fcallee t) {{ (fpost t) }}) ->
  l |= n {{ P }} c {{ Q }}.

Notation "l \^ l' |= n {{ P }} c {{ Q }}" := (hoare_sem_ctxt_n l' n P l c Q) (at level 70, l', n, P, c, Q at next level,
  format "l \^ l' |= n {{  P  }}  c  {{  Q  }}").

Definition hoare_sem_ctxt l' P l c Q :=
  (forall t : ftriple, Ensembles.In _ l' t -> l |={{ (fpre t) }} call (fcallee t) {{ (fpost t) }}) ->
  l |={{ P }} c {{ Q }}.

Notation "l \^ l' |={{ P }} c {{ Q }}" := (hoare_sem_ctxt l' P l c Q) (at level 70, l', P, c, Q at next level,
  format "l \^ l' |={{  P  }}  c  {{  Q  }}").

(* NB: the other direction fails *)
Lemma hoare_sem_ctxt_n_sem_ctxt : forall l l' P c Q,
  (forall n, l \^ l' |= n {{ P }} c {{ Q }}) ->
  l \^ l' |={{ P }} c {{ Q }}.
Proof.
move=> l l' P c Q.
rewrite /hoare_sem_ctxt_n /hoare_sem_ctxt => H K.
apply hoare_semantics_n_semantics => n.
apply H => // => t Ht ls.
apply hoare_semantics_n_semantics.
apply K => //.
Qed.

(*Definition wp_semantics l (c : cmd) (Q : assert) : assert :=
  fun s h => ~ (l |~ Some (s, h) >- c ---> None) /\
    forall s' h', l |~ Some (s, h) >- c ---> Some (s', h') -> Q s' h'.

Definition hoare_semantics_total (P : assert) l (c : cmd) (Q : assert) : Prop :=
  forall s h, P s h ->
    exists s' h', l |~ Some (s, h) >- c ---> Some (s', h') /\  Q s' h'.*)

End WhileSemaxSemantics.

(********************************************************)

Module Type WhileSemax0 (ST : StateBipl) (B : Bipl ST) (L: WhileSemop0 ST B).

Include (WhileSemaxSemantics ST B L).

Parameter hoare0 : assert -> cmd0 -> assert -> Prop.

Parameter soundness0 : forall P Q l c, hoare0 P c Q -> forall n, l |= n {{ P }} cmd_cmd0 c {{ Q }}.

End WhileSemax0.

(********************************************************)

Module Type WhileHoare (ST : StateBipl) (B : Bipl ST) (Semop: WhileSemop0 ST B) (Hoare : WhileSemax0 ST B Semop).

Include Hoare.

Local Open Scope lang_scope.
Local Open Scope whilesemop_scope.
Local Open Scope statebipl_scope.

(** The axioms of Hoare logic are encoded as an inductive type,
    assuming given Hoare triples for one-step, non-branching instructions. *)

Definition assert_of_old (x : gstore * heap -> Prop) : assert :=
  fun s => x (gstate s, hstate s).

Reserved Notation "l \^ E |~{[ P ]} c {[ Q ]}" (at level 70, E, P, c, Q at next level, no associativity).

Inductive hoare (l  : procs) : Ensemble ftriple -> assert -> cmd -> assert -> Prop :=
| hoare_hoare0 : forall E P Q c, hoare0 P c Q -> l \^ E |~{[ P ]} (cmd_cmd0 c) {[ Q ]}
| hoare_seq : forall Q E P R c d, l \^ E |~{[ P ]} c {[ Q ]} ->
  l \^ E |~{[ Q ]} d {[ R ]} -> l \^ E |~{[ P ]} c ; d {[ R ]}
| hoare_conseq_new : forall E c (P Q : assert),
(forall s, P s -> exists P' Q',
  l \^ E |~{[ P' ]} c {[ Q' ]} /\ P' s /\ (Q' ===> Q)) ->
  l \^ E |~{[ P ]} c {[ Q ]}
| hoare_while : forall E P t c, l \^ E |~{[ fun s => P s /\ eval_b t s ]} c {[ P ]} ->
  l \^ E |~{[ P ]} while t c {[ fun s => P s /\ ~~ eval_b t s ]}
| hoare_ifte : forall E P Q t c d, l \^ E |~{[ fun s => P s /\ eval_b t s ]} c {[ Q ]} ->
  l \^ E |~{[ fun s => P s /\ ~~ eval_b t s ]} d {[ Q ]} ->
  l \^ E |~{[ P ]} ifte t c d {[ Q ]}
| hoare_call : forall E P' Q' i (lnew : Ensemble ftriple),
  Ensembles.In _ lnew (mkFTriple (P') i (Q')) ->
  (forall t : ftriple, Ensembles.In _ lnew t ->
   ~ Procs.get (fcallee t) l = None /\
   forall pro, Procs.get (fcallee t) l = Some pro ->
   (l \^ (Union _ E lnew) |~{[ (fpre t) ]} pro {[ (fpost t) ]})) ->
  l \^ E |~{[ P' ]} call i {[ Q' ]}
| hoare_call2 : forall E P' Q' i,
  Ensembles.In _ E (mkFTriple (P') i (Q')) ->
  l \^ E |~{[ P' ]} call i {[ Q' ]}
| hoare_exfalso : forall E P c Q,
  (forall n, l \^ E |= n {{ P }} c {{ Q }}) -> ~ l |={{ P }} c {{ Q}} ->
  l \^ E |~{[ P ]} c {[ Q ]} (* sound by definition *)
where "l \^ E |~{[ P ]} c {[ Q ]}" := (hoare l E P c Q) : whilehoare_scope.

Notation "l \^ l' |-{{ P }} c {{ Q }}" := (hoare l l' P c Q) (at level 70, l', P, c, Q at next level, no associativity) : whilehoare_scope.

Local Open Scope whilehoare_scope.

Lemma hoare_conseq l l' P P' Q Q' c : Q' ===> Q -> P ===> P' ->
  l \^ l' |-{{ P' }} c {{ Q' }} -> l \^ l' |-{{ P }} c {{ Q }}.
Proof.
intros.
apply hoare_conseq_new => s Psh.
exists P', Q'; split; first by assumption.
split; [by apply H0 | done].
Qed.

Lemma hoare_conseq_indep l l' (P Q : assert) (R : Prop) c :
  (forall s, P s -> R) ->
  (R -> l \^ l' |-{{ P }} c {{ Q }}) ->
  l \^ l' |-{{ P }} c {{ Q }}.
Proof.
intros.
apply hoare_conseq_new => s Psh.
exists P, Q.
split => //; last by intuition.
by apply H0, (H _ Psh).
Qed.

Lemma hoare_conseq_aux l l' c (P Q : assert) (P' Q' : state -> assert) :
  (forall s, l \^ l' |-{{ P' s }} c {{ Q' s }}) ->
  (forall s, P s -> exists s', P' s' s /\ (entails (Q' s') Q)) ->
  l \^ l' |-{{ P }} c {{ Q }}.
Proof.
intros.
apply hoare_conseq_new => s Psh.
case/H0 : Psh => s1 [] H1 H2.
by exists (P' s1), (Q' s1).
Qed.

Lemma hoare_ind2 : forall (l : procs)
         (P : Ensemble ftriple -> assert -> cmd -> assert -> Prop),
       (forall (l' : Ensemble ftriple) (P0 Q : assert) (c : cmd0),
        hoare0 P0 c Q -> P l' P0 (cmd_cmd0 c) Q) ->
       (forall (l' : Ensemble ftriple) (P0 Q R : assert) (c d : cmd),
        hoare l l' P0 c Q ->
        P l' P0 c Q -> hoare l l' Q d R -> P l' Q d R -> P l' P0 (c; d) R) ->
(forall (l' : Ensemble ftriple) (c : cmd) (P0 Q : assert),
        (forall (s : state),
         P0 s ->
         exists P' Q' : assert,
           P l' P' c Q' /\ (*(l \^ l' |-{{ P'}}c {{Q'}}) /\*) P' s /\ (Q' ===> Q)) ->
        P l' P0 c Q) ->
       (forall (l' : Ensemble ftriple) (P0 : state -> Prop)
          (t : expr_b) (c : cmd),
        hoare l l' (fun s => P0 s /\ eval_b t s)
          c P0 ->
        P l' (fun s => P0 s /\ eval_b t s) c P0 ->
        P l' P0 (While t {{
                   c
                 }})
          (fun s => P0 s /\ ~~ eval_b t s)) ->
       (forall (l' : Ensemble ftriple) (P0 : state -> Prop)
          (Q : assert) (t : expr_b) (c d : cmd),
        hoare l l' (fun (s : state) => P0 s /\ eval_b t s)
          c Q ->
        P l' (fun s => P0 s /\ eval_b t s) c Q ->
        hoare l l' (fun s => P0 s /\ ~~ eval_b t s) d Q ->
        P l' (fun s => P0 s /\ ~~ eval_b t s) d Q ->
        P l' P0 (If t Then
                   c
                 Else
                   d
                 ) Q) ->
       (forall (l' : Ensemble ftriple) P' Q' (i : string) lnew,
        Ensembles.In _ lnew (mkFTriple (P') i (Q')) /\
        (forall t : ftriple,
         Ensembles.In _ lnew t ->
         Procs.get (fcallee t) l <> None /\
         (forall pro,
          Procs.get (fcallee t) l = Some pro ->
(*          hoare l l'' (pre t) (body pro) (post t) ->*)
          (P (Union _ l' lnew) ((fpre t)) pro ((fpost t))))) ->
        P l' ( P') (call i) (Q')) ->
       (forall (l' : Ensemble ftriple) P' Q' (i : string),
        Ensembles.In _ l' (mkFTriple (P') i (Q')) -> P l' (P') (call i) (Q')) ->
(forall (l' : Ensemble ftriple) (P0 : assert) (c : cmd) (Q : assert),
        (forall n : nat, l \^ l'|= n {{ P0 }} c {{ Q }}) ->
        ~ l |={{ P0 }} c {{ Q }} -> P l' P0 c Q) ->
       forall (l0 : Ensemble ftriple) (a : assert) (c : cmd) (a0 : assert),
       hoare l l0 a c a0 -> P l0 a c a0.
Proof.
fix hoare_ind2 15.
intros.
destruct H7.
by apply H.
apply H0 with Q => //.
apply hoare_ind2 with l => //.
apply hoare_ind2 with l => //.

apply H1 => //.
move=> s.
move/H7.
case=> P' [] Q' K.
exists P', Q'.
split.
apply hoare_ind2 with l => //.
tauto.
tauto.

apply H2 => //.
apply hoare_ind2 with l => //.
apply H3 => //.
apply hoare_ind2 with l => //.
apply hoare_ind2 with l => //.

apply H4 with lnew => //.
split => // t t_lnew.
case: (H8 _ t_lnew) => {}H7 H7'.
split => // pro Hpro.
move: (H7' _ Hpro) => Hhoare.
apply hoare_ind2 with l => //.
by apply H5.

apply H6.
exact H7.
exact H8.
Qed.

(*Reserved Notation "l \^ l' |-{{{[ P ]}}} c {{{[ Q ]}}}" (at level 82, no associativity).

Inductive hoare_total (l : list procedure) : list triple -> assert -> cmd -> assert -> Prop :=
| hoaret_hoare0 : forall l' P Q c, hoare0 P c Q ->
    l \^ l' |-{{{[ P ]}}} (cmd_cmd0 c) {{{[ Q ]}}}
| hoaret_seq : forall l' P Q R c d,
    l \^ l' |-{{{[ P ]}}} c {{{[ Q ]}}} -> l \^ l' |-{{{[ Q ]}}} d {{{[ R ]}}} ->
    l \^ l' |-{{{[ P ]}}} c ; d {{{[ R ]}}}
| hoaret_conseq : forall l' P P' Q Q' c, (Q' ===> Q) -> (P ===> P') ->
  l \^ l' |-{{{[ P' ]}}} c {{{[ Q' ]}}} -> l \^ l' |-{{{[ P ]}}} c {{{[ Q ]}}}
| hoaret_while : forall l' P t c
  A (R : A -> A -> Prop) (Rwf : well_founded R) (V : state -> A) a,
  (forall a, l \^ l' |-{{{[ fun s h => P s h /\ eval_b t (s, h) /\ V (s,h) = a ]}}}
                       c
                       {{{[ fun s h => P s h /\ R (V (s,h)) a ]}}}) ->
  l \^ l' |-{{{[ fun s h => P s h /\ V (s,h) = a ]}}}
    while t c {{{[ fun s h => P s h /\ ~~ eval_b t (s, h) ]}}}
| hoaret_ifte : forall l' P Q t c d,
  l \^ l' |-{{{[ fun s1 h => P s1 h /\ eval_b t (s1, h) ]}}} c {{{[ Q ]}}} ->
  l \^ l' |-{{{[ fun s1 h => P s1 h /\ ~~ eval_b t (s1, h) ]}}} d {{{[ Q ]}}} ->
  l \^ l' |-{{{[ P ]}}} ifte t c d {{{[ Q ]}}}
| hoaret_call : forall l' P Q i pro l'',
  List.find (fun x => name x == i) l = Some pro ->
  Permutation (mkTriple P i Q :: l') l'' ->
  l \^ l'' |-{{{[ P ]}}} body pro {{{[ Q ]}}} ->
  l \^ l' |-{{{[ P ]}}} call i {{{[ Q ]}}}
| hoaret_call2 : forall l' P Q i,
  List.In (mkTriple P i Q) l' ->
  l \^ l' |-{{{[ P ]}}} call i {{{[ Q ]}}}
where "l \^ l' |-{{{[ P ]}}} c {{{[ Q ]}}}" := (hoare_total l l' P c Q) : whilehoare_scope.

Notation "l \^ l' |-{{{ P }}} c {{{ Q }}}" := (hoare_total l l' P c Q) (at level 82, no associativity) : whilehoare_scope.
*)

Lemma hoare_stren P' l' P Q l c : P ===> P' ->
  l \^ l' |-{{ P' }} c {{ Q }} -> l \^ l' |-{{ P }} c {{ Q }}.
Proof. move=> H H'. apply hoare_conseq with P' Q => //. Qed.

Lemma hoare_stren_seq l' (P P' Q Q' : assert) l c c' : l \^ l' |-{{ P' }} c {{ Q' }} ->
  P ===> P' -> l \^ l' |-{{ Q' }} c' {{ Q }} -> l \^ l' |-{{ P }} c; c' {{ Q }}.
Proof.
move=> Hc HP Hc'; apply hoare_seq with Q' => //; by apply (hoare_stren P').
Qed.

Lemma hoare_weak Q' l' (P Q : assert) l c :
  Q' ===> Q -> l \^ l' |-{{ P }} c {{ Q' }} -> l \^ l' |-{{ P }} c {{ Q }}.
Proof. move=> H H'. by apply hoare_conseq with P Q'. Qed.

(*Require Import ClassicalChoice.*)

(*
Lemma hoare_seq_inv : forall l' P Q l c d, l \^ l' |-{{ P }} c ; d {{ Q }} ->
  exists R, l \^ l' |-{{ P }} c {{ R }} /\ (l \^ l' |-{{ R }} d {{ Q }}). (* TODO notation level *)
Proof.
move=> l' P Q l c d.
move H : (c ; d) => Hcd.
move=> H'; move: H' c d H.
move=> H'.
elim H' using hoare_ind => //; clear H' l' P Q Hcd.
- move=> l' P Q R c d Hc H1 Hd H2 c0 d0.
  case=> X Y; subst; by exists Q.
- move=> l' P P' Q Q' c HQ HP Hc IH c0 d.
  case/IH => R [H1 H2].
  exists R; split; by [eapply hoare_stren; eauto | eapply hoare_weak; eauto].
(*- move=> l' P c Q i P1 Q1 P2 Q2 P12 Q21 H IH c0 d ?; subst c.
  case: {IH}(IH _ _ (refl_equal _)) => R [] H1 H2.
  exists R; split.
  by eapply hoare_conseq_L; eauto.
  by eapply hoare_conseq_L; eauto.*)
Qed.*)


(*Lemma hoare_seq_inv_special : forall (A : Type) l' (P Q : A -> assert) l c d,
  (forall x, l \^ l' |-{{ P x }} c ; d {{ Q x }}) ->
  exists R : A -> assert,
    (forall x, l \^ l' |-{{ P x }} c {{ R x }}) /\ (forall x, l \^ l' |-{{ R x }} d {{ Q x }}).
Proof.
move=> A l' P Q l c d H.
have Y : forall x : A, exists R, l \^ l' |-{{ P x }} c{{ R }} /\ (l \^ l' |-{{ R }} d {{ Q x }}).
  move=> ?; by eapply hoare_seq_inv; eauto.
case/choice : Y => f Y.
exists f; split=> a; by [apply (proj1 (Y a)) | apply (proj2 (Y a))].
Qed.*)

(*Lemma hoare_seq_inv_special' : forall (A : Type) l' (P Q : A -> assert) l c d,
  (forall x, exists y, l \^ l' |-{{ P x }} c ; d {{ Q y }}) ->
  exists R : A -> assert,
    (forall x, exists y, l \^ l' |-{{ P x }} c {{ R y }}) /\ (forall x, exists y, l \^ l' |-{{ R x }} d {{ Q y }}).
Proof.
move=> A l' P Q l c d H.
have Y : forall x : A, exists y R, l \^ l' |-{{ P x }} c{{ R }} /\ (l \^ l' |-{{ R }} d {{ Q y }}).
  - move => x; move: {H}(H x) => [] y Hy; exists y.
    by eapply hoare_seq_inv; eauto.
case/choice : Y => f Y.
case/choice : Y => f2 Y.
exists f2; split=> a.
exists a.
by apply (proj1 (Y a)).
exists (f a).
by apply (proj2 (Y a)).
Qed.*)

(*Lemma hoare_seq_assoc : forall l' P l c0 c1 c2 Q,
  l \^ l' |-{{ P }} c0 ; c1 ; c2 {{ Q }}  ->  l \^ l' |-{{ P }} (c0 ; c1) ; c2 {{ Q }}.
Proof.
move=> l' P l c0 c1 c2 Q.
case/hoare_seq_inv => s'' [] Hc0.
case/hoare_seq_inv => s''' [] Hc1 Hc2.
apply hoare_seq with s''' => //.
by apply hoare_seq with s''.
Qed.*)

(*Lemma hoare_ifte_inv : forall l' P Q b l c d, l \^ l' |-{{ P }} ifte b c d {{ Q }} ->
  l \^ l' |-{{ fun s => P s /\ eval_b b s }} c {{ Q }} /\
  (l \^ l' |-{{ fun s => P s /\ ~~ eval_b b s }} d {{ Q }}).
Proof.
move=> l' P Q b l c d.
move H : (ifte b c d) => Hbcd.
move=> H'; move: H' b c d H.
elim=> //; clear l' P Q Hbcd.
- move=> l' c0 P Q IH b c d Hifte.
  destruct c0 => //.
  case: Hifte => ? ? ?; subst e c0_1 c0_2.
(*  case: {IH Hifte}(IH _ _ _ Hifte) => H1 H2; split.
  + eapply hoare_weak; eauto.
    eapply hoare_stren; eauto.
    move=> s h /= [H3 H4]; split => //.
    by apply HP.
  + eapply hoare_weak; eauto.
    eapply hoare_stren; eauto.
    move=> s h /= [H3 H4]; split => //.
    by apply HP.*)
  admit.
- move=> l' P Q b c d Hc IHc Hd IHd b' c' d'.
  case=> X Y Z; by subst.
(*- move=> l' P c Q i P1 Q1 P2 Q2 P12 Q21 H IH b c0 d0 ?; subst c.
  case: {IH}(IH _ _ _ (refl_equal _)) => H1 H2.
  split.
    by eapply hoare_conseq_L; eauto.
  by eapply hoare_conseq_L; eauto.*)
Abort.
*)

Lemma hoare_while_invariant : forall l' P t l c Q Inv, P ===> Inv ->
  (fun s => Inv s /\ ~~ eval_b t s) ===> Q ->
  l \^ l' |-{{ fun s => Inv s /\ eval_b t s }} c {{ Inv }} ->
  l \^ l' |-{{ P }} while t c {{ Q }}.
Proof.
move=> l' P t0 l c0 Q Inv HP HQ H.
apply (hoare_stren Inv) => //.
apply (hoare_weak (fun s => Inv s /\ ~~ eval_b t0 s)) => //.
by apply hoare_while.
Qed.

Lemma hoare_while_invariant_seq : forall b l c I l' P Q c1,
  P ===> I ->
  l \^ l' |-{{ fun s => I s /\ eval_b b s }} c {{ I }} ->
  l \^ l' |-{{ fun s => I s /\ ~~ eval_b b s }} c1 {{ Q }} ->
  l \^ l' |-{{ P }} while b c; c1 {{ Q }}.
Proof.
intros.
apply hoare_seq with (fun s => I s /\ ~~ eval_b b s) => //.
by eapply hoare_while_invariant; eauto.
Qed.

Lemma hoare_while_inv' : forall l' P Q b l c, l \^ l' |-{{ P }} while b c {{ Q }} ->
  exists R, (P ===> R) /\
    (l \^ l' |-{{ fun s => R s /\ eval_b b s }} c {{ R }}) /\
    ((fun s => R s /\ ~~ eval_b b s) ===> Q).
Proof.
move=> l' P Q b l c.
move Hwhile : (while b c) => c'.
move=> H.
move: H b c Hwhile.
elim => //; clear l' P Q c'.
(*- move=> l' P P' Q Q' c' HQ HP Hc IHc b c Hwhile.
  move: {IHc Hwhile}(IHc _ _ Hwhile) => [R [X1 [X2 X3] ] ].
  exists R; split.
  by apply ent_trans with P'.
  split => //.
  by eapply ent_trans; eauto.*) admit.
- move=> l' P b c Hc IH b' c'.
  case=> X Y; subst.
  exists P; split; first by [].
  by split.
(*- move=> l' P c Q i P1 Q1 P2 Q2 P12 Q21 H IH b c0 ?; subst c.
  case: {IH}(IH _ _ (refl_equal _)) => R [] H1 [H2 H3].
  exists R; split => //.
  split => //.
  by eapply hoare_conseq_L; eauto.*)
Abort.

(*
Lemma hoare_while_inv_special : forall (A : Type) l' (P Q : A -> assert) b l c,
  (forall x, l \^ l' |-{{ P x }} while b c {{ Q x }}) ->
  exists R : A -> assert,
    (forall x, l \^ l' |-{{ fun s h => R x s h /\ eval_b b (s, h) }} c {{ R x }}) /\
    (forall x, (P x ===> R x)) /\
    (forall x, ((fun s h =>  R x s h /\ ~~ eval_b b (s, h)) ===> Q x)).
Proof.
move=> A l' P Q b l c H.
have Y : forall x : A, exists R : A -> assert,
    l \^ l' |-{{ fun s h => R x s h /\ eval_b b (s, h) }} c {{ R x }} /\
    (P x ===> R x) /\
    ((fun s h =>  R x s h /\ ~~ eval_b b (s, h)) ===> Q x).
  move=> a.
  move: (H a) => Ha.
  case: (hoare_while_inv' _ _ _ _ _ _ Ha) => R [X1 [X2 X3]].
  by exists (fun x : A => R).
case/choice : Y=> f Y.
exists (fun x => f x x); split.
- move=> a; by apply (proj1 (Y a)).
- split => a; by [apply (proj1 (proj2 (Y a))) | apply (proj2 (proj2 (Y a)))].
Qed.
*)

(*Lemma hoare_call_inv : forall l' P Q l i, l \^ l' |-{{ P }} call i {{ Q }} ->
  (exists P' Q' lnew,
    (P ===> P') /\ (Q' ===> Q) /\
    Ensembles.In _ lnew (mkFTriple P' i Q') /\
      forall t, Ensembles.In _ lnew t ->
      ~ List.find (fun x => name x == callee t) l = None /\
      forall pro, List.find (fun x => name x == callee t) l = Some pro ->
        (l \^ (Union _ l' lnew) |-{{ pre t }} body pro {{ post t }})) \/
  (exists P' Q',
    (P ===> P') /\ (Q' ===> Q) /\
    Ensembles.In _ l' (mkTriple P' i Q')).
Proof.
move=> l' P Q l i.
move H : (call i) => cmdi.
move=> H'; move: H' i H.
elim=> //; clear l' P Q cmdi.
Abort.*)
(*
- move=> l' P P' Q Q' c Q'Q PP' H' H i call_i.
  subst c.
  case: {H}(H i Logic.eq_refl).
    case=> P1 [] Q1 [] lnew [] P'P1 [] Q1Q' [] i_lnew H.
    left.
    exists P1, Q1, lnew; split.
      by apply ent_trans with P'.
    split.
      by apply ent_trans with Q'.
    by split => // t t_lnew.
  case=> P'' [] Q'' [] H1 [] H2 H3.
  right.
  exists P'', Q''.
  split. by apply ent_trans with P'.
  split. by apply ent_trans with Q'.
  assumption.
- move=> l' P Q i lnew i_lnew IH i_ [] ?; subst i_.
  left.
  exists P, Q, lnew.
  split; first by apply ent_id.
  split; first by apply ent_id.
  done.
(*- move=> l' P Q i pro Hpro H _ i0 [] ?; subst i0.
  exists pro, P, Q.
  split; first by apply ent_id.
  split => //; by apply ent_id.*)
- move=> l' P Q i HIn i0 [] ?; subst i0.
  right.
  exists P, Q.
  split. by apply ent_id.
  split. by apply ent_id.
  assumption.
Qed.*)

(*Lemma hoare_call_inv : forall l' P Q l i, l \^ l' |-{{ P }} call i {{ Q }} ->
  (exists pro P' Q' l'',
    (P ===> P') /\ (Q' ===> Q) /\
    List.find (fun x : procedure => name x == i) l = Some pro /\
    Permutation (mkTriple P' i Q' :: l') l'' /\
    (l \^ l'' |-{{ P }} body pro {{ Q }})) \/
  (exists P' Q',
    (P ===> P') /\ (Q' ===> Q) /\
    List.In (mkTriple P' i Q') l').
Proof.
move=> l' P Q l i.
move H : (call i) => cmdi.
move=> H'; move: H' i H.
elim=> //; clear l' P Q cmdi.
- move=> l' P P' Q Q' c Q'Q PP' H' H i call_i.
  subst c.
  case: {H}(H i Logic.eq_refl).
    case=> pro [] P1 [] Q1 [] l'' [] H1 [] H2 [] H3 [] H4 H5.
    left.
    exists pro, P1, Q1, l''; split.
      by apply ent_trans with P'.
    split.
      by apply ent_trans with Q'.
    split => //.
    split => //.
    apply hoare_stren with P' => //.
    by apply hoare_weak with Q'.
  case=> P'' [] Q'' [] H1 [] H2 H3.
  right.
  exists P'', Q''.
  split. by apply ent_trans with P'.
  split. by apply ent_trans with Q'.
  assumption.
- move=> l' P Q i pro l'' Hpro Hincl H _ i0 [] ?; subst i0.
  left.
  exists pro, P, Q, l''.
  split; first by apply ent_id.
  split; first by apply ent_id.
  by split.
(*- move=> l' P Q i pro Hpro H _ i0 [] ?; subst i0.
  exists pro, P, Q.
  split; first by apply ent_id.
  split => //; by apply ent_id.*)
- move=> l' P Q i HIn i0 [] ?; subst i0.
  right.
  exists P, Q.
  split. by apply ent_id.
  split. by apply ent_id.
  assumption.
Qed.*)

(*Lemma hoare_and'' : (forall P Q c, hoare0 P c Q ->
  forall l l' P' Q', l \^ l' |-{{P'}} (cmd_cmd0 c) {{Q'}} ->
                l \^ l' |-{{ P //\\ P' }} cmd_cmd0 c {{ Q //\\ Q' }}) ->
  forall l l',
  forall c P Q, l \^ l' |-{{ P }} c {{ Q }} ->
    forall P' Q' d, l \^ l' |-{{ P' }} d {{ Q' }} ->
      c = d -> l \^ l' |-{{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move=> H0 l l' c P Q H. elim H using hoare_ind2 => //; clear c P Q l' H.
- move=> l' P Q c P_c_Q P' Q' d P'_d_Q' c_d.
  apply H0 => //.
  subst d.
  exact P'_d_Q'.
- (* case seq *) move=> l' P Q R c d P_c_Q IHc Q_d_R IHd P' Q' d0 H ?; subst d0.
  apply hoare_seq_inv in H.
  case: H => R' [H1 H2].
  apply hoare_seq with (Q //\\ R').
  + by apply IHc with c.
  + by apply IHd with d.
- (* case conseq *)
  move=> l' P P' Q Q' c Q'_Q P_P' P'_c_Q' IH P'0 Q'0 d H2 H3.
  apply hoare_conseq with (P' //\\ P'0) (Q' //\\ Q'0).
  rewrite /And /entails => *; by intuition.
  rewrite /And /entails => *; by intuition.
  by apply (IH _ _ d).
- (* case while *) move=> l' P t c Hoare_c IH P' Q' d Hd d_while.
  subst d.
  apply hoare_while_inv' in Hd.
  case: Hd => R [H1 [H2 H3]].
  apply hoare_stren with (P //\\ R).
    rewrite /And => ? ?; by intuition.
  apply hoare_weak with (fun s h => (P //\\ R) s h /\ ~~ eval_b t (s, h)).
    rewrite /And => ? ?; by intuition.
  apply hoare_while => //.
  eapply hoare_stren; last first.
    eapply IH.
    by apply H2.
    reflexivity.
  rewrite /And => ? ?; by intuition.
- (* case ifte *) move=> l' P Q t c d Hoare_c IHc Hoare_d IHd P' Q' d0 Hd0 d0_if.
  subst d0.
  case/hoare_ifte_inv : Hd0 => H1 H2.
  apply hoare_ifte.
    eapply hoare_stren; last first.
      apply IHc with c => //.
      by apply H1.
    rewrite /And => ? ?; by intuition.
  eapply hoare_stren; last first.
    apply IHd with d => //.
    by apply H2.
  rewrite /And => ? ?; by intuition.
- (* case hoare_call *)
  move=> l' P Q i lnew [i_lnew IH] P' Q' [] // i_ H [] ?; subst i_.
  case/hoare_call_inv : H => [ [P'0 [Q'0 [lnew']]] |].
  + move=> [] P'P'0 [] Q'0Q' [] i_lnew' H'.
    apply hoare_call with (mkTriple (P //\\ P') i (Q //\\ Q') :: lnew ++ lnew').
      simpl; by auto.
    move=> t Ht.
    simpl in Ht.
    case: Ht => Ht.
      subst t.
      simpl.
    move: (IH _ i_lnew) => {IH} [] IH1 IH2.
    split => // pro Hpro l'' Hperm.
    apply IH2 with (body pro) => //=.
Abort.*)

(*Lemma hoare_and' : (forall P Q c, hoare0 P c Q ->
  forall P' Q', {{P'}} (cmd_cmd0 c) {{Q'}} ->{{P //\\ P'}}cmd_cmd0 c {{Q //\\ Q'}}) ->
forall c P Q P' Q',
  {{ P }} c {{ Q }} -> {{ P' }} c {{ Q' }} ->
  {{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof. intros. by apply hoare_and'' with c. Qed.*)

Lemma hoare_false' : forall l l',
  (forall (c0 : cmd0) P, l \^ l' |-{{ FF }} (cmd_cmd0 c0) {{ P }}) ->
  forall c P, l \^ l' |-{{ FF }} c {{ P }}.
Proof.
intros.
by apply hoare_conseq_indep with False.
(*move=> l l' Hp; induction c.
- intros P; by apply Hp.
- intros P; apply hoare_seq with (Q := FF); by [apply IHc1 | apply IHc2].
- intros P; apply hoare_ifte.
  + apply hoare_stren with (FF).
    rewrite /entails; by intuition.
    by apply IHc1.
  + apply hoare_stren with (FF).
    rewrite /entails; by intuition.
    by apply IHc2.
- intros P; apply hoare_weak with (fun s h =>
    (fun s' h' => P s' h' /\ ~~ eval_b e (s', h')) s h /\ ~~ eval_b e (s, h)).
  + rewrite /entails; by intuition.
  + apply hoare_stren with (fun s h => P s h /\ ~~ eval_b e (s, h)).
    * rewrite /entails; contradiction.
    * apply hoare_while.
      apply hoare_stren with (P':=FF).
      - rewrite /entails => s h [[H H2] H1]; by rewrite H1 in H2.
      - by apply IHc.*)
Qed.

(* TODO: redo using soundness/completeness? *)
(*Lemma pull_out_conjunction' : (forall (c0 : cmd0) P, {{ FF }} (cmd_cmd0 c0) {{ P }}) -> forall (A : Prop) P Q c,
  (A -> {{ P }} c {{ Q }}) ->
  {{ fun s h => A /\ P s h }} c {{ Q }}.
Proof.
move=> X A P Q c H.
case: (Classical_Prop.classic A) => HA.
eapply hoare_stren; last by apply H.
by move=> s h [].
eapply hoare_stren; last by apply hoare_false'.
move => s h []; by move/HA.
Qed.*)

(** The statement of this lemma as well as the proof idea of using ClassicalChoice comes from Andrew W. Appel, septacs.pdf *)
(*Lemma extract_exists :
  (forall (c : cmd0) (A : Type) (P Q : A -> assert),
    (forall x, {{ P x }} (cmd_cmd0 c) {{ Q x }}) ->
    {{ fun s h => exists x, P x s h }} (cmd_cmd0 c) {{ fun s h => exists x, Q x s h }}) ->
  forall (A : Type) (P Q : A -> assert) c,
  (forall x, {{ P x }} c {{ Q x}}) ->
  {{ fun s h => exists x, P x s h}} c {{ fun s h => exists x, Q x s h }}.
Proof.
move=> extract_exists0 A P Q c; move: c A P Q; elim.
- exact extract_exists0.
- move=> c IHc d IHd A P Q Hseq.
  have [R [X1 X2] ] : exists R : A -> assert,
    {{ fun s h => exists x, P x s h }} c {{ fun s h => exists x, R x s h }} /\
    {{ fun s h => exists x, R x s h }} d {{ fun s h => exists x, Q x s h }}.
    case: (hoare_seq_inv_special A P Q c d Hseq) => R [H1 H2].
    exists R; split.
    by apply IHc.
    by apply IHd.
  eapply hoare_seq; eauto.
- move=> b c IHc d IHd A P Q H.
  apply hoare_ifte.
  apply hoare_stren with (fun s h => (exists x0, P x0 s h /\ eval_b b (s, h))).
    move=> s h /= [ [a H1] H2].
    by exists a.
  apply IHc.
  move=> a.
  case/hoare_ifte_inv: (H a) => H' _ //.
  apply hoare_stren with (fun s h => (exists x0, P x0 s h /\ ~~ eval_b b (s, h))).
    move=> s h /= [ [a H1] H2].
    by exists a.
  apply IHd.
  move=> a.
  case/hoare_ifte_inv: (H a) => H' _ //.
- move=> b c IH A P Q H.
  have [R [X1 [X2 X3]]] : exists R : A -> assert,
    (forall s h, (exists x, P x s h) -> exists x, R x s h) /\
    {{ fun s h => (exists x, R x s h) /\ eval_b b (s, h) }} c {{ fun s h => exists x, R x s h }} /\
    (forall s h, ((exists x, R x s h) /\ ~~ eval_b b (s, h)) -> exists x, Q x s h).
    move: (hoare_while_inv_special _ _ _ _ _ H) => [R [X1 [X2 X3]]].
    exists R; split.
    + move=> s h /= [a X].
      exists a.
      by apply X2.
    + split.
      * move: {IH}(IH A _ _ X1) => IH.
        eapply hoare_stren; eauto.
        move=> s h /= [[a H1] H2].
        by exists a.
      * move=> s h [[a H1] H2].
        exists a.
        by apply X3.
  by apply hoare_while_invariant with (fun s h => exists x, R x s h).
Qed.

Lemma pull_out_exists' :
  (forall (c :cmd0) (A : Type) (P Q : A -> assert),
    (forall x, {{ P x }} (cmd_cmd0 c) {{ Q x }}) ->
    {{ fun s h => exists x, P x s h }} (cmd_cmd0 c) {{ fun s h => exists x, Q x s h }}) ->
  forall (A : Type) (P : A -> assert) c (Q : assert),
  (forall x, {{ P x }} c {{ Q }}) ->
  {{ fun s h => exists x, P x s h }} c {{ Q }}.
Proof.
move=> H0 A P c Q Hc.
eapply hoare_weak; last first.
apply (extract_exists H0 A P (fun x => Q) c) => //.
by move=> s h [].
Qed.
*)

Lemma hoare_sound_n l' P Q l c : l \^ l' |-{{ P }} c {{ Q }} -> forall n, l \^ l' |= n {{ P }} c {{ Q }}.
Proof.
move=> H.
elim H using hoare_ind2; clear H l' P Q c.
- (* cmd0 *) move=> l' P Q c H.
  move: (soundness0 _ _ l _ H) => K n.
  done.
- (* seq *) move=> l' P Q R c d HPcQ IHc HQdR IHd; split.
  + move=> HNone; inversion HNone; subst.
    destruct s' as [s'|].
    * move: (proj2 (IHc n H _ H0) _ H5) => HQ.
      by apply: (proj1 (IHd n H _ HQ)).
    * by apply (proj1 (IHc n H _ H0)).
  + move=> s' Hexec; inversion Hexec; subst.
    case: (IHc n H _ H0) => HcNone HcSome.
    destruct s'0 as [s''|].
    * move: (HcSome _ H5) => HQ.
      case: (IHd _ H _ HQ) => HdNone.
      by apply.
    * by inversion H7 => //.
- (* conseq *) move=> l' c P Q IH n H s HP.
  move: {IH}(IH _ HP) => [] P' [] Q' [] IH1 [] IH2 IH3.
  move: (IH1 n H _ IH2) => {IH1}[] IH1 IH1'.
  split => //.
  move=> s' H'.
  apply IH3.
  by apply IH1'.
(*
- (* conseq *) move=> l' P P' Q Q' c HQ'Q HPP' HP'cQ' IH; split.
  + move: (HPP' _ _ H0) => HP'.
    by apply (proj1 (IH _ H _ _ HP')).
  + move=> s' h' Hc.
    move: (HPP' _ _ H0) => HP'.
    case: (IH _ H _ _ HP') => HcNone HcSome.
    apply HQ'Q => //.
    by apply HcSome.
*)
- (* while *) move=> l' P t c H IH; split.
  + move Hd : (while t c) => d.
    move HS : (Some s) => S.
    move HS' : (@None state) => S'.
    move=> H2; move: l' t H IH s H0 H1 Hd HS HS'. elim: H2 => //.
    move=> n0 s s' s'' t c' H2 H3 _ H4 IHexec l' t' Hd IH s3 H HS [] X Y; subst.
    case => X; subst=> Hs''.
    case: (IH n0 H _ (conj HS H2)) => Hc'None Hc'Some.
    destruct s' as [s'|] => //.
    move: {Hc'Some}(Hc'Some _ H3) => HP'.
    by move: (IHexec l' _ Hd IH _ H HP' (refl_equal _) (refl_equal _) Hs'').
  + move=> s'.
    move HC : (while t c) => C.
    move Hsigma : (Some s) => sigma.
    move Hsigma' : (Some s') => sigma'.
    move=> H2; move: P t c H IH s s' H0 H1 HC Hsigma Hsigma'; elim: H2 => //.
    * (* case exec_while true *) move=> n0 s sigma'' sigma''' t c Ht H0 _ H2 IHexec P t' c1 HC IH s0 s' H Hsigma'.
      case => X Y; subst c1 t'.
      case=> X; subst s0 => Hsigma'''.
      (* we know s,m,h |= P /\ eval_b true, by the inductive hypothesis IH we have sigma'' |= P *)
      destruct sigma'' as [s''|].
      - have HP'' : P s''.
          case: (IH n0 H s (conj Hsigma' Ht)) => _; apply. done.
        (* since sigma'' --while t c---> sigma' and {P}while t c{P /\ eval_b false }, then we have sigma' |= P /\ ~b *)
        by move: (IHexec _ _ _ HC IH _ s'  H HP'' (refl_equal (while t c)) (refl_equal (Some s'')) Hsigma''').
      - inversion H2 => //.
        by rewrite -H5 in Hsigma'''.
    * (* case exec_while false *) move=> n0 s t c Ht P t' c' _ _ s1 s2 H HP [] X Y; subst. case=> X; subst; case=> X; by subst.
- (* ifte *) move=> l' P Q t c d H1 IH1 H2 IH2; split.
  + move=> H4; inversion H4; subst.
    * by case: (IH1 n H _ (conj H0 H10)).
    * by case: (IH2 n H _ (conj H0 H10)).
  + move=> s' H4; inversion H4; subst.
    * case: (IH1 n H _  (conj H0 H10)) => _; by apply.
    * case: (IH2 n H _  (conj H0 H10)) => _; by apply.
- (* case call *) move=> l' P' Q' i lnew [] i_lnew IH n.
  rewrite /hoare_sem_ctxt_n.
  suff K : (forall t : ftriple,
    Ensembles.In _ l' t -> l |= n {{ (fpre t) }} call (fcallee t) {{ (fpost t) }}) ->
   forall P' Q' (i : string),
   Ensembles.In _ lnew (mkFTriple (P') i (Q')) -> l |= n {{ P' }} call i {{ Q' }}.
     move=> H.
     by apply K => //.
  move: n i_lnew IH; elim.
  + move=> H i_lnew IH i' PQi'.
    rewrite /hoare_semantics.
    move=> s P'sh; split.
      move=> abs.
      by inversion abs.
    move=> s' Psh'.
    by inversion Psh'.
  + move=> n IHn i_lnew IH H P'0 Q'0 i' PQi'.
    have H' : forall t : ftriple,
      Ensembles.In _ l' t ->
      l |= n {{ (fpre t)}} call (fcallee t) {{ (fpost t) }}.
      move=> t tl''.
      apply hoare_semantics_Sn.
      by apply H.
    have H'' : forall t : ftriple,
      Ensembles.In _ lnew t -> l |= n {{ (fpre t) }} call (fcallee t) {{ (fpost t)}}.
      move=> t Ht.
      destruct t.
      by apply (IHn i_lnew) => //.
    have H''' : forall t, Ensembles.In _ lnew t ->
       Procs.get (fcallee t) l <> None /\
       (forall pro, Procs.get (fcallee t) l = Some pro ->
        l |= n {{ (fpre t) }} pro {{ (fpost t) }}).
      move=> t Ht.
      move: {IH}(IH _ Ht) => [] IH1 IH2.
      split=> // pro Hpro.
      move: {IH2}(IH2 _ Hpro).
      move/(_ n) => X.
      apply X => t' Ht'.
      inversion Ht'.
        subst t'.
        move=> Z0.
        by apply H'.
      subst t'.
      move=> Z0.
      by apply H'' => //.
    move: (H''' _ PQi') => /= [].
    move Hfind : (Procs.get i' l) => [pro|] //.
    move=> _.
    move/(_ _ Logic.eq_refl) => K.
    move=> s1 P1.
    red in K.
    have P1_ : P'0 s1.
      done.
    move: (P1) => P1_save.
    apply K in P1_.
    case: P1_ => {}P1 P1'.
    split.
      contradict P1.
      inversion P1 => //; subst.
        rewrite Hfind in H3; case: H3 => ?; by subst pro0.
      by rewrite Hfind in H3.
    move=> s' Psh'.
    inversion Psh' => //; subst.
    rewrite Hfind in H4; case: H4 => ?; subst pro0.
    apply P1' in H5.
    done.
- (* case call assumption *) move=> l' P' Q' str HIn n.
  move/(_ _ HIn).
  move=> H s Ps.
  split.
    by case: (H s).
  move=> s'.
  by case: (H s Ps) => _ /(_ s').
- (* case exfalso *)
  move=> l' P c Q H H' n.
  apply H.
Qed.

Lemma hoare_sound E P Q l c : l \^ E |-{{ P }} c {{ Q }} -> l \^ E |={{ P }} c {{ Q }}.
Proof.
intros.
apply hoare_sem_ctxt_n_sem_ctxt => n.
move/hoare_sound_n : H.
by move/(_ n).
Qed.

Lemma soundness_spec : forall P Q l c, l \^ Empty_set _ |-{{ P }} c {{ Q }} -> l |={{ P }} c {{ Q }}.
Proof. move=> P Q l c /hoare_sound; by apply. Qed.

(** from a triple and a termination proof, we can deduce that the program does not fail *)
Lemma termi : forall l c P Q, l \^ Empty_set _ |-{{ P }} c {{ Q }} ->
  (forall s, P s -> exists s', l |~ Some s >- c ---> s') ->
  forall s, P s ->
    exists s', l |~ Some s >- c ---> Some s'.
Proof.
move=> l c P Q Hhoare Hterm s HP.
case: {Hterm}(Hterm _ HP) => s' Hc.
case/exec_iexec : Hc => n Hc.
move: {Hhoare}(soundness_spec _ _ _ _ Hhoare).
rewrite /hoare_semantics.
move/(_ _ HP) => [Hno_err Hsome].
destruct s' as [s'|] => //.
  exists s'.
  by apply iexec_exec with n.
by apply iexec_exec in Hc.
Qed.

End WhileHoare.

(**********************)

Module Type WhileSemaxComplete0 (ST : StateBipl) (B : Bipl ST) (Semop: WhileSemop0 ST B) (Hoare: WhileSemax0 ST B Semop).

Include (WhileHoare ST B Semop Hoare).

Local Open Scope lang_scope.
Local Open Scope whilesemop_scope.
Local Open Scope whilehoare_scope.

Parameter completeness0 : forall l (c0 : cmd0), exists f, forall P, hoare0 (f P) c0 P /\
  forall s', ~ l |~ Some s' >- cmd_cmd0 c0 ---> None -> f (fun s => l |~ Some s' >- cmd_cmd0 c0 ---> Some s) s'.

(*Parameter completeness0 : forall l sh (c0 : cmd0),
  hoare0
     (fun s => s = sh /\ ~ l |~ Some s >- cmd_cmd0 c0 ---> None) c0
     (fun s => l |~ Some sh >- cmd_cmd0 c0 ---> Some s).*)

(*Parameter wp_semantics_sound0 : forall (c : cmd0) Q,
  {{ wp_semantics (cmd_cmd0 c) Q }} (cmd_cmd0 c) {{ Q }}.
Parameter wp0 : cmd0 -> assert -> assert.
Parameter wp0_no_err : forall s h c P,  wp0 c P s h -> ~ (Some (s,h) -- c ----> None).*)

End WhileSemaxComplete0.

(***********************)

Module WhileSemaxComplete (ST : StateBipl) (B : Bipl ST) (Semop: WhileSemop0 ST B) (Hoare: WhileSemax0 ST B Semop) (Complete: WhileSemaxComplete0 ST B Semop Hoare).

Include Complete.

Local Open Scope lang_scope.
Local Open Scope whilesemop_scope.
Local Open Scope whilehoare_scope.

(*Lemma wp_semantics_sound : forall c Q, {{ wp_semantics c Q }} c {{ Q }}.
Proof.
elim.
- move=> c Q; by apply wp_semantics_sound0.
- (* seq *) move=> c1 IHc1 c2 IHc2 Q.
  apply hoare_stren with (wp_semantics c1 (wp_semantics c2 Q)); last first.
    by eapply hoare_seq; [apply IHc1 | apply IHc2].
  move=> s h [H0 H1]; split.
  + by apply exec_seq1_not_None with c2.
  + move=> s' h' H; split.
    * by apply exec_seq2_not_None with s h c1.
    * move=> s'0 h'0 H2.
      apply H1.
      by apply exec_seq with (Some (s', h')).
- (* ifte *) move=> b c1 IHc1 c2 IHc2 Q; apply hoare_ifte.
  + eapply hoare_stren; last by apply IHc1.
    move=> s h [H0 H1].
    rewrite /wp_semantics in H0 *.
    case: H0 => H H2.
    split.
    by apply exec_ifte1_not_None with c2 b.
    move=> s' h' H0; apply H2.
    by apply exec_ifte_true.
  + eapply hoare_stren; last by apply IHc2.
    rewrite /entails => s h [[H H2] H1]; rewrite /wp_semantics; split.
    by apply exec_ifte2_not_None with c1 b.
    move=> s' h' H0; by apply H2, exec_ifte_false.
- (* while_bne *) move=> b c IHc Q; apply hoare_weak with (fun s h' => (wp_semantics (while b c) Q) s h' /\ ~~ eval_b b (s, h')).
  + move=> s h [[H H2] H1]; by apply H2, exec_while_false.
  + apply hoare_while.
    apply hoare_stren with (wp_semantics c (wp_semantics (while b c) Q)).
    * move=> s h [[H H2] H1]; red; split.
      by apply exec_while1_not_None with b.
      move=> s' h' H0; red; split.
      by apply exec_while2_not_None with s h.
      move=> s'0 h'0 H3; by apply H2, exec_while_true with (Some (s', h')).
    * by apply IHc.
Qed.*)

Definition MGT c l l' := forall Z,
l \^ l' |-{{ fun s => s = Z /\ ~ l |~ Some s >- c ---> None }}
          c
          {{ fun s => l |~ Some Z >- c ---> Some s }}.

Definition unroll l b c := clos_refl_trans _ (fun s s' => eval_b b s /\ l |~ Some s >- c ---> Some s').

Lemma unroll_while_stop : forall l b c s' s,
  unroll l b c s s' -> ~~ eval_b b s' ->
  l |~ Some s >- While b {{ c }} ---> Some s'.
Proof.
move=> l b c s'.
apply (clos_refl_trans_ind_right _ _
  (fun z => ~~ eval_b b s' -> l |~ Some z >- While b {{ c }} ---> Some s')).
  intros.
  by apply exec_while_false.
move=> x y H H0 H1 H2.
case: H => H' H''.
move: {H0}(H0 H2) => H0.
move/(exec_seq _ _ _ _ _ _ H'') in H0.
by move: (while_seq' _ _ H' _ _ _ H0).
Qed.

Lemma unroll_while_continue l b c s' : forall s,
  (unroll l b c) s s' ->
  ~ l |~ Some s >- While b {{ c }} ---> None ->
  eval_b b s' -> ~ l |~ Some s' >- c ---> None.
Proof.
apply (clos_refl_trans_ind_right _ _
  (fun z => ~ l |~ Some z >- While b {{ c }} ---> None ->
   eval_b b s' -> ~ l |~ Some s' >- c ---> None) s').
  intros.
  by eapply exec_while1_not_None; eauto.
move=> x y H H0 H1 H2 H3.
case: H => H' H''.
apply H0 => // => abs.
have b_y : eval_b b y.
  apply clos_rt_rt1n in H1.
  inversion H1.
    by subst s'.
  tauto.
move/(exec_seq _ _ _ _ _ _ H'') in abs.
by move: (while_seq' _ _ H' _ _ _ abs).
Qed.

(* TODO: move *)
Lemma not_In_find_None {A : eqType} {B} (f : B -> A): forall (l : list B) a,
  ~ List.In a (map f l) <-> List.find (fun x => f x == a) l = None.
Proof.
elim.
  move=> a /=; tauto.
move=> h t IH a /=; split => [H|].
  case: ifP.
  - move/eqP => ?; tauto.
  - move/negbT=> H'; apply IH; tauto.
case: ifP => // /negbT/eqP H1 H2.
move: (proj2 (IH _) H2) => H3.
tauto.
Qed.

Lemma MGTs_imply_MGT : forall l l',
  (forall t, t \in Procs.dom l -> MGT (call t) l l') ->
  forall c, MGT c l l'.
Proof.
move=> l l' ll'; elim.
- move=> c0 sh.
  case: (completeness0 l c0) => f Hf.
  apply hoare_conseq_new => s [] <- H.
  exists (f (fun s0 => l |~ Some s >- cmd_cmd0 c0 ---> Some s0)).
  exists (fun s0 => l |~ Some s >- cmd_cmd0 c0 ---> Some s0).
  split; first by apply hoare_hoare0, (proj1 (Hf _)).
  split; last by [].
  by apply (proj2 (Hf (fun s0 => l |~ Some s >- cmd_cmd0 c0 ---> Some s0))).
- move=> c1 IH1 c2 IH2 s.
  have {}IH1 : l \^ l'
      |-{{ fun s0 => s0 = s /\ ~ l |~ Some s0 >- c1 ; c2 ---> None }}
        c1
        {{ fun s0 => l |~ Some s >- c1 ---> Some s0 /\
                        ~ l |~ Some s0 >- c2 ---> None }}.
    move: {IH1}(IH1 s) => IH1.
    apply hoare_conseq_new.
    move=> s_ /= [] ? Hc1c2; subst s_.
    eexists; eexists; split; first by apply IH1.
    split.
      split; first by reflexivity.
      by eapply exec_seq1_not_None; eauto.
    move=> s0 /= ?; split; first by assumption.
    by eapply exec_seq2_not_None; eauto.
  have {}IH2 : forall Z, l \^ l'
        |-{{ fun s0 => l |~ Some Z >- c1 ---> Some s0 /\ ~ l |~ Some s0 >- c2 ---> None}}
          c2
          {{fun s0 => l |~ Some Z >- c1; c2 ---> Some s0 }}.
    move=> Z.
    apply hoare_conseq_new.
    move=> s' /= [] H1 H2.
    eexists; eexists; split; first by apply IH2.
    split.
      split; [reflexivity | assumption].
    move=> s'' /= ?.
    by eapply exec_seq; eauto.
  eapply hoare_conseq.
  by apply ent_id.
  by apply ent_id.
  eapply hoare_seq; by [apply IH1 | apply IH2].
- move=> b c IHc d IHd s.
  apply hoare_ifte.
    rewrite /MGT in IHc.
    eapply hoare_conseq_new.
    move=> s' [] [] ?; subst s'.
    move=> Hc Hb.
    eexists; eexists; split; first by apply (IHc s).
    split.
      split; first by reflexivity.
      by eapply exec_ifte1_not_None; eauto.
    move=> s' /= Hc'.
    by apply exec_ifte_true.
  rewrite /MGT in IHc.
  eapply hoare_conseq_new.
  move=> s' [] [] ?; subst s'.
  move=> Hd Hb.
  eexists; eexists; split; first by apply (IHd s).
  split.
    split; first by reflexivity.
    by eapply exec_ifte2_not_None; eauto.
  move=> s' /= Hc'.
  by apply exec_ifte_false.
- move=> b c IH.
  pose P' := fun Z => fun s' => unroll l b c Z s' /\
    (forall s1, unroll l b c Z s1 -> eval_b b s1 -> ~ l |~ Some s1 >- c ---> None).
  have H1 : forall Z, l \^ l' |-{{ fun s => P' Z s /\ eval_b b s }} c {{ P' Z }}.
    move=> Z.
    eapply hoare_conseq_aux.
      move=> s. by apply (IH s).
    move=> s [] HP' Hb.
    exists s.
    split.
      split; first by reflexivity.
      case: HP' => HP'1 HP'2.
      by apply HP'2.
    move=> s' /= Hc; rewrite /P'.
    split.
      case: HP' => HP'1 HP'2.
      eapply rt_trans.
      by apply HP'1.
      by apply rt_step.
    move=> s1 Zs1 bs1.
    case: HP' => HP'1.
    by apply.
  suff Hpost : forall Z, l \^ l' |-{{ P' Z }} While b {{ c }}
                                   {{ fun s => P' Z s /\ ~~ eval_b b s}}.
    move=> Z.
    move: {Hpost}(Hpost Z) => Hpost.
    eapply hoare_conseq_aux.
      move=> s; by apply Hpost.
    move=> s [] ?; subst Z.
    move=> H.
    exists s.
    split.
      split; first by apply rt_refl.
      move=> s1 unroll_s1.
      by apply unroll_while_continue with s.
    move=> s1 /= [] HP' b_s1h1.
    case: HP' => HP'1 HP'2.
    by apply unroll_while_stop.
  move=> Z.
  by apply (hoare_while l l' (P' Z)).
- move=> str.
  case/boolP : (str \in Procs.dom l) => str_l.
(*  case: (List.in_dec string_dec str (map name l)) => str_l.*)
    apply ll' in str_l; by auto.
  move=> Z.
  have : (forall s, (fun s=>
        s = Z /\ ~ l |~ Some s >- call str ---> None) s <-> False).
    split; last by [].
    case => ?; subst Z.
    apply.
    apply exec_call_err.
    by apply Procs.notin_get_None.
  move=> abs.
  apply hoare_conseq_indep with False => //.
  intros.
  move: (abs s); tauto.
Qed.

(* TODO: move *)
Lemma Union0r A (s : Ensemble A) : Union _ s (Empty_set _) = s.
Proof.
apply Extensionality_Ensembles; split; red => a; rewrite /In.
  by case.
move=> *; by constructor.
Qed.

Lemma UnionC A (s1 s2 : Ensemble A) : Union _ s1 s2 = Union _ s2 s1.
Proof.
apply Extensionality_Ensembles; split; red => a; rewrite /In.
  case => a' Ha'; by [apply Union_intror | apply Union_introl].
case => a' Ha'; by [apply Union_intror | apply Union_introl].
Qed.

Lemma Union0l A (s : Ensemble A) : Union _ (Empty_set _) s = s.
Proof.
rewrite UnionC.
apply Union0r.
Qed.

(*Definition proj_state : state -> (gstore * heap) := fun s => (gstate s, hstate s).
Definition to_state : (gstore * heap) -> string -> state := fun s str =>
  mkState (fst s) (bcall str) (snd s).
Definition to_state2 : (gstore * heap) -> store -> state := fun s ls =>
  mkState (fst s) ls (snd s).*)

(* Extensionality of predicates can be safely added to Coq (see Coq FAQ) *)
Axiom prop_ext : prop_extensionality.

Lemma MGTs : forall l str, str \in Procs.dom l ->
   forall Z : state,
     l \^ Empty_set _
     |-{{ fun s => s = Z /\ ~ l |~ Some s >- call str ---> None }}
       call str
       {{ fun s => l |~ Some Z >- call str ---> Some s }}.
Proof.
move=> l.
pose Specs := fun t => exists str (Z : state),
  str \in Procs.dom l /\
  mkFTriple
  (fun s => s = Z /\ ~ l |~ Some Z >- call str ---> None)
  str
  (fun s => l |~ Some Z >- call str ---> Some s) = t.
have H : forall str, str \in Procs.dom l -> forall Z,
     Procs.get str l <> None /\
     (forall pro, Procs.get str l = Some pro ->
      l \^ Specs |-{{ fun s => s = Z /\ ~ l |~ Some s >- pro ---> None }}
      pro
      {{ fun s => l |~ Some Z >- pro ---> Some s }}).
  have H : forall str, str \in Procs.dom l -> forall Z,
       Procs.get str l <> None /\
       (forall pro, Procs.get str l = Some pro ->
        l \^ Specs |-{{ fun s => s = Z /\ ~ l |~ Some s >- call str ---> None }}
        call str
    {{ fun s => l |~ Some Z >- call str ---> Some s }}).
    intros.
    move Hfind : (Procs.get str l) => [pro|]; last first.
      apply Procs.get_None_notin in Hfind; by rewrite H in Hfind.
    split; first by [].
    move=> pro0 [] ?; subst pro0.
    apply hoare_conseq_new.
    move=> s [] sZ Hstr.
    exists ((fun s => s = Z /\ ~ l |~ Some Z >- call str ---> None)).
    exists ((fun s => l |~ Some Z >- call str ---> Some s)).
    split.
      apply hoare_call2.
      by exists str, Z.
    split.
      by subst s.
    rewrite /entails => s'.
    done.
  have {H}Htmp : (forall t : string,
     t \in Procs.dom l -> MGT (call t) l Specs).
    intros.
    move=> Z'.
    case: (H t H0 Z').
    move Hfind : (Procs.get t l) => [pro|]; last first.
      apply Procs.get_None_notin in Hfind; by rewrite H0 in Hfind.
    move=> _ /(_ pro Logic.eq_refl).
    exact.
  move: (MGTs_imply_MGT l Specs Htmp) => MGTs_MGT str Hstr Z {Htmp}.
  move Hfind : (Procs.get str l) => [pro|]; last first.
      apply Procs.get_None_notin in Hfind; by rewrite Hstr in Hfind.
  split; first by [].
  move=> pro0 [] ?; subst pro0.
  move: (MGTs_MGT ((*body*) pro) Z) => {}MGTs_MGT.
  apply hoare_conseq_new => s [] ?; subst Z.
  move=> Hno_err.
  eexists; eexists; split; first by apply MGTs_MGT.
  split.
    split; first by reflexivity.
    contradict Hno_err.
    done.
  move=> s' /=.
  done.
move=> str str_l Z.
have [pro Hpro] : exists pro, Procs.get str l = Some pro.
  case H1 : (Procs.get str l) => [a|].
    by exists a.
  apply Procs.get_None_notin in H1; by rewrite str_l in H1.
apply hoare_conseq_new => s [] sZ Hs.
exists ((fun s => s = Z /\ ~ l |~ Some s >- pro ---> None)).
exists ((fun s => l |~ Some Z >- pro ---> Some s)).
split; last first.
  split.
    split.
      done.
    contradict Hs.
    by apply exec_call_None with pro.
  move=> s0 Hs0.
  by apply exec_call_Some with pro.
apply hoare_call with Specs.
  exists str, Z.
  split => //.
  set a := fun s => _.
  set a' := (fun s => _ in X in _ = X).
  have <- : a = a'.
    apply functional_extensionality => s_.
    rewrite /a /a'.
    apply prop_ext; split.
    case=> H1 H2; split=> //.
    contradict H2.
    apply exec_call_None with pro => //.
    by subst s_.
    case=> -> {s_} /= H1; split => //.
    contradict H1.
    inversion H1; subst.
    rewrite Hpro in H3; case: H3 => ?; by subst pro0.
    by rewrite Hpro in H3.
  congr mkFTriple.
  apply functional_extensionality => s_.
  apply prop_ext; split.
  move=> H1.
  inversion H1; subst.
  simpl in *.
  rewrite Hpro in H4; case: H4 => ?; subst pro0.
  done.
  move=> Hls.
  eapply exec_call_Some.
  by apply Hpro.
  by apply Hls.
move=> t Ht.
move Hfind : (Procs.get (fcallee t) l) => [pro_|]; last first.
  case: Ht => p [] Z' [] abs Ht; subst t.
  rewrite /= in Hfind.
  apply Procs.get_None_notin in Hfind; by rewrite abs in Hfind.
split; first by [].
move=> pro0 [] ?; subst pro0.
rewrite Union0l.
case: Ht => p [] Z' [] abs Ht. subst t.
rewrite /= in Hfind.
move: (H _ abs Z').
case => _.
move/(_ _ Hfind) => {H} /= H.
apply hoare_conseq_new => s_ [] H1 H2.
exists (fun s0 : state =>
           s0 = Z' /\
           ~ l |~ Some s0 >- pro_ ---> None).
exists (fun s0 : state => l
        |~ Some Z' >- pro_ --->
        Some s0).
split.
  by apply H.
split.
  split.
    done.
  contradict H2.
  apply exec_call_None with pro_ => //.
  move: H1.
  move => <-.
  done.
rewrite /entails.
move=> s0 Hs0.
  eapply exec_call_Some.
  by apply Hfind.
  by apply Hs0.
Qed.

Lemma MGT_hoare_complete : forall c l l', MGT c l l' ->
  forall P Q, l |={{ P }} c {{ Q }} -> l \^ l' |-{{ P }} c {{ Q }}.
Proof.
move=> c l l' HMGT P Q H.
apply hoare_conseq_aux with
  (P' := fun s' s => s = s' /\ ~ l |~ Some s >- c ---> None)
  (Q' := fun s' s => l |~ Some s' >- c ---> Some s).
  move=> s; by apply HMGT.
move=> s Ps.
move: {HMGT}(HMGT s) => HMGT.
rewrite /hoare_semantics in H.
case/H : Ps => H1 H2.
by exists s.
Qed.

Lemma hoare_complete_spec : forall P l c Q,
  l |={{ P }} c {{ Q }} -> l \^ Empty_set _ |-{{ P }} c {{ Q }}.
Proof.
move=> P l c Q H.
apply MGT_hoare_complete => //.
apply MGTs_imply_MGT => str Hstr Z.
by apply MGTs.
Qed.

Lemma hoare_weaken : forall l l' P c Q,
  l \^ l' |-{{ P }} c {{ Q }} ->
  forall l'', Included _ l' l'' ->
  l \^ l'' |-{{ P }} c {{ Q }}.
Proof.
move=> l l' P c Q IH.
elim IH using hoare_ind2 => // {l' P c Q IH}.
- move=> l' P Q c H l'' l'l''.
  by apply hoare_hoare0.
- move=> l' P Q R c1 c2 H1 IH1 H2 IH2 l'' l'l''.
  apply hoare_seq with Q => //; by auto.
- move=> l' c P Q IH l'' l'l''.
  apply hoare_conseq_new => s Ps.
  move/IH : Ps => [] P' [] Q' [] H1 [] H2 H3.
  exists P', Q'.
  split => //; by auto.
- move=> l' P b c Hc IHc l'' l'l''.
  apply hoare_while; by auto.
- move=> l' P Q b c d Hc IHc Hd IHd l'' l'l''.
  apply hoare_ifte; by auto.
- move=> l' P Q str lnew.
  move=> [] i_lnew IH l'' l'l''.
  have H : forall t : ftriple, In _ lnew t ->
       Procs.get (fcallee t) l <> None /\
       (forall pro,
        Procs.get (fcallee t) l = Some pro ->
        l \^ Union _ l'' lnew |-{{ (fpre t) }} pro {{ (fpost t) }}).
    intros.
    apply IH in H.
    case: H => H1 H2.
    split => //.
    intros.
    move/H2 in H.
    apply H.
    rewrite /Included /In => x.
    case => y Hy.
      apply Union_introl.
      by apply l'l''.
    by apply Union_intror.
  by apply hoare_call with lnew.
- move=> l' P Q str l'_str l'' l'l''.
  apply hoare_call2.
  by apply l'l''.
- move=> l' P c Q H1 H2 l'' l'l''.
  apply hoare_exfalso => //.
  move=> n H s Ps.
  move: {H1}(H1 n) => H1.
  apply H1 => // t Ht.
  apply H.
  by apply l'l''.
Qed.

Lemma hoare_complete_n : forall P l l' c Q,
  (forall n, l \^ l' |= n {{ P }} c {{ Q }}) -> l \^ l' |-{{ P }} c {{ Q }}.
Proof.
move=> P l l' c Q H.
case: (Classical_Prop.classic (l \^ Empty_set _ |-{{ P }} c {{ Q }})) => Hcase.
  by apply hoare_weaken with (Empty_set _).
apply hoare_exfalso => //.
contradict Hcase.
by apply hoare_complete_spec.
Qed.

(*  new versions *)

Lemma hoare_seq_assoc' : forall l' P l c0 c1 c2 Q,
  l \^ l' |-{{ P }} (c0 ; c1) ; c2 {{ Q }} ->  l \^ l' |-{{ P }} c0 ; c1 ; c2 {{ Q }}.
Proof.
move=> l' P l c0 c1 c2 Q.
move/hoare_sound_n => H.
apply hoare_complete_n => n Ht s Ps.
split.
  case: (H n Ht _ Ps) => {H}H1 _.
  contradict H1.
  by apply iexecA.
move=> s' Hs'.
case: (H n Ht _ Ps) => {H}_ H2.
apply H2.
by apply iexecA.
Qed.

Lemma hoare_seq_inv E P Q l c d : l \^ E |-{{ P }} c ; d {{ Q }} ->
  exists R,
    l \^ E |-{{ P }} c {{ R }} /\ l \^ E |-{{ R }} d {{ Q }}.
Proof.
move=> /hoare_sound_n H.
exists (fun s =>
  exists s0, P s0 /\ exists n,
  l |~ Some s0 >- c -^ n -> Some s /\
  (~ l |~ |_ s _| >- d -^ n -> None /\
  (forall s', l |~ Some s >- d -^ n -> Some s' -> Q s'))).
split.
  apply hoare_complete_n => n Ht s Ps.
  case: (H n Ht s Ps) => {H} H1 H2.
  split.
    contradict H1.
    apply iexec_seq with None => //.
    by apply iexec_none.
  intros.
  exists s; split => //.
  exists n; split => //.
  split.
    by move: (iexec_seq2_not_None _ _ _ _ _ _ H1 H).
  move=> s''.
  move=> H3.
  apply H2 => //.
  by apply iexec_seq with (Some s').
apply hoare_complete_n => n Ht s Ps.
case: Ps => s0 [] Ps0 [] m [] X1 [] X2 X3.
split.
  admit.
move=> s' Hs'.
apply X3.
Abort.

Lemma hoare_ifte_inv : forall l' P Q b l c d, l \^ l' |-{{ P }} ifte b c d {{ Q }} ->
  l \^ l' |-{{ fun s => P s /\ eval_b b s }} c {{ Q }} /\
  (l \^ l' |-{{ fun s => P s /\ ~~ eval_b b s }} d {{ Q }}).
Proof.
move=> l' P Q b l; move: b.
move=> b c d.
move HC : (If _ Then _ Else _) => C H.
move: H b c d HC.
elim => //.
- (* case: hoare_conseq_new *) move=> l'0 c {}P {}Q IH b c0 d Hc.
  subst c.
  rename c0 into c.
  split; apply hoare_complete_n => n Hn s [Ps bs]; split => [abs | s'].
  - case: {IH}(IH _ Ps) => P' [] Q' [].
    move/hoare_sound_n => /(_ _ Hn) HC [] P's Q'Q.
    case: {HC}(HC _ P's) => abs' _; apply abs'.
    by apply iexec_ifte_true.
  - case: {IH}(IH _ Ps) => P' [] Q' [].
    move/hoare_sound_n => /(_ _ Hn) HC [] P's Q'Q Hc.
    case: {HC}(HC _ P's) => H1 H2; apply Q'Q, H2.
    by apply iexec_ifte_true.
  - case: {IH}(IH _ Ps) => P' [] Q' [].
    move/hoare_sound_n => /(_ _ Hn) HC [] P's Q'Q.
    case: {HC}(HC _ P's) => abs' _; apply abs'.
    by apply iexec_ifte_false.
  - case: {IH}(IH _ Ps) => P' [] Q' [].
    move/hoare_sound_n => /(_ _ Hn) HC [] P's Q'Q Hc.
    case: {HC}(HC _ P's) => H1 H2; apply Q'Q, H2.
    by apply iexec_ifte_false.
- (* case: hoare_ifte *) move=> {l'}l'0 {}P {}Q b c d Hc _ Hd _ b' c' d' [] -> -> -> {b' c' d'}.
  by [].
- (* case: hoare_exfalso *)
  move=> {}l' {}P c {}Q H' H b c' d Hc.
  subst c.
  rename c' into c.
  split.
    apply hoare_complete_n => n Hn s [Ps bs]; split => [abs | s'].
    - move: {H'}(H' _ Hn) => /(_ _ Ps) [] H1 H2.
      apply H1.
      by apply iexec_ifte_true.
    - move=> Hc.
      move: {H'}(H' _ Hn) => /(_ _ Ps) [] H1.
      apply .
      by apply iexec_ifte_true.
  apply hoare_complete_n => n Hn s [Ps bs]; split => [abs | s'].
  - move: {H'}(H' _ Hn) => /(_ _ Ps) [] H1 H2.
    apply H1.
    by apply iexec_ifte_false.
  - move=> Hc.
    move: {H'}(H' _ Hn) => /(_ _ Ps) [] H1.
    apply .
    by apply iexec_ifte_false.
Qed.

Local Open Scope statebipl_scope.

Lemma hoare_L_or l E P Q R c :
  l \^ E |-{{ P }} c {{ R }} -> l \^ E |-{{ Q }} c {{ R }} -> l \^ E |-{{ P \\// Q }} c {{ R }}.
Proof.
move=> /hoare_sound_n H1 /hoare_sound_n H2.
apply hoare_complete_n => n Ht s []; by [move/(H1 n Ht s) | move/(H2 n Ht s)].
Qed.

Local Close Scope statebipl_scope.

Lemma hoare_R_ex l E (A : Type) P (Q : A -> assert) c :
  (exists y, l \^ E |-{{ P }} c {{ Q y }}) ->
  l \^ E |-{{ P }} c {{ fun s => exists x, Q x s }}.
Proof.
case=> x Hoare.
eapply hoare_conseq; last 2 first.
  by apply ent_id.
  by apply Hoare.
move => s /= HQ; by exists x.
Qed.

Lemma hoare_L_ex l E (A : Type) Q (P : A -> assert) c :
  (forall x, l \^ E |-{{ P x }} c {{ Q }}) ->
  l \^ E |-{{ fun s => exists x, P x s }} c {{ Q }}.
Proof.
move=> Hoare.
apply hoare_complete_n => n H s [a Ha].
exact (hoare_sound_n E (P a) Q l c (Hoare a) n H _ Ha).
Qed.

Definition pure (P : assert) := forall s s', P s <-> P s'.

Local Open Scope statebipl_scope.

Lemma hoare_pure_left l E : forall P P' Q Q' c, pure P ->
  ((P ===> Q) /\ l \^ E |-{{ P' }} c {{ Q' }}) ->
  l \^ E |-{{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move => P P' Q Q' c Ppure [] H1 H2.
apply hoare_complete_n => n H s [HP HP'].
case: (hoare_sound_n _ _ _ _ _ H2 n H s HP') => H21 H22.
split => //=.
move => s' Hc.
split; last first.
  by apply H22.
apply H1.
rewrite Ppure.
apply HP.
Qed.

Lemma hoare_and_left l E (P P' Q Q' : assert) c :
  (forall s s',
    l |~ |_ s _| >- c ---> |_ s' _| ->
    P s -> Q s') -> l \^ E |-{{ P' }} c {{ Q' }} ->
  l \^ E |-{{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move => H H1.
apply hoare_complete_n => n H2 s [] HP HP'.
move: {H1}(hoare_sound_n E _ _ _ _ H1 n H2 _ HP') => [] H21 H22.
split => //=.
move => s' Hc.
split; last first.
  by apply H22.
apply (H s) => //.
by apply iexec_exec with n.
Qed.

(*Lemma hoare_Or_intro_L l P Q R c :
  l \^ Empty_set _ |-{{ P }} c {{ R }} ->
  l \^ Empty_set _ |-{{ Q }} c {{ R }} ->
  l \^ Empty_set _ |-{{ P \\// Q }} c {{ R }}.
Proof.
  move=> /soundness_spec H1 /soundness_spec H2.
  xxx
apply hoare_complete_spec => s h []; by [move/H1 | move/H2].
Qed.

Lemma intro_exists_postcond l l' : forall (A : Type) P (Q : A -> assert) c,
  (exists y, l \^ l' |-{{ P }} c {{ Q y }}) ->
  l \^ l' |-{{ P }} c {{ fun s h => exists x, Q x s h }}.
Proof.
move => A P Q c [] y Hoare.
eapply hoare_conseq; last first.
  apply Hoare.
  by apply ent_id.
move => s h //= HQ; exists y; done.
Qed.

Lemma intro_exists_precond l : forall (A : Type) Q (P : A -> assert) c,
  (forall x, l \^ Empty_set _ |-{{ P x }} c {{ Q }}) ->
  l \^ Empty_set _ |-{{ fun s h => exists x, P x s h }} c {{ Q }}.
Proof.
move => A P Q c Hoare.
apply hoare_complete_spec => s h [] x Hx.
by apply (soundness_spec _ _ _ _ (Hoare x) s h Hx).
Qed.

(*Local Open Scope statebipl_scope.*)

Lemma intro_and_prepostcond l : forall P P' Q Q' c,
    (l \^ Empty_set _ |-{{ P }} c {{ Q }} /\ (l \^ Empty_set _ |-{{ P' }} c {{ Q' }})) ->
    l \^ Empty_set _ |-{{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move => P P' Q Q' c [] H1 H2.
apply hoare_complete_spec => s h [] HP HP'.
move: {H1}(soundness_spec _ _ _ _ H1 s h HP) => [] H11 H12.
move: {H2}(soundness_spec _ _ _ _ H2 s h HP') => [] H21 H22.
split => //=.
move => s' h' Hc.
split => //=.
by apply H12.
by apply H22.
Qed.

Definition pure (P : assert) := forall s h s' h', P s h <-> P s' h'.

(*Lemma hoare_pure_left : forall P P' Q Q' c, pure P ->
  ((P ===> Q) /\ {{ P' }} c {{ Q' }}) ->
  {{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move => P P' Q Q' c Ppure [] H1 H2.
apply hoare_complete => s h [] HP HP'.
move: {H2}(soundness _ _ _ H2 s h HP') => [] H21 H22.
split => //=.
move => s' h' Hc.
split; last first.
by apply H22 => //=.
apply H1.
rewrite Ppure.
apply HP.
Qed.*)

(*Lemma hoare_and_left : forall (P P' Q Q' : assert) c,
  (forall s h s' h',
    Some (s, h) -- c ---> Some (s', h') ->
    P s h -> Q s' h') -> {{ P' }} c {{ Q' }} ->
  {{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move => P P' Q Q' c H H1.
apply hoare_complete => s h [] HP HP'.
move: {H1}(soundness _ _ _ H1 s h HP') => [] H21 H22.
split => //=.
move => s' h' Hc.
split; last first.
by apply H22 => //=.
apply (H s h) => //=.
Qed.*)

(**)

(*Lemma hoare_total_sound' : (forall (P Q : assert) c, hoare0 P c Q ->
  hoare_semantics_total P (cmd_cmd0 c) Q) ->
forall P Q c, {{{ P }}} c {{{ Q }}} -> hoare_semantics_total P c Q.
Proof.
move=> H0 P Q c; elim; clear P Q c.
- (* cmd0 *) move=> P Q c H.
  by apply H0.
- (* seq *) move=> P Q R c d H1 IHhoare1 H2 IHhoare2 s h HP.
  case: (IHhoare1 _ _ HP) => [s' [h' [K2 K3]]].
  case: (IHhoare2 _ _ K3) => [s'' [h'' [K5 K6]]].
  exists s'', h''; split => //.
  by eapply exec_seq; eauto.
- (* conseq *) move=> P P' Q Q' c H1 H2 H3 IHhoare s h HP.
  move: (H2 _ _ HP) => H'.
  case: (IHhoare _ _ H') => [s' [h' K2]].
  exists s', h'; split; first by tauto.
  apply H1; tauto.
- (* while *) move=> P t c A R Rwf V a.
  elim a using (well_founded_induction Rwf).
  move=> {a} a Hrec H IHhoare s h [HP Ha].
  case/orP : (orbN (eval_b t (s, h))) => Htest.
  - case: (IHhoare a _ _ (conj HP (conj Htest Ha))) => s' [h' [Hexec [HP' HR]]].
    move: {Hrec}(Hrec _ HR H IHhoare) => Hrec.
    case: {Hrec}(Hrec _ _ (conj HP' (refl_equal _))) => s'' [h'' [H1 [H2 H3]]].
    exists s'', h''; split => //.
    apply while_seq' => //.
    by apply exec_seq with (Some (s',h')).
  - exists s, h; split; last by done.
    by apply exec_while_false.
- (* ifte *) move=> P Q t c d H1 IHhoare1 H2 IHhoare2 s h HP.
  case/orP : (orbN (eval_b t (s, h))) => Htest.
  - case: (IHhoare1 s h) => // s' [h' K1].
    exists s', h'; split; last by tauto.
    constructor; tauto.
  - case: (IHhoare2 s h); first by done.
    move=> s' [h' [K1 K2]].
    exists s', h'; split; last by assumption.
    by apply exec_ifte_false.
Qed.*)
*)

Lemma hoare_L_F l E c Q : l \^ E |-{{ FF }} c {{ Q }}.
Proof. by apply hoare_complete_n. Qed.

(*Lemma contra_precond Q P c : P ===> FF -> {{ P }} c {{ Q }}.
Proof. move=> H; eapply hoare_stren; by [apply H | apply FFHoare]. Qed.*)

End WhileSemaxComplete.

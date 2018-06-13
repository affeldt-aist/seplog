(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool.
Require Import Coq.Classes.RelationClasses.
Require Import ClassicalChoice.

(****************************************************************************)
(* An extension of the modules in while.v with Separation-logic connectives *)
(* 1) first define a module L of type LangSemop                             *)
(* 2) then define a module of type L' of type LangHoare L                   *)
(*    starting with an Include WhileSemax(L).                               *)
(* 3) define a module of type L'' of type LangHoareComplete L L'            *)
(*    starting with an Include (WhileHoare Semop Hoare).                    *)
(* 4) finally instantiate a module WhileHoareComplete L L' L''              *)
(****************************************************************************)

Module Type StateBipl.

(** A state is a pair of a store and a mutable memory. *)

Parameter store : Type.
Parameter heap : Type.
Definition state : Type := (store * heap)%type.

(** Structured commands (if-then-else's and while-loops) are parameterized by a type
   for boolean expressions. *)

Parameter expr_b : Type.
Parameter neg : expr_b -> expr_b.
Parameter eval_b : expr_b -> state -> bool.
Parameter eval_b_neg : forall t s, eval_b (neg t) s = ~~ eval_b t s.

Definition assert : Type := store -> heap -> Prop.

End StateBipl.

Module Type StateBiplProp (ST : StateBipl).

Include ST.

Definition TT : assert := fun _ _ => True.
Definition FF : assert := fun _ _ => False.
Definition And (P Q : assert) : assert := fun s h => P s h /\ Q s h.
Notation "P //\\ Q" := (And P Q) (at level 70, right associativity) : statebipl_scope.
Definition Or (P Q : assert) : assert := fun s h => P s h \/ Q s h.
Notation "P \\// Q" := (Or P Q) (at level 80, right associativity) : statebipl_scope.
Definition Not (P : assert) : assert := fun s h => ~ P s h.
Notation "~~~ P" := (Not P) (at level 60, no associativity) : statebipl_scope.
Definition entails (P Q : assert) := forall s h, P s h -> Q s h.
Notation "P ===> Q" := (entails P Q) (at level 89, no associativity) : statebipl_scope.
Definition equiv (P Q : assert) := forall s h, P s h <-> Q s h.
Notation "P <==> Q" := (equiv P Q) (at level 89, no associativity) : statebipl_scope.

Local Open Scope statebipl_scope.

Lemma equiv_refl : forall (P : assert), P <==> P.
Proof. done. Qed.

Lemma equiv_sym : forall (P Q : assert), P <==> Q -> Q <==> P.
Proof. move=> P Q HPQ s h. by case: (HPQ s h). Qed.

Lemma equiv_trans : forall (P Q R : assert), P <==> Q -> Q <==> R -> P <==> R.
Proof.
move=> P Q R HPQ HQR s h.
move: (HPQ s h) (HQR s h).
by intuition.
Qed.

Instance equiv_equivalence : Equivalence equiv.
constructor.
exact equiv_refl.
exact equiv_sym.
exact equiv_trans.
Defined.

Lemma equiv_def P Q : (P <==> Q) <-> ((P ===> Q) /\ (Q ===> P)).
Proof.
split.
- move=> H; split; move=> *; by apply H.
- case => H1 H2 s h; split; by [apply H1 | apply H2].
Qed.

Lemma equiv_imp P Q : P <==> Q -> P ===> Q.
Proof. move=> H s h HP. by apply H. Qed.

Lemma equiv_imp2 P Q : P <==> Q -> Q ===> P.
Proof. move=> H s h HP. by apply H. Qed.

Lemma ent_id P : P ===> P. Proof. by rewrite /entails. Qed.

Lemma ent_trans Q P R : P ===> Q -> Q ===> R -> P ===> R.
Proof. move=> H1 H2 s h HP. by apply H2, H1. Qed.

Lemma ent_L_F Q : FF ===> Q. Proof. by move=> ?. Qed.

Lemma ent_R_T P : P ===> TT. Proof. done. Qed.

Lemma F_is_not_T : FF <==> Not TT. Proof. move=> s h; split=> //; by apply. Qed.

Lemma and_L_1 (P Q R : assert) : P ===> R -> P //\\ Q ===> R.
Proof. move=> H s h [] HP _; by apply H. Qed.

Lemma ent_R_or_1 (P Q R : assert) : P ===> R -> P ===> R \\// Q.
Proof. move=> H s h; left; by apply H. Qed.

Lemma ent_R_or_2 (P Q R : assert) : P ===> Q -> P ===> R \\// Q.
Proof. move=> H s h; right; by apply H. Qed.

Lemma ent_L_or (P Q R : assert) : ((R ===> P) /\ (Q ===> P)) <-> R \\// Q ===> P .
Proof.
split.
  move=> [H1 H2] s h [].
  by apply H1.
  by apply H2.
move=> H; split => s h HR.
  apply H.
  by left.
apply H.
by right.
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

Lemma monotony_R1 P R : P ===> emp -> P ** R ===> R.
Proof. 
move=> H. apply ent_trans with (emp ** R). by apply monotony_R.
apply (proj1 (equiv_def _ _) (coneP R)).
Qed.

Lemma monotony_L1 P R : P ===> emp -> R ** P ===> R.
Proof. 
move=> H. apply ent_trans with (R ** emp). by apply monotony_L.
apply (proj1 (equiv_def _ _) (conPe R)).
Qed.

Lemma monotony_R2 P R : emp ===> P -> R ===> P ** R.
Proof. 
move=> H. apply ent_trans with (emp ** R); last by apply monotony_R.
apply (proj1 (equiv_def _ _) (coneP R)).
Qed.

Lemma monotony_L2 P R : emp ===> P -> R ===> R ** P.
Proof. 
move=> H. apply ent_trans with (R ** emp); last by apply monotony_L.
apply (proj1 (equiv_def _ _) (conPe R)).
Qed.

End BiplProp.

Module Type WhileSemop0 (ST : StateBipl) (B : Bipl ST).

Include (BiplProp ST B).

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

Module Type WhileSemop (ST : StateBipl) (B : Bipl ST) (L: WhileSemop0 ST B).

Include L.

Local Open Scope lang_scope.

(** Using above types, we define the commands of %\while\%#While# languages. *)

Inductive cmd : Type :=
| cmd_cmd0 : 	cmd0 -> cmd
| cmd_seq : 	cmd -> cmd -> cmd
| ifte : 	expr_b -> cmd -> cmd -> cmd
| while : 	expr_b -> cmd -> cmd.
(*Coercion cmd_cmd0 : cmd0 >-> cmd.*)
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

Reserved Notation "s -- c ---> t" (at level 74, no associativity).
Inductive exec : option state -> cmd -> option state -> Prop :=
| exec_none : forall c, None -- c ---> None
| exec_cmd0 : forall s c s', s -- c ----> s' -> s -- (cmd_cmd0 c) ---> s'
| exec_seq : forall s s' s'' c d, s -- c ---> s' -> s' -- d ---> s'' -> s -- c ; d ---> s''
| exec_ifte_true : forall s s' t c d, eval_b t s -> Some s -- c ---> s' -> 
  Some s -- ifte t c d ---> s'
| exec_ifte_false : forall s s' t c d, ~~ eval_b t s -> Some s -- d ---> s' -> 
  Some s -- ifte t c d ---> s'
| exec_while_true : forall s s' s'' t c, eval_b t s -> Some s -- c ---> s' ->
  s' -- while t c ---> s'' -> Some s -- while t c ---> s''
| exec_while_false : forall s t c,
  ~~ eval_b t s -> Some s -- while t c ---> Some s
where "s -- c ---> t" := (exec s c t) : whilesemop_scope.

Lemma from_none : forall c s, None -- c ---> s -> s = None.
Proof.
move Hs0 : None => s0.
move=> c s H; move: H Hs0; elim => //.
- destruct s1 => // c' s'.
  by move/from_none0.
- move=> s1 s' s'' _ _ _ H _ H' H''; subst.
  have {H}H'' : s' = None by apply H.
  subst; by apply H'.
Qed.

(** Inversion lemmas: *)

Lemma exec_cmd0_inv : forall s (c : cmd0) s',
  Some s -- (cmd_cmd0 c) ---> s' -> Some s -- c ----> s'.
Proof. move=> s c. by inversion 1. Qed.

Lemma exec0_not_None_to_exec_not_None : forall s h (c:cmd0),
  ~ Some (s, h) -- cmd_cmd0 c ---> None -> ~ Some (s, h) -- c ----> None.
Proof. move=> s h c H H'. by apply H, exec_cmd0. Qed.

Lemma exec_seq_inv : forall c d s s', s -- c ; d ---> s' ->
  exists s'', s -- c ---> s'' /\ s'' -- d ---> s'.
Proof.
move=> c d s s' H.
inversion H; subst.
- exists None; by split; apply exec_none.
- by exists s'0.
Qed.

Lemma exec_seq_inv_Some : forall c d s s',
  Some s -- c ; d ---> Some s' ->
  exists s'', Some s -- c ---> Some s'' /\ Some s'' -- d ---> Some s'.
Proof.
move=> c d s s' H.
inversion H as [ | | s0 s1 s2 c1 c2 Hc1 Hc2 Hs0 Htmp Hs2 | | | | ]; subst.
destruct s1 as [[s1 h1]|].
by exists (s1, h1).
by move/from_none : Hc2.
Qed.

Lemma exec_while_inv_false : forall b c s h s' h', ~~ eval_b b (s, h) ->
  Some (s, h) -- while b c ---> Some (s', h') -> s = s' /\ h = h'.
Proof. 
move=> b c s h s' h' H H'; inversion H'; subst.
by rewrite H3 in H.
by inversion H'.
Qed.

Lemma exec_while_inv_true b s h : eval_b b (s, h) ->
  forall c s' h', Some (s, h) -- while b c ---> Some (s', h') ->
  exists s'' h'', Some (s, h) -- c ---> Some (s'', h'') /\
                  Some (s'', h'') -- while b c ---> Some (s', h').
Proof.
move=> H c s' h'.
inversion 1; subst.
destruct s'0 as [[s'' h'']|].
by exists s'', h''.
by move/from_none : H7.
by rewrite H in H3.
Qed.

Lemma exec_ifte_true_inv t c1 c2 s h s' : eval_b t (s, h) ->
  Some (s, h) -- ifte t c1 c2 ---> s' -> Some (s, h) -- c1 ---> s'.
Proof. move=> Ht; inversion 1. by subst. by rewrite Ht in H5. Qed.

Lemma exec_ifte_false_inv t c1 c2 s h s' : ~~ eval_b t (s, h) ->
  Some (s, h) -- ifte t c1 c2 ---> s' -> Some (s, h) -- c2 ---> s'.
Proof. move=> Ht; inversion 1. by rewrite H5 in Ht. by subst. Qed.

Lemma exec_seq_assoc s s' c0 c1 c2 :
  s -- (c0 ; c1) ; c2 ---> s' -> s -- c0 ; c1 ; c2 ---> s'.
Proof.
case/exec_seq_inv => s'' [].
case/exec_seq_inv => s''' [H1 H2] H3.
apply exec_seq with s''' => //.
by apply exec_seq with s''.
Qed.

Lemma exec_seq_assoc' s s' c0 c1 c2 :
  s -- c0 ; c1 ; c2 ---> s' -> s -- (c0 ; c1) ; c2 ---> s'.
Proof.
case/exec_seq_inv => s'' [] H1.
case/exec_seq_inv => s''' [] H2 H3.
apply exec_seq with s''' => //.
by apply exec_seq with s''.
Qed.

Lemma while_seq s h t : eval_b t (s, h) -> forall s' c,
  Some (s, h) -- while t c ---> s' -> Some (s, h) -- c ; while t c ---> s'.
Proof.
move=> Ht sigma' c.
inversion 1 as [ | | | | | | ]; subst.
- by apply exec_seq with s'.
- by rewrite Ht in H0.
Qed.

Lemma while_seq' s h t : eval_b t (s, h) -> forall s' c,
  Some (s, h) -- c ; while t c ---> s' -> Some (s, h) -- while t c ---> s'.
Proof.
move=> Hneq s' c; inversion 1; subst.
by apply exec_while_true with s'0.
Qed.

Lemma exec_seq1_not_None s h c1 c2 :
  ~ Some (s, h) -- c1 ; c2 ---> None -> ~ Some (s, h) -- c1 ---> None.
Proof.
move=> H; contradict H; apply exec_seq with None=> //; apply exec_none.
Qed.

Lemma exec_seq2_not_None s h s' h' c1 c2 :
  ~ Some (s, h) -- c1 ; c2 ---> None -> Some (s, h) -- c1 ---> Some (s', h') ->
  ~ Some (s', h') -- c2 ---> None.
Proof.
move=> H H'. contradict H. by apply exec_seq with (Some (s', h')). 
Qed.

Lemma exec_ifte1_not_None s h c1 c2 t :
  ~ Some (s, h) -- ifte t c1 c2 ---> None -> eval_b t (s, h) ->
  ~ Some (s, h) -- c1 ---> None.
Proof. move=> H ?. contradict H. by apply exec_ifte_true. Qed.

Lemma exec_ifte2_not_None s h c1 c2 t :
  ~ Some (s, h) -- ifte t c1 c2 ---> None -> ~~ eval_b t (s, h) -> 
  ~ Some (s, h) -- c2 ---> None.
Proof. move=> H ?. contradict H. by apply exec_ifte_false. Qed.

Lemma exec_while1_not_None s h t c : 
  ~ Some (s, h) -- while t c ---> None -> eval_b t (s, h) -> 
  ~ Some (s, h) -- c ---> None.
Proof.
move=> H ?. contradict H. apply exec_while_true with None=> //. by apply exec_none.
Qed.

Lemma exec_while2_not_None s h c t s0 h0 :
  ~ Some (s, h) -- while t c ---> None -> eval_b t (s, h) ->
  Some (s, h) -- c ---> Some (s0, h0) -> ~ Some (s0, h0) -- while t c ---> None.
Proof.
move=> H ? ?. contradict H. by apply exec_while_true with (Some (s0, h0)).
Qed.

Lemma not_exec_seq_inv_Some c d s h : ~ Some (s, h) -- c ; d ---> None ->
  ~ Some (s, h) -- c  ---> None /\
  forall s', Some (s, h) -- c ---> Some s' -> ~ (Some s' -- d ---> None).
Proof.
move=> H; split.
- contradict H; apply exec_seq with None => //; by apply exec_none.
- move=> s' Hc H'; apply H; by apply exec_seq with (Some s').
Qed.

Lemma not_exec_ifte_inv_Some b c d s h :
  ~ Some (s, h) -- ifte b c d ---> None ->
  (eval_b b (s, h) -> ~ Some (s, h) -- c  ---> None) /\
  (~~ eval_b b (s, h) -> ~ Some (s, h) -- d  ---> None).
Proof.
move=> H.
case/boolP : (eval_b b (s, h)) => Hb.
- split=> [_ H'|Ht] //.
  apply H; by constructor.
- split=> X H'.
  + by move/negP : Hb.
  + apply H; by apply exec_ifte_false.
Qed.

Lemma while_preserves t c (P : store -> Prop) s h s' h' : P s ->
  Some (s, h) -- while t c ---> Some (s', h') ->
  (forall s h s' h', P s -> eval_b t (s, h) -> Some (s, h) -- c ---> Some (s', h') -> P s') ->
  P s'.
Proof.
move=> HP.
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
Qed.

Lemma while_condition_inv s h s' h' b c :
  Some (s, h) -- while b c ---> Some (s', h') -> ~~ eval_b b (s', h').
Proof.
move HS : (Some (s, h)) => S.
move HS' : (Some (s', h')) => S'.
move HC : (while b c) => C Hexec.
move: Hexec s h HS s' h' HS' b c HC; elim => //.
- move=> [s h] s' s'' t c t_s exec_c _ exec_while_t_c IH s0 h0.
  case=> ? ?; subst s0 h0.
  move=> s'0 h'0 Hs'' t0 c0.
  case=> ? ?; subst t0 c0.
  destruct s' as [[s' h']|].
  by eapply IH; eauto.
  move/from_none : exec_while_t_c => ?; by subst s''.
- move=> s t c t_s s0 h0 Hs s' h' Hs'h' t0 c0.
  case=> ? ?; subst t0 c0.
  rewrite -Hs in Hs'h'.
  case: Hs'h' => ? ?; subst s0 h0.
  by case: Hs => ->.
Qed.

End WhileSemop.

Module Type WhileSemaxSemantics (ST : StateBipl) (B : Bipl ST) (L : WhileSemop0 ST B).

Include (WhileSemop ST B L).

(** We now come to the formalization of textbook Hoare logic. Actually, we allow
   for an extension of Hoare logic with a notion of pointer and mutable memory
   (or heap for short) known as Separation logic. Assertions are shallow-encoded. *)

Local Open Scope lang_scope.
Local Open Scope whilesemop_scope.

Definition hoare_semantics (P : assert) (c : cmd) (Q : assert) : Prop :=
  forall s h, P s h -> ~ Some (s, h) -- c ---> None /\
    (forall s' h', Some (s, h) -- c ---> Some (s', h') -> Q s' h').

(** Semantic definition of the weakest liberal precondition of c w.r.t. Q *)
Definition wp_semantics (c : cmd) (Q : assert) : assert :=
  fun s h => ~ (Some (s, h) -- c ---> None) /\
    forall s' h', Some (s, h) -- c ---> Some (s', h') -> Q s' h'.

Definition hoare_semantics_total (P : assert) (c : cmd) (Q : assert) : Prop :=
  forall s h, P s h ->
    exists s', exists h', Some (s, h) -- c ---> Some (s', h') /\  Q s' h'.

End WhileSemaxSemantics.

(********************************************************)

Module Type WhileSemax0 (ST : StateBipl) (B : Bipl ST) (L: WhileSemop0 ST B).

Include (WhileSemaxSemantics ST B L).

Parameter hoare0 : assert -> cmd0 -> assert -> Prop.

Parameter soundness0 : forall P Q c, hoare0 P c Q -> hoare_semantics P (cmd_cmd0 c) Q.

End WhileSemax0.

(********************************************************)

Module Type WhileHoare (ST : StateBipl) (B : Bipl ST) (Semop: WhileSemop0 ST B) (Hoare : WhileSemax0 ST B Semop).

Include Hoare.

Local Open Scope lang_scope.
Local Open Scope whilesemop_scope.
Local Open Scope statebipl_scope.

(** The axioms of Hoare logic are encoded as an inductive type,
    assuming given Hoare triples for one-step, non-branching instructions. *)

Reserved Notation "{[ P ]} c {[ Q ]}" (at level 82, no associativity).
Inductive hoare : assert -> cmd -> assert -> Prop :=
| hoare_hoare0 : forall P Q c, hoare0 P c Q -> {[ P ]} (cmd_cmd0 c) {[ Q ]}
| hoare_seq : forall Q P R c d, {[ P ]} c {[ Q ]} -> {[ Q ]} d {[ R ]} -> {[ P ]} c ; d {[ R ]}
| hoare_conseq : forall P P' Q Q' c, Q' ===> Q -> P ===> P' ->
  {[ P' ]} c {[ Q' ]} -> {[ P ]} c {[ Q ]}
| hoare_while : forall P t c, {[ fun s h => P s h /\ eval_b t (s, h) ]} c {[ P ]} ->
  {[ P ]} while t c {[ fun s h => P s h /\ ~~ eval_b t (s, h) ]}
| hoare_ifte : forall P Q t c d, {[ fun s h => P s h /\ eval_b t (s, h) ]} c {[ Q ]} ->
  {[ fun s h => P s h /\ ~~ eval_b t (s, h) ]} d {[ Q ]} ->
  {[ P ]} ifte t c d {[ Q ]}
where "{[ P ]} c {[ Q ]}" := (hoare P c Q) : whilehoare_scope.

Local Open Scope whilehoare_scope.

Notation "{{ P }} c {{ Q }}" := (hoare P c Q) (at level 82, no associativity) : whilehoare_scope.

Reserved Notation "{{{[ P ]}}} c {{{[ Q ]}}}" (at level 82, no associativity).
Inductive hoare_total : assert -> cmd -> assert -> Prop :=
| hoaret_hoare0 : forall P Q c, hoare0 P c Q -> {{{[ P ]}}} (cmd_cmd0 c) {{{[ Q ]}}}
| hoaret_seq : forall P Q R c d, {{{[ P ]}}} c {{{[ Q ]}}} -> {{{[ Q ]}}} d {{{[ R ]}}} -> {{{[ P ]}}} c ; d {{{[ R ]}}}
| hoaret_conseq : forall P P' Q Q' c, (Q' ===> Q) -> (P ===> P') ->
  {{{[ P' ]}}} c {{{[ Q' ]}}} -> {{{[ P ]}}} c {{{[ Q ]}}}
| hoaret_while : forall P t c
  A (R : A -> A -> Prop) (Rwf : well_founded R) (V : state -> A) a,
  (forall a, {{{[ fun s h => P s h /\ eval_b t (s, h) /\ V (s,h) = a ]}}}
    c {{{[ fun s h => P s h /\ R (V (s,h)) a ]}}}) ->
  {{{[ fun s h => P s h /\ V (s,h) = a ]}}}
    while t c {{{[ fun s h => P s h /\ ~~ eval_b t (s, h) ]}}}
| hoaret_ifte : forall P Q t c d,
  {{{[ fun s1 h => P s1 h /\ eval_b t (s1, h) ]}}} c {{{[ Q ]}}} ->
  {{{[ fun s1 h => P s1 h /\ ~~ eval_b t (s1, h) ]}}} d {{{[ Q ]}}} ->
  {{{[ P ]}}} ifte t c d {{{[ Q ]}}}
where "{{{[ P ]}}} c {{{[ Q ]}}}" := (hoare_total P c Q) : whilehoare_scope.

Notation "{{{ P }}} c {{{ Q }}}" := (hoare_total P c Q) (at level 82, no associativity) : whilehoare_scope.

Lemma hoare_stren P' P Q c : P ===> P' ->
  {{ P' }} c {{ Q }} -> {{ P }} c {{ Q }}.
Proof. move=> H H'; by apply hoare_conseq with P' Q. Qed.

Lemma hoare_stren_seq (P P' Q Q' : assert) c c' : {{ P' }} c {{ Q' }} ->
  P ===> P' -> {{ Q' }} c' {{ Q }} -> {{ P }} c; c' {{ Q }}.
Proof.
move=> Hc HP Hc'; apply hoare_seq with Q' => //; by apply (hoare_stren P').
Qed.

Lemma hoare_weak (Q' P Q : assert) c :
  Q' ===> Q -> {{ P }} c {{ Q' }} -> {{ P }} c {{ Q }}.
Proof. move=> H H'. by apply hoare_conseq with P Q'. Qed.

Lemma hoare_seq_inv P Q c d : {{ P }} c ; d {{ Q }} ->
  exists R, {{ P }} c {{ R }} /\ {{ R }} d {{ Q }}.
Proof.
move H : (c;d) => Hcd.
move=> H'; move: H' c d H.
elim=> //; clear P Q Hcd.
- move=> Q P R c d Hc H1 Hd H2 c0 d0.
  case=> X Y; subst; by exists Q.
- move=> P P' Q Q' c HQ HP Hc IH c0 d.
  case/IH => R [H1 H2].
  exists R; split; by [eapply hoare_stren; eauto | eapply hoare_weak; eauto].
Qed.

Lemma hoare_seq_inv_special (A : Type) (P Q : A -> assert) c d :
  (forall x, {{ P x }} c ; d {{ Q x }}) ->
  exists R : A -> assert,
    (forall x, {{ P x }} c {{ R x }}) /\ (forall x, {{ R x }} d {{ Q x }}).
Proof.
move=> H.
have Y : forall x : A, exists R, {{ P x }} c{{ R }} /\ {{ R }} d {{ Q x }}.
  move=> ?; by eapply hoare_seq_inv; eauto.
case/choice : Y => f Y.
exists f; split=> a; by [apply (proj1 (Y a)) | apply (proj2 (Y a))].
Qed.

Lemma hoare_seq_inv_special' (A : Type) (P Q : A -> assert) c d :
  (forall x, exists y, {{ P x }} c ; d {{ Q y }}) ->
  exists R : A -> assert,
    (forall x, exists y, {{ P x }} c {{ R y }}) /\ (forall x, exists y, {{ R x }} d {{ Q y }}).
Proof.
move=> H.
have Y : forall x : A, exists y R, {{ P x }} c{{ R }} /\ {{ R }} d {{ Q y }}.
  - move => x; move: {H}(H x) => [] y Hy; exists y.
    by eapply hoare_seq_inv; eauto.
case/choice : Y => f Y.
case/choice : Y => f2 Y.
exists f2; split=> a.
exists a.
apply (proj1 (Y a)).
exists (f a).
apply (proj2 (Y a)).
Qed.

Lemma hoare_seq_assoc P c0 c1 c2 Q :
  {{ P }} c0 ; c1 ; c2 {{ Q }}  ->  {{ P }} (c0 ; c1) ; c2 {{ Q }}.
Proof.
case/hoare_seq_inv => s'' [] Hc0.
case/hoare_seq_inv => s''' [] Hc1 Hc2.
apply hoare_seq with s''' => //.
by apply hoare_seq with s''.
Qed.

Lemma hoare_seq_assoc' P c0 c1 c2 Q :
  {{ P }} (c0 ; c1) ; c2 {{ Q }} ->  {{ P }} c0 ; c1 ; c2 {{ Q }}.
Proof.
case/hoare_seq_inv => s'' [].
case/hoare_seq_inv => s''' [] Hc0 Hc1 Hc2.
apply hoare_seq with s''' => //.
by apply hoare_seq with s''.
Qed.

Lemma hoare_ifte_inv P Q b c d : {{ P }} ifte b c d {{ Q }} -> 
  {{ fun s h => P s h /\ eval_b b (s, h) }} c {{ Q }} /\ 
  {{ fun s h => P s h /\ ~~ eval_b b (s, h) }} d {{ Q }}.
Proof.
move H : (ifte b c d) => Hbcd.
move=> H'; move: H' b c d H.
elim=> //; clear P Q Hbcd.
- move=> P P' Q Q' c0 HQ HP Hc IH b c d Hifte.
  case: {IH Hifte}(IH _ _ _ Hifte) => H1 H2; split.
  + eapply hoare_weak; eauto.
    eapply hoare_stren; eauto.
    move=> s h /= [H3 H4]; split => //.
    by apply HP.
  + eapply hoare_weak; eauto.
    eapply hoare_stren; eauto.
    move=> s h /= [H3 H4]; split => //.
    by apply HP.
- move=> P Q b c d Hc IHc Hd IHd b' c' d'.
  case=> X Y Z; by subst.
Qed.

Lemma hoare_while_invariant P t c Q Inv : P ===> Inv ->
  (fun s h => Inv s h /\ ~~ eval_b t (s, h)) ===> Q ->
  {{ fun s h => Inv s h /\ eval_b t (s, h) }} c {{ Inv }} -> 
  {{ P }} while t c {{ Q }}.
Proof.
move=> HP HQ H.
apply (hoare_stren Inv) => //.
apply (hoare_weak (fun s h => Inv s h /\ ~~ eval_b t (s, h))) => //.
by apply hoare_while.
Qed.

Lemma hoare_while_invariant_seq b c I P Q c1 :
  P ===> I ->
  {{ fun s h => I s h /\ eval_b b (s, h) }} c {{ I }} ->
  {{ fun s h => I s h /\ ~~ eval_b b (s, h) }} c1 {{ Q }} ->
  {{ P }} while b c; c1 {{ Q }}.
Proof.
intros.
apply hoare_seq with (fun s => fun h => I s h /\ ~~ eval_b b (s, h)) => //.
by eapply hoare_while_invariant; eauto.
Qed.

Lemma hoare_while_inv' P Q b c : {{ P }} while b c {{ Q }} ->
  exists R, (P ===> R) /\
    {{ fun s h => R s h /\ eval_b b (s, h) }} c {{ R }} /\
    ((fun s h => R s h /\ ~~ eval_b b (s, h)) ===> Q).
Proof.
move Hwhile : (while b c) => c'.
move=> H.
move: H b c Hwhile.
elim => //; clear P Q c'.
- move=> P P' Q Q' c' HQ HP Hc IHc b c Hwhile.
  move: {IHc Hwhile}(IHc _ _ Hwhile) => [R [X1 [X2 X3] ] ].
  exists R; split.
  by apply ent_trans with P'.
  split => //.
  by eapply ent_trans; eauto.
- move=> P b c Hc IH b' c'.
  case=> X Y; subst.
  exists P; split; first by done.
  by split.
Qed.

Lemma hoare_while_inv_special (A : Type) (P Q : A -> assert) b c :
  (forall x, {{ P x }} while b c {{ Q x }}) ->
  exists R : A -> assert,
    (forall x, {{ fun s h => R x s h /\ eval_b b (s, h) }} c {{ R x }}) /\
    (forall x, (P x ===> R x)) /\
    (forall x, ((fun s h =>  R x s h /\ ~~ eval_b b (s, h)) ===> Q x)).
Proof.
move=> H.
have Y : forall x : A, exists R : A -> assert,
    {{ fun s h => R x s h /\ eval_b b (s, h) }} c {{ R x }} /\
    (P x ===> R x) /\
    ((fun s h =>  R x s h /\ ~~ eval_b b (s, h)) ===> Q x).
  move=> a.
  move: (H a) => Ha.
  case: (hoare_while_inv' _ _ _ _ Ha) => R [X1 [X2 X3]].
  by exists (fun x : A => R).
case/choice : Y=> f Y.
exists (fun x => f x x); split.
- move=> a; by apply (proj1 (Y a)).
- split => a; by [apply (proj1 (proj2 (Y a))) | apply (proj2 (proj2 (Y a)))].
Qed.

Lemma hoare_and'' : (forall P Q c, hoare0 P c Q ->
  forall P' Q', {{P'}} (cmd_cmd0 c) {{Q'}} -> {{ P //\\ P' }} cmd_cmd0 c {{ Q //\\ Q' }}) ->
  forall c P Q, {{ P }} c {{ Q }} ->
    forall P' Q' d, {{ P' }} d {{ Q' }} ->
      c = d -> {{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move=> H0 c P Q; elim=> //; clear c P Q.
- move=> P Q c P_c_Q P' Q' d P'_d_Q' c_d.
  apply H0 => //.
  subst d.
  by inversion P'_d_Q'.
- (* case seq *) move=> Q P R c d P_c_Q IHc Q_d_R IHd P' Q' d0 H ?; subst d0.
  apply hoare_seq_inv in H.
  case: H => R' [H1 H2].
  apply hoare_seq with (Q //\\ R').
  + by apply IHc with c.
  + by apply IHd with d.
- (* case conseq *)
  move=> P P' Q Q' c Q'_Q P_P' P'_c_Q' IH P'0 Q'0 d H2 H3.
  apply hoare_conseq with (P' //\\ P'0) (Q' //\\ Q'0).
  rewrite /And /entails => *; by intuition.
  rewrite /And /entails => *; by intuition.
  by apply (IH _ _ d).
- (* case while *) move=> P t c Hoare_c IH P' Q' d Hd d_while.
  subst d.
  apply hoare_while_inv' in Hd.
  case: Hd => R [H1 [H2 H3]].
  apply (hoare_stren (P //\\ R)).
    rewrite /And => ? ?; by intuition.
  apply (hoare_weak (fun s h => (P //\\ R) s h /\ ~~ eval_b t (s, h))).
    rewrite /And => ? ?; by intuition.
  apply hoare_while => //.
  eapply hoare_stren; last first.
    eapply IH.
    by apply H2.
    reflexivity.
  rewrite /And => ? ?; by intuition.
- (* case ifte *) move=> P Q t c d Hoare_c IHc Hoare_d IHd P' Q' d0 Hd0 d0_if.
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
Qed.

Lemma hoare_and' : (forall P Q c, hoare0 P c Q ->
  forall P' Q', {{P'}} (cmd_cmd0 c) {{Q'}} ->{{P //\\ P'}}cmd_cmd0 c {{Q //\\ Q'}}) ->
forall c P Q P' Q',
  {{ P }} c {{ Q }} -> {{ P' }} c {{ Q' }} ->
  {{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof. intros. by apply hoare_and'' with c. Qed.

(* TODO: clean *)
Lemma hoare_false' : (forall (c0 : cmd0) P, {{ FF }} (cmd_cmd0 c0) {{ P }}) -> forall c P, {{ FF }} c {{ P }}.
Proof.
move=> Hp; induction c.
- intro P; by apply Hp.
- intro P; apply hoare_seq with (Q:=FF); by [apply IHc1 | apply IHc2].
- intro P; apply hoare_ifte.
  + apply (hoare_stren FF).
    rewrite /entails; by intuition.
    by apply IHc1.
  + apply (hoare_stren FF).
    rewrite /entails; by intuition.
    by apply IHc2.
- intro P; apply (hoare_weak (fun s h => (fun s' h' => P s' h' /\ ~~ eval_b e (s', h')) s h /\ ~~ eval_b e (s, h))).
  + rewrite /entails; by intuition.
  + apply (hoare_stren (fun s h => P s h /\ ~~ eval_b e (s, h))).
    * rewrite /entails; contradiction.
    * apply hoare_while.
      apply (hoare_stren FF).
      - rewrite /entails => s h [[H H2] H1]; by rewrite H1 in H2.
      - by apply IHc.
Qed.

(* TODO: redo using soundness/completeness? *)
Lemma pull_out_conjunction' : (forall (c0 : cmd0) P, {{ FF }} (cmd_cmd0 c0) {{ P }}) -> forall (A : Prop) P Q c,
  (A -> {{ P }} c {{ Q }}) ->
  {{ fun s h => A /\ P s h }} c {{ Q }}.
Proof.
move=> X A P Q c H.
case: (Classical_Prop.classic A) => HA.
eapply hoare_stren; last by apply H.
by move=> s h [].
eapply hoare_stren; last by apply hoare_false'.
move => s h []; by move/HA.
Qed.

(** The statement of this lemma as well as the proof idea of using ClassicalChoice comes from Andrew W. Appel, septacs.pdf *)
Lemma extract_exists : 
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
  apply (hoare_stren (fun s h => (exists x0, P x0 s h /\ eval_b b (s, h)))).
    move=> s h /= [ [a H1] H2].
    by exists a.
  apply IHc.
  move=> a.
  case/hoare_ifte_inv: (H a) => H' _ //.
  apply (hoare_stren (fun s h => (exists x0, P x0 s h /\ ~~ eval_b b (s, h)))).
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

Lemma soundness P Q c : {{ P }} c {{ Q }} -> hoare_semantics P c Q.
Proof.
elim; clear P Q c.
- (* cmd0 *) move=> P Q c H; by apply soundness0.
- (* seq *) move=> P Q R c d HPcQ IHc HQdR IHd; split.
  + move=> HNone; inversion HNone; subst.
    destruct s' as [[s'h']|].
    * move: (proj2 (IHc _ _ H) _ _ H3) => HQ.
      by apply (proj1 (IHd _ _ HQ)).
    * by apply (proj1 (IHc _ _ H)).
  + move=> s' h' Hexec; inversion Hexec; subst.
    case: (IHc _ _ H) => HcNone HcSome.
    destruct s'0 as [[s'' h'']|].
    * move: (HcSome _ _ H3) => HQ.
      case: (IHd _ _ HQ) => HdNone.
      by apply.
    * by move/from_none : H5.
- (* conseq *) move=> P P' Q Q' c HQ'Q HPP' HP'cQ' IH; split.
  + move: (HPP' _ _ H) => HP'.
    apply (proj1 (IH _ _ HP')).
  + move=> s' h' Hc.
    move: (HPP' _ _ H) => HP'.
    case: (IH _ _ HP') => HcNone HcSome.
    apply HQ'Q => //.
    by apply HcSome.
- (* while *) move=> P t c H IH; split.
  + move Hd : (while t c) => d.
    move HS : (Some (s, h)) => S.
    move HS' : (@None state) => S'.
    move=> H1; move: t H IH s h H0 Hd HS HS'; elim: H1 => //.
    move=> [s h] s' s'' t c' H1 H2 _ H3 IHexec t' Hd IH s3 h1 HS [] X Y; subst.
    case => X Y; subst=> Hs''.
    case: (IH _ _ (conj HS H1)) => Hc'None Hc'Some.
    destruct s' as [[s' h']|] => //.
    move: {Hc'Some}(Hc'Some  _ _ H2) => HP'.
    by move: (IHexec _ Hd IH _ _ HP' (refl_equal _) (refl_equal _) Hs'').
  + move=> s' h'.
    move HC : (while t c) => C.
    move Hsigma : (Some (s, h)) => sigma.
    move Hsigma' : (Some (s', h')) => sigma'.
    move=> H1; move: P t c H IH s h s' h' H0 HC Hsigma Hsigma'; elim: H1 => //.
    * (* case exec_while true *) move=> [s h] sigma'' sigma''' t c Ht H0 _ H2 IHexec P t' c1 HC IH s0 h0 s' h' Hsigma'.
      case => X Y; subst.
      case => X Y; subst => Hsigma'''.
      (* we know s,m,h |= P /\ eval_b true, by the inductive hypothesis IH we have sigma'' |= P *)
      destruct sigma'' as [[s'' h'']|].
      - have HP'' : P s'' h''.
          case: (IH _ _ (conj Hsigma' Ht)) => _; apply; auto.
        (* since sigma'' --while t c---> sigma' and {P}while t c{P /\ eval_b false }, then we have sigma' |= P /\ ~b *)
        by move: (IHexec _ _ _ HC IH _ _ s'  h' HP'' (refl_equal (while t c)) (refl_equal (Some (s'',h''))) Hsigma''').
      - apply from_none in H2.
        by rewrite H2 in Hsigma'''.
    * (* case exec_while false *) move=> [s h] t c Ht P t' c' _ _ s1 h1 s2 h2 HP [] X Y; subst; case=> X Y; subst; case=> X Y; by subst.
- (* ifte *) move=> P Q t c d H1 IH1 H2 IH2; split.
  + move=> H4; inversion H4; subst.
    * by case: (IH1 _ _ (conj H H8)).
    * by case: (IH2 _ _ (conj H H8)).
  + move=> s' h' H4; inversion H4; subst.
    * case: (IH1 _ _  (conj H H8)) => _; by apply.
    * case: (IH2 _ _  (conj H H8)) => _; by apply.
Qed.

(** from a triple and a termination proof, we can deduce that the program does not fail *)
Lemma termi c P Q : {{ P }} c {{ Q }} ->
  (forall s h, P s h -> {s' | Some (s, h) -- c ---> s' } ) ->
  forall s h, P s h ->
    {s' | Some (s, h) -- c ---> Some s' }.
Proof.
move=> Hhoare Hterm s h HP.
move/soundness : Hhoare.
rewrite /hoare_semantics.
move/(_ _ _ HP) => [Hno_err Hsome].
case: {Hterm}(Hterm _ _ HP).
case=> [s' Hexec | ].
by exists s'.
tauto.
Qed.

End WhileHoare.

(**********************)

Module Type WhileSemaxComplete0 (ST : StateBipl) (B : Bipl ST) (Semop: WhileSemop0 ST B) (Hoare: WhileSemax0 ST B Semop).

Include (WhileHoare ST B Semop Hoare).

Local Open Scope lang_scope.
Local Open Scope whilesemop_scope.
Local Open Scope whilehoare_scope.

Parameter wp_semantics_sound0 : forall (c : cmd0) Q, {{ wp_semantics (cmd_cmd0 c) Q }} (cmd_cmd0 c) {{ Q }}.
Parameter wp0 : cmd0 -> assert -> assert.
Parameter wp0_no_err : forall s h c P,  wp0 c P s h -> ~ (Some (s,h) -- c ----> None).

End WhileSemaxComplete0.

(***********************)

Module WhileSemaxComplete (ST : StateBipl) (B : Bipl ST) (Semop: WhileSemop0 ST B) (Hoare: WhileSemax0 ST B Semop) (Complete: WhileSemaxComplete0 ST B Semop Hoare).

Include Complete.

Local Open Scope lang_scope.
Local Open Scope whilesemop_scope.
Local Open Scope whilehoare_scope.

Lemma wp_semantics_sound : forall c Q, {{ wp_semantics c Q }} c {{ Q }}.
Proof.
elim.
- move=> c Q; by apply wp_semantics_sound0.
- (* seq *) move=> c1 IHc1 c2 IHc2 Q.
  apply (hoare_stren (wp_semantics c1 (wp_semantics c2 Q))); last first.
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
- (* while_bne *) move=> b c IHc Q; apply (hoare_weak (fun s h' => (wp_semantics (while b c) Q) s h' /\ ~~ eval_b b (s, h'))).
  + move=> s h [[H H2] H1]; by apply H2, exec_while_false.
  + apply hoare_while.
    apply (hoare_stren (wp_semantics c (wp_semantics (while b c) Q))).
    * move=> s h [[H H2] H1]; red; split.
      by apply exec_while1_not_None with b.
      move=> s' h' H0; red; split.
      by apply exec_while2_not_None with s h.
      move=> s'0 h'0 H3; by apply H2, exec_while_true with (Some (s', h')).
    * by apply IHc.
Qed.

Lemma hoare_complete  P Q c : hoare_semantics P c Q -> {{ P }} c {{ Q }}.
Proof.
move=> H.
apply (hoare_stren (wp_semantics c Q)).
move=> s h; split.
apply (proj1 (H _ _ H0)).
move=> s' h' H'.
apply (proj2 (H _ _ H0) _ _ H').
by apply wp_semantics_sound.
Qed.

(*  new versions *)

Local Open Scope statebipl_scope.

Lemma hoare_L_or P Q R c : 
  {{ P }} c {{ R }} -> {{ Q }} c {{ R }} -> {{ P \\// Q }} c {{ R }}.
Proof.
move=> /soundness H1 /soundness H2.
apply hoare_complete => s h []; by [move/H1 | move/H2].
Qed.

Lemma hoare_R_ex (A : Type) P (Q : A -> assert) c :
  (exists y, {{ P }} c {{ Q y }}) ->
  {{ P }} c {{ fun s h => exists x, Q x s h }}.
Proof.
case=> x Hoare.
eapply hoare_conseq; last 2 first.
  by apply ent_id.
  by apply Hoare.
move => s h /= HQ; by exists x.
Qed.

Lemma hoare_L_ex (A : Type) Q (P : A -> assert) c :
  (forall x, {{ P x }} c {{ Q }}) ->
  {{ fun s h => exists x, P x s h }} c {{ Q }}.
Proof.
move=> Hoare.
apply hoare_complete => s h [x Hx].
by apply (soundness _ _ _ (Hoare x) s h Hx).
Qed.

Lemma hoare_LR_and P P' Q Q' c :
    ({{ P }} c {{ Q }} /\ {{ P' }} c {{ Q' }}) ->
    {{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move => [] H1 H2.
apply hoare_complete => s h [] HP HP'.
move: {H1}(soundness _ _ _ H1 s h HP) => [] H11 H12.
move: {H2}(soundness _ _ _ H2 s h HP') => [] H21 H22.
split => //=.
move => s' h' Hc.
split => //=.
by apply H12.
by apply H22.
Qed.

Definition pure (P : assert) := forall s h s' h', P s h <-> P s' h'.

Lemma hoare_pure_left P P' Q Q' c : pure P ->
  ((P ===> Q) /\ {{ P' }} c {{ Q' }}) ->
  {{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move => pure [] H1 H2.
apply hoare_complete => s h [] HP HP'.
move: {H2}(soundness _ _ _ H2 s h HP') => [] H21 H22.
split => //=.
move => s' h' Hc.
split; last first.
by apply H22 => //=.
apply H1.
rewrite pure.
apply HP.
Qed.

Lemma hoare_and_left (P P' Q Q' : assert) c :
  (forall s h s' h', 
    Some (s, h) -- c ---> Some (s', h') ->
    P s h -> Q s' h') -> {{ P' }} c {{ Q' }} ->
  {{ P //\\ P' }} c {{ Q //\\ Q' }}.
Proof.
move => H H1.
apply hoare_complete => s h [] HP HP'.
move: {H1}(soundness _ _ _ H1 s h HP') => [] H21 H22.
split => //=.
move => s' h' Hc.
split; last first.
by apply H22 => //=.
apply (H s h) => //=.
Qed.

Lemma hoare_total_sound' : (forall (P Q : assert) c, hoare0 P c Q -> 
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
  case/boolP : (eval_b t (s, h)) => Htest.
  - case: (IHhoare a _ _ (conj HP (conj Htest Ha))) => s' [h' [Hexec [HP' HR]]].
    move: {Hrec}(Hrec _ HR H IHhoare) => Hrec.
    case: {Hrec}(Hrec _ _ (conj HP' refl_equal)) => s'' [h'' [H1 [H2 H3]]].
    exists s'', h''; split => //.
    apply while_seq' => //.
    by apply exec_seq with (Some (s',h')).
  - exists s, h; split; last by done.
    by apply exec_while_false.
- (* ifte *) move=> P Q t c d H1 IHhoare1 H2 IHhoare2 s h HP.
  case/boolP : (eval_b t (s, h)) => Htest.
  - case: (IHhoare1 s h) => // s' [h' K1].
    exists s', h'; split; last by tauto.
    constructor; tauto.
  - case: (IHhoare2 s h); first by done.
    move=> s' [h' [K1 K2]].
    exists s', h'; split; last by assumption.
    by apply exec_ifte_false.
Qed.

Lemma hoare_L_F c Q : {{ FF }} c {{ Q }}.
Proof. by apply hoare_complete. Qed.

(*Lemma hoare_contra_precond Q P c : P ===> FF -> {{ P }} c {{ Q }}.
Proof. move=> H; eapply hoare_stren; by [apply H | apply FFHoare]. Qed.*)

End WhileSemaxComplete.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool seq.
Require while.

(** * %\goto%#Goto#: A Low-level Language

   This section corresponds to Section 2 in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. *)

Module Goto (while_semop_m : while.WHILE_SEMOP).

Import while_semop_m.

(** ** Syntax and (Small-step) Semantics of %\goto\ %#Goto# *)

Definition label := nat.

Lemma label_dec : forall (l l' : label), { l = l' } + { l <> l' }.
Proof. decide equality. Qed.

Definition lstate := option (label * state).

(** printing ||- %\ensuremath{\vdash}%*)

(** For the operational semantics of one-step, non-branching instructions of
   %\goto%#Goto#, we use the one-step commands
   (type %\coqdocvar{cmd0}%#cmd0# and operational semantics noted $\cdot-\cdot\to\cdot$#-- ---->#)
   %(see Section \ref{sec:while})%. *)

(** printing ----> %\ensuremath{\rightarrow}%*)

(** printing ---> %\ensuremath{\rightarrow}%*)

Local Open Scope while_cmd_scope.

Reserved Notation " c ||- s ---> t " (at level 82, no associativity).
Inductive exec0_label : lstate -> cmd0 -> lstate -> Prop :=
| exec0_label_cmd0 : forall s c s', Some s -- c ----> Some s' ->
  forall l, exec0_label (Some (l, s)) c (Some (S l, s'))
| exec0_label_err : forall s c, Some s -- c ----> None ->
  forall l, exec0_label (Some (l, s)) c None
where " c ||- s ---> t " := (exec0_label s c t) : goto_scope.

Local Open Scope goto_scope.

(** Branches may be conditional or not. For conditional branches, we use a language of boolean expressions
   (type %\coqdocvar{expr\_b}%#expr_b#)
   %(see Section \ref{sec:while})%: *)

Inductive branch : Type := jmp : label -> branch | cjmp : expr_b -> label -> branch.

(** printing |>> %\ensuremath{\gg}%*)

Reserved Notation "c ||- s |>> t" (at level 82, no associativity).

(** Note that branches never cause errors: *)

Inductive exec_branch : label * state -> branch -> label * state -> Prop :=
| exec_jmp : forall l s l', jmp l' ||- (l, s) |>> (l', s)
| exec_cjmp_true : forall l s t l', eval_b t s -> cjmp t l' ||- (l, s) |>> (l', s)
| exec_cjmp_false : forall l s t l', ~ eval_b t s -> cjmp t l' ||- (l, s) |>> (S l, s)
where "c ||- s |>> t" := (exec_branch s c t) : goto_scope.

(** Unstructured programs are lists of labeled (branching or not) instructions. They are
   wellformed when no instruction has two labels: *)

Inductive insn : Type := C : cmd0 -> insn | B : branch -> insn.

Definition code := seq (label * insn).

Reserved Notation "c ||- s ->> t" (at level 82, no associativity).

Definition wellformed_goto (c : code) : Prop :=
  forall l i i', List.In (l, i) c -> List.In (l, i') c -> i = i'.

Lemma wellformed_goto_app c : wellformed_goto c ->
  forall c1 c2, c = c1 ++ c2 -> wellformed_goto c1 /\ wellformed_goto c2.
Proof.
move=> wf_c c1 c2 Hc; subst; split => x l l' l_c1 l'_c1';
  apply (wf_c x l l'); apply List.in_or_app; by auto.
Qed.

Lemma dom_In_wf c : wellformed_goto c -> forall p i, List.In (p, i) c ->
  forall c1 c2, c = c1 ++ c2 -> List.In p (unzip1 c1) -> List.In (p, i) c1.
Proof.
move=> Hwf p i HIn p1 p2 Hp.
case/List.in_map_iff; case=> p_ i' /= [] ? ?; subst p_.
have : List.In (p, i') c by rewrite Hp; apply List.in_or_app; left.
by move/(Hwf _ _ _ HIn) => ->.
Qed.

Lemma dom_In_wf2 c : wellformed_goto c -> forall p i, List.In (p, i) c ->
  forall c1 c2, c = c1 ++ c2 -> List.In p (unzip1 c2) -> List.In (p, i) c2.
Proof.
move=> Hwf p l HIn p1 p2 Hp.
case/List.in_map_iff; case=> p_ i' /= [] ? ?; subst p_.
have : List.In (p, i') c by rewrite Hp; apply List.in_or_app; right.
by move/(Hwf _ _ _ HIn) => ->.
Qed.

(** printing ->> %\ensuremath{\twoheadrightarrow}%*)

(** We can now define the semantics of %\goto%#Goto#. The type below
   corresponds to Figure 1 (%\figureone%#Small-step semantics rules of Goto#) in
   %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Inductive exec_goto : code -> lstate -> lstate -> Prop :=
| exec_goto_cmd0 : forall l i s s' c, List.In (l, C i) c  ->
  i ||- Some (l, s) ---> Some s' -> c ||- Some (l, s) ->> Some s'
| exec_goto_cmd0_err : forall l i s c, List.In (l, C i) c  ->
  i ||- Some (l, s) ---> None -> c ||- Some (l, s) ->> None
| exec_goto_branch : forall l j s s' c, List.In (l, B j) c ->
  j ||- (l, s) |>> s'  -> c ||- Some (l, s) ->> Some s'
where "c ||- s ->> t" := (exec_goto c s t) : goto_scope.

Lemma cmd0_labels c l s l' s' : c ||- Some (l, s) ---> Some (l', s') ->
  l <> l'.
Proof. move=> H; inversion H; by subst. Qed.

(** ** Properties *)

(** %See the end of Section \ref{sec:closure} for a comment about Lemma 2 (\lemmatwo).%

%\noindent% Lemma 3 (%\lemmathree%#Extension of the domain#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Lemma exec_goto_extension_right' : forall c s s' i, c ||- s ->> s' ->
  c ++ i :: nil ||- s ->> s'.
Proof.
move=> c [ [l s] |] [ [l' s'] |] i H; inversion H; subst => //.
- eapply exec_goto_cmd0; eauto; apply List.in_or_app; by left.
- eapply exec_goto_branch; eauto; apply List.in_or_app; by left.
- eapply exec_goto_cmd0_err; eauto; apply List.in_or_app; by left.
Qed.

Lemma exec_goto_extension_right : forall c' s s' c, c ||- s ->> s'  ->  c ++ c' ||- s ->> s'.
Proof.
elim.
- by move=> *; rewrite cats0.
- move=> i lst IH s s' c H.
  rewrite (_ : c ++ i :: lst = (c ++ i :: nil) ++ lst); last by rewrite -catA.
  by apply IH, exec_goto_extension_right'.
Qed.

Lemma exec_goto_contraction_right_ c st st' : c ||- st ->> st'  ->
 forall c1 c2 l s l' s', c = c1 ++ c2 -> st = Some (l,s) -> st' = Some (l',s') ->
  List.In l (unzip1 c1) -> ~ List.In l (unzip1 c2) ->
   c1 ||- st ->> st'.
Proof.
move=> [] //; 
  move=> {c st st'} p i s [l' s'] c HIn H c1 c2 l0 s0 l1 s1 Hc;
    case=> X Y; subst; case=> X Y; subst => l0_c1 l0_c2.
- eapply exec_goto_cmd0; eauto.
  case: (List.in_app_or _ _ _ HIn) => // abs.
  exfalso; apply/l0_c2/List.in_map_iff.
  eexists; split; last by apply abs. done.
- eapply exec_goto_branch; eauto.
  case: (List.in_app_or _ _ _ HIn) => // abs.
  exfalso; apply/l0_c2/List.in_map_iff.
  eexists; split; last by apply abs. done.
Qed.

Lemma exec_goto_contraction_right c1 c2 : wellformed_goto (c1 ++ c2) ->
  forall l s l' s', c1 ++ c2 ||-  Some (l, s) ->> Some (l', s')  ->
    List.In l (unzip1 c1) -> c1 ||-  Some (l, s) ->> Some (l', s').
Proof.
move=> Hwf l s l' s'; move: Hwf.
move Heqc : (c1 ++ c2) => c. move Heqs : (Some (l, s)) => st. move Heqs' : (Some (l', s')) => st'.
move=> Hwf H; move: H c1 c2 l s l' s' Heqc Heqs Heqs' Hwf.
case=> //; move=> {st st' c} p i s [p' s'] c HIn H c1 c2 l st l' st' Hc;
  case=> X Y; subst; case=> X Y; subst => wf_c p_c1.
- eapply exec_goto_cmd0; eauto; by eapply dom_In_wf; eauto.
- eapply exec_goto_branch; eauto; by eapply dom_In_wf; eauto.
Qed.

Lemma exec_goto_extension_left : forall c s s' i, c ||- s ->> s' -> i :: c ||- s ->> s'.
Proof.
move=> c [[l s]|] [[l' s']|] i H; inversion H; subst => //.
- eapply exec_goto_cmd0; eauto; rewrite /=; by right.
- eapply exec_goto_branch; eauto; rewrite /=; by right.
- eapply exec_goto_cmd0_err; eauto; rewrite /=; by right.
Qed.

Lemma exec_goto_contraction_left_ c st st' : c ||- st ->> st' ->
 forall c1 c2 l s l' s', c = c1 ++ c2 -> st = Some (l, s) -> st' = Some (l', s') ->
  List.In l (unzip1 c2) -> ~ List.In l (unzip1 c1) -> c2 ||- st ->> st'.
Proof.
move=> Hexec; destruct Hexec => c1 c2 l0 s0 l' st' Hc H3 H4 HIn HnotIn.
- case: H3 => X Y; subst.
  case: H4 => X; subst.
  apply exec_goto_cmd0 with i => //.
  case/(List.in_app_or _ _ _) : H => // abs.
  exfalso; apply/HnotIn/List.in_map_iff.
  eexists; split; last by apply abs. done.
- done.
- case: H3 => X Y; subst.
  case: H4 => X; subst.
  apply exec_goto_branch with j => //.
  case/(List.in_app_or _ _ _) : H => // abs.
  exfalso; apply/HnotIn/List.in_map_iff.
  eexists; split; last by apply abs. done.
Qed.

Lemma exec_goto_contraction_left c1 c2 : wellformed_goto (c1 ++ c2) ->
 forall l s l' s', c1 ++ c2 ||- Some (l, s) ->> Some (l', s')  ->
  List.In l (unzip1 c2) -> c2 ||- Some (l, s) ->> Some (l', s').
Proof.
move=> Hwf l s l' s'; move : Hwf.
move Heqc : (c1 ++ c2) => c. move Heqs : (Some (l, s)) => st.
move Heqs' : (Some (l', s')) => st'.
move=> Hwf H; move: H c1 c2 l s l' s' Heqc Heqs Heqs' Hwf.
case=> //; move=> {st st' c} p i s [p' s'] c HIn H c1 c2 l st l' st' Hc;
    case=> X Y; subst; case=> X Y; subst => wf_c p_c2.
- eapply exec_goto_cmd0; eauto; by eapply dom_In_wf2; eauto.
- eapply exec_goto_branch; eauto; by eapply dom_In_wf2; eauto.
Qed.

(** ** Reflexive, Transitive Closure Predicates *)

(** %\label{sec:closure}%

   %\noindent% Reflexive, transitive closure, to be used in Theorem 6 
   (%\theoremsix%#Preservation of evaluations as stuck reduction sequences#) of 
   %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

(** printing --->* %\ensuremath{\twoheadrightarrow^*}% *)

Reserved Notation  " c ||- s '--->*' t " (at level 82, no associativity).

Inductive redseqs : code -> lstate -> lstate -> Prop :=
| redseqs_refl : forall s c, c ||- s --->* s
| redseqs_trans : forall s s' s'' c, c ||- s --->* s' -> c ||- s' ->> s'' -> c ||- s --->* s''
where " c ||- s '--->*' t " :=  (redseqs c s t) : goto_scope.

Lemma redseqs_inv_nil s s' : nil ||- s --->* s' -> s = s'.
Proof.
move H' : nil => c H; move: H H'.
elim=> // ls ls' ls'' c0 H IH H0 H1; subst.
by inversion_clear H0.
Qed.

Lemma redseqs_transitivity' c s' s'' : c ||- s' --->* s'' -> 
  forall s, c ||- s --->* s' -> c ||- s --->* s''.
Proof.
elim=> // st st' st'' c0 H IH H' st0 H''.
apply redseqs_trans with st'; [by apply IH | exact H'].
Qed.

Lemma redseqs_transitivity c s s' : c ||- s --->* s' -> 
  forall s'', c ||- s' --->* s''  ->  c ||- s --->* s''.
Proof. move=> H s'' H'; by apply redseqs_transitivity' with s'. Qed.

Lemma redseqs_extension_left'' c s' s'' : c ||- s' --->* s'' ->
  forall l i l' st', s' = Some (l', st')  ->  (l, i) :: c ||- s' --->* s''.
Proof.
elim=> //; move=> {c s' s''}. 
- move=> *; by apply redseqs_refl.
- move=> s s' s'' c Hc IH Hc' l i l' st' Hs.
  apply redseqs_trans with s'.
  + by eapply IH; eauto.
  + inversion Hc'; subst.
    * eapply exec_goto_cmd0; eauto; rewrite /=; by right.
    * eapply exec_goto_cmd0_err; eauto; rewrite /=; by right.
    * eapply exec_goto_branch; eauto; rewrite /=; by right.
Qed.

Lemma redseqs_extension_left' c l' s' s'' : c ||- Some (l', s') --->* s'' ->
 forall l i, (l, i) :: c ||- Some (l', s') --->* s''.
Proof. move=> H l i; by apply (redseqs_extension_left'' _ _ _ H l i l' s'). Qed.

Lemma redseqs_extension_left c l s s' c' :
  c ||- Some (l, s) --->* s' -> c' ++ c ||- Some (l, s) --->* s'.
Proof.
induction c' => // *.
destruct a; by apply redseqs_extension_left'; auto.
Qed.

Lemma redseqs_extension_right''' c st' st'' : redseqs c st' st'' ->
 forall l i l' s' , st' = Some (l', s') -> redseqs (c ++ (l, i) :: nil) st' st''.
Proof.
elim=> //; move=> {c st' st''}.
- move=> *; by apply redseqs_refl.
- move=> s s' s'' c Hc IH Hc' l i l' s'0 Hs.
  apply redseqs_trans with s'.
  + by eapply IH; eauto.
  + inversion Hc'; subst.
    * eapply exec_goto_cmd0; eauto; apply List.in_or_app; by left.
    * eapply exec_goto_cmd0_err; eauto; apply List.in_or_app; by left.
    * eapply exec_goto_branch; eauto; apply List.in_or_app; by left.
Qed.

Lemma redseqs_extension_right'' c l' s' s'' : redseqs c (Some (l', s')) s'' ->
  forall l i, redseqs (c ++ (l, i) :: nil) (Some (l', s')) s''.
Proof. move=> H l i; by apply (redseqs_extension_right''' _ _ _ H l i l' s'). Qed.

Lemma redseqs_extension_right' : forall c l s s' c',
  redseqs c (Some (l, s)) s' -> redseqs (c ++ rev c') (Some (l, s)) s'.
Proof.
induction c'; intros.
- by rewrite cats0.
- rewrite -cat1s rev_cat catA; destruct a; by apply redseqs_extension_right''; auto.
Qed.

Lemma redseqs_extension_right c l s s' c' :
  c ||- Some (l, s) --->* s' -> c ++ c' ||- Some (l, s) --->* s'.
Proof.
move=> H.
rewrite -(revK c'); by apply redseqs_extension_right'.
Qed.

(** Reflexive, transitive closure with explicit index k,
   to be used in Theorem 7 (%\theoremseven%#Reflection of stuck reduction sequences as evaluations#): *)

Inductive redseq (c : code) : nat -> lstate -> lstate -> Prop :=
| zero_red : forall s, redseq c O s s
| more_red : forall n s s' s'', c ||- s ->> s' -> redseq c n s' s'' -> redseq c (S n) s s''.

Lemma more_red' c n s s' : redseq c n s s' -> forall s'', c ||- s' ->> s'' -> redseq c (S n) s s''.
Proof.
induction 1.
- move=> s'' H. apply more_red with s'' => //; destruct s''; by apply zero_red.
- move=> s''' H'. apply more_red with s' => //; by apply IHredseq.
Qed.

Lemma red_seqs_red_seq p s s' : redseqs p s s' -> exists n, redseq p n s s'.
Proof.
induction 1.
- exists O; destruct s; by apply zero_red.
- case: IHredseqs => n IH; exists (S n); by apply more_red' with s'.
Qed.

Lemma redseq_nil k ST ST' : redseq nil k ST ST' -> ST = ST'.
Proof. elim=> // n s s' s'' Hexec Hredseq; by inversion Hexec. Qed.

Lemma redseq_inv_refl' c k st st' : redseq c k st st' ->
  forall l s, st = Some (l, s) -> ~ List.In l (unzip1 c) -> st = st'.
Proof.
move=> [] // n s s' s'' Hexec Hredseq l s0 H1 H2; subst.
inversion Hexec => //; subst.
exfalso; apply/H2/List.in_map_iff; by eexists (l, C i).
exfalso; apply/H2/List.in_map_iff; by eexists (l, C i).
exfalso; apply/H2/List.in_map_iff; by eexists (l, B j).
Qed.

Lemma redseq_sC_refl : forall k c st st', redseq c k st st' ->
  forall l s l' s' p i, st = Some (l, s) -> st' = Some (l', s') ->
    c = (p, C i) :: nil -> p <> l -> st = st'.
Proof.
move=> [|n] c st st' H l s l' s' p i Hst Hst' Hc Hpl; subst.
- by inversion H; subst.
- inversion H; subst.
  inversion H1; subst.
  * case: H5 => //. case=> X Y; by subst.
  * case: H5 => //. case=> X Y; by subst.
  * by case: H5.
Qed.

Lemma redseq_sC_inv : forall k c st st', redseq c k st st' ->
  forall l s l' s' i, st = Some (l, s) -> st' = Some (l', s') ->
    l <> l' -> c = (l, C i) :: nil -> i ||- st ---> st'.
Proof.
induction 1.
- destruct s as [[l1 s1]|] => //.
  move=> l s0 l' s' i [Hs1 Hs2] [Hs'1 Hs'2] Hll' Hc; by subst.
- move=> l s0 l' s'0 i Hs Hs'' Hll' Hc; subst.
  inversion H; subst.
  + case: H4 => //. case => X; subst.
    inversion H0; subst => //.
    inversion H1; subst.
     * case: H4 => //. case => X Y; subst.
       by apply cmd0_labels in H6.
     * case: H4 => //. case => X Y; subst.
       inversion H2; subst.
       inversion H3; by subst.
     * by case: H4.
  + case: H4 => //. case => X; subst.
    inversion H0; subst.
    inversion H1; by subst.
  + by case: H4.
Qed.

Lemma redseq_self_jump : forall k l s l' s', l <> l' ->
  ~ redseq ((l, B (jmp l)) :: nil) k (Some (l, s)) (Some (l', s')).
Proof.
elim.
- move=> l s l' s' l_l' H; inversion H; by subst.
- move=> k IH l s l' s' l_l' H; inversion H; subst.
  inversion H1; subst.
  + by case: H5.
  + by case: H5.
  + case: H5 => //. case=> X; subst.
    inversion H7; subst.
    by move: (IH _ s _ s' l_l').
Qed.

Lemma redseq_self_cjmp : forall k t l s l' s', l <> l' -> eval_b t s ->
  ~ redseq ((l, B (cjmp t l)) :: nil) k (Some (l, s)) (Some (l', s')).
Proof.
elim.
- move=> t l s l' s' l_l' Hb H; inversion H; by subst.
- move=> k IH t l s l' s' l_l' Hb H; inversion H; subst.
  inversion H1; subst.
  + rewrite /= in H5; by case: H5.
  + rewrite /= in H5; by case: H5.
  + rewrite /= in H5; case: H5; last by done.
    case=> ?; subst j.
    inversion H7; subst => //.
    by move: (IH _ _ _ _ s' l_l' H8).
Qed.

(** The following two lemmas express, in the particular case of branches, a property similar to Lemma 2 (%\lemmatwo%#Stuck states#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. They are used in the proof of Theorem 7 (%\theoremseven%#Reflection of stuck reduction sequences as evaluations#) in lieu of Lemma 2. *)

Lemma redseq_out_of_domain_jump : forall k p m l s l' s', p <> l ->
  redseq ((p, B (jmp m)) :: nil) k (Some (l, s)) (Some (l', s')) -> l = l' /\ s = s'.
Proof.
elim.
- do 7 intro; inversion 1; by subst.
- move=> k IH p m l s l' s' Hpl; inversion 1; subst.
  inversion H1; subst.
  + by case: H5.
  + by case: H5.
  + case: H5 => //. case=> X Y; by subst.
Qed.

Lemma redseq_out_of_domain_cjmp : forall k p t m l s l' s', p <> l ->
  redseq ((p, B (cjmp t m)) :: nil) k (Some (l, s)) (Some (l', s')) -> l = l' /\ s = s'.
Proof.
elim.
- do 8 intro; inversion 1; by subst.
- move=> k IH p t m l s l' s' Hpl; inversion 1; subst.
  inversion H1; subst.
  + by case: H5.
  + by case: H5.
  + case: H5 => //. case=> X Y; by subst.
Qed.

End Goto.

Module Goto_Deter (while_semop_deter_m : while.WHILE_SEMOP_DETER).

Module Import goto_m := Goto while_semop_deter_m.

Import while_semop_deter_m.

Local Open Scope while_cmd_scope.
Local Open Scope goto_scope.

(** ** Properties *)

(** Lemma 1 (%\lemmaone%#Determinacy#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Lemma exec0_label_deter : forall s c s', c ||- s ---> s' ->
  forall s'', c ||- s ---> s'' -> s' = s''.
Proof.
move=> [[l s]|] c [[l' s']|] H; inversion H; subst.
- move=> [[l'' s'']|] H'; inversion H'; subst.
  + case: (exec0_deter _ _ _ H3 _ H4) => ?; by subst.
  + by move: (exec0_deter _ _ _ H3 _ H4).
- move=> [[l'' s'']|] H'; inversion H'; subst; last by reflexivity.
  by move: (exec0_deter _ _ _ H3 _ H4).
Qed.

Lemma branch_deter s c s' : c ||- s |>> s' ->
  forall s'', c ||- s |>> s'' -> s' = s''.
Proof. inversion_clear 1; move=> s''; by inversion_clear 1. Qed.

Lemma exec_goto_deter : forall c, wellformed_goto c ->
 forall s s', c ||- s ->> s' -> forall s'', c ||- s ->> s'' -> s' = s''.
Proof.
move=> c Hwf [[l s]|] [[l' s']|]  H' [[l'' s'']|] H'' //; inversion H'; inversion H''; subst.
- case: (Hwf _ _ _ H3 H9) => ?; subst.
  by rewrite (exec0_label_deter _ _ _ H4 _ H10).
- by move: (Hwf _ _ _ H3 H9).
- by move: (Hwf _ _ _ H3 H9).
- case: (Hwf _ _ _ H3 H9) => ?; subst.
  by rewrite (branch_deter _ _ _ H4 _ H10).
- case: (Hwf _ _ _ H3 H8) => X; subst.
  by move: (exec0_label_deter _ _ _ H4 _ H9).
- by move: (Hwf _ _ _ H3 H8).
- case: (Hwf _ _ _ H2 H8) => X; subst.
  by move: (exec0_label_deter _ _ _ H3 _ H9).
- by move: (Hwf _ _ _ H2 H8).
Qed.

End Goto_Deter.

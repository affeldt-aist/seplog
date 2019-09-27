(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Wf_nat Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import seq_ext goto.

(** * %\sgoto%#SGoto#, A Structured Version

   %\label{sec:sgoto}%

   This corresponds to Section 3.1 of %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. *)

Declare Scope sgoto_scope.

Module SGoto (while_semop_deter_m : while.WHILE_SEMOP_DETER).

Module Import goto_deter_m := Goto_Deter while_semop_deter_m.
Import goto_m.
Import while_semop_deter_m.

(** ** Natural Semantics Rules of %\sgoto%#SGoto# *)

Inductive scode : Type :=
| sO : scode
| sC : label -> cmd0 -> scode
| sB : label -> branch -> scode
| sS : scode -> scode -> scode.

(** printing [+] %\ensuremath{\oplus}% *)

Notation "c '[+]' d" := (sS c d) (at level 69, right associativity) : sgoto_scope.

Local Open Scope sgoto_scope.

Fixpoint sdom sc :=
  match sc with
    | sO => nil | sC l _ => l :: nil | sB l _ => l :: nil
    | sc1 [+] sc2 => sdom sc1 ++ sdom sc2
  end.

Lemma sdom_dec : forall sc, { sdom sc = nil } + { sdom sc <> nil }.
Proof.
elim.
- by left.
- move=> *; by right.
- move=> *; by right.
- move=> s [Hs | Hs] s0 [Hs0 | Hs0] /=.
  - rewrite Hs Hs0 /=; by left.
  - by rewrite Hs /=; right; auto.
  - by rewrite Hs0 /= cats0; right.
  - right=> X; by destruct (sdom s).
Qed.

Lemma lbl_sdom_dec : forall sc l, { List.In l (sdom sc) } + { ~ List.In l (sdom sc) }.
Proof.
elim.
- by auto.
- move=> /= l _ l0; case (label_dec l l0).
  + by auto.
  + move=> X; right; contradict X; by case: X.
- move=> /= l _ l0; case (label_dec l l0).
  + by auto.
  + move=> X; right; contradict X; by case: X.
- move=> s IH s0 IH' l; case: (IH l); case: (IH' l)=> l_s0 l_s.
  + by left; apply List.in_or_app; auto.
  + by left; apply List.in_or_app; auto.
  + by left; apply List.in_or_app; auto.
  + right; contradict l_s0.
    rewrite /= in l_s0; apply List.in_app_or in l_s0; by case: l_s0.
Qed.

Lemma not_in_sdom_sS m c d : ~ List.In m (sdom (c [+] d)) -> ~ List.In m (sdom d).
Proof. move=> /= H; contradict H. apply List.in_or_app; by right. Qed.

Lemma not_in_sdom_sS' m c d : ~ List.In m (sdom (c [+] d)) -> ~ List.In m (sdom c).
Proof. move=> /= H; contradict H. apply List.in_or_app; by left. Qed.

(** Structured code is wellformed when instructions all have different labels: *)

Inductive wellformed : scode -> Prop :=
| wf_sO : wellformed sO
| wf_sC : forall x y, wellformed (sC x y)
| wf_sB : forall x y, wellformed (sB x y)
| wf_sS : forall sc1 sc2, disj (sdom sc1) (sdom sc2) ->
  wellformed sc1 -> wellformed sc2 -> wellformed (sc1 [+] sc2).

Lemma wellformed_inv_L sc1 sc2 : wellformed (sc1 [+] sc2) -> wellformed sc1.
Proof. by inversion 1. Qed.

Lemma wellformed_inv_R sc1 sc2 : wellformed (sc1 [+] sc2) -> wellformed sc2.
Proof. by inversion 1. Qed.

Lemma wellformed_In_L sc0 sc1 l : wellformed (sc0 [+] sc1) ->
 List.In l (sdom sc0) -> ~ List.In l (sdom sc1).
Proof. move=> H H'; inversion H; subst; by apply (proj1 (H2 l)). Qed.

Lemma wellformed_In_R sc0 sc1 l : wellformed (sc0 [+] sc1) ->
 List.In l (sdom sc1) -> ~ List.In l (sdom sc0).
Proof. move=> H H'; inversion H; subst; move: (proj1 (H2 l)); tauto. Qed.

Lemma wellformed_neu sc : wellformed sc -> wellformed (sc [+] sO).
Proof. move=> H. apply wf_sS => //; by [apply disj_nil_R | constructor]. Qed.

Lemma wellformed_ass sc0 sc1 sc2 :
  wellformed ((sc0 [+] sc1) [+] sc2) -> wellformed (sc0 [+] sc1 [+] sc2).
Proof.
inversion_clear 1.
rewrite /= in H0.
inversion_clear H1.
apply wf_sS => //.
- case/disj_app_inv : H0 => H5 H6.
  apply disj_sym => /=.
  apply disj_app; split; by apply disj_sym.
- apply wf_sS => //.
  by case/disj_app_inv : H0.
Qed.

Lemma wellformed_ass' sc0 sc1 sc2 :
  wellformed (sc0 [+] sc1 [+] sc2) -> wellformed ((sc0 [+] sc1) [+] sc2).
Proof.
inversion_clear 1.
inversion_clear H2.
rewrite /= in H0; move/disj_sym : H0.
case/disj_app_inv => sc1_sc0 sc2_sc0.
apply wf_sS => //=.
- apply disj_app; split => //; by apply disj_sym.
- apply wf_sS => //; by apply disj_sym.
Qed.

(** The forgetful function forgets the structure of the code, effectively turning a piece
   of %\sgoto\ %#SGoto# code into a piece of %\goto\ %#Goto# code: *)

Fixpoint U sc :=
  match sc with
    | sO => nil | sC l c => (l, C c) :: nil | sB l b => (l, B b) :: nil
    | sc1 [+] sc2 => U sc1 ++ U sc2
  end.

Lemma sdom_dom : forall sc, sdom sc = unzip1 (U sc).
Proof. elim=> //= s -> s0 ->; by rewrite /unzip1 map_cat. Qed.

Lemma In_U_In_sdom sc l i : List.In (l, i) (U sc) -> List.In l (sdom sc).
Proof. move=> H. rewrite sdom_dom; by apply/List.in_map_iff; exists (l, i). Qed.

Lemma U_ass  sc0 sc1 sc2 : U ((sc0 [+] sc1) [+] sc2) = U (sc0 [+] sc1 [+] sc2).
Proof. move=> /=. by rewrite -catA. Qed.

Lemma wellformed_wellformed_goto sc : wellformed sc -> wellformed_goto (U sc).
Proof.
elim => //.
- move=> x y l i i' [] [] ? ? [] [] ? ?; by subst.
- move=> x y l i i' [] [] ? ? [] [] ? ?; by subst.
- move=> p q Hinter Hwf_p Hwf_goto_p Hwf_q Hwf_goto_q l i i' /=.
  case/(List.in_app_or _ _ _) => i_p.
  + case/(List.in_app_or _ _ _) => i'_p.
    * by apply Hwf_goto_p with l.
    * exfalso.
      apply: (proj1 (Hinter l)); by [apply In_U_In_sdom with i | apply In_U_In_sdom with i'].
  + case/(List.in_app_or _ _ _) => i'_p.
    * exfalso.
      apply: (proj1 (Hinter l)); by [apply In_U_In_sdom with i' | apply In_U_In_sdom with i].
    * by apply Hwf_goto_q with l.
Qed.

(** We can now define the semantics of %\sgoto%#SGoto#. The inductive type below corresponds to Figure 2
   (%\figuretwo%#Natural semantics rules of SGoto#) in
   %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. Note that there is an
   additional constructor for error propagation. *)

(** printing >- %\ensuremath{\Yright}% *)

Reserved Notation "s >- p ---> t" (at level 70, no associativity).

Local Open Scope goto_scope.

Inductive exec_sgoto : scode -> lstate -> lstate -> Prop :=
| exec_sgoto_none : forall c, None >- c ---> None
| exec_sgoto_cmd0 : forall l c s s', c ||- Some (l, s) ---> s' -> Some (l, s) >- sC l c ---> s'
| exec_sgoto_jmp : forall l s l', l <> l' -> Some (l, s) >- sB l (jmp l') ---> Some (l', s)
| exec_sgoto_cjmp_true : forall l s b l',
  eval_b b s -> l <> l' -> Some (l, s) >- sB l (cjmp b l') ---> Some (l', s)
| exec_sgoto_cjmp_false : forall l s b l',
  ~~ eval_b b s -> Some (l, s) >- sB l (cjmp b l') ---> Some (S l, s)
| exec_sgoto_seq0 : forall sc1 sc2 l s s' s'', List.In l (sdom sc1) -> Some (l, s) >- sc1 ---> s' ->
  s' >- sc1 [+] sc2 ---> s'' -> Some (l, s) >- sc1 [+] sc2 ---> s''
| exec_sgoto_seq1 : forall sc1 sc2 l s s' s'', List.In l (sdom sc2) -> Some (l, s) >- sc2 ---> s' ->
  s' >- sc1 [+] sc2 ---> s'' -> Some (l, s) >- sc1 [+] sc2 ---> s''
| exec_sgoto_refl : forall sc l s, ~ List.In l (sdom sc) -> Some (l, s) >- sc ---> Some (l, s)
where "s >- p ---> t" := (exec_sgoto p s t) : sgoto_scope.

(** ** Properties *)

(** Inversion properties: *)

Lemma exec_sgoto_nil : forall c s, sdom c = nil -> s >- c ---> s.
Proof.
move=> c [[l s]|] H.
- apply exec_sgoto_refl => //; by rewrite H.
- by apply exec_sgoto_none.
Qed.

Local Open Scope while_cmd_scope.

Lemma exec_sgoto_inv_cmd' : forall c st st', st >- c ---> st' ->
  forall i l s l' s' l0, c = sC l0 i -> st = Some (l, s) -> st' = Some (l', s') ->
    l = l0 -> l' = S l /\ Some s -- i ---> Some s'.
Proof.
induction 1; intros => //.
- case: H0 => ? ?; case: H1 => ? ?; subst.
  inversion H; subst => //.
  split; [reflexivity | by apply while.exec_cmd0].
- case: H1 => ? ?; case: H2 => ? ?; subst.
  rewrite /= in H; tauto.
Qed.

Lemma exec_sgoto_inv_cmd c l s l' s' :
  Some (l, s) >- sC l c ---> Some (l', s') ->
  l' = S l /\ Some s -- c ---> Some s'.
Proof. move=> H. by eapply exec_sgoto_inv_cmd'; eauto. Qed.

Lemma exec_sgoto_inv_cjmp_true l s t l' s' :
  Some (l, s) >- sB l (cjmp t l') ---> s' ->
  eval_b t s -> s' = Some (l', s) /\ l' <> l.
Proof.
move=> H H'; inversion H; subst.
- split; [reflexivity | by auto].
- by rewrite H' in H5.
- rewrite /= in H4; tauto.
Qed.

Lemma exec_sgoto_inv_cjmp_false l s t l' s' :
  Some (l, s) >- sB l (cjmp t l') ---> s' ->
  ~~ eval_b t s -> s' = Some (S l, s).
Proof.
move=> H H'.
inversion H; subst => //.
by rewrite H5 in H'.
rewrite /= in H4; tauto.
Qed.

Lemma exec_sgoto_inv_jmp st l l' s' :
  Some (l, st) >- sB l (jmp l') ---> s' -> s' = Some (l', st) /\ l <> l'.
Proof. inversion 1; subst => //; rewrite /= in H4; tauto. Qed.

Lemma exec_sgoto_inv_seq0' sc st st'' : st >- sc ---> st'' ->
  forall l s, st = Some (l, s)  -> forall sc0 sc1, sc = sc0 [+] sc1 ->
    List.In l (sdom sc0) -> ~ List.In l (sdom sc1) ->
    exists st', Some (l, s) >- sc0 ---> st' /\ st' >- sc ---> st''.
Proof.
move=> H l s Hst sc0 sc1 Hsc HIn HIn'.
inversion H; intros; subst => //.
- case: H3 => ? ?; case: H4 => ? ?; subst; by exists s'.
- case: H3 => ? ?; case: H4 => ? ?; subst; tauto.
- case: H2 => X Y; subst.
  exfalso.
  apply H0 => /=; apply List.in_or_app; by left.
Qed.

Lemma exec_sgoto_inv_seq0 sc0 sc1 l s s'' :
  Some (l, s) >- sc0 [+] sc1 ---> s'' -> List.In l (sdom sc0) -> ~ List.In l (sdom sc1) ->
  exists s', Some (l, s) >- sc0 ---> s'  /\  s' >- sc0 [+] sc1 ---> s''.
Proof. move=> H HIn HIn'; by eapply (exec_sgoto_inv_seq0' _ _ _ H). Qed.

Lemma exec_sgoto_inv_seq1' sc st st'' : st >- sc ---> st'' ->
 forall l s, st = Some (l, s) -> forall sc0 sc1, sc = sc0 [+] sc1 ->
   List.In l (sdom sc1) -> ~ List.In l (sdom sc0) ->
   exists st', Some (l, s) >- sc1 ---> st' /\ st' >- sc ---> st''.
Proof.
move=> H l s Hst sc0 sc1 Hsc HIn HIn'.
inversion H; intros; subst => //.
- case: H4 => ? ?; case: H3 => ? ?; subst; tauto.
- case: H3 => ? ?; case: H4 => ? ?; subst; by exists s'.
- case: H2 => X Y; subst.
  exfalso.
  apply H0 => /=; apply List.in_or_app; by right.
Qed.

Lemma exec_sgoto_inv_seq1 sc0 sc1 l s s'' :
  Some (l, s) >- sc0 [+] sc1 ---> s'' -> List.In l (sdom sc1) -> ~ List.In l (sdom sc0) ->
  exists s', Some (l, s) >- sc1 ---> s'  /\  s' >- sc0 [+] sc1 ---> s''.
Proof. move=> H HIn HIn'; by eapply (exec_sgoto_inv_seq1' _ _ _ H). Qed.

Lemma exec_sgoto_inv_refl' sc st st' : st >- sc ---> st' ->
  forall l s, st = Some (l, s) -> ~ List.In l (sdom sc) -> st = st'.
Proof.
move=> H l ST H0 H1; inversion H; subst => //.
- case: H4 => X Y; subst; rewrite /= in H1; tauto.
- case: H4 => X Y; subst; rewrite /= in H1; tauto.
- case: H5 => X Y; subst; rewrite /= in H1; tauto.
- case: H4 => X Y; subst; rewrite /= in H1; tauto.
- case: H6 => X Y; subst.
  exfalso.
  apply H1 => /=; apply List.in_or_app; by left.
- case: H6 => X Y; subst.
  exfalso.
  apply H1 => /=; apply List.in_or_app; by right.
Qed.

Lemma exec_sgoto_inv_refl sc l s s' :
  Some (l, s) >- sc ---> s' -> ~ List.In l (sdom sc) -> Some (l, s) = s'.
Proof. move=> H H'; by apply exec_sgoto_inv_refl' with sc l s. Qed.

(** Lemma 4 (%\lemmafour%#Determinacy#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Lemma determinacy : forall c, wellformed c -> forall s s', s >- c ---> s' ->
  forall s'', s >- c ---> s'' -> s' = s''.
Proof.
induction 2; intros; subst.
- by inversion H0.
- inversion H1 => //; subst.
  + by apply (exec0_label_deter _ _ _ H0 _ H6).
  + rewrite /= in H6; tauto.
- apply exec_sgoto_inv_jmp in H1.
  by case: H1.
- apply exec_sgoto_inv_cjmp_true in H2; last by done.
  by case: H2.
- by apply exec_sgoto_inv_cjmp_false in H1.
- have X : s' >- sc1 [+] sc2 ---> s''0.
    have : ~ List.In l (sdom sc2) by apply wellformed_In_L with sc1.
    case/(exec_sgoto_inv_seq0 _ _ _ _ _ H1 H0) => st' [X1 X2].
    move: (IHexec_sgoto1 (wellformed_inv_L _ _ H) _ X1) => X ; by subst.
  by apply IHexec_sgoto2.
- have : s' >- sc1 [+] sc2 ---> s''0.
    have : ~ List.In l (sdom sc1) by apply wellformed_In_R with sc2.
    case/(exec_sgoto_inv_seq1 _ _ _ _ _ H1 H0) => st' [X1 X2].
    move: (IHexec_sgoto1 (wellformed_inv_R _ _ H) _ X1) => X; by subst.
  by apply IHexec_sgoto2.
- by apply exec_sgoto_inv_refl with sc.
Qed.

(** Intermediate lemma: *)

Lemma postlabels_cmd c l s l' s' : Some (l, s) >- sC l c ---> Some (l', s') -> l <> l'.
Proof.
inversion 1 => //; subst.
- by inversion H4.
- rewrite /= in H2; tauto.
Qed.

(** Lemma 5 (%\lemmafive%#Postlabels#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Lemma postlabels c s l' s' : s >- c ---> Some (l', s') -> ~ List.In l' (sdom c).
Proof.
move Hs' : (Some (l', s')) => st'.
move=> H; move: H l' s' Hs'.
induction 1; intros => //.
- subst.
  apply cmd0_labels in H.
  rewrite /=; tauto.
- case: Hs' => X Y /=; subst; tauto.
- case: Hs' => X Y /=; subst; tauto.
- case: Hs' => X Y /=; subst; omega.
- subst.
  destruct s' as [[l'_ s'] |].
  move: (IHexec_sgoto1 _ _ (refl_equal _)).
  by move: (IHexec_sgoto2 _ _ (refl_equal _)).
- by inversion H1.
- subst.
  destruct s' as [[l'_ s'] |].
  move: (IHexec_sgoto1 _ _ (refl_equal _)).
  by move: (IHexec_sgoto2 _ _ (refl_equal _)).
- by inversion H1.
- case: Hs' => ? ?; by subst.
Qed.

(** Theorem 6 (%\theoremsix%#Preservation of evaluations as stuck reduction sequences#) in
   %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. *)

Lemma preservation sc s s' : s >- sc ---> s' -> U sc ||- s --->* s'.
Proof.
elim => //; clear sc s s'.
- move=> c; by apply redseqs_refl.
- move=> p c st [[l' s']|] Hc.
  + eapply redseqs_trans; first by apply redseqs_refl.
    eapply exec_goto_cmd0; eauto; rewrite /=; by left.
  + eapply redseqs_trans; first by eapply redseqs_refl.
    eapply exec_goto_cmd0_err; eauto; rewrite /=; by left.
- move=> p st p' Hpp'.
  eapply redseqs_trans; first by apply redseqs_refl.
  eapply exec_goto_branch; eauto.
  * rewrite /=; left; reflexivity.
  * by constructor.
- move=> p s b p' Hb Hpp'.
  eapply redseqs_trans; first by apply redseqs_refl.
  eapply exec_goto_branch; eauto.
  * rewrite /=; left; reflexivity.
  * by constructor.
- move=> p s b p' Hb.
  eapply redseqs_trans; first by apply redseqs_refl.
  eapply exec_goto_branch; eauto.
  * rewrite /=; left; reflexivity.
  * constructor; by apply/negP.
- move=> sc1 sc2 p st [ [l' s'] | ] s'' HIn1 Hsc1 IHsc1 H IHsc2.
  + apply redseqs_transitivity with (Some (l',s')) => //=.
    apply redseqs_extension_right; by eapply IHsc1; eauto.
  + apply redseqs_transitivity with None; last by done.
    apply redseqs_extension_right; by eapply IHsc1; eauto.
- move=> sc1 sc2 p st [[l' s']|] s'' HIn1 Hsc1 IHsc1 H IHsc2.
  + apply redseqs_transitivity with (Some (l',s')); last by done.
    apply redseqs_extension_left; by eapply IHsc1; eauto.
  + apply redseqs_transitivity with None; last by done.
    apply redseqs_extension_left; by eapply IHsc1; eauto.
- move=> *; by apply redseqs_refl.
Qed.

(* Inversion Lemmas *)

Lemma redseq_trans_inv c n st st' : wellformed_goto c ->
  redseq c n st st' -> forall l s l' s' sc1 sc2,
    st = Some (l, s) -> st' = Some (l', s') -> c = U sc1 ++ U sc2 ->
    List.In l (sdom sc1) -> ~ List.In l' (sdom (sc1 [+] sc2)) ->
    (exists k, exists lk, exists sk, 0 < k <= n /\ ~ List.In lk (sdom sc1) /\
      redseq (U sc1) k st (Some (lk, sk)) /\ redseq c (n - k) (Some (lk, sk)) st').
Proof.
move=> Hwf; induction 1.
- move=> l st l' st' sc1 sc2 H H0 H1 H2 H3.
  destruct s as [[l_ s]|]; last by done.
  case: H => X Y; subst l_ st. case: H0 => X Y; subst l' st'.
  have : List.In l (sdom (sc1 [+] sc2)). by rewrite /=; apply List.in_or_app; auto.
  contradiction.
- move=> l st l' st' sc1 sc2 H1 H2 H3 H4 H5.
  destruct s' as [[l_ st_]|].
  + case: (lbl_sdom_dec sc1 l_) => l__sc1.
    + case: (IHredseq _ _ _ _ _ _ (refl_equal _) H2 H3 l__sc1 H5) => k [lk [stk [k_n [H11 [H7 H9]]]]].
      exists (S k), lk, stk; split; first by rewrite /=; case/andP : k_n => _.
      split; first by done.
      split; last by done.
      apply more_red with (Some (l_, st_)) => //.
      rewrite H1.
      apply exec_goto_contraction_right with (c2 := U sc2).
      * by rewrite -H3.
      * by rewrite -H3 -H1.
      * by rewrite -sdom_dom.
    + exists 1, l_, st_; split => //.
      split; first by done.
      split.
      * apply more_red with (Some (l_, st_)).
        - rewrite H1.
          apply exec_goto_contraction_right with (c2 := U sc2).
          + by rewrite -H3.
          + by rewrite -H3 -H1.
          + by rewrite -sdom_dom.
        - by apply zero_red.
      * by rewrite /= subSS subn0.
  + inversion H0; subst => //.
    inversion H6; by subst.
Qed.

Lemma redseq_trans_inv2 c n st st' : wellformed_goto c ->
  redseq c n st st' -> forall l s l' s' sc1 sc2,
    st = Some (l, s) -> st' = Some (l', s') -> c = U sc1 ++ U sc2 ->
    List.In l (sdom sc2) -> ~ List.In l' (sdom (sc1 [+] sc2)) ->
    (exists k, exists lk, exists sk, 0 < k <= n /\ ~ List.In lk (sdom sc2) /\
      redseq (U sc2) k st (Some (lk, sk)) /\ redseq c (n - k) (Some (lk, sk)) st').
Proof.
move=> Hwf; induction 1.
- move=> l st l' st' sc1 sc2 H H0 H1 H2 H3.
  destruct s as [[l0 s]|]; last by done.
  case: H => X Y; subst l0 st. case: H0 => X Y; subst l' st'.
  have : List.In l (sdom (sc1 [+] sc2)). by rewrite /=; apply List.in_or_app; auto.
  contradiction.
- move=> l st l' st' sc1 sc2 H1 H2 H3 H4 H5.
  destruct s' as [[l_ st_]|].
  + elim: (lbl_sdom_dec sc2 l_) => l__sc2.
    + case: (IHredseq _ _ _ _ _ _ (refl_equal _) H2 H3 l__sc2 H5) => k [lk [stk [k_n [H11 [H7 H9]]]]].
      exists (S k), lk, stk; split; first by rewrite /=; case/andP : k_n => _.
      split; first by done.
      split; last by done.
      apply more_red with (Some (l_,st_)) => //.
      rewrite H1.
      apply exec_goto_contraction_left with (c1 := U sc1).
      * by rewrite -H3.
      * by rewrite -H3 -H1.
      * by rewrite -sdom_dom.
    + exists 1, l_, st_; split => //.
      split; first by done.
      split.
      * apply more_red with (Some (l_, st_)).
        - rewrite H1.
          apply exec_goto_contraction_left with (c1 := U sc1).
          + by rewrite -H3.
          + by rewrite -H3 -H1.
          + by rewrite -sdom_dom.
        - by apply zero_red.
      * by rewrite /= subSS subn0.
  + inversion H0; subst => //.
    inversion H6; by subst.
Qed.

Lemma redseq_sC_inv_none k c st st' : redseq c k st st' ->
  forall l s i, st = Some (l, s) -> st' = None ->
    c = (l, C i) :: nil -> i ||- st ---> st'.
Proof.
induction 1.
- move=> l s0 i Hs Hs' Hc; by subst.
- move=> l s0 i Hs Hs'' Hc; subst.
  inversion H; subst.
  + case: H4 => //; case => X; subst.
    inversion H0; subst.
    inversion H1; subst.
     * case: H4 => //; case=> X Y; subst.
       by apply cmd0_labels in H6.
     * case: H4 => //; case => X Y; subst.
       by apply cmd0_labels in H6.
     * by case: H4.
   + case: H4 => //; case=> X; by subst.
   + by case: H4.
Qed.

(** Theorem 7 (%\theoremseven%#Reflection of stuck reduction sequences as evaluations#) in
   %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. Nested induction whose inner induction
   is noetherian. *)

Lemma reflection_of_stuck_redseq : forall sc k l s l' s',
  wellformed_goto (U sc) -> redseq (U sc) k (Some (l, s)) (Some (l', s')) ->
  ~ List.In l' (sdom sc) -> Some (l, s) >- sc ---> Some (l', s').
Proof.
induction sc.
- (* sO *) move=> k l s l' s' Hwf /= H _.
  case/redseq_nil : H => <- <-; by apply exec_sgoto_refl.
- (* commands *) move=> k l0 s l' s' Hwf H Hl'.
  have {}Hl' : l <> l' by rewrite /= in Hl'; tauto.
  case: (label_dec l l0) => l_l0.
  + (* case where the command will be executed *) subst.
    by apply exec_sgoto_cmd0, (redseq_sC_inv _ _ _ _ H l0 s l' s' c).
  + (* case where the command will not be executed *)
    move: (redseq_sC_refl _ _ _ _ H l0 s l' s' l c erefl erefl erefl l_l0).
    case=> ? ?; subst.
    apply exec_sgoto_refl => /=; tauto.
- (* branches *) move=> k l0 s l' s' Hwf H Hl'.
  have {}Hl' : l <> l' by rewrite /= in Hl'; tauto.
  destruct b.
  + case (label_dec l l0) => l_l0.
    * subst l0.
      case (label_dec l l1) => l_l1.
      - subst l1.
        move: (redseq_self_jump k l s l' s' Hl'); tauto.
      - inversion H; subst.
        + tauto.
        + inversion H0; subst.
          * by case: H5.
          * by case: H5.
          * rewrite /= in H5.
            case: H5 => //; case=> ?; subst.
            inversion H7; subst.
            case: (redseq_out_of_domain_jump _ _ _ _ _ _ _ l_l1 H1) => l1_l' st_st'; subst.
            by constructor.
    * case: (redseq_out_of_domain_jump _ _ _ _ _ _ _ l_l0 H) => l0_l' st_st'; subst.
      apply exec_sgoto_refl => /=; tauto.
  + case (label_dec l l0) => l_l0.
    * subst l0.
      - case/boolP : (eval_b e s) => e_s.
        + case (label_dec l l1) => l_l1.
          * subst l1.
            move: (redseq_self_cjmp k e _ s _ s' Hl' e_s); tauto.
          * inversion H; subst => //.
            inversion H; subst.
            inversion H3; subst.
            - by case: H7.
            - by case: H7.
            - rewrite /= in H7; case: H7 => //; case=> ?; subst.
              inversion H9; subst => //.
              case: (redseq_out_of_domain_cjmp _ _ _ _ _ _ _ _ l_l1 H4) => l1_l' Hst'; subst.
              by constructor.
        + inversion H; subst => //.
          inversion H0; subst.
          * by case: H5.
          * by case: H5.
          * rewrite /= in H5; case: H5 => //; case=> Hj; subst.
            inversion H7; subst => //.
            - by move/negP : e_s.
            - case: (redseq_out_of_domain_cjmp _ _ _ _ _ _ _ _ (n_Sn l) H1) => l_l' Hst'; subst.
              by constructor; auto.
    * case: (redseq_out_of_domain_cjmp _ _ _ _ _ _ _ _ l_l0 H) => l0_l' st_st'; subst.
      apply exec_sgoto_refl => /=; tauto.
- (* case for sS ([+]) *) move=> k.
  apply lt_wf_ind with (P := fun k => forall l s l' s',
      wellformed_goto (U (sc1 [+] sc2)) ->
      redseq (U (sc1 [+] sc2)) k (Some (l, s)) (Some (l', s')) ->
      ~ List.In l' (sdom (sc1 [+] sc2)) ->
      Some (l, s) >- sc1 [+] sc2 ---> Some (l', s')).
  move=> n IH l s l' s' Hwf H HIn.
  have [Hl|[Hl|Hl]] : List.In l (sdom sc1) \/ List.In l (sdom sc2) \/ ~ List.In l (sdom (sc1 [+] sc2)).
    case: (lbl_sdom_dec (sc1 [+] sc2) l) => /=.
    move/(List.in_app_or _ _ _); tauto.
    by auto.
  + (* case List.In l (sdom prg1) *) have [j [lj [sj [/andP [Hj j_n] [lj_sc1 [H1 H2]]]]]] :
      exists k lk sk, 0 < k <= n /\ ~ List.In lk (sdom sc1) /\
          redseq (U sc1) k (Some (l, s)) (Some (lk, sk)) /\
          redseq (U (sc1 [+] sc2)) (n - k) (Some (lk, sk)) (Some (l', s')).
      eapply (redseq_trans_inv _ _ _ _ Hwf H); eauto.
      by rewrite /=; auto.
    apply exec_sgoto_seq0 with (Some (lj, sj)) => //.
    * eapply IHsc1; eauto.
      move: (wellformed_goto_app _ Hwf (U sc1) (U sc2)) => /=; tauto.
    * eapply IH; eauto.
      apply/ltP; by rewrite -ltnS -subSn // -{2}(subn0 n.+1) ltn_sub2l.
  + (* case List.In l (sdom prg2) *) (* similar to above *) have [j [lj [sj [/andP [Hj j_n] [lj_sc2 [H1 H2]]]]]] :
      exists k lk sk, 0 < k <= n /\ ~ List.In lk (sdom sc2) /\
          redseq (U sc2) k (Some (l, s)) (Some (lk, sk)) /\
          redseq (U (sc1 [+] sc2)) (n - k) (Some (lk, sk)) (Some (l', s')).
      eapply (redseq_trans_inv2 _ _ _ _ Hwf H); eauto.
      by rewrite /=; auto.
    apply exec_sgoto_seq1 with (Some (lj, sj)) => //.
    * eapply IHsc2; eauto.
      move: (wellformed_goto_app _ Hwf (U sc1) (U sc2)) => /=; tauto.
    * eapply IH; eauto.
      apply/ltP; by rewrite -ltnS -subSn // -{2}(subn0 n.+1) ltn_sub2l.
  + (* case ~ List.In l (sdom prg) *) move: (redseq_inv_refl' _ _ _ _ H _ _ (refl_equal _)) => X.
    rewrite X; last by rewrite -sdom_dom.
    by apply exec_sgoto_refl.
Qed.

(** ** Semantic Equivalence *)

Definition sem_equ sc0 sc1 := forall s s', Some s >- sc0 ---> Some s' <-> Some s >- sc1 ---> Some s'.

(** printing ~= %\ensuremath{\cong}% *)

Notation "c '~=' d" := (sem_equ c d) (at level 70, right associativity) : sgoto_scope.

(** Theorem 8 (%\theoremeight%#Neutrality wrt phrase structure#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Lemma neutrality sc0 sc1 : wellformed sc0 -> U sc0 = U sc1 ->
  forall s s', Some s >- sc0 ---> Some s' -> Some s >- sc1 ---> Some s'.
Proof.
move=> Hwf Hsc [l s] [l' s'] H.
move: (preservation _ _ _ H) => H'.
rewrite Hsc in H'.
move: (postlabels _ _ _ _ H) => H''.
case: (red_seqs_red_seq _ _ _ H') => n H'''.
eapply reflection_of_stuck_redseq; eauto.
- rewrite -Hsc; by apply wellformed_wellformed_goto.
- contradict H''.
  by rewrite 2!sdom_dom ?Hsc in H'' *.
Qed.

(** Corollary 9 (%\corollarynine%#Partial commutative monoidal structure#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. *)

Lemma sem_equ_ass sc0 sc1 sc2 : wellformed ((sc0 [+] sc1) [+] sc2) ->
  (sc0 [+] sc1) [+] sc2 ~= sc0 [+] (sc1 [+] sc2).
Proof.
move=> Hwf s s'; split => H.
- apply neutrality with ((sc0 [+] sc1) [+] sc2) => //.
  by apply U_ass.
- apply neutrality with (sc0 [+] sc1 [+] sc2) => //.
  + by apply wellformed_ass.
  + by rewrite U_ass.
Qed.

Lemma sem_equ_neu sc : wellformed sc -> sc [+] sO ~= sc.
Proof.
move=> H [l s] [l' s']; split => H'.
- apply neutrality with (sc [+] sO) => //.
  + by apply wellformed_neu.
  + by rewrite /= cats0.
- case: (lbl_sdom_dec sc l) => X.
  + eapply exec_sgoto_seq0; eauto.
    apply exec_sgoto_refl.
    move: (postlabels _ _ _ _ H') => Y /=.
    by rewrite cats0.
  + apply exec_sgoto_inv_refl in H' => //.
    case : H'=> ? ?; subst.
    apply exec_sgoto_refl.
    by rewrite /= cats0.
Qed.

Lemma sem_equ_com' sc sc' sc0 sc1 : sc = sc0 [+] sc1 ->
  sc' = sc1 [+] sc0 -> forall s s', s >- sc ---> s'  ->  s >- sc' ---> s'.
Proof.
move=> Hsc Hsc' s s' H; move: sc' sc0 sc1 Hsc Hsc'.
elim: H => [ * |//|//|//|//|
  s1 s2 l s0 s'0 s'' ls1 H1 IH1 H2 IH2 sc' sc0 sc1|
  s1 s2 l s0 s'0 s'' ls1 H1 IH1 H2 IH2 sc' sc0 sc1|
  sc0 l s0 ls0 sc' sc1 sc2].
- by constructor.
- move=> [] <- <- ->; by eapply exec_sgoto_seq1; eauto.
- move=> [] <- <- ->; by eapply exec_sgoto_seq0; eauto.
- move=> ?; subst sc0 => ->.
  apply exec_sgoto_refl.
  rewrite /= in ls0 *.
  contradict ls0.
  apply List.in_or_app; move: (List.in_app_or _ _ _ ls0); tauto.
Qed.

(** Interestingly, commutativity does not require well-formedness: *)

Lemma sem_equ_com sc0 sc1 : sc0 [+] sc1 ~= sc1 [+] sc0.
Proof. move=> s s'; split => H; by eapply sem_equ_com'; eauto. Qed.

End SGoto.

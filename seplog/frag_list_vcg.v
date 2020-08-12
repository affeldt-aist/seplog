(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Bool List ZArith EqNat.
From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import bipl seplog.
Require Import frag_list_entail frag_list_triple.

Require Import expr_b_dp.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.

Declare Scope frag_list_vc_scope.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.

Inductive cmd'' : Type :=
| skip'' : cmd''
| assign'' : var.v -> expr -> cmd''
| lookup'' : var.v -> expr -> cmd''
| mutation'' : expr -> expr -> cmd''
| malloc'' : var.v -> expr -> cmd''
| free'' : expr -> cmd''
| while'' : expr_b -> Assrt -> cmd'' -> cmd''
| seq'' : cmd'' -> cmd'' -> cmd''
| ifte'' : expr_b -> cmd'' -> cmd'' -> cmd''.

Notation "x <- e" := (assign'' x e) (at level 80) : frag_list_vc_scope.
Notation "x '<-*' e" := (lookup'' x e) (at level 80) : frag_list_vc_scope.
Notation "e '*<-' f" := (mutation'' e f) (at level 80) : frag_list_vc_scope.
Notation "x '<-malloc' e" := (malloc'' x e) (at level 80) : frag_list_vc_scope.
Notation "c ; d" := (seq'' c d) (at level 81, right associativity) : frag_list_vc_scope.
Notation "'ifte' a 'thendo' x 'elsedo' y" := (ifte'' a x y) (at level 80) : frag_list_vc_scope.

Fixpoint proj_cmd (c' : cmd'') : @while.cmd cmd0 expr_b :=
  match c' with
    | skip'' => skip
    | assign'' x e => x <- e
    | lookup'' x e => x <-* e
    | mutation'' e f => e *<- f
    | malloc'' x e => x <-malloc e
    | free'' e => free e
    | while'' b Q c''  => While b {{ proj_cmd c'' }}
    | seq'' c1 c2 => while.seq (proj_cmd c1) (proj_cmd c2)
    | ifte'' b c1 c2 => If b Then proj_cmd c1 Else proj_cmd c2
  end.

Fixpoint Assrt_and_expr_b (A: Assrt) (b: expr_b) {struct A} : Assrt :=
  match A with
    | nil => nil
    | (pi, sig) :: tl => (pi \&& b, sig) :: Assrt_and_expr_b tl b
  end.

Lemma Assrt_and_eval_b_Prop: forall A b s h,
  Assrt_interp (Assrt_and_expr_b A b) s h -> (Assrt_interp A s h /\ eval_b b s).
Proof.
elim=> // [[pi1 sig1] tl] IH b s h /= [].
- case. case/andP => H2 H3 H1; by simpl; auto.
- case/IH; by auto.
Qed.

Lemma Assrt_and_eval_b_Prop': forall A b s h,
  (Assrt_interp A s h /\ eval_b b s) -> Assrt_interp (Assrt_and_expr_b A b) s h.
Proof.
induction A; simpl; intros.
inversion_clear H.
contradiction.
destruct a as [p s0].
simpl.
inversion_clear H.
inversion_clear H0.
simpl in H.
inversion_clear H.
left.
split; auto.
destruct (eval_b p s); destruct (eval_b b s); try discriminate; auto.
right.
eapply IHA.
tauto.
Qed.

(* input : a program with invariants and a post-condition
   output : the pre-condition and a list of "triples" (actually, Assrt -> wpAssrt) *)

Fixpoint vcg (c : cmd'') (Q : wpAssrt) {struct c} : option (wpAssrt * (list (Assrt * wpAssrt))) :=
  match c with
    | skip'' => Some (Q, nil)
    | assign'' x e => Some (wpSubst ((x,e)::nil) Q, nil)
    | lookup'' x e => Some (wpLookup x e Q, nil)
    | mutation'' e f => Some (wpMutation e f Q, nil)
    | seq'' c1 c2 =>
      match vcg c2 Q with
        | None => None
        | Some (Q2, l2) =>
          match vcg c1 Q2 with
            | None => None
            | Some (Q1, l1) =>
              Some (Q1, l1 ++ l2)
          end
      end
    | ifte'' b c1 c2 =>
      match vcg c2 Q with
        | None => None
        | Some (Q2,l2) =>
          match vcg c1 Q with
            | None => None
            | Some (Q1,l1) => Some (wpIf b Q1 Q2, (l1 ++ l2))
          end
      end
    | while'' b Inv c' =>
      match vcg c' (wpElt Inv) with
        | None => None
        | Some (Q',l') => Some (wpElt Inv, (* post-condition courante *)
          (Assrt_and_expr_b Inv (neg_b b), Q) (* Inv /\ ~ b => Q *)
          :: (Assrt_and_expr_b Inv b, Q') (* Inv /\ b => Q' (wp c' Inv) *)
          :: l')
      end
    | _ => None
  end.

Lemma vcg_None_is_None: forall c, wp_frag None c = None.
Proof.
induction c; simpl; auto.
case c; auto.
rewrite IHc2; auto.
rewrite IHc1; auto.
Qed.

Lemma vcg_correct  : forall c Q Q' l,  vcg c Q = Some (Q', l) ->
  (forall A L, In (A, L) l ->
    (Assrt_interp A ===> wpAssrt_interp L)) ->
  {{ wpAssrt_interp Q' }} (proj_cmd c) {{ wpAssrt_interp Q }}.
Proof.
induction c; simpl; intros; try discriminate.
- injection H; clear H; intros; subst Q' l.
  by apply while.hoare_hoare0, hoare0_skip.
- injection H; clear H; intros; subst Q' l.
  simpl.
  by apply while.hoare_hoare0, hoare0_assign.
- injection H; clear H; intros; subst Q' l.
  simpl.
  by apply hoare_lookup_back.
- injection H; clear H; intros; subst Q' l.
  simpl.
  by apply hoare_mutation_backwards.
- move: (IHc (wpElt a)) => H1.
  destruct (vcg c (wpElt a)); try discriminate.
  destruct p.
  injection H; clear H; intros; subst Q' l.
  simpl.
  eapply hoare_prop_m.hoare_weak; [idtac | eapply while.hoare_while].
    rewrite /while.entails in H0; rewrite /while.entails; intros.
    eapply H0.
    simpl; left; intuition.
    by apply Assrt_and_eval_b_Prop'.
  simpl in H1.
  apply hoare_prop_m.hoare_stren with (wpAssrt_interp w).
  red; intros.
  red in H0; eapply H0.
  simpl; right; left; intuition.
  simpl.
  by apply Assrt_and_eval_b_Prop'.
  eapply H1.
  reflexivity.
  red; intros.
  red in H0; eapply H0.
  simpl; right; right; apply H.
  assumption.
- move: (IHc2 Q) => H1.
  destruct (vcg c2 Q); try discriminate.
  destruct p.
  move: (IHc1 w) => H2.
  destruct (vcg c1 w); try discriminate.
  destruct p.
  case : H => ? ?; subst Q' l.
  eapply while.hoare_seq.
  eapply H2.
  reflexivity.
  red; intros.
  red in H0; eapply H0.
  eapply in_or_app; left; by apply H.
  assumption.
  clear H2.
  eapply H1.
  reflexivity.
  red; intros.
  red in H0; eapply H0.
  eapply in_or_app; right; by apply H.
  assumption.
- move: (IHc2 Q) => H1.
  destruct (vcg c2 Q); try discriminate.
  destruct p as [Q2].
  generalize (IHc1 Q); intros.
  destruct (vcg c1 Q); try discriminate.
  destruct p as [Q1].
  case : H => ? ?; subst Q' l.
  apply while.hoare_ifte.
  eapply hoare_prop_m.hoare_stren; [idtac | eapply H2; [intuition | idtac] ].
  simpl.
  red; intros.
  case: H => H3 H4.
  case: H3 => H H5.
  by apply H.
  intros.
  apply H0.
  apply in_or_app; by left.
  eapply hoare_prop_m.hoare_stren; [idtac | eapply H1; [intuition | idtac] ].
  simpl.
  red; intros.
  case: H => H3 H4.
  case: H3 => H H5.
  by apply H5.
  intros.
  apply H0.
  apply in_or_app; by right.
Qed.

Fixpoint triple_transformations (l : list (Assrt * wpAssrt)) : option (list ((expr_b * Sigma) * wpAssrt)) :=
  match l with
    | nil => Some nil
    | (A, L) :: tl =>
      match triple_transformation A L with
        | Some l =>
          match triple_transformations tl with
            | Some l' => Some (l ++ l')
            | None => None
          end
        | None => None
      end
  end.

Lemma triple_transformations_correct: forall l,
  triple_transformations l = Some nil ->
  forall A L, In (A, L) l -> Assrt_interp A ===> wpAssrt_interp L.
Proof.
induction l.
  simpl; red; intros; contradiction.
  rewrite /= /while.entails => H A L H0 s h H1.
  inversion_clear H0.
  + destruct a.
    generalize (triple_transformation_correct A L); intros.
    red in H0; apply H0.
    injection H2; intros; subst a w.
    destruct (triple_transformation A L); destruct (triple_transformations l); simpl in H; try discriminate.
    destruct l0; destruct l1; try discriminate.
    reflexivity.
    assumption.
  + destruct a.
    destruct (triple_transformation a w); destruct (triple_transformations l); simpl in H; try discriminate.
    destruct l1; destruct l0; try discriminate.
    red in IHl; eapply IHl; auto.
    by apply H2.
    assumption.
Qed.

(* entry point *)
Definition bigtoe_fun (c : cmd'') (P Q: Assrt): option (list ((expr_b * Sigma) * wpAssrt)) :=
  match vcg c (wpElt Q) with
    | None => None
    | Some (Q', l) =>
      match triple_transformation P Q' with
        | Some l' =>
          match triple_transformations l with
            | Some l'' => Some (l' ++ l'')
            | None => None
          end
        | None => None
      end
  end.

Lemma bigtoe_fun_correct: forall P Q c, bigtoe_fun c P Q = Some nil ->
  {{ Assrt_interp P }} proj_cmd c {{ Assrt_interp Q }}.
Proof.
intros.
unfold bigtoe_fun in H.
generalize (vcg_correct c (wpElt Q)); intros.
destruct (vcg c (wpElt Q)); try discriminate.
destruct p.
generalize (triple_transformation_correct P w); intros.
generalize (triple_transformations_correct l); intros.
destruct (triple_transformation P w); destruct (triple_transformations l); simpl in H; try discriminate.
destruct l0; destruct l1; try discriminate.
simpl in H0.
eapply hoare_prop_m.hoare_stren; [idtac | eapply H0].
eapply H1; auto.
reflexivity.
by apply H2.
Qed.

Fixpoint resolve_list_Assrt_wpAssrt2 ( l: list (Assrt * wpAssrt)) : bool :=
  match l with
    | nil => true
    | (A, L) :: tl => triple_transformation2 A L && resolve_list_Assrt_wpAssrt2 tl
  end.

Lemma resolve_list_Assrt_wpAssrt2_correct: forall l,
  resolve_list_Assrt_wpAssrt2 l ->
  forall A L, In (A, L) l -> Assrt_interp A ===> wpAssrt_interp L.
Proof.
induction l.
  simpl; red; intros; contradiction.
  rewrite /= /while.entails => H A L H0 s h H1.
  inversion_clear H0.
  - destruct a.
    generalize (triple_transformation2_correct A L); intros.
    red in H0; apply H0.
    injection H2; intros; subst a w.
    destruct (triple_transformation2 A L); destruct (resolve_list_Assrt_wpAssrt2 l); simpl in H; try discriminate.
    done.
    assumption.
  - destruct a.
    destruct (triple_transformation2 a w); destruct (resolve_list_Assrt_wpAssrt2 l); simpl in H; try discriminate.
    red in IHl; eapply IHl; auto.
    by apply H2.
    assumption.
Qed.

Definition frag2_hoare (c : cmd'') (P Q : Assrt) : bool :=
  match vcg c (wpElt Q) with
    | None => false
    | Some (Q',l) => triple_transformation2 P Q' && resolve_list_Assrt_wpAssrt2 l
  end.

Lemma frag2_hoare_correct : forall P Q c, frag2_hoare c P Q ->
  {{ Assrt_interp P }} (proj_cmd c) {{ Assrt_interp Q }}.
Proof.
intros.
unfold frag2_hoare in H.
generalize (vcg_correct c (wpElt Q)); intros.
destruct (vcg c (wpElt Q)); try discriminate.
destruct p.
move: (triple_transformation2_correct P w) => H1.
move: (resolve_list_Assrt_wpAssrt2_correct l) => H2.
destruct (triple_transformation2 P w); destruct (resolve_list_Assrt_wpAssrt2 l); simpl in H; try discriminate.
simpl in H0.
eapply hoare_prop_m.hoare_stren; [idtac | eapply H0].
- by apply H1.
- reflexivity.
- by apply H2.
Qed.

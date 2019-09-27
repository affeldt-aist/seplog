(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrnat_ext ZArith_ext.
Require Import bipl seplog.

Require Import expr_b_dp.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.

(** tactics to make proofs more readable (sic) *)

Ltac Step R :=
  match goal with
    | |- hoare_m.hoare _ _ _ =>
      rewrite /hoare_m.hoare /hoare_m.store /hoare_m.heap
        /hoare_m.cmd0 /hoare_m.expr_b /hoare_m.eval_b /hoare_m.hoare0
    | _ => idtac
  end ;
  match goal with
    | id: {{ ?P' }} ?c {{ ?Q' }} |- {{ ?P }} ?c {{ ?Q }} => eapply while.hoare_conseq; [idtac | idtac | apply id]

    | id: {{ ?P' }} ?c {{ ?Q' }} |- {{ ?P }} ?c; ?c' {{ ?Q }} =>
      eapply hoare_prop_m.hoare_stren_seq; [apply id | idtac | idtac]

    | |- {{?P}} cmd_cmd0_coercion_redefined (?x <- ?e) {{?Q}} =>
      eapply hoare_assign'; rewrite /while.entails

    | |- {{?P}} cmd_cmd0_coercion_redefined (?x <- ?e) ; ?c {{?Q}} =>
      eapply hoare_assign with R; [rewrite /while.entails; intros | idtac]

    | |- {{?P}} cmd_cmd0_coercion_redefined (?x <-* ?e) {{?Q}} => eapply hoare_lookup_back'
    | |- {{?P}} cmd_cmd0_coercion_redefined (?x <-* ?e) ; ?c {{?Q}} =>
      eapply hoare_lookup_back'' with R; [rewrite /while.entails; intros | idtac]
    | |- {{?P}} cmd_cmd0_coercion_redefined (?e1 *<- ?e2) {{?Q}} => eapply hoare_mutation_backwards'
    | |- {{?P}} cmd_cmd0_coercion_redefined (?e1 *<- ?e2) ; ?c {{?Q}} =>
      eapply hoare_mutation_backwards'' with R; [rewrite /while.entails; intros | idtac]
    | |- {{?P}} while.while ?b ?c1 {{?Q}} => eapply hoare_prop_m.hoare_while_invariant with R
    | |- {{?P}} while.while ?b ?c1 ; ?c2 {{?Q}} =>
      eapply hoare_prop_m.hoare_while_invariant_seq with R; [rewrite /while.entails; intros | idtac | idtac]
    | |- {{?P}} cmd_cmd0_coercion_redefined skip {{?Q}} =>  eapply hoare_skip'
    | |- {{?P}} If ?b Then ?c1 Else ?c2 {{?Q}} => eapply while.hoare_ifte
    | |- {{?P}} (If ?b Then ?c1 Else ?c2); ?c' {{?Q}} => apply while.hoare_seq with R; [eapply while.hoare_ifte; [idtac| idtac] | idtac]
    | |- {{?P}} ?c1; ?c2 {{?Q}} => apply while.hoare_seq with R; [idtac| idtac]
  end.

Ltac Frame_rule_pre A :=
  match goal with
    | |- {{?a1 **  A }} ?c {{?Q}} => idtac
    | |- {{ A ** ?a1}} ?c {{?Q}} => rewrite (assert_m.conCE A a1)
    | |- {{ (?a1 ** ?a2) ** ?a3}} ?c {{?Q}} => rewrite (assert_m.conAE a2 a1 a3); Frame_rule_pre A
    | |- {{ ?a1 ** ?a2}} ?c {{?Q}} => rewrite (assert_m.conCE a1 a2); Frame_rule_pre A
  end.

Ltac Frame_rule_post A :=
  match goal with
    | |- {{?P}} ?c {{?a1 **  A }} => idtac
    | |- {{?P}} ?c {{ A ** ?a1}} => rewrite (assert_m.conCE A a1)
    | |- {{?P}} ?c {{ (?a1 ** ?a2) ** ?a3}} => rewrite (assert_m.conAE a2 a1 a3); Frame_rule_post A
    | |- {{?P}} ?c {{ ?a1 ** ?a2}} => rewrite (assert_m.conCE a1 a2); Frame_rule_post A
  end.

Ltac Frame_rule A :=
  match goal with
    | |- hoare_m.hoare _ _ _ =>
      rewrite /hoare_m.hoare /hoare_m.store /hoare_m.heap
        /hoare_m.cmd0 /hoare_m.expr_b /hoare_m.eval_b /hoare_m.hoare0
    | _ => idtac
  end ;
  match goal with
    | |- {{?P}} ?c {{?Q}} =>
      (Frame_rule_pre  A); (Frame_rule_post A);
      eapply frame_rule_R
  end.

(* heap-list related *)

Fixpoint get_endl (l : list (nat * bool)) (startl : nat) : nat :=
   match l with
     | nil => startl
     | (b, c) :: tl => get_endl tl (startl + 2 + b)
   end.

Lemma get_endl_app : forall a b startl, get_endl (a ++ b) startl = get_endl b (get_endl a startl).
Proof. elim=> //; move=> [h1 h2] tl IH b startl /=. by rewrite IH. Qed.

Local Close Scope Z_scope.

Lemma get_endl_gt : forall l startl, startl <= get_endl l startl.
Proof.
elim=> //; move=> [h1 h2] tl IH startl /=.
eapply leq_trans; last by apply IH. ssromega.
Qed.

Fixpoint In_hl (l : list (nat * bool)) (block : nat * nat * bool) (startp : nat) { struct l } : Prop :=
  match l with
    | nil => False
    | (size , stat) :: tl =>
      match block with
        | (adr, sz, st) =>
          if ((startp == adr) && (st == stat)) && (size == sz) then
            True
            else
            In_hl tl block (get_endl ((size, stat) :: nil) startp)
      end
  end.

Lemma In_hl_app_or : forall l1 l2 a b c startp,
  In_hl (l1 ++ l2) (a, b, c) startp ->
  (In_hl l1 (a, b, c) startp \/ In_hl l2 (a, b, c) (get_endl l1 startp)).
Proof.
elim; first by auto.
move=> [h1 h2] tl IH l2 a b c startp /=.
set t := _ && _.
destruct t; by auto.
Qed.

Lemma In_hl_or_app : forall l1 l2 a b c startp,
  (In_hl l1 (a, b, c) startp \/ In_hl l2 (a, b, c) (get_endl l1 startp)) ->
  In_hl (l1 ++ l2) (a, b, c) startp.
Proof.
elim.
by move=> l2 a b c startp [].
move=> [h1 h2] tl IH l2 a b c startp /=.
set t := _ && _.
by destruct t; auto.
Qed.

(** constant used in hmInit and hmAlloc *)
Definition Allocated := cst_e 0%Z.

(** constant used in hmInit, hmAlloc, and hmFree *)
Definition Free := cst_e 1%Z.

(** field access *)
Definition status : integral_type.ZIT.t := 0%Z.
  Definition alloc : bool := false.
  Definition free : bool := true.
Definition next : integral_type.ZIT.t := 1%Z.

(** heap-list *)

Inductive hl : nat -> list (nat * bool) -> assert :=
| hl_last : forall s p h,
  assert_m.emp s h -> hl p nil s h

| hl_Free : forall s h nxt p h1 h2 size flag tl,
  h1 # h2 -> h = h1 \U h2 ->
  flag = true ->
  nxt = p + 2 + size ->
  (nat_e p |--> Free :: nat_e nxt :: nil ** Array (p + 2) size) s h1 ->
  hl nxt tl s h2 ->
  hl p ((size, flag) :: tl) s h

| hl_Allocated : forall s h nxt p h1 h2 size flag tl,
  h1 # h2 -> h = h1 \U h2 ->
  flag = false ->
  nxt = p + 2 + size ->
  (nat_e p |--> Allocated :: nat_e nxt :: nil) s h1 ->
  hl nxt tl s h2 ->
  hl p ((size, flag) :: tl) s h.

Definition hlstat_bool2expr (b : bool) : expr :=
  match b with
    | true => Free
    | _ => Allocated
  end.

Lemma hl_inde_store : forall l startl s s' h,
  hl l startl s h -> hl l startl s' h.
Proof.
move=> l startl s s' h; elim; clear s h.
- intros s p h H; by apply hl_last.
- intros s h nxt p h1 h2 size flag tl h1_d_h2 h1_U_h2 flag_true Hnxt H H'; subst nxt flag.
  apply hl_Free with (h1 := h1) (h2 := h2) => //.
  case_sepcon H.
  Compose_sepcon h11 h12; first by done.
  eapply Array_inde_store; by apply H_h12.
- intros s h nxt p h1 h2 size flag tl h1_d_h2 h1_U_h2 flag_false Hnxt H H'; subst nxt flag.
  by apply hl_Allocated with (h1 := h1) (h2 := h2).
Qed.

Lemma hl_app : forall a b startl s h,
  (hl startl (a ++ b) s h) <-> ((hl startl a ** hl (get_endl a startl) b) s h).
Proof.
induction a.
- simpl.
  split; simpl; intros.
  Compose_sepcon assert_m.heap.emp h; auto.
  eapply hl_last.
  red; auto.
  case_sepcon H.
  inversion_clear H_h1.
  assert (h = h2).
  Heap_emp_clean; map_tac_m.Equal.
  rewrite H0; auto.
- destruct a.
  split; simpl; intros.
  inversion_clear H.
  + subst b nxt.
    move: (IHa b0 (startl + 2 + n) s h2) => [H H2].
    move: (H H5) => {H5 H2 H} => H.
    case_sepcon H.
    Compose_sepcon (h1 \U h21) h22; last by done.
    eapply hl_Free with (h1 := h1) (h2 := h21);
      [(*Heap_emp_clean;*) map_tac_m.Disj | (*Heap_emp_clean;*) map_tac_m.Equal | reflexivity | reflexivity | assumption | assumption].
  + subst b nxt.
    move: (IHa b0 (startl + 2 + n) s h2) => [H H2].
    move : (H H5) => {H5 H2} {}H.
    case_sepcon H.
    Compose_sepcon (h1 \U h21) h22; last by done.
    eapply hl_Allocated with (h1 := h1) (h2 := h21);
      [(*Heap_emp_clean;*) map_tac_m.Disj | (*Heap_emp_clean;*) map_tac_m.Equal | reflexivity | reflexivity | assumption | assumption].
  + case_sepcon H.
    inversion_clear H_h1.
    * subst b nxt.
      eapply hl_Free with (h1 := h3) (h2 := (h2 \U h4));
        [(*Heap_emp_clean;*) map_tac_m.Disj | (*Heap_emp_clean;*) map_tac_m.Equal | reflexivity | reflexivity | assumption | idtac].
      move: (IHa b0 (startl + 2 + n) s (h2 \U h4)) => [H1 H2].
      apply H2; clear H2 H1.
      by Compose_sepcon h4 h2.
    * subst b nxt.
      eapply hl_Allocated with (h1 := h3) (h2 := (h2 \U h4));
        [map_tac_m.Disj | map_tac_m.Equal | reflexivity | reflexivity | assumption | idtac].
      move: (IHa b0 (startl + 2 + n) s (h2 \U h4)) => [H1 H2].
      apply H2; clear H2 H1.
      by Compose_sepcon h4 h2.
Qed.

Definition Heap_List (l : list (nat * bool)) (p : nat) : assert :=
  (hl p l) ** (nat_e (get_endl l p) |--> Allocated :: null :: nil).

Lemma Heap_List_inde_store: forall l startl s h, Heap_List startl l s h -> forall s', Heap_List startl l s' h.
Proof.
intros.
rewrite /Heap_List in H; case_sepcon H.
Compose_sepcon h1 h2; auto.
by eapply hl_inde_store; eauto.
Qed.

Ltac Heap_List_equiv :=
  match goal with
    | id: Heap_List ?l ?start1 ?s1 ?h |-  Heap_List ?l ?start2 ?s2 ?h =>
      assert (Heap_List_equivA1: start2 = start1);
        [omega |
          ((rewrite Heap_List_equivA1) || idtac);
          eapply (Heap_List_inde_store); apply id
        ]
  end.

Ltac Resolve_topsy :=
  match goal with
    | id: Heap_List ?l ?adr ?s1 ?h |- Heap_List ?l ?adr ?s2 ?h =>
      eapply Heap_List_inde_store; apply id
    | |- is_true (eval_b ?b ?s) =>
      (rewrite eval_b_upd_subst; omegab) ||
      omegab
    | |- ?P /\ ?Q => split; Resolve_topsy
    | |- _ => auto
  end.

Lemma Heap_List_compaction : forall l1 l2 size size' p s h,
  Heap_List (l1 ++ (size, free) :: (size', free) :: nil ++ l2) p s h ->
  exists y, (nat_e (get_endl l1 p + 1) |~> y **
    (nat_e (get_endl l1 p + 1) |~> nat_e (get_endl l1 p + size + size' + 4) -*
      Heap_List (l1 ++ (size + size' + 2, free) :: nil ++ l2) p)) s h.
Proof.
intros.
rewrite /Heap_List in H; case_sepcon H.
generalize (hl_app l1 ((size, true) :: (size', true) :: l2) p s h1); intro X; inversion_clear X.
move/H : H_h1 => {H H0} H_h1.
case_sepcon H_h1.
inversion_clear H_h1_h12; try discriminate.
inversion_clear H4; try discriminate.
subst nxt nxt0.
clear H1 H7.
exists (nat_e (get_endl l1 p + 2 + size)).
case_sepcon H3.
simpl in H3_h31; case_sepcon H3_h31.
case_sepcon H3_h31_h312.
Compose_sepcon h3121 (h311 \U h32 \U h4 \U h11 \U h2).
by Mapsto.
move=> h3121' [X1 X2] h' Hh'.
Compose_sepcon (h3121' \U h311 \U h32 \U h4 \U h11) h2.
- case: (hl_app l1 ((size + size' + 2, true) :: l2) p s (h3121' \U h311 \U h32 \U h4 \U h11)) => _ H25.
  apply H25; clear H25.
  Compose_sepcon h11 (h3121' \U h311 \U h32 \U h4); first by assumption.
  eapply hl_Free with (h1 := h3121' \U h311 \U h32 \U h5) (h2 := h6).
  - by map_tac_m.Disj.
  - by map_tac_m.Equal.
  - reflexivity.
  - reflexivity.
  - Compose_sepcon (h3121' \U h311) (h32 \U h5).
    + simpl.
      Compose_sepcon h311 h3121'.
      by Mapsto.
      Compose_sepcon h3121' assert_m.heap.emp.
      by Mapsto.
      done.
    + case_sepcon H9.
      TArray_concat_split_r size (2 + size').
      Compose_sepcon h32 h5; first by assumption.
      TArray_concat_split_r 2 size'.
      Compose_sepcon h51 h52.
      eapply mapstos_to_array.
      by apply H9_h51.
      by omegab.
      reflexivity.
      assumption.
  - rewrite (_ : get_endl l1 p + 2 + (size + size' + 2) = get_endl l1 p + 2 + size + 2 + size') //; ssromega.
- rewrite get_endl_app [get_endl _ _]/= in H_h2.
  rewrite get_endl_app [get_endl _ _]/=.
  rewrite (_ : get_endl l2 (get_endl l1 p + 2 + (size + size' + 2)) = get_endl l2 (get_endl l1 p + 2 + size + 2 + size')) //.
  congr (get_endl l2 _); ring.
Qed.

Lemma compaction_example : forall p,
  {{ Heap_List ((8, free) :: (10, free) :: nil) p }}
  nat_e p \+ cst_e 1%Z *<- nat_e (p + 22)
  {{ Heap_List ((20, free) :: nil) p }}.
Proof.
move=> p.
apply hoare_mutation_backwards'.
rewrite /Heap_List => s h H.
case/(Heap_List_compaction nil) : H => x /= H1.
exists x.
Monotony H1.
Monotony H.
done.
Qed.

Lemma Heap_List_splitting : forall l1 l2 a b startp s h,
  Heap_List (l1 ++ (a + 2 + b, true) :: l2) startp s h ->
  exists y, ((nat_e (get_endl l1 startp + a + 3) |~> y) **
    ((nat_e (get_endl l1 startp + a + 3) |~> (nat_e (get_endl l1 startp + a + b + 4))) -*
      (fun s h => exists y, ((nat_e (get_endl l1 startp + a + 2) |~> y) **
        ((nat_e (get_endl l1 startp + a + 2) |~> Free) -*
          (fun s h => exists y, ((nat_e (get_endl l1 startp + 1) |~> y) **
            ((nat_e (get_endl l1 startp + 1) |~> (nat_e (get_endl l1 startp + a + 2))) -*
              Heap_List (l1 ++ (a, true) :: (b, true) :: l2) startp
            )) s h
          )
        )) s h
      )
    )) s h.
Proof.
intros.
rewrite /Heap_List in H; case_sepcon H.
generalize (hl_app l1 ((a+2+b,true)::l2) startp s h1); intro X; inversion_clear X.
generalize (H H_h1); clear H H_h1 H0; intro.
case_sepcon H.
inversion_clear H_h12; try discriminate.
case_sepcon H3.
TArray_concat_split_l_l a H3_h32.
case_sepcon H3.
TArray_concat_split_l_l 2 H3_h322.
case_sepcon H3.
simpl in H3_h3221.
case_sepcon H3_h3221.
case_sepcon H3_h3221_h32212.
inversion_clear H3_h3221_h32212_h322121.
inversion_clear H3_h3221_h32211.
exists (cst_e x).
Compose_sepcon h322121 (h2 \U h11 \U h4 \U h31 \U h321 \U h3222 \U h32211).
by Mapsto.
move=> h322121' [X1 X2] h' Hh'.
exists (cst_e x0).
Compose_sepcon h32211 (h2 \U h11 \U h4 \U h31 \U h321 \U h3222 \U h322121').
Mapsto.
move=> h32211' [X3 X4] h'' Hh''.
simpl in H3_h31.
case_sepcon H3_h31.
case_sepcon H3_h31_h312.
exists (nat_e nxt).
Compose_sepcon h3121 (h2 \U h11 \U h4 \U h311 \U h321 \U h32211' \U h322121' \U h3222).
Mapsto.
move=> h3121' [X5 X6] h''' Hh'''.
Compose_sepcon (h3121' \U h11 \U h4 \U h311 \U h321 \U h32211' \U h322121' \U h3222) h2.
case: (hl_app l1 ((a,true)::(b,true)::l2) startp s
 (((((((h3121' \U h11) \U h4) \U h311) \U h321) \U h32211') \U
       h322121') \U h3222)
) => _ H40.
apply H40; clear H40.
Compose_sepcon h11  ((((((h3121' \U h4) \U h311) \U h321) \U h32211') \U
       h322121') \U h3222).
auto.
eapply hl_Free with (h1 := h311 \U h3121' \U h321) (h2 := h4 \U h32211' \U h322121' \U h3222).
by map_tac_m.Disj.
Heap_emp_clean; map_tac_m.Equal.
auto.
intuition.
Compose_sepcon (h311 \U h3121') h321.
simpl.
Compose_sepcon h311 h3121'.
Mapsto.
Compose_sepcon h3121' assert_m.heap.emp.
Mapsto.
red; auto.
Array_equiv.
eapply hl_Free with (h1 := h32211' \U h322121' \U h3222) (h2 := h4).
by map_tac_m.Disj.
by map_tac_m.Equal.
reflexivity.
reflexivity.
Compose_sepcon (h32211' \U h322121') h3222.
simpl.
Compose_sepcon h32211' h322121'.
by Mapsto.
Compose_sepcon h322121' assert_m.heap.emp.
by Mapsto.
done.
Array_equiv.
subst nxt.
rewrite (_ : get_endl l1 startp + 2 + a + 2 + b = get_endl l1 startp + 2 + (a + 2 + b)) //.
ring.
rewrite (_ : get_endl (l1 ++ (a, true) :: (b, true) :: l2) startp = get_endl (l1 ++ (a + 2 + b, true) :: l2) startp)
  // !get_endl_app /=.
congr (get_endl l2 _); ring.
Qed.

(** Several lemmas to change the status of blocks *)

Lemma hl_free2alloc l1 l2 a startp s h :
  Heap_List (l1 ++ (a, true) :: l2) startp s h ->
  exists y, ((nat_e (get_endl l1 startp) |~> y) **
    ((nat_e (get_endl l1 startp) |~> Allocated) -*
      (Heap_List (l1 ++ (a, false) :: l2) startp ** Array (get_endl l1 startp + 2) a)))  s h.
Proof.
move=> H.
rewrite /Heap_List in H; case_sepcon H.
generalize (hl_app l1 ((a, true) :: l2) startp s h1); intro X; inversion_clear X.
generalize (H H_h1); clear H H_h1 H0; intros.
case_sepcon H.
inversion_clear H_h12; try discriminate.
subst nxt.
case_sepcon H3.
rewrite /mapstos in H3_h31; case_sepcon H3_h31.
exists Free.
Compose_sepcon h311 (h312 \U h32 \U h4 \U h11 \U h2).
Mapsto.
move=> h311' [X1 X2] h' Hh'.
Compose_sepcon (h312 \U h311' \U h4 \U h11 \U h2) h32.
Compose_sepcon (h312 \U h311' \U h4 \U h11) h2.
case: (hl_app l1 ((a, false) :: l2) startp s (h312 \U h311' \U h4 \U h11)) => _.
apply.
Compose_sepcon h11 (h312 \U h311' \U h4).
auto.
eapply hl_Allocated with (h1 := (h312 \U h311')) (h2 := h4).
map_tac_m.Disj.
Heap_emp_clean; map_tac_m.Equal.
auto.
intuition.
Compose_sepcon h311' h312.
Mapsto.
auto.
auto.
rewrite (_ : get_endl (l1 ++ (a, false) :: l2) startp = get_endl (l1 ++ (a, true) :: l2) startp) //.
by rewrite !get_endl_app.
assumption.
Qed.

Lemma hl_alloc2free l1 l2 a startp s h :
  (Heap_List (l1 ++ (a, false) :: l2) startp ** Array (get_endl l1 startp + 2) a) s h ->
  exists y, ((nat_e (get_endl l1 startp) |~> y) **
    ((nat_e (get_endl l1 startp) |~> Free) -* (Heap_List (l1 ++ (a, true) :: l2) startp))) s h.
Proof.
move=> H.
case_sepcon H.
rewrite /Heap_List in H_h1; case_sepcon H_h1.
generalize (hl_app l1 ((a, false) :: l2) startp s h11); intro X; inversion_clear X.
move/H : H_h1_h11 => {H H0} H_h1_h11.
case_sepcon H_h1_h11.
inversion_clear H_h1_h11_h112; try discriminate.
rewrite /mapstos in H3; case_sepcon H3.
exists Allocated.
Compose_sepcon h31 (h32 \U h4 \U h111 \U h12 \U h2).
Mapsto.
move=> h31' [X1 X2] h' Hh'.
Compose_sepcon (h32 \U h4 \U h111 \U h31' \U h2) h12.
case: (hl_app l1 ((a,true)::l2) startp s (h32 \U h4 \U h111 \U h31' \U h2)) => _.
apply.
Compose_sepcon h111 (h32 \U h4 \U h31' \U h2).
auto.
eapply hl_Free with (h1 := h32 \U h31' \U h2) (h2 := h4).
map_tac_m.Disj.
by map_tac_m.Equal.
reflexivity.
by apply H2.
Compose_sepcon (h32 \U h31') h2.
Compose_sepcon h31' h32.
by Mapsto.
assumption.
auto.
auto.
rewrite (_ : get_endl (l1 ++ (a, true) :: l2) startp = get_endl (l1 ++ (a, false) :: l2) startp) //.
by rewrite !get_endl_app.
Qed.

Lemma hl_free2free l1 l2 a startp s h :
  Heap_List (l1 ++ (a, true) :: l2) startp s h ->
  exists y, ((nat_e (get_endl l1 startp) |~> y) **
    (nat_e (get_endl l1 startp) |~> Free -* (Heap_List (l1 ++ (a, true) :: l2) startp))) s h.
Proof.
move=> H.
rewrite /Heap_List in H; case_sepcon H.
case: (hl_app l1 ((a, true) :: l2) startp s h1).
move/(_ H_h1) => {}H_h1 _.
case_sepcon H_h1.
inversion_clear H_h1_h12; try discriminate.
subst nxt.
case_sepcon H3.
rewrite /mapstos in H3_h31; case_sepcon H3_h31.
exists Free.
Compose_sepcon h311 (h312 \U h32 \U h4 \U h11 \U h2).
Mapsto.
move=> h311' [X1 X2] h' Hh'.
Compose_sepcon (h312 \U h311' \U h4 \U h11 \U h32) h2.
case: (hl_app l1 ((a,true)::l2) startp s (h312 \U h311' \U h4 \U h11 \U h32)) => _.
apply.
Compose_sepcon h11 (h312 \U h311' \U h4 \U h32).
auto.
eapply hl_Free with (h1 := (h312 \U h311' \U h32)) (h2 := h4).
by map_tac_m.Disj.
by map_tac_m.Equal.
reflexivity.
reflexivity.
Compose_sepcon (h311' \U h312) h32.
Compose_sepcon h311' h312.
Mapsto.
assumption.
assumption.
assumption.
assumption.
Qed.

Lemma hl_getnext l1 l2 a b startp s h : Heap_List (l1 ++ (a, b) :: l2) startp s h ->
  (nat_e (get_endl l1 startp + 1) |~> nat_e (get_endl l1 startp + 2 + a) **
    (nat_e (get_endl l1 startp + 1) |~> nat_e (get_endl l1 startp + 2 + a) -*
      Heap_List (l1 ++ (a, b) :: l2) startp)) s h.
Proof.
move=> H.
apply mapsto_strictly_exact; split; last by done.
rewrite /Heap_List in H; case_sepcon H.
case: (hl_app l1 ((a,b)::l2) startp s h1) => H2 _.
move/H2 : H_h1 => H_h1.
case_sepcon H_h1.
inversion_clear H_h1_h12.
- subst nxt.
  rewrite /= in H4; case_sepcon H4.
  case_sepcon H4_h31.
  case_sepcon H4_h31_h312.
  Compose_sepcon h3121 (h311 \U h32 \U h4 \U h11 \U h2).
  by Mapsto.
  done.
- subst nxt.
  rewrite /= in H4; case_sepcon H4.
  case_sepcon H4_h32.
  Compose_sepcon h321 (h31 \U h4 \U h11 \U h2).
  by Mapsto.
  done.
Qed.

Lemma hl_getnext_last l startp s h : Heap_List l startp s h ->
  (nat_e (get_endl l startp + 1) |~> nat_e 0 **
    (nat_e (get_endl l startp + 1) |~> nat_e 0 -* Heap_List l startp)) s h.
Proof.
move=> H.
apply mapsto_strictly_exact; split; last by done.
rewrite /Heap_List in H; case_sepcon H.
simpl in H_h2; case_sepcon H_h2.
case_sepcon H_h2_h22.
Compose_sepcon h221 (h21 \U h1); last by done.
by Mapsto.
Qed.

Lemma hl_getstatus l1 l2 a b startp s h : Heap_List (l1 ++ (a, b) :: l2) startp s h ->
 ((nat_e (get_endl l1 startp) |~> hlstat_bool2expr b) **
   ((nat_e (get_endl l1 startp) |~> hlstat_bool2expr b) -* Heap_List (l1 ++ (a, b) :: l2) startp)) s h.
Proof.
move=> H.
apply mapsto_strictly_exact; split; last by done.
rewrite /Heap_List in H; case_sepcon H.
case: (hl_app l1 ((a,b)::l2) startp s h1) => H2 _.
move/H2 : H_h1 => H_h1.
case_sepcon H_h1.
inversion_clear H_h1_h12.
- subst nxt.
  case_sepcon H4.
  rewrite /= in H4_h31; case_sepcon H4_h31.
  case_sepcon H4_h31_h312.
  Compose_sepcon h311 (h3121 \U h32 \U h4 \U h11 \U h2).
  subst b.
  by Mapsto.
  done.
- subst nxt.
  rewrite /= in H4; case_sepcon H4.
  case_sepcon H4_h32.
  Compose_sepcon h31 (h321 \U h4 \U h11 \U h2).
  subst b.
  by Mapsto.
  done.
Qed.

Lemma hl_getstat_last l startp s h : Heap_List l startp s h ->
  (nat_e (get_endl l startp) |~> Allocated **
    (nat_e (get_endl l startp) |~> Allocated -* Heap_List l startp)) s h.
Proof.
move=> H.
apply mapsto_strictly_exact; split; last by done.
rewrite /Heap_List in H; case_sepcon H.
rewrite /= in H_h2; case_sepcon H_h2.
case_sepcon H_h2_h22.
Compose_sepcon h21 (h221 \U h1); [by Mapsto | done].
Qed.

Lemma In_hl_lt: forall l a b c startp, In_hl l (a, b, c) startp -> a < get_endl l startp.
Proof.
induction l.
simpl; contradiction.
destruct a.
intros.
simpl.
simpl in H.
case: ifP H.
  case/andP => /andP [/eqP ? /eqP ?] /eqP ? _.
  subst startp c.
  move: (get_endl_gt l (a + 2 + n)) => ?.
  ssromega.
move=> _ H.
by eapply IHl; apply H.
Qed.

Lemma In_hl_destruct: forall l a b c adr,
  In_hl l (a, b, c) adr -> exists l1 l2, l = l1 ++ (b, c) :: l2 /\ get_endl l1 adr = a.
Proof.
elim=> //; case=> n b l IHl /= a b0 c adr H.
case: ifP H.
- case/andP => /andP[/eqP ? /eqP ?]; move=> /eqP ?.
  subst adr c b0; by exists nil, l.
- move=> _ /IHl [x [x0 [H2 H3]]].
  exists ((n, b) :: x), x0; by rewrite /= H2.
Qed.

Lemma In_hl_ge_start : forall l x y z adr, In_hl l (x, y, z) adr -> x >= adr.
Proof.
elim => //; case=> [n b] l IHl /= x y z adr H.
case: ifP H.
- by case/andP => /andP [] /eqP ->.
- move=> _ /IHl ?; ssromega.
Qed.

Lemma In_hl_dif: forall l x y a b adr, In_hl l (x, y, alloc) adr -> In_hl l (a, b, free) adr -> a <> x.
Proof.
elim=> //; case=> n b l IHl x y a b0 adr /= H H0.
case: ifP H => [H1|].
  case/andP : H1 => /andP [ /eqP ? /eqP ? ] /eqP => ? _; subst.
  case: ifP H0 => [H2 _|].
    by case/andP : H2 => /andP [ /eqP ? /eqP ? ] /eqP => ?; subst.
  move => _.
  move/In_hl_ge_start => ?; ssromega.
case: ifP H0 => [H2 _|].
   case/andP : H2 => /andP [ /eqP ? /eqP ? ] /eqP => ?; subst.
   move=> _.
   move/In_hl_ge_start => ?; ssromega.
move=> _ /IHl H _.
by apply H.
Qed.

Lemma In_hl_match: forall l1 l2 x y size stat startp,
  In_hl (l1 ++ (x, y) :: l2) (get_endl l1 startp, size, stat) startp ->
  size = x /\ stat = y.
Proof.
induction l1.
simpl; intros.
  rewrite eqxx /= in H.
  case: ifP H.
    by case/andP => /eqP ? /eqP ?.
  move=> _.
  move/In_hl_ge_start => ?; ssromega.
move=> l2 x y size stat startp.
rewrite /=.
destruct a.
case: ifP => //.
  case/andP => /andP [] /eqP ? /eqP ? /eqP ? _.
  move: (get_endl_gt l1 (startp + 2 + n)) => ?; ssromega.
by move=> _ /IHl1.
Qed.

Lemma In_hl_next : forall l x y z b c adr,
  In_hl l (x, y, z) adr ->
  In_hl l (x + 2 + y, b, c) adr ->
  exists l1 l2, l = l1 ++ (y, z) :: (b, c) :: l2 /\ x = get_endl l1 adr.
Proof.
induction l.
simpl; intuition.
destruct a; simpl; intros.
case: ifP H => H2.
- case/andP : H2 => /andP [H1 H3] H2.
  have H4 : (adr == x + 2 + y) && (c == b) && (n == b0) = false.
    by rewrite (eqP H1) -addnA -{1}(addn0 x) eqn_add2l addSn.
  rewrite H4 in H0.
  move: (eqP H2) => ?; subst y.
  move: (eqP H1) => ?; subst x.
  case/In_hl_destruct : (H0) => x [x0 [H6 H7]].
  rewrite H6 in H0.
  destruct x.
    exists nil, x0; by rewrite H6 (eqP H3).
  destruct p.
  rewrite /= in H7.
  move: (get_endl_gt x (adr + 2 + n + 2 + n0)) => H5.
  rewrite H7 in H5.
  assert (~ (adr + 2 + n + 2 + n0 <= adr + 2 + n)) by ssromega.
  tauto.
- move=> H.
  have H1 : (adr == x + 2 + y) && (c == b) && (n == b0) = false.
    apply/negbTE; rewrite !negb_and -orbA; apply/orP; left; apply/eqP.
    move: (In_hl_ge_start _ _ _ _ _ H) => ?; ssromega.
  rewrite H1 in H0.
  case: (IHl _ _ _ _ _ _ H H0) => x0 [x1 [H4 H5]].
  exists ((n, b) :: x0), x1.
  by rewrite H4.
Qed.

Lemma In_hl_last : forall l a b c adr,
  In_hl l (a, b, c) adr -> get_endl l adr = a + 2 + b -> exists l', l = l'++ (b, c) :: nil.
Proof.
elim=> // a l IHl a0 b c adr H H0.
destruct a.
move: (In_hl_lt _ _ _ _ _ H) => H1.
simpl in H1.
simpl in H.
case: ifP H => [H3 _ |H3 H].
- case/andP : H3 => /andP [H2 H4] H3.
  simpl in H0.
  move: (eqP H3) (eqP H2); intros; subst a0 n.
  destruct l.
    by exists nil; by rewrite (eqP H4).
  simpl in H0.
  destruct p.
  move: (get_endl_gt l (adr + 2 + b + 2 + n)).
  rewrite H0 => ?.
  exfalso; ssromega.
- simpl in H0.
  case: (IHl _ _ _ _ H H0) => x H4.
  exists ((n, b0) :: x); by rewrite H4.
Qed.

Lemma In_hl_first : forall l adr sz st, In_hl l (adr, sz, st) adr -> exists l', l = (sz, st) :: l'.
Proof.
elim=> // a l IHl adr sz st H.
destruct a.
simpl in H.
case: ifP H => [H1 _|H1].
  case/andP : H1 => /andP[H1 H3] H2.
  exists l; by rewrite (eqP H3) (eqP H2).
move/In_hl_ge_start => H.
exfalso; ssromega.
Qed.

(** Tactics *)

(* Tactic that compute the equilent of a hl list such that it can be use by hl_getxxx *)
Ltac Norm_head l :=
  match l with
    | ?hd :: ?tl => constr: (hd :: nil)
    | ?l1 ++ ?l2 =>
      let x:= Norm_head l1 in
        match x with
          | nil => l1
          | _ => x
        end
    | _ => l
  end.

Ltac Norm_tail A l :=
  match l with
    | ?hd :: ?tl => tl
    | ?l1 ++ ?l2 =>
      let x := Norm_tail A l1 in
        match x with
          | nil => l2
          | _ => constr: (x ++ l2)
        end
    | _ => constr: (@nil A)
  end.

Ltac Norm_List A l :=
  match l with
    | nil => constr:(@nil A)
    | _ =>
      let hd := Norm_head l in
      let tl := Norm_tail A l in
      let tl' := (Norm_List A tl) in
            match tl' with
              | nil => hd
              | _ => constr:(hd ++ tl')
            end
  end.

Ltac Format_head A l elt :=
  match l with
    | ((elt, ?st) :: nil) => constr:(@nil A)
    | ((elt, ?st) :: nil) ++ ?l2 => constr:(@nil A)
    | ?l1 ++ ?l2 =>
      let hd:= (Format_head A l2 elt) in
        match hd with
          | nil => l1
          | _ => constr:(l1 ++ hd)
        end
  end.

Ltac Format_tail A l elt :=
  match l with
    | ((elt, ?st) :: nil) => l
    | ((elt, ?st) :: nil) ++ ?l2 => constr: ((elt,st)::l2)
    | ?l1 ++ ?l2 =>
      let tl := Format_tail A l1 elt in
        match tl with
          | nil => Format_tail A l2 elt
          | _ => constr: (tl ++ l2)
        end
    | _ => constr:(@nil A)
  end.

Ltac Format_HLList l elt :=
  let A := constr : ((nat * bool)%type) in
  let y := Norm_List A l in
  let hd := Format_head A y elt in
  let tl := Format_tail A y elt in
        constr:(hd ++ tl).

Ltac List_eq :=
  repeat rewrite -catA ;
  repeat rewrite cats0 ;
  repeat match goal with
    | |- context [?h :: (seq.cat ?a ?b) ] =>
      rewrite -(@cat1s _ h (seq.cat a b)) catA
  end ; auto.

(*  repeat rewrite catA; repeat rewrite cats0; repeat rewrite <- List.app_comm_cons; auto.*)

(* Resolve the first hypothese of the mapsto_stricly_exact lemma using hl_getstatus given
   H: the Heap_List Hypothesis
   elt: the size of the block
 *)

Ltac Hl_getstatus H elt x :=
  match goal with
    | H: Heap_List ?l ?start ?s ?h |- _ =>
      let l' := Format_HLList l elt in
        cutrewrite (l = l') in H; [
          let h1:= fresh h "1" in (* NB: kludge: this is only likely to match the h1 and h2 produced by case_sepcon *)
          let h2:= fresh h "2" in
              generalize (hl_getstatus _ _ _ _ _ _ _ H); intro x; case_sepcon x;
                Compose_sepcon h1 h2; [idtac | red; auto]
          | List_eq
        ]
  end.

Ltac Hl_getnext H elt x :=
  match goal with
    | H: Heap_List ?l ?start ?s ?h |- _ =>
      let l' := Format_HLList l elt in
        cutrewrite (l = l') in H; [
          let h1:= fresh h "1" in (* NB: kludge: this is only likely to match the h1 and h2 produced by case_sepcon *)
          let h2:= fresh h "2" in
              generalize (hl_getnext _ _ _ _ _ _ _ H); intro x; case_sepcon x;
                Compose_sepcon h1 h2; [idtac | red; auto]
          | List_eq
        ]
  end.

(** global variable used in hmInit, hmAlloc, and hmFree *)
Definition hmStart : var.v := O.

(** local variables *)
Definition entry : var.v := 3%nat.
Definition cptr : var.v := 4%nat.
Definition nptr : var.v := 5%nat.
Definition result : var.v := 6%nat.
Definition fnd : var.v := 7%nat.
Definition stts : var.v := 8%nat.
Definition sz : var.v := 9%nat. (* used in hmAlloc only *)

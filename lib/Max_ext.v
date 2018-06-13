(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Max Omega.
From mathcomp Require Import ssreflect ssrbool ssrnat seq.
Require Import ssrnat_ext.
Export Max.

Lemma max_lemma1 x1 x2 x3 : x2 <= x1 -> max x2 x3 <= max x1 x3.
Proof.
move=> H.
case: (max_dec x1 x3) => H1.
  case: (max_dec x2 x3) => H2.
    by rewrite H1 H2.
  rewrite H1 H2.
  move: (le_max_r x1 x3) => H0.
  rewrite H1 in H0.
  ssromega.
case: (max_dec x2 x3) => H2.
  rewrite H1 H2.
  move: (le_max_l x1 x3) => H0.
  rewrite H1 in H0.
  ssromega.
by rewrite H1 H2.
Qed.

Lemma max_max a b c d : a <= c -> b <= d -> max a b <= max c d.
Proof.
move=> a_c b_d; case: (max_dec a b) => ->.
- apply (@leq_trans c) => //; by apply/leP/Nat.le_max_l.
- apply (@leq_trans d) => //; by apply/leP/le_max_r.
Qed.

Lemma lt_max_inv x1 x2 x3 : max x2 x3 < x1 -> x2 < x1 /\ x3 < x1.
Proof.
move=> H; case: (max_dec x2 x3) => H0.
- move: (le_max_r x2 x3) => H1; ssromega.
- move: (le_max_l x2 x3) => H1; ssromega.
Qed.

Lemma lt_max x1 x2 x3 : x2 < x1 /\ x3 < x1 -> max x2 x3 < x1.
Proof. move=> [H0 H1]. case: (max_dec x2 x3) => H; ssromega. Qed.

Lemma le_max x1 x2 x3 : x2 <= x1 /\ x3 <= x1 -> max x2 x3 <= x1.
Proof.
move=> [H0 H1].
have [H2 | H2] : (x2 >= x3 \/ x3 >= x2)%coq_nat by omega.
- rewrite max_l; ssromega.
- rewrite max_r; ssromega.
Qed.

Lemma le_max_l_trans x y z : x <= z -> x <= max z y.
Proof. move=> H; generalize (le_max_l z y) => ?; ssromega. Qed.

Lemma le_max_r_trans x y z : x <= z -> x <= max y z.
Proof. move=> H; generalize (le_max_r y z) => ?; ssromega. Qed.

Ltac Resolve_le_max :=
  match goal with
    | |- is_true (max ?y ?z <= ?x) =>
      apply le_max; split; [Resolve_le_max | Resolve_le_max]
    | |- is_true (?z <= max ?x ?y) =>
      apply le_max_l_trans; Resolve_le_max
    | |- is_true (?z <= max ?x ?y) =>
      apply le_max_r_trans; Resolve_le_max
    | |- is_true (?z < ?x + (S ?y)) =>
      cut (is_true (z <= x)); [move=> ?; ssromega | Resolve_le_max]
    | _ => ssromega
  end.

Lemma le_max_inv a b n : max a b <= n -> a <= n /\ b <= n.
Proof.
case: (max_dec a b) => max_a_b.
- rewrite max_a_b => H; split; first by [].
  apply (@leq_trans a) => //.
  rewrite -max_a_b; by apply/leP/le_max_r.
- rewrite max_a_b => H; split; last by [].
  apply (@leq_trans b) => //.
  rewrite -max_a_b; by apply/leP/le_max_l.
Qed.

Definition max_list l def := foldl max def l.

Lemma max_list_max_comm : forall a b c, max_list a (max b c) = max b (max_list a c).
Proof. elim => // hd tl IH b c /=; by rewrite 2!IH max_assoc. Qed.

Lemma le_max_list_R : forall l x def, x <= def -> x <= max_list l def.
Proof.
elim=> // h t IH x def x_def /=.
by apply IH, (le_max_l_trans _ h _ x_def).
Qed.

Lemma In_le_max_list : forall l def x, List.In x l -> x <= max_list l def.
Proof.
elim=> // hd tl IH def x /= [-> | H].
by apply/le_max_list_R/leP/le_max_r.
by apply IH.
Qed.

Lemma le_max_list_def : forall l x, x <= max_list l x.
Proof. elim => // hd tl IH x /=; by apply/le_max_list_R/leP/le_max_l. Qed.

Lemma max_list_inv : forall a b n, max_list a b <= n -> b <= n.
Proof. elim => // hd tl IH b n /=; rewrite max_list_max_comm; by case/le_max_inv. Qed.

Lemma max_list_inv2 : forall a b n, max_list a b <= n ->
  forall x, List.In x a -> x <= n.
Proof.
elim => // hd tl IH b n /= H x [] X.
- subst hd.
  rewrite max_comm max_list_max_comm in H.
  by case/le_max_inv : H.
- apply (IH b) => //.
  rewrite max_comm max_list_max_comm in H.
  by case/le_max_inv : H.
Qed.

Lemma lt_max_list l x y z : max_list l y < x -> z < x -> max_list l (max y z) < x.
Proof. move=> H1 H2; rewrite max_comm max_list_max_comm; by apply lt_max. Qed.

Lemma lt_max_list_inv : forall l x def, max_list l def < x -> def < x.
Proof. elim=> // h t IH x def /= /IH; by case/lt_max_inv. Qed.

Lemma lt_max_list_inv2 : forall l x def, max_list l def < x ->
  forall y, List.In y l -> y < x.
Proof.
elim=> // h t IH x def /= H y [].
  move=> ?; subst h.
  rewrite max_comm max_list_max_comm in H.
  by case/lt_max_inv : H.
move=> y_t.
apply IH with def => //.
rewrite max_comm max_list_max_comm in H.
by case/lt_max_inv : H.
Qed.

Lemma max_list_app_inv : forall a b x def, max_list (a ++ b) def < x ->
  max_list a def < x /\ max_list b def < x.
Proof.
elim=> [ | h t IH b x def] /=.
  move=> b x def H; split; last by done.
  move: H; by apply lt_max_list_inv.
case/IH => H1 H2; split; first by assumption.
rewrite max_comm max_list_max_comm in H2.
by case/lt_max_inv : H2.
Qed.

Lemma max_list_app : forall a b x def, max_list a def < x /\ max_list b def < x ->
  max_list (a ++ b) def < x.
Proof.
elim=> /= [b x def [] // | h t IH b x def [H1 H2]].
apply IH.
split => //.
apply lt_max_list => //.
by move/lt_max_list_inv : H1 => /lt_max_inv [].
Qed.

Definition max_lst l := max_list l O.

Ltac Resolve_lt_max :=
  Resolve_lt_max_hypo; Resolve_lt_max_goal
with
  Resolve_lt_max_hypo := match goal with
    | H: is_true (max ?y ?z < ?x)%nat |- _ =>
      generalize (lt_max_inv _ _ _ H); intro X; inversion_clear X; clear H; Resolve_lt_max_hypo
    | H: is_true (max_lst (seq.cat ?y ?z) < ?x)%nat |- _ =>
      generalize (max_list_app_inv _ _ _ _ H); intro X; inversion_clear X; clear H; Resolve_lt_max_hypo
    | H: is_true (max_lst _ < ?x)%nat |- _ => rewrite /max_lst /= in H; Resolve_lt_max_hypo
    | |- _ =>  idtac
  end
with
  Resolve_lt_max_goal := match goal with
    | |- is_true (max ?y ?z < ?x)%nat =>
      apply lt_max; split; [Resolve_lt_max_goal | Resolve_lt_max_goal]
    | |- is_true (max_lst (seq.cat ?y ?z) < ?x)%nat =>
      apply max_list_app; split; [Resolve_lt_max_goal | Resolve_lt_max_goal]
    | |- is_true (max_lst _ < ?x)%nat => rewrite /max_lst /=; Resolve_lt_max_goal
    | |- _ => ssromega || tauto
  end.

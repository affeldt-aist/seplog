(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ProofIrrelevance.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import seq_ext order.

(**
this files provides:
- a section that defines ordered sequences
- a module type for finite sets (equality is the Coq equality)
- a functor to instantiate finite sets of ordered types
*)

Declare Scope ordset_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module OrderedSequence.

Set Implicit Arguments.

Section ordered_sequence.

Variable A : eqType.
Variable ltA : A -> A -> bool.
Local Notation "x < y" := (ltA x y).
Variable ltA_trans :  forall n m p, m < n -> n < p -> m < p.
Variable ltA_total : forall m n, (m != n) = (m < n) || (n < m).
Variable ltA_irr : forall a, a < a = false.
Local Notation lb := (lb ltA).

Inductive ordered : seq A -> Prop :=
| ord_nil : ordered [::]
| ord_cons : forall s, ordered s -> forall a, lb a s -> ordered (a :: s).

Lemma ordered_inv h t : ordered (h :: t) -> ordered t /\ lb h t.
Proof. move=> H. by inversion_clear H. Qed.

Lemma ordered_app_inv_ltA (a b : seq A) : ordered (a ++ b) ->
  forall x y, x \in a -> y \in b -> ltA x y.
Proof.
move Hab : (a ++ b) => ab Hord.
move: Hord a b Hab.
elim=> [[] // | lst Hord IH a Hlb [|a0 a1] // b /= H].
case: H => ? ?; subst a0 lst => x y.
rewrite in_cons.
case/orP.
- move/eqP=> ?; subst x => Hy.
  apply (mem_lt_lb Hlb).
  by rewrite mem_cat Hy orbC.
- by apply IH.
Qed.

Lemma ordered_app_inv : forall (a b : seq A), ordered (a ++ b) -> ordered a /\ ordered b.
Proof.
elim=> [b /= Hb | h t IH b /=].
  split; [by constructor | exact Hb].
case/ordered_inv.
case/IH => H1 H2 H; split => //.
apply ord_cons => //.
apply lt_lb => n Hn.
eapply mem_lt_lb; eauto.
by rewrite mem_cat Hn.
Qed.

Lemma ordered_singleton x : ordered [:: x].
Proof. apply ord_cons => //; by apply ord_nil. Qed.

Lemma ordered_uniq : forall k, ordered k -> uniq k.
Proof.
elim=> // hd tl IH.
case/ordered_inv => H1 H2 /=.
by rewrite IH // (mem_lb ltA_irr).
Qed.

Lemma ordered_filter : forall l, ordered l -> forall f, ordered (filter f l).
Proof.
elim=> //=.
move=> h t IH.
case/ordered_inv => H1 H2 f.
case: ifP => X.
- apply ord_cons.
  by apply IH.
  by apply lb_incl.
- by apply IH.
Qed.

Lemma ordered_ext : forall (l1 l2 : seq A), ordered l1 -> ordered l2 ->
  (forall x, has (pred1 x) l1 = has (pred1 x) l2) ->
  l1 = l2.
Proof.
elim=> //=.
- case=> //=.
  move=> h2 t2 _ H H'.
  move: {H'}(H' h2) => H'.
  have X : h2 == h2 by apply/eqP => //.
  rewrite X //= in H'.
- move=> h1 t1 IH l2; move: l2 h1 t1 IH; elim=> //=.
  + move=> h1 t1 _ _ _ H'.
    move: {H'}(H' h1) => H'.
    have X : h1 == h1 by apply/eqP => //.
    rewrite X //= in H'.
  + move=> h2 t2 _ h1 t1 IH' H1 H2 H.
    apply ordered_inv in H1; case: H1 => H11 H12.
    apply ordered_inv in H2; case: H2 => H21 H22.
    case: (tri' ltA_total h1 h2) => [X | [X | X]].
    * have : h2 < h1.
        apply mem_lt_lb with t2 => //.
        move: {H}(H h1) => H.
        rewrite -has_pred1.
        rewrite eqxx /= in H.
        rewrite eq_sym (_:h1 == h2 = false) //= in H.
        apply/negP => Y. move/eqP in Y; subst. rewrite ltA_irr // in X.
        move=> Y; move: (ltA_trans X Y); by rewrite ltA_irr.
    * subst h2.
      rewrite (IH' t2) // => x.
      case/boolP : (x == h1) => [/eqP |] X.
      - subst h1.
        by rewrite 2!has_pred1 (negbTE (mem_lb ltA_irr H12)) (negbTE (mem_lb ltA_irr H22)).
      - move: (H x).
        move/negbTE : X.
        by rewrite eq_sym => ->.
    * have Y : h1 < h2.
        apply mem_lt_lb with t1 => //.
        rewrite -has_pred1.
        move: {H}(H h2) => H.
        rewrite eqxx /= in H.
        rewrite eq_sym (_ : h2 == h1 = false) //= in H.
        apply/negP => Y. move/eqP in Y; subst.
        by rewrite ltA_irr // in X.
      move: (ltA_trans X Y); by rewrite ltA_irr.
Qed.

Fixpoint orderedb l :=
  match l with
    | [::] => true
    | h :: t => if lb h t then orderedb t else false
  end.

Lemma orderedb_inv x l : orderedb (x :: l) -> orderedb l /\ lb x l.
Proof.
case: l => // h t.
rewrite {2 3}[cons]lock [lb]lock /= -2!lock => H.
have X : lb x (h :: t).
  apply/negP.
  move/negP=> X.
  by rewrite (negbTE X) in H.
by rewrite X in H.
Qed.

Lemma orderedb_lb : forall l, orderedb l -> forall x, lb x l -> orderedb (x :: l).
Proof. move=> /=. by case=> // h t H l1 ->. Qed.

Lemma orderedP : forall l, ordered l <-> orderedb l.
Proof.
elim.
- split => // _; by apply ord_nil.
- move=> a l H; split.
  + case/ordered_inv => ? /= ->; by apply H.
  + case/orderedb_inv => ? ?; apply ord_cons => //; by apply H.
Qed.

Record ord_seq : Type := mk_ord_seq {
  ord2seq :> seq A ;
  Hord_seq : ordered ord2seq }.

Definition proper (a b : ord_seq) := {subset (ord2seq a) <= ord2seq b} /\ (size a < size b)%nat.

Lemma subset_size (a b : ord_seq) : {subset (ord2seq a) <= ord2seq b} -> (size a <= size b)%nat.
Proof.
case: a b => /=.
elim=> // ha ta IH.
case/ordered_inv => H1 H2.
case => /=.
case.
  move=> _.
  move/(_ ha).
  rewrite in_cons eqxx /= in_nil.
  by move/(_ erefl).
move=> hb tb.
case/ordered_inv => K1 K2 H.
move: (H ha).
rewrite in_cons eqxx /= in_cons.
move/(_ erefl).
case/orP => [|hatb].
  move=> /eqP ?; subst hb.
  rewrite ltnS.
  apply: (IH H1 (mk_ord_seq K1)) => x Hx /=.
  move: (H x).
  rewrite in_cons Hx orbT.
  move/(_ erefl).
  rewrite in_cons.
  case/orP => // /eqP ?; subst ha.
  move: (mem_lb ltA_irr H2).
  by rewrite Hx.
rewrite ltnS.
apply: (IH H1 (mk_ord_seq K1)) => x Hx /=.
move: (H x).
rewrite in_cons Hx orbT.
move/(_ erefl).
rewrite in_cons.
case/orP => //.
move/eqP => ?; subst x.
exfalso.
have hahb : ha < hb by by apply mem_lt_lb with ta.
have hbha : hb < ha by apply mem_lt_lb with tb.
move: (ltA_trans hahb hbha).
by rewrite ltA_irr.
Qed.

(* TODO: move *)
Lemma ord_seq_uniq : forall k, ordered k -> uniq k.
Proof.
elim=> // h t IH /ordered_inv [] Ht ht /=.
by rewrite IH // andbT (mem_lb ltA_irr).
Qed.

(* TODO: move *)
Lemma uniqe_subset_size l k : ordered l -> ordered k ->
  {subset l <= k} ->
  size l = size k ->
  l = k.
Proof.
move Hn : (size l) => n.
elim: n l Hn k.
  case=> // _.
  by case.
move=> n IH.
case=> // h t /= [] tn.
case => // a b H ab L /= [] bn.
move: (L h).
rewrite in_cons eqxx => /(_ erefl).
rewrite in_cons; case/orP.
  move=> /eqP ?; subst h.
  case/ordered_inv : (ab) => H1 H2.
  case/ordered_inv : (H) => K1 K2.
  have : {subset t <= b }.
    rewrite /= => x Hx.
    move: (L x).
    rewrite in_cons Hx orbC /=.
    move/(_ erefl).
    rewrite in_cons.
    case/orP => // /eqP ?; subst a.
    move/(mem_lb ltA_irr) : K2.
    by rewrite Hx.
  move/IH => /=.
  rewrite tn.
  move/(_ erefl K1 H1 bn) => ?; by subst t.
move=> hb.
exfalso.
have abs : {subset h :: t <= b}.
  move=> x.
  rewrite in_cons.
  case/orP => [/eqP -> //| xt].
  move: (L x).
  rewrite in_cons xt orbC.
  move/(_ erefl).
  rewrite in_cons.
  case/orP => //.
  move/eqP=> ?; subst x.
  have ha : h < a.
    apply mem_lt_lb with t => //.
    by case/ordered_inv : H.
  have ah : a < h.
    apply mem_lt_lb with b => //.
    by case/ordered_inv : ab.
  move: (ltA_trans ha ah).
  by rewrite ltA_irr.
apply uniq_leq_size in abs; last exact: ordered_uniq.
by rewrite /= tn bn ltnn in abs.
Qed.

Lemma subset_proper (a b : ord_seq) : {subset ord2seq a <= ord2seq b} -> a = b \/ proper a b.
Proof.
move=> ab.
have sz_ab : (size a <= size b)%nat.
  apply uniq_leq_size => //.
  apply ordered_uniq.
  by case: {ab}a.
rewrite leq_eqVlt in sz_ab.
case/orP : sz_ab.
  move/eqP => sz_ab.
  left.
  move: a b ab sz_ab.
  case=> a Ha.
  case=> b Hb /= ab sz_ab.
  apply uniqe_subset_size in ab => //.
  subst b.
  by rewrite (_ : Ha = Hb) //; apply proof_irrelevance.
move=> sz_ab.
by right.
Qed.

Lemma mk_ord_seq_pi l l' : l = l' -> forall (H : ordered l) (H' : ordered l'),
  mk_ord_seq H = mk_ord_seq H'.
Proof. move=> Hll' Hl Hl'. subst l. by rewrite (proof_irrelevance _ Hl Hl'). Qed.

Definition mk_ord_seq_singleton (x : A) := mk_ord_seq (ordered_singleton x).

(** addition of an element to an ordered sequence (element not added if already present) *)

Fixpoint add_ord_seq x (lst : seq A) :=
  match lst with
    | [::] => [:: x]
    | h :: t =>
      if x < h then x :: h :: t else
        if x == h then h :: t
          else h :: add_ord_seq x t
  end.

Lemma add_ord_seq_reg : forall (l1 l2 : seq A) x, ~ x \in l1 -> ~ x \in l2 ->
  add_ord_seq x l1 = add_ord_seq x l2 -> l1 = l2.
Proof.
elim=> //=.
- move=> [|h t] //= x _.
  move/negP; rewrite !in_cons; case/norP=> X Y.
  rewrite ltA_total in X.
  case/orP: X => X.
  + by rewrite X.
  + rewrite (flip ltA_trans ltA_irr X) eq_sym (lt_neq ltA_total X).
    case; move=>Z; subst.
    by rewrite ltA_irr in X.
- move=> h t IH [| h' t'] /= x.
  + move/negP; rewrite !in_cons; case/norP=> X Y _.
    rewrite ltA_total in X; case/orP: X => X.
    * by rewrite X.
    * rewrite (flip ltA_trans ltA_irr X) eq_sym (lt_neq ltA_total X).
      case; move=>Z; subst.
      by rewrite ltA_irr in X.
  + move/negP; rewrite !in_cons; case/norP=> X Y.
    move/negP; case/norP=> X' Y'.
    rewrite ltA_total in X.
    rewrite ltA_total in X'.
    case/orP: X => X.
    * rewrite X /=.
      case/orP: X' => X'.
      - rewrite X' /=.
        by case => -> ->.
      - rewrite (flip ltA_trans ltA_irr X') eq_sym (lt_neq ltA_total X').
        case; move=> Z; subst.
        by rewrite ltA_irr in X'.
    * rewrite (flip ltA_trans ltA_irr X) eq_sym (lt_neq ltA_total X).
      case/orP: X' => X'.
      - rewrite X' /=.
        case; move=> Z; subst.
        by rewrite ltA_irr in X.
      - rewrite (flip ltA_trans ltA_irr X') eq_sym (lt_neq ltA_total X').
        case=> Z Z'; subst.
        move/negP:Y=>Y; move/negP:Y'=>Y'.
        by rewrite (IH _ _ Y Y').
Qed.

Lemma add_ord_seq_lb : forall s y, lb y s -> forall x, y < x -> lb y (add_ord_seq x s).
Proof.
elim=> /=.
- move=> *; by apply/andP.
- move=> h t IH y. case/andP => H H' x Hx.
  have [-> /=| ->] : x < h \/ x < h = false by case ltA; auto.
  + apply/andP. split => //=. by apply/andP.
  + case/boolP : (x == h) => X.
    * rewrite /=.
      by apply/andP.
    * rewrite /=.
      apply/andP. split => //. by apply IH.
Qed.

Lemma add_ord_seq_ordered l : ordered l -> forall x, ordered (add_ord_seq x l).
Proof.
elim=> [| lst Hlst IH a Hlb x ]/=.
- exact ordered_singleton.
- case: ifP => H1.
  + apply ord_cons => /=.
      by apply ord_cons.
    apply/andP; split => //.
    by apply lb_trans with a.
  + case: ifP => H2.
    * by apply ord_cons.
    * apply ord_cons.
        by apply IH.
      apply add_ord_seq_lb => //.
      move/negP: H2 => /negP H2.
      by rewrite ltA_total H1 in H2.
Qed.

Lemma add_ord_seq_cat : forall l x, lb x l -> add_ord_seq x l = x :: l.
Proof. elim=> //=. move=> h t Hl x H. by move/andP : H => [-> _]. Qed.

Lemma mem_add_ord_seq : forall l x, x \in add_ord_seq x l.
Proof.
elim=> //=.
move=> x; rewrite !in_cons eq_refl //=.
move=> h t IH x.
case: ifP => X.
- by rewrite /= !in_cons eq_refl.
- case: ifP => Y.
  + move/eqP:Y=>Y; subst.
    by rewrite /= !in_cons eq_refl.
  + by rewrite /= !in_cons IH orbC.
Qed.

Lemma add_ord_seq_add_ord_seq'': forall l n, add_ord_seq n (add_ord_seq n l) = add_ord_seq n l.
Proof.
elim=> //=.
move=> n; rewrite ltA_irr eq_refl //=.
move=> h t IH n.
case: ifP => X.
- by rewrite /= ltA_irr /= eq_refl.
- case: ifP => Y.
  + by rewrite /= X Y.
  + by rewrite /= X Y IH.
Qed.

Lemma add_ord_seq_add_ord_seq': forall l n n' , n < n' ->
  add_ord_seq n (add_ord_seq n' l) = add_ord_seq n' (add_ord_seq n l).
Proof.
elim=> /=.
- move=> n n' H.
  rewrite H.
  have -> : n' < n = false.
    apply/negP; move/(ltA_trans H); by rewrite ltA_irr.
  have -> // : n' == n = false.
    apply/negP; move/eqP => ?; subst; by rewrite ltA_irr in H.
- move=> l0 l Hl n n' Hnn'.
  case: (tri ltA_total Hnn' l0) => [H | [ H | [ H | [ H | H ]]] ].
  + have H1 : n' < l0 = false.
      apply/negP => H'; move: {H'}(ltA_trans Hnn' (ltA_trans H' H)); by rewrite ltA_irr.
    rewrite H1.
    have H2 : n < l0 = false.
      apply/negP; move/(ltA_trans H); by rewrite ltA_irr.
    rewrite H2.
    have H3 : n' == l0 = false.
      apply/negP; move/eqP => ?; subst.
      move: (ltA_trans Hnn' H); by rewrite ltA_irr.
    rewrite H3.
    have H4 : n == l0 = false.
      apply/negP; move/eqP => ?; subst; by rewrite ltA_irr in H.
    by rewrite H4 /= H2 H4 H1 H3 Hl.
  + subst.
    have H1 : n' < n = false.
      apply/negP; move/(ltA_trans Hnn'); by rewrite ltA_irr.
    rewrite H1 ltA_irr eq_refl.
    have H2 : n' == n = false.
      apply/negP; move/eqP => ?; subst; by rewrite ltA_irr in Hnn'.
    by rewrite H2 /= ltA_irr eq_refl H1 H2.
  + case: H => H1 H2.
    rewrite H1.
    have H3 : n' < l0 = false.
      apply/negP => H'. move: {H'}(ltA_trans H' H2); by rewrite ltA_irr.
    rewrite H3.
    have H4 : n' == l0 = false.
      apply/negP; move/eqP => H'; subst; by rewrite ltA_irr in H2.
    rewrite H4 /= H1.
    have H5 : n' < n = false.
      apply/negP; move/(ltA_trans Hnn'); by rewrite ltA_irr.
    rewrite H5.
    have H6 : n' == n = false.
      apply/negP; move/eqP => ?; subst; by rewrite ltA_irr in Hnn'.
    by rewrite H6 H3 H4.
  + subst.
    rewrite ltA_irr eq_refl Hnn' /= Hnn'.
    have H1 : n' < n = false.
      apply/negP; move/(ltA_trans Hnn'); by rewrite ltA_irr.
    rewrite H1.
    have H2 : n' == n = false.
      apply/negP; move/eqP => ?; subst; by rewrite ltA_irr in Hnn'.
    by rewrite H2 ltA_irr eq_refl.
  + rewrite H (ltA_trans Hnn' H) /= Hnn'.
    have H1 : n' < n = false.
      apply/negP ; move/(ltA_trans Hnn'); by rewrite ltA_irr.
    rewrite H1.
    have H2 : n' == n = false.
      apply/negP; move/eqP  => H'; subst; by rewrite ltA_irr in Hnn'.
    by rewrite H2 H.
Qed.

Lemma add_ord_seq_add_ord_seq: forall l n n' , n <> n' ->
  add_ord_seq n (add_ord_seq n' l) = add_ord_seq n' (add_ord_seq n l).
Proof.
move=> l n n' Hnn'.
have [H1 | H1] : n < n' \/ n' < n.
  apply/orP.
  rewrite -ltA_total. apply/negP. contradict Hnn'. move/eqP: Hnn' => //.
- by rewrite add_ord_seq_add_ord_seq'.
- by rewrite -add_ord_seq_add_ord_seq'.
Qed.

Lemma add_ord_seq_In: forall k x a, x \in (add_ord_seq a k) -> x = a \/ x \in k.
Proof.
elim=> //= [x a|hd tl IH x a].
- case/orP => //.
  move/eqP; by left.
- case/boolP : (a < hd) => X.
  - rewrite /= !in_cons; case/orP.
    move/eqP; by left.
    case/orP.
    move=> ->; by right.
    move=> ->; rewrite orbC /=; by auto.
  - move/negbTE : X => X.
    rewrite /= !in_cons; case/boolP : (a == hd) => Y.
    + rewrite /= !in_cons; case/orP.
      move=> ->; by right.
      move=> ->; rewrite orbC /=; by auto.
    + move/negbTE : Y => Y.
      rewrite /= !in_cons; case/orP.
      move=> ->; by right.
      move=> Z; apply IH in Z.
      case:Z; auto.
      move=> ->; rewrite orbC /=; by auto.
Qed.

Definition add (x : A) : forall l : ord_seq, ord_seq.
Proof. move=> [l Hl]. exact (mk_ord_seq (add_ord_seq_ordered Hl x)). Defined.

Lemma size_add (a : A) (l : ord_seq ) : a \notin ord2seq l -> size (add a l) = (size l).+1.
Proof.
case : l a => /=.
elim=> // h t /= IH.
case/ordered_inv => H1 H2 a.
rewrite in_cons negb_or.
case/andP => ah ta.
case: ifP => // ha.
case : ifP => [/eqP ? | _ /= ].
  subst h.
  by rewrite eqxx in ah.
by rewrite IH.
Qed.

Lemma mem_add : forall (l : ord_seq) y x, (x \in ord2seq (add y l)) = (x == y) || (x \in ord2seq l).
Proof.
case.
elim=> /= [_ y x | h t IH /ordered_inv [] H1 H2 y]; first by rewrite in_cons.
case: ifP => // /negbT yh x.
case: ifP => [/eqP ? | yh'].
  subst y; by rewrite in_cons [in RHS]orb_idl // => ->.
by rewrite in_cons IH // in_cons orbCA.
Qed.

(** the union of two ordered sequences *)

Fixpoint app_ord_seq (l1 l2 : seq A) { struct l1 } :=
  match l1 with
    | [::] => l2
    | h :: t => add_ord_seq h (app_ord_seq t l2)
  end.

Lemma app_ord_seq_nil : forall l, ordered l -> app_ord_seq l [::] = l.
Proof.
elim=> // l0 l H.
case/ordered_inv => H1 H2.
rewrite /= H //.
by apply add_ord_seq_cat.
Qed.

Lemma app_ord_seq_com : forall l, ordered l -> forall l', ordered l' ->
  app_ord_seq l l' = app_ord_seq l' l.
Proof.
elim=> //= [*|l0 l IHl].
- by rewrite app_ord_seq_nil.
- case/ordered_inv => H1 H2.
  elim=> //= [_ | k0 k IHk].
  + by rewrite app_ord_seq_nil // add_ord_seq_cat.
  + case/ordered_inv => H'1 H'2.
    rewrite -IHk //=.
    case/boolP : (k0 == l0) => [/eqP ? | X ].
    * subst.
      rewrite add_ord_seq_add_ord_seq'' IHl //=; last by constructor.
      by rewrite add_ord_seq_add_ord_seq'' IHl.
    * rewrite -add_ord_seq_add_ord_seq //=; last first.
        by move/esym; apply/eqP.
      rewrite IHl //=; last by constructor.
      by rewrite IHl.
Qed.

Lemma app_ord_seq_ordered : forall l1, ordered l1 -> forall l2, ordered l2 -> ordered (app_ord_seq l1 l2).
Proof.
elim=> //= l10 l1 IH /ordered_inv [] H1 H2 l2 Hl2.
by apply add_ord_seq_ordered, IH.
Qed.

Definition app : forall l1 l2 : ord_seq, ord_seq.
Proof. move=> [l1 Hl1] [l2 Hl2]. exact (mk_ord_seq (app_ord_seq_ordered Hl1 Hl2)). Defined.

Lemma app0s : forall l, app (mk_ord_seq ord_nil) l = l.
Proof. case => l Hl /=; by apply mk_ord_seq_pi. Qed.

Lemma app_com : forall l l', app l l' = app l' l.
Proof. move=> [l Hl] [l' Hl'] /=; by apply mk_ord_seq_pi, app_ord_seq_com. Qed.

(** disjointness *)

Definition dis_ord_seq (l1 l2 : ord_seq) := dis (ord2seq l1) (ord2seq l2).

Lemma dis_ord_seq_com l1 l2 : dis_ord_seq l1 l2 = dis_ord_seq l2 l1.
Proof. by rewrite /dis_ord_seq dis_sym. Qed.

(** element removal *)

Definition dels_seq (x k : seq A) : seq A := filter (fun y => ~~ (y \in x)) k.

Lemma dels_seq_ordered l : ordered l -> forall x, ordered (dels_seq x l).
Proof. move=> H x. rewrite /dels_seq. by apply ordered_filter. Qed.

Definition dels : forall (x l : ord_seq), ord_seq.
Proof. move=> x [l H]. exact (mk_ord_seq (dels_seq_ordered H (ord2seq x))). Defined.

(** inclusion *)

Definition inc_ord (l1 l2 : ord_seq) := inc (ord2seq l1) (ord2seq l2).
End ordered_sequence.

Unset Implicit Arguments.

Arguments lb [A].
Arguments ub [A].
Arguments mem_lt_lb [A].
Arguments ordered [A].

End OrderedSequence.

(** Lemmas only for NatOrder *)

Lemma lb_iota : forall k n m, NatOrder.ltA n m -> lb NatOrder.ltA n (iota m k).
Proof.
elim=> // k IH n m H /=.
apply/andP; split; first by done.
apply IH.
rewrite /NatOrder.ltA.
by apply: (@ssrnat.ltn_trans m).
Qed.

Lemma ordered_iota : forall k n, OrderedSequence.ordered NatOrder.ltA (iota n k).
Proof.
elim => [/= _ | k IH n /=].
- by constructor.
- constructor.
  + by apply IH.
  + apply lb_iota.
    by apply: ssrnat.ltnSn.
Qed.

Section seq_addendum2.
Variable A : eqType.
Variable ltA : A -> A -> bool.
Fixpoint ord_seq_flat (l : seq (seq_eqType (seq_eqType A))) {struct l} : seq (seq_eqType A) :=
  if l is h :: t then OrderedSequence.app_ord_seq (lex ltA) h (ord_seq_flat t) else [::].
End seq_addendum2.

Module Type ORDSET.
Parameter elt : eqType.
Parameter t : Type.
Parameter singleton : elt -> t.
Parameter add : elt -> t -> t.
Parameter dels : t -> t -> t.
Parameter incl : t -> t -> bool.
Notation "k [<=] m" := (incl k m) (at level 69) : ordset_scope.
Local Open Scope ordset_scope.
Parameter union : t -> t -> t.
Notation "k [U] m" := (union k m) (at level 69) : ordset_scope.
Local Open Scope ordset_scope.
Parameter union_com : forall s s', s [U] s' = s' [U] s.
End ORDSET.

Module OrdSet (O : ORDER) : ORDSET.
Definition elt := O.A.

Import OrderedSequence.

Definition t := ord_seq O.ltA.
Definition singleton (e:elt) := mk_ord_seq_singleton O.ltA e.
Definition add := add O.ltA_trans O.ltA_total.
Definition dels : t -> t -> t := @dels O.A O.ltA.
Definition incl := @inc_ord O.A O.ltA.
Notation "k [<=] m" := (incl k m) (at level 69) : ordset_scope.
Local Open Scope ordset_scope.
Definition union := app O.ltA_trans O.ltA_total.
Notation "k [U] m" := (union k m) (at level 69) : ordset_scope.
Local Open Scope ordset_scope.
Lemma union_com : forall s s', s [U] s' = s' [U] s.
Proof.
move=> [s Hs] [s' Hs'] /=.
apply mk_ord_seq_pi, app_ord_seq_com => //;
  [exact O.ltA_trans | exact O.ltA_total | exact O.ltA_irr].
Qed.
End OrdSet.

Module ordset_of_nat := OrdSet NatOrder.

Module ordset_of_pairs_of_nat := OrdSet pair_nat_order.

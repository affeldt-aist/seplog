(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
Require Import seq_ext.
Require Import order ordset.

(** This file provides
- a section with generic definitions for lists of pairs of eqtypes
- a module with a function that adds elements to a map implemented as a lists of pairs of eqtypes.

This is for the implementation of finite maps.
*)

Set Implicit Arguments.

Section sequence_of_pairs.

Variable A B : eqType.

Lemma pair_proj (a : A) (b : B) c d : ((a, b) == (c, d)) = (a == c) && (b == d).
Proof.
case/boolP: (a == c) => X.
- move/eqP : X => X; subst.
  case/boolP : (b == d) => Y.
  + move/eqP : Y => Y; subst; by rewrite !eq_refl.
  + rewrite /=.
    apply/eqP; case => X; subst; by rewrite eq_refl in Y.
- rewrite /=.
  apply/eqP; case => Y; subst; by rewrite eq_refl in X.
Qed.

Implicit Type k : seq_eqType (prod_eqType A B).

Lemma mem_unzip1 k x y : (x, y) \in k  -> x \in unzip1 k.
Proof. move=> H. apply/mapP. by exists (x, y). Qed.

Lemma mem_unzip2 k x y : (x, y) \in k -> y \in unzip2 k.
Proof. move=> Y. apply/mapP. by exists (x, y). Qed.

Lemma not_unzip1_not_mem : forall k x, ~ fst x \in unzip1 k -> ~ x \in k.
Proof. move=> k [x1 x2] /= H; contradict H. by apply mem_unzip1 with x2. Qed.

Lemma unzip1_filter k p : unzip1 (filter (fun x => p (fst x)) k) = filter p (unzip1 k).
Proof. by rewrite /unzip1 -filter_map. Qed.

Lemma unzip1_filter' k p : unzip1 (filter (fun x => ~~ p (fst x)) k) = filter (fun x => ~~ p x) (unzip1 k).
Proof. by rewrite /unzip1 filter_map. Qed.

Lemma filter_in_cons k hd tl : hd \notin unzip1 k ->
  filter (fun x => x.1 \in hd :: tl) k = filter (fun x => x.1 \in tl) k.
Proof.
move=> H.
apply: eq_in_filter => x Hx.
rewrite in_cons.
have ->// : x.1 == hd = false.
destruct x as [x1 x2] => /=.
move: (mem_unzip1 _ _ _ Hx) => Hx'.
apply/eqP => Y; subst.
rewrite Hx' // in H.
Qed.

Lemma dis_seq_unzip1 : forall k1 k2, dis (unzip1 k1) (unzip1 k2) -> dis k1 k2.
Proof.
elim => [ // | [h1 h1'] t1 IH k2 /= ].
case: ifP => // H1 H2.
case: ifP => [H3|_].
- rewrite -H1; apply/mapP; by exists (h1, h1').
- by apply IH.
Qed.

Lemma filter_dis : forall k1 k2, dis (unzip1 k1) (unzip1 k2) -> filter (fun x => x.1 \in unzip1 k2) k1 = [::].
Proof.
elim=> [// |  [hd1 hd1'] t1 IH l2 /=].
case: ifP => // hd1_l2 t1_l2.
by apply IH.
Qed.

End sequence_of_pairs.

Module FinSetOfPairsForMap.

Section finset_map.

Variable A : eqType.
Variable ltA : A -> A -> bool.
Local Notation "x < y" := (ltA x y).
Variable ltA_trans :  forall n m p, m < n -> n < p -> m < p.
Variable ltA_total : forall m n, (m != n) = (m < n) || (n < m).
Variable ltA_irr : forall a, a < a = false.
Variable B : eqType.

(** add a pair to a map (non-destructive) *)
Fixpoint add_map (x : A) (y : B) (l : seq_eqType (prod_eqType A B)) {struct l} :=
  match l with
    | [::] => [:: (x, y)]
    | (h1, h2) :: t =>
      if x < h1 then (x, y) :: (h1, h2) :: t else
        if x == h1 then (h1, h2) :: t
          else (h1, h2) :: add_map x y t
  end.

Lemma mem_add_map : forall l x y, ~ x \in unzip1 l -> (x, y) \in add_map x y l.
Proof.
elim=> /= [x y _ | [h1 h2] /= tl IH x y].
- by rewrite !in_cons eq_refl.
- move/negP.
  rewrite in_cons negb_or.
  case/andP => H1 H2.
  case: ifP => X.
  + by rewrite /= !in_cons eq_refl.
  + rewrite (negbTE H1) /= !in_cons IH.
    by rewrite orbC.
    by apply/negP.
Qed.

Lemma in_unzip1_add_map : forall k x a b, x \in unzip1 k -> x \in unzip1 (add_map a b k).
Proof.
elim=> [ // | [h1 h2] /= tl IH x a b].
rewrite in_cons; case/orP => X.
- move/eqP : X => X; subst.
  case: (tri' ltA_total a h1) => [X | [X | X] ].
  + by rewrite X /= !in_cons eq_refl orbC.
  + subst.
    by rewrite ltA_irr //= eq_refl /= !in_cons eq_refl.
  + rewrite (flip ltA_trans ltA_irr X) /=.
    by rewrite eq_sym (lt_neq ltA_total) //= !in_cons eq_refl.
- case: (tri' ltA_total a h1) => [Y | [Y | Y] ].
  + by rewrite Y /= !in_cons X !orbT.
  + subst.
    by rewrite ltA_irr /= eq_refl /= !in_cons X orbC.
  + rewrite (flip ltA_trans ltA_irr Y) /=.
    by rewrite eq_sym (lt_neq ltA_total) //= !in_cons IH // orbC.
Qed.

Lemma in_unzip1_add_map' : forall k a b, a \in unzip1 (add_map a b k).
Proof.
elim=> /= [a _ | [h1 h2] tl IH a b ].
- by rewrite !in_cons eq_refl.
- case: (tri' ltA_total a h1) => [X | [X | X] ].
  + by rewrite X /= !in_cons eq_refl.
  + subst.
    by rewrite ltA_irr /= eq_refl /= !in_cons eq_refl.
  + by rewrite (flip ltA_trans ltA_irr X) /= eq_sym
    (lt_neq ltA_total) //= !in_cons IH orbC.
Qed.

Lemma in_add_app_inv : forall k x a b,
  x \in add_map a b k -> x = (a, b) \/ fst x \in unzip1  k.
Proof.
elim=> /= [x a b|].
- rewrite in_cons; case/orP => //.
  by move/eqP; left.
- move=> [hd1 hd2] tl IH x a b.
  have [X|X] : a < hd1 \/ a < hd1 = false by case (a < hd1); auto.
  + rewrite X /= !in_cons; case/orP.
    * by move/eqP; left.
    * case/orP=> [|Y].
      - move/eqP=> -> /=.
        by rewrite eq_refl /=; auto.
      - destruct x => /=.
        right.
        by rewrite (mem_unzip1 _ _ _ Y) orbC.
  + rewrite X /= !in_cons; case/boolP: (a == hd1) => Y.
    - case/orP => [|Z].
      * move/eqP => -> /=; rewrite eq_refl /=; by auto.
      * destruct x => /=.
        right.
        by rewrite (mem_unzip1 _ _ _ Z) orbC.
    - rewrite /= !in_cons; case/orP.
      * move/eqP => -> /=; rewrite eq_refl /=; by auto.
      * case/IH.
        - by auto.
        - move=> ->; rewrite orbC /=; by right.
Qed.

(* TODO: direct consequence of in_add_app_inv, try to remove *)
Lemma in_add_app_inv_unzip1 k x a b : x \in unzip1 (add_map a b k) -> x = a \/ x \in unzip1 k.
Proof.
case/mapP; case=> x1 x2 /=.
case/in_add_app_inv => /=.
case=> ? ? ?; subst; by left.
move=> H ?; subst; by right.
Qed.

Lemma notin_unzip1_add_map k x a b : x <> a ->
  ~ x \in unzip1 k -> ~ a \in unzip1 k -> ~ x \in unzip1 (add_map a b k).
Proof. move=> H0 H1 H2. case/in_add_app_inv_unzip1; contradiction. Qed.

Lemma add_map_comm' : forall l n n' w w', n < n' ->
  add_map n w (add_map n' w' l) = add_map n' w' (add_map n w l).
Proof.
elim=> /= [ n n' w w' H | ].
- rewrite H (flip ltA_trans ltA_irr H).
  by rewrite eq_sym (lt_neq ltA_total H).
- move=> [h1 h2] tl Hl n n' w w' Hnn'.
  case: (tri ltA_total Hnn' h1) => [H | [H | [H | [H | H] ] ] ].
  + have H1 : n' < h1 = false by apply (flip ltA_trans ltA_irr); eapply ltA_trans; eauto.
    rewrite H1.
    have H2 : n < h1 = false by apply (flip ltA_trans ltA_irr).
    rewrite H2.
    have H3 : n' == h1 = false by rewrite eq_sym; apply (lt_neq ltA_total); eapply ltA_trans; eauto.   rewrite H3.
    have H4 : n == h1 = false by rewrite eq_sym; apply (lt_neq ltA_total).
    by rewrite H4 /= H2 H4 H1 H3 Hl.
  + subst.
    have H1 : n' < n = false by apply (flip ltA_trans ltA_irr).
    rewrite H1 ltA_irr eq_refl.
    have H2 : n' == n = false by rewrite eq_sym; apply (lt_neq ltA_total).
    by rewrite H2 /= ltA_irr eq_refl H1 H2.
  + case: H => H1 H2.
    rewrite H1.
    have H3 : n' < h1 = false by apply (flip ltA_trans ltA_irr).
    rewrite H3.
    have H4 : n' == h1 = false by rewrite eq_sym; apply (lt_neq ltA_total).
    rewrite H4 /= H1.
    rewrite (flip ltA_trans ltA_irr Hnn').
    have -> : n' == n = false by rewrite eq_sym (lt_neq ltA_total Hnn').
    by rewrite H3 H4.
  + subst.
    rewrite ltA_irr eq_refl Hnn' /= Hnn'.
    rewrite (flip ltA_trans ltA_irr Hnn').
    have -> : n' == n = false by rewrite eq_sym; apply (lt_neq ltA_total).
    by rewrite ltA_irr eq_refl.
  + rewrite H (ltA_trans Hnn' H) /= Hnn'.
    rewrite (flip ltA_trans ltA_irr Hnn').
    have -> : n' == n = false by rewrite eq_sym; apply (lt_neq ltA_total).
    by rewrite H.
Qed.

Lemma add_map_comm l n n' w w' : n <> n' ->
  add_map n w (add_map n' w' l) = add_map n' w' (add_map n w l).
Proof.
move=> Hnn'.
have [H1 | H1] : n < n' \/ n' < n.
  apply/orP. rewrite -ltA_total. by move/eqP : Hnn'.
by rewrite add_map_comm'.
by rewrite -add_map_comm'.
Qed.

Lemma add_map_reg : forall (l1 l2 : seq_eqType (prod_eqType A B)) x y y',
  ~ x \in unzip1 l1 -> ~ x \in unzip1 l2 ->
  add_map x y l1 = add_map x y' l2 ->
  y = y' /\ l1 = l2.
Proof.
elim=> /=.
- move=> [| [hd1 hd2] tl] //= x y y' _.
  + by move=> _ [] ->.
  + move/negP; rewrite !in_cons; case/norP=> X Y.
    rewrite ltA_total in X.
    case/orP: X => [->//|X].
    rewrite (flip ltA_trans ltA_irr X) eq_sym (lt_neq ltA_total X).
    case; move => Z; subst.
    by rewrite ltA_irr in X.
- move=> [hd1 hd2] t IH [| [hd'1 hd'2] t'] /= x y y'.
  + move/negP; case/norP=> X Y _.
    rewrite ltA_total in X; case/orP: X => [->//|X].
    rewrite (flip ltA_trans ltA_irr X) eq_sym (lt_neq ltA_total X).
    case; move => Z; subst.
    by rewrite ltA_irr in X.
  + rewrite !in_cons.
    move/negP; case/norP=> X Y.
    move/negP; case/norP=> X' Y'.
    rewrite ltA_total in X.
    rewrite ltA_total in X'.
    case/orP: X => X.
    * rewrite X /=.
      case/orP: X' => X'.
      - rewrite X' /=.
        case; by move=> _ -> -> -> //.
      - rewrite (flip ltA_trans ltA_irr X') eq_sym (lt_neq ltA_total X').
        case; move => Z; subst.
        by rewrite ltA_irr in X'.
    * rewrite (flip ltA_trans ltA_irr X) eq_sym (lt_neq ltA_total X).
      case/orP: X' => X'.
      - rewrite X' /=.
        case; move=> Z; subst.
        by rewrite ltA_irr in X.
      - rewrite (flip ltA_trans ltA_irr X') eq_sym (lt_neq ltA_total X').
        case=> Z Z'; subst.
        move/negP : Y => Y; move/negP : Y' => Y'.
        move=> Z.
        by case: (IH _ _ y y' Y Y' Z) => -> ->.
Qed.

Lemma ocamlfind_add_map : forall k n w, ~ n \in unzip1 k ->
  ocamlfind (fun x => n == x.1) (add_map n w k) = Some (n, w).
Proof.
elim=> [| [hd1 hd2] tl IH] n w H /=.
- by rewrite eqxx.
- case/boolP : (ltA n hd1) => X.
  + by rewrite /= eq_refl.
  + case/boolP : (n == hd1) => [|Y].
    * move/eqP=> Y; subst.
      by rewrite /= !in_cons eq_refl in H.
    * rewrite /= (negbTE Y) /=.
      apply IH.
      contradict H.
      by rewrite /= !in_cons H orbC.
Qed.

Lemma ocamlfind_add_map' : forall k n w n', n <> n' -> ~ n \in unzip1 k ->
  ocamlfind (fun x => n' == x.1) (add_map n w k) =
  ocamlfind (fun x => n' == x.1) k.
Proof.
elim=> [| [hd1 hd2] tl IH] n w n' H H' /=.
- move/eqP: H.
  move/negbTE.
  by rewrite eq_sym => ->.
- move: H' => /=.
  move/negP.
  rewrite !in_cons; case/norP => H1 H2.
  case/boolP : (ltA n hd1) => X.
  + rewrite /=.
    move/eqP: H => H.
    rewrite eq_sym (negbTE H).
    case: ifP => [|Y //].
    move/eqP => ?; by subst n'.
  + rewrite /= (negbTE H1) /=.
    case/boolP : (n' == hd1) => [|Y].
    * move/eqP => ?; by subst n'.
    * apply IH => //.
      by move/negP: H2.
Qed.

Import OrderedSequence.

Lemma lb_dom_filter : forall (k : seq (A * B)) n p,
  lb ltA n (unzip1 k) -> lb ltA n (unzip1 (filter p k)).
Proof.
elim=> // hd tl IH n p /=.
case/boolP : (p hd) => X.
- rewrite /=.
  case/andP=> H1 H2; by rewrite IH // H1.
- case/andP=> H1 H2; by rewrite IH.
Qed.

Lemma ordered_unzip1_filter : forall (k : seq_eqType (prod_eqType A B)) p,
  ordered ltA (unzip1 k) -> ordered ltA (unzip1 (filter p k)).
Proof.
elim=> // hd tl IH p /=.
case/ordered_inv => H1 H2.
case: ifP => X.
- rewrite /=.
  constructor.
  by apply IH.
  by apply lb_dom_filter.
- by apply IH.
Qed.

Lemma map_filter_drop (k : seq (A * B)) : ordered ltA (unzip1 k) ->
  forall l1 l2, unzip1 k = l1 ++ l2 ->
    filter (fun x => x.1 \in l2) k = drop (size l1) k.
Proof.
move=> Hk l1.
move Hn1 : (size l1) => n1.
move: n1 k Hk l1 Hn1.
elim.
- move=> /= k Hord [|] // _ l2 /= Hl2.
  rewrite drop0.
  transitivity (filter predT k); last by rewrite filter_predT.
  apply: eq_in_filter => x Hx.
  case: x Hx => x1 x2 Hx /=.
  rewrite -Hl2.
  apply/mapP. by exists (x1, x2).
- move=> n1 IH1 k Hord [|h1 t1] // [Hl1] l2 Hk.
  case: k Hord Hk => [|hk tk] Hord Hk //.
  rewrite /= in Hk.
  case: Hk => ? Hk; subst h1.
  rewrite /= in Hord.
  case/ordered_inv : Hord => Hord1 Hord2.
  move: {IH1}(IH1 _ Hord1 _ Hl1 _ Hk) => IH1 /=.
  case: ifP => X //.
  have Htmp2 : hk.1 \in unzip1 tk.
    rewrite /unzip1 in Hk.
    by rewrite /unzip1 Hk mem_cat X orbC.
  move: (mem_lt_lb _ _ _ Hord2 _ Htmp2).
  by rewrite ltA_irr.
Qed.

Lemma map_filter_take (k : seq (A * B)) : ordered ltA (unzip1 k) ->
  forall l1 l2, unzip1 k = l1 ++ l2 ->
    filter (fun x => x.1 \notin l2) k = take (size l1) k.
Proof.
move=> Hk l1.
move Hn1 : (size l1) => n1.
elim: n1 k Hk l1 Hn1.
- move=> /= k Hord [|] // _ l2 /= Hl2.
  rewrite take0.
  transitivity (filter pred0 k); last by rewrite filter_pred0.
  apply: eq_in_filter => x Hx.
  case: x Hx => x1 x2 Hx /=.
  rewrite -Hl2.
  apply/mapP. by exists (x1, x2).
- move=> n1 IH1 k Hord [|h1 t1] // [Hl1] l2 Hk.
  case: k Hord Hk => [|hk tk] Hord Hk //.
  rewrite /= in Hk.
  case: Hk => ? Hk; subst h1.
  rewrite /= in Hord.
  case/ordered_inv : Hord => Hord1 Hord2.
  move: {IH1}(IH1 _ Hord1 _ Hl1 _ Hk) => IH1 /=.
  case/boolP : (hk.1 \in l2) => X.
  - have Htmp2 : hk.1 \in unzip1 tk.
      rewrite /unzip1 in Hk.
      by rewrite /unzip1 Hk mem_cat X orbC.
    move: (mem_lt_lb _ _ _ Hord2 _ Htmp2).
    by rewrite ltA_irr.
  - by rewrite /= IH1.
Qed.

Lemma add_map_is_cons : forall l x y, lb ltA x (unzip1 l) -> add_map x y l = (x,y) :: l.
Proof. elim=> //=. move=> [h1 h2] t Hl x y H. by move/andP : H => [-> _]. Qed.

Lemma lb_unzip1_add_map : forall l h n w, lb ltA h (unzip1 l) -> h < n ->
  lb ltA h (unzip1 (add_map n w l)).
Proof.
elim=> /=.
- move=> hd n _ _ H; by apply/andP.
- move=> [h1 h2] /= tl IH hd n w.
  move/andP => [H1 H2] Hhn.
  case: (tri' ltA_total n h1) => [X | [X | X] ].
  + by rewrite X /= Hhn H1 H2.
  + subst.
    by rewrite ltA_irr /= eq_refl /= Hhn H2.
  + rewrite (flip ltA_trans ltA_irr X) /=.
    by rewrite eq_sym (lt_neq ltA_total) //= H1 /= IH.
Qed.

Lemma ordered_unzip1_add_map : forall l n w, ordered ltA (unzip1 l) ->
  ~ n \in unzip1 l -> ordered ltA (unzip1 (add_map n w l)).
Proof.
elim=> /= [n _ _ _ | [h1 h2] /= tl IH n w H].
- by apply: ordered_singleton.
- apply ordered_inv in H; case: H => H1 H2.
  move/negP.
  rewrite !in_cons; rewrite negb_or.
  move/andP => [H3 H4].
  rewrite eq_sym.
  move/negbTE : H3 => H3.
  rewrite eq_sym H3 /=.
  case/boolP : (n < h1) => Z.
  + rewrite /=.
    constructor.
      by constructor.
    rewrite /= Z /=.
    by apply lb_trans with h1.
  + rewrite /=.
    constructor.
    apply IH => //.
    by apply/negP.
    apply lb_unzip1_add_map => //.
    move: {Z}(flip' ltA_total (negbTE Z)) => [Z|//].
    by rewrite Z eq_refl in H3.
Qed.

Lemma in_inj : forall (l : seq_eqType (prod_eqType A B)) x1 x2 y1 y2,
  ordered ltA (unzip1 l) -> (x1, x2) \in l -> (y1, y2) \in l ->
  x1 = y1 -> x2 = y2.
Proof.
elim=> //; case=> h1 h2 tl IH x1 x2 y1 y2 /=.
case/ordered_inv=> Htl Hh1.
rewrite in_cons.
case/orP => X.
- case/eqP : X => X Y; subst h1 h2.
  rewrite in_cons.
  case/orP => Y.
  + case/eqP : Y => Y Z; by subst y1 y2.
  + move=> Z; subst y1.
    move/(mem_lb ltA_irr) in Hh1.
    move/mem_unzip1 in Y.
    by rewrite Y in Hh1.
- rewrite in_cons.
  case/orP.
  + case/eqP => Y Z; subst h1 h2.
    move=> Z; subst y1.
    move/(mem_lb ltA_irr) in Hh1.
    move/mem_unzip1 in X.
    by rewrite X in Hh1.
  + move=> Y Z; subst y1.
    by apply IH with x1 x1.
Qed.

End finset_map.

End FinSetOfPairsForMap.

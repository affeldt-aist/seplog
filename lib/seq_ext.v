(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Permutation.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ssrnat_ext.

Set Implicit Arguments.
Unset Strict Implicit.

Reserved Notation "l |{ a , n )" (at level 59, no associativity).

Lemma tac_not_In_cons {A: Type} l (a1 a2 : A) : ~ List.In a1 (a2 :: nil) -> ~ List.In a1 l ->
  ~ List.In a1 (a2 :: l).
Proof.
move=> Hhd Htl /= [H|//].
apply Hhd; rewrite H /=; by auto.
Qed.

Lemma tac_not_in_app {A : Type} (l1 l2 : seq A) l :
  ~ List.In l l1 -> ~ List.In l l2 -> ~ List.In l (l1 ++ l2).
Proof. move=> H1 H2 H. case: (List.in_app_or _ _ _ H); auto. Qed.

Lemma InP {A : Type} x : forall (l : seq  A), List.In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
elim=> // h t IH /= [ ->| /IH [l1 [l2 H]]]; first by exists nil, t.
by exists (h :: l1), l2; rewrite /= H.
Qed.

Lemma In_nth {A : Type} (s: seq A) a i : i < size s -> List.In (nth a s i) s.
Proof.
elim: s a i => // h t IH a /= [ _ |i] /=.
by left.
rewrite ltnS => ti.
by right; apply IH.
Qed.

Lemma incl_app_inv {A : Type} (l1 l2 : seq A) k :
  List.incl (l1 ++ l2) k -> List.incl l1 k /\ List.incl l2 k.
Proof. move=> H; split => x Hx; apply H, List.in_or_app; auto. Qed.

Lemma incl_cons_inv_L {A : Type} a (l : seq A) k :
  List.incl (a :: l) k -> List.In a k /\ List.incl l k.
Proof.
rewrite (_ : a :: l = (a :: nil) ++ l) //.
case/incl_app_inv.
by intuition.
Qed.

Fixpoint split_n {A : Type} (l : seq A) (n : nat) {struct n} : (seq A * seq A) :=
  match n with
    | O => (nil, l)
    | S m => match l with
               | nil => (nil, nil)
               | hd :: tl =>
                 let: (one, two) := split_n tl m in
                   (hd :: one, two)
             end
  end.

(** compute an injection of from_list into to_list *)

(* given two lists to_list and from_list (from_list included in to_list),
   returns a list m of length |from_list|
   such that m_i is the index in to_list of the ith element of from_list
   *)

(* find the index c of an element v of type A in a list l *)
(*Ltac Find_var A v l c :=
  match l with
    | @cons A v ?tl => constr:(c)
    | @cons A ?hd ?tl => let x := eval compute in (S c) in Find_var A v tl x
    | @nil A => constr:(O)
  end.*)

Ltac find_indice i l :=
  match l with
    | nil => fail
    | i :: _ => constr:(0)
    | _ :: ?tl => let n := find_indice i tl in eval simpl in (n.+1)
  end.

Ltac compute_list_injection to_list from_list :=
  match from_list with
    | @cons ?A ?hd ?tl =>
      let hd' := find_indice hd to_list (*Find_var A hd to_list O*) in
      let tl' := compute_list_injection to_list tl in
      constr : (List.cons hd' tl')
    | @nil ?A => constr : (@nil nat)
  end.

Goal True.
match goal with
  | _ => let x := (compute_list_injection (O::2::3::4::5::nil)%nat (O::2::4::5::nil)%nat) in
    idtac x
end.
(* prints (0 :: 1 :: 3 :: 4 :: nil) *)
Abort.

Ltac In_tac :=
  match goal with
    | |- List.In ?ELT (@cons _ ?ELT ?LT) => apply List.in_eq
    | |- List.In ?ELT (@cons _ ?ELT' ?LT) => apply List.in_cons; In_tac
    | |- List.In ?ELT nil => fail
  end.

(* INPUT: an element and a list
   OUTPUT: true if the element is in the list, false o.w. *)
Ltac In_list v l :=
  match l with
    | @cons ?A v ?tl => constr:(true)
    | @cons ?A ?hd ?tl => In_list v tl
    | @nil ?A => constr:(false)
  end.

Ltac incl_tac :=
  match goal with
    | |- List.incl (?HD :: ?TL) ?L =>
      let tmp := In_list HD L in
        match tmp with
          | true => apply List.incl_cons ;
            [ In_tac
            |
              incl_tac
            ]
          | false => fail
        end
    | |- List.incl nil ?L =>
      by rewrite /=
  end.

(** remove an element according to a predicate on its index *)
Fixpoint remove_idx {A : Type} (l : seq A) (P : nat -> bool) (idx : nat) :=
  match l with
    | nil => nil
    | hd :: tl =>
      match P idx with
        | true => remove_idx tl P (S idx)
        | false => hd :: remove_idx tl P (S idx)
      end
  end.

Lemma mem_remove_idx (A : eqType) (h : A) : forall t P i, h \in remove_idx t P i -> h \in t.
Proof.
elim=> // h' t IH P i /=.
case: ifP => /= Pi.
  move/IH => ht; by rewrite in_cons ht orbC.
rewrite in_cons; case/orP => [/eqP -> |].
  by rewrite in_cons eqxx.
move/IH => ht; by rewrite in_cons ht orbC.
Qed.

Lemma uniq_remove_idx (A : eqType) : forall (l : seq A), uniq l -> forall p i, uniq (remove_idx l p i).
Proof.
elim=> // hd tl IH /=; case/andP; move/negP => Hhd Htl p i; case (p i) => /=.
- by apply IH.
- apply/andP; split; last by apply IH.
  apply/negP; contradict Hhd.
  by apply: mem_remove_idx Hhd.
Qed.

(* compute the positions of element k in list l (with starting index idx) *)
Ltac compute_positions1 l k idx :=
  match l with
    | @cons ?A k ?tl =>
      let new_idx := constr : (S idx) in
      let new_tl := compute_positions1 tl k new_idx in
      constr: (@cons nat idx new_tl)
    | @cons ?A ?hd ?tl =>
      let new_idx := constr : (S idx) in
      compute_positions1 tl k new_idx
    | _ =>
      constr : (@nil nat)
  end.

(* remove all the occurrences of HD in TL and return TL' ++ HD *)
Ltac remove_head_from_tail HD TL :=
  let ISDUP := In_list HD TL in
    match ISDUP with
      | false => constr: (HD :: TL)
      | true =>
        let POSITIONS := compute_positions1 TL HD O in
        let NEW_TL := eval compute in (remove_idx TL (fun x => (x \in POSITIONS)) O) in
        let NEW_HDTL := eval compute in (seq.cat NEW_TL (HD :: nil)) in
        constr : (NEW_HDTL)
    end.

Ltac remove_duplicates LST :=
  match LST with
    | @cons ?A ?HD ?TL =>
      let NEW_TL := remove_duplicates TL in
        remove_head_from_tail HD NEW_TL
    | @nil ?A => LST
  end.

Inductive permutation {A : Type} : seq A -> seq A -> Prop :=
| permutation_nil: permutation nil nil
| permutation_skip x l l' : permutation l l' -> permutation (x::l) (x::l')
| permutation_swap x y l : permutation (y::x::l) (x::y::l)
| permutation_trans l l' l'' : permutation l l' -> permutation l' l'' -> permutation l l''.

Lemma permutation_reflexive {A} : forall (l : seq A), permutation l l.
Proof. elim => //=; try constructor => //=. Qed.

Lemma permutation_symmetric {A} (l l': seq A) : permutation l l' -> permutation l' l.
Proof.
elim => //=; try constructor => //=.
intros; by apply permutation_trans with l'0.
Qed.

Require Export Setoid Relation_Definitions.

Instance permutation_Equivalence A : Equivalence (@permutation A) | 10.
constructor.
exact permutation_reflexive.
exact permutation_symmetric.
exact permutation_trans.
Defined.

Ltac swap_with_head_rec i :=
  match i with
    | O => apply permutation_swap
    | S _ => eapply permutation_trans; [
      let n := eval simpl in (i.-1) in
        apply permutation_skip;
          swap_with_head_rec n | apply permutation_swap]
  end.

Ltac swap_with_head i :=
  match i with
    | O => idtac
    | S _ => eapply permutation_trans; [
      let n := eval simpl in (i.-1) in
        swap_with_head_rec n | idtac]
  end.

Ltac setl P :=
  match P with
    | nil => idtac
    | ?hd::?tl =>
      let x := fresh in
        (set x := hd); setl tl
  end.

Ltac Solve_permutation :=
  match goal with
    | |- permutation ?l1 ?l2 =>
      setl l1
  end;
  match goal with
    | |- permutation nil nil => apply permutation_nil
    | |- permutation ?l (?hd::_) =>
      (*let i := find_indice hd l in*)
      let A := type of hd in
      let i := find_indice hd l (*Find_var A hd l O*) in
        swap_with_head i; apply permutation_skip; Solve_permutation
  end.

Goal permutation [:: 1; 3; 2] [::2; 1; 3].
Solve_permutation.
Abort.

Section disjunction_Prop.

Variable A : Type.
Implicit Type l : seq A.

Definition disj l1 l2 := forall x,
  (List.In x l1 -> ~ (List.In x l2)) /\ (List.In x l2 -> ~ (List.In x l1)).

Lemma disj_nil_R l : disj l nil. Proof. move=> x /=; tauto. Qed.

Lemma disj_nil_L l : disj nil l. Proof. move=> x /=; tauto. Qed.

Lemma disj_singl a b : a <> b -> disj (a :: nil) (b :: nil).
Proof.
move=> ab x; split; case => //= ?; subst x; contradict ab; firstorder.
Qed.

Lemma disj_sym h1 h2 : disj h1 h2 -> disj h2 h1.
Proof. rewrite /disj => H x; move: (H x); tauto. Qed.

Lemma disj_not_In L x K : disj K L -> List.In x L -> ~ List.In x K.
Proof. move=> Hinter HIn X; move: (Hinter x); tauto. Qed.

Lemma disj_cons_R x L K : disj K L -> ~ List.In x K -> disj K (x :: L).
Proof.
move=> l1_l2 x_l2; rewrite /disj => z; split => /= [z_l2|].
- contradict x_l2; case: x_l2 => [?|z_l1]; [by subst x | move: (l1_l2 z); tauto].
- case => [?|z_l1]; [by subst z | move: (l1_l2 z); tauto].
Qed.

Lemma disj_cons_L x L K : disj K L -> ~ List.In x L -> disj (x :: K) L.
Proof.
move=> l1_l2 x_l2; rewrite /disj => z; split => /= [|z_l2].
- case => [?|z_l1]; [by subst z | move: (l1_l2 z); tauto].
- contradict x_l2; case: x_l2 => [?|z_l1]; [by subst x | move: (l1_l2 z); tauto].
Qed.

Lemma disj_in_cons_R x L K : disj K L -> List.In x L -> disj K (x :: L).
Proof.
move=> l1_l2 x_l1; rewrite /disj => z; split => [z_l2|] /=.
- move: (proj1 (l1_l2 z) z_l2) => H1; contradict H1.
  case: H1; by [move=> ?; subst z | ].
- case.
  + move=> ?; subst z=> ?; move: (l1_l2 x); tauto.
  + move=> z_l1 ?; move: (l1_l2 z); tauto.
Qed.

Lemma disj_cons_inv h1 t1 l2 : disj (h1 :: t1) l2 -> disj t1 l2 /\ ~ List.In h1 l2.
Proof.
move=> H; split => [x | h1_l2].
- rewrite /disj; split=> x_t1 abs; move: (H x) => /=; by firstorder.
- move: (H h1) => /=; by firstorder.
Qed.

Lemma disj_app_inv l k m : disj (l ++ k) m -> disj l m /\ disj k m.
Proof.
move=> H; split=> x; split=> Hx abs; case: (H x) => _.
move/(_ abs). apply. apply List.in_or_app; tauto.
move/(_ Hx). apply. apply List.in_or_app; tauto.
move/(_ abs). apply. apply List.in_or_app; tauto.
move/(_ Hx). apply. apply List.in_or_app; tauto.
Qed.

Lemma disj_app : forall (l k m : seq A), disj l m /\ disj k m -> disj (l ++ k) m.
Proof.
elim => [k m [] // | h t IH k m [H1 H2] /=].
apply disj_cons_L; last first.
  move=> X.
  apply (proj1 (H1 h)); last by [].
  rewrite /=; by auto.
apply IH.
by case/disj_cons_inv : H1.
Qed.

Lemma tac_disj_incl_L l k : disj l k -> forall l', List.incl l' l -> disj l' k.
Proof.
move=> H l' H' x; split=> //=.
- move/H' => Hx abs; move: (H x); tauto.
- move => abs; move/H' => Hx; move: (H x); tauto.
Qed.

Lemma tac_disj_incl_R l k : disj l k -> forall k', List.incl k' k -> disj l k'.
Proof.
move=> H l' H' x; split=> //=.
- move => abs; move/H' => Hx; move: (H x); tauto.
- move/H' => Hx abs; move: (H x); tauto.
Qed.

Lemma disj_incl_LR k' l' k l : disj k' l' -> List.incl k k' -> List.incl l l' -> disj k l.
Proof.
move=> Hinter Hinclk Hincll x; split => // Hx abs.
- apply Hinclk in Hx; apply Hincll in abs; move: (Hinter x); tauto.
- apply Hinclk in abs; apply Hincll in Hx; move: (Hinter x); tauto.
Qed.

End disjunction_Prop.

Ltac disj_remove_duplicates_R :=
  match goal with
    | |- disj ?L (?HD :: ?TL) =>
      let tmp := remove_duplicates (HD :: TL) in
        apply (@tac_disj_incl_R _ L tmp)
end.

Ltac disj_remove_duplicates_L :=
  match goal with
    | |- disj (?HD :: ?TL) _ =>
      let tmp := remove_duplicates (HD :: TL) in
        apply (@tac_disj_incl_L _ tmp)
end.

Ltac Disj_remove_dup :=
  match goal with
    | |- disj (_ :: _) (_ :: _) =>
      ( disj_remove_duplicates_L; last by rewrite /List.incl /=; intuition ) ;
      ( disj_remove_duplicates_R; last by rewrite /List.incl /=; intuition )
    | |- disj (?HD :: ?TL) _ =>
      disj_remove_duplicates_L; last by rewrite /List.incl /=; intuition
    | |- disj _ (?HD :: ?TL) =>
      disj_remove_duplicates_R; last by rewrite /List.incl /=; intuition
  end.

Section fold.

Lemma foldl_map {A B C} (f : B -> A -> B) (f' : C -> A) : forall l acc,
  foldl f acc (map f' l) = foldl (fun acc hd => f acc (f' hd)) acc l.
Proof. by elim => //=. Qed.

Lemma foldr_map {A B C : Type} (f : A -> B -> B) (f' : C -> A) : forall l a,
  foldr f a (map f' l) = foldr (fun h a => f (f' h) a) a l.
Proof. elim=> //= h t IH Hyp; by congr (f _ _). Qed.

Lemma foldl_congr_f {A B} (f f': B -> A -> B) (Hf: forall x y, f x y = f' x y):
  forall l acc, foldl f acc l = foldl f' acc l.
Proof. elim => //= hd tl Hind acc; by rewrite Hind Hf. Qed.

Lemma foldl_ext {A : Type} {B : eqType} : forall k a (f f' : A -> B -> A),
  (forall x a, x \in k -> f a x = f' a x) ->
  foldl f a k = foldl f' a k.
Proof.
elim => // h t IH a f f' H /=.
rewrite H; last by apply mem_head.
apply IH => x a' Hx; apply H.
by rewrite in_cons Hx orbC.
Qed.

Section foldl_monotonic.

Variable (A : Type) (f : nat -> A -> nat).

Lemma foldl_leq_monotonic : (forall a x, a <= f a x) ->
  forall l a, a <= foldl f a l.
Proof. move=> Hf; elim => //= h t IH a; by apply (@leq_trans (f a h)). Qed.

Lemma foldl_ltn_monotonic : (forall a x, a < f a x) ->
  forall l a, l <> nil -> a < foldl f a l.
Proof.
move=> Hf; elim => //= h t IH a _.
apply (@ltn_leq_trans (f a h)) => //=.
apply foldl_leq_monotonic => //= a' x.
by rewrite ltnW.
Qed.

Lemma foldl_lt f' (Hf : forall x1 x2 y, x1 < x2 -> f x1 y < f' x2 y):
  forall l a1 a2, a1 < a2 -> foldl f a1 l < foldl f' a2 l.
Proof. elim=> //= h t IH a1 a2 a12; by apply IH, Hf. Qed.

Lemma foldl_le f' (Hf : forall x1 x2 y, x1 <= x2 -> f x1 y <= f' x2 y) :
  forall l a1 a2, a1 <= a2 -> foldl f a1 l <= foldl f' a2 l.
Proof. elim => //= h t IH a1 a2 a12; by apply IH, Hf. Qed.

End foldl_monotonic.

Section fold_maxn.

Lemma acc_foldl_maxn : forall l a, a <= foldl maxn a l.
Proof.
elim => //= h t IH a.
rewrite {2}/maxn.
case: leqP => //= ah.
by rewrite (@leq_trans h) // ltnW.
Qed.

Lemma in_foldl_maxn : forall l x a, x \in l -> x <= foldl maxn a l.
Proof.
elim => //= h t IH x a.
rewrite in_cons; case/orP => [/eqP -> | xt ]; last by apply IH.
rewrite (@leq_trans (maxn a h)) //; last by rewrite acc_foldl_maxn.
by rewrite leq_max orbC leqnn.
Qed.

Lemma foldr_Prop_and {A: eqType} P: forall (l: seq A),
    foldr (fun hd acc => acc /\ P hd) True l ->
    forall x, x \in l -> P x.
Proof.
elim => //=.
move => hd tl Hind Hyp.
move => x; rewrite in_cons.
move/orP => [] Hx.
- move/eqP: Hx ->.
  tauto.
- apply Hind; tauto.
Qed.

End fold_maxn.

End fold.

Section seq_Type.

Lemma take_drop {A}: forall (l: seq A) i j, take j (drop i l) = drop i (take (i + j) l).
Proof.
elim => //=.
move => hd tl Hind i j.
destruct i => //=.
destruct j => //=.
Qed.

Lemma take_take {A}: forall (l: seq A) i j, take i (take (i + j) l) = take i l.
Proof.
elim => //=.
move => hd tl Hind i j.
destruct i => //=; first by rewrite take0.
by rewrite Hind.
Qed.

Lemma all_impl_bool {A: Type} (b1 b2: A -> bool) (Hb1b2: forall x, b1 x ==> b2 x): forall l,
  all b1 l ==> all b2 l.
Proof.
elim => //=.
move => hd tl Hind.
move: (Hb1b2 hd); apply/implyP.
move: (Hind); apply/implyP.
case: (all b1 tl); case: (b1 hd); case: (all b2 tl); case: (b2 hd) => //=.
Qed.

Lemma all_impl_prop {A: Type} (b1 b2: A -> bool) (Hb1b2: forall x, b1 x ==> b2 x): forall l,
  all b1 l -> all b2 l.
  by move => l; apply/implyP; apply all_impl_bool.
Qed.

Lemma in_nseq {A : eqType} : forall n (a x : A), x \in nseq n a -> x = a.
Proof. elim=> // n IH a x /=; rewrite in_cons; case/orP; by [move/eqP | apply IH]. Qed.

Lemma drop_nseq {A : Type} : forall b a (c : A), a <= b ->
  drop a (nseq b c) = nseq (b - a) c.
Proof.
elim => [ [] // | b IH [| a]].
move=> c _; by rewrite drop0 subn0.
move=> c ab /=; by rewrite subSS IH.
Qed.

Lemma nseqS {A : Type} n (a : A) : nseq (S n) a = nseq n a ++ [:: a].
Proof. by elim: n => // n /= <-. Qed.

Section rcons_ext.

Variable A : Type.

Lemma cons_rcons : forall (tl: seq A) hd, cons hd tl = rcons (belast hd tl) (last hd tl).
Proof. by elim => //= hd tl Hind hd'; rewrite Hind. Qed.

Lemma rcons_cons_head : forall (tl: seq A) hd, rcons tl hd = cons (head hd tl) (behead (rcons tl hd)).
Proof. by elim => //= hd tl Hind hd'; rewrite Hind. Qed.

Lemma rcons_app : forall (tl: seq A) hd, rcons tl hd = tl ++ hd::nil.
Proof. by elim => //=; move => hd tl Hind hd'; rewrite Hind. Qed.

Lemma case_eq_rcons : forall (P: seq A -> Prop),
  (P nil) ->
  (forall hd tl, P (rcons hd tl)) ->
  forall l, P l.
Proof.
move=> P HPnil HPrcons.
case => //= hd tl.
rewrite cons_rcons.
apply HPrcons.
Qed.

End rcons_ext.

Lemma nth_decomp {A} {a} : forall (l : seq A) i, (size l > i) ->
  l = take i l ++ nth a l i :: drop i.+1 l.
Proof.
elim => //= hd tl Hind i Hi.
destruct i => //=; first by rewrite drop0.
by rewrite {1}(Hind i).
Qed.

Lemma take_lt {A} : forall sz' (l1 l2: seq A) sz,
  take sz l1 = take sz l2 -> sz' < sz -> take sz' l1 = take sz' l2.
Proof.
elim.
- intros; by rewrite !take0.
- intros.
  destruct l1; destruct l2.
  + by [].
  + by destruct sz.
  + by destruct sz.
  + destruct sz => //.
    simpl in H0; simpl.
    injection H0 => ? ->.
    f_equal.
    by apply H with sz.
Qed.

Lemma dropS {A} : forall (l : seq A) i, drop (S i) l = drop 1 (drop i l).
Proof. by elim => //= a l IH [|i]. Qed.

Lemma dropS' {A} : forall (l : seq A) i, drop (S i) l = drop i (drop 1 l).
Proof. case => // a l i /=; by rewrite drop0. Qed.

Lemma drop_drop {A} : forall i j (l : seq A), drop i (drop j l) = drop j (drop i l).
Proof.
elim => [|n IH] j l; first by rewrite 2!drop0.
by rewrite (dropS l n) dropS IH -(dropS' _ j) -(dropS _ j).
Qed.

Lemma drop_addn {A} : forall i j (l : seq A), drop (i + j) l = drop i (drop j l).
Proof.
elim => [|i IH] j l; first by rewrite drop0.
by rewrite addSnnS IH dropS (dropS _ i) drop_drop.
Qed.

End seq_Type.

Section cat_ext.

Variable A : Type.

Lemma app_split : forall (l : seq A) k, k <= size l ->
  exists l1, exists l2, size l1 = k /\ l = l1 ++ l2.
Proof.
elim.
- move=> [|k]; last by inversion 1.
  by exists nil; exists nil.
- move=> hd tl IH [_ | k].
    by exists nil, (hd :: tl).
  rewrite ltnS => H.
  case: {IH}(IH _ H) => l1 [l2 [H1 H2]].
  exists (hd :: l1); exists l2; split => /=; by rewrite ?H1 ?H2.
Qed.

Lemma app_app_split_R : forall (l1 l2 k1 k2 : seq A),
  l1 ++ l2 = k1 ++ k2 -> size l1 <= size k1 -> exists k1', k1 = l1 ++ k1' /\ l2 = k1' ++ k2.
Proof.
elim.
- move=> l2 k1 k2 H H'; by exists k1.
- move=> a l IH l2 [|h1 t1] //= k2 H H'.
  case: H => X H; subst h1.
  case: {IH}(IH _ _ _ H H') => k1' [H1 H2].
  exists k1'; split => //.
  by rewrite H1.
Qed.

Lemma cat_inv : forall (l1 l2 k1 k2 : seq A),
  l1 ++ l2 = k1 ++ k2 -> size l1 = size k1 ->
  l1 = k1 /\ l2 = k2.
Proof.
move=> l1 l2 k1 k2 H Hlen.
apply app_app_split_R in H; last by rewrite Hlen.
case: H => k1' [Hk1 Hl2]; subst k1 l2.
destruct k1'; first by rewrite cats0.
rewrite size_cat /= in Hlen.
exfalso.
rewrite -plusE in Hlen.
ssromega.
Qed.

End cat_ext.

Section seq_eqType.

Variable A : eqType.

Lemma mem_tail : forall tl hd (x: A), x \in tl -> x \in hd :: tl.
Proof.
elim => //= hd tl Hind hd' x Hin.
by rewrite in_cons Hin orbC.
Qed.

Lemma inP : forall l (x : A), reflect (List.In x l) (x \in l).
Proof.
elim => [x /= | h t IH x].
- rewrite in_nil; by apply ReflectF.
- rewrite /= in_cons; apply: (iffP idP).
  + case/orP => [ /eqP -> | /IH ?]; by auto.
  + case => [-> | /IH ->].
    * by rewrite eqxx.
    * by rewrite orbC.
Qed.

Lemma filter_mem_cons : forall k (n : A), uniq k -> n \in k ->
  filter (mem (cons n [::])) k = cons n [::].
Proof.
elim=> // hd tl IH n /=.
case/andP => Hk1 Hk2.
rewrite in_cons; case/orP.
- move/eqP => X; subst hd.
  rewrite /= in_cons eqxx /=.
  f_equal.
  eapply trans_eq; last by apply filter_pred0.
  apply eq_in_filter => x Hx.
  rewrite /= in_cons in_nil orbC /=.
  apply/eqP => X; subst x.
  by rewrite Hx in Hk1.
- move=> Hn.
  rewrite /= in_cons in_nil orbC /=.
  have X : hd != n.
    apply/eqP => X; subst n.
    by rewrite Hn in Hk1.
  rewrite (negbTE X).
  by apply IH.
Qed.

Lemma subset_nil {l : seq A} : {subset nil <= l}. Proof. done. Qed.

Lemma subset_cat (l : seq A) l2 (Hl2 : {subset l2 <= l}):
  forall l1, {subset l1 <= l} ->  {subset (l1 ++ l2) <= l}.
Proof.
elim => //=.
move => hd tl Hind Hsubset.
move => x Hx.
rewrite in_cons in Hx; move/orP in Hx; inversion_clear Hx.
- apply Hsubset.
  rewrite in_cons; apply/orP; left; done.
- apply Hind => //=.
  move => y Hy; apply Hsubset.
  rewrite in_cons; apply/orP; right; done.
Qed.

Lemma subset_undup : forall (l : seq A), {subset (undup l) <= l}.
Proof.
elim => //=.
move => hd tl Hind.
case: (hd \in tl); intuition.
by move => x Hx; rewrite in_cons; apply/orP; right; apply Hind.
move => x Hx; rewrite in_cons in Hx; move/orP in Hx; rewrite in_cons; apply/orP; inversion_clear Hx; try auto.
Qed.

Lemma notin_unzip1_notin {B : eqType} (x : A) (y : B): forall l,
  x \notin unzip1 l -> (x, y) \notin l.
Proof.
move=> l.
apply contra => H.
apply/mapP.
by exists (x, y).
Qed.

Lemma uniq_in_eq {B:eqType} {x} {y1} {y2}: forall (l: seq (A * B)),
  uniq (unzip1 l) -> (x, y1) \in l -> (x, y2) \in l -> y1 = y2.
Proof.
elim => //=.
move => [] hd1 hd2 //= tl Hind /andP [] Hnotin Huniq; rewrite !in_cons => /orP Hin1 /orP Hin2.
inversion_clear Hin1; inversion_clear Hin2.
- by move/eqP in H; move/eqP in H0; case: H; case: H0 => *; subst.
- move/eqP in H; case: H => *; subst.
  have Hin: hd1 \in unzip1 tl.
  + apply/mapP; exists (hd1, y2); done.
  rewrite Hin in Hnotin; done.
- move/eqP in H0; case: H0 => *; subst.
  have Hin: hd1 \in unzip1 tl.
  + apply/mapP; exists (hd1, y1); done.
  rewrite Hin in Hnotin; done.
- intuition.
Qed.

Lemma uniq_subset_notin {B: eqType} {x} {y} {l: seq (A * B)} (Hl: uniq (unzip1 l)):
  forall l',
    {subset l' <= l} ->
    (x, y) \notin l' ->
    (x, y) \in l ->
    x \notin unzip1 l'.
Proof.
elim => //=.
move => [] hd1 hd2 //= tl Hind Hsubset Hnotin Hin.
have: (hd1, hd2) \in l /\ {subset tl <= l} by split; [ apply Hsubset; rewrite in_cons; apply/orP; left; done | move => z Hz; apply Hsubset; rewrite in_cons; apply/orP; right; done].
clear Hsubset.
move => [] H Hsubset.
apply/negP => Hin2.
have: (x, y) != (hd1, hd2) /\ (x, y) \notin tl.
- rewrite in_cons negb_or in Hnotin.
  move/andP in Hnotin; done.
clear Hnotin; move => [] Hneq Hnotin.
rewrite in_cons in Hin2; move/orP in Hin2; inversion_clear Hin2; last first.
move: (Hind Hsubset Hnotin Hin).
rewrite H0; done.
clear Hind.
move/eqP in H0; subst.
have: y <> hd2.
- move => Heq; rewrite Heq in Hneq; move/eqP in Hneq; tauto.
clear Hneq; move => Hneq.
move: (uniq_in_eq Hl H Hin) => Heq.
by subst.
Qed.

Lemma undup_subset (l: seq A): forall l', {subset l' <= l} -> {subset (undup l') <= l}.
Proof.
elim => //=.
move => hd tl Hind Hsubset.
have Hsubset_tl: {subset tl <= l} by move => x Hx; apply Hsubset; apply/orP; right.
case: (hd \in tl); intuition.
move => x Hx; apply Hsubset.
rewrite in_cons in Hx; move/orP in Hx.
rewrite in_cons; apply/orP.
inversion_clear Hx; try tauto.
right; apply subset_undup; done.
Qed.

Lemma nseq_count :
  forall n (a e: A), count (pred1 a) (nseq n e) = n * (a == e).
Proof.
elim; [done | ]; move => n IH a e; simpl.
rewrite mulSn -IH; f_equal.
case_eq (a == e).
- move/idP/eqP; move => ->; f_equal; apply/eqP; reflexivity.
- move/idP => H; f_equal; apply: negbTE; apply/eqP; move => E; subst.
  apply: H; apply/eqP; reflexivity.
Qed.

Lemma uniq_belast : forall (l : seq A) e,
  uniq (e :: l) -> uniq (belast e l).
Proof.
elim/last_ind => // hd tl _ e.
rewrite belast_rcons /= rcons_uniq mem_rcons in_cons negb_or andbA.
repeat case/andP.
by move=> _ -> _ ->.
Qed.

Lemma memP : forall  l (e : A), e \in l ->
  exists l1 l2, l = l1 ++ e :: l2 /\ ~ e \in l1.
Proof.
elim => //= hd tl Hind e; rewrite in_cons => Hin.
case/boolP : (e == hd) => [/eqP Heq|/negbTE Hneq].
- subst hd; by exists nil, tl.
- move/orP: Hin => [|Hin]; first by rewrite Hneq.
  move: {Hind}(Hind e Hin) => [] l1 [] l2 [] H1 H2.
  exists (hd :: l1), l2 => //=; rewrite H1; split => //.
  contradict H2.
  move: H2; rewrite in_cons => /orP[|//]; by rewrite Hneq.
Qed.

End seq_eqType.

Section flatten_ext.

Variables A B : eqType.

Lemma in_flatten : forall {f: A -> seq B} {x} {y},
  y \in f x ->
  forall l,
    x \in l ->
    y \in flatten (map f l).
Proof.
move => f x y Hy.
elim => //=.
move => hd tl Hind.
rewrite inE; move/orP => [] //=.
- by move/eqP => <-; rewrite mem_cat; apply/orP; left.
- move => Hx; rewrite mem_cat; apply/orP; right; apply (Hind Hx).
Qed.

Lemma flatten_in : forall {f: A -> seq B} {x} {l},
    x \in flatten (map f l) ->
    exists y, x \in f y /\ y \in l.
Proof.
move => f x.
elim => //=.
move => hd tl Hind.
rewrite mem_cat; move/orP => [] //=.
- by move => Hx; exists hd; rewrite inE eq_refl.
- move => Hx; move: {Hind}(Hind Hx) => [] y [] Hy1 Hy2.
  exists y; rewrite inE.
  split => //=.
  by apply/orP; right.
Qed.

Lemma flatten_map: forall {f: A -> B} {l},
  flatten (map (map f) l) = map f (flatten l).
Proof.
move => f.
elim => //=.
by move => hd tl; rewrite map_cat => ->.
Qed.

End flatten_ext.

Section inclusion_bool.

Variable A : eqType.

Fixpoint inc (l1 l2 : seq A) :=
  if l1 isn't h1 :: t1 then true else if h1 \in l2 then inc t1 l2 else false.

Lemma incP' : forall (l1 l2 : seq A), reflect {subset l1 <= l2} (inc l1 l2).
Proof.
elim => //=.
- by move => l2; apply ReflectT.
- move => hd tl Hind l2.
  case: (@idP (hd \in l2)) => Hin.
  case: (Hind l2).
  + move => Hsubset; apply ReflectT.
    move => x //=; rewrite inE; move /orP => [] //=.
    * by move => /eqP ->.
    * by move => H; apply Hsubset.
  + move => H.
    apply ReflectF.
    move => H'; apply H.
    move => x Hx.
    apply H'.
    by rewrite inE; apply /orP; right.
  apply ReflectF.
  move => Hsubset.
  apply Hin.
  apply Hsubset.
  by rewrite inE; apply /orP; left.
Qed.

Lemma incP (l1 l2 : seq A) : reflect (List.incl l1 l2) (inc l1 l2).
Proof.
apply: (iffP idP).
- move: l1 l2; elim.
  + move=> l2 /= _ x; by inversion 1.
  + move=> h1 t1 IH /= l2.
    case: ifP => X //.
    move/IH => H x /=.
    case=> [h1_x|].
    subst x.
    by apply/inP.
    by apply H.
- move: l1 l2.
  elim => // h1 t1 IH l2 /= H.
  case: ifP => X.
  apply IH => x Hx.
  apply H.
  rewrite /=; by right.
  move: (H h1 (@or_introl _ _ (refl_equal _))).
  move/inP.
  by rewrite X.
Qed.

Lemma inc_nil_inv : forall (d : seq A), inc d [::] -> d = [::].
Proof. by case. Qed.

Lemma inc_cons_R : forall (h : A) a b, inc a b -> inc a (h :: b).
Proof.
move=> c; elim=> // h t IH b /=.
case: ifP => // h_in_b t_inc_b.
by rewrite in_cons h_in_b orbC /= IH.
Qed.

Lemma inc_refl : forall (k : seq A), inc k k.
Proof. elim=> // h t IH /=; by rewrite in_cons eqxx /= inc_cons_R. Qed.

Lemma inc_app_L : forall (l k : seq A), inc l (l ++ k).
Proof. by elim=> // h t IH k /=; rewrite in_cons eqxx /= inc_cons_R. Qed.

Lemma inc_app_R : forall (l k : seq A), inc l (k ++ l).
Proof. move=> l k. apply/incP' => x Hx; by rewrite mem_cat Hx orbC. Qed.

Lemma inc_trans : forall (l1 : seq A) l2 l3, inc l1 l2 -> inc l2 l3 -> inc l1 l3.
Proof.
elim=> // h t IH l2 l3 /=.
case: ifP => // h_l2 t_l2 l2_l3.
case: ifP.
- move=> h_l3; by apply IH with l2.
- move=> <-.
  move/incP' : l2_l3 => l2_l3; exact/l2_l3.
Qed.

Lemma inc_cons_L : forall (x : A) l1 l2, inc (x :: l1) l2 = inc l1 l2 && (x \in l2).
Proof.
move=> x l1 l2; apply/idP/idP => /=.
- by case: ifP => // x_l2 ->.
- by case/andP => /= -> x_l2; case: ifP => // <-.
Qed.

Lemma inc_cons_R_inv : forall l1 (a : A) l2, a \notin l1 -> inc l1 (a :: l2) -> inc l1 l2.
Proof.
elim.
- by move=> a l1 _ _.
- move=> hd tl IH a l2.
  rewrite in_cons negb_or; case/andP => H1 H2.
  rewrite inc_cons_L.
  case/andP => H.
  rewrite in_cons.
  case/orP => H'.
  + by rewrite eq_sym H' in H1.
  + by rewrite inc_cons_L (IH a).
Qed.

Lemma inc_cons_inv : forall (h : A) t1 t2,
  h \notin t1 -> h \notin t2 -> inc (h :: t1) (h :: t2) -> inc t1 t2.
Proof.
move=> k t1 t2 Ht1 Ht2.
rewrite /= in_cons eqxx /=.
by apply inc_cons_R_inv.
Qed.

Lemma inc_filter : forall (l1:seq A) l2, inc l1 l2 -> forall f, inc (filter f l1) (filter f l2).
Proof.
elim => // h t IH l2; rewrite inc_cons_L; case/andP => H1 H2 f /=.
case: ifP => /= f_h.
- case: ifP => [h_l2|<-].
  + by apply IH.
  + move: (mem_filter f h l2); by rewrite f_h H2.
- by apply IH.
Qed.

Lemma inc_filter_L : forall (l1 l2 : seq A),
  inc l1 l2 -> forall f : pred A, inc (filter f l1) l2.
Proof.
elim=> // h t IH l2 /=.
case: ifP => // h_in_l2 t_inc_l2 f.
case: ifP => [/= | ].
by rewrite h_in_l2 IH.
by rewrite  IH.
Qed.

Lemma inc_seq_filter_imp : forall (k : seq A) (p p': pred A),
  (forall x, x \in k -> p x -> p' x ) -> inc (filter p k) (filter p' k).
Proof.
elim => // hd tl IH p p' Himp /=.
case: ifP => X.
+ rewrite /=.
  have Y : p' hd.
    apply Himp => //.
    by rewrite in_cons eqxx.
  rewrite Y /= in_cons eqxx /=.
  apply inc_cons_R.
  apply IH => x Hx.
  apply Himp.
  by rewrite in_cons Hx orbC.
+ case: ifP => Y.
  * apply inc_cons_R, IH.
    move=> x Hx Hp; apply Himp => //.
    by rewrite in_cons Hx orbC.
  * apply IH => //.
    move=> x Hx Hp; apply Himp => //.
    by rewrite in_cons Hx orbC.
Qed.

End inclusion_bool.

Lemma inc_map_fst (A B : eqType) (l1 l2 : seq (A * B)) :
  inc l1 l2 -> inc (map (fun x => fst x) l1) (map (fun x => fst x) l2).
Proof.
move/incP' => H.
apply/incP' => x /mapP[y Hy Hxy].
move/H in Hy.
apply/mapP; by exists y.
Qed.

Lemma inc_iota : forall b b', (b <= b')%nat ->
  forall a, inc (iota a b) (iota a b').
Proof.
elim=> // b IH [|b'] //= Hb' a.
rewrite in_cons eqxx /=; by apply inc_cons_R, IH.
Qed.

Lemma incl_iota : forall a n b m, (b <= a)%coq_nat -> (n + (a - b) <= m)%coq_nat ->
  List.incl (iota a n) (iota b m).
Proof.
move=> a n b m b_a n_m c /inP; rewrite mem_iota => H.
apply/inP; rewrite mem_iota; apply/andP; split; ssromega.
Qed.

Section disjointness_bool.

Variable A : eqType.
Implicit Type l : seq A.

Fixpoint dis l1 l2 :=
  match l1 with
    | h :: t => if h \in l2 then false else dis t l2
    | nil => true
  end.

Lemma disP : forall l1 l2, reflect (disj l1 l2) (dis l1 l2).
Proof.
elim=> /= [l2|h t IH l2].
- by apply ReflectT, disj_nil_L.
- apply: (iffP idP) => [|H].
  + case: ifP => // h_l2 t_l2.
    apply disj_cons_L; by [apply/IH | apply/inP; rewrite h_l2].
  + case/(@disj_cons_inv A) : H; move/IH => H.
    by move/inP /negbTE=> ->.
Qed.

Lemma dis_inc_L l k : dis l k -> forall l', inc l' l -> dis l' k.
Proof. by move/disP => ? l' /incP ?; apply/disP/tac_disj_incl_L; eauto. Qed.

Lemma dis_inc_R l k : dis l k -> forall k', inc k' k -> dis l k'.
Proof. by move/disP => ? l' /incP ?; apply/disP/tac_disj_incl_R; eauto. Qed.

Lemma dis_inc (l k' k : seq A) : dis l k' -> inc k k' -> dis l k.
Proof. by move=> lk' kk'; apply: dis_inc_R; eauto. Qed.

Lemma dis_cons : forall l' l (x : A), dis (x :: l) l' = dis l l' && ~~ (x \in l').
Proof. move=> l' l x /=; case: ifP=> _; by rewrite andbC. Qed.

Lemma dis_filter : forall l1 l2, dis l1 l2 -> forall f, dis (filter f l1) l2.
Proof.
elim=> // h t IH l2 /=.
case: ifP => // h_l2 t_l2 f.
case: ifP => /=; by rewrite ?h_l2 IH.
Qed.

Lemma dis_filter_split : forall (p q : pred A) l l',
  (forall b, (p b -> ~~ q b) /\ (q b -> ~~ p b)) ->
  dis (filter p l) (filter q l').
Proof.
move=> p q; elim => // hd tl IH l' H; apply/disP; split=> /=.
- case: ifP => p_hd.
  + have q_hd : ~~ q hd by move: (proj1 (H _) p_hd).
    rewrite /=; case=> [hd_x|].
    * apply/inP; by rewrite mem_filter negb_and -hd_x q_hd.
    * move/negP : q_hd => q_hd Hx.
      contradict q_hd.
      move/(IH l')/disP : H.
      move/(_ x); tauto.
  + case/boolP : (q hd) => [q_hd Z | ? ?];
      move/(IH l')/disP : H; move/(_ x); tauto.
- case: ifP => p_hd Hx.
  + apply/inP.
    rewrite /= in_cons negb_or.
    move/(IH l')/disP : (H) => {IH}.
    move/(_ x)/proj2/(_ Hx)/inP => ->.
    rewrite andbC /=.
    apply/eqP => ?; subst.
    have q_hd : ~~ q hd by move: (proj1 (H _) p_hd).
    move/inP : Hx.
    by rewrite mem_filter (negbTE q_hd).
  + move/(IH l')/disP : H.
    by move/(_ x)/proj2/(_ Hx).
Qed.

Lemma dis_sym l l' : dis l l' = dis l' l.
Proof. apply/disP/disP; by move/disj_sym. Qed.

Lemma dis_filter_right l1 l2 : dis l1 (filter (fun x => ~~ (x \in l1)) l2).
Proof.
elim: l2 l1 => /= [l1|h t IH l1].
- by rewrite dis_sym.
- move: (IH l1) => IH'.
  case: ifP => //= h_l1.
  by rewrite dis_sym /= (negbTE h_l1) dis_sym.
Qed.

Lemma dis_not_in : forall l l' (x : A), x \in l -> dis l l' -> ~~ (x \in l').
Proof.
elim=> // h t IH l' x.
rewrite in_cons.
case/orP => Hx /=.
- move/eqP : Hx => ?; subst h; by case: ifP.
- case: ifP => // h_l' t_l'; by apply IH.
Qed.

Lemma dis_nil_R l : dis l [::]. Proof. by rewrite dis_sym. Qed.

Lemma dis_singl x y : x != y = dis [:: x] [:: y].
Proof. by rewrite /= in_cons in_nil orbC. Qed.

End disjointness_bool.

Lemma dis_seq_singl x n l : x < n -> dis (iota n l) (x :: nil).
Proof.
move=> x_n; apply/disP => x1; split => /=.
  move/inP; rewrite mem_iota => ?; ssromega.
case=> // ?; subst x1.
move/inP; rewrite mem_iota => ?; ssromega.
Qed.

Lemma dis_seq_singl2 x n l : n + l <= x -> dis (iota n l) (x :: nil).
Proof.
move=> Hxn; apply/disP => y; split => [/inP /= H1|/=].
  rewrite mem_iota in H1; ssromega.
case=> // ?; subst y.
move/inP; rewrite mem_iota => ?; ssromega.
Qed.

Lemma disj_iota_iota a l b k : a + l <= b -> dis (iota a l) (iota b k).
Proof.
move=> H; apply/disP => x1; split => /inP;
  rewrite mem_iota => ? /inP; rewrite mem_iota => ?; ssromega.
Qed.

Lemma dis_iota a a' b c : a + b <= a' -> dis (iota a b) (iota a' c).
Proof.
move=> b'b.
apply/disP => x; split.
  move/inP.
  rewrite mem_iota => Hx.
  move/inP.
  rewrite mem_iota => ?; by ssromega.
move/inP.
rewrite mem_iota => Hx.
move/inP.
rewrite mem_iota => ?; by ssromega.
Qed.

Ltac dis_iota_tac :=
  match goal with
    | |- is_true (dis (iota ?a ?b) (?c :: nil)) =>
      apply dis_seq_singl; ssromega

    | |- is_true (dis (iota ?a ?b) (?c :: nil)) =>
      apply dis_seq_singl2; ssromega

    | |- is_true (dis (?c :: nil) (iota ?a ?b)) =>
      rewrite dis_sym; apply dis_seq_singl; ssromega

    | |- is_true (dis (?c :: nil) (iota ?a ?b)) =>
      rewrite dis_sym; apply dis_seq_singl2; ssromega

    | |- is_true (dis (iota ?a ?b) (iota ?c ?d)) =>
      apply disj_iota_iota; ssromega

    | |- is_true (dis (?a :: nil) (?b :: nil)) =>
      apply dis_singl; ssromega
  end.

(*Lemma filter_not_app : forall l1 l2, dis l1 l2 ->
  filter (fun x : nat => ~~ (x \in l2)) (l1 ++ l2) = l1.
Proof.
elim=> //= [l2 _ | h t IH l2 Hdis].
- move: (@seq.eq_in_filter _ (fun x : ssrnat.nat_eqType => ~~ (x \in l2)) xpred0 l2).
  rewrite seq.filter_pred0.
  move=> <- // i Hi /=.
  by apply/negbF.
- case: ifP Hdis => // Hdis t_l2; by rewrite IH.
Qed.*)

Section OCamlFind.

Variable A : eqType.
Variable a : pred A.

Fixpoint ocamlfind s := if s is x :: s' then if a x then Some x else ocamlfind s' else None.

Lemma ocamlfind_cons hd tl : a hd -> ocamlfind (hd :: tl) = Some hd.
Proof. move=> H; by rewrite /ocamlfind H. Qed.

Lemma ocamlfind_cons' hd tl : ~ a hd -> ocamlfind (hd :: tl) = ocamlfind tl.
Proof. move/negP => H; by rewrite {1}/ocamlfind -/(ocamlfind tl) (negbTE H). Qed.

Lemma ocamlfind_cons'' hd tl r : ocamlfind (hd :: tl) = Some r -> a hd \/ ocamlfind tl = Some r.
Proof.
rewrite /ocamlfind  -/(ocamlfind tl).
case: ifP => X; by auto.
Qed.

Lemma ocamlfind_Some_mem : forall k r, ocamlfind k = Some r -> a r /\ r \in k.
Proof.
elim=> [|hd tl IH] // r.
rewrite {1}/ocamlfind -/(ocamlfind tl).
case: ifP => X.
- case=> Y; subst.
  rewrite !in_cons /= eq_refl //=.
- move=> H /=.
  apply IH in H.
  case:H => H1 H2.
  rewrite !in_cons orbC // H2; auto.
Qed.

End OCamlFind.

Fixpoint delete1 {A : eqType} (l : seq A) e : seq A :=
  match l with
    | nil => nil
    | hd::tl =>
      if e == hd then tl else hd :: delete1 tl e
  end.

Section association_list.

Fixpoint assoc_get {A : eqType} {B : Type} (a : A) (l : seq (A * B)) : option B :=
  match l with
    | nil => None
    | h :: t => if h.1 == a then Some h.2 else assoc_get a t
  end.

Lemma assoc_get_in {A B : eqType} : forall (l : seq (A * B)) (a : A) b,
  assoc_get a l = Some b -> (a, b) \in l.
Proof.
elim => //=; case=> hd1 hd2 tl Hind /= a b.
case: ifP.
- move/eqP => -> [] ->; rewrite inE => //=; apply/orP; left; apply (eq_refl _).
- by move => _ Hassoc; rewrite inE; apply/orP; right; apply Hind.
Qed.

Lemma in_assoc_get {A B : eqType} : forall (l : seq (A * B)) (a : A) b,
  uniq (unzip1 l) ->
  (a, b) \in l ->
  assoc_get a l = Some b.
Proof.
elim=> // h t IH a b /= /andP[] ht ut.
rewrite in_cons.
case/orP => [/eqP ? | abt].
  subst h => /=; by rewrite eqxx.
case: ifP => [/eqP ? | h1a].
  exfalso.
  subst a.
  move/negP : ht; apply.
  apply/mapP; by exists (h.1, b).
exact: IH.
Qed.

Lemma assoc_get_subset_in {A B : eqType} (l: seq (A * B)) : forall
  (Hl: uniq (unzip1 l)) (l': seq (A * B)) (Hl': {subset l' <= l}) (a: A) (b: B),
  (a, b) \in l' ->
  assoc_get a l = Some b.
Proof.
move=> Hl l' l'l a b abl'.
apply in_assoc_get => //.
exact: l'l.
Qed.

Lemma assoc_get_delete_neq {A B : eqType} : forall (l : seq (A * B)) a x,
  a <> x -> forall y, assoc_get a (filter (predC (pred1 (x, y))) l) = assoc_get a l.
Proof.
elim => //=; case=> h1 h2 t IH a x ax y /=.
case: ifPn => [H1|] /=.
  case: ifP => [_ // | H2].
  by rewrite IH.
rewrite negbK => /eqP[? ?]; subst x y.
rewrite eq_sym; move/eqP/negbTE : (ax) => ->.
by rewrite IH.
Qed.

Lemma assoc_get_subset {A B : eqType} (l : seq (A * B)) :
  forall (Hl : uniq (unzip1 l)) (l' : seq (A * B)) (Hl': {subset l' <= l}) (a : A) (b : B),
  assoc_get a l' = Some b ->
  assoc_get a l = Some b.
Proof.
move=> Huniq l' Hsubset a b Hassoc.
apply assoc_get_subset_in with l' => //=.
exact: (assoc_get_in Hassoc).
Qed.

Fixpoint assoc_upd {A : eqType} {B : Type} (a : A) (b : B) (l : seq (A * B)) : seq (A * B) :=
  match l with
    | nil => nil
    | hd :: tl => if hd.1 == a then (a, b) :: tl else hd :: assoc_upd a b tl
  end.

Lemma assoc_get_upd_eq {A : eqType} {B} : forall (l : seq (A * B)) a b c,
  assoc_get a l = Some c ->
  assoc_get a (assoc_upd a b l) = Some b.
Proof.
elim => //=.
move => [] hd1 hd2 //= tl Hind a b c H.
case: (hd1 =P a) => H' //=.
- by rewrite eq_refl.
- case: (hd1 =P a) H => H'' //=.
  apply Hind.
Qed.

Lemma assoc_get_upd_neq {A : eqType} {B : Type} :
  forall (l : seq (A * B)) (a b : A) (c : B),
  a <> b -> assoc_get a (assoc_upd b c l) = assoc_get a l.
Proof.
elim=> // h t IH a b c ab /=.
case: ifP => [|Hif].
- move/eqP => ? /=; subst b.
  move/eqP in ab.
  by rewrite eqtype.eq_sym (negbTE ab).
- case: ifP => [/= -> // |/= ->]; by apply IH.
Qed.

Lemma assoc_get_upd_neq_inv {A : eqType} {B} : forall (l : seq (A*B)) a b c d,
  assoc_get a (assoc_upd b c l) = Some d ->
  a <> b ->
  assoc_get a l = Some d.
Proof.
elim=> // h t IH a b c d /=.
case: ifP => [|Hif].
- move/eqP => <- /= H.
  move/eqP.
  rewrite eqtype.eq_sym.
  move/negbTE => X; by rewrite X in H *.
- move=> /=.
  case: ifP => // Hif2.
  exact: IH.
Qed.

Lemma assoc_upd_inv {A : eqType} {B : Type} (a : A) :
  forall (l : seq (A * B)) b,
    assoc_get a l = Some b ->
    assoc_upd a b l = l.
Proof.
elim =>//=.
move => [] hd1 hd2 //= tl Hind b.
case: (hd1 =P a) => //=.
- by move => ?; case => ?; subst.
- move => _ H; by rewrite Hind.
Qed.

End association_list.

Section slice.

Definition slice {A : Type} (l : seq A) (a n : nat) := take n (drop a l).
Local Notation "l |{ a , n )" := (slice l a n).

Lemma slice_shift {A} : forall d (l1 l2 : seq A) i1 i2 sz sz',
  l1 |{ i1, sz ) = l2 |{ i2, sz) ->
  d + sz' < sz ->
  l1 |{ i1 + d, sz') = l2 |{ i2 + d, sz').
Proof.
move=> d l1 l2 i1 i2 sz sz' H H0.
rewrite /slice !drop_addn (drop_drop i1 d) (drop_drop i2 d) take_drop (take_drop _ d sz').
f_equal.
by apply take_lt with sz.
Qed.

Lemma size_slice_leq {A : Type} : forall (l : seq A) b a, size (l |{ a , b)) <= b.
Proof.
move=> l b a; rewrite /slice size_take size_drop ltn_subRL.
case: ifP => // /negbT; by rewrite -leqNgt -leq_subLR.
Qed.

Lemma size_slice_exact {A : Type} : forall (l : seq A) (b a : nat),
  a + b <= size l -> size (l |{ a, b)) = b.
Proof.
elim.
  by case=> //= n [].
move=> h t IH b [|a] /=.
- rewrite add0n leq_eqVlt.
  case/orP.
    move/eqP => ->.
    by rewrite /slice /= size_take ltnn.
  by rewrite /slice drop0 size_take /= => ->.
- rewrite addSn => H.
  by rewrite /slice /= IH.
Qed.

Lemma slice_app {A : Type} : forall (l : seq A) a b c,
  l |{ a, b + c ) = l |{ a, b) ++ l |{ a + b, c).
Proof.
elim=> // h t IH [|a] b c.
- rewrite /slice drop0 take_drop.
  rewrite (_ : take b (h :: t) = take b (take (b + c) (h :: t))); last by rewrite take_take.
  by rewrite cat_take_drop.
- move=> /=.
  exact: IH.
Qed.

Lemma nth_slice {A} (l : seq A) start sz i def (_ : i < sz) :
  nth def (slice l start sz) i = nth def l (start + i).
Proof. by rewrite /slice take_drop nth_drop nth_take // ltn_add2l. Qed.

Lemma nth_slices {A} start' sz' (l l' : seq A) start sz i def:
  start <= i < start + sz ->
  0 < sz <= sz' ->
  slice l start sz = slice l' start' sz' ->
  nth def l i = nth def l' (start' + (i - start)).
Proof.
move=> /andP Hi /andP Hsz Hl.
have Harith1 : i - start < sz by rewrite ltn_sub_add; tauto.
rewrite {1}(_ : i = start + (i - start)); last by rewrite subnKC //; tauto.
rewrite -(@nth_slice _ _ _ sz _ _) // Hl (@nth_slice _ _ _ sz' _ _) //.
eapply (ltn_leq_trans sz); tauto.
Qed.

Lemma slices_sem {A} (l : seq A) i sz : l = take i l ++ slice l i sz ++ drop (i+sz) l.
Proof. by rewrite /slice take_drop -{1}(take_take _ _ sz) catA !cat_take_drop. Qed.

End slice.

Notation "l |{ a , n )" := (slice l a n) : seq_ext_scope.

Definition map_indices {A : Type} (def : A) (l : seq A) (indices : seq nat) : seq A :=
  map (nth def l) indices.

Lemma map_indices_iota {A : Type} {def : A} : forall sz i (l : seq A),
  i + sz <= size l ->
  map_indices def l (iota i sz) = take sz (drop i l).
Proof.
rewrite /map_indices.
elim => //=.
- move => i l _.
  by rewrite take0.
- move => n Hind i l.
  destruct i => //=.
  + destruct l => //=.
    move => Hlt; rewrite Hind //=; rewrite drop0 //=.
  + destruct l => //=.
    move => Hlt; rewrite Hind //=; last by move: Hlt; nat_norm.
    rewrite (@drop_nth _ def i l) => //=.
    ssromega.
Qed.

Lemma map_indices_self {A : Type} {def : A} (l : seq A) :
  map_indices def l (iota O (size l)) = l.
Proof.
rewrite map_indices_iota.
  by rewrite drop0 take_size.
by rewrite add0n.
Qed.

Lemma seq_forall_exists :
  forall {T : eqType} (P : T -> nat -> Prop),
    (forall y i a, P y i -> P y (i + a)) ->
    forall (Y : seq T),
    (forall y, y \in Y -> exists i : nat, P y i) ->
    exists i : nat, forall y, y \in Y -> P y i.
Proof.
  move => T P closed.
  elim => [ | y0 Y]; [ move => _; exists 0 => y; done | ].
  move => IH H; move: (H y0).
  rewrite in_cons eq_refl.
  case; [ done | ].
  move => i0 Pyi0.
  have IH' : exists i : nat, forall y : T, y \in Y -> P y i.
  - apply: IH => y I; apply: H.
    rewrite in_cons; apply/orP; right; assumption.
  move: IH => _; case: IH' => i1 IH; exists (maxn i0 i1).
  move => y; rewrite in_cons; case/orP.
  - move/eqP => I; subst;
    have -> : maxn i0 i1 = i0 + (maxn i0 i1 - i0)
    by rewrite subnKC; [done | ]; exact: leq_maxl.
    apply: closed; assumption.
  - move => I.
    have -> : maxn i0 i1 = i1 + (maxn i0 i1 - i1)
    by rewrite subnKC; [done | ]; exact: leq_maxr.
    apply: closed; apply: IH; assumption.
Qed.

Section repeated_take.

Variable A : Type.

Fixpoint takes' (k : nat) (n : nat)(* size argument *) (l : seq A) {struct n} : list (seq A) :=
  match n with
    | O => nil
    | S m => take k l :: takes' k (m - (k - 1)) (drop k l)
  end.

Definition takes (k : nat) (l : seq A) : seq (seq A) :=
  match k with
    | O => nil
    | S _ => takes' k (size l)(* size_argument*) l
  end.

Lemma takes_nil n : takes n (@nil A) = nil. Proof. by case: n. Qed.

Lemma takes_skipn : forall n (l : seq A) hd tl,
  takes n l = hd :: tl -> takes n (drop n l) = tl.
Proof.
move=> [|n] // [|l1 l2] // [|hd1 hd2] // tl [] ?; subst hd1 => Hhd2.
rewrite /= subSS subn0 /= => <-.
by rewrite size_drop.
Qed.

Lemma len_takes' n : forall (l : seq A), size l = n -> forall k q,
  n = q * S k -> size (takes' (S k) n l) = q.
Proof.
induction n using Wf_nat.lt_wf_ind.
destruct n as [|n]; first by case=> // _ k [|q].
case=> hd tl // [Hlen] k [|q] //= n_k; rewrite subSS subn0; f_equal.
apply H.
  apply/ltP.
  rewrite ltnS.
  by rewrite leq_subLR leq_addl.
  by rewrite size_drop Hlen.
rewrite mulSn addSn in n_k.
case: n_k => ->.
by rewrite mulnC mulSn addnC addnK.
Qed.

Lemma len_takes n : forall (l : seq A), size l = n -> forall k q,
  n = q * S k -> size (takes (S k) l) = q.
Proof.
induction n using Wf_nat.lt_wf_ind.
destruct n as [|n]; first by case=> // _ k [|q].
case=> hd tl // [Hlen] k [|q] //= n_k; rewrite subSS subn0; f_equal.
have /ltP Htmp : n - k < S n by rewrite ltnS leq_subLR leq_addl.
move: (H _ Htmp (drop k tl)).
rewrite size_drop Hlen.
move/(_ (refl_equal _) k q).
rewrite /takes.
rewrite size_drop Hlen.
apply.
case : n_k => ->.
by rewrite plusE addnC addnK.
Qed.

Lemma In_takes' : forall n (l : seq A), size l = n -> forall k q,
  (n = q * S k) -> forall x, List.In x (takes (S k) l) -> size x = (S k).
Proof.
move=> n; induction n using Wf_nat.lt_wf_ind.
destruct n as [|n]; first by case=> // _ k [|q].
case=> hd tl // [Hlen] k [|q] // n_k x.
rewrite /=; case.
  destruct x as [|hx tx]; first by [].
  case=> ? ?; subst hx tx => /=.
  f_equal.
  rewrite size_take Hlen.
  rewrite -ltnS n_k.
  rewrite mulSn.
  destruct q.
    rewrite mul0n addn0 ltnn.
    by rewrite mul1n in n_k; case: n_k.
  rewrite mulnS (addSn q) addnS.
  by rewrite leq_addr.
rewrite subSS subn0.
move=> H1.
have /ltP H2 : ((n - k) < S n).
  by rewrite ltnS leq_subLR leq_addl.
have H3 : size (drop k tl) = (n - k) by rewrite size_drop Hlen.
apply (H (n - k) H2 (drop k tl) H3 k q).
  rewrite /= in n_k.
  case: n_k => ->.
  by rewrite plusE addnC addnK.
by rewrite /takes size_drop.
Qed.

Lemma In_takes n (l : seq A) : size l = n -> forall k q,
  (n = q * k) -> forall x, List.In x (takes k l) -> size x = k.
Proof. move=> Hlen [] //; by apply In_takes'. Qed.

Lemma takes_app : forall t (H : t <> O) (a b : seq A), size a = t ->
  takes t (a ++ b) = a :: takes t b.
Proof.
move=> t Ht a b Ha.
destruct t => //= {Ht}.
rewrite (_ : size (a ++ b) = S (t + size b)); last by rewrite size_cat /= Ha /=.
destruct a as [|ha ta] => //.
case: Ha => Ha.
by rewrite /= subSS subn0 drop_cat // take_cat // Ha ltnn subnn take0 cats0 addnC addnK drop0.
Qed.

End repeated_take.

(* TODO: move outside? *)
Lemma takes_inj {A : Type} : forall n k nk (l1 l2 : seq A), k <> O ->
  nk = (k * n)%nat -> size l1 = nk -> size l2 = nk ->
  takes k l1 = takes k l2 -> l1 = l2.
Proof.
elim.
  move=> k nk l1 l2 Hk.
  rewrite muln0 => ->.
  destruct l1 => //.
  by destruct l2.
move=> n IH k nk l1 l2 Hk Hnk Hl1 Hl2 H.
rewrite -addn1 mulnDr muln1 in Hnk.
rewrite -(cat_take_drop k l1) -(cat_take_drop k l2).
rewrite -(cat_take_drop k l1) // -(cat_take_drop k l2) // in H.
rewrite (@takes_app _ k) // in H; last by rewrite size_takel // Hl1 Hnk leq_addl.
rewrite (@takes_app _ k) // in H; last by rewrite size_takel // Hl2 Hnk leq_addl.
case: H => H1 H2.
f_equal => //.
apply (IH k (k * n)%nat) => //.
by rewrite size_drop // Hl1 Hnk addnK.
by rewrite size_drop // Hl2 Hnk addnK.
Qed.

Definition injection {A B : Type} (f : A -> B) :=
  forall x y, f x = f y -> x = y.

Lemma map_inj (A B : Type) : forall (f : list A -> B), injection f ->
  forall n (a b : list (list A)) ,
  size a = n -> size b = n ->
  map f a = map f b -> a = b.
Proof.
move=> f Hf.
elim => [ | n IH [|ha ta] // [|hb tb] // [Ha] [Hb] /=].
  case=> //; by case.
by case => /Hf <- /(IH _ _ Ha Hb) <-.
Qed.

Section flat_map.

Variable A B : Type.

Fixpoint flat_map (f : A -> seq B) l :=
  match l with
  | [::] => [::]
  | x :: t => (f x ++ flat_map f t)
  end.

Implicit Type l : seq A.
Implicit Type k : seq B.

Lemma len_flat_map : forall n l m (f : A -> seq B),
  (forall a, size (f a) = m) -> size l = n ->
  size (flat_map f l) = n * m.
Proof.
elim=> [[]// |n IHn [|h t] // k f f_k [len_t] /=].
by rewrite size_cat (IHn _ k) // f_k.
Qed.

Lemma len_flat_map_inv : forall l q m (f : A -> seq B),
  size (flat_map f l) = q * m ->
  (forall a, size (f a) = m) ->
  m <> O ->
  size l = q.
Proof.
elim=> /=.
  move=> q k f /esym/eqP.
  rewrite muln_eq0.
  by case/orP => /eqP -> //.
move=> hd tl IH [|q] k f Hlen H Hk.
  rewrite size_cat H /= mul0n in Hlen.
  move/eqP in Hlen.
  rewrite addn_eq0 in Hlen.
  case/andP : Hlen => /eqP Hlen _.
  by rewrite Hlen in Hk.
f_equal.
apply IH with k f => //.
rewrite /= size_cat /= H mulSn in Hlen.
move/eqP : Hlen.
by rewrite eqn_add2l => /eqP.
Qed.

Lemma flat_map_inj : forall (f : A -> seq B), injection f ->
  (exists k: nat, k <> O /\ forall a, size (f a) = k) ->
  forall l1 l2, flat_map f l1 = flat_map f l2 -> l1 = l2.
Proof.
move=> f f_inj [k [Hk Hf]].
elim=> /=.
- case=> //= h2 t2 abs.
  suff : False by done.
  move: (Hf h2) => abs'.
  destruct (f h2) => //.
  by subst k.
- move=> h1 t1 IH [|h2 t2] /=.
  move: (Hf h1).
  destruct (f h1) => //.
  move=> ?; by subst k.
  move=> H.
  apply cat_inv in H; last by rewrite Hf.
  rewrite (IH t2); last by tauto.
  f_equal.
  apply f_inj; tauto.
Qed.

End flat_map.

Fixpoint upd_nth {A : Type} (l : seq A) (n : nat) (v : A) {struct l} : seq A :=
  match l with
    | nil => nil
    | hd :: tl => match n with
		  | O => v :: tl
		  | S n' => hd :: upd_nth tl n' v
		end
  end.

Lemma size_upd_nth {A : Type} : forall n (l : seq A) k (v : A),
  size l = n -> size (upd_nth l k v) = n.
Proof. elim => [ [] // | n IHn [|hd tl] // [|k] // v [H] /= ]; by rewrite IHn. Qed.

Lemma upd_nth_cat {A : Type} : forall n l (a : A), size l <= n ->
  forall l', upd_nth (l ++ l') n a = l ++ upd_nth l' (n - size l) a.
Proof. elim=> [ [] // | n H [ // |h t]] v H0 l'; by rewrite /= H. Qed.

Lemma upd_nth_cat' (A: Type) : forall n l (a : A), n < size l ->
  forall l', upd_nth (l ++ l') n a = (upd_nth l n a) ++ l'.
Proof.
Proof. elim=> [ [] // | n H [ // |h t]] v H0 l'; by rewrite /= H. Qed.

Lemma nth_upd_nth {A : Type} : forall n (a : A) l def,
  n < size l -> nth def (upd_nth l n a) n = a.
Proof. elim => [m [|] // | n H m [ // |h t] def_val H0 /=]; by rewrite H. Qed.

Lemma nth_upd_nth' {A : Type} : forall l n n' (a : A) def, n <> n' ->
  nth def (upd_nth l n' a) n = nth def l n.
Proof. elim=> [ // |h t IH] [|n] [|n'] m def_val /= H //; rewrite IH // => nn'; by subst. Qed.

Lemma drop_upd_nth {A : Type} : forall l n (a : A) m, (n < m)%nat ->
  drop m (upd_nth l n a) = drop m l.
Proof. elim => //= h t IH [|n] /= e [|m] //=; rewrite ltnS => nm; by rewrite IH. Qed.

Lemma take_upd_nth {A:Type} : forall lst n (m:A),
  take n (upd_nth lst n m) = take n lst.
Proof. elim => // hd tl IH [|n0] //= m. by rewrite IH. Qed.

Section index_deletion.

Variable A : Type.

Fixpoint idel (n : nat) (l : seq A) {struct l} : seq A :=
  if l isn't hd :: tl then nil else
    (if n isn't S n' then tl else hd :: idel n' tl).

Lemma size_idel : forall (s : seq A) n, n < size s ->
  size (idel n s) = size s - 1.
Proof.
elim => // a l IH [|n] /=.
- by rewrite subn1.
- rewrite ltnS => H0; rewrite IH // -subSn //; exact: leq_ltn_trans H0.
Qed.

Lemma idel_size_last (s : seq A) (a : A) : idel (size s) (s ++ a :: nil) = s.
Proof. elim: s a => // hd tl IH a /=. by rewrite IH. Qed.

Lemma idel_upd_nth (s : seq A) k m : idel k (upd_nth s k m) = idel k s.
Proof. by elim : s k m => // h t IH [|k] //= m; rewrite IH. Qed.

Lemma idel_app : forall k (l1 : seq A), size l1 = k ->
  forall l a l2, l = l1 ++ a :: l2 -> idel k l = l1 ++ l2.
Proof.
elim=> [[] // H l a l2 -> // |].
move=> k IHk [|a0 l1] // [H] [|a1 l] // a l2 [-> Hl] /=; congr cons.
exact: IHk Hl.
Qed.

End index_deletion.

Definition idel_last {A : Type} (l : seq A) : seq A :=
  match l with
    | nil => nil
    | _ => idel (size l - 1) l
  end.

Lemma size_idel_last {A : Type} : forall n (l : seq A), size l = n ->
  size (idel_last l) = n - 1.
Proof.
case => [ [] // | n [|a l] // [len_l]].
by rewrite /idel_last [_ - _]/= subn1 size_idel //= len_l.
Qed.

Lemma size_idel_last' {A : Type} : forall (lst : seq A),
  O < size lst -> size (idel_last lst) = size lst - 1.
Proof. move=> lst H; by rewrite (size_idel_last (refl_equal (size lst))). Qed.

Lemma list_split {A : Type} def n (l : seq A) : size l = n ->
  forall j, j < n -> exists l1, size l1 = j /\
    exists l2, l = l1 ++ nth def l j :: nil ++ l2.
Proof.
move=> ln j jn.
exists (take j l).
rewrite size_takel; last by rewrite ln ltnW.
split => //.
exists (drop j.+1 l).
rewrite -drop_nth //; last by rewrite ln.
by rewrite cat_take_drop.
Qed.

(** An append function that removes doubles *)
Section app_set_function.

Variable A : eqType.

(** add an element to a list only if not already include *)
Fixpoint add_set (a : A) (l : seq A) {struct l} : seq A :=
  match l with
    | nil => a :: nil
    | hd :: tl => if hd == a then l else hd :: add_set a tl
  end.

Lemma In_add_set_inv : forall l a b, List.In a (add_set b l) -> a = b \/ List.In a l.
Proof.
elim=> //= [| hd tl IH a b]; first by firstorder.
move Heq : (hd == b) => [] /=.
- case=> Y; by auto.
- case=> Y; auto; move/IH : Y; tauto.
Qed.

Lemma In_add_set_L : forall l a, List.In a (add_set a l).
Proof.
elim=> //= [|hd tl IH a]; first tauto.
move Heq : (hd == a) => [] /=.
- move/eqP : Heq; by auto.
- right; by apply IH.
Qed.

Lemma In_add_set_R : forall l a b, List.In a l -> List.In a (add_set b l).
Proof.
elim=> //= hd tl IH a b; case=> X.
- subst hd.
  move Heq : (a == b) => []; rewrite /=; by auto.
- move Heq : (hd == b) => []; rewrite /=; by auto.
Qed.

Lemma incl_add_set k x : List.incl k (add_set x k).
Proof. move=> y Hy. exact: In_add_set_R. Qed.

(** append two lists using the previous functions
   (adding only the elements not already included) *)
Fixpoint app_set l1 l2 : seq A :=
  match l1 with
    | nil => l2
    | hd :: tl => app_set tl (add_set hd l2)
  end.

Lemma in_app_set_or : forall l m a, List.In a (app_set l m) -> List.In a l \/ List.In a m.
Proof.
elim=> //= [| hd tl IH m a H ] ; first by tauto.
case: {IH H}(IH _ _ H); first by firstorder.
case/In_add_set_inv; by firstorder.
Qed.

Lemma in_or_app_set : forall l m a, List.In a l \/ List.In a m -> List.In a (app_set l m).
Proof.
elim=> //=; first tauto.
move=> hd tl IH m a [[-> | H] | H]; apply IH.
- right; exact: In_add_set_L.
- tauto.
- right; exact: In_add_set_R.
Qed.

Lemma disj_app_set l k m : disj (app_set l k) m -> disj l m /\ disj k m.
Proof.
move=> H; split=> x.
- split=> // Hx abs; case: (H x) => H1; apply => //;
  apply in_or_app_set; by left.
- split=> // Hx abs; case: (H x) => H1; apply => //;
  apply in_or_app_set; by right.
Qed.

Lemma In_app_set_nil l x : List.In x (app_set l nil) -> List.In x l.
Proof. by case/in_app_set_or. Qed.

Lemma disj_app_set_nil l k : disj l k -> disj (app_set l nil) k.
Proof.
move=> H x; split=> //.
move/In_app_set_nil => H1 abs; move: (H x); tauto.
move=> Hx abs.
apply (proj2 (H x)) => //.
by move/In_app_set_nil : abs.
Qed.

Lemma incl_app_set_L l1 l2 : List.incl l1 (app_set l1 l2).
Proof. move=> x Hx. apply in_or_app_set; by auto. Qed.

Lemma incl_app_set_R l1 l2 : List.incl l2 (app_set l1 l2).
Proof. move=> x Hx. apply in_or_app_set; by auto. Qed.

Lemma incl_app_set l1 l2 l3 :
  List.incl l1 l3 -> List.incl l2 l3 -> List.incl (app_set l1 l2) l3.
Proof.
move=> H12 H13 a Ha.
apply in_app_set_or in Ha.
case: Ha => Ha.
by apply H12.
by apply H13.
Qed.

Lemma NoDup_add_set : forall l a, List.NoDup l -> List.NoDup (add_set a l).
Proof.
elim=> /= [a _ | hd tl IH a Ha].
- apply List.NoDup_cons => //.
  by apply List.NoDup_nil.
- case: ifP => // X.
  apply List.NoDup_cons; last first.
    apply IH.
    by inversion Ha.
  case/In_add_set_inv => Y.
    subst a.
    by rewrite eqxx in X.
  by inversion_clear Ha.
Qed.

Lemma NoDup_app_set : forall a b, List.NoDup b -> List.NoDup (app_set a b).
Proof.
elim => // hd tl IH b Hb /=; apply IH.
by apply NoDup_add_set.
Qed.

End app_set_function.

Section Permutation_ext.

Variable A : Type.

Implicit Type l : seq A.

Lemma Permutation_notin l l' x : Permutation l l' -> ~ List.In x l -> ~ List.In x l'.
Proof.
move=> H H'; contradict H'. apply Permutation_sym in H. eapply Permutation_in; eauto.
Qed.

Lemma permut_rotate (a : A) l : Permutation (a :: l) (l ++ a :: nil).
Proof.
apply Permutation_cons_app.
rewrite -List.app_nil_end; by apply Permutation_refl.
Qed.

Lemma Permutation_incl_L l1 l2 k : Permutation l1 l2 -> List.incl l1 k -> List.incl l2 k.
Proof.
move=> Hperm Hincl x Hx; apply Hincl.
apply Permutation_in with l2 => //.
by apply Permutation_sym, Hperm.
Qed.

Lemma Permutation_incl_R l1 l2 k : Permutation l1 l2 -> List.incl k l1 -> List.incl k l2.
Proof.
move=> Hperm Hincl x Hx.
apply Permutation_in with l1; by [apply Hperm | apply Hincl].
Qed.

Lemma incl_refl_Permutation l1 l2 : Permutation l1 l2 -> List.incl l1 l2.
Proof. move=> H x Hxl1; by apply Permutation_in with l1. Qed.

Lemma Permutation_app_cons l l' e : Permutation (l ++ (e :: nil) ++ l') (e :: l ++ l').
Proof. exact/Permutation_sym/Permutation_cons_app/Permutation_refl. Qed.

Lemma Permutation_disj_L k l m : Permutation m l -> disj m k -> disj l k.
Proof.
move=> m_l m_k; split=> [x_l x_k | x_k x_l]; apply (m_k x) => //;
apply Permutation_in with l => //; exact: Permutation_sym.
Qed.

Lemma Permutation_disj_R k l m : Permutation m l -> disj k m -> disj k l.
Proof.
move=>  m_l k_m.
apply disj_sym.
apply Permutation_disj_L with m => //.
exact: disj_sym.
Qed.

Lemma Permutation_nth def : forall l k, Permutation k (iota O (size l)) ->
  Permutation l (map (fun x => nth def l x) k).
Proof.
elim/last_ind=> [k|t h IH k H].
- rewrite [iota _ _]/=.
  move/Permutation_sym; move/Permutation_nil=> -> /=.
  by apply Permutation_refl.
- rewrite -cats1.
  apply Permutation.perm_trans with
    (map (fun x => nth def (t ++ h :: nil) x) (iota O (size t) ++ size t :: nil)); last first.
    rewrite -cats1 size_cat /= addnC /= in H.
    apply Permutation_map; rewrite -/(iota (size t) 1) -iota_add addn1; exact/Permutation_sym.
  + rewrite map_cat /=.
    rewrite nth_cat ltnn subnn /=.
    apply Permutation_app => //.
    have -> : map (fun x => nth def (t ++ h :: nil) x) (iota 0 (size t)) =
        map (fun x => nth def t x) (iota 0 (size t)).
        apply eq_in_map => x.
        rewrite mem_iota add0n => /andP [ _ xt].
        by rewrite nth_cat xt.
    apply IH; by apply Permutation_refl.
Qed.

Variable B : Type.

Definition Permutation_preserving (f : seq A -> seq B) :=
  forall l1 l2 : list A, Permutation l1 l2 ->
    Permutation (f l1) (f l2).

End Permutation_ext.

(*Arguments Permutation_notin [A].
Arguments permut_rotate [A].
Arguments Permutation_incl_L [A].
Arguments Permutation_incl_R [A].
Arguments Permutation_app_cons [A].
Arguments incl_refl_Permutation [A].
Arguments Permutation_disj_L [A].
Arguments Permutation_disj_R [A].
Arguments Permutation_nth [A].
Arguments Permutation_preserving [A B].*)

Lemma Permutation_size {A : Type} (l1 l2 : seq A) : Permutation l1 l2 -> size l1 = size l2.
Proof.
elim => //.
by move=> x l l' _ /= ->.
by move=> {l1 l2}l1 l2 l3 _ ->.
Qed.

Lemma Permutation_cons_cat {A : Type} : forall (l : seq A) (x : A),
  Permutation (x :: l) (l ++ [:: x]).
Proof.
elim=> // h t IH x /=.
eapply Permutation_trans.
  by apply perm_swap.
by apply perm_skip, IH.
Qed.

Lemma Permutation_app_inv_r {A : Type} :
   forall l l1 l2 : seq A, Permutation (l1 ++ l) (l2 ++ l) -> Permutation l1 l2.
Proof.
move=> l l1 l2 H.
move: (Permutation_size H).
rewrite !size_cat => /eqP; rewrite eqn_add2r => /eqP Hn.
elim: l l1 l2 H Hn => //.
  by move=> ??; rewrite !cats0.
move=> h t IH l1 l2.
rewrite -cat1s !catA => H Hn.
move: (IH _ _ H).
rewrite !size_cat /= Hn => /(_ (refl_equal _)) => K.
apply Permutation_cons_inv with h.
eapply Permutation.perm_trans.
  apply Permutation_cons_cat.
eapply Permutation.perm_trans.
  apply K.
apply Permutation_sym.
by apply Permutation_cons_cat.
Qed.

Lemma Permutation_seq_inv : forall (l : seq nat) n, size l <> O ->
  Permutation l (iota 0 (S n)) ->
  exists l1, exists l2, l = l1 ++ (n :: nil) ++ l2 /\ Permutation (l1 ++ l2) (iota O n).
Proof.
case=> // sh st n _ H.
have /inP : List.In n (sh :: st).
  apply Permutation_in with (iota O (S n)).
  - by apply Permutation_sym.
  - rewrite -addn1 iota_add /= add0n.
    apply List.in_or_app; right; simpl; by auto.
case/memP => l1 [l2 [Hl1l2 _]].
exists l1, l2; split; first by [].
apply Permutation_app_inv_r with (n :: nil).
rewrite -{2}/(iota n 1) -iota_add.
apply Permutation.perm_trans with (sh :: st) => //.
rewrite Hl1l2 -catA.
apply Permutation_app.
- by apply Permutation_refl.
- by apply Permutation_sym, permut_rotate.
by rewrite addn1.
Qed.

Ltac Permut n :=
  match goal with
  |  |- (Permutation ?X1 ?X1) => apply Permutation_refl
  |  |- (Permutation (?X1 :: ?X2) (?X1 :: ?X3)) =>
      let newn := eval compute in (size X2) in
      (apply perm_skip; Permut newn)
  |  |- (Permutation (?X1 :: ?X2) ?X3) =>
      match eval compute in n with
      | 1 => fail
      | _ =>
          let l0' := constr:(X2 ++ X1 :: nil) in
          (apply (@Permutation.perm_trans _ (X1 :: X2) l0' X3);
            [ apply permut_rotate | compute; Permut (Peano.pred n) ])
      end
  end.

Ltac PermutProve :=
  match goal with
  |  |- (Permutation ?X1 ?X2) =>
      match eval compute in (size X1 = size X2) with
      | (?X1 = ?X1) => Permut X1
      end
  end.

Section fixpoint_permutation.

Variable A : Type.

Variable eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}.

(** remove only one occurrence of an element (the Coq standard library remove function removes all of them) *)
Fixpoint remove1 (a : A) l :=
  match l with
    | nil => nil
    | h :: t => if eq_dec a h then t else h :: remove1 a t
  end.

(* NB: move to remove_ext? *)
Lemma Permutation_remove1 : forall h1 h h2,
  Permutation (remove1 h (h1 ++ h :: h2)) (h1 ++ h2).
Proof.
elim=> [h h2 | hd tl IH h h2] /=.
by case: (eq_dec h h) => // X.
case: (eq_dec h hd) => /= X.
- subst h.
  rewrite -/((hd :: nil) ++ h2); by apply Permutation_app_cons.
- by apply perm_skip, IH.
Qed.

Fixpoint fpermut (l k : seq A) :=
  match (l,k) with
    | (nil, nil) => true
    | (h :: t, h' :: t') =>
      if eq_dec h h' then
        fpermut t t'
      else if List.In_dec eq_dec h t' then
        fpermut t (h' :: remove1 h t')
      else
        false
    | _ => false
  end.

Lemma function_permut_Permutation : forall n (l k : seq A),
  size l = n -> fpermut l k -> Permutation l k.
Proof.
elim.
- move=> [] // [] // *; by apply Permutation_refl.
- move=> n IH [|h t] // [|h' t'] // [Hlent] /=.
  case: (eq_dec h h') => /= X.
  + subst h'.
    move/(IH _ _ Hlent).
    by apply perm_skip.
  + case: (List.In_dec eq_dec h t') => /= Y // Z.
    case/(@InP A) : (Y) => h1' [h2' H'].
    rewrite H' List.app_comm_cons.
    apply Permutation_cons_app.
    move: {IH}(IH _ _ Hlent Z) => IH.
    apply Permutation.perm_trans with (h' :: remove1 h t') => //=.
    apply perm_skip.
    rewrite H'.
    by apply Permutation_remove1.
Qed.

End fixpoint_permutation.

Lemma tail_app {A : Type}: forall (lst lst' : seq A), 0 < size lst ->
  List.tail (lst ++ lst') = List.tail lst ++ lst'.
Proof. case=> //= l' H; by inversion H. Qed.

Lemma list_tail { A : Type}: forall def (l : seq A), 0 < size l -> nth def l 0 :: List.tail l = l.
Proof. move=> def. case=> //=. Qed.

Section about_substitution.

Variable A : Type.

Lemma sub_substitution : forall n s0 s1, size (s0 ++ (n :: nil) ++ s1) = S n ->
  (forall x, List.In x (s0 ++ s1) -> (x < n)) ->
  forall (def e : A) l0 l1 k,
    size (l0 ++ (e :: nil) ++ l1) = S n ->
    size (k ++ e :: nil) = S n ->
    size l0 = size s0 ->
    (forall i, i < S n ->
      nth def (l0 ++ (e :: nil) ++ l1) i = nth def (k ++ e :: nil) (nth 0 (s0 ++ (n :: nil) ++ s1) i)) ->
    (forall i, i < n ->
      nth def (l0 ++ l1) i = nth def k (nth 0 (s0 ++ s1) i)).
Proof.
move=> n s0 s1 Hs Hx def e l0 l1 k Hl Hk Hlenl0 H i Hin.
have Hlenk : size k = n by rewrite !size_cat /= in Hk; ssromega.
have [Hi | [Hi | Hi]] : i < size s0 \/ i = size s0 \/ size s0 < i.
  case: (PeanoNat.Nat.lt_trichotomy i (size s0)) => [|[->|]].
  by left; apply/ltP.
  by auto.
  by right; right; apply/ltP.
- have {Hin}Hin : i < n.+1 by rewrite ltnW.
  move: {H}(H _ Hin) => H.
  rewrite nth_cat Hlenl0 Hi in H.
  rewrite (_ : nth _ _ i = nth 0 s0 i) in H; last first.
    by rewrite nth_cat Hi.
  rewrite nth_cat // Hlenk Hx in H; last first.
    apply List.in_or_app; left; by apply In_nth.
  by rewrite nth_cat Hlenl0 Hi nth_cat Hi.
- destruct s1 as [|hs1 ts1]; subst i.
  + have {Hs}Hs : size s0 = n by rewrite size_cat /= in Hs; ssromega.
    by rewrite Hs ltnn in Hin.
  + rewrite -ltnS in Hin.
    move: {H}(H _ Hin) => H.
    rewrite -{1}Hlenl0 nth_cat ltnn subnn nth_cat ltnn subnn.
    rewrite nth_cat Hlenl0 (_ : _.+1 < _ = false) // in H; last first.
      apply/negbTE; by rewrite -leqNgt.
    rewrite subSn // subnn in H.
    rewrite nth_cat ltnn subnn in H.
    rewrite nth_cat Hlenk Hx in H; last first.
      rewrite nth_cat (_ : _ < _ = false); last first.
        apply/negbTE.
        by rewrite -leqNgt.
      rewrite subSn // subnn /=.
      apply List.in_or_app; right; left; by auto.
    rewrite nth_cat (_ : _ < _ = false) in H; last first.
      apply/negbTE.
      by rewrite -leqNgt.
    by rewrite H subSn // subnn.
- rewrite -ltnS in Hin.
  move: {H}(H _ Hin) => H.
  rewrite nth_cat in H.
  rewrite (_ : _ < _ = false) in H; last first.
    apply/negbTE.
    rewrite -leqNgt -ltnS.
    rewrite Hlenl0.
    by apply (@ltn_trans i).
  rewrite nth_cat subSn in H; last by rewrite Hlenl0 ltnW.
  rewrite ltnS ltn0 subSS subn0 in H.
  rewrite catA in H.
  rewrite nth_cat ltnNge ltnW //=; last by rewrite Hlenl0.
  rewrite H.
  rewrite nth_cat Hlenk Hx; last first.
    apply List.in_or_app; right.
    rewrite nth_cat size_cat addn1 ltnS ltnNge ltnW //= subSS.
    apply In_nth.
    rewrite size_cat /= addnS in Hs.
    case: Hs => Hs.
    rewrite -(ltn_add2r (size s0)).
    rewrite subnK; last by rewrite ltnW.
    by rewrite addnC Hs.
  rewrite nth_cat size_cat addn1 ltnS ltnNge ltnW //= subSS.
  by rewrite nth_cat ltnNge ltnW //.
Qed.

Lemma substitution_Permutation : forall n s, size s = n ->
  Permutation s (iota O n) ->
  forall (def : A) l k, size l = n -> size k = n ->
    (forall i, i < n -> nth def l i = nth def k (nth 0 s i)) ->
    Permutation l k.
Proof.
elim; first by case=> // _ _ def [] // [] // _ _ _; apply Permutation_refl.
move=> n IH [|sh st] // [len_st] perm_shst def l k len_l len_k bij.
have [s0 [s1 [sh_st perm_s0s1]]] : exists s0, exists s1,
  sh :: st = s0 ++ (n :: nil) ++ s1 /\ Permutation (s0 ++ s1) (iota 0 n).
  by apply Permutation_seq_inv.
have len_s0s1 : size (s0 ++ s1) = n.
  have : size (sh :: st) = S n by rewrite -(List.seq_length (S n) 0); apply Permutation_length.
  rewrite sh_st !size_cat add1n addnS; by case.
have len_s0 : size s0 < S n.
  have : size (sh :: st) = S n by rewrite -(List.seq_length (S n) 0); apply Permutation_length.
  rewrite sh_st !size_cat add1n addnS => <-.
  by rewrite ltnS leq_addr.
have [l0 [elt [l1 [l_def len_l0]]]] : exists l0 elt l1,
  l = l0 ++ (elt :: nil) ++ l1 /\ size l0 = size s0.
  case: (@list_split A def (S n) _ len_l _ len_s0) => l0 [l0_s0 [l1 l_def]].
  exists l0; exists (nth def l (length s0)); by exists l1.
have len_l0l1 : size (l0 ++ l1) = n.
  rewrite l_def !size_cat /= add1n addnS in len_l.
  rewrite size_cat; by case: len_l.
have [k0 k_def] : exists k0, k = k0 ++ elt :: nil.
  move: (bij _ len_s0).
  rewrite sh_st nth_cat ltnn subnn /= l_def nth_cat len_l0 ltnn subnn /= => ->.
  exists (take n k).
  rewrite cats1 -take_nth //; last by rewrite len_k.
  by rewrite take_oversize // len_k.
have len_k0 : size k0 = n. rewrite k_def size_cat /= addn1 in len_k; by case: len_k.
rewrite l_def k_def.
have IH_hyp : (forall i, i < n -> nth def (l0 ++ l1) i = nth def k0 (nth 0 (s0 ++ s1) i)).
  apply sub_substitution with elt => //.
  - by rewrite -sh_st // (Permutation_size perm_shst) // size_iota.
  - move=> x Hx; move: (Permutation_in _ (perm_s0s1) Hx).
    by move/inP; rewrite mem_iota leq0n /= add0n.
  - by rewrite -l_def.
  - by rewrite -k_def.
  - by rewrite -l_def -k_def -sh_st.
move: {IH}(IH _ len_s0s1 perm_s0s1 def _ _ len_l0l1 len_k0 IH_hyp) => IH.
apply Permutation.perm_trans with (elt :: (l0 ++ l1)).
- by apply Permutation_sym, Permutation_cons_app, Permutation_refl.
- apply Permutation.perm_trans with (elt :: k0).
  + by apply perm_skip.
  + apply Permutation_cons_app; rewrite -List.app_nil_end; by apply Permutation_refl.
Qed.

End about_substitution.

Section onth_ext.

Variable A : Type.

(* NB: Nth: semi_ring_theory 0%N 1%N Nplus Nmult eq *)
Fixpoint onth (n : nat) (l : seq A) : option A :=
  match n with
    | O => match l with nil => None | h :: _ => Some h end
    | S m => match l with nil => None | _ :: t => onth m t end
  end.

Lemma onth_nil : forall i, onth i (@nil A) = None.
Proof. by case. Qed.

Lemma onth_In : forall (l : seq A) n a, onth n l = Some a -> List.In a l.
Proof.
elim=> [[] // | h t IH [|n] /= a].
by case; auto.
by move/IH; auto.
Qed.

Lemma onth_Some_inv1 : forall (l : seq A) i v, onth i l = Some v -> i < size l.
Proof. elim=> [[] // | h t IH [ // |i] v /=]; by move/IH => ?. Qed.

Lemma onth_Some_lt : forall (l : seq A) n a, onth n l = Some a -> n < size l.
Proof. by elim=> [[] // | h t IH [|n] //= a /IH]. Qed.

Lemma onth_nth : forall l def (a : A) i, onth i l = Some a -> nth def l i =  a.
Proof.
elim.
  move=> def a i.
  by rewrite onth_nil.
move=> h t IH def a0 [|i] /=.
by case.
move/IH; exact.
Qed.

End onth_ext.

Lemma onth_map : forall {A B : Type} (l : seq A) x v,
  onth x l = Some v -> forall f : A -> B, onth x (map f l) = Some (f v).
Proof.
move=> A B; elim => [[] // | h t IH [|x] /= v].
by case=> <-.
by move/IH.
Qed.

Lemma onth_map_Some_inv : forall {A B : Type} (f : A -> B) l i x,
  onth i (map f l) = Some x -> exists y, onth i l = Some y /\ f y = x.
Proof.
move=> A B f; elim=> [/= i x | hd tl IH [|i] x /= H].
- by rewrite onth_nil.
- case: H => ?; subst x; by exists hd.
- case/IH : H => y H; by exists y.
Qed.

Lemma onth_map_inv : forall {A B : Type} (f : A -> B) l i b,
  onth i (map f l) = Some b -> exists a, onth i l = Some a /\ b = f a.
Proof.
move=> A B f; elim=> /= [i b| h t IH [|i] /=].
by rewrite onth_nil.
move=> b [] <-; by exists h.
move=> b; case/IH => a [H1 H2]; by exists a.
Qed.

Lemma onth_Some_exists : forall {A B: Type} (l : seq A) (l' : seq B),
  size l = size l' -> forall n f, n < size l ->
    onth n l = Some f -> exists f', onth n l' = Some f'.
Proof.
move=> A B; elim => [[] // _ [] // | ht t IH [|h' t'] //= [t_t'] ].
destruct n as [|n].
move=> f _ _; eexists; reflexivity.
move=> f Hn n_f.
by apply (IH _ t_t' n f) in Hn.
Qed.

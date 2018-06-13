(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(**
This file provides:
- a section that proves some facts about total orders
- a module type for orders
- a section that defines an order for pairs
- a section that defines the lexicographic order
- functors to instantiate order for pairs and lexicographic order
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section total_order_facts.

Variable A : eqType.
Variable ltA : A -> A -> bool.
Notation "x < y" := (ltA x y).
Variable ltA_trans : forall n m p, m < n -> n < p -> m < p.
Variable ltA_irr : forall a, a < a = false.
Variable ltA_total : forall m n, (m != n) = (m < n) || (n < m).

Lemma flip a b : a < b -> b < a = false.
Proof.
move=> H.
case/boolP : (b < a) => [|X].
- move/(ltA_trans H); by rewrite ltA_irr.
- exact/negbTE.
Qed.

Lemma flip' a b : a < b = false -> a = b \/ b < a.
Proof.
move=> H.
case/boolP: (a == b) => [/eqP ab|ab].
- by left.
- right.
  rewrite ltA_total in ab.
  case/orP : ab => //.
  by rewrite H.
Qed.

Lemma lt_neq a b : a < b -> a == b = false.
Proof. move=> H. apply/eqP. apply/eqP. by rewrite ltA_total H. Qed.

Lemma tri' a b : a < b \/ a = b \/ b < a.
Proof.
case/boolP : (a == b).
- move/eqP; auto.
- rewrite ltA_total; case/orP; auto.
Qed.

Lemma tri n n' : n' < n -> forall a, a < n' \/ a = n' \/ n' < a /\ a < n \/ a = n \/ n < a.
Proof.
move=> H a.
case/boolP : (a == n').
- move/eqP; auto.
- rewrite ltA_total. case/orP; auto.
  move: (tri' a n); case; auto.
Qed.

(** strict lower bound of an sequence *)
Fixpoint lb n (lst : seq A) :=
  if lst isn't h :: t then true else (n < h) && lb n t.

Lemma lt_lb : forall l m, (forall n, n \in l -> m < n) -> lb m l.
Proof.
elim=> // hd tl IH m H /=.
rewrite H /= ?mem_head // IH // => n Hn; by rewrite H // inE Hn orbT.
Qed.

Lemma lb_trans : forall l n m, lb n l -> m < n -> lb m l.
Proof.
elim => //= s s0 Hs n m.
case/andP => [H1 H2] H3.
apply/andP; split.
- by apply ltA_trans with n.
- by apply Hs with n.
Qed.

Lemma mem_lt_lb : forall l x, lb x l -> forall y, y \in l -> x < y.
Proof.
elim=> //= h t H x.
move/andP => [H1 H2] y.
move/orP => [H3 | H3].
- by move/eqP : H3 => ->.
- by apply H.
Qed.

Lemma lb_incl : forall l n, lb n l -> forall f, lb n (filter f l).
Proof.
elim=> //= h t IH n /andP[H1 H2] f.
case: ifPn => X /=; by [rewrite H1 /= IH | rewrite IH].
Qed.

Lemma mem_lb : forall l x, lb x l -> ~~ (x \in l).
Proof.
elim=> //= h t H x.
move/andP => [H1 H2].
rewrite !in_cons; apply/orP.
case => H3.
- move/eqP in H3; subst.
  by rewrite ltA_irr in H1.
- move: (H _ H2); by rewrite H3.
Qed.

(** strict upper bound of an sequence *)
Fixpoint ub a (k : seq A) :=
  if k isn't h :: t then true else (h < a) && ub a t.

Lemma mem_ub : forall k a, ub a k -> a \notin k.
Proof.
elim=> // hd tl /= IH a /andP[H1 H2].
rewrite in_cons negb_or IH // andbT; apply/negP => /eqP ?; subst hd.
by rewrite ltA_irr in H1.
Qed.

End total_order_facts.

Module Type ORDER.
Parameter A : eqType.
Parameter ltA : A -> A -> bool.
Notation "x < y" := (ltA x y). (* TODO: put a scope and open it when defining
NatOrder and ZOrder *)
Parameter ltA_trans : forall n m p, m < n -> n < p -> m < p.
Parameter ltA_total : forall m n, (m != n) = (m < n) || (n < m).
Parameter ltA_irr : forall a, a < a = false.
End ORDER.

Module NatOrder <: ORDER.
Definition A := nat_eqType.
Definition ltA : A -> A -> bool := ltn.
Lemma ltA_trans : forall n m p, m < n -> n < p -> m < p.
Proof. exact ltn_trans. Qed.
Lemma ltA_total : forall m n, (m != n) = (m < n) || (n < m).
Proof. exact neq_ltn. Qed.
Lemma ltA_irr : forall a, a < a = false.
Proof. exact ltnn. Qed.
End NatOrder.

Section order_pair.

Variable A : eqType.
Variable ltA : A -> A -> bool.
Local Notation "x < y" := (ltA x y).
Variable ltA_trans : forall n m p, m < n -> n < p -> m < p.
Variable ltA_irr : forall a, a < a = false.
Variable ltA_total : forall m n, (m != n) = (m < n) || (n < m).
Variable B : eqType.
Variable ltB : B -> B -> bool.
Local Notation "x '<<<' y" := (ltB x y) (at level 70).
Variable ltB_trans : forall n m p, (m <<< n) -> (n <<< p) -> (m <<< p).
Variable ltB_irr : forall a, a <<< a = false.
Variable ltB_total : forall m n, (m != n) = (m <<< n) || (n <<< m).

Definition lt_pair : prod_eqType A B -> prod_eqType A B -> bool :=
  fun x => fun y => (x.1 < y.1) || ( (x.1 == y.1) && (x.2 <<< y.2) ).

Lemma lt_pair_trans : forall (n m p : prod_eqType A B),
  lt_pair m n -> lt_pair n p -> lt_pair m p.
Proof.
move=> [n1 n2] [m1 m2] [p1 p2]; rewrite /lt_pair /= => H1 H2.
case/orP: H1 => H1.
- case/orP: H2 => H2.
  + rewrite (ltA_trans H1 H2) //.
  + case/andP: H2 => /eqP H2 H3; subst n1.
    by rewrite H1.
- case/andP: H1 => /eqP H1 H3; subst n1.
  case/orP: H2 => H2.
  + by rewrite H2.
  + case/andP: H2 => /eqP H1 H2; subst p1.
    by rewrite ltA_irr /= eq_refl /= (@ltB_trans n2).
Qed.

Lemma lt_pair_total : forall (m n : prod_eqType A B),
  (m != n) = lt_pair m n || lt_pair n m.
Proof.
move=> [m1 m2] [n1 n2]; rewrite /lt_pair /=.
case: (tri' ltA_total m1 n1) => [X | [X | X]].
- rewrite X /=.
  apply/eqP; case=> X1 X2; subst.
  by rewrite ltA_irr in X.
- subst.
  rewrite ltA_irr /= eq_refl /= -ltB_total.
  apply/eqP.
  case: ifPn => [/eqP|] X.
  + contradict X.
    by case : X.
  + rewrite negbK in X.
    by rewrite (eqP X).
- rewrite X /= orbT.
  apply/eqP.
  case=> Y Z; subst.
  by rewrite ltA_irr in X.
Qed.

Lemma lt_pair_irr : forall (m : prod_eqType A B), lt_pair m m = false.
Proof. move=> [m1 m2]; rewrite /lt_pair /=. rewrite ltA_irr /= eq_refl /= ltB_irr //. Qed.

End order_pair.

Unset Implicit Arguments.

Module PairOrder (O1 O2:ORDER) <: ORDER.
Definition A := prod_eqType O1.A O2.A.
Definition ltA : A -> A -> bool := lt_pair O1.ltA O2.ltA.
Notation "x < y" := (ltA x y).
Lemma ltA_trans : forall n m p, m < n -> n < p -> m < p.
Proof. exact (lt_pair_trans O1.ltA_trans O1.ltA_irr O2.ltA_trans). Qed.
Lemma ltA_total : forall m n, (m != n) = (m < n) || (n < m).
Proof. exact (lt_pair_total O1.ltA_irr O1.ltA_total O2.ltA_total). Qed.
Lemma ltA_irr : forall a, a < a = false.
Proof. exact (lt_pair_irr O1.ltA_irr O2.ltA_irr). Qed.
End PairOrder.

Module pair_nat_order := PairOrder NatOrder NatOrder.

Set Implicit Arguments.

(** given an order ltA (over an eqtype A), define the lexicographic order lex (over the type seq A) *)

Section lexicographic_order.
Variable A : eqType.
Variable ltA : A -> A -> bool.
Notation "x < y" := (ltA x y).
Variable ltA_trans : forall n m p, m < n -> n < p -> m < p.
Variable ltA_irr : forall a, a < a = false.
Variable ltA_total : forall m n, (m != n) = (m < n) || (n < m).

Fixpoint lex (l l':seq A) {struct l} : bool :=
  match l with
    | [::] => match l' with
                | [::] => false
                | _ => true
              end
    | h :: t => match l' with
                  | [::] => false
                  | h' :: t' =>
                    if h < h' then true else
                      if h == h' then lex t t' else
                        false
                end
  end.

Lemma lex_seq0 : forall (n : seq A), ~ lex n [::]. Proof. by case. Qed.

Lemma lex_app : forall l a b, lex a b -> lex (l ++ a) (l ++ b).
Proof. elim=> //= l0 l Hl a b Hab. rewrite ltA_irr eq_refl. apply Hl => //. Qed.

Lemma lex_trans : forall n m p, lex m n -> lex n p -> lex m p.
Proof.
move=> n m; move: m n; elim.
- case=> //. move=> n0 n. by case.
- move=> n0 n Hn m; move: m n0 n Hn. elim=> //.
  move=> m0 m Hm n0 n Hn p; move: p m0 m Hm n0 n Hn. elim=> //.
  move=> p0 p Hp  m0 m Hm n0 n Hn /=.
  move=> Hnm Hmp.
  have [H1 | [H1 | H1] ] : n0 < p0 \/ n0 = p0 \/ p0 < n0 by apply tri'.
  + rewrite H1 //.
  + subst p0.
    rewrite ltA_irr eq_refl.
    have [H2 | [H2 | H2] ] : n0 < m0 \/ n0 = m0 \/ m0 < n0 by apply tri'.
    * have H3 : m0 < n0 = false.
        apply/negP => H'. move: (ltA_trans H2 H') => H''. rewrite ltA_irr // in H''.
      rewrite H3 in Hmp.
      have H4 : m0 == n0 = false.
        apply/eqP. move=> H'; subst. rewrite H2 // in H3.
      rewrite H4 // in Hmp.
    * subst m0.
      rewrite ltA_irr eq_refl in Hnm.
      rewrite ltA_irr eq_refl in Hmp.
      by apply Hn with m.
    * have H3 : n0 < m0 = false.
        apply/negP => H'. move: (ltA_trans H2 H') => H''. rewrite ltA_irr // in H''.
      rewrite H3 in Hnm.
      have H4 : n0 == m0 = false.
        apply/eqP. move=> H'; subst. rewrite H2 // in H3.
      rewrite H4 // in Hnm.
  + move: (tri ltA_total H1 m0) => [ H2 | [ H2 | [ [H2 H2'] | [ H2 | H2 ] ] ] ].
    * have H3 : n0 < m0 = false.
        apply/negP => H'. move: (ltA_trans (ltA_trans H1 H') H2) => H''. rewrite ltA_irr // in H''.
      rewrite H3 in Hnm.
      have H4 : n0 == m0 = false.
        apply/eqP. move=> H'; subst. rewrite (ltA_trans H2 H1) // in H3.
      rewrite H4 // in Hnm.
    * subst p0.
      rewrite ltA_irr eq_refl in Hmp.
      have H3 : n0 < m0 = false.
        apply/negP => H'. move: (ltA_trans H1 H') => H''. rewrite ltA_irr // in H''.
      rewrite H3 in Hnm.
      have H4 : n0 == m0 = false.
        apply/eqP. move=> H'; subst. rewrite H1 // in H3.
      rewrite H4 // in Hnm.
    * have H3 : n0 < m0 = false.
        apply/negP => H'. move: (ltA_trans H' H2') => H''. rewrite ltA_irr // in H''.
      rewrite H3 in Hnm.
      have H6 : n0 == m0 = false.
        apply/eqP. move=> H'; subst. rewrite H2' // in H3.
      rewrite H6 // in Hnm.
    * subst n0.
      rewrite ltA_irr eq_refl in Hnm.
      have H3 : m0 < p0 = false.
        apply/negP => H'. move: (ltA_trans H1 H') => H''. rewrite ltA_irr // in H''.
      rewrite H3.
      rewrite H3 in Hmp.
      have H4 : m0 == p0 = false.
        apply/eqP. move=> H'; subst. rewrite H1 // in H3.
      rewrite H4 // in Hmp.
    * have H3 : n0 < p0 = false.
        apply/negP => H'. move: (ltA_trans H1 H') => H''. rewrite ltA_irr // in H''.
      rewrite H3.
      have H4 : m0 < p0 = false.
        apply/negP => H'. move: (ltA_trans H1 (ltA_trans H2 H')) => H''. rewrite ltA_irr // in H''.
      rewrite H4 in Hmp.
      have H5 : m0 == p0 = false.
        apply/eqP. move=> H'; subst. rewrite (ltA_trans H1 H2) // in H4.
      rewrite H5 // in Hmp.
Qed.

Lemma lex_total : forall m n, ~~ (m == n) = lex m n || lex n m.
Proof.
elim.
- by case.
- move=> m0 m Hm. elim=> //.
  move=> n0 n Hn /=.
  have [ H | [ H | H ] ] : m0 < n0 \/ m0 = n0 \/ n0 < m0 by apply tri'.
  + rewrite H /=.
    apply/negP => H'.
    move/eqP: H' => H'.
    case: H' => H1 H2; subst.
    rewrite ltA_irr // in H.
  + subst.
    rewrite ltA_irr; rewrite eq_refl; rewrite -Hm.
    have [H | H] : m == n \/ m == n = false by case (m == n); auto.
    * rewrite H /=.
      move/eqP : H => H; subst.
      apply/negP => H'.
      by apply H'.
    * rewrite H /=.
      apply/negP => H'.
      move/eqP : H' => H'.
      case: H' => H'; subst.
      move/negP: H => H.
      apply H.
      by rewrite eqxx.
    * have H' : m0 < n0 = false.
        apply/negP => H'. move: (ltA_trans H H') => H''. rewrite ltA_irr // in H''.
      rewrite H' H.
      have H'' : m0 == n0 = false.
        apply/eqP. move=> H''; subst. rewrite H // in H'.
      rewrite H'' /=.
      apply/negP => H'''.
      move/eqP: H''' => H'''.
      case: H''' => H1 H2; subst.
      move/negP: H'' => H''.
      apply H''.
      by rewrite eqxx.
Qed.

Lemma lex_irr : forall n, lex n n = false.
Proof. elim=> //=. move=> h t IH; rewrite ltA_irr eq_refl //. Qed.

End lexicographic_order.

Unset Implicit Arguments.

Module LexOrder (O:ORDER) <: ORDER with Definition A := seq_eqType O.A.
Definition A := seq_eqType O.A.
Definition ltA : A -> A -> bool := lex O.ltA.
Notation "x < y" := (ltA x y).
Lemma ltA_trans n m p : m < n -> n < p -> m < p.
Proof. exact: (lex_trans O.ltA_trans O.ltA_irr O.ltA_total). Qed.
Lemma ltA_total m n : (m != n) = (m < n) || (n < m).
Proof. exact: (lex_total O.ltA_trans O.ltA_irr O.ltA_total). Qed.
Lemma ltA_irr a : a < a = false.
Proof. exact: (lex_irr O.ltA_irr). Qed.
End LexOrder.

Module seq_nat_order := LexOrder NatOrder.
Module seq_pair_of_nats_order := LexOrder pair_nat_order.

Require Import ssrZ ZArith_ext.

Module ZOrder <: ORDER.
Definition A := Z_eqType.
Definition ltA : A -> A -> bool := Zlt_bool.
Lemma ltA_trans n m p : ltA m n -> ltA n p -> ltA m p.
Proof. move=> m_n n_p; apply/ltZP/ltZ_trans; apply/ltZP; eauto. Qed.
Lemma ltA_total m n : (m != n) = (ltA m n) || (ltA n m).
Proof.
case: (Z_lt_dec m n).
- move/ltZP => X; rewrite /ltA X /=.
  move/ltZP : X. move/ltZ_eqF. by move/eqP.
  move/ltZP; rewrite -leZNgt' => /leZP; case/leZ_eqVlt.
  + by move=> ->; rewrite eqxx /= /ltA ltZZ'.
  + move/ltZP => X; rewrite /ltA X orbC /=.
    move/ltZP : X. move/gtZ_eqF. move/eqP. apply contra. by move/eqP=> ->.
Qed.
Lemma ltA_irr a : ltA a a = false.
Proof. by rewrite /ltA ltZZ'. Qed.
End ZOrder.

Require Import Ascii.

Definition eq_ascii (a b : ascii) : bool :=
  match ascii_dec a b with left _ => true| right _ => false end.

Lemma eq_asciiP : Equality.axiom eq_ascii.
Proof. move=> x y; apply: (iffP idP); rewrite /eq_ascii; by case: (ascii_dec _ _). Qed.

Canonical Structure ascii_eqMixin := EqMixin eq_asciiP.
Canonical Structure ascii_eqType := Eval hnf in EqType _ ascii_eqMixin.

Definition lt_ascii (a b : ascii) : bool := ltn (nat_of_ascii a) (nat_of_ascii b).

Module AsciiOrder <: ORDER.
Definition A := ascii_eqType.
Definition ltA : A -> A -> bool := lt_ascii.
Lemma ltA_trans : forall n m p, ltA m n -> ltA n p -> ltA m p.
Proof. move=> n m p. by apply: ltn_trans. Qed.
Lemma ltA_total m n : (m != n) = (ltA m n) || (ltA n m).
Proof.
rewrite -neq_ltn.
apply/negP/negP => X; contradict X; last by move/eqP : X => ->.
rewrite -(ascii_nat_embedding m) -(ascii_nat_embedding n); by move/eqP : X => ->.
Qed.
Lemma ltA_irr : forall a, ltA a a = false.
Proof. move=> a; by apply: ltnn. Qed.
End AsciiOrder.

Module lex_ascii := LexOrder AsciiOrder.

Require Import String_ext.

Definition lt_string (a b : string) : bool := lex_ascii.ltA (string2asciis a) (string2asciis b).

Module StringOrder <: ORDER with Definition A := string_eqType.

Definition A := string_eqType.

Definition ltA : A -> A -> bool := lt_string.

Lemma ltA_trans : forall n m p, ltA m n -> ltA n p -> ltA m p.
Proof.
move=> n m p; rewrite /ltA /lt_string => n_m m_p.
by eapply lex_ascii.ltA_trans; eauto.
Qed.

Lemma ltA_total m n : (m != n) = (ltA m n) || (ltA n m).
Proof.
rewrite /ltA /lt_string -lex_ascii.ltA_total.
apply/negP/negP => X; contradict X; last by move/eqP : X => ->.
by move/eqP : X; move/string2asciis_inj; by move=> <-.
Qed.

Lemma ltA_irr : forall a, ltA a a = false.
Proof. move=> a; by apply lex_ascii.ltA_irr => b. Qed.

End StringOrder.

Module ORDER_ext (X : ORDER).
Definition leA (x y: X.A) := ~~ (X.ltA y x).
Notation "x <= y" := (leA x y).
Lemma leA_trans : forall (n m p: X.A), m <= n -> n <= p -> m <= p.
Proof.
  move => n m p.
  rewrite/leA.
  move => nm.
  apply: contra.
  case: (tri' X.ltA_total n m).
  - by move => nm'; apply False_ind;
    move/negP:nm => //.
  - move: nm => _.
    case.
    - by move => ->.
    - by move => mn pm; move : pm mn; exact: X.ltA_trans.
Qed.
End ORDER_ext.

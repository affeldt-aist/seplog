(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.

Declare Scope cmp_scope.

Lemma ltn_leq_trans n m p : m < n -> n <= p -> m < p.
Proof. move=> ?; exact: leq_trans. Qed.

Lemma ltn_leq_add2l : forall n1 n2 m1 m2,
  n1 <= n2 -> m1 < m2 -> n1 + m1 < n2 + m2.
Proof.
move=> n1 [|n2] m1 m2.
by case: n1.
move=> *; by rewrite -addnS leq_add.
Qed.

Lemma ltn_sub_add : forall m n p, 0 < p -> (m - n < p) = (m < n + p).
Proof. move=> m n [//|p] _; by rewrite ltnS leq_subLR addnS. Qed.

Lemma eq_succ : forall l, ~ l = l.+1.
Proof. by elim. Qed.

Lemma nat_rec_inv ub (P : nat -> Prop) :
  P ub ->
  (forall n, P n.+1 -> n < ub -> P n) ->
  forall i, i <= ub ->
  P i.
Proof.
elim: ub => //=.
- move => P0 _ i.
  by rewrite leqn0 => /eqP ->.
- move => n Hind HPSn HPsub i0.
  rewrite leq_eqVlt.
  case/orP => /= [ /eqP -> // | ].
  rewrite ltnS leq_eqVlt.
  case/orP => [/eqP -> | Hi0].
  + by apply HPsub.
  + apply Hind => //=.
    * by apply HPsub.
    * move => n0 HPSn0 Hn0.
      apply HPsub => //=.
      by rewrite (ltn_trans Hn0).
    * by rewrite ltnW.
Qed.

Ltac ssromega :=
  (repeat ssrnat2coqnat_hypo ;
   ssrnat2coqnat_goal ;
   omega)
with ssrnat2coqnat_hypo :=
  match goal with
    | H : context [?L < ?R] |- _ 	=> move/ltP: H => H
    | H : context [?L <= ?R] |- _ 	=> move/leP: H => H
    | H : context [?L < ?M < ?R] |- _ 	=> let H1 := fresh in case/andP: H => H H1
    | H : context [?L <= ?M < ?R] |- _ 	=> let H1 := fresh in case/andP: H => H H1
    | H : context [?L <= ?M <= ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [addn ?L ?R] |- _ => rewrite <- plusE in H
    | H : context [muln ?L ?R] |- _ => rewrite <- multE in H
    | H : context [subn ?L ?R] |- _ => rewrite <- minusE in H
    | H : ?x == _ |- _ => match type of x with nat => move/eqP in H end; idtac x
    | H : _ == ?x |- _ => match type of x with nat => move/eqP in H end; idtac x
    | H : _ != ?x |- _ => match type of x with nat => move/eqP in H end
(*    | H : ?a <> ?b |- _ =>
      match type of a with
      | nat => apply Coq.Arith.Compare_dec.not_eq in H
      end*)
  end
with ssrnat2coqnat_goal :=
  rewrite -?plusE -?minusE -?multE;
  match goal with
    | |- is_true (_ < _)%nat => apply/ltP
    | |- is_true (_ <= _)%nat => apply/leP
    | |- is_true (_ && _) => apply/andP; split; ssromega
    | |- is_true (?x != _) => match type of x with nat => apply/eqP end
    | |- is_true (_ != ?x) => match type of x with nat => apply/eqP end
    | |- is_true (?x == _) => match type of x with nat => apply/eqP end
    | |- is_true (_ == ?x) => match type of x with nat => apply/eqP end
    | |- _ /\ _ => split; ssromega
    | |- _ \/ _ => (left; ssromega) || (right; ssromega)
    | |- _ => idtac
  end.

Goal forall x y : nat, x + 4 - 2 > y + 4 -> (x + 2) + 2 >= y + 6.
Proof.
intros.
ssromega.
Qed.

Fact increasing (m : nat) (A : nat -> nat) :
 (forall m : nat, A m <= A (m.+1)) ->
 forall n, A m <= A (m + n).
Proof.
move=> inc; elim => [| n K]; first by rewrite addn0.
by rewrite addnS (leq_trans K (inc (m + n))).
Qed.

Lemma bounded_inc_convergent : forall max (A : nat -> nat),
  (forall n, A n.+1 >= A n) ->
  (forall m, m <= max.+1 -> A m <= max) ->
  (forall K L, A K = L -> A K.+1 = L -> forall m : nat, K <= m -> A m = L) ->
  forall m, max <= m -> A max = A m.
Proof.
elim.
- move=> A A_inc H same_stays.
  have -> : A 0 = 0 by apply/eqP; rewrite -leqn0 ; exact: H.
  move=> m mlarge; apply/esym/(same_stays O) => //; apply/eqP; rewrite -leqn0; exact: H.
- move=> max IH A A_inc small same_stays.
  case_eq (A 1) => a1.
  + have H : forall m : nat, 0 <= m -> A m = 0.
      apply: same_stays => //.
      apply/eqP; rewrite -leqn0 -{2}a1.
      apply: increasing; exact: A_inc.
    move=> m _; rewrite !H //.
  + move=> a1_; pose B n := (A n.+1).-1.
    move=> m max_m.
    have -> : A m = (B (m.-1)).+1.
      rewrite/B; have -> : succn (predn m) = m by move: max_m; exact: ltn_predK.
      rewrite prednK //.
      move: max_m.
      case: m => [ // | m _].
      elim: m => [ | m]; first by rewrite a1_.
      have H := A_inc m.+1.
      rewrite !ltnNge.
      apply: contra; exact: leq_trans.
    have -> : A max.+1 = (B max).+1.
      rewrite/B prednK //.
      move: IH max_m => _ _; move: small => _.
      have H : A 1 <= A max.+1 by apply: increasing; exact: A_inc.
      rewrite ltnNge.
      apply/negP.
      move => I.
      have : A 1 <= 0 by move: H I; exact: leq_trans.
      by rewrite a1_.
    congr S.
    apply: IH.
    * rewrite /B => n.
      rewrite -!subn1; apply: leq_sub2r; exact: A_inc.
    * case => [ _ | n ].
      - rewrite/B.
        have ? : A 1 <= succn max by apply: small.
        rewrite -(leq_add2r 1).
        have -> : predn (A 1) + 1 = A 1 by rewrite addn1 prednK // a1_.
        by rewrite addn1.
      + rewrite /B => nsmall.
        suff H : A n.+2 <= max.+1.
          move: (leq_sub2r 1 H) => I.
          suff -> : max = max.+1 - 1 by rewrite -subn1.
          by rewrite subn1.
        apply: small.
        rewrite -(ltn_add2r 1) in nsmall.
        by rewrite -(addn1 (max.+1)) -addn1.
    * move => K L; rewrite /B => KL KKL x Kx; apply/eqP.
      rewrite -(eqn_add2r 1).
      have -> : (A x.+1).-1 + 1 = A x.+1.
        rewrite addn1; apply: prednK.
        suff H : a1.+1 <= A x.+1 by apply: leq_ltn_trans H.
        rewrite -a1_; apply: increasing; exact: A_inc.
      apply/eqP; apply: (same_stays (succn K)).
      - move/eqP: KL; rewrite -(eqn_add2r 1); move/eqP => KL.
        rewrite -KL addn1 prednK //.
        suff I : a1.+1 <= A K.+1 by apply: leq_ltn_trans I.
        rewrite -a1_.
        apply: increasing; exact: A_inc.
      - move/eqP: KKL; rewrite -(eqn_add2r 1); move/eqP => KKL.
        rewrite - KKL addn1 prednK //.
        suff I : a1.+1 <= A K.+2 by apply: leq_ltn_trans I.
        rewrite -a1_; apply: increasing; exact: A_inc.
      - exact: Kx.
    * rewrite -ltnS; by apply: ltn_leq_trans (leqSpred m).
Qed.

Lemma dvdn_0 : forall n, n <> 0 -> ~ 0 %| n. Proof. rewrite /dvdn /modn. case => //=. Qed.

Lemma divn_lt0 : forall a b, 0 < a -> 0 < a %/ (gcdn a b).
Proof.
move=> a b Ha.
rewrite divn_gt0.
apply dvdn_leq => //.
apply dvdn_gcdl.
rewrite gcdn_gt0 Ha //.
Qed.

Lemma modn_subr_eq m a b : b * m <= a -> a - b * m = a %[mod b].
Proof.
move=> H.
apply/eqP.
by rewrite -(eqn_modDr (b * m)) subnK // addnC mulnC modnMDl.
Qed.

Module comparison.

Inductive cmp : Type := LT | EQ | GT.

Module Compare.
Section Compare.

Variable A : Type.
Variable lt : A -> A -> Prop.
Variable compare : A -> A -> cmp.

CoInductive reflect_cmp (x y: A): cmp -> Set :=
| Reflect_LT: lt x y -> ~(x = y) -> ~(lt y x) -> reflect_cmp x y LT
| Reflect_EQ: ~(lt x y) -> x = y -> ~(lt y x) -> reflect_cmp x y EQ
| Reflect_GT: ~(lt x y) -> ~(x = y) -> lt y x -> reflect_cmp x y GT.
End Compare.

Definition axiom T (lt : T -> T -> Prop) (e : T -> T -> cmp) :=
  forall x y, reflect_cmp T lt x y (e x y).

Structure mixin_of T := Mixin {lt : T -> T -> Prop; op : T -> T -> cmp; _ : axiom T lt op}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.
Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.
End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation cmpType := type.
Notation CmpMixin := Mixin.
Notation CmpType T m := (@pack T m).
Notation "[ 'eqMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'eqMixin' 'of' T ]") : form_scope.
Notation "[ 'eqType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'eqType' 'of' T 'for' C ]") : form_scope.
Notation "[ 'eqType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'eqType' 'of' T ]") : form_scope.
End Exports.

End Compare.
Export Compare.Exports.

(*Print Compare.mixin_of.
Check Compare.op.
Check Equality.op.*)

Definition cmp_op T := Compare.op _ (Compare.class T).
Arguments cmp_op [T].
(*Check cmp_op.*)

Definition cmp_lt T := Compare.lt _ (Compare.class T).
(*Check cmp_lt.*)

Lemma cmpE : forall T x, @cmp_op T x = @Compare.op _ (Compare.class T) x.
Proof. by []. Qed.

Lemma cmpP : forall T, Compare.axiom _ (@cmp_lt T) (@cmp_op T).
Proof. case => s [] //=. Qed.

Arguments cmpP {T x y}.

Delimit Scope cmp_scope with CMP.
Open Scope cmp_scope.

Definition eq_cmp c1 c2 := match c1, c2 with | LT, LT => true | EQ, EQ => true | GT, GT => true | _, _ => false end.

Lemma eq_cmpP : Equality.axiom eq_cmp.
Proof.
case; case => //=;
  match goal with
    | |- reflect _ true => apply ReflectT =>//=
    | |- reflect _ false => apply ReflectF =>//=
  end.
Qed.

Canonical Structure cmp_eqMixin := EqMixin eq_cmpP.
Canonical Structure cmp_eqType := Eval hnf in EqType _ cmp_eqMixin.

Definition cmp_cmp (c1 c2 : cmp):=
  match c1, c2 with
    | LT, LT => EQ
    | LT, _ => LT
    | EQ, LT => GT
    | EQ, EQ => EQ
    | EQ, GT => LT
    | GT, GT => EQ
    | GT, _ => GT
  end.

Inductive lt_cmp: cmp -> cmp -> Prop :=
| lt_LT_EQ: lt_cmp LT EQ
| lt_LT_GT: lt_cmp LT GT
| lt_EQ_GT: lt_cmp EQ GT.

Lemma cmp_cmpP: Compare.axiom _ lt_cmp cmp_cmp.
case; case => //=;
match goal with
  | |- Compare.reflect_cmp _ _ _ _ EQ =>
    apply Compare.Reflect_EQ => //=; [ move => H; inversion H | move => H; inversion H ]
  | |- Compare.reflect_cmp _ _ _ _ LT =>
    apply Compare.Reflect_LT => //=; [ constructor | move => H; inversion H ]
  | |- Compare.reflect_cmp _ _ _ _ GT =>
    apply Compare.Reflect_GT => //=; [ move => H; inversion H | constructor ]
  | |- _ => idtac
end.
Qed.

Canonical Structure cmp_cmpMixin := CmpMixin _ _ _ cmp_cmpP.
Canonical Structure cmp_cmpType := Eval hnf in CmpType _ cmp_cmpMixin.

Notation "x < y" := (cmp_op x y == LT)
  (at level 70, no associativity) : bool_scope.

Notation "x <= y" := ((cmp_op x y == LT) || (cmp_op x y == EQ))
  (at level 70, no associativity) : bool_scope.

Notation "x > y" := (cmp_op x y == GT)
  (at level 70, no associativity) : bool_scope.

Notation "x >= y" := ((cmp_op x y == GT) || (cmp_op x y == EQ))
  (at level 70, no associativity) : bool_scope.

Notation "x === y" := (cmp_op x y == EQ)
  (at level 70, no associativity) : bool_scope.

Fixpoint cmp_nat (x y : nat):=
  match x, y with
    | O, O => EQ
    | S _, O => GT
    | O, S _ => LT
    | S x, S y => cmp_nat x y
  end.

Inductive lt_nat : nat -> nat -> Prop :=
| lt_O_S : forall x, lt_nat O (S x)
| lt_S_S : forall x y, lt_nat x y -> lt_nat (S x) (S y).

Lemma cmp_natP: Compare.axiom _ lt_nat cmp_nat.
Proof.
red; induction x => //=.
- case.
  + constructor; [move => H; inversion H | done | move => H; inversion H].
  + move => n; constructor; [constructor | done | move => H; inversion H].
- case => //=.
  + constructor; [move => H; inversion H | done | constructor].
  + move => n.
    move: {IHx}(IHx n) => H; inversion H.
    * constructor => //=.
      - constructor => //=.
      - move/eqP=> //= H4; simpl in H4.
        apply: H2.
        apply/eqP.
        by rewrite -eqSS.
      - by move => H4; inversion H4; subst; clear H4.
    * constructor => //=.
      - by move => H4; inversion H4; subst; clear H4.
      - by apply/eqP; rewrite eqSS; apply/eqP.
      - by move => H4; inversion H4; subst; clear H4.
    * constructor => //=.
      - by move => H4; inversion H4; subst; clear H4.
      - move/eqP=> //= H4; simpl in H4.
        apply: H2.
        apply/eqP.
        by rewrite -eqSS.
      - by constructor.
Qed.

Canonical Structure nat_cmpMixin := CmpMixin _ _ _ cmp_natP.
Canonical Structure nat_cmpType := Eval hnf in CmpType _ nat_cmpMixin.

End comparison.

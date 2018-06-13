(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple.

Set Implicit Arguments.
Unset Strict Implicit.

Section Type_ext.

Variable A : Type.

Lemma thead_tuple1 : forall (i : 1.-tuple A), [tuple thead i] = i.
Proof. move=> [ [|h []] H] //. by apply val_inj. Qed.

Lemma behead_tuple1: forall (i : 1.-tuple A), behead i = nil.
Proof. move => [] [] //= _ [] //=. Qed.

End Type_ext.

Section eqType_ext.

Variable A : eqType.

(* compute the last element of a non-empty tuple *)
Definition tlast {n: nat} (t: {:n.+1.-tuple A}) : A :=
  last (thead t) (behead t).

(* compute the rcons on tuples *)
Definition trcons {n: nat} (t: {:n.-tuple A}) (e: A) : {:n.+1.-tuple A}.
Proof.
refine (@Tuple _ _ (rcons t e) _).
by rewrite size_rcons size_tuple.
Defined.

(* t minus its last item *)
Definition tbelast {n : nat} (t : {:n.+1.-tuple A}) : {:n.-tuple A}.
Proof.
exists (belast (thead t) (behead t)).
by rewrite size_belast size_behead size_tuple.
Defined.

Lemma thead_belast n : forall (t : {:n.+2.-tuple A}),
  thead [tuple of belast (thead t) (behead t)] = thead t.
Proof.
case/tupleP => h1. case/tupleP => h2 t /=; by rewrite !theadE.
Qed.

Lemma thead_tbelast n : forall (t : {:n.+2.-tuple A}),
  thead (tbelast t) = thead t.
Proof.
case/tupleP => h1. case/tupleP => h2 t /=; by rewrite !theadE.
Qed.

Lemma tlast_tbelast n : forall (t : {:n.+2.-tuple A}),
  thead (tbelast t) = thead t.
Proof.
case/tupleP => h1. case/tupleP => h2 t /=; by rewrite !theadE.
Qed.

Lemma thead_trcons n e : forall (t : {:n.+1.-tuple A}), thead (trcons t e) = thead t.
Proof. case/tupleP => h1 => //=. Qed.

Lemma trcons_tbelast_tlast {n} (p: {:n.+1.-tuple A}) :
  trcons (tbelast p) (tlast p) = p.
Proof.
apply val_inj => /=.
rewrite /tlast -lastI.
by case: (tupleP p).
Qed.

Lemma behead_trcons : forall {n} e (p : {:n.+1.-tuple A}),
  behead (trcons p e) = rcons (behead p) e.
Proof. move => n e. by case/tupleP. Qed.

Lemma tlast_trcons {n} : forall e (p : {:n.-tuple A}), tlast (trcons p e) = e.
Proof.
case: n => [|n] e p.
- by rewrite (tuple0 p).
- by rewrite /tlast behead_trcons last_rcons.
Qed.

Lemma decomp_tuple {n} : forall (t: {:n.+2.-tuple A}),
  cons (thead t) (rcons (behead (tbelast t)) (tlast t)) = t.
Proof.
case/tupleP => h1.
case/tupleP => h2 t /=.
by rewrite !theadE /= -lastI.
Qed.

Definition tbehead {n : nat} (t : {:n.+1.-tuple A}) : {:n.-tuple A}.
Proof.
refine (@Tuple _ _ (behead t) _).
by rewrite size_behead size_tuple.
Defined.

Lemma tbeheadE x n : forall (t : n.+1.-tuple A), tbehead [tuple of x :: t] = [tuple of t].
Proof.
case/tupleP => h1 t /=.
by apply/eqP; rewrite /eq_op; simpl.
Qed.

Lemma tlastE x n : forall (t : n.+1.-tuple A), tlast [tuple of x :: t] = tlast t.
Proof. by case/tupleP. Qed.

End eqType_ext.

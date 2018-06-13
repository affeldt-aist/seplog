(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Ltac typeof X := type of X.

From mathcomp Require Import ssreflect ssrbool eqtype.
Require ProofIrrelevance.

Notation "'|_' x '_|'" := (Some x)
  (at level 55, right associativity) : core_scope.
Notation "'|_' s , h '_|'" := (Some (s, h))
  (at level 55, right associativity) : core_scope.

Section core.

Context {A : Type}.

Lemma not_Some_is_None (v : option A) : ~ (exists k, v = Some k) -> v = None.
Proof. destruct v => // H; exfalso. apply H; by exists a. Qed.

Lemma None_is_not_Some (v : option A) : v = None -> ~ (exists k, v = Some k).
Proof. move=> ->; by case. Qed.

Lemma optionT_dec : forall (a : option A), sigT (fun l => a = Some l) + {a = None}.
Proof.
move=> [].
left; by exists a.
by right.
Defined.

Lemma option_decT : forall (H : forall (x y : A), {x = y} + {x <> y}) (a : option A),
  sigT (fun l => a = Some l) + {a = None}.
Proof.
move=> H [].
left; by exists a.
by right.
Defined.

Lemma constructive_indefinite_description' :
  forall (P : A -> Prop), { x : A | P x } -> exists x, P x.
Proof. move=> P [x' Px']; by exists x'. Qed.

End core.

Section eqtype.

Context {A : eqType}.

Definition option_dec (a : option A) : sigT (fun l => a = Some l) + {a = None} :=
match a with
| Some a' => inleft (@existT A (fun l => |_ a' _| = |_ l _|) a' Logic.eq_refl)
| None => inright Logic.eq_refl
end.

Lemma eq_comparable_eq (x : A) : eq_comparable x x = left (x <> x) (Logic.eq_refl x).
Proof.
case: eq_comparable.
move=> H.
f_equal.
by apply eq_irrelevance.
move=> b.
exfalso.
by [].
Qed.

Lemma eq_comparable_neq (x y : A) (H : x <> y) : eq_comparable x y = right (x = y) H.
Proof.
case: eq_comparable.
move=> H'.
exfalso.
apply H; apply H'.
move=> H'.
f_equal.
by apply ProofIrrelevance.proof_irrelevance.
Qed.

End eqtype.

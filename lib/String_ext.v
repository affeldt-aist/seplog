(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import Ascii String ZArith.
Export String.

Lemma eqaP : Equality.axiom ascii_dec.
Proof.
  move => x y.
  simpl.
  case (ascii_dec x y).
  - exact: ReflectT.
  - exact: ReflectF.
Qed.

Canonical ascii_eqMixin := EqMixin eqaP.
Canonical ascii_eqType := Eval hnf in EqType ascii ascii_eqMixin.

Definition eq_string (a b : string) : bool :=
  match string_dec a b with left _ => true| right _ => false end.

Lemma eq_string_refl : forall s, eq_string s s.
Proof.
elim=> // h t; rewrite /eq_string.
case: (string_dec _ _) => // _ _; by case: (string_dec _ _).
Qed.

Lemma eq_stringP : Equality.axiom eq_string.
Proof. move=> x y; apply: (iffP idP); rewrite /eq_string; by case: (string_dec _ _). Qed.

Canonical Structure string_eqMixin := EqMixin eq_stringP.
Canonical Structure string_eqType := Eval hnf in EqType _ string_eqMixin.

Lemma eq_string_eq : forall a b, eq_string a b -> a = b.
Proof. move=> a b; by move/eqP. Qed.

Fixpoint string2asciis (s : string) : seq ascii :=
  match s with
    | EmptyString => nil
    | String hd tl => cons hd (string2asciis tl)
  end.

Lemma string2asciis_inj : forall m n, string2asciis m = string2asciis n -> m = n.
Proof.
elim; first by case. move=> h t IH [|h' t'] //= [] ? H; subst h'; f_equal; by apply IH.
Qed.

Lemma string_decxx str : string_dec str str = left Logic.eq_refl.
Proof.
destruct string_dec => //.
f_equal.
apply eq_irrelevance.
Qed.

Local Open Scope char_scope.
Local Open Scope Z_scope.

Definition oZ_of_hex (c : Ascii.ascii) : option Z :=
  match c with
    | "0" => Some 0 | "1" => Some 1 | "2" => Some 2 | "3" => Some 3
    | "4" => Some 4 | "5" => Some 5 | "6" => Some 6 | "7" => Some 7
    | "8" => Some 8 | "9" => Some 9 | "A" => Some 10 | "B" => Some 11
    | "C" => Some 12 | "D" => Some 13 | "E" => Some 14 | "F" => Some 15
    | _ => None
  end.

Local Close Scope Z_scope.
Local Close Scope char_scope.

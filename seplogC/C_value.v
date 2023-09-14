(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import div tuple path.
Require Import Init_ext ssrZ ZArith_ext String_ext Max_ext.
Require Import machine_int seq_ext ssrnat_ext tuple_ext path_ext.
Require order finmap.
Import MachineInt.
Require Import C_types C_types_fp.

Declare Scope C_value_scope.
Declare Scope heap_scope.

Local Open Scope C_types_scope.

Unset Elimination Schemes.

Definition i8_of_ptr (ptr : int ptr_len) : seq (int 8) := int_break erefl ptr.
Notation "'i8<=ptr'" := (i8_of_ptr) (at level 9) : C_value_scope.
Local Open Scope C_value_scope.

Definition optr_of_i8 (l : seq (int 8)) : option (int ptr_len) := int_flat erefl l.
Notation "'optr<=i8'" := (optr_of_i8) (at level 9) : C_value_scope.

Lemma optr_of_i8_Some l : size l = sizeof_ptr -> {x | optr<=i8 l = Some x}.
Proof. move=> Hl. by apply int_flat_Some. Qed.

Definition i8_of_i32 (i : int 32) : seq (int 8) := @int_break 32 8 4 erefl i.
Notation "'i8<=i32'" := (i8_of_i32) (at level 9) : C_value_scope.

Definition oi32_of_i8 (l : seq (int 8)) : option (int 32) := @int_flat 32 8 4 erefl l.
Notation "'oi32<=i8'" := (oi32_of_i8) (at level 9) : C_value_scope.

Lemma oi32_of_i8_inj x y a : oi32<=i8 x = Some a -> oi32<=i8 y = Some a -> x = y.
Proof. move=> *. eapply (@int_flat_inj 8%nat 4 x y 32 a); eauto. Qed.

Lemma oi32_of_i8_Some (l : seq (int 8)) : size l = 4%nat -> {x | oi32<=i8 l = Some x}.
Proof. move=> Hl. by apply int_flat_Some. Qed.

Definition i32_of_i8 (l : seq (int 8)) (Hl : size l = 4%nat) : int 32 := int_flat_ok erefl Hl.
Notation "'i32<=i8'" := (i32_of_i8) (at level 9) : C_value_scope.

Lemma i32_of_i8_irr l1 l2 H1 H2 : l1 = l2 -> i32<=i8 l1 H1 = i32<=i8 l2 H2.
Proof. move=> ?; subst l1. congr (i32<=i8 _ _). by apply eq_irrelevance. Qed.

Lemma i32_of_i8_inj l1 Hl1 l2 Hl2 : i32<=i8 l1 Hl1 = i32<=i8 l2 Hl2 -> l1 = l2.
Proof. rewrite /i32_of_i8. move/int_flat_ok_inj. by apply. Qed.

Lemma i8_of_i32K z H : i32_of_i8 (i8_of_i32 z) H = z.
Proof. rewrite /i32_of_i8 /i8_of_i32. by apply int_flat_int_flat_ok, int_flat_int_break. Qed.

Lemma oi32_of_i8_bij a b : oi32_of_i8 a = Some b -> i8_of_i32 b = a.
Proof.  rewrite /oi32_of_i8 /i8_of_i32 /= => H. by apply int_flat_break. Qed.

Lemma i32_of_i8_bij (a : seq (int 8)) (b : int 32) : forall H,
  i32_of_i8 a H = b -> i8_of_i32 b = a.
Proof.
move=> H H'.
apply oi32_of_i8_bij.
move: H'; by apply int_flat_ok_int_flat.
Qed.

Lemma i32_of_i8_bij2 (a : seq (int 8)) (b : int 32) (H : size a = 4%nat) :
  i8_of_i32 b = a -> i32_of_i8 a H = b.
Proof. rewrite /i8_of_i32 /i32_of_i8 => b_a. by apply int_flat_int_flat_ok, int_break_flat. Qed.

Lemma i32_of_i8_bij3 (a : seq (int 8)) (b : int 32) (H : size a = 4%N) :
   oi32_of_i8 a = Some b -> i32_of_i8 a H = b.
Proof. move=> H'. by apply i32_of_i8_bij2, oi32_of_i8_bij. Qed.

Lemma i8_of_i32Ko b : oi32_of_i8 (i8_of_i32 b) = Some b.
Proof. by rewrite /oi32_of_i8 /i8_of_i32 /= int_flat_int_break. Qed.

Definition i16_of_i8 (l : seq (int 8)) (Hl : size l = 2%nat) : int 16 := int_flat_ok erefl Hl.
Notation "'i16<=i8'" := (i16_of_i8) (at level 9) : C_value_scope.

Local Open Scope zarith_ext_scope.

Definition ptr_of_i8 (l : seq (int 8)) (Hl : size l = sizeof_ptr) : int ptr_len := int_flat_ok erefl Hl.
Notation "'ptr<=i8'" := (ptr_of_i8) (at level 9) : C_value_scope.

Lemma i8_of_ptrK z H : ptr<=i8 (i8<=ptr z) H = z.
Proof. rewrite /ptr_of_i8 /i8_of_ptr. by apply int_flat_int_flat_ok, int_flat_int_break. Qed.

Lemma i8_of_ptrKo b : optr<=i8 (i8<=ptr b) = Some b.
Proof. by rewrite /optr_of_i8 /i8_of_ptr /= int_flat_int_break. Qed.

Lemma optr_of_i8_bij a b : optr_of_i8 a = Some b -> i8_of_ptr b = a.
Proof.  rewrite /optr_of_i8 /i8_of_ptr /= => H; by apply int_flat_break. Qed.

Lemma ptr_of_i8_bij2 (a : seq (int 8)) (b : int ptr_len) (H : size a = sizeof_ptr) :
  i8_of_ptr b = a -> ptr_of_i8 a H = b.
Proof. rewrite /i8_of_ptr /ptr_of_i8 => b_a. by apply int_flat_int_flat_ok, int_break_flat. Qed.

Lemma optr_of_i8_bij3 (a : seq (int 8)) (b : int ptr_len) (H : size a = sizeof_ptr%N) :
   optr_of_i8 a = Some b -> ptr_of_i8 a H = b.
Proof. move=> H'. by apply ptr_of_i8_bij2, optr_of_i8_bij. Qed.

Lemma optr_of_i8_inj x y a : optr_of_i8 x = Some a -> optr_of_i8 y = Some a -> x = y.
Proof. move=> *. eapply (@int_flat_inj 8%nat sizeof_ptr x y ptr_len a); eauto. Qed.

Lemma ptr_of_i8_inj x y Hx Hy : ptr_of_i8 x Hx = ptr_of_i8 y Hy -> x = y.
Proof.
move=> H.
rewrite /ptr_of_i8 in H.
by apply (@int_flat_ok_inj ptr_len 8%nat sizeof_ptr erefl x Hx y Hy).
Qed.

Definition i8_of_i64 (i : int 64) : seq (int 8) := @int_break 64 8 8 Logic.eq_refl i.
Notation "'i8<=i64'" := (i8_of_i64) (at level 9) : C_value_scope.

Definition oi64_of_i8 (l : seq (int 8)) : option (int 64) := @int_flat 64 8 8 Logic.eq_refl l.
Notation "'oi64<=i8'" := (oi64_of_i8) (at level 9) : C_value_scope.

Definition i64_of_i8 (l : seq (int 8)) (Hl : size l = 8%nat) : int 64 := int_flat_ok erefl Hl.
Notation "'i64<=i8'" := (i64_of_i8) (at level 9) : C_value_scope.

Lemma i8_of_i64K z H : i64_of_i8 (i8_of_i64 z) H = z.
Proof. rewrite /i64_of_i8 /i8_of_i64. by apply int_flat_int_flat_ok, int_flat_int_break. Qed.

Lemma i64_of_i8_inj l1 Hl1 l2 Hl2 : i64_of_i8 l1 Hl1 = i64_of_i8 l2 Hl2 -> l1 = l2.
Proof. rewrite /i64_of_i8. move/int_flat_ok_inj. by apply. Qed.

Lemma oi64_of_i8_bij a b : oi64_of_i8 a = Some b -> i8_of_i64 b = a.
Proof. rewrite /oi64_of_i8 /i8_of_i64 /= => H. by apply int_flat_break. Qed.

Lemma i8_of_i64Ko b : oi64_of_i8 (i8_of_i64 b) = Some b.
Proof. by rewrite /oi64_of_i8 /i8_of_i64 /= int_flat_int_break. Qed.

Definition i8_to_i8 (l : seq (int 8)) (Hl : size l = 1%nat) : int 8 :=
  if l is x :: nil then x else Z2u 8 0 (* dummy *).

Lemma i8_to_i8_inj l1 Hl1 l2 Hl2 : i8_to_i8 l1 Hl1 = i8_to_i8 l2 Hl2 -> l1 = l2.
Proof.
move=> Heq.
rewrite /i8_to_i8 in Heq.
destruct l1 as [|h1 [|]] => //.
destruct l2 as [|h2 [|]] => //.
by subst h1.
Qed.

(** Definition of physical values *)

Record phy {g} (t : g.-typ) : Type := mkPhy {
  phy2seq :> seq (int 8) ;
  Hphy : size phy2seq = sizeof t }.
Arguments phy2seq [g] [t] _.
Arguments mkPhy [g] _ _ _.

Notation "ty '.-phy'" := (phy ty) (at level 2, format "ty '.-phy'") : C_value_scope.

Lemma mkPhy_irrelevance {g} (t : g.-typ) (pv pv' : t.-phy) :
  phy2seq pv = phy2seq pv' -> pv = pv'.
Proof.
destruct pv. destruct pv' => /= ?; subst phy2seq0.
congr mkPhy.
by apply eq_irrelevance.
Qed.

Lemma size_phy2seq {g} {ty : g.-typ} (v : ty.-phy) : size v = sizeof ty.
Proof. by destruct v. Qed.

Section PhyEqType.

Variable g : wfctxt.
Variable ty : g.-typ.

Definition phy_eq (v w : phy ty) := phy2seq v == phy2seq w.

Lemma phy_eqP : Equality.axiom phy_eq.
Proof.
move => [] l1 Hl1 [] l2 Hl2 //=.
rewrite /phy_eq /=.
case: eqP => ?.
- subst l2.
  constructor.
  by rewrite (eq_irrelevance Hl1 Hl2).
- econstructor. by case.
Qed.

Canonical Structure phy_eqMixin := EqMixin phy_eqP.
Canonical Structure phy_eqType := Eval hnf in EqType (phy ty) phy_eqMixin.

End PhyEqType.

(** from physical values to machine integers ... *)

Definition ui32_of_phy {g} (pv : (g.-ityp: uint).-phy) : int 32 :=
  match option_dec (oi32_of_i8 pv) with
    | inright _ => Z2u 32 0 (* dummy (cannot happen) *)
    | inleft i => projT1 i
  end.
Notation "'ui32<=phy'" := (ui32_of_phy) (at level 9) : C_value_scope.

Lemma oi32_of_i8_ui32_of_phy {g} : forall (pv : (g.-ityp: uint).-phy),
  oi32_of_i8 pv = Some (ui32<=phy pv).
Proof.
case=> l Hl /=.
rewrite /ui32_of_phy /=.
case: option_dec.
- by case.
- rewrite /oi32_of_i8.
  by case: (int_flat_Some erefl Hl) => l_ ->.
Qed.

Lemma i8_of_ui32_of_phyK {g} (pv : (g.-ityp: uint).-phy) : i8<=i32 (ui32<=phy pv) = pv.
Proof.
rewrite /ui32_of_phy /=.
move Ho : (option_dec _) => [ [s Hs] /= | ].
  by apply int_flat_break.
move=> _. by rewrite oi32_of_i8_ui32_of_phy in Ho.
Qed.

Definition si32_of_phy {g} (pv : (g.-ityp: sint).-phy) : int 32 :=
  match option_dec (oi32_of_i8 pv) with
    | inright _ => Z2s 32 0 (* dummy (cannot happen) *)
    | inleft i => projT1 i
  end.
Notation "'si32<=phy'" := (si32_of_phy) (at level 9) : C_value_scope.

Lemma si32_of_phy_inj {g} : forall (pv1 pv2 : (g.-ityp: sint).-phy),
  si32<=phy pv1 = si32<=phy pv2 -> pv1 = pv2.
Proof.
move=> [pv1 H1] [pv2 H2].
rewrite /si32_of_phy /=.
have H1' : size pv1 = 4%nat by rewrite H1 sizeof_ityp.
have H2' : size pv2 = 4%nat by rewrite H2 sizeof_ityp.
case/oi32_of_i8_Some : H1' => x1 H1'; rewrite H1'.
case/oi32_of_i8_Some : H2' => x2 H2'; rewrite H2'.
move=> /= ? ; subst x1.
apply mkPhy_irrelevance.
by apply oi32_of_i8_inj with x2.
Qed.

Lemma oi32_of_i8_si32_of_phy {g} : forall (pv : (g.-ityp: sint).-phy),
  oi32<=i8 pv = Some (si32<=phy pv).
Proof.
case=> l Hl /=.
rewrite /si32_of_phy /=.
case: option_dec.
- by case.
- rewrite /oi32_of_i8.
  by case: (int_flat_Some erefl Hl) => l_ ->.
Qed.

Definition i8_of_phy {g} (pv : (g.-ityp: uchar).-phy) : int 8 :=
  match phy2seq pv with
    | hd :: nil => hd
    | _ => Z2u 8 0 (* dummy (cannot happen) *)
  end.
Notation "'i8<=phy'" := (i8_of_phy) (at level 9) : C_value_scope.

Lemma phy2seq_i8_of_phy {g} : forall (pv : (g.-ityp: uchar).-phy),
  phy2seq pv = [:: i8<=phy pv].
Proof. case=> l Hl /=. rewrite /i8_of_phy /=. by case: l Hl => // hd []. Qed.

Lemma i8_of_phy_inj {g} : forall pv1 pv2,
  @i8_of_phy g pv1 = i8_of_phy pv2 -> pv1 = pv2.
Proof.
move=> [pv1 H1] [pv2 H2].
rewrite /i8_of_phy /=.
have H1' : size pv1 = 1%nat by rewrite H1 sizeof_ityp.
have H2' : size pv2 = 1%nat by rewrite H2 sizeof_ityp.
destruct pv1; first by done.
destruct pv2; first by done.
destruct pv1; last by done.
destruct pv2; last by done.
move => ?; subst.
by have ->: H1 = H2 by apply/eq_irrelevance.
Qed.

Definition i64_of_phy {g} (pv : (g.-ityp: ulong).-phy) : int 64 :=
  match option_dec (oi64_of_i8 pv) with
    | inright _ => Z2s 64 0 (* dummy (cannot happen) *)
    | inleft i => projT1 i
  end.
Notation "'i64<=phy'" := (i64_of_phy) (at level 9) : C_value_scope.

Lemma oi64_of_i8_i64_of_phy {g} : forall (pv : (g.-ityp: ulong).-phy),
  oi64_of_i8 pv = Some (i64_of_phy pv).
Proof.
case=> l Hl /=.
rewrite /i64_of_phy /=.
case: option_dec.
- by case.
- rewrite /oi64_of_i8.
  by case: (int_flat_Some erefl Hl) => l_ ->.
Qed.

Lemma i64_of_phyK {g} (pv : (g.-ityp: ulong).-phy) : i8<=i64 (i64<=phy pv) = pv.
Proof.
rewrite /i64_of_phy /=.
move Ho : (option_dec _) => [ [s Hs] /= | ].
  by apply int_flat_break.
move=> _. by rewrite oi64_of_i8_i64_of_phy in Ho.
Qed.

Definition ptr_of_phy {g} {t : g.-typ} (pv : (:* t).-phy) : int ptr_len :=
  match option_dec (optr_of_i8 pv) with
    | inright _ => Z2u ptr_len 0 (* dummy *)
    | inleft i => projT1 i
  end.
Notation "'ptr<=phy'" := (ptr_of_phy) (at level 9) : C_value_scope.

Lemma ptr_of_phy_inj {g} {t : g.-typ} : forall (pv1 : (:* t).-phy) pv2,
  ptr<=phy pv1 = ptr<=phy pv2 -> pv1 = pv2.
Proof.
move=> [pv1 H1] [pv2 H2].
rewrite /ptr_of_phy /=.
have H1' : size pv1 = sizeof_ptr by rewrite H1 sizeof_ptyp.
have H2' : size pv2 = sizeof_ptr by rewrite H2 sizeof_ptyp.
case/optr_of_i8_Some : H1' => x1 H1'; rewrite H1'.
case/optr_of_i8_Some : H2' => x2 H2'; rewrite H2'.
move=> /= ? ; subst x1.
apply mkPhy_irrelevance.
eapply int_flat_inj; eauto.
Qed.

Lemma optr_of_i8_of_phy {g} {ty : g.-typ} : forall (pv : (:* ty).-phy),
  optr<=i8 pv = Some (ptr<=phy pv).
Proof.
case=> l Hl /=.
rewrite /ptr_of_phy.
case: option_dec; first by case.
rewrite /optr_of_i8 /=.
have Hl' : size l = sizeof_ptr by rewrite Hl sizeof_ptyp.
by case: (int_flat_Some erefl Hl') => l_ ->.
Qed.

(** from machine integers to physical values *)

Definition phy_of_ui8 {g} (i : int 8) := mkPhy (g.-ityp: uchar) [:: i] erefl.
Notation "'phy<=ui8'" := (phy_of_ui8) (at level 9) : C_value_scope.

Definition phy_of_si8 {g} (i : int 8) := mkPhy (g.-ityp: schar) [:: i] erefl.
Notation "'phy<=si8'" := (phy_of_si8) (at level 9) : C_value_scope.

Lemma Hphy_of_ui32 {g} (i : int 32) : size (i8<=i32 i) = sizeof (g.-ityp: uint).
Proof. by rewrite /i8_of_i32 size_int_break. Qed.

Definition phy_of_ui32 {g} (i : int 32) := mkPhy (g.-ityp: uint) _ (Hphy_of_ui32 i).
Notation "'phy<=ui32'" := (phy_of_ui32) (at level 9) : C_value_scope.

Lemma phy_of_ui32_inj {g} i j : @phy_of_ui32 g i = @phy_of_ui32 g j -> i = j.
Proof. case. move/int_break_inj. by apply. Qed.

Lemma phy_of_ui32K {g} i : ui32<=phy (@phy_of_ui32 g i) = i.
Proof.
rewrite /ui32_of_phy.
case: option_dec => [ [l Hl] | ] //=.
- by rewrite oi32_of_i8_ui32_of_phy /ui32_of_phy /= i8_of_i32Ko /= in Hl; case: Hl => ->.
- by rewrite i8_of_i32Ko.
Qed.

Lemma Hphy_of_si32 {g} (i : int 32) : size (i8<=i32 i) = sizeof (g.-ityp: sint).
Proof. by rewrite /i8_of_i32 size_int_break. Qed.

Definition phy_of_si32 {g} (i : int 32) := mkPhy (g.-ityp: sint) _ (Hphy_of_si32 i).
Notation "'phy<=si32'" := (phy_of_si32) (at level 9) : C_value_scope.

Lemma phy_of_si32K {g} (i :int 32) : si32<=phy (@phy_of_si32 g i) = i.
Proof.
rewrite /si32_of_phy.
case: option_dec => [ [l Hl] | ] //=.
- by rewrite oi32_of_i8_si32_of_phy /si32_of_phy /= i8_of_i32Ko /= in Hl; case: Hl => ->.
- by rewrite i8_of_i32Ko.
Qed.

Lemma si32_of_phyK {g} (i : (g.-ityp: sint).-phy) : phy<=si32 (si32<=phy i) = i.
Proof.
case: i => [i Hi] /=.
apply si32_of_phy_inj.
by rewrite phy_of_si32K.
Qed.

Lemma phy_of_si32_inj {g} x y : @phy_of_si32 g x = @phy_of_si32 g y -> x = y.
Proof. case. rewrite /i8_of_i32. move/int_break_inj; by auto. Qed.

Lemma ui32_of_phyK {g} : forall pv : (g.-ityp: _).-phy, phy<=ui32 (ui32<=phy pv) = pv.
Proof.
case=> l Hl.
rewrite /ui32_of_phy /=.
case: option_dec => [ [] i Hi //= | abs].
- rewrite /phy_of_ui32.
  apply/eqP; rewrite /eq_op /= /phy_eq /=.
  have ?: l = i8_of_i32 i by rewrite (oi32_of_i8_bij _ _ Hi).
  by subst.
- exfalso.
  move: abs.
  rewrite /oi32_of_i8.
  by case: (int_flat_Some erefl Hl) => l_ ->.
Qed.

Lemma phy_of_ui8K {g} i : i8<=phy (@phy_of_ui8 g i) = i. Proof. done. Qed.

Lemma Hphy_of_iu64 {g} (i : int 64) : size (i8<=i64 i) = sizeof (g.-ityp: ulong).
Proof. by rewrite /i8_of_i64 size_int_break. Qed.

Definition phy_of_ui64 {g} (i : int 64) := mkPhy (g.-ityp: ulong) _ (Hphy_of_iu64 i).
Notation "'phy<=i64'" := (phy_of_ui64) (at level 9) : C_value_scope.

Lemma phy_of_ui64_inj {g} i j : @phy_of_ui64 g i = @phy_of_ui64 g j -> i = j.
Proof. case. move/int_break_inj. by apply. Qed.

Lemma phy_of_ui64K {g} i : i64<=phy (@phy_of_ui64 g i) = i.
Proof.
rewrite /i64_of_phy.
case: option_dec => [ [l Hl] | ] //=.
- by rewrite oi64_of_i8_i64_of_phy /i64_of_phy /= i8_of_i64Ko /= in Hl; case: Hl => ->.
- by rewrite i8_of_i64Ko.
Qed.

Lemma Hphy_ptr {g} (t : g.-typ) p : size (i8<=ptr p) = sizeof (:* t).
Proof. by rewrite size_int_break sizeof_ptyp. Qed.

Definition phy_of_ptr {g} (t : g.-typ) (p : int ptr_len) := mkPhy (:* t) _ (Hphy_ptr t p).
Notation "'phy<=ptr'" := (phy_of_ptr) (at level 9) : C_value_scope.

Lemma phy_of_ptr_inj {g} (t : g.-typ) (a b : int ptr_len) :
  phy<=ptr t a = phy<=ptr t b -> a = b.
Proof. rewrite /phy_of_ptr. case. rewrite /i8_of_ptr. by apply int_break_inj. Qed.

Lemma phy_of_ptrK {g} {t : g.-typ} i : ptr<=phy (phy<=ptr t i) = i.
Proof.
rewrite /ptr_of_phy.
case: option_dec => [ [l Hl] | ] //=.
- by rewrite optr_of_i8_of_phy /ptr_of_phy /= i8_of_ptrKo /= in Hl; case: Hl => ->.
- by rewrite i8_of_ptrKo.
Qed.

Lemma ptr_of_phyK {g} {t : g.-typ} : forall v : (:* t).-phy, phy<=ptr t (ptr<=phy v) = v.
Proof.
case => l Hl.
rewrite /ptr_of_phy /=.
case: option_dec => [ [] i Hi //= | abs ].
- rewrite /ptr_of_phy.
  apply/eqP; rewrite /eq_op /= /phy_eq /=.
  have ?: l = i8_of_ptr i by rewrite (optr_of_i8_bij _ _ Hi).
  by subst.
- exfalso.
  move: abs.
  rewrite /optr_of_i8.
  by case: (int_flat_Some erefl Hl) => l_ ->.
Qed.

Structure phy_of_int {g : wfctxt} (n : nat) :=
  { phy_of_int_typ : integral ;
    phy_of_int_fun : int n -> (g.-ityp: phy_of_int_typ).-phy }.
Canonical phy_of_int_8u {g} := @Build_phy_of_int g _ _ phy_of_ui8.
Canonical phy_of_int_8s {g} := @Build_phy_of_int g _ _ phy_of_si8.
Canonical phy_of_int_32u {g} := @Build_phy_of_int g _ _ phy_of_ui32.
Canonical phy_of_int_32s {g} := @Build_phy_of_int g _ _ phy_of_si32.
Canonical phy_of_int_64u {g} := @Build_phy_of_int g _ _ phy_of_ui64.

Definition phy_of_int_nosimpl {g} := nosimpl (@phy_of_int_fun g).
Notation "'[' i ']p'" := (phy_of_int_nosimpl _ _ i) (at level 9) : C_value_scope.

Structure phy_of_Zs {g : wfctxt} :=
  { phy_of_Zs_typ : integral ;
    phy_of_Zs_fun : Z -> (g.-ityp: phy_of_Zs_typ).-phy }.
Canonical phy_of_Z_8s {g} := @Build_phy_of_Zs g _ (fun z => phy<=si8 (Z2s _ z)).
Canonical phy_of_Z_32s {g} := @Build_phy_of_Zs g _ (fun z => phy<=si32 (Z2s _ z)).
Definition phy_of_Zs_nosimpl {g} := nosimpl (@phy_of_Zs_fun g).
Notation "'[' z ']s'" := (phy_of_Zs_nosimpl _ z) (at level 9, format "'[' [  z  ]s ']'") : C_value_scope.

Structure phy_of_Zu {g : wfctxt} :=
  { phy_of_Zu_typ : integral ;
    phy_of_Zu_fun : Z -> (g.-ityp: phy_of_Zu_typ).-phy }.
Canonical phy_of_Zu_8 {g} := @Build_phy_of_Zu g _ (fun z => phy<=ui8 (Z2u _ z)).
Canonical phy_of_Zu_32 {g} := @Build_phy_of_Zu g _ (fun z => phy<=ui32 (Z2u _ z)).
Canonical phy_of_Zu_64 {g} := @Build_phy_of_Zu g _ (fun z => phy_of_ui64 (Z2u _ z)).
Definition phy_of_Zu_nosimpl {g} := nosimpl (@phy_of_Zu_fun g).
Notation "'[' z ']u'" := (phy_of_Zu_nosimpl _ z) (at level 9, format "'[' [  z  ]u ']'") : C_value_scope.

Definition pv0 {g} {t : g.-typ} : t.-phy := mkPhy _ _ (size_nseq (sizeof t) (Z2u 8 0)).

Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.

Lemma phy_of_si32_of_Z2s g (z : Z) :
  (- 2 ^^ 31 <= z < 2 ^^ 31)%Z -> Z<=s (@si32_of_phy g [ Z2s 32 z ]p) = z.
Proof.
move=> Hz.
rewrite /si32_of_phy.
destruct Init_ext.option_dec as [[x e]|e] => /=.
  rewrite i8_of_i32Ko in e.
  case: e => <-.
  by rewrite Z2sK.
by rewrite i8_of_i32Ko in e.
Qed.

Definition is_zero {g} (v : (g.-ityp: uint).-phy) := v == [ 0 ]u.

Lemma not_is_zero_1 {g} : ~~ is_zero ( [ 1 ]u : (_ : g.-typ).-phy).
Proof.
rewrite /is_zero.
apply/negP.
move/eqP/phy_of_ui32_inj.
by apply Z2u_dis.
Qed.

Lemma is_zero_0 {g} : is_zero ( [ 0 ]u : (_ : g.-typ).-phy).
Proof. by rewrite /is_zero. Qed.

(** Definition of logical values *)

Section logval_def.

Variable g : wfctxt.
Implicit Type t : g.-typ.

Inductive log : g.-typ -> Type :=
| log_of_uint : forall t, t = ityp: uint ->
  int 32 -> log t
| log_of_sint : forall t, t = ityp: sint ->
  int 32 -> log t
| log_of_uchar : forall t, t = ityp: uchar ->
  int 8 -> log t
| log_of_ulong : forall t, t = ityp: ulong ->
  int 64 -> log t
| log_of_ptr : forall t t', t = :* t' ->
  int ptr_len -> log t
| log_of_styp : forall t tg, styp tg = t ->
  logs (get_fields g tg) -> log t
| log_of_atyp : forall t n Hn tg (H : Ctyp.ty _ t = atyp n Hn tg),
  alog n (Ctyp_styp (atyp_styp H)) -> log t
with logs : g.-env -> Type :=
| nil_logs : logs nil
| cons_logs : forall hd tl, log hd.2 -> logs tl ->
  logs (hd :: tl)
with alog : nat -> g.-typ -> Type :=
| nil_alog : forall t, alog 0 t
| cons_alog: forall n t, alog n t -> alog n.+1 t.

End logval_def.

Arguments log [g] _.
Arguments log_of_uint [g] _ _ _.
Arguments log_of_sint [g] _ _ _.
Arguments log_of_uchar [g] _ _ _.
Arguments log_of_ulong [g] _ _ _.
Arguments log_of_ptr [g] _ _ _ _.
Arguments log_of_styp [g] _ _ _ _.
Arguments log_of_atyp [g] _ _ _ _ _ _.
Arguments logs {g} _.
Arguments nil_logs {g}.
Arguments cons_logs [g] _ _ _ _.
Arguments alog [g] _ _.
Arguments nil_alog [g] _.
Arguments cons_alog [g] _ _ _.

Notation "t '.-log'" := (log t) (at level 2, format "t '.-log'") : C_value_scope.

Definition mkUintLog {g} : int 32 -> log (g.-ityp: uint) := log_of_uint (g.-ityp: uint) erefl.
Definition mkSintLog {g} : int 32 -> log (g.-ityp: sint) := log_of_sint (g.-ityp: sint) erefl.
Definition mkUcharLog {g} : int 8 -> log (g.-ityp: uchar) := log_of_uchar (g.-ityp: uchar) erefl.
Definition mkUlongLog {g} : int 64 -> log (g.-ityp: ulong) := log_of_ulong (g.-ityp: ulong) erefl.

Local Open Scope C_value_scope.

Set Elimination Schemes.

Scheme log_rect := Induction for log Sort Type
with logs_rect := Induction for logs Sort Type
with alog_rect := Induction for alog Sort Type.

Scheme log_ind := Induction for log Sort Prop
with logs_ind := Induction for logs Sort Prop
with alog_ind := Induction for alog Sort Prop.

(** inversion lemmas *)

Lemma log_of_uint_inv {g} {ty : g.-typ} (H : ty = g.-ityp: uint) (v : ty.-log) :
  exists i, v = log_of_uint _ H i.
Proof.
destruct v => //=.
- exists i; by rewrite (eq_irrelevance H e).
- by subst t.
- by subst t.
- by subst t.
- subst t; by destruct t'.
- by subst t.
- by subst t.
Qed.

Lemma log_of_sint_inv {g} {ty : g.-typ} (H : ty = g.-ityp: sint) (v : ty.-log) :
  exists i, v = log_of_sint _ H i.
Proof.
destruct v => //=.
- by subst t.
- exists i; by rewrite (eq_irrelevance H e).
- by subst t.
- by subst t.
- subst t; by destruct t'.
- by subst t.
- by subst t.
Qed.

Lemma log_of_uchar_inv {g} {ty : g.-typ} (H : ty = g.-ityp: uchar) (v : ty.-log) :
  exists i, v = log_of_uchar _ H i.
Proof.
destruct v => //=.
- by subst t.
- by subst t.
- exists i; by rewrite (eq_irrelevance H e).
- by subst t.
- subst t; by destruct t'.
- by subst t.
- by subst t.
Qed.

Lemma log_of_ulong_inv {g} {ty : g.-typ} (H : ty = g.-ityp: ulong) (v : ty.-log) :
  exists i, v = log_of_ulong _ H i.
Proof.
destruct v => //=.
- by subst t.
- by subst t.
- by subst t.
- exists i; by rewrite (eq_irrelevance H e).
- subst t; by destruct t'.
- by subst t.
- by subst t.
Qed.

Lemma log_of_ptr_inv {g} {ty ty' : g.-typ} (H : ty' = :* ty) (v : ty'.-log) :
  exists i, v = log_of_ptr _ _ H i.
Proof.
destruct v => //=.
- subst t; by destruct ty.
- subst t; by destruct ty.
- subst t; by destruct ty.
- subst t; by destruct ty.
- exists i.
  have Heq : ty = t'.
    subst t.
    by apply Ctyp_ptyp_inj.
  subst t'.
  by rewrite (eq_irrelevance H e).
- subst t; by destruct ty.
- subst t; by destruct ty.
Qed.

Lemma log_of_styp_inv {g} {ty : g.-typ} {s} (H : styp s = ty) v :
  exists vals, v = log_of_styp ty s H vals.
Proof.
destruct v => //=.
- by subst t.
- by subst t.
- by subst t.
- by subst t.
- subst t; by destruct t'.
- have Heq : s = tg by rewrite -H in e; case: e.
  subst tg.
  have Heq : H = e by apply eq_irrelevance.
  subst e.
  by exists l.
- destruct t => //=; simpl in *; by subst ty.
Qed.

(* extracting machine-int's from some logical values *)

Definition uint_of_log {g} (lv : (g.-ityp: uint).-log) :=
  match lv return int 32 with log_of_uint _ _ i => i | _ => zero32 end.

Lemma log_of_uintK {g} i : uint_of_log (@log_of_uint g _ erefl i) = i.
Proof. by []. Qed.

Lemma uint_of_logK {g} v : @log_of_uint g _ erefl (uint_of_log v) = v.
Proof. by move: (log_of_uint_inv erefl v) => [] i ->. Qed.

Definition sint_of_log {g} (lv : (g.-ityp: sint).-log) :=
  match lv return int 32 with log_of_sint t Ht i => i | _ => zero32 end.

Lemma log_of_sintK {g} i : sint_of_log (@log_of_sint g _ erefl i) = i.
Proof. by []. Qed.

Lemma sint_of_logK {g} v : @log_of_sint g _ erefl (sint_of_log v) = v.
Proof. by move: (log_of_sint_inv erefl v) => [] i ->. Qed.

Definition uchar_of_log {g} (lv : (g.-ityp: uchar).-log) :=
  match lv return int 8 with log_of_uchar t Ht c => c | _ => zero8 end.

Lemma log_of_ucharK {g} i : uchar_of_log (@log_of_uchar g _ erefl i) = i.
Proof. by []. Qed.

Lemma uchar_of_logK {g} v : @log_of_uchar g _ (erefl _) (uchar_of_log v) = v.
Proof. by move: (log_of_uchar_inv erefl v) => [] i ->. Qed.

Definition ulong_of_log {g} (lv : (g.-ityp: ulong).-log) :=
  match lv return int 64 with log_of_ulong t Ht i => i | _ => Z2u 64 0 end.

Lemma log_of_ulongK {g} i : ulong_of_log (@log_of_ulong g _ erefl i) = i.
Proof. by []. Qed.

Lemma ulong_of_logK {g} v : @log_of_ulong g _ erefl (ulong_of_log v) = v.
Proof. by move: (log_of_ulong_inv erefl v) => [] i ->. Qed.

Definition ptr_of_log {g} {ty : g.-typ} (v : (:* ty).-log) : int ptr_len :=
  match v with log_of_ptr t t' tt' p => p | _ => Z2u ptr_len 0 end.

Lemma log_of_ptrK {g} t i : ptr_of_log (@log_of_ptr g _ t erefl i) = i.
Proof. by []. Qed.

Lemma ptr_of_logK {g} {ty: g.-typ} v : @log_of_ptr g _ ty erefl (ptr_of_log v) = v.
Proof. by move: (log_of_ptr_inv erefl v) => [] i ->. Qed.

(** logical value set / get *)

Lemma values_get_helper1 g (str : string) (t : g.-typ) h1 h2 (l : g.-env) :
  str <> h1 ->  (str, t) \in (h1, h2) :: l -> (str, t) \in l.
Proof.
rewrite in_cons => H.
case/orP; last by done.
by case/eqP.
Qed.

Lemma values_get_helper2 g (str : string) (t : g.-typ) h1 h2 (l : g.-env) :
  t <> h2 -> (str, t) \in (h1, h2) :: l ->  (str, t) \in l.
Proof.
rewrite in_cons => H.
case/orP; last by done.
by case/eqP.
Qed.

Lemma values_get_helper3 g (str : string) (t : g.-typ) : (str, t) \in nil -> False.
Proof. by rewrite in_nil. Qed.

Fixpoint values_get {g} str (t : g.-typ) (l : g.-env) (vals : logs l) : forall (H : (str, t) \in l), log t :=
  match vals in (logs l) return (str, t) \in l -> log t with
    | nil_logs => fun (H : (str, t) \in nil) => False_rect (log t) (values_get_helper3 _ _ _ H)
    | cons_logs (h1, h2) tl lv vals' => fun (H : (str, t) \in (h1, h2) :: tl) =>
        match string_dec str h1 with
          | right H' => values_get str t tl vals' (values_get_helper1 g str t h1 h2 tl H' H)
          | left H' =>
            match eq_comparable t h2 with
              | left H'' => @eq_rect _ h2 (@log g) lv t (@sym_eq _ _ _ H'')
              | right H'' => values_get str t tl vals' (values_get_helper2 g str t h1 h2 tl H'' H)
          end
      end
  end.

Lemma values_get_eq {g} n (t : g.-typ) l H vhd vtl :
  values_get n t ((n, t) :: l) (cons_logs (n, t) l vhd vtl) H = vhd.
Proof. by rewrite /= string_decxx eq_comparable_eq. Qed.

Lemma values_get_neq {g} n n' (ty : g.-typ) ty' l H H' vhd vtl :
  (n, ty) <> (n', ty') ->
  values_get n ty ((n',ty') :: l) (cons_logs (n', ty') l vhd vtl) H =
  values_get n ty l vtl H'.
Proof.
move=> Hneq /=.
destruct (string_dec n n').
  subst n'.
  rewrite eq_comparable_neq; first by move=> ?; subst ty'.
  move=> tyty'.
  congr values_get.
  by apply eq_irrelevance.
congr values_get.
by apply eq_irrelevance.
Qed.

Fixpoint values_set {g} (n : string_eqType) (ty : g.-typ)
               (v : ty.-log) (l : g.-env) (vals : logs l) :
               forall (H : (n, ty) \in l), logs l :=
match vals in (logs l) return (n, ty) \in l -> logs l with
| nil_logs => fun (H : (n, ty) \in nil) => False_rect (logs nil) (values_get_helper3 _ _ _ H)
| cons_logs (h1, h2) tl lv lvs => fun (H : (n, ty) \in (h1, h2) :: tl) =>
  match string_dec n h1 with
  | right H' => cons_logs (h1, h2) _ lv (values_set n ty v tl lvs (values_get_helper1 g n ty h1 h2 tl H' H))
  | left H' =>
    match eq_comparable ty h2 with
      | left H'' => cons_logs (h1, h2) _ (@eq_rect _ _ (@log g) v h2 (H'')) lvs
      | right H'' => cons_logs (h1, h2) _ lv (values_set n ty v tl lvs (values_get_helper2 g n ty h1 h2 tl H'' H))
    end
  end
end.

Lemma values_set_eq {g} n (t : g.-typ) l H vhd vtl v :
 values_set n t v ((n, t) :: l) (cons_logs (n, t) l vhd vtl) H = (cons_logs (n, t) l v vtl).
Proof. by rewrite /= string_decxx eq_comparable_eq. Qed.

Lemma values_set_neq {g} n n' (ty: g.-typ) ty' l H H' vhd vtl v :
  (n, ty) <> (n', ty') ->
  values_set n ty v ((n',ty')::l) (cons_logs (n', ty') l vhd vtl) H =
  cons_logs (n', ty') l vhd (values_set n ty v l vtl H').
Proof.
move=> Hneq /=.
destruct (string_dec n n').
  subst n'.
  rewrite eq_comparable_neq; first by move=> ?; subst ty'.
  move=> tyty'.
  congr (cons_logs _ _ _ (values_set _ _ _ _ _ _)).
  by apply eq_irrelevance.
congr (cons_logs _ _ _ (values_set _ _ _ _ _ _)).
by apply eq_irrelevance.
Qed.

(** a heap is a list of bytes *)

Module Int8 <: finmap.EQTYPE.
Definition A : eqType := int_eqType 8.
End Int8.

Module hp := finmap.map order.NatOrder Int8.

Notation "k '\d\' m" := (hp.dif k m) (at level 69, format "k  '\d\'  m") : heap_scope.
Notation "k '\U' m" := (hp.union k m) (at level 69, format "k  '\U'  m") : heap_scope.
Notation "k '#' m" := (hp.disj k m) (at level 79, format "k  '#'  m") : heap_scope.
Notation "k '\D\' m" := (hp.difs k m) (at level 69, format "k  '\D\'  m") : heap_scope.
Notation "k '|P|' m" := (hp.proj k m) (at level 69, format "k  '|P|'  m") : heap_scope.
Local Open Scope heap_scope.

(** a few functions about the heap *)

Definition heap_get' {g} (t : g.-typ) a (k : hp.t) : option (seq (int 8)) :=
  match inc (iota a (sizeof t)) (hp.dom k) with
    | false => None
    | true => Some (hp.cdom (k |P| iota a (sizeof t)))
  end.

Lemma heap_get'_sizeof {g} (t : g.-typ) a h l : heap_get' t a h = Some l -> size l = sizeof t.
Proof.
rewrite /heap_get'.
case: ifP => // Hinc.
rewrite /heap_get'.
case => <-.
rewrite hp.size_cdom_dom (hp.size_dom_proj_exact h _) //.
by rewrite size_iota.
by rewrite iota_uniq.
Qed.

Definition heap_get {g} (t : g.-typ) (a : nat) (h : hp.t) : option (t.-phy) :=
  match option_dec (heap_get' t a h) with
    | inleft (existT a Pa) => Some (mkPhy _ _ (heap_get'_sizeof _ _ _ _ Pa))
    | _ => None
end.

Lemma heap_get'_union_L {g} {t : g.-typ} h1 h2 : h1 # h2 ->
  forall (n : hp.l) (z : seq (int 8)), heap_get' t n h1 = Some z -> heap_get' t n (h1 \U h2) = Some z.
Proof.
move=> h1_d_h2 n z.
rewrite /heap_get /heap_get'.
set binc1 := inc _ _.
move X : binc1 => [|] //.
have : inc (iota n (sizeof t)) (hp.dom (h1 \U h2)).
  apply inc_trans with (hp.dom h1); first by assumption.
  apply hp.inclu_inc_dom, hp.inclu_union_L; [assumption | by apply hp.inclu_refl].
move=> Y; rewrite Y.
case=> ?; subst z.
have Htmp : size (hp.cdom (h1 |P| iota n (sizeof t))) = sizeof t.
  rewrite hp.size_cdom_dom hp.size_dom_proj_exact //.
  by rewrite size_iota.
  by rewrite iota_uniq.
have Z : (hp.cdom ((h1 \U h2) |P| iota n (sizeof t))) =
  take (sizeof t) (hp.cdom (h1 |P| iota n (sizeof t))).
  rewrite take_oversize //; last by rewrite Htmp.
  rewrite (hp.proj_restrict h1) //.
  apply hp.inclu_union_L; [assumption | by apply hp.inclu_refl].
rewrite Z take_oversize // Htmp. apply leqnn.
Qed.

Lemma heap_get_value_union_L {g} {ty : g.-typ} h1 h2 : h1 # h2 ->
  forall (n : hp.l) v, heap_get ty n h1 = Some v -> heap_get ty n (h1 \U h2) = Some v.
Proof.
move=> h12 n v.
rewrite /heap_get.
move H : (option_dec _) => h.
destruct h => //.
destruct s as [s Hs].
case => ?; subst v.
move H' : (option_dec _) => h'.
destruct h' => //.
destruct s0 as [s' Hs'].
congr Some.
apply mkPhy_irrelevance => /=.
apply/eqP.
clear H'.
rewrite (heap_get'_union_L _ _ _ _ _ Hs) // in Hs'.
by case: Hs' => ->.
clear H'.
rewrite (heap_get'_union_L _ _ _ _ _ Hs) // in e.
Qed.

Lemma heap_get_inc {g} {t : g.-typ} a val h :
  heap_get t a h = Some val -> inc (iota a (sizeof t)) (hp.dom h).
Proof.
move=> H.
rewrite /heap_get in H.
destruct (option_dec (heap_get' t a h)); last by done.
clear H.
destruct s as [l Hl].
rewrite /heap_get' in Hl.
by destruct (inc (iota a (sizeof t)) (hp.dom h)).
Qed.

(* update *)

Module hp_prop_m := finmap.Map_Prop hp.

Definition bytes2heap (a : nat) (l : seq (int 8)) : hp.t :=
  hp_prop_m.mk_finmap (zip (iota a (size l)) l).

Lemma dom_bytes2heap l a : hp.dom (bytes2heap a l) = iota a (size l).
Proof.
rewrite /bytes2heap -hp.elts_dom hp_prop_m.elts_mk_finmap; last first.
  rewrite unzip1_zip. by apply ordset.ordered_iota.
by rewrite size_iota.
move: unzip1_zip.
rewrite /unzip1.
apply.
by rewrite size_iota.
Qed.

Lemma cdom_bytes2heap a l : hp.cdom (bytes2heap a l) = l.
Proof.
rewrite /bytes2heap -hp.elts_cdom hp_prop_m.elts_mk_finmap; last first.
  rewrite unzip1_zip; last first.
    by rewrite size_iota.
  by apply ordset.ordered_iota.
move: unzip2_zip; rewrite /unzip2; apply.
by rewrite size_iota.
Qed.

Definition heap_upd {g} (t : g.-typ) (a : nat) (v : t.-phy) (k : hp.t) : hp.t :=
  if inc (iota a (size v)) (hp.dom k) then
    (k \D\ iota a (size v)) \U bytes2heap a v
  else
    k.

Lemma dom_heap_upd {g} {t : g.-typ} a v h : hp.dom (heap_upd t a v h) = hp.dom h.
Proof.
rewrite /heap_upd.
case: ifP => // Hinc.
rewrite hp.unionC; last first.
  apply hp.disj_sym, hp.disj_difs'.
  rewrite dom_bytes2heap; by apply inc_refl.
rewrite (_ : iota _ _ = hp.dom (bytes2heap a v)); last by rewrite dom_bytes2heap.
by rewrite -hp.dom_union_difsK // dom_bytes2heap.
Qed.

Lemma heap_no_upd {g} {t : g.-typ} h a v :
  ~ inc (seq.iota a (sizeof t)) (hp.dom h) -> heap_upd t a v h = h.
Proof.
rewrite /heap_upd size_phy2seq.
set b := inc _ _.
by destruct b.
Qed.

Lemma disj_heap_upd {g} {t : g.-typ} a v h1 h2 : h1 # h2 -> heap_upd t a v h1 # h2.
Proof.
move=> Hdisj.
rewrite /heap_upd.
case: ifP => // Hinc.
apply hp.disjUh.
- exact/hp.disj_sym/hp.disj_difs/hp.disj_sym.
- rewrite hp.disjE dis_sym.
  apply: (@dis_inc_R _ _ (hp.dom h1)).
  + by rewrite dis_sym -hp.disjE.
  + apply inc_trans with (List.seq a (sizeof t)).
    * rewrite dom_bytes2heap inc_iota //.
      destruct v as [v Hv] => /=.
      by rewrite Hv.
    * move/incP : Hinc.
      destruct v as [v Hv] => /=.
      move/incP.
      by rewrite Hv.
Qed.

Lemma heap_upd_union_L {g} {t : g.-typ} h1 h2 : h1 # h2 -> forall a v,
  inc (seq.iota a (sizeof t)) (hp.dom h1) ->
  heap_upd t a v (h1 \U h2) = heap_upd t a v h1 \U h2.
Proof.
move=> h1_d_h2 a v Hdom.
rewrite /heap_upd.
destruct v as [v Hv] => /=.
rewrite Hv.
case: ifP => [Hinc | ].
- rewrite Hdom.
  have Htmp : dis (hp.dom h2) (hp.dom (bytes2heap a v)).
    rewrite dom_bytes2heap.
    apply (@dis_inc_R _ _ (hp.dom h1)).
    - rewrite -hp.disjE; by apply hp.disj_sym.
    - apply inc_trans with (iota a (sizeof t)) => //.
      by rewrite inc_iota // Hv.
  rewrite hp.difs_union_L; last by rewrite dom_bytes2heap Hv in Htmp.
  by rewrite -!hp.unionA (hp.unionC h2) // hp.disjE.
- move/negP => Hinc.
  exfalso.
  exact/Hinc/(inc_trans Hdom)/hp_prop_m.incl_dom_union.
Qed.

Lemma heap_upd_union_R {g} (t : g.-typ) (h1 h2 : hp.t) : h1 # h2 ->
  forall a (v : t.-phy), inc (iota a (sizeof t)) (hp.dom h2) ->
    heap_upd t a v (h1 \U h2) = h1 \U heap_upd t a v h2.
Proof.
move=> h1_d_h2 a v Hinc.
rewrite hp.unionC // heap_upd_union_L //; last by apply hp.disj_sym.
rewrite hp.unionC //.
by apply disj_heap_upd, hp.disj_sym.
Qed.

Lemma cdom_heap_upd {g} {t : g.-typ} a (pv : t.-phy) h :
  hp.dom h = hp.dom (bytes2heap a pv) -> hp.cdom (heap_upd t a pv h) = pv.
Proof.
move => Hh.
rewrite dom_bytes2heap in Hh.
destruct pv as [pv Hpv] => /=.
rewrite /= in Hh.
rewrite /heap_upd -Hh inc_refl /= hp.difs_self hp.unioneh.
apply cdom_bytes2heap.
Qed.

(** Physical mapsto *)

Inductive phy_mapsto {g} {t : g.-typ} : t.-phy -> nat -> hp.t -> Prop :=
| mkPhy_mapsto : forall a (v : t.-phy) h,
  hp.cdom h = v ->
  hp.dom h = iota a (sizeof t) ->
  Z<=nat a + Z<=nat (sizeof t) < 2 ^^ ptr_len ->
  align t %| a ->
  phy_mapsto v a h.

Notation "a '|pZ~>' v" := (fun _ => @phy_mapsto _ _ v a) (at level 77, no associativity) : C_value_scope.

Notation "a '|pV~>' v" :=
  (fun _ => phy_mapsto v (nat<=u (ptr<=phy a))) (at level 77, no associativity) : C_value_scope.

Lemma phy_mapsto_eq {g} {t : g.-typ} {pv : t.-phy} {pv' a a' h h'}:
  phy_mapsto pv a h ->
  pv = pv' -> a = a' -> h = h' ->
  phy_mapsto pv' a' h'.
Proof. by move => H <- <- <-. Qed.

Lemma phy_mapsto_heap_eq {g} {t : g.-typ} a (pv : t.-phy) h1 h2 :
  phy_mapsto pv a h1 -> phy_mapsto pv a h2 -> h1 = h2.
Proof.
move=> H1 H2.
inversion H1; subst.
inversion H2; subst.
apply hp.dom_cdom_heap; congruence.
Qed.

Lemma phy_mapsto_overflow {g} {t : g.-typ} {pv : t.-phy} {a h} :
  phy_mapsto pv a h -> Z_of_nat a + Z_of_nat (sizeof t) < 2 ^^ ptr_len.
Proof. by case. Qed.

Lemma phy_mapsto_heap_cdom {g} {t : g.-typ} a (pv : t.-phy) h :
  phy_mapsto pv a h -> hp.cdom h = pv.
Proof. by inversion 1; subst. Qed.

Lemma phy_mapsto_heap_get {g} {t : g.-typ} a (pv : t.-phy) h :
  phy_mapsto pv a h -> heap_get t a h = Some pv.
Proof.
inversion 1; subst.
rewrite /heap_get.
case: option_dec => [ [l Hl] | ].
- congr Some.
  apply mkPhy_irrelevance => /=.
  destruct pv => //=.
  rewrite /heap_get /heap_get' in Hl.
  rewrite H1 in Hl; rewrite inc_refl in Hl.
  rewrite -H1 in Hl; rewrite hp.proj_itself in Hl.
  simpl in H0.
  rewrite H0 in Hl; by case: Hl => ->.
- rewrite /heap_get /heap_get'.
  case: (incP (iota a (sizeof t)) (hp.dom h)) => //=.
  rewrite -H1.
  move/incP.
  by rewrite inc_refl.
Qed.

(** Logical mapsto *)

Unset Elimination Schemes.

Definition phy_of_log {g} {t : g.-typ} (lv : t.-log) : t.-phy :=
  match lv in t.-log return t.-phy with
  | log_of_uint _ H i => eq_rect _ _ (phy_of_ui32 i) _ (sym_eq H)
  | log_of_sint t H i => eq_rect _ _ (phy_of_si32 i) _ (sym_eq H)
  | log_of_uchar t H c => eq_rect _ _ (phy_of_ui8 c) _ (sym_eq H)
  | log_of_ulong t H i => eq_rect _ _ (phy_of_ui64 i) _ (sym_eq H)
  | log_of_ptr t t' H p => eq_rect _ _ (phy_of_ptr _ p) _ (sym_eq H)
  | _ => pv0
  end.

Notation "'phy<=log'" := (phy_of_log) (at level 9) : C_value_scope.

Section log_mapsto_def.

Variable g : wfctxt.

Inductive log_mapsto {g} : forall {t : g.-typ}, t.-log -> nat -> hp.t -> Prop :=
| log_of_uint_mapsto : forall (v : (g.-ityp: uint).-log) a h,
  phy_mapsto (phy<=log v) a h -> log_mapsto v a h
| log_of_sint_mapsto : forall (v : (g.-ityp: sint).-log) a h,
  phy_mapsto (phy<=log v) a h -> log_mapsto v a h
| log_of_uchar_mapsto : forall (v : (g.-ityp: uchar).-log) a h,
  phy_mapsto (phy<=log v) a h -> log_mapsto v a h
| log_of_ulong_mapsto : forall (v : (g.-ityp: ulong).-log) a h,
  phy_mapsto (phy<=log v) a h -> log_mapsto v a h
| log_of_ptr_mapsto : forall t (v : (:* t).-log) a h,
  phy_mapsto (phy<=log v) a h -> log_mapsto v a h
| log_of_styp_mapsto : forall t tg H vs a h pad pad_sz,
  align t %| a ->
  Z<=nat (a + size (hp.dom h)) + Z<=nat pad_sz < 2 ^^ ptr_len ->
  logs_mapsto (get_fields g tg) vs a h ->
  pad_sz = padd (a + size (hp.dom h)) (align t) ->
  hp.dom pad = iota (a + size (hp.dom h)) pad_sz ->
  log_mapsto (log_of_styp t tg H vs) a (h \U pad)
with logs_mapsto {g} :
  forall (l : g.-env), logs l -> nat -> hp.t -> Prop :=
| nil_logs_mapsto : forall a, logs_mapsto nil nil_logs a hp.emp
| cons_logs_mapsto : forall hd tl v vs a pad pad_sz h1 h2,
  pad_sz = padd a (align hd.2) ->
  hp.dom pad = iota a pad_sz ->
  log_mapsto v (a + pad_sz) h1 ->
  logs_mapsto tl vs (a + pad_sz + sizeof hd.2) h2 ->
  logs_mapsto (hd :: tl) (cons_logs hd tl v vs) a
    (pad \U h1 \U h2).

End log_mapsto_def.

Arguments log_mapsto [g] [t] _ _ _.
Arguments log_of_uint_mapsto [g] _ _ _ _.
Arguments log_of_sint_mapsto [g] _ _ _ _.
Arguments log_of_uchar_mapsto [g] _ _ _ _.
Arguments log_of_ulong_mapsto [g] _ _ _ _.
Arguments log_of_ptr_mapsto [g] _ _ _ _ _.
Arguments log_of_styp_mapsto [g] _ _ _ _ _ _ _ _ _ _ _ _ _.
Arguments logs_mapsto [g] _ _ _ _.
Arguments nil_logs_mapsto [g] _.
Arguments cons_logs_mapsto [g] _ _ _ _ _ _ _ _ _ _ _ _ _.

Set Elimination Schemes.

Scheme log_mapsto_ind := Induction for log_mapsto Sort Prop
with logs_mapsto_ind := Induction for logs_mapsto Sort Prop.

Lemma foldl_subn g (t : g.-typ) tg (H : Ctyp.ty _ t = styp tg) a (Hdiv: align t %| a) : forall l
  (Hsubset : {subset l <= get_fields g tg}) a' (Ha': (a' >= a)%nat),
  let f := (fun acc elt => acc + padd acc (align elt.2) + sizeof elt.2)%nat in
  (foldl f a' l - a = foldl f (a' - a) l)%nat.
Proof.
elim=> //=.
move => hd tl Hind Hsubset a' Ha'//=.
have Hsubset': { subset tl <= get_fields g tg}.
  by move=> x Hx; apply Hsubset; rewrite in_cons Hx orbC.
rewrite (Hind Hsubset') {Hind}; last first.
  apply leq_trans with a' => //.
  by rewrite -addnA leq_addr.
congr foldl.
nat_norm.
rewrite addnC -addnBA //= addnC; nat_congr.
rewrite addnC (addnC _ (sizeof _)); nat_congr.
rewrite padd_sub //=.
have Hdiv': align hd.2 %| align t.
  by apply (align_styp_div _ tg H); apply/mapP; exists hd => //=; apply Hsubset; rewrite in_cons eqxx.
by apply: dvdn_trans _ Hdiv.
Qed.

Lemma log_mapsto_heap_dom_styp {g} (t : Ctyp.t g) tg H (a : nat) (vs : logs (get_fields g tg)) (lv : log t) :
  lv = log_of_styp t tg H vs ->
  align t %| a ->
    forall h_vs,
      logs_mapsto (get_fields g tg) vs a h_vs ->
      hp.dom h_vs =
      iota a
      (foldl (fun acc hd => acc + padd acc (align hd.2) + sizeof hd.2)%nat a
        (get_fields g tg) - a) ->
      forall (padding : nat) (h_padd : hp.t),
        h_vs # h_padd ->
        padding = padd (a + size (hp.dom h_vs)) (align t) ->
        hp.dom h_padd = iota (a + size (hp.dom h_vs)) padding ->
        Z_of_nat (a + size (hp.dom h_vs)) + Z_of_nat padding < 2 ^^ ptr_len ->
        hp.dom (h_vs \U h_padd) = iota a (sizeof t).
Proof.
move=> Hlv Halign h_vs Hmapstos Hind padding h_padd Hdisj Hapadding Hdom Hoverflow.
rewrite hp.dom_union.
+ rewrite Hdom Hind size_iota -iotaD.
  congr iota.
  rewrite (sizeof_foldl g t tg) //=.
  rewrite foldl_map.
  rewrite Hind in Hapadding.
  rewrite size_iota in Hapadding.
  rewrite Hapadding.
  rewrite padd_add //=.
  set Q := foldl _ _ _.
  set Q' := foldl _ _ _.
  suff: ((Q - a) = Q')%nat by move => ->.
  rewrite /Q.
  move: (inc_refl (get_fields g tg)); move /incP' => Hsubset'.
  rewrite (foldl_subn g t tg _ a Halign (get_fields g tg) Hsubset' a (leqnn _)) //.
  by rewrite subnn.
+ move=> i j.
  rewrite Hind mem_iota; case/andP => _ Hi.
  rewrite Hdom mem_iota Hind size_iota; case/andP => Hj _.
  by apply (leq_trans Hi).
Qed.

Lemma log_mapstos_heap_dom_nil {g} a (h : hp.t) :
   h = hp.emp ->
   hp.dom h = iota a
     (foldl
        (fun (acc : nat) (hd : string * g.-typ) =>
         (acc + padd acc (align hd.2) + sizeof hd.2)%nat) a nil - a).
Proof. move=> /= ->. by rewrite subnn hp.dom_emp. Qed.

Lemma log_mapstos_inv_heap_dom_cons {g} : forall (hd : string * g.-typ) (tl : g.-env)
     (vhd : log hd.2) (vtl : logs tl) a
     (h_padd : hp.t) (padding : nat) (h_hd h_tl : hp.t),
   h_hd # h_padd ->
   h_tl # h_padd ->
   h_hd # h_tl ->
   padding = padd a (align hd.2) ->
   hp.dom h_padd = iota a padding ->
   log_mapsto vhd (a + padding) h_hd ->
   hp.dom h_hd = iota (a + padding) (sizeof hd.2) ->
   logs_mapsto tl vtl (a + padding + sizeof hd.2) h_tl ->
   hp.dom h_tl =
   iota (a + padding + sizeof hd.2)
     (foldl
        (fun (acc : nat) (hd0 : string * g.-typ) =>
         (acc + padd acc (align hd0.2) + sizeof hd0.2)%nat)
        (a + padding + sizeof hd.2)%nat tl - (a + padding + sizeof hd.2)) ->
   hp.dom ((h_padd \U h_hd) \U h_tl) =
   iota a
     (foldl
        (fun (acc : nat) (hd0 : string * g.-typ) =>
         (acc + padd acc (align hd0.2) + sizeof hd0.2)%nat) a
        (cons hd tl) - a).
Proof.
move => hd tl vhd vtl addr h_padd padding h_hd h_tl Hdisj1 Hdisj2 Hdisj3 Hpadding Hpadd Hmapsto' Hhd Hmapstos Htl.
have Htmp : hp.dom (h_padd \U h_hd) = hp.dom h_padd ++ hp.dom h_hd.
  rewrite hp.dom_union // => i j.
  rewrite Hpadd mem_iota; case/andP => _ Hi.
  rewrite Hhd mem_iota; case/andP => Hj _.
  by apply (leq_trans Hi).
rewrite hp.dom_union; last first.
  move=> i j.
  rewrite Htmp Hpadd Hhd -iotaD mem_iota addnA; case/andP => _ Hi.
  rewrite Htl mem_iota; case/andP => Hj _.
  by apply (leq_trans Hi).
rewrite Htmp Hpadd Hhd -iotaD Htl -addnA -iotaD /=.
congr iota.
rewrite Hpadding addnA.
set Q := foldl _ _ _.
set A := padd _ _.
set B := sizeof _.
rewrite addnBA.
- rewrite -(addnA addr _ _) (addnC A _) (addnC addr _).
  rewrite -(addnA B A addr) -(addnA B A Q).
  by rewrite subnDl subnDl.
- apply foldl_leq_monotonic => acc x.
  nat_norm; apply leq_addr.
Qed.

Lemma log_mapsto_inv_heap_dom {g} : forall {t : g.-typ} (lv : log t) a h,
  log_mapsto lv a h -> hp.dom h = iota a (sizeof t).
Proof.
apply log_mapsto_ind with (P0 := fun l lvs addr h H =>
  hp.dom h = iota addr
  (foldl (fun acc (hd: (string * g.-typ)) =>
    (acc + (padd acc (align hd.2)) + (sizeof hd.2))%nat
  ) addr%nat l - addr) ) => //.
- move=> a h v; by inversion 1; subst.
- move=> a h v; by inversion 1; subst.
- move=> a h v; by inversion 1; subst.
- move=> a h v; by inversion 1; subst.
- move=> a h v; by inversion 1; subst.
- intros.
  apply log_mapsto_heap_dom_styp with tg H vs (log_of_styp t tg H vs) pad_sz => //.
  by rewrite hp.disjE H0 e0 dis_iota // H0 size_iota.
- move=> aa /=.
  by rewrite subnn /= hp.dom_emp.
- intros.
  eapply log_mapstos_inv_heap_dom_cons; eauto.
  by rewrite hp.disjE H e0 dis_sym dis_iota.
  by rewrite hp.disjE H0 e0 dis_sym -addnA dis_iota // leq_add2l leq_addr.
  by rewrite hp.disjE H H0 dis_iota.
Qed.

Lemma log_mapstos_inv_heap_dom {g} : forall l (lv: @logs g l) a h,
  logs_mapsto l lv a h -> hp.dom h =
  iota a
  (foldl
     (fun acc (hd: string * g.-typ) => (acc + (padd acc (align hd.2)) + (sizeof hd.2))%nat)
     a%nat
     l
   - a).
Proof.
apply logs_mapsto_ind with (P := fun (t : g.-typ) (lv : log t) a (h : hp.t) H =>
  hp.dom h = iota a (sizeof t)) => //.
- move=> a h v; by inversion 1; subst.
- move=> a h v; by inversion 1; subst.
- move=> a h v; by inversion 1; subst.
- move=> a h v; by inversion 1; subst.
- move=> a h v; by inversion 1; subst.
- intros.
  apply log_mapsto_heap_dom_styp with tg H vs (log_of_styp t tg H vs) pad_sz => //.
  by rewrite hp.disjE H0 e0 dis_iota // H0 size_iota.
- intros.
  by rewrite /= subnn hp.dom_emp.
- intros.
  eapply log_mapstos_inv_heap_dom_cons; eauto.
  by rewrite hp.disjE H e0 dis_sym dis_iota.
  by rewrite hp.disjE H0 e0 dis_sym -addnA dis_iota // leq_add2l leq_addr.
  by rewrite hp.disjE H H0 dis_iota.
Qed.

Lemma log_mapsto_inv_fit {g} : forall (t : g.-typ) (vhd : log t) a (h : hp.t),
  log_mapsto vhd a h -> Z_of_nat a + Z_of_nat (sizeof t) < 2 ^^ ptr_len.
Proof.
apply (@log_mapsto_ind g
  _
  (fun (l : g.-env) (lvs : logs l) (a : nat) (h : hp.t) (H : logs_mapsto l lvs a h) =>
    forall t, t \in unzip2 l ->
      Z_of_nat a + Z_of_nat (sizeof t) < 2 ^^ ptr_len
  )) => //.
- move=> a h v; by inversion 1.
- move=> a h v; by inversion 1.
- move=> a h v; by inversion 1.
- move=> a h v; by inversion 1.
- move=> a h v; by inversion 1.
- move=> ty tg ty_tg vs a h h_padd padding Halign Hfit Hlog_mapstos IH Hpaddin Hh_padd.
  apply: (leZ_ltZ_trans _ Hfit).
  rewrite inj_plus -addZA; apply leZ_add2l.
  rewrite -inj_plus; apply inj_le.
  rewrite (sizeof_foldl g ty tg _) //=.
  rewrite foldl_map.
  rewrite Hpaddin.
  apply log_mapstos_inv_heap_dom in Hlog_mapstos; rewrite Hlog_mapstos.
  rewrite size_iota /=.
  rewrite (foldl_subn g _ tg _ a Halign) //.
  rewrite subnn.
  apply/leP.
  by rewrite leq_add2l padd_add.
- move=> a hd tl vhd vtl h_padd padding h_hd h_tl Hpadding Hh_padd Hlog_mapsto Hfit Hlog_mapstos Halign' t.
  rewrite [_ \in _]/= in_cons.
  case/orP => [ /eqP ? | Ht].
  + subst t.
    apply: (leZ_ltZ_trans _ Hfit).
    rewrite inj_plus -addZA leZ_add2l.
    apply leZ_addl; by [apply Zle_0_nat | apply leZZ].
  + apply Halign' in Ht.
    apply: (leZ_ltZ_trans _ Ht).
    rewrite 2!inj_plus -!addZA leZ_add2l addZA.
    apply leZ_addl.
    rewrite -inj_plus; exact: Zle_0_nat.
    exact: leZZ.
Qed.

Lemma log_mapsto_inv_align {g} : forall (t : g.-typ) (vhd : log t) a (h : hp.t),
  log_mapsto vhd a h -> align t %| a.
Proof.
apply (@log_mapsto_ind g
  _
  (fun (l : g.-env) (lvs : logs l) a (h : hp.t) (H : logs_mapsto l lvs a h) =>
    forall t, t \in unzip2 l -> align t %| a + padd a (align t)
  )) => //.
- move=> a h v; by inversion 1.
- move=> a h v; by inversion 1.
- move=> a h v; by inversion 1.
- move=> a h v; by inversion 1.
- move=> a hd tl vhd vtl h_padd padding h_hd h_tl Hpadding Hh_padd Hlog_mapsto Halign Hlog_mapstos Halign'.
  move=> t.
  rewrite /= in_cons.
  case/orP => [/eqP ? | Ht].
  + congruence.
  + by apply padd_isdiv, align_gt0.
Qed.

Lemma log_mapsto_eq {g} {t : g.-typ} {lv lv' : log t} {a a' h h'}:
  log_mapsto lv a h -> lv = lv' -> a = a' -> h = h' -> log_mapsto lv' a' h'.
Proof. by move => H <- <- <-. Qed.

Lemma log_mapsto_heap_get_ex {g} {t : g.-typ} (lv : t.-log) a h :
  log_mapsto lv a h -> exists pv, heap_get t a h = Some pv.
Proof.
move => H.
move: (log_mapsto_inv_heap_dom lv a h H) => Hdom.
move: (hp.size_cdom_dom h) => Hcdom.
rewrite Hdom in Hcdom.
rewrite size_iota in Hcdom.
exists (mkPhy t (hp.cdom h) Hcdom).
rewrite /heap_get.
case: option_dec => //= [ [l Hl] | ].
- congr Some.
  apply mkPhy_irrelevance => /=.
  rewrite /heap_get' Hdom inc_refl -Hdom hp.proj_itself in Hl.
  by case: Hl.
- by rewrite /heap_get' Hdom inc_refl -Hdom hp.proj_itself.
Qed.

(** Relation between physical and logical values *)

Definition is_styp_or_atyp {g} (t : g.-typ) :=
  match t with
  | Ctyp.mk (styp _) _ => true
  | Ctyp.mk (atyp _ _ _) _ => true
  | _ => false
  end.

Definition phylog_conv {g} {t : g.-typ} (pv : t.-phy) (lv : t.-log) :=
  (~~ is_styp_or_atyp t) && (pv == phy<=log lv).

Notation "pv '|x|' lv" := (phylog_conv pv lv) (at level 50) : C_value_scope.

Lemma log_mapsto_heap_get_conv {g} (t : g.-typ) (lv : t.-log) (a : nat) (h : hp.t) :
  log_mapsto lv a h ->
    forall pv, pv |x| lv ->
      heap_get t a h = Some (pv : t.-phy).
Proof.
move=> H.
apply log_mapsto_ind with
(P := fun t lv a h H => forall pv : t.-phy, pv |x| lv -> heap_get t a h = Some pv)
(P0 := fun sigma lvs a h (H : logs_mapsto sigma lvs a h) => True) => //; clear.
- move=> lv a h.
  move V : (phy<=log _) => v H; move: H V.
  move=> [a' pv' h' Hcdom Hdom Hfit Halign] V pv pv_lv'.
  rewrite /heap_get.
  case: Init_ext.option_dec => [[s Hs]|].
    congr Some.
    apply mkPhy_irrelevance => /=.
    move: Hs.
    rewrite /heap_get' [sizeof]lock.
    case: ifP => // Hs [] <-.
    rewrite -lock -Hdom hp.proj_itself Hcdom -V.
    by case/andP: pv_lv' => _ /eqP <-.
  rewrite /heap_get'.
  case: ifP => //.
  by rewrite Hdom inc_refl.
- move=> lv a h.
  move V : (phy<=log _) => v H; move: H V.
  move=> [a' pv' h' Hcdom Hdom Hfit Halign] V pv pv_lv'.
  rewrite /heap_get.
  case: Init_ext.option_dec => [[s Hs]|].
    congr Some.
    apply mkPhy_irrelevance => /=.
    move: Hs.
    rewrite /heap_get' [sizeof]lock.
    case: ifP => // Hs [] <-.
    rewrite -lock -Hdom hp.proj_itself Hcdom.
    case/andP: pv_lv' => _ /eqP ->; congruence.
  rewrite /heap_get'.
  case: ifP => //.
  by rewrite Hdom inc_refl.
- move=> lv a h.
  move V : (phy<=log _) => v H; move: H V.
  move=> [a' pv' h' Hcdom Hdom Hfit Halign] V pv pv_lv'.
  rewrite /heap_get.
  case: Init_ext.option_dec => [[s Hs]|].
    congr Some.
    apply mkPhy_irrelevance => /=.
    move: Hs.
    rewrite /heap_get' [sizeof]lock.
    case: ifP => // Hs [] <-.
    rewrite -lock -Hdom hp.proj_itself Hcdom.
    case/andP: pv_lv' => _ /eqP ->; congruence.
  rewrite /heap_get'.
  case: ifP => //.
  by rewrite Hdom inc_refl.
- move=> lv a h.
  move V : (phy<=log _) => v H; move: H V.
  move=> [a' pv' h' Hcdom Hdom Hfit Halign] V pv pv_lv'.
  rewrite /heap_get.
  case: Init_ext.option_dec => [[s Hs]|].
    congr Some.
    apply mkPhy_irrelevance => /=.
    move: Hs.
    rewrite /heap_get' [sizeof]lock.
    case: ifP => // Hs [] <-.
    rewrite -lock -Hdom hp.proj_itself Hcdom.
    case/andP: pv_lv' => _ /eqP ->; congruence.
  rewrite /heap_get'.
  case: ifP => //.
  by rewrite Hdom inc_refl.
- move=> t lv a h.
  move V : (phy<=log _) => v H; move: H V.
  move=> [a' pv' h' Hcdom Hdom Hfit Halign] V pv pv_lv'.
  rewrite /heap_get.
  case: Init_ext.option_dec => [[s Hs]|].
    congr Some.
    apply mkPhy_irrelevance => /=.
    move: Hs.
    rewrite /heap_get' [sizeof]lock.
    case: ifP => // Hs [] <-.
    rewrite -lock -Hdom hp.proj_itself Hcdom.
    case/andP: pv_lv' => _ /eqP ->; congruence.
  rewrite /heap_get'.
  case: ifP => //.
  by rewrite Hdom inc_refl.
- move=> t tg tgt lvs a h pad pad_sz t_a a_pad_sz Hlogs_mapsto _ pad_sz_a dom_pad pv pv_lv.
  suff : False by done.
  case/andP: pv_lv.
  destruct t as [t Ht] => /=.
  rewrite /= in tgt.
  by subst t.
Qed.

Lemma phylog_mapsto_conv : forall {g} (t : g.-typ) (pv : t.-phy) (lv : t.-log),
  pv |x| lv ->
  forall h a, phy_mapsto pv a h <-> log_mapsto lv a h.
Proof.
move=> g0 t pv lv H h a; split.
- destruct 1.
  destruct lv => //.
  + subst t.
    apply log_of_uint_mapsto.
    econstructor; eauto.
    case/andP: H => _ /eqP; congruence.
  + subst t.
    apply log_of_sint_mapsto.
    econstructor; eauto.
    case/andP: H => _ /eqP; congruence.
  + subst t.
    apply log_of_uchar_mapsto.
    econstructor; eauto.
    case/andP: H => _ /eqP; congruence.
  + subst t.
    apply log_of_ulong_mapsto.
    econstructor; eauto.
    case/andP: H => _ /eqP; congruence.
  + subst t.
    apply log_of_ptr_mapsto.
    econstructor; eauto.
    case/andP: H => _ /eqP; congruence.
  + suff : False by done.
    case/andP: H.
    destruct t as [t Ht] => /=.
    rewrite /= in e.
    by subst t.
  + suff : False by done.
    case/andP: H.
    destruct t as [t Ht] => /=.
    clear a0.
    rewrite /= in H4.
    by subst t.
- destruct 1.
  + move: H0.
    move V : (phy<=log v) => lv X; move: X V.
    case => {}a {}lv {}h H1 H2 H3 H4 H5.
    constructor => //.
    case/andP: H => _ /eqP ->.
    congruence.
  + move: H0.
    move V : (phy<=log v) => lv X; move: X V.
    case => {}a {}lv {}h H1 H2 H3 H4 H5.
    constructor => //.
    case/andP: H => _ /eqP ->.
    congruence.
  + move: H0.
    move V : (phy<=log v) => lv X; move: X V.
    case => {}a {}lv {}h H1 H2 H3 H4 H5.
    constructor => //.
    case/andP: H => _ /eqP ->.
    congruence.
  + move: H0.
    move V : (phy<=log v) => lv X; move: X V.
    case => {}a {}lv {}h H1 H2 H3 H4 H5.
    constructor => //.
    case/andP: H => _ /eqP ->.
    congruence.
  + move: H0.
    move V : (phy<=log v) => lv X; move: X V.
    case => {}a {}lv {}h H1 H2 H3 H4 H5.
    constructor => //.
    case/andP: H => _ /eqP ->.
    congruence.
  + case/andP: H => H _.
    destruct t as [t Ht].
    rewrite /= in H0.
    by subst t.
Qed.

Local Close Scope Z_scope.

(** Pointer arithmetic *)

Lemma Hshift_pointer {g} (t : g.-typ) (v : (:* t).-phy) (t' : g.-typ) (shift : nat) :
  size (i8<=ptr (ptr<=phy v `+ `( Z<=nat shift )_ptr_len)) = sizeof (:* t').
Proof. by rewrite /i8_of_ptr size_int_break sizeof_ptyp. Qed.

Definition shift_pointer {g} (t : g.-typ) (v : (:* t).-phy) (t' : g.-typ) (shift : nat) :
  (:* t').-phy :=
  mkPhy _ (i8<=ptr ((ptr<=phy v) `+ Z2u _ (Z_of_nat shift))) (Hshift_pointer _ v t' shift).

Local Open Scope machine_int_scope.
Require Import ZArith_ext.
Local Open Scope zarith_ext_scope.

Lemma value_phy_shift_pointer {g} {t : g.-typ} : forall (pv : (:* t).-phy) (t' : g.-typ) shift,
  u2Z (ptr<=phy pv) + Z<=nat shift < 2 ^^ ptr_len ->
  (nat<=u (ptr<=phy pv) + shift)%nat =
  nat<=u (ptr<=phy (shift_pointer t pv t' shift)).
Proof.
move=> [l e] ty' shift Hshift.
rewrite /shift_pointer.
set Hx := Hshift_pointer _ _ _ _.
set x := ptr<=phy (mkPhy _ (i8_of_ptr _) _).
have -> : x = ptr<=phy (mkPhy (:* t) l e) `+ Z2u ptr_len (Z_of_nat shift).
  by rewrite /x {1}/ptr_of_phy /= i8_of_ptrKo.
have Htmp : u2Z (Z2u ptr_len (Z_of_nat shift)) = Z_of_nat shift.
  rewrite Z2uK //.
  set tmp := ptr<=phy _ in Hshift.
  move: (min_u2Z tmp) => ?; lia.
rewrite {2}/u2nat u2Z_add; last by rewrite Htmp.
rewrite Zabs_nat_Zplus; last 2 first.
  by apply min_u2Z.
  by apply min_u2Z.
by rewrite Htmp Zabs2Nat.id.
Qed.

Lemma heap_upd_styp {g} (t : g.-typ) tg (H : Ctyp.ty _ t = styp tg) a
  (pv : t.-phy) h hpadd padding (vs : logs (get_fields g tg)) :
  align t %| a ->
  logs_mapsto (get_fields g tg) vs a h ->
  h # hpadd ->
  padding = padd (a + size (hp.dom h)) (align t) ->
  hp.dom hpadd = iota (a + size (hp.dom h)) padding ->
  heap_upd t a pv (h \U hpadd) =
    (bytes2heap a pv \D\ hp.dom hpadd) \U (bytes2heap a pv |P| hp.dom hpadd).
Proof.
move=> Halign vs_h h_hpadd Hpadding dom_hpadd.
rewrite /heap_upd.
destruct pv as [pv Hpv] => /=.
move/log_mapstos_inv_heap_dom : (vs_h) => dom_h.
rewrite (foldl_subn g t tg H) // subnn in dom_h.
have dom_h_hpadd : hp.dom (h \U hpadd) = hp.dom h ++ hp.dom hpadd.
  rewrite hp.dom_union //.
  move=> i j.
  rewrite dom_h mem_iota; case/andP=> _ Hi.
  rewrite dom_hpadd mem_iota; case/andP=> Hj _.
  apply (leq_trans Hi); by rewrite dom_h size_iota in Hj.
have -> : inc (iota a (size pv)) (hp.dom (h \U hpadd)).
  rewrite dom_h_hpadd dom_hpadd dom_h size_iota -iotaD.
  set x := (_ + _)%nat.
  suff : size pv = x by move=> ->; rewrite inc_refl.
  rewrite Hpv (sizeof_foldl g t tg H) /= !foldl_map /= /x.
  by rewrite Hpadding dom_h size_iota padd_add.
have -> : (h \U hpadd) \D\ iota a (size pv) = hp.emp.
  suff : hp.dom (h \U hpadd) = iota a (size pv).
    move=> <-; by rewrite hp.difs_self.
  rewrite dom_h_hpadd dom_hpadd dom_h size_iota -iotaD Hpv.
  rewrite (sizeof_foldl g t tg H) /= !foldl_map.
  by rewrite Hpadding dom_h size_iota padd_add.
rewrite hp.unioneh hp.unionC; last first.
  by apply hp.disj_sym, hp_prop_m.proj_difs_disj_spec.
by rewrite -hp.proj_difs.
Qed.

(* series of lemmas about list and logs and log_mapsto *)

Fixpoint app_logs {g} (l1 l2 : g.-env) (lvs1 : logs l1) (lvs2 : logs l2) : logs (l1 ++ l2) :=
  match lvs1 with
    | nil_logs => lvs2
    | cons_logs hd tl lvs lvss => cons_logs hd (tl ++ l2) lvs (app_logs tl l2 lvss lvs2)
  end.

Arguments app_logs [g l1 l2] _ _.

Require Import JMeq.

Program Definition lvals_nil {g} (lvs : @logs g nil) : lvs = nil_logs :=
  match lvs with
    | nil_logs => Logic.eq_refl _
    | cons_logs _ _ _ _ => False_rect _ _
  end.
Next Obligation.
by rewrite (JMeq_eq Heq_lvs).
Qed.

Lemma app_nil_logs {g} l lvs1 lvs2 : @app_logs g nil l lvs1 lvs2 = lvs2.
Proof. by rewrite (lvals_nil lvs1). Qed.

Program Definition lvals_cons {g} hd tl (lvs : @logs g (hd :: tl)) :
  exists vhd vtl, lvs = cons_logs hd tl vhd vtl :=
  match lvs with
    | nil_logs => False_rect _ _
    | cons_logs hd tl vhd vtl => _
  end.
Next Obligation.
by exists vhd; exists vtl; rewrite (JMeq_eq Heq_lvs).
Qed.

Lemma cons_logs_inj {g} tl hd vhd vhd' vtl vtl' :
  @cons_logs g hd tl vhd vtl = cons_logs hd tl vhd' vtl' ->
  vhd = vhd' /\ vtl = vtl'.
Proof.
case => Heq1 Heq2.
apply Eqdep.EqdepTheory.inj_pair2 in Heq1.
by apply Eqdep.EqdepTheory.inj_pair2 in Heq2.
Qed.

Lemma log_vals_decomp {g} : forall (l1 : g.-env) l2 (lvals : logs (l1 ++ l2)),
  exists lvals1 lvals2, lvals = app_logs lvals1 lvals2.
Proof.
elim => //=.
- move => l2 lvals; exists nil_logs; exists lvals; done.
- move => hd tl Hind l2 lvals.
  move: (lvals_cons _ _ lvals) => [] vhd [] vtl Hlvals.
  move: {Hind}(Hind _ vtl) => [] lvals1 [] lvals2 Hvtl.
  exists (cons_logs _ _ vhd lvals1); exists lvals2.
  by rewrite Hlvals Hvtl.
Qed.

Module map_tac_m := finmap.Map_Tac hp.

Lemma app_logs_mapstos {g}:
  forall (l1 l2 : g.-env) (lvs1 : logs l1) (lvs2 : logs l2) a h,
  logs_mapsto (l1 ++ l2) (app_logs lvs1 lvs2) a h ->
  l2 <> nil ->
  exists h1 h2,
    h1 # h2 /\
    h = h1 \U h2 /\
    logs_mapsto l1 lvs1 a h1 /\
    logs_mapsto l2 lvs2 (foldl (fun acc hd => acc + padd acc (align hd.2) + sizeof hd.2)%nat a l1) h2.
Proof.
elim => //=.
- move => l2 lvs1 lvs2 addr h Hlog_mapstos Hl2.
  exists hp.emp; exists h => //=.
  split; first by map_tac_m.Disj.
  split; first by map_tac_m.Equal.
  split => //=.
  - by rewrite (lvals_nil lvs1); apply nil_logs_mapsto.
  - by rewrite (lvals_nil lvs1) in Hlog_mapstos.
- move => hd tl Hind l2 lvs1 lvs2 addr h Hlogmapstos Hl2.
  inversion Hlogmapstos; subst; clear Hlogmapstos.
  apply Eqdep.EqdepTheory.inj_pair2 in H1.
  move: (lvals_cons _ _ lvs1) => [] vhd' [] vtl' Hlvs1.
  subst lvs1.
  simpl in H1.
  case: H1.
  case => Heq1 Heq2.
  apply Eqdep.EqdepTheory.inj_pair2 in Heq1.
  apply Eqdep.EqdepTheory.inj_pair2 in Heq2.
  subst vhd'; subst vs.
  move: {Hind}(Hind _ _ _ _ _ H7 Hl2) => [] h1' [] h2' [] Hdisj [] Hheq [] Hlogmapstos1 Hlogmapstos2.
  exists (pad \U h1 \U h1'); exists h2'.
  split.
    apply hp.disjUh => //.
    apply hp.disjUh.
      apply log_mapstos_inv_heap_dom in Hlogmapstos2.
      rewrite hp.disjE Hlogmapstos2 H3 dis_iota //.
      eapply leq_trans; last first.
        apply foldl_leq_monotonic => *.
        by rewrite -addnA leq_addr.
      by rewrite leq_addr.
    apply log_mapsto_inv_heap_dom in H4.
    apply log_mapstos_inv_heap_dom in Hlogmapstos2.
    rewrite hp.disjE H4 Hlogmapstos2 dis_iota //.
    eapply leq_trans; last first.
        apply foldl_leq_monotonic => *.
        by rewrite -addnA leq_addr.
      by rewrite leqnn.
  split; first by map_tac_m.Equal.
  split => //.
  by apply cons_logs_mapsto with (pad_sz := padd addr (align hd.2)).
Qed.

Lemma mapstos_app_logs {g} : forall (l1 l2 : g.-env) (lvs1 : logs l1) (lvs2 : logs l2) a h,
  l2 <> nil ->
  forall h1 h2,
    h1 # h2 ->
    h = h1 \U h2 ->
    logs_mapsto l1 lvs1 a h1 ->
    logs_mapsto l2 lvs2 (foldl (fun acc hd => acc + padd acc (align hd.2) + sizeof hd.2)%nat a l1) h2 -> logs_mapsto (l1 ++ l2) (app_logs lvs1 lvs2) a h.
Proof.
elim => //=.
- move => l2 lvs1 lvs2 addr h Hl2 h1 h2 Hdisj Heq Hlog_mapstos1 Hlogmapstos2.
  inversion Hlog_mapstos1; subst.
  by rewrite hp.unioneh (lvals_nil lvs1).
- move => hd tl Hind l2 lvs1 lvs2 addr h Hl2 h1 h2 Hdisj Heq Hlog_mapstos1 Hlog_mapstos2.
  move: (lvals_cons _ _ lvs1) => [] vhd [] vtl Hlvs1.
  subst lvs1.
  inversion Hlog_mapstos1.
  subst.
  apply (Eqdep.EqdepTheory.inj_pair2) in H1; subst v.
 apply (Eqdep.EqdepTheory.inj_pair2) in H2; subst vs.
  have -> : ((pad \U h0) \U h3) \U h2 = pad \U h0 \U (h3 \U h2) by map_tac_m.Equal.
  eapply cons_logs_mapsto; try (map_tac_m.Equal || map_tac_m.Disj).
  - by apply Logic.eq_refl.
  - assumption.
  - assumption.
  - apply (Hind _ _ _ _ _ Hl2 h3 h2); try (map_tac_m.Equal || map_tac_m.Disj) => //=.
    + assumption.
    + assumption.
Qed.

Lemma log_mapstos_mapsto {g} :
  forall l a n (t : g.-typ) (lvs : logs l) (Hin : (n, t) \in l) h,
    logs_mapsto l lvs a h ->
    exists h1 h2,
      h1 # h2 /\
      h = h1 \U h2 /\
      let new_addr := (a + padd a (align (head (n, t) l).2))%nat in
      log_mapsto (values_get n t l lvs Hin) (field_address new_addr n t l (Hin)) h1.
Proof.
elim => // hd tl Hind addr n ty vals Hin h Hmapsto.
inversion Hmapsto => //; subst.
apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
rewrite /=.
destruct (eq_comparable (n, ty) hd).
- subst.
  exists h1, (pad \U h2).
  split.
    apply hp.disjhU.
      apply log_mapsto_inv_heap_dom in H4.
      by rewrite hp.disjE H4 H3 dis_sym dis_iota.
    apply log_mapsto_inv_heap_dom in H4.
    apply log_mapstos_inv_heap_dom in H7.
    by rewrite hp.disjE H4 H7 dis_iota.
  split.
    rewrite hp.unionA (hp.unionC pad) //.
    apply log_mapsto_inv_heap_dom in H4.
    by rewrite hp.disjE H4 H3 dis_iota.
  by rewrite /= string_decxx eq_comparable_eq /= eq_comparable_eq.
- have Hintl : (n, ty) \in tl by rewrite inE in Hin; move/orP: Hin => [] //=; move/eqP.
  move: {Hind}(Hind _ _ _ _ Hintl _ H7) => [] h1' [] h2' [] Hdisj [] Heq Hmapsto'.
  exists h1', (h2' \U pad \U h1).
  have Htmp : h1' # pad.
    apply log_mapsto_inv_heap_dom in Hmapsto'.
    rewrite hp.disjE Hmapsto' H3 dis_sym dis_iota //.
    eapply leq_trans; last by apply field_address_ge.
    by rewrite -addnA leq_addr.
  have Htmp' : h1' # h1.
    apply log_mapsto_inv_heap_dom in H4.
    apply log_mapsto_inv_heap_dom in Hmapsto'.
    rewrite hp.disjE Hmapsto' H4 dis_sym dis_iota //.
    eapply leq_trans; last by apply field_address_ge.
    by rewrite leq_addr.
  split.
    apply hp.disjhU => //.
    by apply hp.disjhU.
  split.
    clear Hmapsto'.
    rewrite 2!hp.unionA -Heq hp.unionC; last first.
      apply hp.disjUh.
        apply log_mapstos_inv_heap_dom in H7.
        by rewrite hp.disjE H3 H7 dis_iota // leq_addr.
      apply log_mapstos_inv_heap_dom in H7.
      apply log_mapsto_inv_heap_dom in H4.
      by rewrite hp.disjE H7 H4 dis_iota.
    by rewrite hp.unionA.
  destruct hd as [hd1 hd2].
  rewrite /=.
  case: (eq_comparable (n, ty) (hd1, hd2)) => Hcomp //=.
  rewrite /= in Hmapsto'.
  apply (log_mapsto_eq Hmapsto') => //.
  + destruct (string_dec n hd1).
      subst hd1.
      rewrite eq_comparable_neq; first by move=> ?; subst hd2.
      move=> tyhd2.
      congr values_get.
      by apply eq_irrelevance.
    congr values_get.
    by apply eq_irrelevance.
  + rewrite !addnA.
    congr field_address.
    apply eq_irrelevance.
Qed.

Lemma log_mapstos_inv {g} hd (tl : g.-env) lvs a h : logs_mapsto (hd :: tl) lvs a h ->
  align hd.2 %| a + padd a (align hd.2).
Proof.
inversion 1; subst.
apply Eqdep.EqdepTheory.inj_pair2 in H2.
inversion H5; subst.
- destruct hd as [hd1 hd2].
  rewrite /= in H0.
  subst hd2.
  apply Eqdep.EqdepTheory.inj_pair2 in H6; subst v0.
  inversion H9; subst; clear H9.
  by rewrite {1}H1.
- destruct hd as [hd1 hd2].
  rewrite /= in H0.
  subst hd2.
  apply Eqdep.EqdepTheory.inj_pair2 in H6; subst v0.
  inversion H9; subst; clear H9.
  by rewrite {1}H1.
- destruct hd as [hd1 hd2].
  rewrite /= in H0.
  subst hd2.
  apply Eqdep.EqdepTheory.inj_pair2 in H6; subst v0.
  inversion H9; subst; clear H9.
  by rewrite {1}H1.
- destruct hd as [hd1 hd2].
  rewrite /= in H0.
  subst hd2.
  apply Eqdep.EqdepTheory.inj_pair2 in H6; subst v0.
  inversion H9; subst; clear H9.
  by rewrite {1}H1.
- destruct hd as [hd1 hd2].
  rewrite /= in H0.
  subst hd2.
  apply Eqdep.EqdepTheory.inj_pair2 in H6; subst v0.
  inversion H9; subst; clear H9.
  by rewrite {1}H1.
- exact H3.
Qed.

Lemma log_mapstos_inv2 {g} (l : g.-env) lvs a h str ty (H : (str, ty) \in l) :
  logs_mapsto l lvs a h ->
  align (head (str, ty) l).2 %| a + padd a (align (head (str, ty) l).2).
Proof.
destruct l as [|hd tl] => //=.
eapply log_mapstos_inv; eauto.
Qed.

Lemma log_mapsto_log_of_styp_inv {g} (ty : g.-typ) tg H
  (lvs : logs (get_fields g tg)) a h :
  log_mapsto (log_of_styp ty tg H lvs) a h ->
  exists h_vs h_padd,
    h_vs # h_padd /\
    h = h_vs \U h_padd /\
    logs_mapsto (get_fields g tg) lvs a h_vs /\
    let padding := padd (a + size (hp.dom h_vs)) (align ty) in
    hp.dom h_padd = iota (a + size (hp.dom h_vs)) padding /\
    align ty %| a /\
      Z_of_nat (a + size (hp.dom h_vs)) + Z_of_nat padding < 2 ^^ ptr_len.
Proof.
inversion 1 => //; subst.
- done.
- done.
- done.
- done.
- exfalso.
  by destruct t.
- exists h0, pad.
  split.
    apply log_mapstos_inv_heap_dom in H8.
    by rewrite hp.disjE H12 H8 size_iota dis_iota.
  split; first by [].
  have ? : H = H3 by apply eq_irrelevance. subst H3.
  apply Eqdep.EqdepTheory.inj_pair2 in H4; by subst vs0.
Qed.

Definition logs_cons_take_head {g} a (b : g.-env) (x : logs (a :: b)) : log a.2 :=
  match x in logs l return (match l with nil => unit | cons _ _ => _ end) with
    | cons_logs _ _ hd tl => hd
    | nil_logs => tt
  end.

Definition logs_cons_take_tail {g} a (b : g.-env) (x : logs (a :: b)) : logs b :=
match x in logs l return (match l with nil => unit | cons _ _ => _ end) with
  | cons_logs _ _ hd tl => tl
  | nil_logs => tt
end.

(*Program Definition logs_cons_inv'_statement {g} := forall a (b : g.-env) y (x : logs y),
  y = a :: b ->
  x = cons_logs a b (logs_cons_take_head a b x) (logs_cons_take_tail a b x).*)

Program Definition logs_cons_inv'_statement {g} := forall a (b : g.-env) y (x : logs y)
  (H : y = a :: b),
  x = cons_logs a b
    (logs_cons_take_head a b x)
    (logs_cons_take_tail a b x).

Lemma logs_cons_inv' {g} : @logs_cons_inv'_statement g.
Proof.
rewrite /logs_cons_inv'_statement.
move=> a b y x.
destruct x => //.
move=> H.
have [? ?] : hd = a /\ tl = b by case: H.
subst a b.
by rewrite -2!Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

Lemma logs_cons_inv {g} (a : string * g.-typ) b : forall (x : logs (a :: b)),
  x = cons_logs a b (logs_cons_take_head a b x) (logs_cons_take_tail a b x).
Proof.
set y := a :: b.
move=> x.
by rewrite (@logs_cons_inv' g a b y x) -!Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

Program Definition values_set_app_logs_statement :=
  forall g (l1 : g.-env) l2 lvs1 lvs2 n ty val Hin
    (H : ~ (n, ty) \in l1),
    values_set n ty val (l1 ++ l2) (app_logs lvs1 lvs2) Hin =
    app_logs lvs1 (values_set n ty val l2 lvs2 _).
Next Obligation.
rewrite mem_cat in Hin; move/orP: Hin => [] => //=.
Qed.

Lemma values_set_app_logs : values_set_app_logs_statement.
Proof.
rewrite /values_set_app_logs_statement.
move => g.
elim => //=.
- move => l2 lvs1 lvs2 n ty val Hin H.
  rewrite (lvals_nil lvs1) => //=.
  set ob := values_set_app_logs_statement_obligation_1 _ _ _ _ _ _ _.
  by have ->: Hin = ob by apply/eq_irrelevance.
- move => hd tl Hind l2 lvs1 lvs2 n ty val Hin Hnotin.
  set ob := values_set_app_logs_statement_obligation_1 _ _ _ _ _ _ _; move: ob => ob.
  move: (lvals_cons _ _ lvs1) => [] vhd [] vtl Hlvs1.
  subst lvs1.
  simpl app_logs.
  have Hin': (n, ty) \in (tl ++ l2) by rewrite mem_cat; apply/orP; right.
  have Hneq: (n ,ty) <> hd by move => Heq; apply Hnotin; rewrite in_cons; apply/orP; left; apply/eqP.
  destruct hd.
  rewrite (values_set_neq n s ty _ _ _ Hin') => //=.
  have Hin'': ~(n, ty) \in tl by  move => Heq; apply Hnotin; rewrite in_cons; apply/orP; right.
  rewrite (Hind _ _ _ _ _ _ Hin' Hin'').
  congr (cons_logs _ _ _ (app_logs _ (values_set _ _ _ _ _ _))).
  apply eq_irrelevance.
Qed.

Lemma log_mapsto_heap_upd {g} {t : g.-typ} (vhd : log t) a h :
  log_mapsto vhd a h ->
  forall pv (lv : log t),
  pv |x| lv ->
  log_mapsto lv a (heap_upd t a pv h).
Proof.
move=> H pval lval.
move/phylog_mapsto_conv => Hequiv.
move/log_mapsto_inv_heap_dom : (H) => H'.
apply Hequiv.
constructor.
- apply cdom_heap_upd.
  by rewrite H' dom_bytes2heap size_phy2seq.
- by rewrite dom_heap_upd H'.
- by eapply log_mapsto_inv_fit; eauto.
- by eapply log_mapsto_inv_align; eauto.
Qed.

Lemma log_mapstos_heap_upd {g} : forall str (t : g.-typ) (l1 l2 : g.-env)
  (Hnotin : ~ (str, t) \in l1)
  (Hin : (str, t) \in l1 ++ (str, t) :: l2)
  (pv : t.-phy) (lv : log t)
  (Hequiv : pv |x| lv)
  (ty' : g.-typ) tg (ty'_tg : Ctyp.ty _ ty' = styp tg)
  (Hget_fields : get_fields g tg = l1 ++ (str, t) :: l2)
  (vhd : log t)
  (vtl : logs l2) (h4 : hp.t) a
  (Halign : align ty' %| a),
  let f := (fun (acc : nat) (hd : string * g.-typ) =>
        (acc + padd acc (align hd.2) + sizeof hd.2)%nat) in
  logs_mapsto
    ((str, t) :: l2)
    (cons_logs (str, t) l2 vhd vtl)
    (foldl f a l1)
    h4 ->
  logs_mapsto
    ((str, t) :: l2)
    (cons_logs (str, t) l2 lv vtl)
    (foldl f a l1)
    (heap_upd t (a + field_address 0 str t (l1 ++ (str, t) :: l2) Hin) pv h4).
Proof.
move=> str ty l1 l2 Hnotin Hin pv lv Hequiv ty' tg ty_tg Hget_fields vhd vtl h a Halign f H.
inversion H; subst; clear H.
apply Eqdep.EqdepTheory.inj_pair2 in H2; subst v.
apply Eqdep.EqdepTheory.inj_pair2 in H3; subst vs.
have a1a2 : (a + field_address 0 str ty (l1 ++ (str, ty) :: l2) Hin =
   foldl f a l1 + padd (foldl f a l1) (align ty))%nat.
  rewrite -field_address_slide0 //; last first.
    move=> i Hi str_dummy ty_dummy Hdummy.
    eapply dvdn_trans; last by apply Halign.
    rewrite -Hget_fields.
    apply align_get_fields => //; by rewrite Hget_fields.
  rewrite field_address_eq_foldl //=; last first.
    rewrite -nth0.
    eapply dvdn_trans; last by apply Halign.
    rewrite -Hget_fields.
    apply align_get_fields => //.
    by rewrite Hget_fields.
    by rewrite Hget_fields size_cat /= addnS.
  have -> : take (seq.index (str, ty) (l1 ++ (str, ty) :: l2))
         (l1 ++ (str, ty) :: l2) = l1.
    rewrite take_cat index_cat.
    move/negP : Hnotin.
    move/negbTE => ->.
    by rewrite -{2}(addn0 (size l1)) ltn_add2l ltn0 addKn /= eqxx cats0.
  rewrite -/f.
  congr (_ + padd _ _)%nat.
  suff : align
    (nth (str, ty) (l1 ++ (str, ty) :: l2) (seq.index (str, ty) (l1 ++ (str, ty) :: l2))).2 =
    align ty by move=> ->.
  rewrite nth_cat index_cat.
  move/negP/negbTE : Hnotin => ->.
  by rewrite -{2}(addn0 (size l1)) ltn_add2l ltn0 addKn /= eqxx.
rewrite heap_upd_union_L; last 2 first.
  apply hp.disjUh.
    apply log_mapstos_inv_heap_dom in H9.
    by rewrite hp.disjE H9 H5 dis_iota // leq_addr.
  apply log_mapstos_inv_heap_dom in H9.
  apply log_mapsto_inv_heap_dom in H8.
  by rewrite hp.disjE H9 H8 dis_iota.
  rewrite hp.dom_union.
  - (* same as below *) eapply inc_trans; last by apply inc_app_R.
    rewrite a1a2.
    move/log_mapsto_inv_heap_dom : (H8) => -> /=.
    by rewrite inc_refl.
  - move=> i j.
    rewrite H5 mem_iota.
    case/andP=> _ Hi.
    move/log_mapsto_inv_heap_dom : H8 => ->.
    rewrite mem_iota.
    case/andP=> Hj _.
    rewrite /hp.ltl /order.NatOrder.ltA /=.
    by eapply ltn_leq_trans; last by apply Hj.
rewrite heap_upd_union_R; last 2 first.
  apply log_mapsto_inv_heap_dom in H8.
  by rewrite hp.disjE H5 H8 dis_iota.
  rewrite a1a2.
  move/log_mapsto_inv_heap_dom : (H8) => -> /=.
  by rewrite inc_refl.
eapply cons_logs_mapsto.
reflexivity.
exact H5.
2: exact H9.
rewrite a1a2.
by apply log_mapsto_heap_upd with vhd.
Qed.

Lemma values_set_heap_upd {g} {str} {tg} {t t' : g.-typ} {H}
  {Hin : (str, t) \in get_fields g tg} vals a pv lv h :
  pv |x| lv ->
  log_mapsto (log_of_styp t' tg H vals) a h ->
  log_mapsto
  (log_of_styp t' tg H (values_set str _  lv _ vals Hin)) a
  (heap_upd t (a + field_address 0 str t (get_fields g tg) Hin) pv h).
Proof.
move => Hequiv Hlog_mapsto.
move: (log_mapsto_log_of_styp_inv _ _ _ _ _ _ Hlog_mapsto) => [] h1 [] h2 [] Hdisj [] Hheq [] Hlog_mapstos //= [] Hh2_dom [] Halign Hoverflow.
rewrite Hheq.
rewrite heap_upd_union_L => //=; last first.
  apply log_mapstos_inv_heap_dom in Hlog_mapstos.
  rewrite Hlog_mapstos.
  apply/incP/incl_iota.
  by apply/leP; rewrite leq_addr.
  rewrite (foldl_subn g t' tg _) // subnn addKn addnC.
  apply/leP.
  by apply (leq_field_address_foldl _ t' _ (esym H) str t Hin refl_equal).
eapply (log_of_styp_mapsto t' tg _) => //=.
- by rewrite !dom_heap_upd.
- move: {Hlog_mapsto} (memP Hin) => //= [] l1 [] l2 [] H1 H2.
  move: Hin vals Hlog_mapstos.
  rewrite H1 => Hin vals Hlog_mapstos.
  move: (log_vals_decomp _ _ vals) => [] lvs1 [] lvs2 Hvals.
  subst vals.
  have Hnotnil : (str, t) :: l2 <> nil by done.
  move: (app_logs_mapstos _ _ _ _ _ _ Hlog_mapstos Hnotnil) => [] h3 [] h4 [] Hdisj' [] Heq' [] Hlog_mapstos1 Hlog_mapstos2.
  rewrite values_set_app_logs.
  apply (mapstos_app_logs _ _ _ _ _ _ Hnotnil h3 (heap_upd t (a + field_address 0 str t (l1 ++ (str, t) :: l2) Hin) pv h4)) => //=.
  + apply hp.disj_sym; apply disj_heap_upd; by map_tac_m.Disj.
  + rewrite Heq' hp.unionC; last by map_tac_m.Disj.
    rewrite heap_upd_union_L.
    * rewrite hp.unionC; first by done.
      apply disj_heap_upd; by map_tac_m.Disj.
    * by map_tac_m.Disj.
    * apply log_mapstos_inv_heap_dom in Hlog_mapstos2.
      set f1 := foldl _ _ _ in Hlog_mapstos2.
      rewrite -field_address_slide; last first.
        move=> i Hi str_dummy ty_dummy Hin_dummy.
        eapply dvdn_trans; last by apply Halign.
        apply align_styp_div with tg => //.
        apply/mapP.
        exists (nth (str_dummy, ty_dummy) (l1 ++ (str, t) :: l2) i) => //.
        rewrite H1.
        apply/(nthP (str_dummy, ty_dummy)).
        by exists i; eauto.
      rewrite addn0.
      have head_div_addr : align (head (str, t) (l1 ++ (str, t) :: l2)).2 %| a.
        eapply dvdn_trans; last by apply Halign.
        apply align_styp_div with tg => //.
        apply/mapP.
        exists (head (str, t) (l1 ++ (str, t) :: l2)) => //.
        rewrite H1 -nth0.
        apply/(nthP (str, t)).
        exists O => //.
        by rewrite size_cat /= addnS.
      have f1_leq : (f1 <= field_address a str t (l1 ++ (str, t) :: l2) Hin)%nat.
        rewrite /f1 field_address_eq_foldl //=.
        eapply leq_trans; last by apply leq_addr.
        rewrite take_cat index_cat.
        move/negP/negbTE : (H2) => ->.
        set test := (_ < _)%nat.
        have -> : test = false  by rewrite /test -ltn_subRL subnn ltn0.
        rewrite foldl_cat.
        apply foldl_leq_monotonic => acc Hacc.
        by rewrite -addnA leq_addr.
      apply/incP.
      rewrite Hlog_mapstos2.
      apply incl_iota.
      - by apply/leP.
      - apply/leP.
        rewrite addnBA // leq_subLR addnBA; last first.
          apply foldl_leq_monotonic => acc Hacc; by rewrite -addnA leq_addr.
        rewrite addKn addnC /f1 -foldl_cat.
        by apply leq_field_address_foldl with t' tg.
  + set ob := values_set_app_logs_statement_obligation_1 _ _ _ _ _ _ _.
    move: ob => ob.
    move: (lvals_cons _ _ lvs2) => [] vhd [] vtl Hlvs2.
    subst lvs2.
    rewrite values_set_eq.
    by eapply log_mapstos_heap_upd; eauto.
- by rewrite !dom_heap_upd.
Qed.

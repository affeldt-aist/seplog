(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext.

Local Open Scope zarith_ext_scope.

Module Type IntegralType.

Parameter t : eqType.
Parameter of_nat : nat -> t.
Axiom of_nat_inj : forall a b, of_nat a = of_nat b -> a = b.

Parameter add : t -> t -> t.
Axiom addA : forall a b c, add a (add b c) = add (add a b) c.
Axiom addC : forall n m, add n m = add m n.
Axiom add0 : forall a, add a (of_nat 0) = a.
Axiom add1 : forall a, add (of_nat 1) (of_nat a) = of_nat a.+1.

Parameter sub : t -> t -> t.
Parameter mul : t -> t -> t.
Parameter div : t -> t -> t.
Parameter rem : t -> t -> t.
Parameter abs : t -> t.

Parameter ge : t -> t -> Prop.
Parameter gt : t -> t -> Prop.
Parameter geb : t -> t -> bool.
Parameter gtb : t -> t -> bool.
Axiom geP : forall a b : t, geb a b <-> ge a b.
Axiom gtP : forall a b : t, gtb a b <-> gt a b.

Parameter eqb : t -> t -> bool.
Axiom eqP : Equality.axiom eqb.

Axiom ge_refl : forall a, ge a a.
Axiom gebNgt : forall a b, geb b a = (~~ gtb a b).
Axiom gtbE : forall a b, gtb a b = geb a b && (a != b).
Axiom gtW : forall a b, gt a b -> ge a b.
Axiom ge_trans : forall b a c, ge a b -> ge b c -> ge a c.
Axiom gt_add1 : forall n, gt (add (of_nat 1) n) n.

End IntegralType.

Module IntegralType_Prop (X : IntegralType).

Import X.

Lemma gt_trans a b c : gt a b -> gt b c -> gt a c.
Proof.
move=> /gtW a_b /gtP/negPn.
rewrite -gebNgt => c_b.
apply/gtP/negPn.
rewrite -gebNgt.
apply: contra c_b => c_a.
apply/geP/(ge_trans a) => //; exact/geP.
Qed.

Lemma ge_gt_dec a b : ge a b \/ gt b a.
Proof.
move H : (geb a b) => [|]; first by left; exact/geP.
right.
apply/gtP/negPn.
move/negbT : H.
apply contra.
by rewrite -gebNgt.
Qed.

Lemma geb_false a b : ~~ geb a b <-> ~ ge a b.
Proof. split; [by move/negP => H /geP | move=> H; exact/negP/geP]. Qed.

Lemma gtb_false a b : ~~ gtb a b <-> ~ gt a b.
Proof. split; [by move/negP => H /gtP | move=> H; exact/negP/gtP]. Qed.

Definition max (a b : t) := if geb a b then a else b.

Lemma ge_max_r a b : ge (max a b) b.
Proof. rewrite /max. move H : (geb _ _) => []; [exact/geP | exact/ge_refl]. Qed.

Lemma ge_max_l a b : ge (max b a) b.
Proof.
rewrite /max.
move H : (geb _ _) => []; first exact/ge_refl.
move/negbT : H; rewrite gebNgt => /negPn H; exact/gtW/gtP.
Qed.

Lemma maxA a b c : max a (max b c) = max (max a b) c.
Proof.
rewrite /max.
case/boolP : (geb b c) => b_c.
  case/boolP : (geb a b) => a_b //; last by rewrite b_c.
  case/boolP : (geb a c) => //.
  move/geP in b_c. move/geP in a_b.
  by move/geP: (ge_trans _ _ _ a_b b_c) => ->.
move a_c : (geb a c) => [|].
  move a_b : (geb a b) => [|]; first by rewrite a_c.
  move: b_c; rewrite gebNgt => /negPn c_b.
  move: a_b; rewrite gebNgt => /negPn b_a.
  have a_c2 : gtb c a.
    apply/gtP/(gt_trans _ b) => //; exact/gtP.
  by rewrite gebNgt a_c2 in a_c.
move a_b : (geb a b) => [|]; [by rewrite a_c | by rewrite (negbTE b_c)].
Qed.

Definition max_list l def := List.fold_left max l def.

Lemma ge_max_list_max : forall tl def x, ge (max_list tl (max def x)) x.
Proof.
elim => [def x /= | hd tl IH def x /=].
exact: ge_max_r.
case: (ge_gt_dec hd x) => X; first exact: (ge_trans hd).
rewrite -maxA.
apply (ge_trans (max x hd)) => //; exact/ge_max_l.
Qed.

Lemma my_max_list_prop : forall l def x, List.In x l -> ge (max_list l def) x.
Proof.
elim=> // hd tl IH def x /= [-> | H]; by [apply ge_max_list_max | apply IH].
Qed.

Lemma my_max_list_disj l : disj (add (of_nat 1) (max_list l (of_nat O)) :: List.nil) l.
Proof.
apply disj_cons_L; first by apply disj_nil_L.
move/(my_max_list_prop _ (of_nat O)).
move/geP.
rewrite gebNgt => /negP.
apply; exact/gtP/gt_add1.
Qed.

End IntegralType_Prop.

(*Inductive negpos : Set :=
| neg : positive -> negpos
| pos : positive -> negpos.

Definition of_negpos (x : negpos) : Z :=
  match x with neg p => Zneg p | pos p => Zpos p end.

Definition negpos_eqb a b :=
  match (a, b) with
    | (neg a', neg b') => Ndec.Peqb a' b'
    | (pos a', pos b') => Ndec.Peqb a' b'
    | _ => false
  end.

Lemma negpos_eqbP : Equality.axiom negpos_eqb.
Proof.
  move=> x y.
  apply: (iffP idP) => H.
  destruct x; destruct y => //.
  rewrite /negpos_eqb /= in H.
  move/positiveP:H => H.
  subst => //.
  rewrite /negpos_eqb /= in H.
  move/positiveP:H => H.
  subst => //.
  subst.
  destruct y; rewrite /negpos_eqb => /=.
  apply/positiveP => //.
  apply/positiveP => //.
Qed.

Canonical Structure negpos_eqMixin := EqMixin negpos_eqbP.
Canonical Structure negpos_eqType := Eval hnf in EqType _ negpos_eqMixin.

Lemma negposP : forall x, of_negpos x <> Z_of_nat 0.
Proof. case=> p //=. Qed.

Definition to_negpos (i : Z) (H : i == Z_of_nat O <> true) : negpos.
Proof.
case: i H => // p H; [exact (pos p) | exact (neg p)].
Defined.

Lemma to_negposK : forall z (H : z == Z_of_nat O <> true), of_negpos (to_negpos z H) = z.
Proof. by case. Qed.

Lemma negpos_inj : forall x y, of_negpos x = of_negpos y -> x = y.
Proof. case=> p; case=> p' //=; case=> -> //. Qed.*)

Module ZIT <: IntegralType.

Definition t : eqType := Z_eqType.
Definition of_nat : nat -> t := Z_of_nat.
Definition of_nat_inj a b : of_nat a = of_nat b -> a = b := Z_of_nat_inj a b.

Definition add : t -> t -> t := Zplus.
Definition addA : forall a b c, add a (add b c) = add (add a b) c := addZA.
Definition addC : forall n m, add n m = add m n := addZC.
Definition add0 a : add a (of_nat 0) = a := addZ0 a.
Lemma add1 a : add (of_nat 1) (of_nat a) = of_nat a.+1.
Proof. by rewrite /add /of_nat !Z_S [Z_of_nat 0]/= add0Z addZC. Qed.

Definition sub := Zminus.
Definition mul := Zmult.
Definition div := divZ.
Definition rem := Zmod.
Definition abs := Z.abs.

Definition ge := Z.ge.
Definition gt := Z.gt.
Definition geb := Zge_bool.
Definition gtb := Zgt_bool.

Lemma geP a b : geb a b <-> ge a b. Proof. split => *; exact/geZP. Qed.
Lemma gtP a b : gtb a b <-> gt a b. Proof. split => *; by apply/gtZP. Qed.

Definition eqb := @eq_op Z_eqType. (* so that we can use eqxx *)
Lemma eqP : Equality.axiom eqb. Proof. move=> *; exact: eqP. Qed.

Lemma ge_refl a : ge a a. Proof. exact/Z.le_ge/leZZ. Qed.

Lemma gebNgt a b : geb b a = (~~ gtb a b).
Proof. by rewrite /gtb Z.gtb_ltb ltZNge' negbK -Z.geb_leb. Qed.

Lemma gtbE a b : gtb a b = geb a b && (a != b).
Proof.
apply/gtZP; case: ifP => [|/negP X Y].
  case/andP => /geZP X /eqP Y; lia.
apply/X/andP; split; [apply/geZP; lia | apply/eqP; lia].
Qed.

Lemma gtW a b : gt a b -> ge a b. Proof. rewrite /gt /ge; lia. Qed.

Lemma ge_trans b a c : ge a b -> ge b c -> ge a c.
Proof. move=> *; exact: (Zge_trans _ b) . Qed.

Lemma gt_add1 n : gt (add (of_nat 1) n) n.
Proof. rewrite /gt /add /of_nat [Z_of_nat _]/=; lia. Qed.

End ZIT.

Module Import ZIT_prop_m := IntegralType_Prop ZIT.

(* turn the abstract (A.t_geb _ _) = true, (A.t_ge _ _ ), etc. hypotheses into their implementation,
   so as to be able to use third-party tactics to solve goals (e.g., lia) *)

Ltac open_integral_type_hyp :=
  match goal with
    | |- is_true (ZIT.gtb _ _) => apply (proj1 (ZIT.gtP _ _)); unfold ZIT.gt
    | H : is_true (ZIT.gtb _ _) |- _ =>
        move: {H}(proj1 (ZIT.gtP _ _) H) => H; unfold ZIT.gt in H
    | |- is_true (~~ ZIT.gtb _ _) => apply (proj1 (gtb_false _ _)); unfold ZIT.gt
    | H : is_true (~~ ZIT.gtb _ _) |- _ =>
        move: {H}((proj1 (gtb_false _ _)) H) => H; unfold ZIT.gt in H
    | |- is_true (~~ ZIT.geb _ _) => apply (proj1 (geb_false _ _)); unfold ZIT.ge
    | |- is_true (ZIT.geb _ _) => apply (proj1 (ZIT.geP _ _)); unfold ZIT.ge
    | H : is_true (ZIT.geb _ _) |- _ =>
        move: {H}(proj1 (ZIT.geP _ _) H) => H; unfold ZIT.ge in H
    | H : is_true (~~ ZIT.geb _ _) |- _ =>
        move: {H}((proj1 (geb_false _ _)) H) => H; unfold ZIT.ge in H
    | |- is_true (ZIT.eqb _ _) => apply/ZIT.eqP
    | H : is_true (ZIT.eqb _ _) |- _ => move/ZIT.tP : H => H

    | H : context [ZIT.add _ _] |- _ => unfold ZIT.add in H
    | H : context [ZIT.sub _ _] |- _ => unfold ZIT.sub in H
    | H : context [ZIT.mul _ _] |- _ => unfold ZIT.mul in H
    | H : context [ZIT.gt _ _] |- _ => unfold ZIT.gt in H
    | H : context [ZIT.ge _ _] |- _ => unfold ZIT.ge in H
    | H : context [ZIT.of_nat _] |- _ => unfold ZIT.of_nat in H
  end.

Ltac open_integral_type_goal :=
  match goal with
    | |- _ => unfold ZIT.add, ZIT.sub, ZIT.mul, ZIT.gt, ZIT.ge, ZIT.of_nat, ZIT.geb, ZIT.gtb, ZIT.eqb
  end.

Lemma ZIT_ring_theory : @ring_theory ZIT.t Z0 1%Z Zplus Zmult Zminus Z.opp (@eq _).
Proof.
constructor.
exact add0Z.
exact addZC.
exact addZA.
exact mul1Z.
exact mulZC.
exact mulZA.
exact mulZDl.
move=> x [] //.
move=> x.
exact: addZN.
Qed.

Add Ring ZIT_ring : ZIT_ring_theory.

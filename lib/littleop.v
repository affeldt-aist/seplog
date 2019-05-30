(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool seq eqtype ssrnat.
From mathcomp Require Import path.
Require Import ssrZ seq_ext.
Require Export Setoid Relation_Definitions.
Require Import Init_ext.

Class Abelian {A: Type} (op: A -> A -> A) := {
  equiv : A -> A -> Prop;
  equiv_equivalence : Equivalence equiv;
  zero: A;
  zero_neutral : forall x, equiv (op x zero) x;
  opC : forall x y, equiv (op x y) (op y x);
  opA : forall x y z, equiv (op x (op y z)) (op (op x y) z);
  op_morphism : Morphisms.Proper (equiv ==> equiv ==> equiv) op
}.

Instance Abelean_equivalence {A: Type} op `{AA : @Abelian A op} : Equivalence equiv.
exact equiv_equivalence.
Defined.

Instance Abelean_morphism {A: Type} op `{AA : @Abelian A op} :
  Morphisms.Proper (equiv ==> equiv ==> equiv) op.
exact op_morphism.
Defined.

Instance Abelean_equiv {A: Type} op `{AA : @Abelian A op} :
  Morphisms.Proper (equiv ==> equiv ==> iff) equiv.
move=> x1 x2 Hx.
move=> y1 y2 Hy.
split=> H.
- transitivity x1; first by symmetry.
  by transitivity y1.
- transitivity x2; first by done.
  transitivity y2; first by done.
  by symmetry.
Defined.

Fixpoint Sum {A : Type} (op : A -> A -> A) {Ab : Abelian op} (l : seq A) : A :=
  match l with
    | nil => zero
    | hd :: nil => hd
    | hd :: tl => op hd (@Sum _ op Ab tl)
  end.

Check (Sum addn (4::5::nil)).

Set Implicit Arguments.

Section LittleOp.

Variable A: Type.

Variable op: A -> A -> A.

Context {AA : Abelian op}.

Notation "x + y" := (op x y) (at level 50, left associativity).
Notation "x === y" := (equiv x y)(at level 60).

(* Print HintDb typeclass_instances.*)

Lemma Sum_eq1 : Sum op nil = zero.
Proof. done. Qed.

Lemma Sum_eq2 P : Sum op (P :: nil) = P.
Proof. done. Qed.

Lemma Sum_eq3 P Q R : Sum op (P :: Q :: R) = P + Sum op (Q :: R).
Proof. done. Qed.

Lemma Sum_eq4 P Q : Sum op ( P::Q ) === P + Sum op Q.
Proof.
destruct Q.
- rewrite (zero_neutral P); reflexivity.
- rewrite Sum_eq3; reflexivity.
Qed.

Opaque Sum.

Lemma Sum_cons : forall tl hd, Sum op (cons hd tl) === hd + (Sum op tl).
Proof.
elim => //= hd.
- rewrite Sum_eq2 Sum_eq1; symmetry.
  by apply zero_neutral.
- move => l Hl hd0.
  rewrite Sum_eq3 Hl.
  by apply Equivalence_Reflexive.
Qed.

Lemma Sum_cat : forall l1 l2, Sum op (l1 ++ l2) === Sum op l1 + Sum op l2.
Proof.
elim.
- move=> l2 /=.
  rewrite opC zero_neutral; by apply Equivalence_Reflexive.
- move => hd tl Hind l2.
  rewrite Sum_cons.
  rewrite <- opA.
  rewrite <- Hind.
  rewrite <- Sum_cons; simpl; by apply Equivalence_Reflexive.
Qed.

Lemma Sum_op R P Q : Sum op ((P + Q) :: R) === Sum op (P :: Q :: R).
Proof. rewrite !Sum_cons opA; apply Equivalence_Reflexive. Qed.

Lemma Sum_perm_eq l l1 l2 : perm_eq l1 l2 ->
  Sum op (map_indices zero l l1) === Sum op (map_indices zero l l2).
Proof.
move/permP.
elim: l1 l2 => [| i l1 Hl1] l2 eq_l1l2.
  case: l2 eq_l1l2; last first.
  by move => // i l2; move/(_ (pred1 i)); rewrite /= eqxx.
  reflexivity.
have r2i: i \in l2 by rewrite -has_pred1 has_count -eq_l1l2 /= eqxx.
case/splitPr: l2 / r2i => [r3 r4] in eq_l1l2 *; rewrite /map_indices map_cons map_cat.
rewrite Sum_cat.
rewrite Sum_cons.
rewrite map_cons.
rewrite Sum_cons.
set X1 := Sum op (map _ r3).
set X2 := Sum op (map _ r4).
rewrite (opC X1).
rewrite <- opA.
apply op_morphism; first by apply Equivalence_Reflexive.
rewrite opC.
rewrite /X1 /X2.
rewrite <- Sum_cat.
rewrite /map_indices in Hl1.
rewrite -map_cat.
apply: Hl1 => a.
move/(_ a): eq_l1l2; rewrite !count_cat /=  addnCA; exact: addnI.
Qed.

Lemma Sum_rearrangement l l' : perm_eq l' (iota 0 (size l)) ->
  Sum op l === Sum op (map_indices zero l l').
Proof.
move=> Hl'.
rewrite -{1}(@map_indices_self _ zero l).
rewrite (Sum_perm_eq _ _ _ Hl'); apply Equivalence_Reflexive.
Qed.

Variable f: A -> A.

Context {f_morph: Morphisms.Proper (equiv ==> equiv) f}.

Variable f_zero:  f zero === zero.
Variable f_homomorphism: forall x y, f (x + y) === f x + f y.

Lemma Sum_distrib : forall l, f (Sum op l) === Sum op (map f l).
Proof.
elim => //=.
move => hd tl Hind.
rewrite Sum_cons.
rewrite f_homomorphism.
rewrite Sum_cons.
rewrite Hind; apply Equivalence_Reflexive.
Qed.

Inductive Sum_sem : seq A -> A -> Prop :=
| zero_sem: Sum_sem nil zero
| op_sem: forall l1 a1 l2 a2,
  Sum_sem l1 a1 ->
  Sum_sem l2 a2 ->
  Sum_sem (l1 ++ l2) (op a1 a2)
| elt_sem: forall e,
  Sum_sem (e::nil) e.

Lemma Sum_sem_conv {l} {e} : Sum_sem l e -> equiv (Sum op l) e.
Proof.
elim => //=; first by apply Equivalence_Reflexive.
move => l1 a1 l2 a2 _ H1 _ H2.
rewrite Sum_cat H1 H2; apply Equivalence_Reflexive.
move => *; apply Equivalence_Reflexive.
Qed.

End LittleOp.

Unset Implicit Arguments.

Ltac Sum_sem_compute i :=
  (eapply zero_sem || eapply (@op_sem _ _ i); [Sum_sem_compute i | Sum_sem_compute i] || eapply elt_sem).

Ltac Fold_abelean X i :=
  let ty := typeof X in
  let x := fresh in
    (evar (x: seq ty));
    let Hx := fresh in
      (have Hx: @Sum_sem _ _ i x X by Sum_sem_compute i);
      rewrite <- (@Sum_sem_conv _ _ _ _ _ Hx);
        unfold x; clear Hx x.

Opaque Sum.

Instance Sum_morphism {A} {op} `{Ab: @Abelian A op} : Morphisms.Proper (permutation ==> equiv) (Sum op).
move => l l'.
elim => //=.
- apply Equivalence_Reflexive.
- move => x l0 l'0 Hperm Hind.
  rewrite !Sum_cons.
  rewrite Hind; apply Equivalence_Reflexive.
- move => x y l0.
  rewrite !Sum_cons.
  rewrite -> opC at 1.
  rewrite <- opA.
  apply Abelean_morphism.
  apply Equivalence_Reflexive.
  rewrite -> opC; apply Equivalence_Reflexive.
- move => l1 l2 l3 Hperm1 Hequiv1 Hperm2 Hequiv2.
  rewrite -> Hequiv1.
  rewrite <- Hequiv2.
  apply Equivalence_Reflexive.
Defined.

Transparent Sum.

Ltac Solve_Abelean_equiv i :=
  match goal with
    | |- ?equiv ?X ?Y =>
      Fold_abelean X i; Fold_abelean Y i; apply Sum_morphism; simpl; Solve_permutation
  end.

Instance nat_abelean : Abelian addn.
eapply Build_Abelian with (equiv := @eq nat) (zero := 0).
apply eq_equivalence.
move=> x; apply addn0.
move=> x y ; apply addnC.
move=> x y z ; apply addnA.
move => x y Hxy x0 y0 Hx0y0; by subst.
Defined.

Canonical Structure nat_abelean.

Goal forall x y, 0 + 1 + x + y = y + 0 + 1 + x.
  move => x y.
  Solve_Abelean_equiv nat_abelean.
Abort.

(* a few instance of Abelean *)

Require Import machine_int.
Import MachineInt.

Section MIAbelean.

Variable n : nat.

Instance int_abelean: Abelian (@add n).
eapply Build_Abelian with (equiv := eq) (zero := Z2u n 0).
apply  @eq_equivalence.
move => x; apply addi0.
move => x y ; apply addC.
by move => x y z ; rewrite addA.
by move => x y Hxy x0 y0 Hx0y0; subst.
Defined.

End MIAbelean.

Arguments int_abelean [n].

Require Import ssrZ ZArith_ext.

Instance Z_abelean : Abelian Z.add.
eapply Build_Abelian with (equiv := eq) (zero := 0%Z).
apply  @eq_equivalence.
move => x; omega.
move => x y ; omega.
by move => x y z; omega.
by move => x y Hxy x0 y0 Hx0y0; subst.
Defined.

(* some lemmas over Sum *)

Lemma sum_Z_pos_pos : forall (l : seq Z),
  (forall x, x \in l -> 0 <= x)%Z ->
  (0 <= @Sum _ (Z.add) _ l)%Z.
Proof.
Opaque Sum.
elim; first by done.
move => hd tl Hind H.
destruct tl.
- rewrite Sum_eq2.
  apply H.
  by rewrite in_cons eq_refl.
- rewrite Sum_eq3.
  have hdPos: (0 <= hd)%Z.
  apply H.
  by rewrite in_cons eq_refl.
  suff Hpos: (0 <= @Sum _ (Z.add) Z_abelean (z :: tl))%Z.
  omega.
  apply Hind.
  move => x Hx.
  apply H.
  rewrite in_cons Hx.
  by rewrite orbC.
Transparent Sum.
Qed.

Local Open Scope zarith_ext_scope.

Lemma s2Z_sumop: forall {n} (l : seq (int n.+1)),
   (@Sum _ (Z.add) Z_abelean (map (@s2Z n.+1) l) < 2^^n)%Z ->
   foldr (fun hd acc => acc /\ 0 <= s2Z hd)%Z True l ->
   s2Z (@Sum _ (@add n.+1) (@int_abelean n.+1) l) = @Sum _ (Z.add) _ (map (@s2Z n.+1) l).
Opaque Sum.
move => n.
elim => //=.
- move => ? ?; rewrite s2Z_u2Z_pos'.
  + rewrite Z2uK //.
    split; [done | exact: expZ_gt0].
  + rewrite Z2uK.
    * split; [done | exact: expZ_gt0].
    * split; [done | exact: expZ_gt0].
- move => hd tl Hind H H0.
  destruct tl; first by rewrite 2!Sum_eq2; simpl.
  rewrite Sum_eq3 /=.
  rewrite (Sum_eq3 (s2Z hd)) /=.
  rewrite /= Sum_eq3 in H.
  simpl in H0.
  inversion_clear H0.
  inversion_clear H1.
  have Hpos: (0 <= @Sum _ (Z.add) Z_abelean [seq s2Z i | i <- i::tl])%Z.
    apply sum_Z_pos_pos.
    apply foldr_Prop_and.
    rewrite /= foldr_map.
    tauto.
  have Hind_eq1: (@Sum _ Z.add Z_abelean [seq s2Z i0 | i0 <- i :: tl] < 2 ^^ n)%Z.
    clear Hind.
    rewrite addZC in H; by apply Zlt_Zplus_inv in H.
  move: {Hind}(Hind Hind_eq1) => Hind.
  have Hind_eq2: foldr
                  (fun (hd : int n.+1) (acc : Prop) => acc /\ (0 <= s2Z hd)%Z)
                  True (i :: tl).
    simpl; tauto.
  move: {Hind}(Hind Hind_eq2) => Hind.
  rewrite s2Z_add.
  + by rewrite Hind.
  + rewrite Hind.
    split; last by apply H.
    move: (expZ_ge0 n) => ?.
    move: Hpos H3.
    set X := @Sum _ _ _ _.
    set Y := s2Z _.
    move => ? ?; omega.
Transparent Sum.
Qed.

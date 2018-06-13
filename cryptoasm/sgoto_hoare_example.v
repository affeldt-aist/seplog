(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext.
Require Import machine_int.
Import MachineInt.
Require Import mips_seplog.
Require Import goto sgoto sgoto_hoare.

Local Close Scope Z_scope.
Local Close Scope positive_scope.
Local Open Scope mips_expr_scope.

Module Import sgoto_hoare_m := SGoto_Hoare WMIPS_Hoare.
Import sgoto_m.
Import goto_deter_m.
Import goto_m.
Import assert_m.
Import expr_m.

Local Open Scope sgoto_scope.
Local Open Scope sgoto_hoare_scope.
Local Open Scope machine_int_scope.
Local Open Scope eqmod_scope.

Module SumOfFirstNaturals.

(** printing `< %\ensuremath{<}% *)
(** printing `<= %\ensuremath{\leq}% *)
(** printing `+ %\ensuremath{\boxplus}% *)
(** printing one16 %\ensuremath{1_{16}}% *)
(** printing one32 %\ensuremath{1_{32}}% *)
(** printing zero32 %\ensuremath{0_{32}}% *)

(** printing =m %\ensuremath{=}% *)
(** printing {{ %\ensuremath{[}% *)
(** printing }} %\ensuremath{]}% *)

(** * Example: The Sum of the n First Naturals *)

(** %\label{sec:example}%

   %\noindent% This example corresponds to Section 4.3 in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. The main difference is that the program is shown to compute its result %{\em modulo $2^{32}$}%#modulo 2^32#, which is not the case with the archetypal assembly language of %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. *)

(** We first define registers to hold an intermediate value
  %\coqdocvar{x}%#x#, the output %\coqdocvar{r}%#r#, and the input
  %\coqdocvar{n}%#n#. Since registers have a finite size, the number of
  values that can be represented is limited. *)

Definition x := reg_t0.
Definition r := reg_t1.
Definition n := reg_t2.

(** The program consists of the following four labeled instructions: *)

Definition i1 := sB 1 (cjmp (beq x n) 5).
Definition i2 := sC 2 (addiu x x one16).
Definition i3 := sC 3 (addu r x r).
Definition i4 := sB 4 (jmp 1).
Definition prg : scode := i1 [+] ((i2 [+] i3) [+] i4).

(** The pre-condition is as follows. The output value %\coqdocvar{r}%#r# is initialized to 0
and the input value is expected to be positive (which actually holds naturally when registers' contents are regarded as unsigned). *)

Definition I1 : assn := fun pc => fun s h => pc = 1 /\ zero32 `<= [n]_s /\ [x]_s = zero32 /\ [r]_s = zero32.

(** The post-condition is as follows. The intermediate value %\coqdocvar{x}%#x# (repeatedly incremented during execution) is expected to be equal to the input value %\coqdocvar{n}%#n# and the output value is exepected to be equal to the sum of the $n$#n# first naturals %{\em modulo $2^{32}$}%#modulo 2^32#. The non-modulo equality cannot be achieved in practice because of potential arithmetic overflows. %\coqdoccst{u2Z}%#u2Z# is a function that interprets a finite-size integer as unsigned and returns its decimal value. *)

Local Open Scope zarith_ext_scope.

Definition I5' : assn := fun pc => fun s h => pc = 5 /\
  [x]_s = [n]_s /\ u2Z [r]_s =m Zisum (u2Z [x]_s) {{2^^32}}.

Definition I1' : assn := fun pc => fun s h => pc = 1 /\
  [x]_s `<= [n]_s /\
  u2Z [r]_s =m Zisum (u2Z [x]_s) {{ 2^^32 }}.

Definition I2 : assn := fun pc => fun s h => pc = 2 /\
  [x]_s `< [n]_s /\
  [x]_s `<= [n]_s /\
  u2Z [r]_s =m Zisum (u2Z [x]_s) {{ 2^^32 }}.

(** The correctness proof consists of the application of the rules of the Hoare logic for %\sgoto%#SGoto#. For the purpose of presentation, this proof can be decomposed in a sequence of basic steps, each consisting of the application of a single rule of the Hoare logic. For example, the following step shows that the addition of the intermediate value really corresponds to compute and add the next natural. *)

Definition I2' : assn := fun pc => fun s h => pc = 2 /\
  [x]_s `< [n]_s /\ u2Z [r]_s =m Zisum (u2Z [x]_s) {{ 2^^32 }}.

Definition I2'' : assn := fun pc => fun s h => pc = 2 /\
  [x]_s `+ one32 `<= [n]_s /\
  u2Z [r]_s + u2Z ([x]_s `+ one32) =m Zisum (u2Z ([x]_s `+ one32)) {{2^^32}}.

Definition I3 : assn := fun pc => fun s h => pc = 3 /\ [x]_s `<= [n]_s /\
  u2Z ([x]_s `+ [r]_s) =m Zisum (u2Z [x]_s) {{2^^32}}.

Definition I4 : assn := fun pc => fun s h => pc = 4 /\
  [x]_s `<= [n]_s /\
  u2Z [r]_s =m Zisum (u2Z [x]_s) {{2^^32}}.

Definition I5 : assn := fun pc => fun s h => pc = 5 /\
  ~ [x]_s `< [n]_s /\
  [x]_s `<= [n]_s /\
  u2Z [r]_s =m Zisum (u2Z [x]_s) {{2^^32}}.

Local Open Scope  mips_assert_scope.

Definition I1'24 := fun pc => I1' pc \\// (I2 pc \\// I4 pc).

Definition I1'25 : assn := fun pc => I1' pc \\// (I2 pc \\// I5 pc).

Definition I2'34 : assn := fun pc => I2' pc \\// (I3 pc \\// I4 pc).

Definition I25 : assn := fun pc => fun s h => I2 pc s h \/ I5 pc s h.

Definition J1' : assn := fun pc => fun s h =>
  pc = 1 /\
     (~~ eval_b (beq x n) s /\ I25 (S 1) s h
     \/
     (eval_b (beq x n) s) /\ (I25 5 s h \/ 5 = 1))
  \/
  pc <> 1 /\ I25 pc s h .

Definition J2'' : assn := fun pc => fun s h =>
  pc = 2 /\ (wp0 (addiu x x one16) (I3 3)) s h
  \/
  pc <> 2 /\ I3 pc s h.

Definition J3 : assn := fun pc => fun s h =>
  pc = 3 /\ (wp0 (addu r x r) (I4 4)) s h
  \/
  pc <> 3 /\ I4 pc s h.

Definition J4 : assn := fun pc => fun s h =>
  pc = 4 /\ (I1' 1 s h \/ 1 = 4)
  \/
  pc <> 4 /\ I1' pc s h.

Lemma step_20 : [^ J2'' ^] i2 [^ I3 ^].
Proof. rewrite /J2'' /i2. by apply hoare_cmd. Qed.

Lemma step_19 : [^ J2'' ^] i2 [^ I3 ^] -> [^ I2'' ^] i2 [^ I3 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h.
- rewrite /I2'' /J2''.
  case=> H1 [H2 H3]; subst l; left; split; first by [].
  rewrite /wp0 /wp_addiu /I3; split; first by [].
  rewrite store.get_upd' // !store.get_upd // /one16 /one32 sext_Z2u //.
  split; first by [].
  eapply eqmod_trans; first by apply u2Z_add_eqmod.
  by rewrite addZC.
- by apply hoare_prop_m.entails_id.
Qed.

Local Open Scope Z_scope.

Lemma step_18 :  [^ I2'' ^] i2 [^ I3 ^] -> [^ I2' ^] i2 [^ I3 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h.
- rewrite /I2' /I2''.
  case=> ? [x_lt_n Hr]; subst l; split; first by [].
  split; first exact: add_n_lt_n.
  eapply eqmod_trans.
  + eapply eqmod_compat_plus_R; by apply Hr.
  + apply lt_n2Zlt in x_lt_n.
    have X : u2Z [x]_s < 2 ^^ 32 - 1 by move: (max_u2Z [n]_s) => ?; omega.
    case: (Z_lt_le_dec (u2Z [x]_s + u2Z one32) (2 ^^ 32)) => Y.
    * rewrite u2Z_add // Z2uK // Zisum_prop.
      by apply eqmod_refl.
      by apply min_u2Z.
    * rewrite Z2uK // in Y.
      have : ~ (2 ^^ 32 <= u2Z [x]_s + 1) by omega.
      tauto.
- by apply hoare_prop_m.entails_id.
Qed.

Local Close Scope Z_scope.
Local Close Scope zarith_ext_scope.

Lemma step_17 : [^ I2' ^] i2 [^ I3 ^] ->
  [^ restrict I2'34 (sdom i2) ^] i2 [^ I2'34 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h.
- rewrite /restrict /while.And /I2'34 /I2' /=.
  case=> X [H0 | H0 //].
  split; first by done.
  case: X => [X | [ [H1 H3] | [H1 H4] ] ].
  * tauto.
  * by subst l.
  * by subst l.
- rewrite /I3 /I2'34 => X; by right; left.
Qed.

Lemma step_16 : [^ J3 ^] i3 [^ I4 ^].
Proof. rewrite /J3 /i3. by apply hoare_cmd. Qed.

Lemma step_15 : [^ J3 ^] i3 [^ I4 ^] -> [^ I3 ^] i3 [^ I4 ^].
Proof.
move=> H; apply hoare_sgoto_conseq with J3 I4 => // l s h.
- rewrite /I3 /J3.
  case=> H1 [H2 H3].
  left; split; first by [].
  rewrite /wp0 /wp_addu /I4; split; first by [].
  by rewrite store.get_upd' // !store.get_upd.
- by apply hoare_prop_m.entails_id.
Qed.

Lemma step_14 : [^ I3 ^] i3 [^ I4 ^] ->
  [^ restrict I2'34 (sdom i3) ^] i3 [^ I2'34 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h.
- rewrite /restrict /I2'34; move=> [[X|X] Y].
  case: X => X //; subst l; rewrite /= in Y; by case: Y.
  case: X => X //.
  case: X => X //; subst l; rewrite /= in Y; by case: Y.
- rewrite /I2'34 => H'; by right; right.
Qed.

Lemma step_13 : [^ restrict I2'34 (sdom i2) ^] i2 [^ I2'34 ^] ->
  [^ restrict I2'34 (sdom i3) ^] i3 [^ I2'34 ^] ->
  [^ I2'34 ^] i2 [+] i3 [^ restrict_cplt I2'34 (sdom (i2 [+] i3)) ^].
Proof. move=> ? ?. by apply hoare_sS. Qed.

Lemma step_12 : [^ I2'34 ^] i2 [+] i3 [^ restrict_cplt I2'34 (sdom (i2 [+] i3)) ^] ->
  [^ I2' ^] i2 [+] i3 [^ I4 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h.
- rewrite /I2'34 => H'; by left.
- rewrite /restrict_cplt /while.Not; move => /= [X [ [Y1 _] | [ [Y1 _] | Y ] ] ] //; subst l; tauto.
Qed.

Lemma step_11 : [^ I2' ^] i2 [+] i3 [^ I4 ^] -> [^ I2 ^] i2 [+] i3 [^ I4 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h.
- rewrite /I2 /I2'; by move=> [X [Y [Z W]]].
- by apply hoare_prop_m.entails_id.
Qed.

Lemma step_10 : [^ I2 ^] i2 [+] i3 [^ I4 ^] ->
  [^ restrict I1'24 (sdom (i2 [+] i3)) ^] i2 [+] i3 [^ I1'24 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h.
- rewrite /restrict /I1'24; move=> [X /= Y].
  case: X => [X | X].
  + case: X => X //; subst l.
    case: Y => //; by case.
  + case: X => X //.
    case: X => X //; subst l.
    case: Y => //; by case.
- move=> *; by right; right.
Qed.

Lemma step_9 : [^ J4 ^] i4 [^ I1' ^].
Proof. rewrite /J4 /i4. by apply hoare_jmp. Qed.

Lemma step_8 :
  [^ J4 ^] i4 [^ I1' ^] -> [^ restrict I1'24 (sdom i4) ^] i4 [^ I1'24 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h.
- rewrite /I1'24 /J4; case; case => [ [?] | [ [?] | [?] ]] X; subst l.
  + by right.
  + by case.
  + move=> _; left; split => //; by left.
- rewrite /I1'24 /while.Or; tauto.
Qed.

Lemma step_7 :
  [^ restrict I1'24 (sdom (i2[+]i3)) ^] i2 [+] i3 [^ I1'24 ^] ->
  [^ restrict I1'24 (sdom i4) ^] i4 [^ I1'24 ^] ->
  [^ I1'24 ^] (i2 [+] i3) [+] i4 [^ restrict_cplt I1'24 (sdom ((i2 [+] i3) [+] i4)) ^].
Proof. move=> ? ?; by apply hoare_sS. Qed.

Lemma step_6 :
  [^ I1'24 ^] (i2 [+] i3) [+] i4 [^ restrict_cplt I1'24 (sdom ((i2 [+] i3) [+] i4)) ^] ->
  [^ restrict I1'25 (sdom ((i2 [+] i3) [+] i4)) ^] (i2 [+] i3) [+] i4 [^ I1'25 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h.
- rewrite /restrict; move=> /= [[ [X1 _] | [ X | [X1 _] ] ] Y].
  + subst l; by firstorder.
  + by right; left.
  + subst l; by firstorder.
- rewrite /restrict_cplt /while.Not; move => /= [X [ Y | [Y | [Y1 _]]]].
  + by left.
  + by right; left.
  + subst l; tauto.
Qed.

Lemma step_5 : [^ J1' ^] i1 [^ I25 ^].
Proof. rewrite /J1' /i1.
move: hoare_branch. rewrite /WMIPS_Hoare.eval_b. by apply.
Qed.

Lemma step_4 : [^ J1' ^] i1 [^ I25 ^] ->
  [^ restrict I1'25 (sdom i1) ^] i1 [^ I1'25 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h.
- rewrite /restrict /while.And; case; case=> [ H1 _ | H1 H2].
  + rewrite /I1' in H1; rewrite /J1'.
    case: H1 => Hl [H2 H3].
    left; split; first exact Hl.
    case/boolP : (eval_b (beq x n) s) => [/eqP/u2Z_inj |] X.
    * right; split; first by [].
      left; rewrite /I25 /I5; right.
      split; first by [].
      rewrite {1 2}X.
      split; first exact: lt_n_irrefl.
      split; by [exact: le_n_refl | ].
    * left; split; first by [].
      rewrite /I25 /I2; left; split; first by [].
      split; last by [].
      apply le_nE in H2.
      case : H2 => H2 //.
      rewrite /= H2 in X.
      by move/eqP : X.
  + rewrite /= in H2; case : H2 => H2 //.
    subst l; case : H1; by case.
- rewrite /I25 /I1'25 /while.Or; tauto.
Qed.

Lemma step_3 : [^ restrict I1'25 (sdom i1) ^] i1 [^ I1'25 ^] ->
  [^ restrict I1'25 (sdom ((i2 [+] i3) [+] i4)) ^] (i2 [+] i3) [+] i4 [^ I1'25 ^] ->
  [^ I1'25 ^] prg [^ restrict_cplt I1'25 (sdom prg) ^].
Proof. move=> ? ?; by apply hoare_sS. Qed.

Lemma step_2 : [^ I1'25  ^] prg [^ restrict_cplt I1'25 (sdom prg) ^] ->
  [^ I1' ^] prg [^ I5 ^].
Proof.
move=> H; eapply hoare_sgoto_conseq; eauto => l s h; rewrite /I1'25.
- rewrite /while.Or; tauto.
- move=> [H1 [ [H2 _]|[ [H2 _] | H2 //]]]; subst l; by firstorder.
Qed.

Lemma step_1 : [^ I1' ^] prg [^ I5 ^] -> [^ I1 ^] prg [^ I5' ^].
Proof.
move=> H; apply hoare_sgoto_conseq with I1' I5 => //.
- move=> l s h; rewrite /I1 /I1'; move => [Hl [O_le_n [Hx Hr]]].
  rewrite Hx Hr Z2uK //.
  split; first by [].
  split; first by [].
  by apply eqmod_refl.
- move=> l s h; rewrite /I5 /I5'; move=> [H1 [H2 [x_le_n H4]]].
  move/le_nE in x_le_n; tauto.
Qed.

(** Once all such steps are proved individually, the correctness proof consists in the sequential application of the corresponding lemmas: *)

Lemma prf : [^ I1 ^] prg [^ I5' ^].
Proof.
apply step_1.
apply step_2.
apply step_3.
apply step_4.
apply step_5.
apply step_6.
apply step_7; last first.
apply step_8.
apply step_9.
apply step_10.
apply step_11.
apply step_12.
apply step_13; last first.
apply step_14.
apply step_15.
apply step_16.
apply step_17.
apply step_18.
apply step_19.
by apply step_20.
Qed.

End SumOfFirstNaturals.

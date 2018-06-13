(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith.
Notation "m ^ n" := (expn m n) : nat_scope. (* TODO: kludge *)
Require Import Znumtheory.
Require Import ssrZ.
Export ZArith.
Export Znumtheory.

Local Close Scope positive_scope.
Local Close Scope Z_scope.

Local Open Scope zarith_ext_scope.

Lemma positiveP : Equality.axiom Pos.eqb.
Proof.
move=> x y.
apply: (iffP idP); first by move/Ndec.Peqb_Pcompare/Pcompare_Eq_eq.
move=> ->; exact: Ndec.Peqb_correct.
Qed.

Canonical Structure positive_eqMixin := EqMixin positiveP.
Canonical Structure positive_eqType := Eval hnf in EqType _ positive_eqMixin.

Local Open Scope Z_scope.

Lemma Zle_minus_1 a b : a < b -> a <= b - 1.
Proof. omega. Qed.

Lemma Zminus_le_decr a b : 0 <= b -> a - b <= a.
Proof. move=> Hb. omega. Qed.

Lemma Zmult_sign : forall a b, 0 <= a -> b <= 0 -> a * b <= 0.
Proof.
move=> [|a|a] // b Ha Hb.
by case: b Hb.
Qed.

Lemma Z_S n : Z_of_nat n.+1 = Z_of_nat n + 1.
Proof. by rewrite inj_S. Qed.

Lemma Zmult_neg' a b : a < 0 -> (0 < b)%nat -> a * Z_of_nat b < 0.
Proof.
elim: b a => [a Ha | [|b] IHb a Ha _].
- by rewrite ltnn.
- by rewrite mulZ1.
- rewrite Z_S mulZDr mulZ1 -(addZ0 0).
  apply ltZ_add => //; exact: IHb.
Qed.

Lemma Zmult_neg a b : a < 0 -> 0 < b -> a * b < 0.
Proof.
move=> Ha Hb.
move/ltZW : (Hb) => Hb'.
move/Z_of_nat_complete : Hb' => [[|b'] Hb'].
- move: Hb; by rewrite Hb' => /ltZP; rewrite ltZZ'.
- rewrite Hb'; exact/Zmult_neg'.
Qed.

Lemma Zle_scale a b : 0 <= a -> 0 < b -> a <= a * b.
Proof.
move=> Ha Hb.
rewrite (_ : a * b = a + a * (b - 1)); last by ring.
rewrite -{1}(addZ0 a); apply/leZ_add2l/mulZ_ge0; omega.
Qed.

Lemma Zle_scale_neg a b : a <=0 -> 0 < b -> a * b <= a.
Proof.
move=> Ha Hb.
rewrite (_ : a * b = a + a * (b - 1)); last by ring.
rewrite -{3}(addZ0 a).
apply leZ_add2l.
rewrite mulZC.
apply Zmult_sign => //; omega.
Qed.

Lemma Zle_plus_trans a b c : 0 <= b -> a <= c -> a <= b + c.
Proof.
move=> Hb a_c.
rewrite -(add0Z a).
exact: leZ_add.
Qed.

Lemma Zle_plus_trans_L a b c : b <= 0 -> a <= c -> a + b <= c.
Proof.
move=> Hb a_c.
rewrite -(addZ0 c).
exact: leZ_add.
Qed.

(* NB: Coq.ZArith.Zorder.Zmult_lt_compat2 *)
Lemma Zlt_Zmult_inv' a b c : 0 <= a -> 0 < b -> 0 <= c -> a * b < c -> a < c.
Proof.
move=> Ha Hb Hc Habc.
apply (ltZ_pmul2r b) => //.
apply (@ltZ_leZ_trans c) => //.
apply Zle_scale; omega.
Qed.

Lemma Zlt_Zmult_inv a b c : (a * b < c -> 0 < a -> 0 <= c -> b < c)%Z.
Proof.
move=> H Ha Hc.
case: (Z_lt_le_dec b 0) => Hb.
exact/(@ltZ_leZ_trans Z0).
apply Zlt_Zmult_inv' with a => //.
by rewrite mulZC.
Qed.

Lemma Zlt_Zplus_inv a b c : 0 <= b -> a + b < c -> a < c.
Proof. move=> Hb ab_c. omega. Qed.

Lemma Zle_neq_lt n m : n <= m -> n <> m -> n < m.
Proof. move=> *; omega. Qed.

Lemma Z_of_nat_neg : forall z, (Z_of_nat z <= 0)%Z -> z = O.
Proof. by case. Qed.

Lemma Z_of_nat_0 : forall a, Z_of_nat a = 0 -> a = O.
Proof. by case. Qed.

Lemma Z_of_nat_lt0 : forall a, (0 < a)%nat -> 0 < Z_of_nat a.
Proof. case=> //; by inversion 1. Qed.

Lemma Zplus_pos_inv a b c d : a <= c -> b <= d -> a + b = c + d -> a = c /\ b = d.
Proof. move=> H H1 H2. omega. Qed.

Lemma Zle_plus_0_inv a b : a + b <= 0 -> 0 <= a -> b <= 0.
Proof. move=> H. omega. Qed.

Lemma Zle_0_mult_inv a b : 0 <= a * b -> (0 <= a /\ 0 <= b) \/ (a <= 0 /\ b <= 0).
Proof.
move=> H; destruct a.
- destruct b; omega.
- destruct b.
  + omega.
  + by left.
  + move: (Pos2Z.is_pos p) => H1.
    move: (Zlt_neg_0 p0) => H2.
    have H3 : Zpos p * Zneg p0 < 0.
      rewrite mulZC.
      by apply Zmult_neg.
    omega.
- destruct b.
  + omega.
  + move: (Pos2Z.is_pos p0) => H1.
    move: (Zlt_neg_0 p) => H2.
    have H3 : Zneg p * Zpos p0 < 0.
      by apply Zmult_neg.
    omega.
  + by right.
Qed.

(* NB: see also Zmult_lt_0_reg_r *)
Lemma Zle_mult_0_inv a b : a * b <= 0 -> 0 < a -> b <= 0.
Proof.
move=> H Ha.
case: (Z_lt_le_dec 0 b) => // Hb.
move: (mulZ_gt0 a b Ha Hb).
by move/ltZNge.
Qed.

Lemma Zlt_mult_0_inv a b :  a * b < 0 -> (a < 0 /\ 0 < b) \/ (0 < a /\ b < 0).
Proof.
move=> H; destruct a.
- rewrite mul0Z in H.
  by apply ltZZ in H.
- destruct b.
  + omega.
  + by left.
  + move: (Pos2Z.is_pos p) => H1.
    move: (Zlt_neg_0 p0) => H2.
    have H3 : Zpos p * Zneg p0 < 0.
      rewrite mulZC.
      by apply Zmult_neg.
    omega.
- destruct b.
  + omega.
  + move: (Pos2Z.is_pos p0) => H1.
    move: (Zlt_neg_0 p) => H2.
    have H3 : Zneg p * Zpos p0 < 0.
      by apply Zmult_neg.
    omega.
  + by right.
Qed.

Lemma Zlt_mult_interval_inv b k a : (0 < k)%Z -> (- b <= k * a < b)%Z -> (- b <= a < b)%Z.
Proof.
move=> Hk [H1 H2].
split.
  case: (Z_lt_ge_dec 0 a) => ?.
    apply (@leZ_trans Z0); omega.
  apply (leZ_trans H1).
  rewrite -{2}(mul1Z a).
  apply Z.mul_le_mono_nonpos_r.
  exact: Zge_le.
  omega.
case: (Z_lt_ge_dec 0 a) => ?.
  apply: (leZ_ltZ_trans _ H2).
  rewrite -{1}(mul1Z a).
  apply Z.mul_le_mono_pos_r => //.
  omega.
omega.
Qed.

Lemma Zabs_Z_of_nat : forall n, `| Z_of_nat n | = Z_of_nat n.
Proof. by case. Qed.

Lemma Zabs_Zsgn_1 : forall z, z <> 0 -> `| sgZ z | = 1.
Proof. by case. Qed.

Lemma Zabs_nat_0_inv : forall a, '| a | = O -> a = 0.
Proof. case=> //= p H; move: (lt_O_nat_of_P p); rewrite H; by inversion 1. Qed.

Lemma Zabs_nat_mult : forall a b, '| a * b | = ('| a | * '| b |)%nat.
Proof. move=> [|p|p] [|q|q] //=; by rewrite nat_of_P_mult_morphism. Qed.

Lemma Z_of_nat_Zabs_nat z : 0 <= z -> Z<=nat '| z | = z.
Proof. case : z => //= p Hp; by rewrite Zpos_eq_Z_of_nat_o_nat_of_P. Qed.

Lemma S_Zabs_nat n : 0 <= n -> '| n |.+1 = '| n + 1 |.
Proof.
case : n => //; rewrite /= => p _.
by rewrite nat_of_P_plus_morphism // plus_comm.
Qed.

Lemma O_lt_Zabs_nat z : 0 < z -> (O < '| z |)%nat.
Proof.
move=> Hz; rewrite (_ : O = '| 0 |) //.
apply/ltP/Zabs_nat_lt; split => //; exact: leZZ.
Qed.

Lemma Z_of_nat_Zsgn l : Z_of_nat l = sgZ (Z_of_nat l) * Z_of_nat l.
Proof. by case: l. Qed.

Lemma Zsgn_pos0 : forall z, 0 <= z <-> 0 <= sgZ z.
Proof. by case. Qed.

Lemma Zsgn_neg0 : forall z, z <= 0 <-> sgZ z <= 0.
Proof. by case. Qed.

Lemma Zodd_Zsgn : forall z, z <> 0 -> Zodd (sgZ z).
Proof. by case. Qed.

Lemma Zabs_lt b z : - b < z < b -> `| z | < b.
Proof.
move=> [H1 H2].
case: (Z_le_gt_dec 0 z) => Hz; first by rewrite Z.abs_eq.
rewrite Zabs_non_eq; [omega | exact/ltZW/Z.gt_lt].
Qed.

Lemma Zlt_abs b z : `| z | < b -> - b < z < b.
Proof.
move=> H.
case: (Z_le_gt_dec z 0) => Hz.
  rewrite Zabs_non_eq // in H; omega.
rewrite Z.abs_eq // in H; last by omega.
split; [omega|done].
Qed.

Lemma Zabs_le b z : - b <= z <= b -> `| z | <= b.
Proof.
move=> [H1 H2].
case: (Z_le_gt_dec 0 z) => Hz; first by rewrite Z.abs_eq.
rewrite Zabs_non_eq; [omega | exact/ltZW/Z.gt_lt].
Qed.

Lemma Zlt_0_Zdiv a b : 0 < b -> b <= a -> 0 < a / b.
Proof.
move/Z.lt_gt => Hb Hba.
rewrite (_ : a = b * 1 + (a - b)); last omega.
rewrite mulZC Z_div_plus_full_l; last omega.
apply (@ltZ_leZ_trans 1); first by auto.
have ? : 0 <= (a - b) / b by apply Z_div_pos => //; omega.
omega.
Qed.

Lemma Z_div_neg a b : b > 0 -> a <= 0 -> a / b <= 0.
Proof. move=> ? ?; apply Zdiv_le_upper_bound => //; exact/Z.gt_lt. Qed.

Lemma Zdiv_le_pos : forall z b, 0 <= z -> 0 < b -> z / b <= z.
Proof. move=> *. apply Zdiv_le_upper_bound => //; exact: Zle_scale. Qed.

Lemma Zdiv_le_neg : forall z b, z <= 0 -> 0 < b -> z <= z / b.
Proof. move=> *; apply Zdiv_le_lower_bound => //; exact: Zle_scale_neg. Qed.

Lemma poly_eq0_inv : forall a b k, 0 <= k -> -k < b < k ->
  a * k + b = 0 -> a = 0 /\ b = 0.
Proof.
move=> a b k H H0 H1.
case/leZ_eqVlt : H => H.
subst k; omega.
have {H1}H1 : a * k = - b by omega.
case: (Z_lt_ge_dec a 0) => ?.
- have H2 :  b > 0.
    suff ? : -b < 0 by omega.
    rewrite -H1.
    by apply Zmult_neg.
  have H5 : a * k <= - k.
    rewrite (_ : -k = (-1) * k); last omega.
    apply leZ_pmul2r; omega.
  rewrite H1 in H5.
  have ? : k <= b by omega.
  omega.
- case: (Z.eq_dec a 0) => H2.
  + split; first assumption.
    subst a; omega.
  + have H3 : a > 0 by omega.
    have H4 : b < 0.
      suff ? : 0 < -b by omega.
      rewrite -H1.
      apply mulZ_gt0; omega.
    have H5 : k <= a * k.
      cutrewrite (k = 1 * k); last by omega.
      apply leZ_pmul => //; omega.
    rewrite H1 in H5.
    have ? : -k >= b by omega.
    exfalso.
    omega.
Qed.

Lemma poly_eq_inv a b a' b' k :
  0 <= a /\ 0 <= b < k /\ 0 <= a' /\ 0 <= b' < k ->
  a * k + b = a' * k + b' -> a = a' /\ b = b'.
Proof.
move=> H H0.
have {H0}H0 : (a - a') * k + (b - b') = 0 by rewrite mulZBl; omega.
have H1 : (0 < k) by omega.
have H2 : (-k < b - b' < k) by omega.
move: (poly_eq0_inv _ _ _ (ltZW H1) H2 H0) => ?; omega.
Qed.

Lemma poly_Zlt1_inv b a k : 0 <= b -> 0 <= a -> 0 <= k ->
  a * k + b < k -> a = 0.
Proof.
move=> Hb Ha Hk H.
destruct a => //.
move=> {Ha}.
have H' : 1 * k <= Zpos p * k.
  apply leZ_wpmul2r => //.
  by case: p H.
have ? : k <= b + Zpos p * k by omega.
omega.
Qed.

Lemma poly_Zlt1_Zabs_inv b a k : 0 <= b -> 0 <= a -> 0 <= k ->
  Z.abs (a * k + b) < k -> a = 0.
Proof.
move=> Hb Ha Hk.
rewrite Z.abs_eq //; first exact/poly_Zlt1_inv.
apply addZ_ge0 => //; exact/mulZ_ge0.
Qed.

Lemma poly_Zlt a a' b b' k :
  0 <= a -> 0 <= a' -> 0 <= b -> 0 <= b' -> 0 <= k ->
  a < k ->
  a >= a' ->
  b < b' ->
  a + k * b < a' + k * b'.
Proof.
move=> Ha Ha' Hb Hb' Hk Hak Haa' Hbb'.
have [b'' Hb''] : exists b'', b' = 1 + b'' by exists (b'-1); omega.
subst b'.
rewrite mulZDr mulZ1 addZA.
apply ltZ_le_add => //; [omega| apply leZ_wpmul2l => //; omega].
Qed.

Lemma ZsgnK z : sgZ (sgZ z) = sgZ z.
Proof. by case : z. Qed.

Definition bZsgn z := if z == 0 then 1%Z else (-1)%Z.

Lemma Zmod_le : forall a b, 0 <= b -> 0 <= a mod b.
Proof.
move=> a; case.
- move=> _; rewrite Zmod_0_r //.
- move=> p H.
  have X : Zpos p > 0 by done.
  move: (Z_mod_lt a (Zpos p) X).
  by tauto.
- move=> p H.
  move: (Zlt_neg_0 p) => H'; by omega.
Qed.

(* similar to Coq.ZArith.Zpower.Zpower_nat *)
(* see also Coq.ZArith.Zpow_def.Zpower *)
Fixpoint expZ (b : Z) (e : nat) { struct e } : Z :=
  match e with
    | O => 1
    | e'.+1 => b * expZ b e'
  end.

Notation "b ^^ e" := (expZ b e) (at level 30, right associativity) : zarith_ext_scope.

Lemma ZpowerS : forall k n, k ^^ n.+1 = k * k ^^ n. Proof. by []. Qed.

Lemma ZpowerD b : forall n m, b ^^ (n + m) = b ^^ n * b ^^ m.
Proof.
elim => [m|n IH m].
by rewrite [Zmult]lock /= -lock mul1Z.
rewrite addSn 2!ZpowerS IH; ring.
Qed.

Lemma expZ_gt0 : forall n, 0 < 2 ^^ n.
Proof. elim => // n IH; rewrite ZpowerS; omega. Qed.

Lemma expZ_ge0 n : 0 <= 2 ^^ n.
Proof. by move: (expZ_gt0 n) => /ltZW. Qed.

Lemma expZ_ge1 n : 1 <= 2 ^^ n.
Proof. move: (expZ_gt0 n) => ?; omega. Qed.

Lemma expZ_2_lt : forall n m, (n < m)%nat -> 2 ^^ n < 2 ^^ m.
Proof.
elim => [ [|m _] | n IH [ // |m] ].
- by rewrite ltnn.
- apply (@ltZ_leZ_trans 2) => //.
  rewrite ZpowerS.
  move: (expZ_ge1 m) => ?; omega.
- rewrite ltnS => /IH.
  rewrite 2!ZpowerS => ?; omega.
Qed.

Lemma Zpower_2_le n m : (2 ^^ n <=? 2 ^^ m) = (n <= m)%nat.
Proof.
apply/esym.
apply/idP/idP.
  elim : n m.
  - move=> m _ /=; exact/leZP/expZ_ge1.
  - move=> n IH [|m] //.
    rewrite ltnS => /IH.
    rewrite 2!ZpowerS => ?.
    by rewrite leZ_pmul2l'.
move=> H.
rewrite leqNgt; apply/negP => n_m.
move/leZP : H; exact/ltZNge/expZ_2_lt.
Qed.

Lemma Zpower_2_inv n m : 2 ^^ n.+1 < 2 ^^ m.+1 -> (n < m)%nat.
Proof.
move=> H.
rewrite ltnNge; apply/negP => n_m.
apply/leZNgt/leZP : H; by rewrite Zpower_2_le.
Qed.

Lemma Zpower_plus n : 2 ^^ n + 2 ^^ n = 2 ^^ n.+1.
Proof. rewrite ZpowerS; by ring. Qed.

Lemma Zpower_b_square z : z * z = z ^^ 2.
Proof. move=> /=. rewrite mulZ1 //. Qed.

Lemma expZM : forall m n z, (z ^^ n) ^^ m = z ^^ (n * m).
Proof.
elim => [m z /= | n IHn m z].
- by rewrite muln0.
- by rewrite ZpowerS mulnC ZpowerD IHn mulnC.
Qed.

Lemma Zpower_exp_mod : forall m n z modu,
  (z ^^ n mod modu) ^^ m mod modu = z ^^ (n * m) mod modu.
Proof.
elim=> [m z modu /= | n IHn m z modu].
- by rewrite muln0.
- by rewrite ZpowerS mulnC ZpowerD -Zmult_mod_idemp_r IHn -Zmult_mod mulnC.
Qed.

Lemma power_Zpower b n : Z_of_nat (b ^ n) = Z_of_nat b ^^ n.
Proof. elim : n => // n0 IH; by rewrite expnS ZpowerS inj_mult IH. Qed.

Lemma Zabs_power (a : Z) : forall (b : nat), 0 <= a -> `| a ^^ b | = a ^^ b.
Proof.
elim=> // b IH Ha /=.
by rewrite normZM geZ0_norm // IH.
Qed.

Lemma Zpower_mod b : forall (n : nat), O <> n -> b ^^ n mod b = 0.
Proof. by move=> [|n] //= _; rewrite mulZC Z_mod_mult. Qed.

Lemma Zpower_div b : forall n, 0 < b -> O <> n -> b ^^ n / b = b ^^ (n - 1).
Proof.
move=> [|n] //= Hb _. rewrite mulZC subSS subn0 Z_div_mult_full //. omega.
Qed.

Lemma id_rem_minus a b : (a - b) ^^ 2 = a ^^ 2 + b ^^ 2 - 2 * a * b.
Proof. rewrite -Zpower_b_square mulZBr 2!mulZBl 2!Zpower_b_square; ring. Qed.

Lemma id_rem_plus a b : (a + b) ^^ 2 = a ^^ 2 + b ^^ 2 + 2 * a * b.
Proof.
rewrite -Zpower_b_square mulZDr 2!mulZDl 2!Zpower_b_square; ring.
Qed.

Lemma Zpower_Zmult : forall n a b, (a * b) ^^ n = a ^^ n * b ^^ n.
Proof. elim=> // n IH a b /=. rewrite !IH; ring. Qed.

Lemma Zmod_2_Zeven : forall z, z mod 2 = 0 -> Zeven z.
Proof.
move=> z.
move/Zmod_divide => H.
lapply H; last done.
move=> {H}.
destruct 1.
rewrite H.
exact: Zeven_mult_Zeven_r.
Qed.

Lemma not_Zmod_2_Zodd z : z mod 2 <> 0 -> Zodd z.
Proof.
move=> Hz.
case: (Zeven_odd_dec z) => //.
case/Zeven_ex=> z' Hz'; subst z.
by rewrite mulZC Z_mod_mult in Hz.
Qed.

Lemma Zeven_2 : forall m, Zeven (2 * m). Proof. by case. Qed.

Lemma Zodd_1 : forall m, Zodd (2 * m + 1). Proof. elim => //. by case. Qed.

Lemma Zodd_opp : forall z, Zodd z -> Zodd (- z). Proof. by case. Qed.

Lemma Zeven_opp : forall z, Zeven z -> Zeven (- z). Proof. by case. Qed.

Lemma Zeven_opp_inv : forall z, Zeven (- z) -> Zeven z. Proof. by case. Qed.

Lemma Zodd_Zdivide_2 : forall m, Zodd m -> ~ (2 | m ).
Proof.
move=> m Hm [k Hk]; subst m.
apply Zodd_not_Zeven in Hm.
apply Hm.
by rewrite mulZC; apply Zeven_2.
Qed.

Lemma ZevenP z : ssrbool.reflect (Zeven z) (Z.even z).
Proof.
apply: (iffP idP).
destruct z => //=; by destruct p.
destruct z => //=; by destruct p.
Qed.

Arguments ZevenP [z].
Prenex Implicits ZevenP.

Definition Zodd_bool z := ~~ Z.even z.

Lemma Zodd_mult_inv : forall a b, Zodd (a * b) -> Zodd a /\ Zodd b.
Proof.
move=> a b H; case : (Zeven_odd_dec a) => Ha.
by move/Zeven_not_Zodd : (Zeven_mult_Zeven_l a b Ha).
case: (Zeven_odd_dec b) => [ Hb | // ].
move/Zeven_not_Zodd : (Zeven_mult_Zeven_l b a Hb).
by rewrite mulZC.
Qed.

Lemma ZoddP : forall z, Zodd z <-> Zodd_bool z.
Proof. rewrite /Zodd_bool; case => //=; by case=> [p|p|]. Qed.

Lemma Zeven_Zmod_2 z : Zeven z -> z mod 2 = 0.
Proof. case/Zeven_ex => z' ->; by rewrite mulZC Z_mod_mult. Qed.

Lemma Zodd_Zmod_2 z : Zodd z -> z mod 2 = 1.
Proof.
case/Zodd_ex => z' ->.
rewrite addZC mulZC; by apply Z_mod_plus_full.
Qed.

Lemma Zeven_plus_inv : forall a b, Zeven (a + b) ->
  (Zeven a /\ Zeven b) \/ (Zodd a /\ Zodd b).
Proof.
move=> a b H.
case: (Zeven_odd_dec a) => Ha.
case: (Zeven_odd_dec b) => Hb.
tauto.
move/Zodd_not_Zeven: (Zodd_plus_Zeven _ _ Hb Ha).
by rewrite addZC.
case: (Zeven_odd_dec b) => Hb; last tauto.
by move/Zodd_not_Zeven : (Zodd_plus_Zeven _ _ Ha Hb).
Qed.

Lemma Zmult_2_Zeven a b : a = 2 * b -> Zeven a.
Proof. move=> ->;  by apply Zeven_2. Qed.

Lemma Zeven_mult_inv a b : Zeven (a * b) -> Zeven a \/ Zeven b.
Proof.
case: (Zeven_odd_dec a) => X; first by auto.
case: (Zeven_odd_dec b) => Y; first by auto.
by move/Zodd_not_Zeven : (Zodd_mult_Zodd _ _ X Y).
Qed.

Lemma Zodd_plus_inv : forall a b, Zodd (a + b) -> (Zodd a /\ Zeven b) \/ (Zeven a /\ Zodd b).
Proof.
move=> a b H.
case: (Zeven_odd_dec a) => Ha; case: (Zeven_odd_dec b) => Hb.
by move/Zeven_not_Zodd : (Zeven_plus_Zeven _ _ Ha Hb).
tauto.
tauto.
by move/Zeven_not_Zodd: (Zodd_plus_Zodd _ _ Ha Hb).
Qed.

Lemma Zodd_bool_Zplus a b : Z.even b -> Zodd_bool (a + b) = Zodd_bool a.
Proof.
move/ZevenP => H.
move H' : (Zodd_bool (a + b)) => c.
destruct c.
- move/ZoddP in H'.
  apply/esym/ZoddP.
  case/Zodd_plus_inv : H'; first tauto.
  case=> _.
  by move/Zeven_not_Zodd.
- move/negP in H'.
  apply/esym/negP.
  contradict H'.
  contradict H'.
  move/ZevenP in H'.
  apply/ZevenP.
  case/Zeven_plus_inv : H' => H'; first tauto.
  case : H' => _.
  by move/Zodd_not_Zeven.
Qed.

Lemma Zeven_bool_S z : Z.even (z + 1) = ~~ Z.even z.
Proof.
case/boolP : (Z.even z) => Z.
by rewrite Z.even_add /= Z.
by rewrite Z.even_add /= (negbTE Z).
Qed.

Lemma Zeven_power : forall m, Zeven (2 ^^ m.+1).
Proof. elim=> // n H. rewrite ZpowerS (Zeven_div2 _ H). by apply Zeven_2. Qed.

Lemma Zeven_power' : forall m, (0 < m)%nat -> Zeven (2 ^^ m).
Proof. case => // => n _; by apply Zeven_power. Qed.

Lemma Zodd_bool_Zplus_Zpower n (z : Z) b k : (0 < n)%nat -> (0 < k)%nat ->
  Zodd_bool (z + (2 ^^ (k * n)) * b) = Zodd_bool z.
Proof.
move=> Hn Hk.
rewrite Zodd_bool_Zplus //.
apply/ZevenP/Zeven_mult_Zeven_l.
destruct n; first by inversion Hn.
destruct k; first by inversion Hk.
apply/Zeven_power'; by rewrite muln_gt0.
Qed.

Lemma Zpower_Zdivide : forall n d1 d2, d1 >= 0 -> 2 ^^ n = d1 * d2 ->
  exists p, exists q, d1 = 2 ^^ p /\ d2 = 2 ^^ q.
Proof.
elim => [d1 d2 Hd1 /= H | n IH d1 d2 Hd1].
- symmetry in H.
  case: (Zmult_1_inversion_l _ _ H) => H1.
  + subst d1.
    rewrite mul1Z in H.
    subst d2.
    by exists O, O.
  + subst d1.
    suff : ~ (-1 >= 0) by contradiction.
    omega.
- rewrite ZpowerS mulZC => H.
  symmetry in H.
  move: (Zdivide_intro _ _ _ H) => H'.
  case: {H'}(prime_mult _ prime_2 _ _ H') => H'.
  - inversion H' as [kd1 Hkd1]; clear H'.
    have X : 2 ^^ n = kd1 * d2.
      rewrite Hkd1 (mulZC kd1) (mulZC (2 ^^ n)) -mulZA in H.
      by apply eqZ_mul2l in H.
    apply IH in X; last omega.
    case: X => [p [q [H1 H2]]].
    exists p.+1, q; by rewrite ZpowerS Hkd1 H1 mulZC.
  - inversion H' as [kd2 Hkd2]; clear H'.
    have X : 2 ^^ n = d1 * kd2.
      rewrite Hkd2 mulZA in H.
      by apply eqZ_mul2r in H.
    apply IH in X; last omega.
    case: X => [p [q [H1 H2]]].
    exists p, q.+1; by rewrite ZpowerS Hkd2 H2 mulZC.
Qed.

Definition Zmax_seq l := foldl (fun e a => Z.max e a) 0 l.

Lemma Zis_gcd_eq : forall n m, 0 <= n -> Zis_gcd n n m -> n = m \/ n = - m.
Proof.
move=> n m H [H1 [q H2]].
move/(_ n (Z.divide_refl _) (Z.divide_refl _)) => X.
exact: Z.divide_antisym.
Qed.

Lemma Zis_gcd_Zpower_odd : forall n m, Zodd m -> Zis_gcd (2 ^^ n) m 1.
Proof.
move=> n m Hm; constructor.
by apply Zone_divide.
by apply Zone_divide.
move=> d [dpower Hdpower] [dm Hdm].
have [k Hk] : exists k, 1 = k * d.
  have [X|X] : dpower >= 0 \/ dpower < 0 by omega.
  - case: (Zpower_Zdivide _ _ _ X Hdpower) => p [q [H1 H2]].
    case: (leqP q 0) => [|Hq].
    + rewrite leqn0 => /eqP Hq; subst q.
      rewrite /= in H2.
      subst d.
      by exists 1.
    + have Habsurd : (2 | m).
        subst d.
        destruct q.
        * by inversion Hq.
        * exists (dm * 2 ^^ q).
          rewrite Hdm ZpowerS; ring.
      by apply Zodd_Zdivide_2 in Hm.
  - have Y : d < 0.
      destruct d => //.
      * rewrite mulZ0 in Hdpower.
        move: (expZ_gt0 n) => ?; omega.
      * move: (expZ_gt0 n) => Y.
        rewrite Hdpower in Y.
        apply Zmult_gt_0_lt_0_reg_r in Y => //.
        omega.
    have Hdpower' : 2 ^^ n = -dpower * (-d) by rewrite mulZNN.
    have X' : (-dpower) >= 0 by omega.
    case: (Zpower_Zdivide _ _ _ X' Hdpower') => p [q [H1 H2]].
    case: (leqP q 0) => [|Hq].
    + rewrite leqn0 => /eqP Hq; subst q.
      rewrite /= in H2.
      by exists (-1).
      have Habsurd : (2 | m).
        have Hdm' : m = (-dm) * (-d) by rewrite mulZNN.
        rewrite H2 in Hdm'.
        destruct q.
        * by inversion Hq.
        * exists (-(dm * 2 ^^ q)).
          rewrite Hdm' ZpowerS; ring.
      by apply Zodd_Zdivide_2 in Hm.
    by exists k.
Qed.

Lemma Zis_gcd_even a b g : Zeven a -> Zeven b ->
  Zis_gcd a b (2 * g) -> Zis_gcd (a / 2) (b / 2) g.
Proof.
case/Zeven_ex => qa Ha; subst a.
case/Zeven_ex => qb Hb; subst b => Hgcd.
rewrite (mulZC 2 qa) (mulZC 2 qb) !Z_div_mult //.
case: Hgcd; move=> [a Ha] [b Hb] Hgcd.
rewrite (mulZC a) -mulZA in Ha.
apply eqZ_mul2l in Ha => //.
rewrite (mulZC b) -mulZA in Hb.
apply eqZ_mul2l in Hb => //.
apply Zis_gcd_intro.
- rewrite Ha; exact: Zdivide_factor_r.
- rewrite Hb; exact: Zdivide_factor_r.
- move=> x [qqa Hqa] [qqb Hqb]; subst qa qb.
  have [qq Hqq] : (2 * x | 2 * g).
    by apply Hgcd; apply Zmult_divide_compat_l; eapply Zdivide_intro; eauto.
  rewrite (mulZC qq) -mulZA in Hqq.
  apply eqZ_mul2l in Hqq => //.
  apply Zdivide_intro with qq.
  by rewrite mulZC.
Qed.

(* NB : lemma Zis_gcd_even_odd in the standard library is for Zpos/Zneg *)
Lemma Zis_gcd_even_odd_new a b g :
  Zis_gcd a (2 * b + 1) g -> Zis_gcd (2 * a) (2 * b + 1) g.
Proof.
case=> Ha Hb Hgcd.
apply Zis_gcd_intro => //.
by apply Zdivide_mult_r.
move=> x Hxa Hxb.
apply Hgcd => //.
have : rel_prime x 2.
  apply bezout_rel_prime.
  case: Hxb => xb Hxb.
  apply Bezout_intro with xb (-b).
  rewrite -Hxb; ring.
by apply Gauss.
Qed.

Lemma Zgcd_0_R : forall a, 0 <= a -> gcdZ a 0 = a.
Proof. move=> a Ha. apply Zis_gcd_gcd => //. exact/Zis_gcd_0. Qed.

Lemma Zgcd_same : forall a, 0 <= a -> gcdZ a a = a.
Proof. move=> a Ha. apply Zis_gcd_gcd => //. exact/Zis_gcd_refl. Qed.

Lemma Zgcd_sym a b : gcdZ a b = gcdZ b a.
Proof.
apply Zis_gcd_gcd; by [apply Zgcd_is_pos | apply Zis_gcd_sym, Zgcd_is_gcd].
Qed.

Lemma Zgcd_opp a b : gcdZ a (-b) = gcdZ a b.
Proof.
move: (Zis_gcd_minus a (-b) (gcdZ a b)).
rewrite oppZK => X.
rewrite Zgcd_sym; apply Zis_gcd_gcd; [exact/Zgcd_is_pos | exact/X/Zgcd_is_gcd].
Qed.

Lemma Zgcd_even a b : Zeven a -> Zeven b -> gcdZ a b = 2 * gcdZ (a / 2) (b / 2).
Proof.
move=> Ha Hb; apply Zis_gcd_gcd.
- apply mulZ_ge0 => //; exact: Zgcd_is_pos.
- case/Zeven_ex: Ha => qa Ha; subst a.
  case/Zeven_ex: Hb => qb Hb; subst b.
  rewrite {2}(mulZC 2 qa) {2}(mulZC 2 qb) !Z_div_mult //.
  exact/Zis_gcd_mult/Zgcd_is_gcd.
Qed.

Lemma Zgcd_mult a b k : 0 <= k -> gcdZ (k * a)  (k * b) = k * gcdZ a b.
Proof.
move=> Hk.
apply Zis_gcd_gcd => //; last exact/Zis_gcd_mult/Zgcd_is_gcd.
apply mulZ_ge0 => //; exact: Zgcd_is_pos.
Qed.

Lemma Zgcd_even_odd : forall a b, Zeven a -> Zodd b -> gcdZ a b = gcdZ (a / 2) b.
Proof.
move=> a b Ha Hb; apply Zis_gcd_gcd; first by apply Zgcd_is_pos.
case/Zeven_ex: Ha => qa Ha; subst a.
case/Zodd_ex: Hb => qb Hb; subst b.
rewrite {2}(mulZC 2) Z_div_mult_full //; by apply Zis_gcd_even_odd_new, Zgcd_is_gcd.
Qed.

Lemma Zgcd_Zpower_odd : forall k a b, Zodd b -> gcdZ (a * 2 ^^ k) b = gcdZ a b.
Proof.
elim=> [a b Hb /=|n IH a b Hb]; first by rewrite mulZ1.
rewrite ZpowerS (mulZC 2) mulZA Zgcd_even_odd //.
by rewrite Z_div_mult_full // IH.
by apply Zeven_mult_Zeven_r.
Qed.

Lemma Zgcd_for_euclid a b q : gcdZ (a + q * b) b = gcdZ a b.
Proof.
move: (Zis_gcd_for_euclid2 b (gcdZ a b) q a) => X.
apply Zis_gcd_gcd; first exact: Zgcd_is_pos.
rewrite addZC mulZC; exact/Zis_gcd_sym/X/Zgcd_is_gcd.
Qed.

Definition Zbeta' e := 2 ^^ (e * 32).
Definition Zbeta := nosimpl Zbeta'.
Notation "\B^ n" := (Zbeta n) (at level 4, format "\B^ n") : zarith_ext_scope.

Lemma ZbetaE e : \B^ e = 2 ^^ (e * 32). Proof. by []. Qed.

Lemma Zbeta1E : \B^ 1 = 2 ^^ 32. Proof. by []. Qed.

Lemma Zbeta2E : \B^ 2 = 2 ^^ 64 . Proof. by []. Qed.

Lemma ZbetaD n m : Zbeta (n + m) = Zbeta n * Zbeta m.
Proof. by rewrite ZbetaE mulnDl ZpowerD. Qed.

Lemma Zbeta_S n : \B^n.+1 = \B^1 * \B^n.
Proof. by rewrite -ZbetaD. Qed.

Lemma Zbeta_gt0 l : 0 < \B^l. Proof. exact: expZ_gt0. Qed.

Lemma Zbeta_ge0 n : 0 <= \B^n. Proof. exact: expZ_ge0. Qed.
Hint Resolve Zbeta_ge0.

Lemma Zbeta_ge1 l : 1 <= \B^l. Proof. exact: expZ_ge1. Qed.

Lemma Zbeta_lt m n : (m < n)%nat -> \B^ m < \B^ n.
Proof. move=> H; rewrite /Zbeta; apply expZ_2_lt => //; by rewrite ltn_mul2r. Qed.

Lemma Zbeta_le m n : (m <= n)%nat -> \B^m <= \B^n.
Proof. by move=> H; apply/leZP; rewrite /Zbeta Zpower_2_le // leq_pmul2r. Qed.

Lemma Zpower_shift_2 n : 4 * n < \B^1 -> n < 2 ^^ 30.
Proof.
rewrite Zbeta1E.
have -> : (32 = 2 + 30)%nat by [].
rewrite ZpowerD [Zmult]lock /= -lock; omega.
Qed.

Lemma Zbeta1_1 a : ~ a * \B^1 = 1.
Proof.
move=> H.
move: (Ztrichotomy a 0) => [X | [X | X]].
- by destruct a.
- by rewrite X in H.
- suff H' : 1 < a * \B^1 by omega.
  apply (@leZ_ltZ_trans (a * 1)).
  + rewrite mulZ1; omega.
  + apply ltZ_pmul2l => //; exact: Z.gt_lt.
Qed.

Lemma inv_mod_beta0 m : 1 * m + 0 * \B^1 = m. Proof. ring. Qed.
Lemma inv_mod_beta1 m : 0 * m + 1 * \B^1 = \B^1. Proof. ring. Qed.
Lemma inv_mod_beta2 : forall m d, Zis_gcd m (\B^1) d -> Zis_gcd m (\B^1) d.
Proof. done. Qed.

Definition inv_mod_beta m :=
  match euclid_rec m \B^1 \B^1 (Zbeta_ge0 1) 1 0 m 0 1
        (inv_mod_beta0 m) (inv_mod_beta1 m) (inv_mod_beta2 m) with
    Euclid_intro u _ d _ _ =>
    if d <=? 0 then u mod (\B^1) else
      if u == 0 then 0 else
        - (u mod (\B^1)) + \B^1
  end.

Definition eqmod (a b m : Z) := exists k : Z, a = b + k * m.

Notation "a =m b {{ m }}" := (eqmod a b m) (at level 80) : eqmod_scope.
Local Open Scope eqmod_scope.

Lemma eqmod_Zmod a b m : 0 < m -> (a =m b {{ m }} <-> a mod m = b mod m).
Proof.
move=> Hm; split.
- move=> [k' ->]; by rewrite Z_mod_plus_full.
- move=> H.
  rewrite (Z_div_mod_eq a m (Z.lt_gt _ _ Hm)) (Z_div_mod_eq b m (Z.lt_gt _ _ Hm)) H.
  exists ((a / m) - (b / m)); ring.
Qed.

Lemma eqmod_Zmod2 a b m : 0 <= m -> (a =m b {{ m }} -> a mod m = b mod m).
Proof. move=> Hm [k' ->]; by rewrite Z_mod_plus_full. Qed.

Lemma eqmod_refl : forall a m, a =m a {{ m }}. Proof. exists 0 => /=; ring. Qed.

Lemma eqmod_sym a b m : a =m b {{ m }} -> b =m a {{ m }}.
Proof. move=> [k ->]; exists (- k); ring. Qed.

Lemma eqmod_trans a b c m : a =m b {{ m }} -> b =m c {{ m }} -> a =m c {{ m }}.
Proof.
rewrite /eqmod; move=> [kab Hab] [kbc Hbc].
exists (kab + kbc); rewrite Hab Hbc; ring.
Qed.

Lemma eqmod_compat_plus_R a b c m : a =m c {{ m }} -> a + b =m c + b {{ m }}.
Proof. move=> [kac Hac]. exists kac. rewrite Hac; ring. Qed.

Lemma eqmod_div k m a b : a =m b {{ k * m }} -> a =m b {{ m }}.
Proof. move=> [x Hx]; exists (x * k); rewrite Hx; ring. Qed.

(* TODO: change *)
Lemma eqmod_reg_mult a b d m : a =m b {{ m }} -> a * d =m b * d {{ m }}.
Proof. move=> [k' ->]. exists (k' * d); ring. Qed.

(* TODO: change *)
Lemma eqmod_reg_mult_l a b d m : a =m b {{ m }} -> d * a =m d * b {{ m }}.
Proof. move=> [k' ->]. exists (k' * d); ring. Qed.

Lemma eqmod_rewrite m a a' b c : a =m a' {{ m }} ->
  a * b =m c {{ m }} -> a' * b =m c {{ m }}.
Proof.
move=> [ka Hka] [kab Hkab].
rewrite Hka {Hka} in Hkab.
ring_simplify in Hkab.
exists (kab - ka * b).
apply Zplus_minus_eq in Hkab.
rewrite Hkab; ring.
Qed.

Lemma eqmod_reg_mult' a b d m : Zis_gcd m d 1 ->
  a * d =m b * d {{ m }} -> a =m b {{ m }}.
Proof.
move=> Hgcd H.
move: (euclid m d).
inversion 1 as [m' d' gcd Hdd' Hgcd'].
case: {Hgcd Hgcd'}(Zis_gcd_uniqueness_apart_sign _ _ _ _ Hgcd Hgcd') => Hinv; subst gcd.
- have Hinv' : d * d' =m 1 {{ m }}.
    exists (-m'); rewrite Hinv; ring.
  move: {H}(eqmod_reg_mult _ _ d' _ H) => H.
  rewrite -mulZA mulZC in H.
  move: {H}(eqmod_rewrite _ _ _ _ _ Hinv' H).
  rewrite mul1Z.
  move/eqmod_sym.
  rewrite -mulZA mulZC => H.
  move/(eqmod_rewrite _ _ _ _ _ Hinv') : H => H.
  rewrite mul1Z in H.
  by apply eqmod_sym.
- have Hinv' : d * d' =m -1 {{ m }}.
    exists (- m').
    have X : 1 + d * d' = - m' * m by rewrite Hinv; ring.
    omega.
  move: {H}(eqmod_reg_mult _ _ d' _ H) => H.
  rewrite -mulZA mulZC in H.
  move: {H}(eqmod_rewrite _ _ _ _ _ Hinv' H) => H.
  apply eqmod_sym in H.
  rewrite -mulZA mulZC in H.
  move: {H}(eqmod_rewrite _ _ _ _ _ Hinv' H) => [k H].
  exists k.
  have -> : k * m = -1 * b + 1 * a by omega.
  ring.
Qed.

Lemma eqmod_reg_mult_beta_odd a b k m : Zodd m ->
  \B^k * a =m \B^k * b {{ m }} -> a =m b {{ m }}.
Proof.
move=> Hm.
rewrite mulZC.
move/eqmod_sym.
rewrite mulZC => H.
apply eqmod_reg_mult' in H.
apply eqmod_sym => //.
rewrite ZbetaE; exact/Zis_gcd_sym/Zis_gcd_Zpower_odd.
Qed.

Lemma eqmod_minmod m a b k : a =m b {{ m }} -> a - k * m =m b {{ m }}.
Proof. move=> [k' H]. exists (k' - k); rewrite H; ring. Qed.

Lemma eqmod_mod m a b : 0 < m -> a =m b {{ m }} -> a =m b mod m {{ m }}.
Proof. move=> Hm => /eqmod_Zmod; rewrite eqmod_Zmod // Zmod_mod; by auto. Qed.

Lemma eqmod_inv a a' m : 0 <= a < m -> 0 <= a' < m -> a =m a' {{ m }} -> a = a'.
Proof.
move=> [Ham1 Ham2] [Ha'm1 Ha'm2] [[|p|p] H].
- by rewrite mul0Z addZ0 in H.
- suff ? : m <= a by omega.
  rewrite H -{1}(add0Z m).
  apply leZ_add => //.
  rewrite -{1}(mul1Z m).
  apply leZ_pmul2r => //; [omega | by destruct p].
- suff ? : a < 0 by omega.
  rewrite H.
  have : forall a b, a < -b -> a + b < 0 by move=> ? ?; omega.
  apply.
  rewrite -mulNZ Zopp_neg.
  apply (@ltZ_leZ_trans m) => //.
  rewrite -{1}(mul1Z m).
  apply leZ_wpmul2r; [omega | by destruct p].
Qed.

Local Close Scope eqmod_scope.
Local Close Scope zarith_ext_scope.

Fixpoint isum n := if n is n'.+1 then ((isum n') + n'.+1)%nat else O.

Definition Zisum z := if z is Zpos p then Z_of_nat (isum (nat_of_P p)) else 0.

Lemma Zisum_prop : forall a, 0 <= a -> Zisum (a + 1) = Zisum a + (a + 1).
Proof.
case=> // p _ /=.
rewrite nat_of_P_plus_morphism plus_comm /=.
by rewrite inj_plus /= Pos2SuccNat.id_succ -Pos.add_1_r.
Qed.

Definition Zfact (z : Z) : Z :=
  match z with
    | Zpos p => Z_of_nat (fact (nat_of_P p))
    | _ => 1
  end.

Lemma Zfact_neg : forall z, z < 0 -> Zfact z = 1.
Proof. by destruct z. Qed.

Lemma fact_lemma : forall n, (0 < n)%nat -> (fact n = n * fact (n - 1))%nat.
Proof.
elim=> //; case=> [ // |n] IH _.
by rewrite subSS subn0 IH //= subSS subn0 !mulnE.
Qed.

Lemma Zfact_pos : forall z, z > 0 -> Zfact z = z * Zfact (z - 1).
Proof.
case => // p Hp.
rewrite [X in X = _]/=.
rewrite fact_lemma; last by apply/ltP/Pos2Nat.is_pos.
rewrite inj_mult positive_nat_Z.
f_equal.
destruct p => //.
  rewrite (_ : Z.pos p~1 - 1 = Z.pos p~0) //=.
  do 2 f_equal.
  by rewrite Pos2Nat.inj_xO Pos2Nat.inj_xI subSS subn0.
rewrite /=.
do 2 f_equal.
by rewrite -Pos.succ_pred_double Pos2Nat.inj_succ subSS subn0.
Qed.

Local Open Scope zarith_ext_scope.

Fixpoint bbs_fun_rec (n : nat) (seed m : Z) {struct n} : seq bool :=
  match n with
    | O => nil
    | n.+1 => (Zodd_bool seed) :: (bbs_fun_rec n (seed ^^ 2 mod m) m)
  end.

Definition bbs_fun (len:nat)(seed m:Z) : seq bool :=
  bbs_fun_rec len ((seed * seed) mod m) m.

Lemma bbs_fun_rec_cat0 : forall n seed modu,
  bbs_fun_rec n.+1 (seed mod modu) modu =
  bbs_fun_rec n (seed mod modu) modu ++
  bbs_fun_rec 1 ((seed mod modu)^^(2 ^ n) mod modu) modu.
Proof.
elim => [seed modu | n0 IHn0 seed modu].
- by rewrite /= mulZ1 Zmod_mod.
- by rewrite [n0.+1]lock /= -lock IHn0 /= mulZ1 expnS
    {2}Zpower_b_square (Zpower_exp_mod (2 ^ n0) 2 (seed mod modu) modu).
Qed.

Lemma bbs_fun_rec_cat0' : forall n seed modu,
  bbs_fun_rec n.+1 (seed mod modu) modu =
  bbs_fun_rec 1 (seed mod modu) modu ++
  bbs_fun_rec n ((seed mod modu)^^2 mod modu) modu.
Proof. by elim. Qed.

Lemma bbs_fun_rec_cat1 : forall n k seed modu,
  bbs_fun_rec (n + k) (seed mod modu) modu =
  bbs_fun_rec n (seed mod modu) modu ++
  bbs_fun_rec k ((seed mod modu) ^^ (2 ^ n) mod modu) modu.
Proof.
elim => [k seed modu | n0 IHn0 k seed modu].
- by rewrite /= mulZ1 Zmod_mod.
- by rewrite addSnnS IHn0 -{1}(addn1 n0) IHn0 -catA
   bbs_fun_rec_cat0' Zpower_exp_mod expnS mulnC.
Qed.

Lemma bbs_fun_rec_cat : forall k n seed modu,
  bbs_fun_rec (k * n.+1) (seed mod modu) modu =
  bbs_fun_rec (k * n) (seed mod modu) modu ++
  bbs_fun_rec k ((seed mod modu)^^(2 ^ (k * n)) mod modu) modu.
Proof.
elim=> // k IHk n0 seed modu.
have -> : (k.+1 * n0.+1 = k.+1 * n0 + k.+1)%nat by rewrite mulnS addnC.
by rewrite bbs_fun_rec_cat1.
Qed.

Ltac strip_Z_of_nat_from_hypo :=
  match goal with
  | H : (?x1 = ?x2)%Z |- _ => generalize (Z_of_nat_inj _ _ H); intros
  | H : (?x1 > ?x2)%Z |- _ => generalize (proj2 (Nat2Z.inj_gt _ _) H); intros
  | H : (?x1 < ?x2)%Z |- _ => generalize (proj2 (Nat2Z.inj_lt _ _)) H; intros
  | H : (?x1 >= ?x2)%Z |- _ => generalize (proj2 (Nat2Z.inj_ge _ _) H); intros
  | H : (?x1 <= ?x2)%Z |- _ => generalize (proj2 (Nat2Z.inj_le _ _) H); intros
  | |- _ => idtac
  end.

Lemma Z_of_nat_congr: forall x y, x = y -> Z_of_nat x = Z_of_nat y.
Proof. intros x y H; rewrite H; reflexivity. Qed.

Ltac strip_Z_of_nat_from_goal :=
  match goal with
  | |- (Z_of_nat ?x1 = Z_of_nat ?x2)%Z => apply Z_of_nat_congr
  | |- (Z_of_nat ?x1 <= Z_of_nat ?x2)%Z => apply inj_le
  | |- (Z_of_nat ?x1 < Z_of_nat ?x2)%Z => apply inj_lt
  | |- (Z_of_nat ?x1 >= Z_of_nat ?x2)%Z => apply inj_ge
  | |- (Z_of_nat ?x1 < Z_of_nat ?x2)%Z => apply inj_gt
  | |- _ => idtac
  end.

Ltac omegaz_inj_plus_hyp :=
  match goal with
    | H : context [Z_of_nat (plus _ _)] |- _ => rewrite inj_plus in H
    | H : context [Z_of_nat (ssrnat.addn _ _)] |- _ => rewrite inj_plus in H
  end.

Ltac omegaz_inj_plus :=
  match goal with
    | |- context [Z_of_nat (plus _ _)] => rewrite inj_plus
    | |- context [Z_of_nat (ssrnat.addn _ _)] => rewrite inj_plus
  end.
Ltac omegaz_inj_minus_hyp :=
  match goal with
    | id : context [Z_of_nat (minus _ _)] |- _ => rewrite inj_minus1 in id
    | id : context [Z_of_nat (ssrnat.subn _ _)] |- _ => rewrite inj_minus1 in id
  end.
Ltac omegaz_inj_minus :=
  match goal with
    | |- context [Z_of_nat (minus _ _)] => rewrite inj_minus1
    | |- context [Z_of_nat (ssrnat.subn _ _)] => rewrite inj_minus1
  end.
Ltac omegaz_inj_mult_hyp :=
  match goal with
    | id : context [Z_of_nat (mult _ _)] |- _ => rewrite inj_mult in id
    | id : context [Z_of_nat (ssrnat.muln _ _)] |- _ => rewrite inj_mult in id
  end.
Ltac omegaz_inj_mult :=
  match goal with
    | |- context [Z_of_nat (mult _ _)] => rewrite inj_mult
    | |- context [Z_of_nat (ssrnat.muln _ _)] => rewrite inj_mult
  end.

Ltac simpl_Z_of_nat_cst :=
  match goal with
    | |- context [Z_of_nat O] => simpl (Z_of_nat O)
    | |- context [Z_of_nat (S O)] => rewrite [Z_of_nat (S O)]/=
    | |- context [Z_of_nat (S (S O))] => rewrite [Z_of_nat (S (S O))]/=
    | |- context [Z_of_nat (S (S (S O)))] => rewrite [Z_of_nat (S (S (S O)))]/=
    | |- context [Z_of_nat (S (S (S (S O))))] => rewrite [Z_of_nat (S (S (S (S O))))]/=
    | |- context [Z_of_nat (S ?x)] => rewrite (Z_S x)
  end.

Ltac simpl_Z_of_nat_cst_hyp :=
  match goal with
    | H : context [Z_of_nat O] |- _ => simpl (Z_of_nat O) in H
    | H : context [Z_of_nat (S O)] |- _ => rewrite [Z_of_nat (S O)]/= in H
    | H : context [Z_of_nat (S (S O))] |- _ => rewrite [Z_of_nat (S (S O))]/= in H
    | H : context [Z_of_nat (S (S (S O)))] |- _ => rewrite [Z_of_nat (S (S (S O)))]/= in H
    | H : context [Z_of_nat (S (S (S (S O))))4] |- _ => rewrite [Z_of_nat (S (S (S (S O))))]/= in H
    | H : context [Z_of_nat (S ?x)] |- _ => rewrite (Z_S x) in H
  end.

Ltac Zabs_nat_tac_hyp :=
  match goal with
    | H : context [Z.abs_nat (Z_of_nat ?n)] |- _ => rewrite (Zabs_nat_Z_of_nat n) in H
    | H : context [Z.abs_nat 1%Z] |- _ => rewrite (_ : Z.abs_nat 1%Z = 1%nat) in H; last by []
  end.
Ltac Zabs_nat_tac :=
  match goal with
    | |- context [Z.abs_nat (Z_of_nat ?n)] => rewrite (Zabs_nat_Z_of_nat n)
    | |- context [Z.abs_nat 1%Z] => rewrite (_ : Z.abs_nat 1%Z = 1%nat); last by []
  end.

Ltac omegaz_hyp :=
  repeat omegaz_inj_plus_hyp ;
  repeat omegaz_inj_minus_hyp ;
  repeat omegaz_inj_mult_hyp ;
  repeat simpl_Z_of_nat_cst_hyp ;
  repeat strip_Z_of_nat_from_hypo.

Ltac omegaz_goal :=
  repeat omegaz_inj_plus ;
  repeat omegaz_inj_minus ;
  repeat omegaz_inj_mult ;
  repeat simpl_Z_of_nat_cst ;
  repeat strip_Z_of_nat_from_goal.

Ltac omegaz' ome :=
  repeat omegaz_hyp ;
  repeat omegaz_goal ;
  ome.

(* extension of omega to handle goals/hypos that contains Z_of_nat *)
Ltac omegaz := omegaz' omega.

Goal forall x y,
  ((Z_of_nat x) + 4%Z - 2%Z > (Z_of_nat (y +4)))%Z ->
  ((Z_of_nat (x + 2)) + 2%Z >= (Z_of_nat y) + 6%Z)%Z.
Proof.
intros.
omegaz.
Abort.

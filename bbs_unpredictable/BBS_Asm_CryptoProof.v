(** This file contains the proof of unpredictability of the implementation in Assembly of
    the Blum-Blum-Shub (BBS) pseudorandom bit generator. Security is based on the intractability
    of the quadratic residuosity problem.
  *)

Require Import Euclid List Znumtheory Zpow_facts Rbase.
From mathcomp Require Import ssreflect ssrbool.
Require Import ZArith_ext.
Require Import listbit.
Add LoadPath "./toolbox".
Require MiscLists BBS.
Add LoadPath "../cryptoasm".
Require bbs_encode_decode.

Local Close Scope Z_scope.

Lemma euclid_unique : forall m n q r q' r',
  0 < n -> m = q * n + r -> m = q' * n + r' -> n > r -> n > r' -> q = q' /\ r = r'.
Proof.
intros m n q r q' r' Hn Hq Hq' Hr Hr'.
suff H : Z_of_nat q = Z_of_nat q' /\ Z_of_nat r = Z_of_nat r' by omega.
apply Zdiv_mod_unique with (Z_of_nat n).
- rewrite Zabs_eq; omega.
- rewrite Zabs_eq; omega.
- rewrite mult_comm in Hq.
  rewrite mult_comm in Hq'.
  rewrite -2!inj_mult -2!inj_plus; congruence.
Qed.

Definition ceiling_div (m n : nat) (H : 0 < n) :=
  if eq_nat_dec (proj1_sig (modulo n H m)) O then
    proj1_sig (quotient n H m)
  else
    S (proj1_sig (quotient n H m)).

Lemma lt_0_ceiling_div : forall m n, 0 < m ->
  forall H : 0 < n, 0 < ceiling_div m n H.
Proof.
rewrite /ceiling_div => m n Hm Hn.
destruct (modulo n Hn m) as [r [q [H1 H2]]] => /=.
destruct (quotient n Hn m) as [q' [r' [H3 H4]]] => /=.
destruct (eq_nat_dec r 0) as [H5 | H5] => /=.
- apply neq_O_lt => Hq.
  subst.
  rewrite /= in Hm; rewrite /= plus_0_r in H1.
  destruct q.
  + omega.
  + induction q as [| q IH].
    * omega.
    * apply IH.
      rewrite /= in H1 *.
      by intuition.
- omega.
Qed.

Lemma le_mult_ceiling_div : forall m n (H:0<n), m <= n * ceiling_div m n H.
Proof.
rewrite /ceiling_div => m n Hn.
destruct (modulo n Hn m) as [r [q [H1 H2]]] => /=.
destruct (quotient n Hn m) as [q' [r' [H3 H4]]] => /=.
have {H3 H4}[H5 H6] : q = q' /\ r = r' by apply euclid_unique with m n.
subst q' r'.
destruct (eq_nat_dec r 0) as [H3 | H3] => /=.
- subst r m.
  by rewrite plus_0_r mult_comm.
- subst m.
  rewrite (mult_comm n) /=; omega.
Qed.

Local Open Scope Z_scope.

Lemma Zmult_le_lt : forall m n p, 1 < m -> 0 < n -> m * n <= p -> n < p.
Proof.
intros m n p Hm Hn H.
apply Zmult_lt_reg_r with m.
- omega.
- rewrite Zmult_comm in H.
  apply Zle_lt_trans with p => //.
  rewrite -{1}(Zmult_1_r p).
  apply Zmult_lt_compat_l => //.
  have H0 : (0 < n * m) by apply Zmult_lt_0_compat => //; omega.
  omega.
Qed.

Lemma lt_0_N_digits : forall n, 1 < n -> 0 < N_digits n.
Proof. elim => //; case=> [p|p|] Hp //=; by apply Zle_lt_succ, log_inf_correct1. Qed.

Local Open Scope zarith_ext_scope.

(** We show that the restrictions are decidable. *)

Lemma Restrictions_dec : forall nn nk modu seed,
  {bbs_encode_decode.Implem.Restrictions nn nk modu seed} +
  {~ bbs_encode_decode.Implem.Restrictions nn nk modu seed}.
Proof.
intros nn nk modu seed.
unfold bbs_encode_decode.Implem.Restrictions.
destruct (le_lt_dec nk 0) as [H1 | H1]; auto with zarith.
- destruct (Z_lt_dec 0 modu) as [H2 | H2]; auto with zarith.
  destruct (Z_lt_dec modu (ZArith_ext.Zpower 2 (nk * 32))) as [H3 | H3]; auto with zarith.
  destruct (Zodd_dec modu) as [H4 | H4]; try tauto.
  destruct (Z_le_dec 0 seed) as [H5 | H5]; auto with zarith.
  destruct (Z_lt_dec seed modu) as [H6 | H6]; auto with zarith.
  destruct (Z_lt_dec (4 * Z_of_nat (4 * nk + nn + 2)) (2^^32)) as [H7 | H7]; auto with zarith.
  tauto.
- destruct (Z_lt_dec 0 modu) as [H2 | H2]; auto with zarith.
  destruct (Z_lt_dec modu (ZArith_ext.Zpower 2 (nk * 32))) as [H3 | H3]; auto with zarith.
  destruct (Zodd_dec modu) as [H4 | H4]; try tauto.
  destruct (Z_le_dec 0 seed) as [H5 | H5]; auto with zarith.
  destruct (Z_lt_dec seed modu) as [H6 | H6]; auto with zarith.
  destruct (Z_lt_dec (4 * Z_of_nat (4 * nk + nn + 2)) (2^^32)) as [H7 | H7]; auto with zarith.
  tauto.
Qed.

Section BBS.

Variables p q : Z.

Lemma gt_32_0 : (32 > 0)%nat. Proof. omega. Qed.

Lemma tech1 : p * q < 2 ^^ (32 * (ceiling_div (S (Zabs_nat (N_digits (p * q)))) 32 gt_32_0)).
Proof.
unfold ceiling_div.
destruct (modulo 32 gt_32_0 (S (Zabs_nat (N_digits (p * q))))) as [r1 [q1 [H1 H2]]].
destruct (quotient 32 gt_32_0 (S (Zabs_nat (N_digits (p * q))))) as [q2 [r2 [H3 H4]]].
simpl proj1_sig.
have [H5 H6] : q1 = q2 /\ r1 = r2.
  apply euclid_unique with (S (Zabs_nat (N_digits (p * q)))) (32%nat) => //.
  by repeat constructor.
subst q2 r2.
clear H3 H4.
destruct (eq_nat_dec r1 0) as [H | H]; rewrite [mult]lock /= -lock.
- subst r1.
  rewrite plus_0_r mult_comm in H1.
  rewrite -H1.
  destruct (p * q) => //.
  + destruct (log_inf_correct p0) as [H3 [H4 H5] ].
    eapply Zlt_le_trans; first by apply H5.
    rewrite two_p_S //.
    (match goal with |- context [2 ^^ (S ?x)] => replace (S x) with (1 + x)%nat end) ; trivial.
    rewrite Zpower_is_exp.
    simpl Zpower.
    apply Zmult_le_compat_l; last by done.
    rewrite /two_p.
    destruct (log_inf p0) => //.
    - rewrite two_power_pos_correct Zpower_pos_nat Zpower_nat_Zpower
        (Zpos_eq_Z_of_nat_o_nat_of_P p1) Zabs_nat_Z_of_nat.
      by apply Zle_refl.
    - contradict H3; by auto.
  + apply Zle_lt_trans with 0 => //.
    by apply Zpower_0.
- rewrite /N_digits in H1.
  destruct (p * q).
  + by apply Zpower_0.
  + destruct (log_inf_correct2 p0) as [_ Hp0].
    eapply Zlt_trans; first by apply Hp0.
    apply Zle_lt_trans with (Zpower_nat 2 (1 + (Zabs_nat (log_inf p0)))).
    - rewrite two_p_S.
      + rewrite Zpower_nat_is_exp (_ : Zpower_nat 2 1 = 2) //.
        apply Zmult_le_compat_l; last by omega.
        destruct (log_inf p0) => //.
        + rewrite /= two_power_pos_nat two_power_nat_correct; omega.
        + rewrite /= Zpower_nat_Zpower.
          move: (Zpower_0 (nat_of_P p1)) => X; omega.
      + by apply log_inf_correct1.
    - rewrite Zpower_nat_Zpower [plus _ _]/= H1.
      apply expZ_2_lt; omega.
  + apply Zlt_trans with 0 => //.
    by apply Zpower_0.
Qed.

Hypothesis p_prime : prime p.

Hypothesis q_prime : prime q.

Lemma firstn_bbs : forall len1 len2 seed, (len1 <= len2)%nat ->
  firstn len1 (BBS.bbs p q p_prime q_prime len2 seed) = BBS.bbs p q p_prime q_prime len1 seed.
Proof.
rewrite /BBS.bbs /mult.
induction len1 as [|len1 IH] => //.
destruct len2 as [|len2].
+ intros seed H.
  contradict H; omega.
+ intros seed H.
  rewrite MiscLists.firstn_cons IH //; omega.
Qed.

(** [Implem.bbs_fun] and [BBS.bbs] return equal results when the seed [seed] is restricted to
    the multiplicative group pf integers modulo [p*q]. *)

Lemma bbs_fun_bbs : forall len seed,
  bbs_fun len (proj1_sig seed) (p * q) = BBS.bbs p q p_prime q_prime len seed.
Proof.
rewrite /bbs_fun /BBS.bbs.
move=> len [seed Hseed] /=.
move: seed Hseed.
induction len as [ | len IH] => // seed Hseed /=; f_equal.
+ rewrite /Zstar.parity /=.
  case: (Zodd_dec ((seed * seed) mod (p * q))) => H.
  * by apply/Zodd_Zodd_bool.
  * move/Zodd_Zodd_bool : H.
    move/negP.
    by destruct Zodd_bool.
+ rewrite Zmult_1_r.
  erewrite IH; reflexivity.
Qed.

(** The semantics of [bbs_asm]: *)

Require Import Group. (* 8.3 *)

Definition bbs_asm_sem (len : nat) 
  (seed : Zstar.Zstar _ (Zstar.pq_gt_1 _ _ p_prime q_prime) ) : list bool :=
  let nn := ceiling_div len 32 gt_32_0 in
  let nk := ceiling_div (S (Zabs_nat (N_digits (p * q)))) 32 gt_32_0 in
  let modu := p * q in
  let seed' := proj1_sig seed in
  match Restrictions_dec nn nk modu seed' with
  | left H => firstn len 
    (bbs_encode_decode.Implem.decode (proj1_sig (bbs_encode_decode.Implem.exec_bbs_asm nn nk modu seed' H)))
  | right _ => nil
  end.

Hypothesis p_odd : Zodd p.

Hypothesis q_odd : Zodd q.

(** The assembly code [Implem.bbs_asm] implements [BBS.bbs].
    We need a technical lemma [tech1]. *)

Lemma bbs_semop : forall (len : nat) (seed : Zstar.Zstar (p * q) (Zstar.pq_gt_1 p q p_prime q_prime)) final_state,
  let nn := ceiling_div (S len) 32 gt_32_0 in
  let nk := ceiling_div (S (Zabs_nat (N_digits (p * q)))) 32 gt_32_0 in
  let modu := p * q in
  let seed' := proj1_sig seed in
  4 * (Z_of_nat (4 * nk + nn + 2)) < 2^^32 ->
  bbs_encode_decode.Implem.exec_sgoto bbs_encode_decode.Implem.bbs_asm 
    (Some (O, bbs_encode_decode.Implem.encode nn nk seed' modu)) (Some (240%nat, final_state)) ->
  bbs_encode_decode.Implem.decode final_state =
  BBS.bbs _ _ p_prime q_prime (nn * 32) seed.
Proof.
intros len seed final_state nn nk modu seed' Hny Hexec_sgoto.
rewrite (bbs_encode_decode.Implem.bbs_semop nn nk modu seed') //.
- by apply bbs_fun_bbs.
- split.
  apply Zmult_lt_0_compat; [destruct p_prime | destruct q_prime]; omega.
  split.
  rewrite mult_comm.
  by apply tech1.
  split.
  by apply Zodd_mult_Zodd.
  split; rewrite /seed'.
  * destruct seed => /=; omega.
  * split => //.
    rewrite /modu /=.
    destruct seed => /=; omega.
Qed.

Lemma bbs_asm_sem_bbs : forall seed len, 
  let nn := ceiling_div (S len) 32 gt_32_0 in
  let nk := ceiling_div (S (Zabs_nat (N_digits (p * q)))) 32 gt_32_0 in
  4 * Z_of_nat (4 * nk + nn + 2) < 2 ^^ 32 ->
  bbs_asm_sem (S len) seed = BBS.bbs p q p_prime q_prime (S len) seed.
Proof.
move=> seed len nn nk Hny.
rewrite /bbs_asm_sem.
rewrite -/nn -/nk.
case: (Restrictions_dec nn nk (p * q) (proj1_sig seed)) => Hrestr.
- idtac.
  match goal with
    | |- context [bbs_encode_decode.Implem.exec_bbs_asm ?a ?b ?c ?d ?e] =>
      destruct (bbs_encode_decode.Implem.exec_bbs_asm a b c d e) as [final_state [Hfinal_state ?] ]
  end.
  rewrite (bbs_semop len seed) //.
  rewrite mult_comm.
  by apply firstn_bbs, le_mult_ceiling_div.
- contradict Hrestr.
  (* similar as above *)
  split.
  apply Zmult_lt_0_compat; [destruct p_prime | destruct q_prime]; omega.
  split.
  rewrite mult_comm.
  by apply tech1.
  split.
  by apply Zodd_mult_Zodd.
  split.
  * destruct seed => /=; omega.
  * split => //.
    rewrite /=.
    destruct seed => /=; omega.
Qed.

(** Under the quadratic residuosity assumption [qra], the assembly code [Implem.bbs_asm] is
    unpredictable. *)

Hypothesis distinct : p <> q.

Hypothesis p_blum : p mod 4 = 3 mod 4.

Hypothesis q_blum : q mod 4 = 3 mod 4.

Variable epsilon : R.

Hypothesis qra : HardProblem.QR _ _ p_prime q_prime epsilon.

Theorem unpredictable : forall len,
  let nn := ceiling_div (S len) 32 gt_32_0 in
  let nk := ceiling_div (S (Zabs_nat (N_digits (p * q)))) 32 gt_32_0 in
  4 * Z_of_nat (4 * nk + nn + 2) < 2 ^^ 32 ->
  Security.left_unpredictability _ (Zstar.Zstar_listNE _ (Zstar.pq_gt_1 _ _ p_prime q_prime)) bbs_asm_sem len epsilon.
Proof.
intros len nn nk Hny.
rewrite /Security.left_unpredictability => A.
apply: (Distribution.DistribLib.Equiv_transitive _ (fun b : bool => eqb b true) 0 epsilon
  _ _ _ _ _ (BBS.unpredictable _ _ p_prime q_prime distinct p_odd q_odd p_blum q_blum _ qra len A)); last by ring.
apply Distribution.DistribLib.Equiv_extensionality => seed.
rewrite bbs_asm_sem_bbs //.
by apply Distribution.DistribLib.Equiv_reflexive.
Qed.

End BBS.

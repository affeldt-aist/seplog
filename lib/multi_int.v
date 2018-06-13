(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext seq_ext.
Require listbit listbit_correct.
Require Import ssrZ machine_int.
Import MachineInt.

Reserved Notation "\S_{ n } l" (at level 4, format "'\S_{'  n  '}'  l").

Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.

(** a multi_int is a list of (int n) that represents an unsigned integer in base 2^n, LSW first*)

(** expected: length l = n * k *)
(** the input list l is with MSb first, the output list is a multi_int *)
Fixpoint listbit_to_ints n k (l : list bool) : list (int n) :=
  match k with
    | O => nil
    | k'.+1 => let (a, b) := (take n l, drop n l) in
      listbit_to_ints n k' b ++ bits2u n a :: nil
  end.

Lemma size_listbit_to_ints k n l : size l = (k * n)%nat ->
  size (listbit_to_ints n k l) = k.
Proof.
elim : k n l => [ // | k IHk n l H].
have [hd [tl [Hl [Hhd Htl]]]] : exists hd tl, l = hd ++ tl /\ size hd = n /\ (size tl = k * n)%nat.
  have : (n <= size l)%nat by rewrite H /= mulSn leq_addr.
  case/app_split => hd [tl [H' H'']].
  exists hd, tl; split => //; split => //.
  move/eqP: H.
  by rewrite H'' size_cat mulSn H' eqn_add2l => /eqP.
by rewrite Hl /= drop_size_cat // size_cat IHk // addn1.
Qed.

(** Z2ints: turn a Z into a multi_int *)

Definition adjust_to_ints n k (l : list bool) : list (int n) :=
  listbit_to_ints n k (listbit.bits.adjust_u l (k * n)).

Definition Z2ints n k z : list (int n) :=
  match z with
    | Zpos p => adjust_to_ints n k (rev (listbit_correct.bitZ.pos2lst p))
    | Zneg p => adjust_to_ints n k (rev (listbit_correct.bitZ.pos2lst p))
    | _ => nseq k (Z2u n 0)
  end.

Lemma Z2ints_0 n x : Z2ints n 0 x = List.nil.
Proof. by case: x. Qed.

Lemma size_Z2ints k n z : size (Z2ints n k z) = k.
Proof.
elim : k n z => [n [] // | k IH n [ | p | p] /=].
- by rewrite size_nseq.
- by rewrite size_listbit_to_ints // listbit.bits.size_adjust_u.
- by rewrite size_listbit_to_ints // listbit.bits.size_adjust_u.
Qed.

(** * lists of finite-size integers seen as unsigned multi-precision integers *)

Section sum_section.

Variable n : nat.

(** sum_k k lst sum the list elements of indices [0,k-1],
    little-endian / least significant first *)
Fixpoint sum_k k (lst : list (int n)) :=
  match lst with
    | nil => 0
    | hd :: tl => match k with
		    | O => u2Z hd
		    | S k' => u2Z hd + 2 ^^ n * sum_k k' tl
		  end
  end.

Lemma sum_k_nil : forall k, sum_k k (@nil (int n)) = 0.
Proof. by case. Qed.

Lemma sum_k_0 : forall (h : int n) t, sum_k 0 (h :: t) = u2Z h.
Proof. by []. Qed.

Lemma sum_k_S : forall k (h : int n) t, sum_k (S k) (h :: t) = u2Z h + 2 ^^ n * sum_k k t.
Proof. by []. Qed.

(** sum the first k list members (with k>=1),
    little-endiant / least significant first  *)
Definition lSum k (lst : list (int n)) :=
  match k with O => 0 | S k' => sum_k k' lst end.

Local Notation "\S_{ n } l" := (lSum n l).

Lemma lSum_nil : forall k, lSum k (@nil (int n)) = 0.
Proof. case => // k /=; by rewrite sum_k_nil. Qed.

Lemma lSum_S : forall k (h : int n) t,
  lSum (S k) (h :: t) = u2Z h + 2 ^^ n * lSum k t.
Proof. move=> [|] //= ? _; ring. Qed.

Lemma min_lSum k (lst : list (int n)) : 0 <= lSum k lst.
Proof.
elim: lst k => [k|h t IH].
- by rewrite lSum_nil.
- case=> [|k].
  + rewrite /=; exact/leZZ.
  + rewrite lSum_S.
    apply addZ_ge0; first exact: min_u2Z.
    apply mulZ_ge0; [exact: expZ_ge0 | exact: IH].
Qed.

Lemma max_lSum : forall k (lst : list (int n)), lSum k lst < 2 ^^ (k * n).
Proof.
elim=> // k IH [|h t].
rewrite lSum_nil; exact: expZ_gt0.
rewrite lSum_S mulSn ZpowerD.
apply (@ltZ_leZ_trans (2 ^^ n * (1 + lSum k t))).
- rewrite mulZDr mulZ1; exact/ltZ_add2r/max_u2Z.
- apply leZ_wpmul2l; first exact: expZ_ge0.
  move: (IH t) => ?; omega.
Qed.

Lemma lSum_inj : forall k (l1 l2 : list (int n)), size l1 = k -> size l2 = k ->
  lSum k l1 = lSum k l2 -> l1 = l2.
Proof.
elim.
- by case=> //; case.
- move=> k IHk [|h1 t1] // [|h2 t2] // [Hlen1] [Hlen2].
  rewrite !lSum_S addZC mulZC => H.
  symmetry in H.
  rewrite addZC mulZC in H.
  apply poly_eq_inv in H.
  + case: H => H1.
    move/u2Z_inj => H2.
    subst h2.
    f_equal.
    by apply IHk.
  + split; first by apply min_lSum.
    split.
      split; by [apply min_u2Z | apply max_u2Z].
    split; first by apply min_lSum.
    split; by [apply min_u2Z | apply max_u2Z].
Qed.

Lemma lSum_head_swap : forall k h h' (tl : list (int n)), (k > 0)%nat ->
  lSum k (h :: tl) + u2Z h' = lSum k (h' :: tl) + u2Z h.
Proof.
move=> [| k] hd hd' tl H.
- by inversion H.
- rewrite 2!lSum_S; ring.
Qed.

(**  (0 a_0 ... a_{k-1}) + z = (z a_0 ... a_{k-1})  *)
Lemma lSum_head_swap0 k lst z :
  lSum (S k) (Z2u n 0 :: lst) + u2Z z = lSum (S k) (z :: lst).
Proof.
rewrite lSum_head_swap //.
rewrite Z2uK; first by omega.
split => //; exact: expZ_gt0.
Qed.

(**  beta * (a_0 ... a_{k-1}) = (0 a_0...a_{k-1})  *)
Lemma lSum_Zpower_Zmult k lst : 2 ^^ n * lSum k lst = lSum (S k) (Z2u n 0 :: lst).
Proof.
rewrite lSum_S Z2uK //.
split; [done | exact: expZ_gt0].
Qed.

Lemma lSum_1 : forall lst, lSum 1 lst = u2Z (nth (`( 0 )_ n) lst 0).
Proof. move=> [|hd tl] //=; rewrite Z2uK //; split => //; exact: expZ_gt0. Qed.

Lemma lSum_nseq_0 : forall k k', lSum k (nseq k' (Z2u n 0)) = 0.
Proof.
elim => // k IH [|k'].
- simpl nseq; by rewrite lSum_nil.
- simpl nseq; rewrite lSum_S IH mulZ0 Z2uK //.
  split; [done | exact: expZ_gt0].
Qed.

Lemma lSum_0_inv_first : forall k (l : list (int n)), (k <= size l)%nat ->
  lSum k l = 0 -> take k l = nseq k (Z2u n 0).
Proof.
elim => [| k IH [|h t]].
- by move=> l _ _; by rewrite take0.
- by inversion 1.
- move=> Hk.
  rewrite /= ltnS in Hk.
  rewrite lSum_S => H /=.
  move: (min_u2Z h) (expZ_gt0 n) (min_lSum k t) => ? ? ?.
  have ? : 0 <= 2 ^^ n * lSum k t by apply mulZ_ge0 => //; exact/ltZW.
  have HH : 0 = 2 ^^ n * lSum k t by omega.
  rewrite IH //.
  + congr cons.
    apply u2Z_inj.
    rewrite Z2uK //; omega.
  + move/esym/eqP : HH; rewrite mulZ_eq0 => /orP[|] /eqP // ?; omega.
Qed.

Lemma lSum_0_inv len (l : list (int n)) : size l = len -> lSum len l = 0 ->
  l = nseq len (Z2u n 0).
Proof.
move=> l_len Sum_0.
apply lSum_0_inv_first in Sum_0; last by rewrite l_len.
rewrite take_oversize // in Sum_0.
by rewrite l_len.
Qed.

Lemma lSum_remove_last' : forall K (lst : list (int n)) k, size lst = K ->
  lSum (S k) lst = lSum k lst + 2 ^^ (k * n) * u2Z (nth (`( 0 )_ n) lst k).
Proof.
elim=> //=.
- case => // k _.
  rewrite sum_k_nil lSum_nil nth_nil Z2uK //.
  + by rewrite mulZ0.
  + split => //.
    apply (@ltZ_leZ_trans 1) => //; exact: expZ_ge1.
- move=> K IHK [|hd tl] //; case.
  + case => HK.
    rewrite [Zmult]lock /= -lock; ring.
  + move => k'; case => HK.
    rewrite lSum_S sum_k_S IHK //= mulSn ZpowerD; ring.
Qed.

Lemma lSum_remove_last (lst : list (int n)) k :
  lSum (S k) lst = lSum k lst + 2 ^^ (k * n) * u2Z (nth (`( 0 )_ n) lst k).
Proof. by apply lSum_remove_last' with (length lst). Qed.

Lemma lSum_cat : forall k (h t : seq (int n)),
   (size h <= k)%nat ->
   lSum k (h ++ t) = lSum k h + 2 ^^ (size h * n) * lSum (k - size h) t.
Proof.
elim => [[] //|k IH [|h1 h2]].
  by move=> t _; rewrite lSum_nil add0Z mul0n cat0s mul1Z.
move=> t H.
rewrite cat_cons 2!lSum_S IH; last by rewrite ltnS in H.
by rewrite mulZDr addZA /= mulZA ZpowerD.
Qed.

Lemma lSum_beyond : forall k (l : list (int n)), size l = k ->
  forall l', lSum k l = lSum k (l ++ l').
Proof.
elim => // k IH [|h t] // [H] lst'; by rewrite [cat _ _]/= 2!lSum_S -IH.
Qed.

Lemma lSum_take i (X : seq (int n)) : (i <= size X)%nat -> lSum i (take i X) = lSum i X.
Proof.
move=> H; rewrite -{2}(cat_take_drop i X).
apply lSum_beyond; by rewrite size_takel.
Qed.

Lemma lSum_beyond_idx : forall (k : nat) (l : list (int n)), size l = k ->
  forall k', lSum (k + k') l = lSum k l.
Proof.
induction k.
- case=> //= _ k'.
  by rewrite lSum_nil.
- case=> hd lt.
  + rewrite 2!lSum_nil //.
  + case=> Hk k'.
    by rewrite addSn 2!lSum_S IHk.
Qed.

Lemma lSum_cut k1 (l1 : list (int n)) : size l1 = k1 ->
  forall k l l2, size l = k -> l = l1 ++ l2 ->
    lSum k (l1 ++ l2) = lSum k1 l1 + 2 ^^ (k1 * n) * lSum (k - k1) l2.
Proof.
move=> H1 k l l2 H2 H3.
rewrite lSum_cat //; last by rewrite -H2 H3 size_cat leq_addr.
rewrite H1; f_equal.
rewrite (_ : k = k1 + (k - k1))%nat; last first.
  rewrite addnBA; first by rewrite addnC addnK.
  by rewrite -H1 -H2 H3 size_cat leq_addr.
exact: lSum_beyond_idx.
Qed.

Lemma lSum_cut_last k (l : list (int n)) tl : size (l ++ tl :: nil) = k ->
  lSum k (l ++ tl :: nil) = lSum (k - 1) l + 2 ^^ ((k - 1) * n) * u2Z tl.
Proof.
move=> Hk'.
have H : (size l = k - 1)%nat by rewrite -Hk' size_cat //= addn1 subn1.
rewrite (lSum_cut _ _ H k (l ++ tl :: nil)) //.
have Hk : (0 < k)%nat by rewrite -Hk' size_cat addn1.
rewrite ( _ : k - (k - 1) = 1)%nat; last by rewrite subnBA // addnC addnK.
by rewrite /Zbeta mulnC.
Qed.

Lemma lSum_cut_last_beyond k (l : list (int n)) :
  (0 < k)%nat -> size l = k ->
  lSum k l = lSum (k - 1) l + 2 ^^ ((k - 1) * n) * u2Z (nth (`( 0 )_ n) l (k - 1)).
Proof.
move=> Hk Hk'.
case/lastP : l => /= h t in Hk Hk' *.
  by rewrite -t in h.
rewrite -cats1 lSum_cut_last; last first.
  by rewrite -cats1 in Hk'.
rewrite -lSum_beyond // -Hk'; last first.
  by rewrite size_rcons subn1.
rewrite size_rcons subn1 /=.
do 2 f_equal.
by rewrite nth_cat ltnn subnn /=.
Qed.

Lemma lSum_beyond_inv : forall l (s: list (int n)) l',
  size s = l -> (l' < l)%nat -> lSum l s < 2 ^^ (l' * n) ->
  s = take l' s ++ nseq (l - l') (Z2u n 0).
Proof.
elim => [ [] // [] // | l IH ].
elim => // hd tl _.
case=> l'.
- rewrite take0 [_ ++ _]/= => _ H.
  rewrite [_ ^^ _]/= in H.
  have {H} H : lSum l.+1 (hd :: tl) = 0 by move: (min_lSum l.+1 (hd :: tl)) => ?; omega.
  by apply lSum_0_inv in H.
- case=> H.
  rewrite ltnS => l'l.
  rewrite lSum_S.
  rewrite [take _ _]/= [_ ++ _]/= => H'.
  rewrite -IH //.
  apply Znot_ge_lt => H''.
  have {H''} H'' : 2 ^^ (l'.+1 * n) <= 2 ^^ n * lSum l tl.
    rewrite /= mulSn ZpowerD.
    apply leZ_wpmul2l.
    exact: expZ_ge0.
    exact: Zge_le.
  move: (min_u2Z hd) => ?; omega.
Qed.

Lemma lSum_upd_nth : forall (lst : list (int n)) k m,
  lSum k lst = lSum k (upd_nth lst k m).
Proof.
elim=> [ // |hd tl IH [|k] // m].
by rewrite 2!lSum_S -IH.
Qed.

Lemma lSum_upd_nth2 : forall k (lst : list (int n)) i z,
  size lst = k ->
  (i < k)%nat ->
  lSum k lst - u2Z (nth (`( 0 )_ n) lst i) * 2 ^^ (i * n) + u2Z z * 2 ^^ (i * n) = lSum k (upd_nth lst i z).
Proof.
elim.
- case=> // i z _; by inversion 1.
- move=> k IHk [|hd tl] // [|i] z; case=> Hk.
  + move=> _.
    rewrite [nth _ _ _]/= 2!lSum_S mul0n /= !mulZ1; ring.
  + rewrite ltnS => ?.
    rewrite [nth _ _ _]/= 2!lSum_S -IHk // (_ : S i = 1 + i)%nat // mulnDl.
    rewrite ZpowerD mul1n; ring.
Qed.

Lemma lSum_skipn : forall l (A B : list (int n)) m k, size A = l -> size B = l ->
  lSum (k - m) (drop m A) < lSum (k - m) (drop m B) ->
  lSum k A < lSum k B.
Proof.
elim.
- move=> [|] // [|] //= m k _ _ H.
  by rewrite lSum_nil /= in H.
- move=> l IH.
  move=> [|hdA tlA] // [|hdB tlB] //.
  move=> [|m] // [|n0] // [HA] [HB] H.
  rewrite 2!lSum_S.
  rewrite /= in H.
  move: {IH}(IH _ _ _ _ HA HB H) => IH.
  move: (max_u2Z hdA) => HhdA.
  move: (max_u2Z hdB) => HhdB.
  move: (min_u2Z hdA) => HhdA'.
  move: (min_u2Z hdB) => HhdB'.
  move: (min_lSum n0 tlA) => HtlA.
  move: (min_lSum n0 tlB) => HtlB.
  case: (Ztrichotomy (u2Z hdA) (u2Z hdB)) => [X|[X|X]].
  + apply (@ltZ_trans (u2Z hdB + 2 ^^ n * lSum n0 tlA)); first omega.
    apply/ltZ_add2l/ltZ_pmul2l => //; exact/expZ_gt0.
  + rewrite X.
    apply/ltZ_add2l/ltZ_pmul2l => //; exact/expZ_gt0.
  + apply poly_Zlt => //; omega.
Qed.

Lemma lSum_positive_to_ints : forall k l, size l = (k * n)%nat ->
  lSum k (listbit_to_ints n k l) = listbit_correct.bitZ.u2Z l.
Proof.
elim.
- move=> l.
  rewrite mul0n.
  by destruct l.
- move=> k IHk l H.
  rewrite /= in H.
  have [hd [tl [Hl [Hlenhd Hlentl] ] ] ] : exists hd tl, l = hd ++ tl /\ size hd = n /\ (size tl = k * n)%nat.
    have X : (n <= size l)%nat.
      by rewrite H /= mulSn leq_addr.
    move/app_split : X => [hd [tl [H' H'']]].
    exists hd; exists tl; split => //.
    rewrite H'; split => //.
    rewrite H'' /= size_cat mulSn in H.
    move/eqP in H.
    rewrite H' eqn_add2l in H.
    by move/eqP in H.
  rewrite {1}Hl.
  simpl listbit_to_ints.
  rewrite drop_size_cat //.
  eapply trans_eq.
  + eapply lSum_cut; [ idtac | idtac | reflexivity ].
    * by apply size_listbit_to_ints.
    * by rewrite size_cat /= size_listbit_to_ints // addnC.
  + rewrite IHk //.
    rewrite (_ : S k - k = 1)%nat; last first.
      by rewrite -addn1 addnC addnK.
    simpl lSum.
    rewrite u2Z_bits2u_u2Z //; last by rewrite size_takel // size_cat Hlenhd leq_addr.
    rewrite Hl listbit_correct.bitZ.u2Z_app listbit_correct.bitZ.u2Z_app_zeros Hlentl.
    rewrite take_size_cat //; ring.
Qed.

Lemma lSum_Z2ints len : forall z, `| z | < 2 ^^ (len * n) ->
  lSum len (Z2ints n len z) = `| z |.
Proof.
move=> [|p|p] Hp' /=.
- clear Hp'.
  by apply lSum_nseq_0.
- rewrite /adjust_to_ints lSum_positive_to_ints.
  + by rewrite listbit_correct.bitZ.adjust_u2Z listbit_correct.bitZ.u2Z_rev_poslst.
  + by rewrite listbit.bits.size_adjust_u.
- rewrite /adjust_to_ints lSum_positive_to_ints.
  + by rewrite listbit_correct.bitZ.adjust_u2Z listbit_correct.bitZ.u2Z_rev_poslst.
  + by rewrite listbit.bits.size_adjust_u.
Qed.

Lemma lSum_Z2ints_pos len z : 0 <= z /\ z < 2 ^^ (len * n) ->
  lSum len (Z2ints n len z) = z.
Proof.
move=> [Hz Hz'].
rewrite -{2}(geZ0_norm z) //.
apply lSum_Z2ints.
by rewrite geZ0_norm.
Qed.

Lemma Z2ints_lSum k lst : k = size lst -> lst = Z2ints n k (lSum k lst).
Proof.
move=> H.
have H1 : 0 <= lSum k lst by apply min_lSum.
have H2 : lSum k lst < 2 ^^ (k * n) by apply max_lSum.
move: (lSum_Z2ints_pos  k (lSum k lst) (conj H1 H2)).
move/lSum_inj => Heq.
symmetry.
apply Heq => //.
by apply size_Z2ints.
Qed.

(** most significant first, big-endian *)

Definition bSum_c (l : seq (int n)) : Z :=
  foldl (fun acc x => acc * 2 ^^ n + (@u2Zc n x)) 0 l.

Lemma bSum_c_Sum : forall (l : seq (int n)),
  bSum_c l = lSum (size l) (rev l).
Proof.
elim/last_ind => // h t IH.
rewrite /bSum_c -{1}cats1 foldl_cat.
rewrite -/(bSum_c h) IH [in X in X = _]/=.
rewrite rev_rcons size_rcons lSum_S u2ZE.
by rewrite mulZC addZC.
Qed.

(** Sum_hole *)

Definition Sum_hole len hole (l : list (int n)) := lSum (len - 1) (idel hole l).

Lemma Sum_hole_last : forall (l : list (int n)) k, size l = k ->
  Sum_hole k (k - 1)%nat l = lSum (k - 1)%nat l.
Proof.
case/lastP => [|h t] // [|k] //; rewrite size_rcons; case=> Hk.
rewrite /Sum_hole subn1 -cats1.
by rewrite -{2}Hk idel_size_last -lSum_beyond.
Qed.

Lemma Sum_hole_last' : forall (l : seq (int n)) k, size l = k ->
  Sum_hole k 0 l = lSum (k - 1)%nat (List.tail l).
Proof. by case. Qed.

Lemma Sum_hole_upd_nth l (lst : list (int n)) k m : size lst = l ->
  Sum_hole l k lst = Sum_hole l k (upd_nth lst k m).
Proof. move=> H; by rewrite /Sum_hole idel_upd_nth. Qed.

Lemma Sum_hole_shift : forall k (l : list (int n)), size l = k ->
  forall j, (j < k)%nat ->
    Sum_hole k j l + u2Z (nth (Z2u n 0) l j) * 2 ^^ (n * (j - 1)) =
    Sum_hole k (j - 1) l + u2Z (nth (Z2u n 0) l (j - 1)) * 2 ^^ (n * (j - 1)).
Proof.
induction k; intros.
- by destruct l.
- destruct j => //.
  rewrite subn1.
  case: (list_split (Z2u n 0) H H0) => l1 [H2 [l2 H1]].
  rewrite /Sum_hole.
  rewrite {1}H1.
  have -> : (idel (S j) (l1 ++ nth (Z2u n 0) l (S j) :: nil ++ l2)) = (l1 ++ l2).
    rewrite -H1.
    by apply idel_app with (nth (Z2u n 0) l (S j)).
  have H4 : (0 < size l1)%nat by rewrite H2.
  have H5 : (j < S j)%nat by [].
  case: (list_split (Z2u n 0) H2 H5) => l1' [H7 [l3 H6]].
  destruct l3.
  + rewrite H6 -catA in H1.
    have H8 : idel j (l1' ++ nth (Z2u n 0) l1 j :: nil ++ nth (Z2u n 0) l (S j) :: l2) =
                                                     l1' ++ nth (Z2u n 0) l (S j) :: l2.
      rewrite -H1.
      by apply idel_app with (nth (Z2u n 0) l1 j).
    rewrite -H1 in H8.
    rewrite H6 -catA.
    have H9 : size (l1' ++ nth (Z2u n 0) l1 j :: l2) = k.
      rewrite size_cat.
      rewrite H1 size_cat addnS in H.
      by case: H.
    have H10 : size (l1' ++ nth (Z2u n 0) l (S j) :: l2) = k.
      rewrite size_cat /=.
      rewrite H1 size_cat /= addnS in H.
      by case: H.
    rewrite -{1}H9 size_cat (lSum_cut _ _ H7 _ (l1' ++ nth (Z2u n 0) l1 j :: l2)) //; last first.
      by rewrite size_cat // -size_cat H9 subn1.
    rewrite -H10 H8 (lSum_cut _ _ H7 _ (l1' ++ nth (Z2u n 0) l (S j) :: l2)) //; last first.
      by rewrite subn1.
    rewrite H10.
    ring_simplify.
    rewrite -!addZA.
    f_equal.
    rewrite (mulnC j).
    rewrite (mulZC _ (2 ^^ (n * j))).
    rewrite -!mulZDr !subn1.
    rewrite -size_cat.
    rewrite H9.
    rewrite (_ : lSum (k - j) (nth (Z2u n 0) l1 j :: l2) + u2Z (nth (Z2u n 0) l (S j)) =
                 lSum (k - j) (nth (Z2u n 0) l (S j) :: l2) + u2Z (nth (Z2u n 0) l1 j)) //.
      have ->// : nth (Z2u n 0) l1 j = nth (Z2u n 0) l j.
      rewrite H6 H1.
      cutrewrite (l1' ++ [:: nth (Z2u n 0) l1 j, nth (Z2u n 0) l (S j) & l2] =
        (l1' ++ nth (Z2u n 0) l1 j :: nil) ++ nth (Z2u n 0) l (S j):: l2).
        symmetry.
        rewrite !(cat0s,cats0) in H7 H6 *.
        by rewrite nth_cat H7 ltnn subnn /= -H6.
      by rewrite -catA.
    apply lSum_head_swap => //.
    by rewrite ltn_subRL addn0.
  + rewrite H6 size_cat /= H7 addnS in H2.
    case: H2 => H2.
    rewrite -{2}(addn0 j) in H2.
    move/eqP : H2.
    by rewrite eqn_add2l.
Qed.

End sum_section.

Arguments sum_k [n].
Arguments lSum [n].
Arguments min_lSum [n].
Arguments max_lSum [n].
Arguments lSum_1 [n].
Arguments lSum_cut [n].
Arguments lSum_cut_last [n].
Arguments lSum_cut_last_beyond [n].
Arguments lSum_upd_nth2 [n].
Arguments lSum_skipn [n].
Arguments lSum_nseq_0 [n].
Arguments lSum_Z2ints [n].
Arguments lSum_Z2ints_pos [n].
Arguments Z2ints_lSum [n].
Arguments Sum_hole [n].
Arguments Sum_hole_last [n].
Arguments Sum_hole_last' [n].
Arguments Sum_hole_upd_nth [n].
Arguments Sum_hole_shift [n].

Notation "\S_{ n } l" := (lSum n l) : multi_int_scope.

Local Open Scope multi_int_scope.

Lemma Z2ints_1 {n} : forall m, Z2u (S n) 1 :: nseq m (Z2u (S n) 0) = Z2ints (S n) (S m) 1.
Proof.
move=> m.
rewrite (Z2ints_lSum (S m) (Z2u (S n) 1 :: nseq m (Z2u (S n) 0))); last by rewrite /= size_nseq.
f_equal.
rewrite lSum_S Z2uK //.
  by rewrite lSum_nseq_0 mulZ0.
split => //.
rewrite (_ : 1 = 2 ^^ 0) //.
exact/expZ_2_lt.
Qed.

Lemma Zodd_lSum n : forall (lst : list (int (S n))) len, Zodd (lSum len lst) ->
  Zodd (u2Z (nth (`( 0 )_(S n)) lst 0)).
Proof.
elim => /=.
- move=> len.
  rewrite lSum_nil Z2uK //; split; [exact: leZZ | exact: expZ_gt0].
- move=> hd tl IH [|len] //.
  rewrite lSum_S.
  case: (Zeven_odd_dec (u2Z hd)) => // Hhd.
  move: (Zeven_power n).
  move/(Zeven_mult_Zeven_l _ (lSum len tl)).
  move/(Zeven_plus_Zeven _ _ Hhd).
  move/Zeven_not_Zodd.
  contradiction.
Qed.

Lemma Zeven_lSum n : forall (l : list (int (S n))) len, (0 < len)%nat ->
  Zeven (lSum len l) -> Zeven (u2Z (nth (Z2u (S n) 0) l 0)).
Proof.
elim => /=.
- move=> len Hlen.
  rewrite lSum_nil Z2uK //; split; [exact: leZZ | exact: expZ_gt0].
- move=> hd tl IH [|len] //.
  move=> Hlen; rewrite lSum_S.
  case: (Zeven_odd_dec (u2Z hd)) => // Hhd.
  move: (Zeven_power n).
  move/(Zeven_mult_Zeven_l _ (lSum len tl)).
  move/(Zodd_plus_Zeven _ _ Hhd).
  move/Zeven_not_Zodd.
  contradiction.
Qed.

Lemma Z2ints_inj n k x x' :
  0 <= x < 2 ^^ (k * n) -> 0 <= x' < 2 ^^ (k * n) ->
  Z2ints n k x = Z2ints n k x' -> x = x'.
Proof.
move=> Hx Hx' H.
have : lSum k (Z2ints n k x) = lSum k (Z2ints n k x') by rewrite H.
by rewrite lSum_Z2ints_pos // lSum_Z2ints_pos.
Qed.

Lemma Z2ints_neg n k : forall z, Z2ints n k z = Z2ints n k (-z).
Proof. by move=> [|p|p]. Qed.

Lemma Zodd_bool_multi : forall n (X : list (int 32)), size X = n ->
  Zodd_bool (\S_{ n } X) = Zodd_bool (u2Z (X `32_ 0)).
Proof.
elim => [|n IHn].
- case=> //= _; by rewrite /zero32 Z2uK.
- elim/last_ind => // hd tl _.
  rewrite size_rcons; case=> Hlenhd.
  destruct hd as [|i hd].
  - by destruct n.
  - rewrite /= in Hlenhd.
    rewrite -cats1.
    rewrite lSum_cut_last; last by rewrite size_cat /= addn1 -Hlenhd.
    rewrite subSS subn0.
    destruct n as [|n] => //.
    rewrite lSum_S -addZA /Zbeta ( _ : (n.+1 * 32) = 32 + n * 32)%nat
      // ZpowerD -mulZA -mulZDr {2}(_ : 32 = 1 * 32)%nat //.
    apply Zodd_bool_Zplus_Zpower => //; omega.
Qed.

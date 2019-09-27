(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Max.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext ssrnat_ext seq_ext.
Require Import listbit.

(**************************************************************************)
(* This file provides functions to interpret lists of bits as (signed     *)
(* or unsigned) integers and proves their arithmetic properties.  This is *)
(* for the implementation of finite-size integers.                        *)
(**************************************************************************)

Reserved Notation "'.[' l ']u'" (at level 30, format "'[' .[  l  ]u ']'").
Reserved Notation "'.[' l ']s'" (at level 30, format "'[' .[  l  ]s ']'").

Declare Scope listbit_correct_scope.

Local Open Scope zarith_ext_scope.

Module bitZ.

Import bits.

(** interpretation of listbits as unsigned integers, and properties *)
Fixpoint u2Z l : Z:=
  match l with
    | nil => 0
    | hd :: tl =>
      match hd with
        | true => 2 ^^ size tl + u2Z tl
        | false => u2Z tl
      end
  end.

Notation "'.[' l ']u'" := (u2Z l) : listbit_correct_scope.

Local Open Scope listbit_correct_scope.

Lemma u2Z_false l : .[ false :: l ]u = .[ l ]u.
Proof. done. Qed.

Lemma u2Z_falses k l : .[ nseq k false ++ l ]u = .[ l ]u.
Proof. by move: k l; elim. Qed.

Lemma u2Z_true l : .[ true :: l ]u = 2 ^^ size l + .[ l ]u.
Proof. done. Qed.

Lemma u2Z_zeros : forall n, .[ zeros n ]u = 0. Proof. by elim. Qed.

Lemma u2Z_ones : forall n, .[ ones n ]u = 2 ^^ n - 1.
Proof. elim => // n; simpl u2Z => ->; rewrite size_nseq ZpowerS; omega. Qed.

Lemma u2Z_app : forall l l', .[ l ++ l' ]u = .[ l ++ zeros (size l') ]u + .[ l' ]u.
Proof.
elim => [l' | [] //= l IH l' ].
- by rewrite u2Z_zeros.
- symmetry.
  by rewrite size_cat size_nseq -size_cat (IH l') addZA.
Qed.

Lemma u2Z_app_zeros : forall l n, .[ l ++ zeros n ]u = .[ l ]u * 2 ^^ n.
Proof.
elim => [n| [] //= l Hn n].
- by rewrite u2Z_zeros.
- rewrite Hn size_cat size_nseq ZpowerD; ring.
Qed.

Lemma u2Z_Zpower_inv : forall n a, size a = n.+1 ->
  .[ a ]u = 2 ^^ n -> a = true :: zeros n.
Proof.
elim => [ [] // a [] // _ | n IH ].
- by destruct a.
- elim/last_ind => // h t _.
  rewrite size_rcons; case => H.
  move: {IH}(IH _ H) => IH.
  rewrite -cats1 u2Z_app u2Z_app_zeros [2 ^^ size _]/=.
  destruct t.
  + move=> abs.
    rewrite ZpowerS [ .[ [:: true] ]u ]/= in abs.
    have H' : Zeven (2 * 2 ^^ n) by rewrite -ZpowerS; apply Zeven_power.
    rewrite -abs in H'.
    move: (Zodd_1 (.[ h ]u)).
    rewrite mulZC.
    by move/Zodd_not_Zeven.
  + rewrite addZ0 ZpowerS mulZC => H'.
    have {}H' : .[h ]u = 2 ^^ n by move/eqZ_mul2l : H'; apply.
    move/IH : H' => ->.
    by rewrite /= -nseqS.
Qed.

Lemma Zodd_lst_true lst : Zodd (.[ lst ++ [:: true] ]u).
Proof.
rewrite u2Z_app /= (_ : [:: false] = zeros 1) // u2Z_app_zeros /= mulZC.
by apply Zodd_1.
Qed.

Lemma Zeven_ulst_false lst : Zeven (.[ lst ++ [:: false] ]u).
Proof.
rewrite u2Z_app /= (_ : [:: false] = zeros 1) // u2Z_app_zeros /= mulZC addZ0.
exact: Zeven_2.
Qed.

Lemma max_u2Z : forall n l, (size l <= n)%nat -> .[ l ]u < 2 ^^ n.
Proof.
elim => [ [] // | n IHn [|[|] tl] ]; simpl size.
- move=> _; exact/expZ_gt0.
- rewrite ltnS => H.
  rewrite u2Z_true.
  apply (@leZ_ltZ_trans (2 ^^ n + .[ tl ]u)).
  + apply/leZ_add2r/leZP; by rewrite Zpower_2_le.
  + rewrite -Zpower_plus; exact/ltZ_add2l/IHn.
- rewrite ltnS => H.
  rewrite u2Z_false.
  exact/(ltZ_trans (IHn _ H))/expZ_2_lt.
Qed.

Lemma min_u2Z : forall l, 0 <= .[ l ]u.
Proof.
elim => [// | [] // l H]; rewrite u2Z_true.
apply addZ_ge0 => //; exact: expZ_ge0.
Qed.

Lemma overflow_size_u2Z l n : 2 ^^ n <= .[ l ]u -> (n <= size l)%nat.
Proof.
move=> H.
move: (max_u2Z _ _ (leqnn (size l))) => X.
rewrite leqNgt; apply/negP.
move/expZ_2_lt/(ltZ_trans X) => ?; omega.
Qed.

Lemma u2Z_inj : forall n (v w : list bool),
  size v = n -> size w = n -> .[ v ]u = .[ w ]u -> v = w.
Proof.
elim => [ [] [] // | ].
move=> n IHn; case => //.
move=> v0 v; case => //.
move=> w0 w; case => Hv; case => Hw; move: v0 w0.
case; case => //.
+ rewrite !u2Z_true => H1.
  rewrite Hv Hw in H1.
  rewrite (IHn v w) //; omega.
+ rewrite u2Z_false u2Z_true => H1.
  have H2 : .[ w ]u < 2 ^^ size v by apply max_u2Z; rewrite Hv Hw.
  move: (min_u2Z v) => H3.
  have H4 : ~ (.[ w ]u < 2^^ size v) by omega.
  contradiction.
+ rewrite u2Z_false u2Z_true => H1.
  have H2 : .[ v ]u < 2 ^^ size w by apply max_u2Z; rewrite Hv Hw.
  move: (min_u2Z w) => H3.
  have ? : ~ (.[ v ]u < 2 ^^ size w) by omega.
  contradiction.
+ rewrite !u2Z_false => H1.
  by rewrite (IHn v w).
Qed.

Lemma u2Z_zeros_inv n l : size l = n -> .[ l ]u = 0 -> l = zeros n.
Proof.
move=> Hn; rewrite -(u2Z_zeros n) => Hl.
apply (u2Z_inj n) => //; by rewrite size_nseq.
Qed.

Lemma u2Z_power_inv : forall n l m, (m <= n)%nat ->
  size l = n -> .[ l ]u < 2 ^^ m ->
  exists l', l = zeros (n - m) ++ l'.
Proof.
elim.
- case => //=.
  move=> *; by exists [::].
- move=> n IHn [ | [|] l ] //= m Hmn [Hlenl] Hl //.
  + rewrite Hlenl in Hl.
    move: Hmn; rewrite leq_eqVlt; case/orP => [/eqP|] Hmn.
    - subst m.
      rewrite subSS subnn; by exists (true :: l).
    - rewrite ltnS in Hmn.
      move: Hmn; rewrite leq_eqVlt; case/orP => [/eqP|] Hmn.
      * subst m.
        have Hl' : ~ (0 <= .[ l ]u) by omega.
        by move/Hl': (min_u2Z l).
      * apply expZ_2_lt in Hmn.
        have : ~ (2 ^^ m < 2 ^^ n) by move: (min_u2Z l) => ?; omega.
        by move/(_ Hmn).
  + move: Hmn; rewrite leq_eqVlt; case/orP => [/eqP|] Hmn.
    * rewrite Hmn subnn; by exists (false :: l).
    * rewrite ltnS in Hmn.
      case: {IHn}(IHn _ _ Hmn Hlenl Hl) => l' Hl'.
      exists l'.
      by rewrite subSn //= Hl'.
Qed.

Lemma u2Z_last : forall l b, .[ l ++ [:: b] ]u = 2 * .[ l ]u + .[ [:: b] ]u.
Proof.
elim => //. case => // l Hl [|];
rewrite [Zmult]lock /= -lock Hl size_cat ZpowerD [Zmult]lock /= -lock; ring.
Qed.

Lemma u2Z_erase_leading_zeros: forall l, .[ erase_leading_zeros l ]u = .[ l ]u.
Proof. elim => //. by case. Qed.

Lemma zext_correct : forall p l, .[ zext p l ]u = .[ l ]u.
Proof. by elim. Qed.

(** Z2u *)
(** NB:
   positive is a type that represents strictly positive number
   xH is the leading 1
   xO (resp. xH) represents the bit 0 (resp. 1)
   binary numbers are represented in signed-magnitude notation, with the LSB first
*)
Fixpoint pos2lst p :=
  match p with
    | xI p' => true :: pos2lst p'
    | xO p' => false :: pos2lst p'
    | xH => [:: true]
  end.

Lemma pos2lst_inj : forall p q, pos2lst p = pos2lst q -> p = q.
Proof.
elim.
- move=> p Hp [] //.
  + move=> q [] Hq. by rewrite (Hp q).
  + case=> Hq; by case: p Hp Hq.
- move=> p Hp [] //.
  move=> q [] Hq. by rewrite (Hp q).
- case=> //; by case.
Qed.

Lemma pos2lst_size_pos : forall p, (O < size (pos2lst p))%nat.
Proof. elim => // p Hp /=; by apply lt_O_Sn. Qed.

Lemma pos2lst_O : forall p, ~ pos2lst p = zeros (size (pos2lst p)).
Proof. elim=> // p Hp; contradict Hp; by case: Hp. Qed.

Lemma pos2lst_nil : forall p, pos2lst p <> [::]. Proof. case => //=. Qed.

Lemma pos2lst_len : forall p m, Zpos p < 2 ^^ m -> (size (pos2lst p) <= m)%nat.
Proof.
elim.
- move=> p Hp [|m] H /=; first by inversion H.
  rewrite ltnS; apply Hp.
  rewrite Zpos_xI ZpowerS in H; omega.
- move=> p Hp [|m] H /=; first by inversion H.
  rewrite ltnS; apply Hp.
  rewrite Zpos_xO ZpowerS in H; omega.
- move=> [|m] Hp /=; [by inversion Hp | done].
Qed.

Lemma pos2lst_len2 : forall p m, 2 ^^ m <= Zpos p -> (m < size (pos2lst p))%nat.
Proof.
elim => [p IH m Hm /=|p IH m Hm /=|m Hm].
- rewrite Zpos_xI in Hm.
  destruct m.
  + ssromega.
  + rewrite ltnS; apply IH.
    rewrite ZpowerS in Hm; omega.
- rewrite (Zpos_xO p) in Hm.
  destruct m.
  + ssromega.
  + rewrite ltnS; apply IH.
    erewrite ZpowerS in Hm; omega.
- destruct m => //.
  rewrite ZpowerS in Hm.
  move: (expZ_gt0 m) => ?; omega.
Qed.

Lemma Zpos_Zpower : forall m p, Zpos p = 2 ^^ m -> rev (pos2lst p) = true :: zeros m.
Proof.
elim.
- move=> p /=; by case => -> //.
- move=> n Hn [p|p|] Hp.
  + have Habsurd : Zodd (Zneg (xI p)) by auto.
    have H : (Zeven ( - (2 ^^ n.+1))) by rewrite ZpowerS Zopp_mult_distr_r; by apply Zeven_2.
    apply Zeven_not_Zodd in H.
    rewrite -Hp in H; contradiction.
  + rewrite Zpos_xO ZpowerS in Hp.
    rewrite rev_cons -cats1 Hn; last by omega.
    by rewrite /= -nseqS.
  + have Habsurd : 2 <= 2 ^^ n.+1.
      rewrite {1}(_ : 2 = 2 ^^ 1) //.
      apply/leZP; by rewrite Zpower_2_le.
    rewrite -Hp{Hp} in Habsurd.
    have : ~ (2 <= 1) by auto.
    by move/(_ Habsurd).
Qed.

Lemma Zneg_Zpower m p : Zneg p = - 2 ^^ m -> rev (pos2lst p) = true :: zeros m.
Proof. move=> H. apply Zpos_Zpower. rewrite -Zopp_neg; omega. Qed.

Lemma Zpos_Zpower_m1 : forall m p, Zpos p = 2 ^^ m - 1 -> rev (pos2lst p) = ones m.
Proof.
elim=> // n Hn [p|p|] Hp.
+ rewrite rev_cons -cats1 Hn; last by rewrite Zpos_xI ZpowerS in Hp; omega.
  by rewrite -nseqS.
+ have Habsurd : Zeven (Zpos p~0) by rewrite Zpos_xO; apply Zeven_2.
  have H : Zodd (2 ^^ n.+1 - 1).
    apply Zeven_plus_Zodd; [by apply Zeven_power | done].
  apply Zeven_not_Zodd in H => //.
  by rewrite -Hp.
+ rewrite ZpowerS in Hp.
  destruct n => //.
  have H : (1 < 2 * 2 ^^ n.+1 - 1).
    apply (@leZ_ltZ_trans (2 * 2 ^^ O - 1)) => //.
    apply/ltZ_sub2r/ltZ_pmul2l => //; exact: expZ_2_lt.
  by move: H; rewrite -Hp => /ltZZ.
Qed.

Definition Z2u n :=
  match n with
    | Z0 => [::]
    | Zpos p => let l := pos2lst p in rev l
    | _ => [::]
  end.

Lemma Z2u_2 : forall z, 0 <= z -> Z2u (2 * z + 1) = Z2u z ++ [:: true].
Proof.
case=> //.
by elim=> //= p IH Hp; by rewrite !rev_cons /= -!cats1.
Qed.

Lemma Z2u_2_0 : forall z, 0 < z -> Z2u (2 * z) = Z2u z ++ [:: false].
Proof.
case=> //.
by elim=> //= p IH Hp; by rewrite !rev_cons /= -!cats1.
Qed.

Lemma Z2u_2_Zpower : forall k, Z2u (2 ^^ k) = true :: zeros k.
Proof.
elim=> // n IH.
rewrite /Z2u.
move Hz : (_ ^^ _) => z.
destruct z => //.
move: (expZ_gt0 n.+1); rewrite Hz; by inversion 1.
by rewrite (Zpos_Zpower (n.+1)).
move: (expZ_gt0 n.+1); rewrite Hz; by inversion 1.
Qed.

Lemma Z2u_2_Zpower_m1 : forall k, Z2u (2 ^^ k - 1) = ones k.
Proof.
elim=> // n IH.
rewrite /Z2u.
move Hz : (_ ^^ _ - 1) => z.
destruct z => //.
have X : 2 ^^ n.+1 - 1 <> 0.
  rewrite ZpowerS.
  move: (expZ_gt0 n) => ?; omega.
contradiction.
apply Zpos_Zpower_m1 => //.
have X : 0 < 2 ^^ n.+1 - 1.
  rewrite ZpowerS.
  move: (expZ_gt0 n) => ?; omega.
rewrite Hz in X.
by destruct p.
Qed.

Lemma Z2u_nil : forall z, 0 <= z -> Z2u z = [::] -> z = 0.
Proof.
elim => // p _.
rewrite (_ : [::] = rev [::]) //.
move/(congr1 rev).
rewrite /= !revK.
by move: (pos2lst_nil p).
Qed.

Lemma Z2u_inj : forall a b, 0 <= a -> 0 <= b -> Z2u a = Z2u b -> a = b.
Proof.
case.
- move=> b _ Hb H.
  symmetry; by apply Z2u_nil.
- move=> p; case=> //=.
  + move=> _ _.
    rewrite (_ : [::] = rev [::]) //.
    move/(congr1 rev).
    rewrite /= !revK.
   by move: (pos2lst_nil p).
  + move=> q _ _.
    move/(congr1 (fun x => rev x)).
    rewrite /= !revK.
    by move/pos2lst_inj => ->.
- move=> p b H.
  move: (Zlt_neg_0 p) => ?; omega.
Qed.

Lemma u2Z_rev_poslst: forall p, .[ rev (pos2lst p) ]u = Zpos p.
Proof.
elim => //= p H; rewrite rev_cons -cats1 u2Z_app u2Z_app_zeros /= H.
- by rewrite Zpos_xI mulZC.
- by symmetry; rewrite Zpos_xO mulZC addZ0.
Qed.

Lemma Z2uK : forall n, 0 <= n -> .[ Z2u n ]u = n.
Proof.
move=> n.
move/Z_le_lt_eq_dec => [H | H].
- destruct n => //=.
  by apply u2Z_rev_poslst.
- by subst n.
Qed.

Lemma Z2u_size z m : z < 2 ^^ m -> (size (Z2u z) <= m)%nat.
Proof.
move=> Hnm.
elim (Ztrichotomy z 0) => [H | [H|H] ].
- by destruct z => //=.
- by rewrite H /=.
- destruct z => //=.
  rewrite size_rev.
  by apply pos2lst_len.
Qed.

Lemma u2Z_not_zeros l : l <> zeros (size l) -> 0 < u2Z l.
Proof.
move=> H.
move: (min_u2Z l).
case/Z_le_lt_eq_dec => X //.
symmetry in X; move/(u2Z_zeros_inv _ l (refl_equal _)) : X => /=.
by move/H.
Qed.

Lemma u2ZK : forall n (l : list bool) (Hlst : size l = n),
  Z2u (u2Z l) = erase_leading_zeros l.
Proof.
elim; first by case.
move=> n IHn l // H.
have [hd [tl Hl]] : exists hd tl, l = hd ++ [:: tl].
  case/lastP : l H => // h t H.
  exists h, t; by rewrite cats1.
rewrite {1}Hl u2Z_app [zeros _]/= (_ : [:: false] = zeros 1) // u2Z_app_zeros [_ ^^ _]/= mulZC.
destruct tl.
- rewrite [u2Z [:: true]]/= Z2u_2; last by apply min_u2Z.
  rewrite IHn.
  rewrite Hl; by apply erase_leading_zeros_app.
  rewrite Hl size_cat addnC /= in H.
  by case: H.
- case: (zeros_dec hd) => X.
  by rewrite X u2Z_zeros /= Hl X -nseqS -/(zeros ((size hd).+1)) erase_leading_zeros_zeros.
  rewrite [u2Z [:: false]]/= addZ0 Z2u_2_0.
  rewrite IHn.
  by rewrite Hl erase_leading_zeros_app'.
  rewrite Hl size_cat /= addnC /= in H.
  by case: H.
  exact: u2Z_not_zeros.
Qed.

Lemma size_u2ZK n l : size l = n ->
  ohead l = Some true -> size (Z2u (u2Z l)) = n.
Proof. by move=> ln H; rewrite (@u2ZK n) // (size_erase_leading_zeros_eq n). Qed.

(** correctness of comparisons *)
Lemma ult_correct : forall n a b, size a = n -> size b = n ->
  ult a b = true -> .[ a ]u < .[ b ]u.
Proof.
elim=> //.
- case=> //; by case.
- move=> n IH [|ha ta] [|hb tb] //.
  case=> Ha; case=> Hb.
  case: ha; case: hb => //=.
  + move/(IH _ _ Ha Hb) => ?; by rewrite Ha Hb ltZ_add2l.
  + move=> _.
    apply (@ltZ_leZ_trans (2 ^^ n)).
    apply max_u2Z.
    by rewrite Ha.
    rewrite Hb.
    move: (min_u2Z tb) => ?; omega.
  - by apply IH.
Qed.

Lemma ult_correct_alt : forall n m a b, size a = n -> size b = m ->
  forall p, p = max n m ->
    ult (zext (p - n)%nat a) (zext (p - m)%nat b) = true ->
    .[ zext (p - n)%nat a ]u < .[ zext (p - m)%nat b ]u.
Proof.
move=> n m a b H H0 p H1 H2.
apply ult_correct with p.
- rewrite (size_zext n) // addnC addnBA.
  by rewrite addnC addnK.
  by rewrite H1; apply/leP/le_max_l.
- rewrite (size_zext m) // addnC addnBA.
  by rewrite addnC addnK.
  by rewrite H1; apply/leP/le_max_r.
- exact H2.
Qed.

Definition pos_lt (a b : positive) : bool :=
  let a' := rev (pos2lst a) in
  let b' := rev (pos2lst b) in
  let max_len := max (size a') (size b') in
  let a'' := zext (max_len - size a') a' in
  let b'' := zext (max_len - size b') b' in
  ult a'' b''.

Lemma pos_lt_correct' : forall p q, pos_lt p q = true -> Zpos p < Zpos q.
Proof.
move=> p q H.
rewrite -2!u2Z_rev_poslst.
rewrite -(zext_correct (max (size (rev (pos2lst p))) (size (rev (pos2lst q))) - size (rev (pos2lst p))) (rev (pos2lst p))).
rewrite -(zext_correct (max (size (rev (pos2lst p))) (size (rev (pos2lst q))) - size (rev (pos2lst q)))(rev (pos2lst q))).
by apply ult_correct_alt.
Qed.

Lemma ult_correct' : forall n a b, size a = n -> size b = n ->
  .[ a ]u < .[ b ]u -> ult a b = true.
Proof.
elim.
- by case=> //; case.
- move=> n IH [|ha ta] [|hb tb] //.
  case=> Ha; case=> Hb.
  case: ha; last first; case: hb; last first => //=.
  + move=> H.
    rewrite Ha in H.
    have X : .[tb]u < 2^^n by apply max_u2Z => //; rewrite Hb.
    have Z : 2 ^^ n < .[ tb ]u by move: (min_u2Z ta) => ?; omega.
    by move: (ltZ_trans X Z) => /ltZZ.
  + rewrite Ha Hb => /ltZ_add2l; by auto.
  + exact: IH.
Qed.

(** properties of bits.add' / bits.add w.r.t. u2Z *)

Lemma add'_nat : forall n a b carry, size a = n -> size b = n ->
  .[ rev a ]u + .[ rev b ]u + .[ [:: carry] ]u < 2 ^^ n ->
  .[ rev (add' a b carry) ]u =
  .[ rev a ]u + .[ rev b ]u + .[ [:: carry] ]u.
Proof.
induction n.
- move=> [|ha ta] // [|hb tb] // [|] // H H0 H1.
- move=> [| b0 a] // [|b b1] // carry [H] [H0] H1.
  destruct b0; destruct b; destruct carry; (
    simpl;
      rewrite !rev_cons -!cats1 ZpowerS in H1;
        simpl rev in H1;
      rewrite !rev_cons -!cats1;
          repeat rewrite u2Z_last;
            repeat rewrite u2Z_last in H1;
              simpl u2Z;
                simpl u2Z in H1).
  + have H2 : u2Z (rev a) + u2Z (rev b1) + u2Z [:: true] < 2 ^^ n. rewrite /=; omega.
    move: (IHn _ _ true H H0 H2) => H3.
    rewrite /= in H3; omega.
  + have H2 : u2Z (rev a) + u2Z (rev b1) + u2Z [:: true] < 2 ^^ n. rewrite /=; omega.
    move: (IHn _ _ true H H0 H2) => H3.
    rewrite /= in H3; omega.
  + have H2 : u2Z (rev a) + u2Z (rev b1) + u2Z [:: true] < 2 ^^ n. rewrite /=; omega.
    move: (IHn _ _ true H H0 H2) => H3.
    rewrite /= in H3; omega.
  + have H2 : u2Z (rev a) + u2Z (rev b1) + u2Z [:: false] < 2 ^^ n. rewrite /=; omega.
    move: (IHn _ _ false H H0 H2) => H3.
    rewrite /= in H3; omega.
  + have H2 : u2Z (rev a) + u2Z (rev b1) + u2Z [:: true] < 2 ^^ n. rewrite /=; omega.
    move: (IHn _ _ true H H0 H2) => H3.
    rewrite /= in H3; omega.
  + have H2 : u2Z (rev a) + u2Z (rev b1) + u2Z [:: false] < 2 ^^ n. rewrite /=; omega.
    move: (IHn _ _ false H H0 H2) => H3.
    rewrite /= in H3; omega.
  + have H2 : u2Z (rev a) + u2Z (rev b1) + u2Z [:: false] < 2 ^^ n. rewrite /=; omega.
    move: (IHn _ _ false H H0 H2) => H3.
    rewrite /= in H3; omega.
  + have H2 : u2Z (rev a) + u2Z (rev b1) + u2Z [:: false] < 2 ^^ n. rewrite /=; omega.
    move: (IHn _ _ false H H0 H2) => H3.
    rewrite /= in H3; omega.
Qed.

(** The hardware addition behaves like the mathematical addition only
when non-overflow conditions are met: *)
Lemma add_nat n a b : size a = n -> size b = n -> .[ a ]u + .[ b ]u < 2 ^^ n ->
  .[ add a b false ]u = .[ a ]u + .[ b ]u.
Proof.
move=> Ha Hb H.
rewrite /add (add'_nat n).
rewrite 2!revK /=; ring.
by rewrite size_rev.
by rewrite size_rev.
rewrite 2!revK /=; omega.
Qed.

Lemma u2Z_add' : forall n l k carry, size l = n -> size k = n ->
  .[ rev (add' (l ++ [:: false]) (k ++ [:: false]) carry) ]u =
  .[ rev l ]u + .[ rev k ]u + .[ [:: carry] ]u.
Proof.
induction n.
- by move=> [|hl tl] // [|hk tk].
- move=> [|hl tl] // [|hk tk] // carry [H] [H0].
  destruct hl; destruct hk; destruct carry; (simpl;
      rewrite !rev_cons -!cats1;
      repeat rewrite u2Z_last;
        rewrite IHn; auto;
          simpl u2Z;
            ring).
Qed.

Lemma u2Z_add n l k carry : size l = n -> size k = n ->
  .[ add (false :: l) (false :: k) carry ]u = .[ l ]u + .[ k ]u + .[ [:: carry] ]u.
Proof.
move=> H H0.
rewrite /add /= !rev_cons -!cats1 (u2Z_add' n); last 2 first.
  by rewrite size_rev.
  by rewrite size_rev.
rewrite 2!revK; by destruct carry.
Qed.

Lemma add'_nat_overflow : forall n (a b : list bool) carry,
  size a = n -> size b = n ->
  2 ^^ n <= .[ rev a ]u + .[ rev b ]u  + .[ [:: carry] ]u ->
  .[ rev (add' a b carry) ]u + 2 ^^ n =
  .[ rev a ]u + .[ rev b ]u + .[ [:: carry] ]u.
Proof.
induction n.
- move=> [|ha ta] // [|hb tb] // [|] _ _ //= H; omega.
- move=> [|b0 a] // [|b b1] // carry [H] [H0] H1.
  destruct b0; destruct b; destruct carry; (
    simpl add';
      simpl u2Z in H1;
      rewrite !rev_cons -!cats1 in H1;
        simpl rev;
      rewrite !rev_cons -!cats1;
          repeat rewrite u2Z_last;
            repeat rewrite u2Z_last in H1;
              simpl u2Z in H1;
                simpl u2Z;
                  rewrite ZpowerS in H1).
  + have H2 : 2 ^^ n <= u2Z (rev a) + u2Z (rev b1) + u2Z [:: true] by simpl; omega.
    move: (IHn _ _ _ H H0 H2) => H3.
    rewrite /= in H3.
    rewrite ZpowerS; omega.
  + have H2 : 2 ^^ n <= u2Z (rev a) + u2Z (rev b1) + u2Z [:: true] by simpl; omega.
    move: (IHn _ _ true H H0 H2) => H3.
    rewrite /= in H3.
    rewrite ZpowerS; omega.
  + have H2 : 2 ^^ n <= u2Z (rev a) + u2Z (rev b1) + u2Z [:: true] by simpl; omega.
    move: (IHn _ _ true H H0 H2) => H3.
    rewrite /= in H3.
    rewrite ZpowerS; omega.
  + have H2 : 2 ^^ n <= u2Z (rev a) + u2Z (rev b1) + u2Z [:: false] by simpl; omega.
    move: (IHn _ _ false H H0 H2) => H3.
    rewrite /= in H3.
    rewrite ZpowerS; omega.
  + have H2 : 2^^n <= u2Z (rev a) + u2Z (rev b1) + u2Z [:: true] by simpl; omega.
    move: (IHn _ _ true H H0 H2) => H3.
    rewrite /= in H3.
    rewrite ZpowerS; omega.
  + have H2 : 2^^n <= u2Z (rev a) + u2Z (rev b1) + u2Z [:: false] by simpl; omega.
    move: (IHn _ _ false H H0 H2) => H3.
    rewrite /= in H3.
    rewrite ZpowerS; omega.
  + have H2 : 2^^n <= u2Z (rev a) + u2Z (rev b1) + u2Z [:: false] by simpl; omega.
    move: (IHn _ _ false H H0 H2) => H3.
    rewrite /= in H3.
    rewrite ZpowerS; omega.
  + have H2 : 2^^n <= u2Z (rev a) + u2Z (rev b1) + u2Z [:: false] by simpl; omega.
    move: (IHn _ _ false H H0 H2) => H3.
    rewrite /= in H3.
    rewrite ZpowerS; omega.
Qed.

Lemma add_overflow n a b : size a = n -> size b = n -> 2 ^^ n <= .[ a ]u + .[ b ]u ->
  .[ add a b false ]u + 2 ^^ n = .[ a ]u + .[ b ]u.
Proof.
move=> Ha Hb H.
rewrite /add (add'_nat_overflow n).
rewrite 2!revK /=; ring.
by rewrite size_rev.
by rewrite size_rev.
rewrite 2!revK /=; omega.
Qed.

(** subtraction *)

Lemma sub'_nat : forall n (a b : list bool) borrow,
  size a = n -> size b = n ->
  (0 < n)%nat ->
  .[ a ]u >= .[ b ]u + .[ [:: borrow] ]u ->
  .[ rev (sub' (rev a) (rev b) borrow) ]u + .[ [:: borrow] ]u + .[ b ]u = .[ a ]u.
Proof.
case => [ // | n].
elim: n => [ | n IHn].
+ case => // => hda.
  case => //.
  case => // => hdb.
  case => //.
  case => // => _ _ _ /=.
  move: hda hdb; case => //=; case => //=; move=> *; omega.
  move: hda hdb; case => //=; case => //=; move=> *; omega.
+ move=> a b borrow H H0 _.
  case/lastP : a H => // hda tla.
  rewrite size_rcons; case => H3.
  case/lastP : b H0 => // hdb tlb.
  rewrite size_rcons; case => H4.
  rewrite -!cats1.
  do ! rewrite u2Z_app u2Z_app_zeros.
  rewrite /=.
  move: tla H3; case => // => H3.
  * move: tlb H4; case => // => H4.
    - move: borrow; case => // => H2.
      + rewrite !rev_cat /= !rev_cons -cats1 /= u2Z_app u2Z_app_zeros /=.
        by rewrite -(IHn _ _ true H3 H4) /=; try omega.
      + rewrite !rev_cat /= !rev_cons -cats1 /= u2Z_app u2Z_app_zeros /=.
        by rewrite -(IHn _ _ false H3 H4) /=; try omega.
    - move: borrow; case => // => H2.
      + rewrite !rev_cat /= !rev_cons -cats1 /= u2Z_app u2Z_app_zeros /=.
        by rewrite -(IHn _ _ false H3 H4) /=; try omega.
      + rewrite !rev_cat /= !rev_cons -cats1 /= u2Z_app u2Z_app_zeros /=.
        by rewrite -(IHn _ _ false H3 H4) /=; try omega.
  * move: tlb H4; case => // => H4.
    - move: borrow; case => // => H2.
      + rewrite !rev_cat /= !rev_cons -cats1 /= u2Z_app u2Z_app_zeros /=.
        by rewrite -(IHn _ _ true H3 H4) /=; try omega.
      + rewrite !rev_cat /= !rev_cons -cats1 /= u2Z_app u2Z_app_zeros /=.
        by rewrite -(IHn _ _ true H3 H4) /=; try omega.
    - move: borrow; case => // => H2.
      + rewrite !rev_cat /= !rev_cons -cats1 /= u2Z_app u2Z_app_zeros /=.
        by rewrite -(IHn _ _ true H3 H4) /=; try omega.
      + rewrite !rev_cat /= !rev_cons -cats1 /= u2Z_app u2Z_app_zeros /=.
        by rewrite -(IHn _ _ false H3 H4) /=; try omega.
Qed.

Lemma sub_nat n a b borrow : size a = n -> size b = n ->
  (0 < n)%nat ->
  .[ a ]u >= .[ b ]u + .[ [:: borrow] ]u ->
  .[ sub a b borrow ]u + .[ [:: borrow] ]u + .[ b ]u = .[ a ]u.
Proof. move=> Ha Hb Hn H; rewrite /sub. by apply sub'_nat with n. Qed.

Lemma sub'_nat_overflow : forall n (a b : list bool) borrow,
  size a = n -> size b = n ->
  (0 < n)%nat ->
  .[ a ]u < .[ b ]u + .[ [:: borrow] ]u ->
  .[ rev (sub' (rev a) (rev b) borrow) ]u + .[ [:: borrow] ]u = .[ a ]u + 2 ^^ n - .[ b ]u.
Proof.
case => [ // | n].
elim: n => [ | n IHn].
+ case => // => hda.
  case => //.
  case => // => hdb.
  case => //.
  case => // => _ _ _ /=.
  move: hda hdb; case => //=; case => //=; move=> *; omega.
  move: hda hdb; case => //=; case => //=; move=> *; omega.
+ move=> a b borrow H H0 _.
  case/lastP : a H => // hda tla.
  rewrite size_rcons; case => H3.
  case/lastP : b H0 => // hdb tlb.
  rewrite size_rcons; case => H4.
  rewrite -!cats1.
  do ! rewrite u2Z_app u2Z_app_zeros.
  rewrite (ZpowerS 2 n.+1).
  rewrite {4}[expZ]lock {4}[Zmult]lock /= -!lock.
  move: tla H3; case => // => H3.
  * move: tlb H4; case => // => H4.
    - move: borrow; case => // => H2.
      + ring_simplify.
        apply trans_eq with (2 * (.[ hda ]u + 2 ^^ n.+1 - .[hdb ]u)); last by omega.
        rewrite -(IHn _ _ true H3 H4) //; try by rewrite /=; omega.
        rewrite !rev_cat rev_cons -!cats1 !cat0s [LHS]/= rev_cons [LHS]/=.
        rewrite -cats1 u2Z_app u2Z_app_zeros [Zmult]lock /= -lock; ring.
      + ring_simplify.
        apply trans_eq with (2 * (.[ hda ]u + 2 ^^ n.+1 - .[hdb ]u)); last by omega.
        rewrite -(IHn _ _ false H3 H4) //; try by rewrite /=; omega.
        rewrite !rev_cat rev_cons -!cats1 !cat0s [LHS]/= rev_cons [LHS]/=.
        rewrite -cats1 u2Z_app u2Z_app_zeros [Zmult]lock /= -lock; ring.
    - move: borrow; case => // => H2.
      + ring_simplify.
        apply trans_eq with (2 * (.[ hda ]u + 2 ^^ n.+1 - .[hdb ]u) + 1); last by omega.
        rewrite -(IHn _ _ false H3 H4) //; try by rewrite /=; omega.
        rewrite !rev_cat rev_cons -!cats1 !cat0s [LHS]/= rev_cons [LHS]/=.
        rewrite -cats1 u2Z_app u2Z_app_zeros [Zmult]lock /= -lock; ring.
      + ring_simplify.
        apply trans_eq with (2 * (.[ hda ]u + 2 ^^ n.+1 - .[hdb ]u) + 1); last by omega.
        rewrite -(IHn _ _ false H3 H4) //; try by rewrite /=; omega.
        rewrite !rev_cat rev_cons -!cats1 !cat0s [LHS]/= rev_cons [LHS]/=.
        rewrite -cats1 u2Z_app u2Z_app_zeros [Zmult]lock /= -lock; ring.
  * move: tlb H4; case => // => H4.
    - move: borrow; case => // => H2.
      + ring_simplify.
        apply trans_eq with (2 * (.[ hda ]u+ 2 ^^ n.+1 - .[hdb ]u) - 1); last by omega.
        rewrite -(IHn _ _ true H3 H4) //; try by rewrite /=; omega.
        rewrite !rev_cat rev_cons -!cats1 !cat0s [LHS]/= rev_cons [LHS]/=.
        rewrite -cats1 u2Z_app u2Z_app_zeros [Zmult]lock /= -lock; ring.
      + ring_simplify.
        apply trans_eq with (2 * (.[ hda ]u+ 2 ^^ n.+1 - .[hdb ]u) - 1); last by omega.
        rewrite -(IHn _ _ true H3 H4) //; try by rewrite /=; omega.
        rewrite !rev_cat rev_cons -!cats1 !cat0s [LHS]/= rev_cons [LHS]/=.
        rewrite -cats1 u2Z_app u2Z_app_zeros [Zmult]lock /= -lock; ring.
    - move: borrow; case => // => H2.
      + ring_simplify.
        apply trans_eq with (2 * (.[hda ]u + 2 ^^ n.+1 - .[hdb ]u)); last by omega.
        rewrite -(IHn _ _ true H3 H4) //; try by rewrite /=; omega.
        rewrite !rev_cat rev_cons -!cats1 !cat0s [LHS]/= rev_cons [LHS]/=.
        rewrite -cats1 u2Z_app u2Z_app_zeros [Zmult]lock /= -lock; ring.
      + ring_simplify.
        apply trans_eq with (2 * (.[ hda ]u + 2 ^^ n.+1 - .[hdb ]u)); last by omega.
        rewrite -(IHn _ _ false H3 H4) //; try by rewrite /=; omega.
        rewrite !rev_cat rev_cons -!cats1 !cat0s [LHS]/= rev_cons [LHS]/=.
        rewrite -cats1 u2Z_app u2Z_app_zeros [Zmult]lock /= -lock; ring.
Qed.

Lemma sub_nat_overflow n a b borrow : size a = n -> size b = n ->
  (0 < n)%nat ->
  .[ a ]u < .[ b ]u + .[ [:: borrow] ]u ->
  .[ sub a b borrow ]u + .[ [:: borrow] ]u = .[ a ]u + 2^^n - .[ b ]u.
Proof. move=> Ha Hb Hn H. rewrite /sub. apply sub'_nat_overflow; by auto. Qed.

(** correctness of adjust *)

Lemma adjust_u2Z: forall n lst, .[ lst ]u < 2 ^^ n ->
  .[ adjust_u lst n ]u = .[ lst ]u.
Proof.
move=> n lst H.
have [/leP H0|H0] : (size lst >= n \/ size lst < n)%coq_nat by omega.
- elim (u2Z_power_inv _ _ _ H0 (refl_equal _) H) => x Hx.
  rewrite /adjust_u.
  have H' : (size lst < n = false)%nat by apply/ltP; ssromega.
  rewrite {}H' Hx drop_cat u2Z_app zeros_app u2Z_zeros //.
  by rewrite -Hx size_nseq ltnn subnn drop0.
- rewrite /adjust_u.
  move: H0; move/ltP => H0; rewrite H0 {H0}.
  by rewrite /zext u2Z_app zeros_app u2Z_zeros.
Qed.

Lemma skipn_Zmod : forall m lst n, (n <= m)%nat -> size lst = m ->
  .[ drop n lst ]u = .[lst]u mod 2 ^^ (m - n).
Proof.
induction m.
- by destruct lst.
- move=> [| hd tl] //.
  move=> n Hnm H; rewrite /= in H; case:H=>H.
  destruct n.
  + rewrite drop0.
    rewrite subn0.
    have X : .[hd :: tl ]u < 2^^(m.+1).
      apply max_u2Z.
      by rewrite /= H.
    rewrite Zmod_small //.
    split; [by apply min_u2Z | exact X].
  + rewrite ltnS in Hnm.
    simpl.
    destruct hd => //=.
    * rewrite IHm //.
      rewrite H -Zplus_mod_idemp_l subSS.
      suff : 2 ^^ m mod 2 ^^ (m - n) = 0 by move=> ->.
      have -> : 2 ^^ m = (2 ^^ n) * ( 2 ^^ (m - n)) by rewrite -ZpowerD addnBA // addnC addnK.
      by rewrite Z_mod_mult.
    * by rewrite IHm.
Qed.

Lemma adjust_u2Z_overflow n lst : 2 ^^ n <= .[ lst ]u ->
  .[ adjust_u lst n ]u = .[ lst ]u mod 2 ^^ n.
Proof.
move=> H.
move: (overflow_size_u2Z lst n H) => X.
rewrite /adjust_u.
move : (X); rewrite leqNgt; move/negbTE => ->.
rewrite (skipn_Zmod (size lst)) //.
- rewrite subKn //; by apply/leP.
- by rewrite leq_subr.
Qed.

Lemma zext_Z2u n m m' : n < 2 ^^ m ->
  zext m' (adjust_u (Z2u n) m.+1) = adjust_u (Z2u n) (m + m').+1.
Proof.
move/Z2u_size => H1.
rewrite /adjust_u.
rewrite ltnS H1.
have H3 : (size (Z2u n) < (m + m').+1)%nat.
  rewrite ltnS; apply: (leq_trans H1); by rewrite leq_addr.
rewrite H3 /zext.
destruct (size (Z2u n)).
- by rewrite /= -(cat1s false) catA -nseqS catA /= zeros_app addnC.
- rewrite subSS.
  have -> : (m - n0)%nat = (m - n0.+1).+1 by rewrite -subSn.
  rewrite catA zeros_app.
  suff : (m' + (m - n0.+1).+1 = (m + m').+1 - n0.+1)%nat by move=> ->.
  rewrite -subSn // 2!subSS addnBA.
  by rewrite addnC.
  by rewrite ltnW.
Qed.

(** properties of cplt2_lst w.r.t. u2Z *)

Lemma u2Z_cplt2_O : forall a, size a = O -> a <> zeros O ->
  .[ cplt2 a ]u = 2 ^^ O - .[ a ]u.
Proof. by case. Qed.

Lemma u2Z_cplt2_1 : forall a, size a = 1%nat -> a <> zeros 1 ->
  .[ cplt2 a ]u = 2 ^^ 1 - .[ a ]u.
Proof. move=> [|[|] [|hd' tl] ] // Hlena Ha_isnot_i. Qed.

Lemma u2Z_cplt2' : forall n a, size a = n.+2 -> a <> zeros n.+2 ->
  .[ cplt2 a ]u = 2 ^^ n.+2 - .[ a ]u.
Proof.
induction n; intros.
- destruct a => //.
  destruct a => //.
  destruct a => //.
  destruct b; by destruct b0.
- destruct a => //.
  destruct b.
  + simpl in H; injection H; clear H; intro.
    have [H1 | H1] : a <> zeros n.+2 \/ a = zeros n.+2.
      generalize (dec_equ_lst_bit' a (zeros n.+2)); tauto.
    * rewrite cplt2_prop.
      - rewrite u2Z_false u2Z_true IHn // H //.
        lapply (max_u2Z n.+2 a); last by rewrite H.
        intro.
        rewrite -(Zpower_plus n.+2); omega.
      - case=> x H2.
        rewrite H2 size_nseq in H.
        subst x.
        by move: (H1 H2).
      - intro.
        case: H2 => x [H3].
        rewrite H3 size_nseq in H.
        subst x.
        by move: (H1 H3).
    * rewrite H1 cplt2_weird u2Z_true u2Z_zeros size_nseq -(Zpower_plus n.+2); ring.
  + case: H => H.
    rewrite cplt2_prop.
    * rewrite u2Z_true size_cplt2 IHn //; last first.
        intro X; apply H0; by rewrite X.
      rewrite H // u2Z_false.
      lapply (max_u2Z n.+2 a); last by rewrite H.
      move=> H1.
      rewrite -(Zpower_plus n.+2); omega.
    * case=> x H1.
      rewrite H1 size_nseq in H.
      subst x.
      apply H0; by rewrite H1.
    * by case.
Qed.

Lemma u2Z_cplt2 : forall n l, size l = n -> l <> zeros n ->
  .[ cplt2 l ]u = 2 ^^ n - .[ l ]u.
Proof.
destruct n.
apply u2Z_cplt2_O.
destruct n.
by apply u2Z_cplt2_1.
by apply u2Z_cplt2'.
Qed.

(** correctness of 2k-multiplication (given k-long inputs, the result fits in 2k) *)

Lemma umul_nat: forall n l k, size l = n.+1 -> size k = n.+1 ->
  .[ umul l k ]u = .[ l ]u * .[ k ]u.
Proof.
induction n.
- destruct l; destruct k; intros; try discriminate.
  destruct l; destruct k; intros; try discriminate.
  destruct b; destruct b0; auto.
- intros.
  destruct l; try discriminate.
  destruct k; try discriminate.
  destruct b; destruct b0; case:H => H; case:H0 => H0.
  + rewrite umul_leading_true /= (u2Z_add (n.+1 + n.+1).+1).
    rewrite /= (u2Z_add (n.+1 + n.+1)).
    rewrite /= IHn // u2Z_app_zeros u2Z_app_zeros size_cat size_nseq ZpowerD.
    ring.
    by rewrite size_cat size_nseq H H0.
    by rewrite size_umul // H H0.
    by rewrite /= size_cat size_nseq H H0.
    rewrite (size_add (n.+2 + size k)).
    by rewrite H0.
    by rewrite /= size_cat size_nseq H H0.
    by rewrite /= size_umul H H0.
  + rewrite umul_leading_true /= (u2Z_add (S (S n + S n))).
    rewrite /= u2Z_app_zeros IHn //; ring.
    by rewrite /= size_cat size_nseq H H0.
    by rewrite /= size_umul H H0.
  + rewrite umul_leading_false //.
    rewrite /= (u2Z_add (n.+1 + n.+1)).
    rewrite u2Z_app_zeros /= IHn //.
    ring.
    by rewrite size_cat size_nseq H H0.
    by rewrite size_umul // H H0.
    intro; subst l; discriminate.
  + rewrite umul_leading_false//.
    by rewrite /= IHn.
    by move=> abs; rewrite abs in H.
Qed.

(** correctness of k-multiplication (given k-long inputs, returns a result in k) *)

Lemma mul_nat : forall n a b, size a = n -> size b = n ->
  .[ a ]u * .[ b ]u < 2 ^^ n ->
  .[ adjust_u (umul a b) n ]u = .[ a ]u * .[ b ]u.
Proof.
destruct n.
- case=> //. by case.
- move=> a b H H0 H1.
  rewrite -(umul_nat n) // in H1.
  by rewrite -(umul_nat n) // adjust_u2Z.
Qed.

(** properties of shift-left w.r.t. u2Z *)

Lemma shl_u2Z k n l : size l = n ->
  forall k', (k + k' <= n)%nat ->
    .[ l ]u < 2 ^^ k' -> .[ shl k l ]u = .[ l ]u * 2 ^^ k.
Proof.
move=> H k' H0 H1.
have [lst' Hlst] : exists lst'', l = zeros (n - k') ++ lst''.
  apply u2Z_power_inv => //; rewrite -plusE in H0; ssromega.
rewrite Hlst.
rewrite (_ : n - k' = k + (n - (k + k')))%nat; last first.
  rewrite -!minusE -!plusE in H0 *; ssromega.
rewrite -{1}zeros_app -{1}catA shl_zeros_cat -{1}catA
  {1}u2Z_app zeros_app u2Z_zeros /=.
symmetry.
by rewrite -u2Z_app_zeros -catA {1}u2Z_app zeros_app u2Z_zeros.
Qed.

Lemma shl_u2Z_overflow : forall l a k, l = size a ->
  (k < l)%nat -> .[ shl k a ]u = (.[a]u * 2 ^^ k) mod 2 ^^ l.
Proof.
elim.
- by move=> [|_ _] //.
- move=> n IH [|hd tl] // k [H] Hk.
  destruct k.
  + rewrite [shl _ _]/= [2 ^^ 0]/= Zmult_1_r.
    move: (max_u2Z (n.+1) (hd :: tl)) => X.
    rewrite (Zmod_small (.[hd :: tl]u) (2 ^^ n.+1)) //.
    split.
    * by apply min_u2Z.
    * apply X.
      by rewrite /= -H.
  + rewrite [shl _ _]/= u2Z_app u2Z_app_zeros [size _]/= [ .[ [:: false] ]u ]/=.
    rewrite IH //; last first.
  * ring_simplify.
    have X : 2 ^^ n = 2 ^^ (n - k) * 2 ^^ k by rewrite -ZpowerD subnK // ltnW.
    rewrite X Zmult_mod_distr_r.
    have Y : 2 ^^ n.+1 = 2 ^^ (n.+1 - k.+1) * 2 ^^ k.+1 by rewrite -ZpowerD subnK // ltnW.
    rewrite Y Zmult_mod_distr_r -mulZA -ZpowerD addnC subSS.
    destruct hd.
    - rewrite u2Z_true -H -Zplus_mod_idemp_l.
      suff : 2 ^^ n mod 2 ^^ (n - k) = 0 by move=> ->.
      have -> : 2 ^^n = 2 ^^ (n - k) * 2 ^^ k by rewrite -ZpowerD subnK // ltnW.
      by rewrite mulZC Z_mod_mult.
    - by rewrite u2Z_false.
Qed.

Lemma shl_u2Z' : forall n lst, size lst = n ->
  forall l, u2Z lst < 2 ^^ l ->
    forall k, (k + l <= n)%nat ->
      u2Z (shl k lst) <= 2 ^^ (l + k) - 2 ^^ k.
Proof.
induction k.
- rewrite /= addn0; omega.
- move=> H1.
  have H2 : (k + l <= n)%nat by rewrite ltnW.
  move/IHk : H2 => H2 {IHk}.
  rewrite (shl_u2Z k n lst H l) // in H2; last by rewrite ltnW.
  rewrite (shl_u2Z k.+1 n lst H l) //.
  cutrewrite (2 ^^ (l + k.+1) - 2 ^^ k.+1 = 2 * (2 ^^ (l + k) - 2 ^^ k)); last first.
    rewrite addnS !ZpowerS; omega.
  rewrite ZpowerS mulZC -mulZA (mulZC (2 ^^ k)); omega.
Qed.

(** properties of shift-left-extend w.r.t. lst2nat *)

Lemma shl_ext_u2Z : forall k n lst, size lst = n ->
  .[ shl_ext k lst ]u = .[ lst ]u * 2 ^^ k.
Proof.
destruct k; intros.
unfold shl_ext.
rewrite /= cats0; ring.
by rewrite /shl_ext u2Z_app_zeros.
Qed.

Lemma shl_ext_u2Z' : forall n lst, size lst = n ->
  forall l, .[ lst ]u < 2 ^^ l ->
    forall k, .[ shl_ext k lst ]u <= 2 ^^ (l + k) - 2 ^^ k.
Proof.
unfold shl_ext.
induction k.
rewrite /= cats0 addn0; omega.
cutrewrite (lst ++ zeros k.+1 = (lst ++ zeros k) ++ zeros 1); last by rewrite /= -catA -nseqS.
rewrite u2Z_app_zeros addnS 2!ZpowerS [2 ^^ 0]/= ZpowerS; omega.
Qed.

(** properties of shrl_lst / u2Z *)

Lemma shrl_lst_shl n l : size l = n -> forall m, u2Z l < 2 ^^ m ->
  shrl (n - m) (shl (n - m) l) = l.
Proof.
move=> Hlenl m H.
case: (le_gt_dec m n) => X.
  move/leP in X.
  case: (u2Z_power_inv n l m X Hlenl H) => l' Hl'.
  rewrite Hl' shl_zeros_cat.
  rewrite (shrl_app_zeros _ m) //.
  move: Hlenl.
  rewrite Hl' size_cat /= size_nseq -minusE -plusE => ?; ssromega.
have : (n - m = O)%coq_nat by omega.
rewrite minusE => ->; by rewrite shrl_0.
Qed.

Lemma ult_shrl_overflow : forall k n lst, size lst = n -> (k < n)%nat ->
  ult lst (adjust_u (Z2u (2 ^^ k)) n) -> shrl k lst = zeros n.
Proof.
elim.
- case.
  + inversion 2.
  + rewrite [Z2u _]/=.
    move=> n lst Hlenlst _ H.
    rewrite (adjust_u_S'' (n.+1) 1 [:: true]) //= subSS subn0 in H.
    have X : (0 < size lst)%coq_nat by rewrite Hlenlst; apply lt_O_Sn.
    case/lastP : lst => // hd tl in X Hlenlst H * => {X}.
    apply (ult_correct n.+1) in H; last 2 first.
      by rewrite -Hlenlst.
      by rewrite size_cat /= size_nseq // addnC.
    rewrite (u2Z_app (zeros n)) zeros_app u2Z_zeros /= in H.
    have {}H : u2Z (rcons hd tl) = 0.
      move: (min_u2Z (rcons hd tl)) => ?; omega.
    by move/(u2Z_zeros_inv (n.+1)) : H => ->.
- move=> k IHk [|n].
  + by inversion 2.
  + move=> lst Hlenlst.
    rewrite ltnS => Hkn.
    have X : (0 < size lst)%coq_nat by rewrite Hlenlst; apply lt_O_Sn.
    case/lastP : lst => // hd tl in X Hlenlst * => {X}.
    rewrite size_rcons in Hlenlst; case: Hlenlst => Hlenlst.
    rewrite -cats1 shrl_S => H.
    rewrite (IHk n) //.
    rewrite Z2u_2_Zpower (adjust_u_S'' n.+1 k.+2) /= in H; last 2 first.
      by rewrite size_nseq.
      by rewrite ltnS.
    rewrite (_ : zeros _ ++ _ :: _ :: _ = (zeros (n - k.+1)%coq_nat ++ true :: zeros k) ++ false::nil) in H; last first.
      by rewrite -catA /= -nseqS.
    rewrite Z2u_2_Zpower (adjust_u_S'' n (S k)) //=; last by rewrite size_nseq.
    eapply ult_tail'; eauto.
    rewrite size_cat /= 2!size_nseq.
    by rewrite subnK.
Qed.

(** properties of s_extend w.r.t. u2Z/Z2u *)

Lemma sext_u2Z : forall n lst l, size lst = l -> 0 <= .[ lst ]u < 2 ^^ (predn l) ->
  .[ sext n lst ]u = .[ lst ]u.
Proof.
move => n [|[|] tl] l /= H H0.
- destruct n => //=.
  by rewrite u2Z_zeros.
- destruct l => //.
  case: H => H.
  rewrite H /= in H0.
  have H1 :  ~ (2 ^^ l + .[ tl ]u < 2 ^^ l).
    move: (min_u2Z tl) => ?; omega.
  tauto.
- by rewrite sext_0 u2Z_app zeros_app u2Z_zeros.
Qed.

Lemma sext_false: forall l n, .[ sext n (false :: l) ]u = .[ l ]u.
Proof. by induction n. Qed.

Lemma sext_true : forall n l, .[ sext n (true :: l) ]u = 2 ^^ (size l) * (2 ^^ n.+1 - 1) + .[ l ]u.
Proof.
induction n; intros.
- rewrite (_ : 2 ^^ 1 - 1 = 1) //=; ring.
- rewrite [u2Z _]/= size_sext IHn [size _]/= ZpowerD (ZpowerS 2 n.+1) 2!ZpowerS; ring.
Qed.

Lemma sext_Z2u n m m' : n < 2 ^^ m ->
  sext m' (adjust_u (Z2u n) m.+1) = adjust_u (Z2u n) (m + m').+1.
Proof.
move=> H0.
move: (Z2u_size _ _ H0) => H1.
rewrite /adjust_u.
rewrite ltnS H1.
have H3 : (size (Z2u n) < (m + m').+1)%nat.
  rewrite ltnS.
  apply: (leq_trans H1); by rewrite leq_addr.
rewrite /zext.
destruct (size (Z2u n)).
- by rewrite /= sext_0 catA zeros_app /= addnC.
- rewrite subSS.
  have -> : (m - n0)%nat = (m - n0.+1).+1 by rewrite -subSn.
  by rewrite /= sext_0 catA zeros_app H3 addnBA // addSn // addnC.
Qed.

(** interpretation of list bools as signed integers in two's complement notation *)

Definition s2Z (l : list bool) : Z :=
  match l with
    | nil => 0
    | false :: tl => .[ tl ]u
    | true :: tl => - 2 ^^ (size tl) + .[ tl ]u
  end.

Notation "'.[' l ']s'" := (s2Z l) : listbit_correct_scope.

Lemma s2Z_false : forall l, .[ false :: l ]s = .[ l ]u. Proof. done. Qed.

Lemma s2Z_true : forall l, .[ true :: l ]s = - 2 ^^ (size l) + .[ l ]u.
Proof. done. Qed.

Lemma s2Z_inj : forall n a b, size a = n -> size b = n ->
  .[ a ]s = .[ b ]s -> a = b.
Proof.
induction n; intros.
- destruct a => //.
  by destruct b.
- destruct a as [| a0 a]; try discriminate.
  case: H; intro.
  destruct b as [| b0 b]; try discriminate.
  case: H0; intro.
  destruct a0; destruct b0; last first.
  do 2 rewrite s2Z_false in H1.
  by rewrite (u2Z_inj n a b).
  rewrite s2Z_false s2Z_true H0 in H1.
  assert ( .[ b ]u < 2^^n ).
    apply max_u2Z.
    by rewrite H0.
  have H3 : .[ a ]u < 0 by omega.
  have : (~(.[ a ]u < 0)).
    move: (min_u2Z a) => ?; omega.
  by move/(_ H3).
  rewrite s2Z_false s2Z_true H in H1.
  have H2 : .[ a ]u < 2 ^^ n by apply max_u2Z; rewrite H.
  have H3 : .[ b ]u < 0 by omega.
  have: ~( .[ b ]u < 0) by move: (min_u2Z b) => ?; omega.
  by move/(_ H3).
  do 2 rewrite s2Z_true in H1.
  rewrite H H0 in H1.
  assert (.[ a ]u = .[ b ]u) by omega.
  by rewrite (u2Z_inj n a b).
Qed.

Lemma s2Z_u2Z_pos : forall n l, size l = n -> 0 <= .[ l ]s ->
  .[ l ]s = .[ l ]u.
Proof.
destruct l; intros; auto.
destruct b; auto.
simpl in H.
destruct n; try discriminate.
case: H => H.
rewrite /= H in H0.
have H1 : 0 <= .[ l ]u < 2 ^^ n.
  split.
  - by apply min_u2Z.
  - apply max_u2Z; by rewrite H.
omega.
Qed.

Lemma s2Z_u2Z_pos_equiv : forall n lst, size lst = n ->
  (0 <= .[ lst ]s <-> .[ lst ]u < 2 ^^ n.-1).
Proof.
induction n.
- by case.
- move=> lst H.
  destruct lst; try discriminate.
  case : H => H.
  move: (IHn _ H) => [H1 H2].
  destruct b; last first; simpl.
  + split => H0.
    * apply max_u2Z; by rewrite H.
    * by apply min_u2Z.
  + split => H0.
    * rewrite H in H0.
      rewrite H.
      have H3 : (2 ^^ n <= .[ lst ]u) by omega.
      lapply (max_u2Z n lst).
      - move=> H4.
        have H5 : (~(2 ^^ n <= .[ lst ]u)) by omega.
        contradiction.
      - by rewrite H.
    * rewrite H in H0.
      rewrite H.
      move: (min_u2Z lst) => ?; omega.
Qed.

Lemma s2Z_u2Z_neg : forall n l, size l = n ->  .[ l ]s < 0 ->
  .[ l ]s = .[ l ]u - 2 ^^ n.
Proof.
move=> n l H H0.
destruct n.
- destruct l; try discriminate.
  destruct l; try discriminate.
- destruct b; last first.
  simpl in H0.
  generalize (min_u2Z l); omega.
  rewrite u2Z_true s2Z_true ZpowerS.
  case : H => ->; ring.
Qed.

Lemma s2Z_zeros : forall n, .[ zeros n ]s = 0.
Proof.
induction n; auto.
simpl.
by destruct n.
Qed.

(*  Lemma s2Z_true_lt0: forall tl,
    s2Z (i :: tl) < 0.
    intros.
    rewrite s2Z_true.
    generalize tl.
    clear tl.
    induction tl.
    simpl.
    omega.
    destruct a.
    simpl u2Z.
    simpl size.
    rewrite ZpowerS.
    generalize (Zpower_1 (size tl)); omega.
    simpl u2Z.
    simpl size.
    rewrite ZpowerS.
    generalize (Zpower_1 (size tl)); omega.
  Qed.*)

Lemma max_s2Z : forall n lst, size lst = n.+1 -> .[ lst ]s < 2 ^^ n.
Proof.
elim.
case=> //; case; case=> //.
move=> n IH [| [|] tl ] // [H].
- move: {IH}(IH _ H) => IH.
  rewrite s2Z_true.
  apply (@ltZ_trans 0); last exact: expZ_gt0.
  have X : .[ tl ]u < 2^^n.+1.
    apply max_u2Z.
    by rewrite H.
  rewrite H; omega.
- move: {IH}(IH _ H) => IH.
  rewrite s2Z_false.
  apply max_u2Z.
  by rewrite H.
Qed.

Lemma min_s2Z : forall n l, size l = n.+1 -> - 2 ^^ n <= .[ l ]s.
Proof.
elim.
case=> //; case; case=> //.
- move=> n IH [| [|] tl ] // [H].
  move: {IH}(IH _ H) => IH.
  rewrite s2Z_true.
  apply (@leZ_trans (-2 ^^ n.+1)).
  omega.
- rewrite H.
  move: (min_u2Z tl) => ?; omega.
- move: {IH}(IH _ H) => IH.
  rewrite s2Z_false.
  apply (@leZ_trans 0); last exact: min_u2Z.
  move: (expZ_gt0 n.+1) => ?; omega.
Qed.

Lemma s2Z_overflow_len l n : 2 ^^ n <= .[ l ]s -> (n.+1 <= size l)%nat.
Proof.
move=> H.
move Hlen : (size l) => [|].
  destruct l => //.
  by move/ltZZ: (leZ_ltZ_trans H (expZ_gt0 n)).
move/max_s2Z.
move/(leZ_ltZ_trans H) => {}H.
rewrite ltnS -Zpower_2_le; exact/leZP/ltZW.
Qed.

Lemma s2Z_app : forall l e, (O < size l)%nat ->
  .[ l ++ [:: e] ]s = 2 * .[ l ]s + .[ [:: e] ]u.
Proof.
induction l.
- move=> e.
  by inversion 1.
- move=> e H.
  have -> : (a :: l) ++ [:: e] = (a :: l ++ [:: e]) ++ nil.
    by rewrite /= -catA.
  rewrite cats0.
  destruct a.
  + rewrite s2Z_true s2Z_true u2Z_last size_cat.
    simpl size.
    rewrite ZpowerD mulZDr; simpl expZ; ring.
  + by rewrite s2Z_false s2Z_false u2Z_last.
Qed.

Lemma s2Z_Zpower_inv : forall n a, size a = n.+1 ->
  .[ a ]s = - 2 ^^ n -> a = true :: zeros n.
Proof.
elim=> //.
- case=> // a [] // _.
  by destruct a.
- move=> n IH.
  case/lastP => // h t.
  rewrite size_rcons; case=> H.
  move: {IH}(IH _ H) => IH.
  rewrite -cats1.
  rewrite s2Z_app; last by rewrite H.
  destruct t.
  + simpl u2Z => abs.
    have H' : Zeven (- 2 ^^ n.+1) by apply Zeven_opp, Zeven_power.
    rewrite -abs in H'.
    move: (Zodd_1 (.[ h ]s)).
    by move/Zodd_not_Zeven.
  + simpl u2Z.
    rewrite addZ0 ZpowerS => H'.
    have {}H' : .[h ]s = - 2 ^^ n.
      rewrite Zopp_mult_distr_r in H'.
      move/eqZ_mul2l : H'; by apply.
    move/IH : H' => ->.
    by rewrite /= -nseqS.
Qed.

Lemma Zeven_slstZ_false  : forall l, Zeven (.[ l ++ [:: false] ]s).
Proof.
elim=> // hd tl IH.
rewrite /=.
destruct hd => //=.
  apply Zeven_plus_Zeven.
    apply/Zeven_opp/Zeven_power'.
    by rewrite size_cat /= addnC.
  by apply Zeven_ulst_false.
by apply Zeven_ulst_false.
Qed.

Lemma bZsgn_Zsgn_s2Z def : forall n a, size a = n -> a <> zeros n ->
  bZsgn (.[ [:: head def a] ]u ) = Z.sgn (.[ a ]s).
Proof.
case.
- by case.
- move=> n [|[] t] //= [len_t] H.
  + clear H.
    set xxx := _ + _.
    have : xxx < 0.
      have Ht : .[t ]u < 2 ^^ n.
        apply max_u2Z; by rewrite len_t.
     rewrite /xxx len_t; omega.
    by destruct xxx.
  + have : 0 < .[t ]u.
      move: (min_u2Z t) => X.
      have : .[t ]u = 0 \/ 0 < .[t ]u by omega.
      case=> //.
      move/(u2Z_zeros_inv _ _ len_t) => ?; subst t.
      tauto.
      by destruct (.[t ]u).
Qed.

Lemma s2Z_neg_ones : forall n lst, size lst = n ->
  forall l', (l' < n)%nat ->
    - 2 ^^ l' <= .[ lst ]s < 0 ->
    exists lst', lst = ones (n - l') ++ lst'.
Proof.
induction n.
- intros.
  by inversion H0.
- intros.
  destruct lst; try discriminate.
  simpl in H; injection H; clear H; intro.
  destruct b; last first.
  + rewrite s2Z_false in H1.
    case : H1 => H2 H3.
    move: (min_u2Z lst) => H1.
    assert (~ (u2Z lst < 0)) by omega.
    tauto.
  + rewrite s2Z_true H in H1.
    have [H3|H3] : (l' = n \/ l' < n)%coq_nat by move/ltP in H0; omega.
    * subst l'.
      rewrite subSnn.
      by exists lst; auto.
    * move/ltP in H3; generalize (IHn _ H _ H3) => H2.
      destruct lst.
        simpl in H; subst n; by inversion H3.
      destruct b; last first.
        simpl u2Z in H1.
        rewrite s2Z_false in H2.
        destruct n; try discriminate.
        case: H => H.
        destruct n.
        destruct lst; try discriminate.
        clear H.
        destruct l'.
        simpl in H1.
        have H : ~(-1<=-2) by omega.
        tauto.
        by inversion H3.
        rewrite ltnS in H3.
        assert (u2Z lst < 2 ^^ n.+1).
          apply max_u2Z; by rewrite H.
        assert (- 2 ^^ n.+2 + u2Z lst < - 2 ^^ n.+1).
          rewrite ZpowerS; omega.
        assert ( - 2 ^^ l' <  - 2 ^^ n.+1) by omega.
        assert ( 2 ^^ l' > 2 ^^ n.+1) by omega.
        have : (l' <= n.+1)%nat by ssromega.
        rewrite -Zpower_2_le => /leZP ?.
        assert ( ~ (2 ^^ l' <= 2 ^^ n.+1)) by omega.
        tauto.
      rewrite s2Z_true in H2.
      rewrite u2Z_true in H1.
      destruct n; try discriminate.
      case : H => H.
      rewrite !H in H2, H1.
      rewrite ZpowerS in H1.
      have H4 : (- 2 ^^ l' <= - 2 ^^ n + u2Z lst < 0) by omega.
      move: (H2 H4) => [x H6].
      rewrite (_ : n.+1 - l' = (n - l').+1)%nat in H6.
      + simpl in H6.
        injection H6; intro H5.
        exists x.
        rewrite (_ : n.+2 - l' = (n - l').+2)%nat.
        * by rewrite /= H5.
        * by rewrite subSn // subSn.
      + by rewrite subSn.
Qed.

Lemma s2Z_u2Z_pos_zeros n lst : size lst = n ->
  forall l', (l' < n)%nat ->
    0 <= .[ lst ]s < 2^^l' ->
    exists lst', lst = zeros (n - l') ++ lst'.
Proof.
move=> H l' H0 H1.
destruct lst.
- simpl in H.
  subst n.
  by inversion H0.
- destruct n; try discriminate.
  simpl in H; injection H; clear H; intro.
  destruct b; last first.
  + rewrite s2Z_false in H1.
    move/ltP in H0.
    assert (n >= l')%coq_nat by omega.
    assert ( u2Z lst < 2 ^^ l') by omega.
    move/leP in H2.
    case: (u2Z_power_inv _ _ _ H2 H H3) => x H4.
    exists x.
    rewrite H4 (_ : (n.+1 - l')%nat = ((n-l').+1 )%coq_nat) // -!minusE; omega.
  - rewrite s2Z_true H in H1.
    assert (u2Z lst < 2 ^^ n).
      apply max_u2Z; by rewrite H.
    have H3 : - 2 ^^ n + u2Z lst < 0 by omega.
    have : ~( - 2 ^^ n + u2Z lst < 0) by omega.
    by move/(_ H3).
Qed.

Lemma s2Z_leading_bit_0 n a : size a = n.+1 ->
  0 <=? .[a ]s -> exists ta, size ta = n /\ a = false :: ta.
Proof.
move=> a_n a_pos.
destruct a as [|[|] ta] => //; last first.
  exists ta; by case: a_n.
rewrite /= in a_pos.
case: a_n => ?; subst n.
move: (max_u2Z (size ta) _ (leqnn _)) => ?.
exfalso.
move/leZP in a_pos.
omega.
Qed.

Lemma s2Z_shl : forall l lst, size lst = l ->
  forall k l', (l' > k)%nat ->
    forall lst', lst = ones l' ++ lst' \/ lst = zeros l' ++ lst' ->
      .[ shl k lst ]s = .[ lst ]s * 2^^k.
Proof.
induction l.
- intros.
  destruct lst; try discriminate.
  destruct k; by auto.
- intros.
  destruct lst; try discriminate.
  simpl in H; injection H; clear H; intro.
  destruct l'; first by inversion H0.
  simpl in H1.
  destruct b.
  + destruct k.
    * rewrite [shl _ _]/= [_ ^^ _]/=; ring.
    * rewrite ltnS in H0. move/ltP in H0.
      move/ltP in H0.
      lapply (IHl _ H _ _ H0 lst').
      - move=> H3.
        rewrite [shl _ _]/= s2Z_true H.
        destruct l.
        + destruct lst; try discriminate.
          inversion_clear H1.
            destruct l'; try discriminate.
          destruct lst'; try discriminate.
        + rewrite s2Z_app.
          * rewrite [u2Z _]/= H3.
            destruct l' => //.
            case: H1; last by done.
            case => H1.
            rewrite H1 s2Z_true u2Z_true size_cat size_nseq.
            have -> : (size lst' = l - l')%nat.
              rewrite H1 /= size_cat size_nseq in H.
              by case: H => <-; rewrite addnC addnK.
              rewrite ltnS in H0.
            cutrewrite ((l' + (l-l')%nat)%nat = l); last first.
              rewrite H1 /= size_cat size_nseq in H.
              case: H => <-; rewrite addnBA //.
              by rewrite addnC addnK.
              by rewrite leq_addr.
            rewrite 2!ZpowerS.
            ring.
        * rewrite (size_shl k l.+1) //; by apply lt_0_Sn.
      - case: H1 => [|]; last by done.
        case ; by left.
  + inversion_clear H1; try discriminate.
    injection H2; clear H2; intro.
    destruct k.
    * by rewrite /= Zmult_1_r.
    * rewrite [shl _ _]/= s2Z_false.
      rewrite ltnS in H0.
      lapply (IHl _ H _ _ H0 lst'); last by right.
      move=> H3.
      destruct l.
      - destruct lst; try discriminate.
        simpl.
        by destruct k.
      - rewrite s2Z_app.
        + rewrite [u2Z _]/= H3.
          destruct l' => //.
          simpl in H1.
          rewrite H1 s2Z_false u2Z_false ZpowerS; ring.
        + rewrite (size_shl k l.+1) //; omega.
Qed.

Lemma shra_ones n a m : size a = n.+1 -> .[ a ]s < 0 -> (n <= m)%nat ->
  shra m a = ones n.+1.
Proof.
destruct a as [|h t] => //.
case=> len_a Ha n_m.
rewrite /= in Ha len_a.
destruct h.
- rewrite /=; f_equal.
  rewrite len_a.
  move/minn_idPr : (n_m) => ->.
  rewrite /ones.
  have -> : (n - m = O)%nat.
    apply/eqP.
    by rewrite subn_eq0.
  by rewrite take0 cats0.
- move: (min_u2Z t).
  by move/Zle_not_lt.
Qed.

Lemma shra_zeros n a m : size a = n.+1 -> 0 <= .[ a ]s -> (n <= m)%nat ->
  shra m a = zeros n.+1.
Proof.
destruct a as [|h t] => //.
case=> len_a Ha n_m.
rewrite /= in Ha len_a.
destruct h.
- move: (max_u2Z n t).
  rewrite len_a.
  move/(_ (leqnn _)) => X.
  rewrite len_a in Ha.
  have abs : - 2 ^^ n + .[t ]u < 0 by omega.
  suff : False by done.
  omega.
- rewrite /=; f_equal.
  rewrite len_a.
  move/minn_idPr : (n_m) => ->.
  rewrite /ones.
  have -> : (n - m = O)%nat. apply/eqP. by rewrite subn_eq0.
  by rewrite take0 cats0.
Qed.

(** correctness of cplt2 *)

Lemma cplt2_correct : forall n a, size a = S n -> a <> true :: zeros n ->
  .[ cplt2 a ]s = - .[ a ]s.
Proof.
induction n.
- destruct a => //.
  destruct a => //.
  by destruct b.
- intros.
  destruct a => //.
  destruct a => //.
  case : H => H.
  destruct b; destruct b0; last first.
  + case: (dec_equ_lst_bit' a (zeros n)) => H1.
    * rewrite H1.
      have -> : false :: false :: zeros n = zeros n.+2 by done.
      by rewrite cplt2_zeros s2Z_zeros.
    * rewrite cplt2_prop; last 2 first.
        - move=> [ [|k] // [Hk] ]; rewrite Hk size_nseq in H; subst k; tauto.
        - by case.
      rewrite s2Z_true size_cplt2 s2Z_false u2Z_false.
      simpl size.
      rewrite cplt2_prop; last 2 first.
        - move=> [k Hk]; rewrite Hk size_nseq in H; subst k; tauto.
        - by case.
      rewrite u2Z_true size_cplt2 H.
      have H2 : size (false :: a) = S n by rewrite /= H.
      move: {H2}(IHn (false :: a) H2) => H4.
      rewrite cplt2_prop // in H4; last first.
        - by case.
        - move=> [k Hk]; rewrite Hk size_nseq in H; subst k; tauto.
      rewrite s2Z_true s2Z_false size_cplt2 H in H4.
      rewrite -H4; last by intuition.
      rewrite -(Zpower_plus n); ring.
  + rewrite cplt2_prop; last 2 first.
      - by move => [ [|k] Hk].
      - by case.
    case: (dec_equ_lst_bit' a (zeros n)) => H1.
    * rewrite H1 cplt2_weird s2Z_true s2Z_false u2Z_true.
      rewrite [size _]/=.
      rewrite size_nseq u2Z_zeros -(Zpower_plus n); ring.
    * have H2 : size (true :: a) = n.+1 by simpl; auto.
      move: {H2}(IHn _ H2) => H4.
      rewrite cplt2_prop in H4; last 2 first.
        move=> [k Hk] //; rewrite Hk size_nseq in H; subst k; tauto.
        move=> [k [Hk]] //; rewrite Hk size_nseq in H; subst k; tauto.
      rewrite s2Z_false s2Z_true in H4.
      rewrite s2Z_true s2Z_false u2Z_true.
      rewrite cplt2_prop; last 2 first.
        move=> [k Hk] //; rewrite Hk size_nseq in H; subst k; tauto.
        move=> [k [Hk]] //; rewrite Hk size_nseq in H; subst k; tauto.
      simpl cplt.
      simpl size.
      rewrite size_cplt2 ZpowerS u2Z_false H4; last first.
        contradict H1.
        by case: H1 => ->.
      ring.
  + case: (dec_equ_lst_bit' a (zeros n)) => H1.
    * by subst a.
    * rewrite cplt2_prop; last 2 first.
        move=> [ [|k] // [Hk]]; rewrite Hk size_nseq in H; by subst k.
        move=> [ [|k] // [Hk]]; rewrite Hk size_nseq in H; by subst k.
      have H2 : size (false :: a) = S n by simpl; auto.
      move: {H2}(IHn _ H2) => H4.
      rewrite s2Z_false cplt2_prop in H4; last 2 first.
        move=> [k Hk]; rewrite Hk size_nseq in H; by subst n.
        by case.
      rewrite cplt2_prop; last 2 first.
        move=> [k Hk]; rewrite Hk size_nseq in H; by subst n.
        by case.
      rewrite s2Z_true size_cplt2 in H4.
      rewrite s2Z_true s2Z_false u2Z_true u2Z_false size_cplt2.
      simpl size.
      lapply H4; last first.
        contradict H0; by rewrite H0.
      move=> {}H4.
      rewrite ZpowerS; omega.
  + rewrite cplt2_prop; last 2 first.
      by move=> [ [|k] Hk].
      by move=> [ [|k] Hk].
    case: (dec_equ_lst_bit' a (zeros n)) => H1.
    * rewrite H1 cplt2_weird s2Z_false s2Z_true u2Z_true u2Z_zeros.
      simpl size.
      rewrite ZpowerS size_nseq; ring.
    * have H2 : size (true :: a) = S n by simpl; auto.
      move: {H2}(IHn _ H2) => H4.
      rewrite cplt2_prop in H4; last first.
        move=> [k [Hk]]; rewrite Hk size_nseq in H; by subst n.
        move=> [k Hk]; rewrite Hk size_nseq in H; by subst n.
      rewrite cplt2_prop; last 2 first.
        move=> [k Hk]; rewrite Hk size_nseq in H; by subst n.
        move=> [k [Hk]]; rewrite Hk size_nseq in H; by subst n.
      rewrite s2Z_false s2Z_true in H4.
      rewrite s2Z_false s2Z_true u2Z_true u2Z_false.
      simpl size.
      rewrite H4; last first.
        contradict H1.
        by case: H1.
      rewrite ZpowerS; ring.
Qed.

(** from Coq integers to integers in two's complement notation *)

Definition Z2s (z : Z) : list bool :=
  match z with
    | Z0 => [:: false ; false]
    | Zpos p => false :: Z2u z
    | Zneg p => cplt2 (false :: Z2u (Zpos p))
  end.

Lemma Z2s_Z2u_eq n k : 0 < k < 2 ^^ n -> Z2s k = false :: Z2u k.
Proof. case=> H1 H2; by destruct k. Qed.

Lemma Z2s2Z : forall z, .[ Z2s z ]s = z.
Proof.
destruct z => //=.
- by rewrite u2Z_rev_poslst.
- rewrite (cplt2_correct (size (pos2lst p))) //; last first.
    by rewrite /= size_rev.
  by rewrite /= u2Z_rev_poslst.
Qed.

Lemma Z2s_weird m : Z2s (- 2 ^^ m) = true :: true :: zeros m.
Proof.
move Heq : (- 2 ^^ m) => z.
destruct z as [|p|p].
- exfalso.
  move: (expZ_gt0 m) => ?; omega.
- have Habsurd : - (2 ^^ m) > 0 by rewrite Heq; apply Zgt_pos_0.
  exfalso.
  move: (expZ_gt0 m) => ?; omega.
- rewrite /= cplt2_prop /=; last 2 first.
    case=> x H1.
    rewrite (Zneg_Zpower m) // in H1.
    by destruct x.
    by case.
  symmetry in Heq.
  move/Zneg_Zpower : Heq => ->.
  by rewrite cplt2_weird.
Qed.

Lemma size_Z2s_weird n : size (Z2s (- 2 ^^ n)) = n.+2.
Proof. by rewrite Z2s_weird //= size_nseq. Qed.

Lemma adjust_s_Z2s_0' : forall n, adjust_s (Z2s 0) n.+3 = zeros n.+3.
Proof.
elim=> // n /=.
rewrite /adjust_s /=.
by case => ->.
Qed.

Lemma adjust_s_Z2s_0 : forall n, adjust_s (Z2s 0) n = zeros n.
Proof.
case=> //.
case=> //.
case=> //.
by apply adjust_s_Z2s_0'.
Qed.

Lemma size_Z2s_max : forall n, size (Z2s (2 ^^ n)) = n.+2.
Proof.
elim=> // n.
rewrite ZpowerS.
move H : (2 ^^ n) => [|p|p] /=.
- move: (expZ_gt0 n) => ?; omega.
- rewrite rev_cons -cats1.
  rewrite size_cat size_rev /= -addn1 -plusE.
  by move=>->.
- exfalso.
  move: (expZ_gt0 n).
  rewrite H => Z.
  move: (Zlt_neg_0 p) => ?; omega.
Qed.

Lemma Z2s_len n : forall z, 0 < z < 2 ^^ n -> (size (Z2s z) <= n.+1)%nat.
Proof.
case.
- case; by move/ltZZ.
- by move=> p [_ H]; rewrite /= size_rev; apply pos2lst_len.
- by move=> p [].
Qed.

Lemma Z2s_overflow_len z n : 2 ^^ n <= z -> (n < size (Z2s z))%nat.
Proof.
destruct z.
- move=> Hn.
  move: (expZ_gt0 n) => ?; omega.
- move=> H.
  rewrite /= size_rev ltnS ltnW //.
  by apply pos2lst_len2.
- move=> H.
  move: (expZ_gt0 n) (Zlt_neg_0 p) => ? ?; omega.
Qed.

Lemma s2Z_cplt1 : forall n a, size a = n.+1 -> .[ cplt1 a ]s = - .[ a ]s - 1.
Proof.
elim.
  case=> // ha [] // _ /=.
  by destruct ha.
move=> n IH.
case=> // ha [] // ha' ta [Ha].
destruct ha.
  simpl cplt1.
  rewrite s2Z_false.
  move: (IH (ha' :: ta)).
  rewrite [size _]/= Ha.
  move/(_ Logic.eq_refl).
  simpl cplt1.
  destruct ha'.
    rewrite s2Z_false u2Z_false => ->.
    rewrite !s2Z_true !u2Z_true.
    simpl size.
    rewrite Ha ZpowerS; ring.
  rewrite 2!s2Z_true u2Z_false u2Z_true.
  simpl size.
  rewrite size_cplt1 Ha ZpowerS.
  simpl s2Z => ?; omega.
simpl cplt1.
rewrite s2Z_true.
simpl size.
rewrite size_cplt1 Ha ZpowerS.
move: (IH (ha' :: ta)).
rewrite [size _]/= Ha.
move/(_ Logic.eq_refl).
destruct ha'.
  simpl cplt1.
  rewrite s2Z_false u2Z_false.
  simpl s2Z.
  rewrite Ha => ?; omega.
simpl cplt1.
rewrite s2Z_true u2Z_true size_cplt1 Ha.
simpl s2Z => ?; omega.
Qed.

Lemma sext_s2Z : forall l n, .[ sext n l ]s = .[ l ]s.
Proof.
induction n.
- destruct l; auto.
- destruct l.
  + by rewrite /= u2Z_zeros.
  + destruct b.
    * rewrite [sext n.+1 (true :: l)]/= s2Z_true size_sext sext_true [size _]/=.
      rewrite ZpowerD -2!Zpower_plus s2Z_true; ring.
    * by rewrite /= sext_false.
Qed.

(** correctness of the addition for signed numbers *)

Lemma s2Z_last : forall l e, l <> nil ->
  .[ l ++ [:: e] ]s = 2 * .[ l ]s + .[ [:: e] ]u.
Proof.
elim => //.
simpl app.
case => // l H e _.
- rewrite 2!s2Z_true size_cat [size _]/= ZpowerD u2Z_last. simpl expZ; ring.
- rewrite 2!s2Z_false; by apply u2Z_last.
Qed.

Lemma add'_Z_falseo n l k carry : size l = n -> size k = n -> (0 < n)%nat ->
  .[ rev l ]u + .[ rev k ]u + .[ [:: carry] ]u < 2 ^^ n ->
  .[ rev (add' (l ++ [:: false])  (k ++ [:: false]) carry) ]s =
  .[ rev l ]u + .[ rev k ]u + .[ [:: carry] ]u.
Proof.
move=> Hl Hk Hn H.
lapply (s2Z_u2Z_pos_equiv n.+1 (rev (add' (l ++ [:: false]) (k ++ [:: false]) carry))).
move=> H'.
rewrite -(u2Z_add' n) // -(s2Z_u2Z_pos n.+1) //.
rewrite size_rev size_add'.
by rewrite size_cat Hl //= addn1.
by rewrite 2!size_cat Hl Hk.
apply (proj2 H').
by rewrite (u2Z_add' n).
rewrite size_rev size_add'.
by rewrite size_cat Hl //= addn1.
by rewrite 2!size_cat Hl Hk.
Qed.

Lemma add_Z_falseo n l k c : size l = n -> size k = n ->
  (n > 0)%nat -> .[ l ]u + .[ k ]u + .[ [:: c] ]u < 2 ^^ n ->
  .[ add (false :: l) (false :: k) c ]s =  .[ l ]u + .[ k ]u + .[ [:: c] ]u.
Proof.
move=> Hl Hk Hn H.
rewrite /add 2!rev_cons -cats1 -(cats1 (rev k)) (add'_Z_falseo n) //.
by rewrite !revK.
by rewrite size_rev.
by rewrite size_rev.
by rewrite !revK.
Qed.

Lemma add'_Z_falsei : forall n l k c, size l = n -> size k = n ->
  (0 < n)%nat -> .[ rev (add' (l ++ [:: false]) (k ++ [:: true]) c) ]s =
  .[ rev l ]u + .[ rev k ]u + .[ [:: c] ]u - 2 ^^ n.
Proof.
elim => // n IHn.
- move=> [|b l] // [|b0 k] // c [Hl] [Hk] H1.
  case: (zerop n) => Hn.
  + subst n.
    destruct l; last by done.
    destruct k; last by done.
    by destruct b; destruct b0; destruct c.
  + move/ltP in Hn.
    destruct b; destruct b0; destruct c; simpl rev; rewrite !rev_cons -!cats1.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite 2!size_cat Hl Hk.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn // ZpowerS; ring.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite 2!size_cat Hl Hk.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn // ZpowerS; ring.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite 2!size_cat Hl Hk.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn // ZpowerS; ring.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite 2!size_cat Hl Hk.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn // ZpowerS; ring.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite 2!size_cat Hl Hk.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn // ZpowerS; ring.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite 2!size_cat Hl Hk.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn // ZpowerS; ring.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite 2!size_cat Hl Hk.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn // ZpowerS; ring.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite 2!size_cat Hl Hk.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn // ZpowerS; ring.
Qed.

Lemma add_Z_falsei n l k c : size l = n -> size k = n -> (0 < n)%nat ->
  .[ add (false :: l) (true :: k) c ]s =
  .[ l ]u + .[ k ]u + .[ [:: c] ]u - 2 ^^ n.
Proof.
move=> Hl Hk Hn; rewrite /add 2!rev_cons.
rewrite -cats1 -(cats1 (rev k)).
rewrite (add'_Z_falsei n) //; last 2 first.
  by rewrite size_rev.
  by rewrite size_rev.
by rewrite 2!revK.
Qed.

Lemma add'_Z_truei : forall n l k c, size l = n -> size k = n ->
  (0 < n)%nat ->
  2 ^^ n <= .[ rev l ]u + .[ rev k ]u + .[ [:: c] ]u ->
  .[ rev (add' (l ++ [:: true]) (k ++ [:: true]) c) ]s =
  .[ rev l ]u + .[ rev k ]u + .[ [:: c] ]u - 2 ^^ n.+1.
Proof.
elim => // n IHn.
- move=> [|b l] // [|b0 k] // c [H] [H0] H1 H2.
  destruct n.
  + destruct l; last by done.
    destruct k; last by done.
    destruct b; destruct b0; destruct c; auto.
    rewrite /= in H2; omega.
    rewrite /= in H2; omega.
    rewrite /= in H2; omega.
    rewrite /= in H2; omega.
  + destruct b; destruct b0; destruct c; simpl rev; rewrite !rev_cons -!cats1.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite !size_cat H H0.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn //.
      rewrite (ZpowerS 2 n.+2); ring.
      rewrite !rev_cons -!cats1 in H2.
      simpl rev in H2. rewrite ZpowerS !u2Z_last in H2. simpl u2Z in H2. simpl u2Z; omega.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite !size_cat H H0.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn //.
      rewrite (ZpowerS 2 n.+2); ring.
      rewrite !rev_cons -!cats1 in H2.
      simpl rev in H2. rewrite ZpowerS !u2Z_last in H2. simpl u2Z in H2. simpl u2Z; omega.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite !size_cat H H0.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn //.
      simpl u2Z. rewrite (ZpowerS 2 n.+2); ring.
      rewrite !rev_cons -!cats1 in H2.
      simpl rev in H2. rewrite ZpowerS !u2Z_last in H2. simpl u2Z in H2. simpl u2Z; omega.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite !size_cat H H0.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn //.
      simpl u2Z. rewrite (ZpowerS 2 n.+2); ring.
      rewrite !rev_cons -!cats1 in H2.
      simpl rev in H2. rewrite ZpowerS !u2Z_last in H2. simpl u2Z in H2. simpl u2Z; omega.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite !size_cat H H0.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn //.
      simpl u2Z. rewrite (ZpowerS 2 n.+2); ring.
      rewrite !rev_cons -!cats1 in H2.
      simpl rev in H2. rewrite ZpowerS !u2Z_last in H2. simpl u2Z in H2. simpl u2Z; omega.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite !size_cat H H0.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn //.
      simpl u2Z. rewrite (ZpowerS 2 n.+2); ring.
      rewrite !rev_cons -!cats1 in H2.
      simpl rev in H2. rewrite ZpowerS !u2Z_last in H2. simpl u2Z in H2. simpl u2Z; omega.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite !size_cat H H0.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn //.
      simpl u2Z. rewrite (ZpowerS 2 n.+2); ring.
      rewrite !rev_cons -!cats1 in H2.
      simpl rev in H2. rewrite ZpowerS !u2Z_last in H2. simpl u2Z in H2. simpl u2Z; omega.
    * rewrite s2Z_last; last first.
        move/eqP; rewrite -size_eq0.
        rewrite size_rev size_add'; last by rewrite !size_cat H H0.
        by rewrite size_cat /= addn1.
      rewrite !u2Z_last IHn //.
      simpl u2Z. rewrite (ZpowerS 2 n.+2); ring.
      rewrite !rev_cons -!cats1 in H2.
      simpl rev in H2. rewrite ZpowerS !u2Z_last in H2. simpl u2Z in H2. simpl u2Z; omega.
Qed.

Lemma add_Z_truei n l k c : size l = n -> size k = n ->
  (O < n)%nat -> 2 ^^ n <= .[ l ]u + .[ k ]u + .[ [:: c] ]u ->
  .[ add (true :: l) (true :: k) c ]s =
  .[ l ]u + .[ k ]u + .[ [:: c] ]u - 2 ^^ n.+1.
Proof.
move=> Hl Hk Hn H.
rewrite /add 2!rev_cons -(cats1 (rev l)) -cats1 (add'_Z_truei n) //.
by rewrite !revK.
by rewrite size_rev.
by rewrite size_rev.
by rewrite !revK.
Qed.

Lemma add_Z : forall n a b, size a = n.+1 -> size b = n.+1 -> forall c,
  - 2 ^^ n - (if c then 1 else 0) <= .[ a ]s + .[ b ]s < 2 ^^ n - (if c then 1 else 0) ->
  .[ add a b c ]s = .[ a ]s + .[ b ]s + if c then 1 else 0.
Proof.
case.
- case => // b [] // [] // b0 [] // _ _ c H.
  move: b b0 H; case; case; move=> H.
  + destruct c => //=.
    simpl in H;omega.
  + by destruct c.
  + by destruct c.
  + destruct c => //=.
    simpl in H; omega.
- move=> n [|a0 a] // [|b0 b] // [H] [H0] c H1.
  destruct a0; destruct b0.
  - (* we add two negative numbers *)
    rewrite 2!s2Z_true H H0 in H1.
    rewrite 2!s2Z_true H H0 (add_Z_truei n.+1) //.
    * simpl u2Z.
      rewrite ZpowerS.
      destruct c; ring.
    * destruct c; simpl u2Z; omega.
  - rewrite (addC (true :: a) (false :: b) c) (add_Z_falsei n.+1) //.
    + rewrite s2Z_true s2Z_false in H1.
      rewrite s2Z_true s2Z_false.
      destruct c.
      * simpl u2Z.
        rewrite H in H1 *; omega.
      * simpl u2Z.
        rewrite H in H1 *; omega.
  - (* we add a positive number with a negative number (never overflows) *)
    rewrite s2Z_false s2Z_true H0 in H1.
    destruct c.
    + rewrite s2Z_false s2Z_true H0 (add_Z_falsei n.+1) //.
      * simpl u2Z; ring.
    + rewrite s2Z_false s2Z_true H0 (add_Z_falsei n.+1) //.
      * simpl u2Z; ring.
  - (* we add two positive numbers *)
    destruct c.
    + rewrite 2!s2Z_false in H1.
      rewrite 2!s2Z_false (add_Z_falseo n.+1) //.
      simpl u2Z; omega.
    + rewrite 2!s2Z_false in H1.
      rewrite 2!s2Z_false (add_Z_falseo n.+1) //.
      simpl u2Z; omega.
Qed.

Lemma sub_Z n a b : size a = n.+1 -> size b = n.+1 ->
  (- 2 ^^ n <= .[ a ]s - .[ b ]s < 2 ^^ n)%Z ->
  .[ sub a b false ]s = .[ a ]s - .[ b ]s.
Proof.
move=> Ha Hb H.
rewrite (sub_add_cplt1 n.+1) //= (add_Z n) //.
- rewrite (s2Z_cplt1 n) //; ring.
- by rewrite size_cplt1.
- rewrite (s2Z_cplt1 n) //; omega.
Qed.

(** correctness of the signed multiplication *)

Lemma smul_Z1 : forall n a b, size a = n.+2 -> size b = n.+2 ->
  ~ (is_pos a = true) -> is_pos b = true ->
  .[ smul a b ]s = .[ a ]s * .[ b ]s.
Proof.
move=> n [|[] [|a0 a1]] // [|[] [|b0 b1]] // [H] [H0] H1 H2.
destruct n.
- destruct a1 => //.
  destruct b1 => //.
  by destruct a0; destruct b0.
- rewrite /smul [s2Z _]/=.
  eapply trans_eq.
    apply (cplt2_correct (n.+1 + n.+1).+3).
    case: b0 H2 => H2; last first.
      by rewrite /= size_umul size_cplt2 H0 /= H.
    rewrite /= (size_add (n + n + 5)).
    by nat_norm.
    rewrite /= size_cat size_cplt2 /= size_nseq H H0 //=; by nat_norm.
    rewrite /= size_umul size_cplt2 /= H H0 /=; by nat_norm.
    by [].
  rewrite s2Z_false s2Z_true s2Z_false.
  simpl length.
  rewrite H0.
  destruct b0.
  + destruct a0.
    * rewrite u2Z_true H (u2Z_add (n + n.+1).+3); last 2 first.
        rewrite size_cat /= size_cplt2 size_nseq /= H; by nat_norm.
        by rewrite size_umul size_cplt2 /= H H0.
      rewrite u2Z_true [ .[ [:: false] ]u ]/= H0 u2Z_app_zeros.
      have -> : cplt2 (true :: true :: a1) = cplt true :: cplt2 (true :: a1).
        apply cplt2_prop; by move=> [k Hk]; destruct k.
      rewrite u2Z_false umul_leading_false; last 2 first.
        move=> H'.
        have X : size (cplt2 (true :: a1)) = O by rewrite H'.
        by rewrite size_cplt2 /= H in X.
        by move=> H'; subst b1.
      rewrite u2Z_false.
      case: (zeros_dec a1) => H3.
      - rewrite H3 cplt2_weird umul_leading_true u2Z_true size_nseq H u2Z_zeros.
        rewrite (umulC n.+1) //; last by rewrite size_nseq.
        rewrite umull0 addl0; last by rewrite /= size_cat /= size_nseq /= H0.
        rewrite [size _]/= size_nseq.
        rewrite u2Z_false u2Z_app_zeros -(Zpower_plus n.+1); ring.
      - rewrite (u2Z_cplt2' n) //; last by rewrite /= H.
        rewrite u2Z_true H.
        have -> : cplt2 (true :: a1) = cplt true :: cplt2 a1.
          apply cplt2_prop.
          case=> k Hk; by rewrite Hk size_nseq in H3.
          case=> k; case=> Hk; by rewrite Hk size_nseq in H3.
        rewrite umul_leading_false; last 2 first.
          move/eqP; rewrite -size_eq0.
          by rewrite size_cplt2 H.
          by move=> ?; subst b1.
        rewrite u2Z_false (umul_nat n) //; last by rewrite size_cplt2.
        destruct n.
        + destruct a1 => //.
          destruct a1 => //.
          destruct b1 => //.
          destruct b1 => //.
          by destruct b; destruct b0.
        + rewrite (u2Z_cplt2' n) //; last first.
            by move=> H'; rewrite H' size_nseq in H3.
          rewrite [size _]/= H.
          rewrite -(Zpower_plus n.+2); ring.
    * rewrite u2Z_false.
      case : (zeros_dec a1) => H3.
      - rewrite H3 (_ : false :: zeros (size a1) = zeros n.+2); last by rewrite H.
        rewrite cplt2_weird u2Z_zeros u2Z_true umul_leading_true size_nseq.
        rewrite (u2Z_add (S (S (S (S ((n + n))))))); last 2 first.
          rewrite /= size_cat size_nseq /= size_nseq; by nat_norm.
          rewrite /= (size_add (n.+2 + n.+2)).
          - by nat_norm.
          - rewrite /= size_cat /= size_nseq H0; by nat_norm.
          - rewrite /= size_umul /= size_nseq H0; by nat_norm.
        rewrite u2Z_false [u2Z nil]/= u2Z_app_zeros {3}/zeros [nseq _ _]/= umul_leading_false; last 2 first.
          done.
          by move=> ?; subst b1.
        rewrite (umulC n.+1) //; last by rewrite /= size_nseq.
        rewrite -/(zeros n).
        rewrite (_ : false :: zeros n = zeros n.+1) //.
        rewrite umull0 -(Zpower_plus n.+1) H0.
        rewrite (u2Z_add (n + n.+1).+2); last 2 first.
          rewrite size_cat /= H0 size_nseq //=; by nat_norm.
          by rewrite /= size_nseq.
        rewrite u2Z_false u2Z_app [size _]/=.
        rewrite size_nseq u2Z_app_zeros !u2Z_zeros !u2Z_false u2Z_true !u2Z_false.
        rewrite [size _]/= size_nseq u2Z_zeros [ .[ nil ]u ]/= (ZpowerS 2 (S (n))); ring.
      - rewrite (u2Z_add (n + n).+4); last first.
          rewrite size_umul size_cplt2 /= H H0; by nat_norm.
          rewrite size_cat /= size_cplt2 /= H size_nseq; by nat_norm.
        have -> : cplt2 (true :: false :: a1) = cplt true :: cplt2 (false :: a1).
          apply cplt2_prop.
          case=> k Hk.
          destruct k as [|k]; first by done.
          case: Hk => Hk.
          by rewrite Hk size_nseq in H3.
          case=> k; case => Hk.
          destruct k as [|k]; first by done.
          case: Hk => Hk.
          by rewrite Hk size_nseq in H3.
        rewrite u2Z_false u2Z_app_zeros u2Z_false umul_leading_false; last 2 first.
          move=> X.
          have Y : size (cplt2 (false :: a1)) = O by rewrite X.
          by rewrite size_cplt2 in Y.
          by move=> ?; subst b1.
        rewrite u2Z_false u2Z_true H0.
        have -> : cplt2 (false :: a1) = cplt false :: cplt2 a1.
          apply cplt2_prop.
          case=> k Hk.
          by rewrite Hk size_nseq in H3.
          by case.
        rewrite u2Z_true umul_leading_true size_cplt2 (u2Z_add (n + n).+2); last 2 first.
          rewrite size_cat H0 size_nseq /= H; by nat_norm.
          rewrite size_umul size_cplt2 H H0; by nat_norm.
        rewrite [ .[ [:: false] ]u ]/= [ .[nil ]u ]/= u2Z_app_zeros (umul_nat n) //; last first.
          by rewrite size_cplt2.
        rewrite H.
        destruct n.
        * destruct a1 => //.
          destruct a1 => //.
          destruct b1 => //.
          destruct b1 => //.
          by destruct b; destruct b0.
        * rewrite (u2Z_cplt2' n) //; last first.
            by move=> H'; rewrite H' size_nseq in H3.
          rewrite [size _]/= H.
          rewrite -(Zpower_plus n.+2); ring.
  + rewrite 2!u2Z_false.
    destruct a0.
    * rewrite u2Z_true H.
      have -> : cplt2 (true :: true :: a1) = cplt true :: cplt2 (true :: a1).
        apply cplt2_prop.
        move=> [ [|] Hk] //=.
        by move => [ [|] Hk].
      rewrite umul_leading_false; last 2 first.
        move=> H'.
        have : size (cplt2 (true :: a1)) <> O by rewrite size_cplt2.
        by rewrite H'.
        by move=> ?; subst b1.
      case: (zeros_dec a1) => H3.
      - rewrite H3 u2Z_zeros cplt2_weird umul_leading_true.
        rewrite (umulC n.+1) //; last by rewrite -H3.
        rewrite umull0 addl0; last by rewrite /= size_cat 2!size_nseq.
        rewrite size_nseq H [size _]/= size_nseq.
        rewrite 2!u2Z_false u2Z_app_zeros -(Zpower_plus n.+1); ring.
      - have -> : cplt2 (true :: a1) = cplt true :: cplt2 a1.
          apply cplt2_prop.
          case=> k Hk; by rewrite Hk size_nseq in H3.
          case=> k [Hk]; by rewrite Hk size_nseq in H3.
        rewrite umul_leading_false; last 2 first.
          have H' : size (cplt2 a1) <> O by rewrite size_cplt2 H.
          contradict H'.
          by rewrite H'.
          by move=> ?; subst b1.
        rewrite 2!u2Z_false (umul_nat n) //; last by rewrite size_cplt2.
        destruct n.
        + destruct a1 => //.
          destruct a1 => //.
          destruct b1 => //.
          destruct b1 => //.
          by destruct b; destruct b0.
        + rewrite (u2Z_cplt2' n) //; first last.
            by move=> H'; rewrite H' size_nseq in H3.
          rewrite [size _]/= H.
          rewrite -(Zpower_plus n.+2); ring.
    * rewrite u2Z_false.
      case: (zeros_dec a1) => H3.
      - rewrite H3 (_ : false :: zeros (size a1) = zeros n.+2); last by rewrite H.
        rewrite cplt2_weird umul_leading_true. rewrite {3}/zeros. simpl nseq. rewrite umul_leading_false //; last first.
          by move=> ?; subst b1.
        rewrite (umulC n.+1) //; last by rewrite /= size_nseq.
        rewrite -/(zeros n). rewrite (_ : false :: zeros n = zeros n.+1) // umull0 [size _]/= size_nseq addl0; last first.
          by rewrite /= size_cat /= size_nseq H0 [in RHS]addnS.
        rewrite u2Z_false u2Z_zeros u2Z_app_zeros; ring.
      - have -> : cplt2 (true :: false :: a1) = cplt true :: cplt2 (false :: a1).
          apply cplt2_prop.
          case=> k Hk.
          destruct k as [|k]; first by done.
          case: Hk => Hk.
          by rewrite Hk size_nseq in H3.
          case=> k; case=> Hk.
          destruct k as [|k]; first by done.
          case: Hk => Hk.
          by rewrite Hk size_nseq in H3.
        rewrite umul_leading_false; last 2 first.
          move=> H'.
          have : size (cplt2 (false :: a1)) <> O by rewrite size_cplt2.
          by rewrite H'.
          by move=> ?; subst b1.
        have -> : cplt2 ( false :: a1) = cplt false :: cplt2 a1.
          apply cplt2_prop.
          case=> k Hk.
          by rewrite Hk size_nseq in H3.
          by case.
        rewrite umul_leading_true u2Z_false (u2Z_add (n + n).+2); last 2 first.
          by rewrite size_cplt2 size_cat size_nseq H H0 -addSnnS.
          by rewrite size_umul size_cplt2 H H0 -addSnnS.
        rewrite u2Z_app_zeros size_cplt2 u2Z_false (umul_nat n) //; last first.
          by rewrite size_cplt2 H.
        destruct n.
        + destruct a1 => //.
          destruct a1 => //.
          destruct b1 => //.
          destruct b1 => //.
          by destruct b; destruct b0.
        + rewrite (u2Z_cplt2' n) //; last by move=> H'; rewrite H' size_nseq in H3.
          rewrite [u2Z  nil]/=.
          rewrite H [size _]/= H.
          rewrite -(Zpower_plus n.+2) [u2Z _]/=; ring.
Qed.

Lemma smul_Z : forall n a b, size a = n -> size b = n ->
  .[ smul a b ]s = .[ a ]s * .[ b ]s.
Proof.
move=> n a b H H0.
destruct a; destruct b; auto.
- simpl in H; subst n; discriminate H0.
- simpl in H0; subst n.
  discriminate H0.
- destruct b0; destruct b.
  + destruct n => //.
    rewrite /smul.
    rewrite [s2Z _]/=.
    destruct n => //.
    destruct a => //.
    destruct b1 => //.
    case : H => H.
    case : H0 => H0.
    case: (zeros_dec a) => H1.
    * rewrite H1.
      case: (zeros_dec b1) => H2.
      - rewrite H2 2!cplt2_weird H H0 umul_weird s2Z_false s2Z_true u2Z_true.
        rewrite size_nseq u2Z_zeros size_nseq u2Z_zeros ZpowerD; ring.
      - rewrite (umulC n.+2) //; last 2 first.
          rewrite size_cplt2 //.
          by rewrite /= size_nseq H.
          by rewrite size_cplt2 /= H0.
        rewrite cplt2_prop; last 2 first.
          case=> k Hk; by rewrite Hk size_nseq in H2.
          case=> k [Hk]; by rewrite Hk size_nseq in H2.
        rewrite umul_leading_false; last 2 first.
          apply cplt2_nil.
          by move=> Hb1; rewrite Hb1 in H0.
          by apply cplt2_nil.
        rewrite s2Z_false cplt2_weird (umul_weird' (length (cplt2 b1))) //.
        rewrite u2Z_false u2Z_app_zeros.
        destruct n => //.
        + destruct a => //.
          destruct b1 => //.
          destruct a => //.
          destruct b1 => //.
          by destruct b; destruct b0.
        + rewrite (u2Z_cplt2' n) //; last first.
            by move=> Hk; rewrite Hk size_nseq in H2.
          rewrite 2!s2Z_true size_nseq u2Z_zeros H H0; ring.
    * rewrite cplt2_prop; last 2 first.
          case=> k Hk; by rewrite Hk size_nseq in H1.
          case=> k [Hk]; by rewrite Hk size_nseq in H1.
      rewrite umul_leading_false; last 2 first.
        apply cplt2_nil.
        by move=> Hk; rewrite Hk in H1.
        by apply cplt2_nil.
      rewrite s2Z_false.
      case: (zeros_dec b1) => H2.
      - rewrite H2 cplt2_weird (umul_weird' n.+1); last by rewrite size_cplt2.
        rewrite u2Z_false u2Z_app_zeros H0.
        destruct n.
        + destruct a => //.
          destruct b1 => //.
          destruct a => //.
          destruct b1 => //.
          by destruct b; destruct b0.
        + rewrite (u2Z_cplt2' n) //; last first.
            move=> Hk; by rewrite Hk size_nseq in H1.
          rewrite 2!s2Z_true size_nseq u2Z_zeros H; ring.
      - rewrite cplt2_prop; last 2 first.
          case=> k Hk; by rewrite Hk size_nseq in H2.
          case=> k [Hk]; by rewrite Hk size_nseq in H2.
        rewrite umul_leading_false'; last 2 first.
          apply cplt2_nil.
          by move=> Hk; rewrite Hk in H.
          apply cplt2_nil.
          by move=> Hk; rewrite Hk in H2.
        rewrite u2Z_false (umul_nat n); last 2 first.
          by rewrite size_cplt2.
          by rewrite size_cplt2.
        destruct n.
        + destruct a => //.
          destruct b1 => //.
          destruct a => //.
          destruct b1 => //.
          by destruct b; destruct b0.
        + rewrite (u2Z_cplt2' n) //; last first.
           move=> Hk; by rewrite Hk size_nseq in H1.
          rewrite (u2Z_cplt2' n) //; last first.
            move=> Hk; by rewrite Hk size_nseq in H2.
          rewrite 2!s2Z_true H0 H; ring.
  + destruct n => //.
    destruct a.
    * destruct b1 => //.
      case: H => H; by subst n.
    * destruct b1.
       - case: H0 => H0; by subst n.
       - destruct n => //.
         by rewrite (smul_Z1 n).
  + destruct n => //.
    destruct a => //.
    * destruct b1 => //.
      case: H => H; by subst n.
    * destruct b1.
      - case: H0 => H0; by subst n.
      - destruct n => //.
        by rewrite (smulC n) // (smul_Z1 n) // mulZC.
  + simpl.
    destruct n => //.
    destruct n => //.
    * destruct a => //.
      by destruct b1.
    * case: H => H. case: H0 => H0.
    rewrite umul_leading_false.
      by rewrite u2Z_false (umul_nat n).
      by destruct a.
      by destruct b1.
Qed.

(** Examples: *)
Eval compute in (.[ [:: true; true; true; true] ]u).
Eval compute in (.[ [:: false; false; false; true] ]s).
Eval compute in (ult [:: true; true; true; true] [:: false; false; false; true]).
Eval compute in (.[ [:: true; false; true; true] ]s).
Eval compute in (.[ adjust_s [:: true; false; true; true] 3 ]s).
Eval compute in (.[ adjust_s [:: true; false; true; true] 2 ]s).

End bitZ.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq.
Require Import seq_ext.

(** Definition of lists of bits, of various operations
on lists of bits, along with their algebraic properties.

This is for the implementation of finite-size integers. *)

Module bits.

Lemma dec_equ_bit : forall (a b : bool), { a = b } + { a <> b }.
Proof. decide equality. Qed.

Lemma dec_equ_lst_bit : forall (a b : list bool), { a = b } + { a <> b }.
Proof.
elim.
- case; by [left | right].
- move=> hd tl IH [|hd' tl'].
  + by right.
  + case: (dec_equ_bit hd hd') => X.
    * subst hd'.
      case: {IH}(IH tl') => Y.
      - subst tl'; by left.
      - right; contradict Y; by case: Y.
    * right; contradict X; by case: X.
Qed.

Lemma dec_equ_lst_bit' : forall (a b : list bool), a = b \/ a <> b.
Proof. move=> a b; case(dec_equ_lst_bit a b); by auto. Qed.

(** lists of zeros *)
Definition zeros (n : nat) := nseq n false.

Lemma zeros_dec : forall l, {l = zeros (size l)} + {l <> zeros (size l)}.
Proof.
elim.
- by left.
- case=> l.
  + case=> [-> | X]; by right.
  + case=> [-> /= | X].
    * left; by rewrite size_nseq.
    * right; contradict X; by case: X.
Qed.

Lemma zeros_app n m : zeros n ++ zeros m = zeros (n + m).
Proof. elim: n m => // n IH m; by rewrite /= IH. Qed.

Lemma zeros_app2 : forall m n, (n <= m)%coq_nat -> zeros m = zeros n ++ zeros (m - n).
Proof. move=> m n n_m. rewrite zeros_app subnKC //. by apply/ssrnat.leP. Qed.

Lemma skipn_zeros : forall n m, drop n (zeros m) = zeros (m - n).
Proof.
elim => n.
- by rewrite subn0 drop0.
- move=> IHn [|k] //=; by rewrite IHn.
Qed.

Lemma rev_zeros n : rev (zeros n) = zeros n.
Proof. elim: n => // n IH /=; by rewrite rev_cons IH -cats1 -nseqS. Qed.

(** zero-extend *)
Definition zext m l := zeros m ++ l.

Lemma size_zext n s k : size s = n -> size (zext k s) = k + n.
Proof. move=> <-; by rewrite /zext size_cat size_nseq. Qed.

Lemma zext_true k l : zext k (true :: l) = zeros k ++ true :: l.
Proof. done. Qed.

Lemma rev_zext_true : forall k l, rev (zext k (true :: l)) = rev l ++ true :: zeros k.
Proof.
case => [l|n l]; first by rewrite /zext /= cats1 rev_cons.
by rewrite zext_true -(cat1s true) catA rev_cat rev_cat rev_zeros.
Qed.

Fixpoint erase_leading_zeros (l : list bool) : list bool :=
  match l with
    | false :: t => erase_leading_zeros t
    | true :: t => l
    | _ => nil
  end.

Lemma size_erase_leading_zeros : forall n l, size l = n ->
  size (erase_leading_zeros l) <= n.
Proof.
elim => [ [] // | n IHn [|[] /= tl] // [H]].
- by rewrite H.
- by rewrite ltnW // ltnS; apply/IHn.
Qed.

Lemma size_erase_leading_zeros_eq : forall n l, size l = n ->
  ohead l = Some true -> size (erase_leading_zeros l) = n.
Proof. by elim => [ [] // | n IHn [|[] /= tl] // [H] ]. Qed.

Lemma erase_leading_zeros_prop : forall n l, size l = n ->
  zeros (n - size (erase_leading_zeros l)) ++ erase_leading_zeros l = l.
Proof.
elim; first by case.
move=> n IHn [|[|] /= tl] // [H].
- by rewrite H subnn.
- rewrite subSn /=.
  + by rewrite IHn.
  + by apply size_erase_leading_zeros.
Qed.

Lemma erase_leading_zeros_app : forall l, erase_leading_zeros l ++ [:: true] =
  erase_leading_zeros (l ++ [:: true]).
Proof. elim=> // h t H /=; by destruct h. Qed.

Lemma erase_leading_zeros_app' : forall l, l <> zeros (size l) ->
  erase_leading_zeros l ++ [:: false] = erase_leading_zeros (l ++ [:: false]).
Proof.
elim=> // h t IH H /=.
destruct h => //.
rewrite IH //.
contradict H.
by rewrite /= H size_nseq.
Qed.

Lemma erase_leading_zeros_zeros : forall n, erase_leading_zeros (zeros n) = nil.
Proof. by elim. Qed.

Lemma tail_zeros : forall n, (0 < n)%coq_nat -> behead (zeros n) = zeros (n - 1).
Proof. elim => //; by move=> [|n] // IHn. Qed.

Lemma heads_zeros : forall m n, (m <= n)%coq_nat -> take m (zeros n) = zeros m.
Proof.
elim => [|m IHm [|n]].
  move=> n _; by rewrite take0.
- by inversion 1.
- move/le_S_n => H /=; by rewrite IHm.
Qed.

Lemma nth_zeros : forall k n def, (k < n)%coq_nat -> nth def (zeros n) k = false.
Proof.
elim.
- case => //; by inversion 1.
- move=> k IHk [|n] dec.
  + by inversion 1.
  + move/ltP; rewrite ltnS => /ltP H /=; by apply IHk.
Qed.

(** shift-left and extend *)
Definition shl_ext n (l : list bool) := l ++ zeros n.

Lemma size_shl_ext n l m : size l = n -> size (shl_ext m l) = m + n.
Proof. move=> H; by rewrite /shl_ext size_cat size_nseq H addnC. Qed.

(** lists of ones *)
Definition ones (n : nat) := nseq n true.

Lemma rev_ones n : rev (ones n) = ones n.
Proof. elim: n => // n IH /=; by rewrite rev_cons IH -cats1 -nseqS. Qed.

Definition one_extend_n_lst lst cnt := ones cnt ++ lst.

Lemma one_extend_n_lst_true : forall k lst, one_extend_n_lst (true :: lst) k = ones k ++ true :: lst.
Proof. done. Qed.

(** sign-extension for signed list-bits *)
Fixpoint sext (m : nat) (l : list bool) :=
  match l with
    | nil => zeros m
    | hd :: _ => match m with
                   | 0 => l
                   | m'.+1 => hd :: sext m' l
                 end
  end.

Lemma size_sext m l : size (sext m l) = size l + m.
Proof.
elim: m l => [ [] //=| n IH [|h t] /=].
by move=> _ l; rewrite addn0.
by rewrite /zeros size_nseq.
by rewrite IH /= addnS.
Qed.

Lemma sext_0 : forall n l, sext n (false :: l) = zeros n.+1 ++ l.
Proof. elim=> //. move=> n /= H l /=; by rewrite H. Qed.

(** zero-extend or shrink a given list ("adjust" it to some size) *)
Definition adjust_u l n := if size l < n then
                             zext (n - size l) l
                           else
                             drop (size l - n) l.

Lemma size_adjust_u n l : size (adjust_u l n) = n.
Proof.
rewrite /adjust_u.
case: ifP => H.
- rewrite (size_zext (size l)) // addnC subnKC //; by auto.
- rewrite size_drop subKn // leqNgt; by apply/negbT.
Qed.

Lemma adjust_u_nil: forall n, adjust_u nil n = zeros n.
Proof.
elim=> //= n _; by rewrite /adjust_u /= subn0 /zext /= cats0.
Qed.

Lemma adjust_u_0 : forall l, adjust_u l 0 = nil.
Proof.
elim=> // a l H.
rewrite /adjust_u /=.
move: (size_drop (size l) l).
rewrite subnn.
by destruct drop.
Qed.

Lemma adjust_u_id : forall n l, size l = n -> adjust_u l n = l.
Proof.
elim; first by case. move=> n IH [|h t] // [H].
by rewrite /adjust_u /= H ltnn subnn.
Qed.

Lemma adjust_u_S : forall n h t l,
  size (h ++ [:: t]) = l -> l >= n.+1 ->
  adjust_u (h ++ [:: t]) n.+1 = adjust_u h n ++ [:: t].
Proof.
induction n.
- move=> h t l H H0.
  rewrite adjust_u_0 /= /adjust_u.
  have -> : size (h ++ [:: t]) < 1 = false by rewrite H; destruct l.
  by rewrite drop_cat //= size_cat /= subn1 addn1 /= ltnn subnn.
- move=> [|b h] /= t l H H0.
  + subst l.
    by destruct n.
  + rewrite size_cat /= addn1 in H.
    rewrite /adjust_u /= size_cat /= addn1 H !subSS.
    rewrite (_ : l < n.+2 = false); last by apply/negbTE; rewrite -leqNgt.
    rewrite (_ : l <= n.+1 = false); last by apply/negbTE; rewrite leqNgt negbK.
    rewrite (_ : b :: _ ++ [:: t] = (b :: h) ++ [:: t]) //.
    rewrite -H 2!subSS.
    move K : (size h - n) => [|k] //.
    by rewrite drop_cat -K leq_subr.
Qed.

Lemma adjust_u_S' : forall n lst l, size lst = l -> l < n ->
  adjust_u lst n = zeros (n - l)%coq_nat ++ lst.
Proof.
destruct n.
- by case.
- move=> [| b lst] //.
  + by case.
  + case=> // n0 [H] H0.
    by rewrite /adjust_u /= H H0.
Qed.

Lemma adjust_u_S'' n l lst : size lst = l -> l <= n ->
  adjust_u lst n = zeros (n - l) ++ lst.
Proof.
move=> H.
rewrite leq_eqVlt.
case/orP.
- move/eqP => <-; by rewrite /= adjust_u_id // subnn.
- move=> X; by rewrite -adjust_u_S'.
Qed.

Lemma adjust_u_zeros : forall k n, adjust_u (zeros n) k = zeros k.
Proof.
elim.
- move=> n; by rewrite adjust_u_0.
- move=> n IHn [|k].
  + by rewrite adjust_u_nil.
  + rewrite (_ : zeros (k.+1) = zeros k ++ [:: false]); last first.
      by rewrite -nseqS.
    case: (ltnP n k.+1) => X.
    * rewrite (adjust_u_S _ _ _ k.+1) //; last first.
        by rewrite -nseqS size_nseq.
      by rewrite IHn -nseqS.
    * rewrite /adjust_u size_cat /= addnC size_nseq add1n.
      rewrite ltnS X subSS /zext catA zeros_app subnK; last by rewrite ltnW.
      by rewrite -nseqS.
Qed.

Lemma adjust_u_erase_leading_zeros :
  forall l k, adjust_u (erase_leading_zeros l) k = adjust_u l k.
Proof.
  elim => //= [[]] // l IH k.
  rewrite {}IH /adjust_u; case:ifP; first case: ifP; rewrite /zext //=.
  - move=> H H0.
    by rewrite -cat1s catA -nseqS -subSn.
  - move/negbT; rewrite -leqNgt => H H0.
    have: (size l).+1 = k by apply/eqP; rewrite eqn_leq H H0.
    by move => <-; rewrite subnn subSnn.
  - move => H.
    rewrite ltn_neqAle H Bool.andb_false_r.
    move/negbT: H; rewrite -leqNgt => H.
    by rewrite (subSn H).
Qed.

(** sign-extend or shrink a given list *)

Definition adjust_s lst n := if size lst < n then
                               sext (n - size lst) lst
                             else
                               drop (size lst - n) lst.

Lemma size_adjust_s n lst : size (adjust_s lst n) = n.
Proof.
rewrite /adjust_s.
case: ifP => H.
- rewrite size_sext subnKC //; by apply ltnW.
- rewrite size_drop subKn // leqNgt; by apply/negbT.
Qed.

Lemma adjust_s_nil : forall n, adjust_s nil n = zeros n.
Proof. by elim. Qed.

(** bit complement *)

Definition cplt b := match b with true => false | false => true end.

Lemma cplt_inj : forall a b, cplt a = cplt b -> a = b.
Proof. by case; case. Qed.

Lemma cplt_involutive : forall b, cplt (cplt b) = b.
Proof. destruct b; by auto. Qed.

(** ones' complement *)

Fixpoint cplt1 lst := if lst is hd :: tl then cplt hd :: cplt1 tl else nil.

Lemma cplt1_inj : forall n a b, size a = n -> size b = n ->
                                  cplt1 a = cplt1 b -> a = b.
Proof.
elim.
  case => //.
  by case.
move=> n IH [|ha ta] // [|hb tb] // [Ha] [Hb] /= [] H1 H2.
by rewrite (IH ta tb) // (cplt_inj _ _ H1).
Qed.

Lemma size_cplt1 : forall a, size (cplt1 a) = size a.
Proof. by elim=> // a l /= ->. Qed.

(*Lemma len_cplt1' : forall n a, size a = n -> size (cplt1 a) = n.
Proof. move=> n a H; by rewrite len_cplt1. Qed.*)

Lemma cplt1_cat : forall a b, cplt1 (a ++ b) = cplt1 a ++ cplt1 b.
Proof. elim=> //. move=> a l IH b /=; by rewrite IH. Qed.

Lemma cplt1_zeros : forall k, cplt1 (zeros k) = ones k.
Proof. by elim=> // n /= ->. Qed.

Lemma cplt1_involutive : forall lst, cplt1 (cplt1 lst) = lst.
Proof. elim=> //. move=> a l H /=; by rewrite cplt_involutive H. Qed.

(** shift left *)

Fixpoint shl m (l : list bool) :=
  match m with
    | 0 => l
    | m'.+1 => match l with
                | nil => nil
                | hd :: tl => shl m' tl ++ [:: false]
              end
  end.

Lemma size_shl : forall m n l, size l = n -> size (shl m l) = n.
Proof.
elim=> // m IH [|n] [|h t] // [H] /=.
by rewrite size_cat (IH n) //=; nat_norm.
Qed.

Lemma shl_zeros : forall m n, shl m (zeros n) = zeros n.
Proof. elim => // m IHm [|n] //=; by rewrite IHm -nseqS. Qed.

Lemma shl_cat : forall m l k, size l = m -> shl m (l ++ k) = k ++ zeros m.
Proof.
elim.
- case => //=.
  move=> k _; by rewrite cats0.
- move=> m IHm [|hd tl] // k [H] /=.
  by rewrite IHm // -catA -nseqS.
Qed.

Lemma shl_zeros_cat n l : shl n (zeros n ++ l) = l ++ zeros n.
Proof. by rewrite shl_cat // size_nseq. Qed.

Lemma shl_overflow : forall n l lst, size lst = l -> (n >= l)%coq_nat ->
  shl n lst = zeros l.
Proof.
elim.
- case.
  by case.
  by move=> n l _; inversion 1.
- move=> n IH [|l] [|h t] // [Hlst] Hl /=.
  rewrite (IH l) //; last by move/leP in Hl; apply/leP; rewrite -ltnS.
  by rewrite -nseqS.
Qed.

Lemma shl_app' : forall m n l k, size l = n -> (m <= n)%nat ->
  shl m (l ++ k) = drop m l ++ k ++ zeros m.
Proof.
elim.
- move=> n l k H Hn /=; by rewrite cats0 drop0.
- move=> m IHm [|n] // [|hd tl] // k [H].
  move/leP.
  move/le_S_n => Hmn /=.
  rewrite (IHm n) //=.
  by rewrite -!catA -nseqS.
  by apply/leP.
Qed.

(** logical shift right (fill the freed bits with 0) *)
Fixpoint shrl (m : nat) (l : list bool) :=
  match l with
  | nil => nil
  | h :: t => match m with
              | 0 => l
              | m'.+1 => false :: shrl m' (belast h t)
              end
  end.

Lemma shrl_nil : forall k, shrl k nil = nil. Proof. by elim. Qed.

Lemma shrl_0 : forall l, shrl 0 l = l. Proof. by case. Qed.

Lemma shrl_S k hd tl : shrl k.+1 (hd ++ [:: tl]) = false :: shrl k hd.
Proof.
rewrite /=.
move K : ( _ ++ _) => [|h t].
  by case: hd K.
suff : belast h t = hd by move=> ->.
rewrite (lastI h t) -cats1 -rot_size_cat -[in RHS]rot_size_cat in K.
move/rot_inj : K => /eqP; rewrite eqseq_cat //; by case/andP => _ /eqP.
Qed.

Lemma size_shrl : forall n m l, size l = n -> size (shrl m l) = n.
Proof.
induction n; move=> m i0 H.
- destruct i0 => //.
  by destruct m.
- case: (lastP i0) H => {i0} // h t.
  rewrite size_rcons; case=> H0.
  destruct m.
  + rewrite /= -cats1.
    case: h H0 => //.
      by case: n IHn.
    move=> a l /=; by rewrite size_cat /= addn1 => ->.
  + by rewrite -cats1 shrl_S /= IHn.
Qed.

Lemma shrl_false : forall n l, shrl n (false :: l) = false :: shrl n l.
Proof.
elim => [l|n IH].
- by rewrite !shrl_0.
- elim/last_ind => [|hd tl _].
  + by rewrite /= shrl_nil.
  + by rewrite -cats1 -cat1s catA 2!shrl_S cat1s IH.
Qed.

Lemma shrl_comp : forall l m n, shrl m (shrl n l) = shrl (m + n) l.
Proof.
elim/last_ind => [m n|h t IH m [|n]].
- by rewrite 3!shrl_nil.
- + by rewrite addn0 shrl_0.
  + by rewrite -cats1 shrl_S addnS shrl_S -IH shrl_false.
Qed.

Lemma shrl_zeros : forall n m, shrl m (zeros n) = zeros n.
Proof.
elim => //=; first by move=> m; apply shrl_nil.
move=> n IHn [|m] //.
by rewrite shrl_false IHn.
Qed.

Lemma shrl_unfold : forall n h l, n <> O -> shrl n (h :: l) = false :: shrl (n.-1) (belast h l).
Proof. case=> //; move=> [|n]; by case. Qed.

Lemma shrl_app_zeros : forall k n l, size l = n ->
  shrl k (l ++ zeros k) = zeros k ++ l.
Proof.
elim.
- move=> n l Hlenl; by rewrite shrl_0 cats0.
- move=> k Hk n l Hlenl.
  destruct l as [|h t].
    by rewrite shrl_zeros cats0.
  rewrite cat_cons shrl_unfold //.
  rewrite -{2}add1n -{1}zeros_app catA belast_cat cats1 last_rcons belast_rcons.
  rewrite (_ : belast false (zeros k) = zeros k); last first.
    by elim: k {Hk} => // k /= ->.
  by rewrite (Hk n).
Qed.

Lemma shrl_tail : forall n l m, size l = n -> (m <= n)%coq_nat ->
  shrl m l = zeros m ++ take (n - m) l.
Proof.
elim.
- case=> //.
  case=> //.
  by inversion 2.
- move=> n IHn [|h t] // [|m] [Hlent].
  + move=> _.
    by rewrite shrl_0 /= take_oversize // Hlent.
  + move/le_S_n => Hmn.
    rewrite shrl_unfold // subSS IHn //; last by rewrite size_belast.
    rewrite [in X in X ++ _]/= -cat1s catA; congr cat.
    rewrite (lastI h t) -cats1 take_cat size_belast Hlent.
    rewrite -subSn; last by apply/leP.
    rewrite leq_subLR ltn_neqAle leq_addl andbT.
    case: ifP => // /negbT.
    rewrite negbK -{1}(add0n n) eqn_add2r => /eqP <-.
    by rewrite subn0 subnn cats0 take_oversize // size_belast Hlent.
Qed.

Lemma shrl_overflow: forall n lst k, size lst = n -> (n <= k)%nat -> shrl k lst = zeros n.
Proof.
elim => [| n IH].
- case=> // k _ _.
  by rewrite shrl_nil.
- elim/last_ind => tl hd _ //.
  move=> [ //|k] H nk.
  rewrite -cats1 shrl_S IH //.
  rewrite size_rcons in H; by case: H.
Qed.

Lemma shl_shrl n l k : size l = n -> k <= n ->
  shl k (shrl k l) = take (n - k) l ++ zeros k.
Proof.
move=> ln kn.
rewrite (shrl_tail n) //; last by apply/leP.
by rewrite shl_cat // size_nseq.
Qed.

(** arithmetic right shift (fill the freed bits with the bit-sign) *)

Definition shra (m : nat) (l : list bool) :=
  match l with
    | nil => nil
    | h :: t => h :: nseq (minn m (size t)) h ++ take (size t - m) t
  end.

Lemma shra_nil : forall m, shra m nil = nil. Proof. by case. Qed.

Lemma size_shra n m : forall l, size l = n -> size (shra m l) = n.
Proof.
case=> // h t.
case: n => // n /= [len_t].
rewrite size_cat; congr S.
rewrite size_take // size_nseq {}len_t.
rewrite -ltnS.
case: (leqP m n) => mn.
  rewrite -subSn // ltnS leq_subLR.
  case: (boolP (m == 0)) => [/eqP ->|m0]; first by rewrite min0n ltnn.
  move/minn_idPl : (mn) => ->.
  by rewrite -{1}(add0n n) ltn_add2r lt0n m0 addnBA // addnC addnK.
rewrite ltnS (_ : n - m = 0); last by apply/eqP; rewrite subn_eq0 ltnW.
rewrite minnC.
move/ltnW/minn_idPl : mn => ->.
by case: n => //= n; rewrite addn0.
Qed.

(** shift right and forget about the freed bits *)
Fixpoint shr_shrink n (l : list bool) : list bool :=
  match n with
    | 0 => l
    | n'.+1 => match l with
                | nil => nil
                | h :: t => shr_shrink n' (belast h t)
              end
  end.

Lemma shr_shrink_nil : forall n, shr_shrink n nil = nil.
Proof. induction n; by auto. Qed.

Lemma shr_shrink_S n h t : shr_shrink n.+1 (t ++ [:: h]) = shr_shrink n t.
Proof. rewrite /=; case: t => // t0 t1 /=; by rewrite cats1 belast_rcons. Qed.

Lemma size_shr_shrink : forall n m l, size l = n ->
  size (shr_shrink m l) = n - m.
Proof.
elim=> [m l H|n IH m l H].
- destruct l => //=.
  by rewrite shr_shrink_nil.
- elim/last_ind : l H => // h t _.
  rewrite size_rcons.
  case=> hn.
  destruct m => //=.
    by rewrite size_rcons hn subn0.
  rewrite -cats1.
  destruct h as [|h0 h1] => //=.
    by rewrite shr_shrink_nil /= -hn.
  by rewrite cats1 belast_rcons IH.
Qed.

Lemma shr_shrink_overflow : forall n lst, size lst <= n ->
  shr_shrink n lst = nil.
Proof.
elim => /=.
- case=> //=; by inversion 1.
- move=> n Hn [_ // | h t H].
  by rewrite Hn // size_belast.
Qed.

Lemma shr_shrink_is_take : forall m s n, size s = m -> shr_shrink n s = take (m - n) s.
Proof.
elim=> //.
  case => //= n _.
  by rewrite shr_shrink_nil.
move=> m IH.
elim/last_ind => h t // _ n.
rewrite size_rcons; case=> tm.
destruct n.
  by rewrite take_oversize // size_rcons tm.
rewrite -subSS -{2}(cats1 h t) -cats1 shr_shrink_S IH // 2!subSS take_cat.
destruct m as [|m] => //.
  by destruct h.
case: ifP => // /negbT.
rewrite -leqNgt => hm.
suff -> : n = 0.
  by rewrite subn0 tm subnn take0 take_oversize // ?cats0 // tm.
destruct n as [|n] => //.
rewrite subSS tm ltn_subRL in hm.
by rewrite -{2}(add0n m) ltn_add2r in hm.
Qed.

Lemma shr_shrink_adjust_u : forall l lst n, size lst = l -> l >= n ->
  shr_shrink n lst ++ adjust_u lst n = lst.
Proof.
move=> l lst n H1 H2.
by rewrite /adjust_u H1 ltnNge H2 /= (shr_shrink_is_take l) // cat_take_drop.
Qed.

Lemma shr_shrink_shrl : forall n l, size l = n -> forall k, k <= n ->
  zeros k ++ shr_shrink k l = shrl k l.
Proof.
move=> n l ln k kn.
rewrite (shrl_tail n) //; last by apply/leP.
by rewrite (shr_shrink_is_take n).
Qed.

Lemma shr_shrink_app : forall k l' l, size l' = k -> shr_shrink k (l ++ l') = l.
Proof.
move=> k l' l l'k.
by rewrite (shr_shrink_is_take (size (l ++ l'))) // size_cat l'k addnK take_cat ltnn subnn take0 cats0.
Qed.

(** bitwise-and *)
Definition bit_and a b := if (a, b) is (true, true) then true else false.

Fixpoint and a b :=
  if (a, b) is (h :: t, h' :: t') then bit_and h h' :: and t t' else nil.

Lemma size_and : forall n a b, size a = n -> size b = n ->
  size (and a b) = n.
Proof.
elim; first by case.
move=> n IH [|h t] // [|h' t'] // [H1] [H2]; by rewrite /= IH.
Qed.

Lemma andl0 : forall n l, size l = n -> and l (zeros n) = zeros n.
Proof.
elim; first by case.
move=> n IH [| [|] t] // [H] /=; by rewrite IH.
Qed.

Lemma andl1 : forall n l, size l = n -> and l (ones n) = l.
Proof.
elim; first by case.
move=> n IH [| [|] t] // [H] /=; by rewrite IH.
Qed.

Lemma and_app : forall n a a' b b', size a = n -> size a' = n ->
  and (a ++ b) (a' ++ b') = and a a' ++ and b b'.
Proof.
elim.
- by move=> [] [].
- move=> n IH [|a1 a2] // [|b1 b2] // a' b' [H1] [H2] /=.
  by rewrite IH.
Qed.

Lemma and_idempotent : forall n a, size a = n -> and a a = a.
Proof.
elim; first by case.
move=> n IH [|ha ta] // [Hlena] /=.
rewrite IH //.
by destruct ha.
Qed.

Lemma andC: forall n l k, size l = n -> size k = n -> and l k = and k l.
Proof.
elim.
- by move=> [|] // [|].
- move=> n IH [|[|] ta] // [|[|] tb] // [Ha] [Hb] /=; by rewrite /bit_and /= IH.
Qed.

(** bitwise-or *)
Definition bit_or a b :=
  match (a, b) with | (true, _) => true | (_, true) => true | _ => false end.

Lemma bit_or_false : forall b, bit_or b false = b. Proof. by case. Qed.

Fixpoint or a b {struct a} :=
  if (a, b) is (h :: t, h' :: t') then bit_or h h' :: or t t' else nil.

Lemma size_or : forall n a b, size a = n -> size b = n -> size (or a b) = n.
Proof.
elim=> //; first by case.
move=> n IH [|h t] // [|h' t'] // [H1] [H2]; by rewrite /= IH.
Qed.

Lemma orl0 : forall n l, size l = n -> or l (zeros n) = l.
Proof.
elim=> //; first by case.
move=> n IH [| [|] t] // [H1]; by rewrite /= IH.
Qed.

Lemma orC: forall n l k, size l = n -> size k = n -> or l k = or k l.
Proof.
elim.
- by move=> [|] // [|].
- move=> n IH [|[|] ta] // [|[|] tb] // [Ha] [Hb] /=; by rewrite /bit_or /= IH.
Qed.

Lemma or_idempotent : forall n a, size a = n -> or a a = a.
Proof.
elim; first by case.
move=> n IH [|ha ta] // [Hlena] /=.
rewrite IH //.
by destruct ha.
Qed.

Lemma nth_or : forall len n l k, size l = len -> size k = len ->
  nth true (or l k) n = bit_or (nth true l n) (nth true k n).
Proof.
elim=> /=.
- by move=> [|n] // [|hdl tll] // [|hdk tlk] // _ _.
- move=> len IHlen [|n] // [|[|] tll] // [|[|] tlk] // [Hl] [Hk] //=; by rewrite IHlen.
Qed.

Lemma take_or : forall len n a b, size a = len -> size b = len ->
  take n (or a b) = or (take n a) (take n b).
Proof.
elim=> /=.
by move=> [|n] [|] // [|].
move=> len IHlen [|n] // [|hda tla] // [|hdb tlb] // [Ha] [Hb] /=; by rewrite IHlen.
Qed.

Lemma drop_or : forall len n a b, size a = len -> size b = len ->
  drop n (or a b) = or (drop n a) (drop n b).
Proof.
elim=> /=.
- move=> [|n] [|] // [|] // _ _ /=; by rewrite skipn_nil.
- move=> len_cplt1 IHlen [|n] // [|hda tla] // [|hdb tlb] // [Ha] [Hb] /=; by rewrite IHlen.
Qed.

Lemma or_cat : forall n m a b a' b',
  size a = n -> size b = m -> size a' = n -> size b' = m ->
  or (a ++ b) (a' ++ b') = or a a' ++ or b b'.
Proof.
elim => [m | n IHn m].
- case => // b.
  by case.
- case=> hda tla // b.
  case=> hda' tla' // b' [Ha] Hb [Ha'] Hb'.
  by rewrite /= (IHn m).
Qed.

Lemma rev_or : forall len a b, size a = len -> size b = len ->
  rev (or a b) = or (rev a) (rev b).
Proof.
elim=> /=.
- by move=> [|n] [|] // [|].
- move=> len IHlen [|hda tla] // [|hdb tlb] // [Ha] [Hb] /=.
  by rewrite rev_cons IHlen // !rev_cons -!cats1 (or_cat len 1) // size_rev.
Qed.

Lemma cplt1_or : forall n a b, size a = n -> size b = n ->
  cplt1 (or a b) = and (cplt1 a) (cplt1 b).
Proof.
elim; first by case.
move=> n IH [|ha ta] // [|hb tb] // [Hlena] [Hlenb].
rewrite ![cplt1 _]/= IH //.
destruct ha => //.
by destruct hb.
Qed.

Lemma shr_or : forall n a (Ha : size a = n) b (Hb : size b = n) m,
  shl m (or a b) = or (shl m a) (shl m b).
Proof.
elim.
- by case=> // _ [] // _ /= [|m].
- move=> n IHn [|ha ta] // [Hlena] [|hb tb] // [Hlenb] [|m] //=.
  rewrite (or_cat n 1) //.
  by rewrite IHn.
  by apply size_shl.
  by apply size_shl.
Qed.

Lemma shrl_or : forall n a (Ha : size a = n) b (Hb : size b = n) m,
  shrl m (or a b) = or (shrl m a) (shrl m b).
Proof.
elim.
- case=> // _ [] // _ /= m.
  by rewrite shrl_nil.
- move=> n IHn a Hlena b Hlenb [|m].
  + by rewrite !shrl_0.
  + elim/last_ind : a Hlena => // ha ta _.
    rewrite size_rcons; case=> Ha.
    elim/last_ind : b Hlenb => // hb tb _.
    rewrite size_rcons; case=> Hb.
    rewrite -2!cats1 (or_cat n 1) //.
    rewrite 2!shrl_S [in RHS]/= -IHn //.
    by rewrite shrl_S.
Qed.

Lemma adjust_u_or : forall n a (Ha : size a = n) b (Hb : size b = n) m,
   adjust_u (or a b) m = or (adjust_u a m) (adjust_u b m).
Proof.
move=> n a Ha b Hb m.
rewrite /adjust_u.
rewrite (size_or n) // Ha Hb.
case: ifP => nm.
  by rewrite /zext (or_cat (m - n) n) // ?size_nseq // orl0 ?size_nseq.
by rewrite (drop_or n).
Qed.

(** bitwise-xor *)

Lemma bit_xor_tri_ine : forall a b c, xorb a b <= xorb a c + xorb c b.
Proof. by move=> [|] [|] [|]. Qed.

Fixpoint xor a b :=
  if (a, b) is (h :: t, h' :: t') then xorb h h' :: xor t t' else nil.

Lemma size_xor : forall n a b, size a = n -> size b = n -> size (xor a b) = n.
Proof. elim => [[] // | n IH [|h t] // [|h' t'] // [H1] [H2]]; by rewrite /= IH. Qed.

Lemma xor_app : forall a b c d, size a = size c ->
  xor (a ++ b) (c ++ d) = xor a c ++ xor b d.
Proof. elim => [? [] // | ha ta IH b [|hc tc] // d [Hac] /=]; by rewrite IH. Qed.

Lemma xorl0 : forall n l, size l = n -> xor l (zeros n) = l.
Proof. elim => [ [] // | n IH [| [|] t] // [H1]]; by rewrite /= IH. Qed.

Lemma xor_ones : forall n l, size l = n -> xor l (ones n) = cplt1 l.
Proof. elim => [ [] // | n IH [|h t] // [] t_n /=]; by rewrite Bool.xorb_true_r IH. Qed.

Lemma xorC : forall n a b, size a = n -> size b = n -> xor a b = xor b a.
Proof. elim=> [[|] // [|] // | n IH [|[|] ta] // [|[|] tb] // [Ha] [Hb] /=]; by rewrite /= IH. Qed.

Lemma xorA : forall n a b c, size a = n -> size b = n -> size c = n ->
  xor a (xor b c) = xor (xor a b) c.
Proof.
elim => [[|] // [|] // [|] // | n IH [|[|] ta] // [|[|] tb] // [|[|] tc] // [Ha] [Hb] [Hc] /=]; by rewrite /= IH.
Qed.

Lemma xor_self : forall n a, size a = n -> xor a a = zeros n.
Proof. elim => [ [] // | n IH [|[|] a] //= [H]]; by rewrite /= IH. Qed.

Lemma xor_map : forall n {A : Type} (a : list A) f g, size a = n ->
  xor (map f a) (map g a) = map (fun x => xorb (f x) (g x)) a.
Proof. elim => [? [] // | n IH A [|hd tl] // f g [H] /=]; by rewrite IH. Qed.

(** We model the hardware addition as a recursive function that does
bitwise comparisons and carry propagation. The last carry is ignored.
The least significant bit (LSb) is first. *)
Fixpoint add' a b c :=
  match (a, b) with
    | (false :: a', false :: b') => c :: add' a' b' false
    | (true :: a', true :: b') => c :: add' a' b' true
    | (_ :: a', _ :: b') => match c with false => true :: add' a' b' false | true => false :: add' a' b' true end
    | _ => nil
  end.

Lemma size_add' : forall a b, size a = size b ->
  forall carry, size (add' a b carry) = size a.
Proof.
elim=> //.
case=> tl IH [| [|] tl'] // ; case=> H [|] /=; by rewrite IH H.
Qed.

Lemma add'l0 : forall l zs, zs = zeros (size l) -> add' l zs false = l.
Proof. elim=> // h t IH zs -> /=. rewrite IH //; by case: h. Qed.

Lemma add'C : forall a b, add' a b false = add' b a false /\ add' a b true = add' b a true.
Proof.
induction a; induction b; auto.
destruct a; auto.
destruct a; auto.
destruct a; destruct a1=> //=.
by rewrite (proj2 (IHa b)).
by rewrite (proj1 (IHa b)) (proj2 (IHa b)).
by rewrite (proj1 (IHa b)) (proj2 (IHa b)).
by rewrite (proj1 (IHa b)).
Qed.

Lemma add'_inj : forall n a b c x, size a = n -> size b = n -> size c = n ->
  add' a c x = add' b c x -> a = b.
Proof.
elim.
  case => //.
  by case => //.
move=> n IH [|ha ta] // [|hb tb] // [|hc tc] // x [Hta] [Htb] [Htc] /=.
case: ifP => Hha.
- case: ifP => Hhc.
  + case: ifP => Hhb.
    * case.
      by move/(IH _ _ _ _ Hta Htb Htc) => ->.
    * by case: ifP => // Hx.
  + case: ifP => Hhx.
    * case: ifP => Hhb //.
      case.
      by move/(IH _ _ _ _ Hta Htb Htc) => ->.
    * case: ifP => Hhb //.
      case.                       
      by move/(IH _ _ _ _ Hta Htb Htc) => ->.
- case: ifP => Hhc.
  + case: ifP => Hhx.
    * case: ifP => Hhb //.
      case.
      by move/(IH _ _ _ _ Hta Htb Htc) => ->.
    * case: ifP => Hhb //.
      case.
      by move/(IH _ _ _ _ Hta Htb Htc) => ->.
  + case: ifP => Hhb.
    * by case: ifP => Hhx //.
    * case.
      by move/(IH _ _ _ _ Hta Htb Htc) => ->.
Qed.

(** Hardware addition with MSb first. *)
Definition add a b carry := rev (add' (rev a) (rev b) carry).

Lemma size_add n a b : size a = n -> size b = n ->
  forall carry, size (add a b carry) = n.
Proof.
move=> H H0 carry.
rewrite size_rev size_add'.
by rewrite size_rev.
by rewrite 2!size_rev H0.
Qed.

Lemma addC a b carry : add a b carry = add b a carry.
Proof.
unfold add.
case: (add'C (rev a) (rev b)) => H H0.
destruct carry.
by rewrite H0.
by rewrite H.
Qed.

Lemma addl0 : forall l zs, zs = zeros (size l) -> add l zs false = l.
Proof.
move=> l Hl H.
rewrite /add H rev_zeros -H (add'l0 (rev l)).
by rewrite revK.
by rewrite size_rev.
Qed.

Lemma carry_add l k zs : k.+1 = size l -> zs = zeros (size l) ->
  add l zs true = add l (zext k [:: true]) false.
Proof.
move=> H H0.
rewrite /add rev_zext_true H0 rev_zeros -H.
have [hd [tl ->]] : exists h t, l = h ++ [:: t].
  elim/last_ind : l H H0 => // h t ? ? _.
  by exists h, t; rewrite cats1.
by rewrite /= rev_cat.
Qed.

Lemma carry_add' l k : k.+1 = size l ->
  rev (add' l (zeros k.+1) true) = rev (add' l (rev (zext k [:: true])) false).
Proof.
move=>H.
move: (carry_add (rev l) k (rev (zeros k.+1))) => H1.
rewrite /add !revK in H1.
apply H1.
by rewrite size_rev.
by rewrite size_rev !rev_zeros H.
Qed.

Lemma add'_no_overflow : forall n l1 l2 c, size l1 = n.+1 -> size l2 = n.+1 ->
  add' (l1 ++ [:: false; false]) (l2 ++ [:: false; false]) c =
  (add' (l1 ++ [:: false]) (l2 ++ [:: false]) c) ++ [:: false].
Proof.
elim.
- by move=> [|[] []] // [|[] []] // [] _ _.
- move=> n IHn [|[] t1] // [|[] t2] // [] [Hl1] [Hl2] /=; by rewrite IHn.
Qed.

Lemma add_no_overflow : forall n l1 l2, size l1 = n -> size l2 = n ->
  add (false :: false :: l1) (false :: false :: l2) false = false :: add (false :: l1) (false :: l2) false.
Proof.
case.
- by case=> //; case.
- move=> n l1 l2 H1 H2; rewrite /add.
  rewrite ( _ : rev (false :: false :: l1) = rev l1 ++ [:: false; false]); last first.
    by rewrite (_ : [:: false, false & l1] = [:: false; false] ++ l1) // rev_cat.
  rewrite ( _ : rev (false :: false :: l2) = rev l2 ++ [:: false; false]); last first.
    by rewrite (_ : [:: false, false & l2] = [:: false; false] ++ l2) // rev_cat.
  by rewrite /= (add'_no_overflow n) ?size_rev // !cats1 !rev_cons rev_rcons.
Qed.

Lemma add'_leading_bit : forall n l1 l2 c, size l1 = n -> size l2 = n ->
  add' (l1 ++ [:: true; false]) (l2 ++ [:: false; false]) c =
  add' (l1 ++ [:: false; false]) (l2 ++ [:: true; false]) c.
Proof.
elim.
- by move=> [] [].
- move=> n IH [|h1 t1] // [|h2 t2] // c.
  rewrite [size _]/=; case=> H1.
  rewrite [size _]/=; case=> H2.
  destruct h1; destruct h2; destruct c=> //=; by rewrite IH.
Qed.

Lemma add_leading_bit : forall n l1 l2 c, size l1 = n -> size l2 = n ->
  add (false :: true :: l1) (false :: false :: l2) c = add (false :: false :: l1) (false :: true :: l2) c.
Proof.
move=> n l1 l2 c H1 H2.
rewrite /add /=.
have Htmp : forall b l, [:: false, b & l] = [:: false; b] ++ l by done.
rewrite (Htmp true l1) (Htmp false l2) (Htmp false l1) (Htmp true l2) // !rev_cat.
by rewrite (add'_leading_bit n) // size_rev.
Qed.

Local Open Scope coq_nat_scope.

Lemma add_carry_xchg : forall n l1 l2 l3 c1 c2,
  size l1 = n -> size l2 = n -> size l3 = n ->
  add (add l1 l2 c1) l3 c2 = add (add l1 l2 c2) l3 c1.
Proof.
elim => /=; first by case.
move=> n Hn l1 l2 l3 c1 c2 Hl1 Hl2 Hl3.
elim/last_ind : l1 Hl1 => // h1 t1 _ /=; rewrite size_rcons; case=> Hl1.
elim/last_ind : l2 Hl2 => // h2 t2 _ /=; rewrite size_rcons; case=> Hl2.
elim/last_ind : l3 Hl3 => // h3 t3 _ /=; rewrite size_rcons; case=> Hl3.
subst.
rewrite /add /= in Hn *.
case c1 => //.
- case c2 => //.
  case t1 => //.
  + case t2.
    * case t3; by rewrite !(rev_rcons, rev_cons).
    * case t3; by rewrite !(rev_rcons, rev_cons) Hn.
  + case t2.
    * case t3; by rewrite !(rev_rcons, rev_cons) Hn.
    * case t3; by rewrite !(rev_rcons, rev_cons).
- case c2 => //.
  case t1.
  + case t2.
    * case t3; by rewrite !(rev_rcons, rev_cons).
    * case t3; by rewrite !(rev_rcons, rev_cons) Hn.
  + case t2.
    * case t3; by rewrite !(rev_rcons, rev_cons) Hn.
    * case t3; by rewrite !(rev_rcons, rev_cons).
Qed.

Lemma addA : forall n l1 l2 l3 c1 c2,
  size l1 = n -> size l2 = n -> size l3 = n ->
  add (add l1 l2 c1) l3 c2 = add l1 (add l2 l3 c1) c2.
Proof.
elim => //=; first by case.
move=> n Hn l1 l2 l3 c1 c2 Hl1 Hl2 Hl3.
elim/last_ind : l1 Hl1 => // h1 t1 _ /=; rewrite size_rcons; case=> Hl1.
elim/last_ind : l2 Hl2 => // h2 t2 _ /=; rewrite size_rcons; case=> Hl2.
elim/last_ind : l3 Hl3 => // h3 t3 _ /=; rewrite size_rcons; case=> Hl3.
rewrite /add /= in Hn *.
case c1 => //=.
- case c2 => //=.
  - case t1 => //=.
    + case t2 => //=.
      * case t3 => //=; by rewrite !(rev_rcons, rev_cons) Hn.
      * case t3 => //=.
        - by rewrite !(rev_rcons, rev_cons) Hn.
        - rewrite !(rev_rcons, rev_cons).
          move: (add_carry_xchg n h1 h2 h3) => H.
          rewrite /add in H.
          by rewrite H // Hn.
    + case t2 => //=.
      * case t3 => //=; by rewrite !(rev_rcons, rev_cons) Hn.
      * case t3 => //=.
        - rewrite !(rev_rcons, rev_cons).
          move: (add_carry_xchg n h1 h2 h3) => H.
          rewrite /add in H.
          by rewrite H // Hn.
        - by rewrite !(rev_rcons, rev_cons) Hn.
  - case t1 => //=.
    + case t2 => //=.
      * case t3 => //=; by rewrite !(rev_rcons, rev_cons) Hn.
      * case t3.
        - by rewrite !(rev_rcons, rev_cons) Hn.
        - rewrite !(rev_rcons, rev_cons).
          move: (add_carry_xchg n h1 h2 h3) => H.
          rewrite /add in H.
          by rewrite H // Hn.
    + case t2 => //=.
      * case t3 => //=; by rewrite !(rev_rcons, rev_cons) Hn.
      * case t3 => //=.
        - rewrite !(rev_rcons, rev_cons).
          move: (add_carry_xchg n h1 h2 h3) => H.
          rewrite /add in H.
          by rewrite H // Hn.
        - by rewrite !(rev_rcons, rev_cons) Hn.
- case c2 => //=.
  - case t1 => //=.
    + case t2 => //=.
      * case t3 => //=.
        - by rewrite !(rev_rcons, rev_cons) Hn.
        - rewrite !(rev_rcons, rev_cons).
          move: (add_carry_xchg n h1 h2 h3) => H.
          rewrite /add in H.
          by rewrite H // Hn.
      * case t3 => //=; by rewrite !(rev_rcons, rev_cons) Hn.
    + case t2 => //=.
      * case t3 => //=.
        - rewrite !(rev_rcons, rev_cons).
          move: (add_carry_xchg n h1 h2 h3) => H.
          rewrite /add in H.
          by rewrite H // Hn.
        - by rewrite !(rev_rcons, rev_cons) Hn.
      * case t3 => //=; by rewrite !(rev_rcons, rev_cons) Hn.
  - rewrite !(rev_rcons, rev_cons).
    case t1 => //=.
    + case t2 => //=.
      * case t3 => //=.
        - by rewrite !(rev_rcons, rev_cons) Hn.
        - rewrite !(rev_rcons, rev_cons).
          move: (add_carry_xchg n h1 h2 h3) => H.
          rewrite /add in H.
          by rewrite H // Hn.
      * case t3 => //=; by rewrite !(rev_rcons, rev_cons) Hn.
    + case t2 => //=.
      * case t3.
        - rewrite !(rev_rcons, rev_cons).
          move: (add_carry_xchg n h1 h2 h3) => H.
          rewrite /add in H.
          rewrite H // Hn //.
        - by rewrite !(rev_rcons, rev_cons) Hn.
      * case t3; by rewrite !(rev_rcons, rev_cons) Hn.
Qed.

Local Close Scope coq_nat_scope.

Lemma add_cat_zeros : forall m n l1 l2, size l1 = n -> size l2 = n ->
  add l1 l2 false ++ zeros m = add (l1 ++ zeros m) (l2 ++ zeros m) false.
Proof.
induction m.
- simpl; intros.
  by rewrite !cats0.
- cutrewrite (zeros m.+1 = zeros m ++ [:: false]); last by rewrite -nseqS.
  unfold add.
  move=> n l1 l2 H H0.
  rewrite !rev_cat.
  simpl.
  unfold add in IHm.
  by rewrite -!rev_cat rev_cons -(IHm n) // -cats1 -catA.
Qed.

Lemma add'_cons_zeros : forall l m top, size l = m ->
  top :: l = add' (top :: zeros m) (false :: l) false.
Proof.
induction l.
- intros.
  destruct top; rewrite add'l0; by destruct m.
- intros.
  destruct top; by rewrite /= (proj1 (add'C (zeros m) (a :: l))) add'l0 // H.
Qed.

Lemma add'_zeros_cat : forall k n m l top, size k = n -> size l = m ->
  k ++ top :: l = add' (zeros n ++ top :: zeros m) (k ++ false :: l) false.
Proof.
induction k.
- intros => /=.
  rewrite (add'_cons_zeros l m top) //.
  by destruct n.
- intros => /=.
  destruct n => //.
  rewrite /= (IHk n m l top) //.
  by destruct a.
  by case: H.
Qed.

Lemma add'_zeros_cat2 : forall l1 l2,
  l1 ++ true :: l2 = add' (zeros (size l1) ++ true :: zeros (size l2)) (l1 ++ false :: l2) false.
Proof. intros; by rewrite (add'_zeros_cat l1 (size l1) (size l2) l2). Qed.

Lemma add_zeros_cat : forall l1 l2,
  l1 ++ true :: l2 = add (zeros (size l1) ++ true :: zeros (size l2)) (l1 ++ false :: l2) false.
Proof.
intros.
rewrite /add 2!rev_cat 2!rev_cons /= 2!rev_zeros.
move: (add'_zeros_cat2 (rev l2) (rev l1)) => H.
rewrite 2!size_rev in H.
do 2 rewrite -cats1 -catA.
by rewrite -H rev_cat rev_cons 2!revK -cats1 -catA.
Qed.

Lemma add'_app : forall n l m l', size l = n -> size l' = m ->
  add' (l ++ zeros m) (zeros n ++ l') false = l ++ l'.
Proof.
induction n.
- intros.
  destruct l; last by done.
  by rewrite /= (proj1 (add'C (zeros m) l')) add'l0 // H0.
- intros.
  simpl.
  destruct l; first by done.
  case: H => H.
  destruct b; by rewrite /= IHn.
Qed.

Lemma add_app : forall n l m l', size l = m -> size l' = n ->
  add (zeros m ++ l') (l ++ zeros n) false = l ++ l'.
Proof.
intros.
rewrite /add 2!rev_cat 2!rev_zeros add'_app.
by rewrite rev_cat 2!revK.
by rewrite size_rev.
by rewrite size_rev.
Qed.

(** subtraction *)

Fixpoint sub' (a b : list bool) (borrow : bool) {struct a} : list bool :=
  match (a, b) with
    | (false :: tla, false :: tlb) =>
    match borrow with
      | false => false :: sub' tla tlb false
      | true => true :: sub' tla tlb true
    end
    | (true :: tla, true :: tlb) =>
      match borrow with
        | false => false :: sub' tla tlb false
        | true => true :: sub' tla tlb true
      end
    | (true :: tla, false :: tlb) =>
      match borrow with
        | false => true :: sub' tla tlb false
        | true => false :: sub' tla tlb false
      end
    | (false :: tla, true :: tlb) =>
      match borrow with
        | false => true :: sub' tla tlb true
        | true => false :: sub' tla tlb true
      end
    | _ => nil
  end.

Definition sub (a b : list bool) (bor : bool) := rev (sub' (rev a) (rev b) bor).

Lemma size_sub : forall n a b bor, size a = n -> size b = n ->
  size (sub a b bor) = n.
Proof.
induction n.
- move=> [|ha ta] // [|hb tb] // bor Ha Hb.
- move=> a b bor Ha Hb.
  elim/last_ind : a Ha => // ta ha _; rewrite size_rcons; case=> Ha.
  elim/last_ind : b Hb => // tb hb _; rewrite size_rcons; case=> Hb.
  rewrite /sub !rev_rcons /=.
  rewrite /sub in IHn.
  by destruct ha; destruct hb; destruct bor; rewrite rev_cons size_rcons IHn.
Qed.

Lemma sub_add_cplt1 : forall n (a b : list bool),
  size a = n -> size b = n -> forall c,
  sub a b c = add a (cplt1 b) (negb c).
Proof.
elim; first by case.
move=> n IH a b Ha Hb c.
have [ha [ta hta]] : exists ha ta, a = ha ++ [:: ta].
  elim/last_ind : a Ha => // ha ta _ _.
  by exists ha, ta; by rewrite -cats1.
have [hb [tb htb]] : exists hb tb, b = hb ++ [:: tb].
  elim/last_ind : b Hb => // hb tb _ _.
  by exists hb, tb; by rewrite -cats1.
rewrite {1}hta {1}htb /sub.
rewrite !rev_cat /=.
have Hha : size ha = n.
  rewrite hta size_cat /= addn1 in Ha; by case: Ha.
have Hhb : size hb = n.
  rewrite htb size_cat /= addn1 in Hb; by case: Hb.
destruct ta.
- destruct tb.
  + have : sub ha hb c = add ha (cplt1 hb) (~~ c).
       by apply IH.
    rewrite /= {1}/sub.
    destruct c => /=; rewrite rev_cons => ->;
      by rewrite hta htb {2}/add rev_cat /= cplt1_cat rev_cat /= rev_cons.
  + have : sub ha hb false = add ha (cplt1 hb) (~~ false) by apply IH.
    destruct c => /=; rewrite rev_cons;
      rewrite /= {1}/sub => ->;
      by rewrite hta htb {2}/add rev_cat /= cplt1_cat rev_cat /= rev_cons.
- destruct tb.
  + have : sub ha hb true = add ha (cplt1 hb) (~~ true) by apply IH.
    rewrite /= {1}/sub.
    destruct c => /=; rewrite rev_cons => ->;
      by rewrite hta htb {2}/add rev_cat /= cplt1_cat rev_cat /= rev_cons.
  + destruct c => /=.
      have : sub ha hb true = add ha (cplt1 hb) (~~ true) by apply IH.
      rewrite /= {1}/sub rev_cons => ->.
      by rewrite hta htb {2}/add rev_cat /= cplt1_cat rev_cat rev_cons.
    have : sub ha hb false = add ha (cplt1 hb) (~~ false) by apply IH.
    rewrite /= {1}/sub rev_cons => ->.
    by rewrite hta htb {2}/add rev_cat /= cplt1_cat rev_cat rev_cons.
Qed.

(** two's complement *)
Definition cplt2 l := add (cplt1 l) (zext (size l - 1) [:: true]) false.

Lemma cplt2_inj n a b : size a = n.+1 -> size b = n.+1 ->
  cplt2 a = cplt2 b -> a = b.
Proof.
move=> Ha Hb.
rewrite /cplt2 /add.
move/(ssrfun.congr1 (fun x => rev x)); rewrite !revK.
rewrite Ha Hb.
move/(@add'_inj n.+1).
rewrite 3!size_rev 2!size_cplt1.
move/(_ Ha Hb).
rewrite /zext size_cat size_nseq /= subn1 /= addn1.
move/(_ Logic.eq_refl).
move/(ssrfun.congr1 (fun x => rev x)); rewrite !revK.
by eapply cplt1_inj; eauto.
Qed.

Definition size_cplt2 : forall l, size (cplt2 l) = size l.
Proof.
case=> [|hd tl] //.
rewrite /cplt2 (size_add (size (hd :: tl))) //.
- by rewrite size_cplt1.
- by rewrite (size_zext 1) //= addn1 subSS subn0.
Qed.

Lemma cplt2_nil : forall l, l <> nil -> cplt2 l <> nil.
Proof.
move=> l H H0.
apply H => {H}.
destruct l; first by done.
have H : size (cplt2 (b :: l)) = O by rewrite H0.
by rewrite size_cplt2 in H.
Qed.

Lemma cplt2_zeros : forall k, cplt2 (zeros k) = zeros k.
Proof.
elim => // k IHk.
rewrite /cplt2 /add in IHk *.
rewrite size_nseq subSS subn0 cplt1_zeros rev_ones /zext rev_cat rev_zeros /=.
destruct k; first by done.
rewrite rev_cons carry_add'; last by rewrite size_nseq.
rewrite size_nseq subSS subn0 cplt1_zeros rev_ones in IHk.
by rewrite IHk -cats1 -nseqS.
Qed.

(** the two's complement of the weird number is itself *)

Lemma cplt2_weird : forall k, cplt2 (true :: zeros k) = true :: zeros k.
Proof.
elim => //= k IHk.
rewrite /cplt2 /add /zext /= size_nseq /subn /= -/subn subn0 in IHk.
rewrite /cplt2 /add /= !rev_cons -(cats1 _ true).
have -> : rev (cplt1 (zeros k)) ++ [:: true] = true :: rev (cplt1 (zeros k)).
  by rewrite cplt1_zeros rev_ones -nseqS.
have H : rev (zeros k ++ [:: true]) = true :: zeros k.
  by rewrite rev_cat /= rev_zeros.
rewrite size_nseq rev_cat /= rev_zeros -(cats1 (zeros k) false) -nseqS rev_cons carry_add'; last first.
  by rewrite size_rcons size_rev size_cplt1 size_nseq.
rewrite rev_cons in IHk.
by rewrite zext_true IHk rcons_cons /= -cats1 -cat1s -nseqS.
Qed.

Lemma two2one : forall l, size l > O ->
  cplt2 (l ++ [:: false]) = add (cplt1 l ++ [:: true]) (zext (size l) [:: true]) false.
Proof.
elim=> // hd tl IH H.
by rewrite /cplt2 /= size_cat /= subSS subn0 cplt1_cat /= addn1.
Qed.

Lemma one2two : forall l, size l > 0 ->
  add (cplt1 l ++ [:: true]) (zext (size l) [:: true]) false = cplt2 l ++ [:: false].
Proof.
elim=> // hd tl IH H.
rewrite /cplt2 /= subSS subn0 /add.
rewrite rev_cons -cats1.
have -> : rev (cplt1 tl ++ [:: true]) = true :: rev (cplt1 tl) by rewrite rev_cat.
rewrite /zext.
rewrite rev_cat /=.
rewrite rev_cons.
rewrite rev_cons.
rewrite -(cats1 (rev (zeros _))).
rewrite rev_zeros -nseqS.
rewrite carry_add'.
  rewrite -cats1.
  by rewrite !rev_cons -cats1.
by rewrite size_cat size_rev size_cplt1 addn1.
Qed.

Lemma cplt2_involutive_false : forall l, l <> nil -> ~ (exists k, l = zeros k) ->
  cplt2 (l ++ [:: false]) = cplt2 l ++ [:: false].
Proof. elim=> // hd tl IH H H'; by rewrite two2one // one2two. Qed.

Lemma cplt2_involutive_true : forall l, l <> nil -> cplt2 (l ++ [:: true]) = cplt1 l ++ [:: true].
Proof.
case=> // hd tl _.
rewrite /cplt2 /= subSS subn0 size_cat /= /add /=.
rewrite rev_cons.
have -> : rev (cplt1 (tl ++ [:: true])) = false :: rev (cplt1 tl).
  by rewrite cplt1_cat /= rev_cat.
have -> : rev (zext (size tl + 1) [:: true]) = true :: zeros (size tl + 1).
  by rewrite /zext rev_cat /= rev_zeros.
rewrite /= add'l0.
- by rewrite -cats1 rev_cons rev_cat revK rcons_cat cats1.
- by rewrite -cats1 size_cat size_rev size_cplt1.
Qed.

Lemma cplt2_ones : forall n, cplt2 (ones n) = adjust_u [:: true] n.
Proof.
case=> [ // | [ // |n]].
rewrite /ones.
rewrite (nseqS n.+1 true).
rewrite cplt2_involutive_true //.
rewrite (adjust_u_S'' n.+2 1 [:: true] (refl_equal _) (refl_equal _)) /=.
suff : cplt1 (ones n) = zeros n by move=> ->.
by rewrite -(cplt1_involutive (zeros n)) cplt1_zeros.
Qed.

(** two-complement is involutive *)

Lemma cplt2_involutive l : cplt2 (cplt2 l) = l.
Proof.
move H0 : (size l) => k.
move: l H0.
induction k; intros.
- by destruct l.
- case: (dec_equ_lst_bit' l (zeros (size l)))=> H.
  + rewrite H cplt2_zeros cplt2_zeros //.
  + have [l' [H1 | H1]] : exists l', l = l' ++ [:: false] \/ l = l' ++ [:: true].
      have H1 : (size l > 0)%coq_nat.
        rewrite H0; by apply/ltP.
      elim/last_ind : l H0 H H1 => // h t _ H0 H H1.
      exists h.
      rewrite !cats1; by destruct t; auto.
    * rewrite H1.
      destruct l'; first by done.
      rewrite cplt2_involutive_false //; last first.
        move=> [x H3].
        apply H.
        destruct x; first by done.
        case: H3 => ? H4; subst b.
        by rewrite H1 /= H4 -nseqS // size_nseq.
      rewrite cplt2_involutive_false; last 2 first.
        move=> H2.
        move: (size_cplt2 (b :: l')).
        rewrite H2 //.
        move=> [x H3].
        have H2 : size (b :: l') = k.
          rewrite H1 size_cat addn1 in H0; by case: H0.
        move: (IHk _ H2) => H4.
        rewrite H3 cplt2_zeros in H4.
        destruct b.
        - by destruct x.
        - apply H.
          by rewrite H1 -H4 /= -nseqS size_nseq.
      rewrite H1 size_cat /= in H0.
      rewrite IHk //=.
      case: H0 => <-.
      by rewrite -addn1.
    * rewrite H1.
      destruct l'; first by done.
      by rewrite cplt2_involutive_true // cplt2_involutive_true // cplt1_involutive.
Qed.

Lemma cplt2_prop tl : ~ (exists k, tl = zeros k) ->
  forall hd, ~ (exists k, hd :: tl = true :: zeros k) ->
    cplt2 (hd :: tl) = cplt hd :: cplt2 tl.
Proof.
move H0 : (size tl) => k.
move: tl H0.
induction k.
- intros.
  have : exists k, tl = zeros k.
    exists O => //.
    by destruct tl.
  contradiction.
- intros.
  destruct k.
  + destruct tl=> //.
    case: H0 => H0.
    destruct tl.
    rewrite /cplt2.
    destruct hd; destruct b=> //=.
    have H3 : exists k, [:: false] = zeros k by exists 1%nat.
    contradiction.
    have H3 : exists k, [:: false] = zeros k by exists 1%nat.
    contradiction.
    rewrite //= in H0.
  + have [x H3] : exists tl' b, tl = tl' ++ [:: b].
      elim/last_ind : tl H0 H H1 => // tl' tl'' _ H0 H H1.
      exists tl', tl''; by rewrite cats1.
    inversion_clear H3 as [c H2].
    have H3 : ( hd :: x ++ [:: c] = (hd :: x) ++ [:: c]) by done.
    rewrite H2 H3{H3}.
    destruct c.
    * rewrite cplt2_involutive_true //.
      rewrite cplt2_involutive_true; last first.
        move=> H3.
        rewrite H3 in H2.
        by rewrite H2 in H0.
      by destruct hd.
    * rewrite cplt2_involutive_false //; last first.
        move=> [x0 H4].
        apply H1.
        have H3 : exists k, tl = zeros k.
          rewrite H2.
          exists x0.
          destruct x0; first by done.
          case: H4 => H3 -> /=.
          by rewrite -nseqS.
        contradiction.
      rewrite IHk //; last 3 first.
        rewrite H2 size_cat /= addn1 in H0; by case: H0.
        move=> [x0 H4].
        apply H.
        exists x0.+1.
        by rewrite H2 H4 -nseqS.
        move=> [x0 H4].
        apply H.
        case:H4 => ? H4; subst hd.
        rewrite H2 H4.
        exists x0.+1; by rewrite /= -nseqS.
      rewrite cplt2_involutive_false //; last 2 first.
        move=> H3.
        rewrite H3 in H2.
        by rewrite H2 in H0.
        case => x0 H4.
        apply H.
        rewrite H2.
        exists x0.+1; by rewrite /= H4 -nseqS.
Qed.

(** unsigned multiplication (result on 2*n bits) *)
Fixpoint umul (a b : list bool) {struct b} :=
  match b with
    | nil => zeros (size a)
    | io :: tl => match io with
                  | false => false :: umul a tl
                  | true => add (false :: a ++ zeros (size tl)) (false :: umul a tl)
      	            false
                end
  end.

Lemma size_umul a b : size (umul a b) = size a + size b.
Proof.
elim: b a => [a /=|h t IH a /=]; first by rewrite /zeros size_nseq addn0.
case: ifPn => /= Hh; last by rewrite IH addnS.
rewrite (size_add (size a + (size t).+1)) //=; last by rewrite IH addnS.
by rewrite size_cat /zeros size_nseq addnS.
Qed.

Lemma umulnill : forall l, umul nil l = zeros (size l).
Proof.
elim=> // hd tl IH.
destruct hd => /=.
- by rewrite IH addl0 //= size_nseq.
- by rewrite IH.
Qed.

Lemma umull0 : forall n a, umul a (zeros n) = zeros (size a + n).
Proof.
elim=> [a /= | n IH [| h t]].
- by rewrite <- plus_n_O.
- by rewrite /= umulnill size_nseq.
  by rewrite [umul _ _]/= IH [size _]/= addnS.
Qed.

Lemma umul_leading_false : forall l1 l2, l1 <> nil -> l2 <> nil ->
  umul (false :: l1) l2 = false :: umul l1 l2.
Proof.
induction l1.
- destruct l2; tauto.
- move=> l2 _ H0; move: l2 H0.
  induction l2; first by tauto.
  move=> H0.
  destruct a0.
  + rewrite /=.
    destruct l2.
    * rewrite /= (add_no_overflow (size l1).+1) //.
      by rewrite /= size_cat /= addnC.
      by rewrite /= size_nseq.
    * rewrite IHl2 //.
      rewrite (add_no_overflow (size l1 + size l2).+2) //.
      - by rewrite /= size_cat /= size_nseq addnS.
      - by rewrite size_umul /= addSn addnS.
  + rewrite /=.
    destruct l2; first by done.
    by rewrite IHl2.
Qed.

Lemma umul_leading_false' : forall l1 l2, l1 <> nil -> l2 <> nil ->
  umul l1 (false :: l2) = false :: umul l1 l2.
Proof.
induction l1.
- destruct l2; tauto.
- move=> l2 _ H0; move: l2 H0.
  induction l2; tauto.
Qed.

Lemma umul_leading_true : forall l2 l1,
  umul (true :: l1) l2 = add (false :: l2 ++ zeros (size l1)) (false :: umul l1 l2) false.
Proof.
induction l2.
  induction l1; auto.
  by rewrite /= addl0 //= size_nseq.
- intros.
  destruct a.
  + rewrite /= IHl2.
    rewrite <- (add_no_overflow (size l1 + size l2)).
    rewrite <- (addA (size l1 + size l2 + 2)).
    rewrite (add_leading_bit (size l1 + size l2)).
    rewrite <-(add_no_overflow (size l1 + size l2)).
    rewrite <- (addA (size l1 + size l2 + 2)).
    rewrite (addC (false :: false :: l1 ++ zeros (size l2)) (false :: true :: l2 ++ zeros (size l1)) false).
    auto.
    rewrite /= size_cat size_nseq //=.
    nat_norm.
    by rewrite addnC.
    by rewrite /= size_cat size_nseq //= addn2.
    by rewrite /= size_umul addn2.
    rewrite /= size_cat size_nseq //=; ring.
    rewrite /= size_umul; ring.
    rewrite /= size_cat size_nseq //=; ring.
    by rewrite /= size_cat size_nseq //= addnC.
    by rewrite /= size_cat size_nseq //= addn2.
    by rewrite /= size_cat size_nseq //= addn2 addnC.
    by rewrite /= size_umul addn2.
    by rewrite /= size_cat size_nseq //= addnC.
    rewrite /= size_umul; ring.
  + rewrite /= IHl2 (add_no_overflow (size l1 + size l2)) //.
    rewrite size_cat size_nseq //=; by nat_congr.
    by rewrite size_umul.
Qed.

Lemma umulC : forall n l2 l1, size l1 = n -> size l2 = n -> n > 0 ->
  umul l1 l2 = umul l2 l1.
Proof.
induction n=> //.
move=> [|hd2 l2] // [|hd1 l1] //= [H] [H0] _.
destruct n.
  by destruct l1=> //; destruct l2=> //=; destruct hd2; destruct hd1.
destruct hd2.
- destruct hd1.
  + rewrite /= 2!umul_leading_true.
    rewrite H H0 /=.
    rewrite -(add_no_overflow (n.+1 + n.+1)); last 2 first.
      by rewrite /= size_cat /= size_nseq H0.
      by rewrite /= size_umul H H0.
    rewrite -(add_no_overflow (n.+1 + n.+1)); last 2 first.
      by rewrite /= size_cat /= size_nseq H.
      by rewrite /= size_umul H H0.
    rewrite -(addA (size l1 + size l2 + 2)); last 3 first.
      by rewrite /= size_cat /= size_nseq H H0; nat_norm.
      by rewrite /= size_cat /= size_nseq H H0; nat_norm.
      by rewrite /= size_umul; nat_norm.
    rewrite (add_leading_bit (n.+1 + n.+1)); last 2 first.
      by rewrite /= size_cat /= size_nseq H.
      by rewrite /= size_cat /= size_nseq H0.
    rewrite -(addA (size l1 + size l2 + 2)); last 3 first.
      by rewrite /= size_cat /= size_nseq H H0; nat_norm.
      by rewrite /= size_cat /= size_nseq H H0; nat_norm.
      by rewrite /= size_umul addnC; nat_norm.
    by rewrite (addC (false :: false :: l1 ++ false :: zeros n) (false :: true :: l2 ++ false :: zeros n) false) IHn.
  + rewrite /= umul_leading_false; last 2 first.
      by move=> X; subst.
      by move=> X; subst l2.
    rewrite umul_leading_true (add_no_overflow (n.+1 + n.+1)); last 2 first.
      by rewrite size_cat size_nseq H H0.
      by rewrite size_umul H H0.
    by rewrite IHn.
- destruct hd1.
  + rewrite /= umul_leading_false; last 2 first.
      by move=> X; subst.
      by move=> X; subst.
    rewrite H /= (add_no_overflow (n.+1 + n.+1)).
    by rewrite umul_leading_true H IHn.
    by rewrite size_cat /= size_nseq // H0.
    by rewrite size_umul H H0.
  + rewrite /= umul_leading_false //; last 2 first.
      by intro; subst.
      by intro; subst.
    rewrite umul_leading_false //; last 2 first.
      by intro; subst.
      by intro; subst.
    by rewrite IHn.
Qed.

Lemma umul_zero : forall b a, umul a (b ++ [:: false]) = umul a b ++ [:: false].
Proof.
elim=> [|hb tb IHb].
- move=> l1 /=; by rewrite -nseqS.
- destruct hb=> l1 /=.
  + rewrite IHb /add /=.
    have -> : size (tb ++ [:: false]) = (size tb).+1.
      by rewrite size_cat /= addn1.
    rewrite !rev_cons !rev_cat.
    rewrite /zeros (nseqS (size tb) false).
    rewrite rev_cat rcons_cat /=.
    by rewrite rcons_cat rev_cons -cats1.
  + by rewrite IHb.
Qed.

Lemma umull1 : forall l lst, size lst = l.+1 ->
  umul lst (zeros l ++ [:: true]) = zeros l.+1 ++ lst.
Proof.
elim.
- by move=> [|[] [|]].
- move=> l IHl [|b lst] //= [H] /=.
  destruct b.
  + f_equal.
    rewrite umul_leading_true IHl //=.
    have -> : false :: (zeros l ++ [:: true]) ++ zeros (size lst) =
        zeros (size (zeros l.+1)) ++ true :: zeros (size lst).
      by rewrite /= size_nseq -catA.
    have -> : false :: zeros l.+1 ++ lst = zeros l.+1 ++ false :: lst.
      by rewrite -[in RHS](cat1s false) catA -nseqS.
    by rewrite -add_zeros_cat.
  + rewrite umul_leading_false; last 2 first.
      by move=> ?; subst.
      by move=> ?; destruct l.
    by rewrite IHl // -(cat1s false lst) catA -nseqS.
Qed.

Lemma umul_zero_list: forall n l1 l2, umul l1 (l2 ++ zeros n) = umul l1 l2 ++ zeros n.
Proof.
elim=> [|n IHn] a b.
- by rewrite /= !cats0.
- have -> : zeros n.+1 = zeros n ++ [:: false] by rewrite -nseqS.
  by rewrite 2!catA (umul_zero (b ++ zeros n) a) IHn.
Qed.

Lemma umul_weird : forall l,
  umul (true :: zeros l) (true :: zeros l) = false :: true :: zeros (l + l).
Proof.
move=> [|n] /=.
- by rewrite addl0.
- by rewrite size_nseq umull0 addl0 -zeros_app //= size_cat /= size_nseq zeros_app -addSnnS addSn.
Qed.

Lemma umul_weird' : forall n l k, size k = n ->
  umul k (true :: zeros l) = false :: k ++ zeros l.
Proof.
induction n.
- elim=> k H.
  + by rewrite /= cats0 addl0.
  + move=> [|k0] // Hk0.
    by rewrite umulnill /= size_nseq.
- induction l=> k H.
  + by rewrite /= addl0 // cats0.
  + destruct k=> //.
    rewrite /= in H.
    case: H => H.
    destruct b.
    * rewrite umul_leading_true.
      have -> : true :: zeros l.+1 = (true :: zeros l) ++ [:: false].
        by rewrite /= -nseqS.
      rewrite umul_zero IHn //= -2!catA /=.
      move: (add_zeros_cat [:: false] (k ++ false :: zeros l)) => /= ->.
      match goal with
          | |- add ?L ?K _ = add ?M ?N _ => have H1 : L = M /\ K = N
      end.
      rewrite size_cat /= size_nseq addnC addSn /= -zeros_app.
      split=> //.
      by rewrite -[in X in _ ++ X](cat1s false) catA -nseqS.
      by rewrite -nseqS.
      by rewrite (proj1 H1); rewrite (proj2 H1).
   * destruct k as [|b k].
     - rewrite /= umull0 /= addl0.
       by rewrite size_nseq.
       by rewrite size_nseq /= size_nseq.
     - rewrite umul_leading_false //.
       have -> : true :: zeros l.+1 = (true :: zeros l) ++ [:: false] by rewrite /= -nseqS.
       by rewrite umul_zero IHn //= -catA -nseqS.
Qed.

(** signed multiplication *)
Definition is_pos (a : list bool) : bool := if a is true :: _ then false else true.

Definition smul (a b : list bool) :=
  match is_pos a, is_pos b with
    | true, true => umul a b
    | false, false => umul (cplt2 a) (cplt2 b)
    | true, false => cplt2 (umul a (cplt2 b))
    | false, true => cplt2 (umul (cplt2 a) b)
  end.

Lemma size_smul n (a b : list bool) :
  size a = n -> size b = n -> size (smul a b) = 2 * n.
Proof.
move=> Ha Hb.
destruct a; destruct b.
- by destruct n.
- by destruct n.
- by destruct n.
- rewrite /= in Ha, Hb.
  destruct b0; destruct b.
  + by rewrite /smul /= size_umul 2!size_cplt2 /= Ha Hb addnn mul2n.
  + by rewrite /smul /= size_cplt2 /= size_umul size_cplt2 /= Ha -Hb addSn addnn mul2n.
  + by rewrite /smul /= size_cplt2 size_umul size_cplt2 /= Ha Hb addnn mul2n.
  + by rewrite /= size_umul /= Ha -Hb addSn addnn mul2n.
Qed.
 
Lemma smulC n a b : size a = n.+2 -> size b = n.+2 -> smul a b = smul b a.
Proof.
move=> H H0.
destruct a; destruct b=> //.
destruct b; destruct b0; rewrite /smul //.
- by rewrite (umulC n.+2 (cplt2 (true :: a)) (cplt2 (true :: b1))) // size_cplt2.
- by rewrite (umulC n.+2 (false :: a) (cplt2 (true :: b1))) // size_cplt2.
- by rewrite (umulC n.+2) // (umulC n.+2 (cplt2 (true :: a)) (false :: b1)) // size_cplt2.
- by rewrite (umulC n.+2).
Qed.

(** Booth algorithm (definition only) *)
Definition shift_right_1 := shrl 1.

Fixpoint booth_mul' (a s p : list bool) (n : nat) : list bool :=
  match n with
    | O => p
    | m.+1 =>
      match rev p with
        | false :: false :: _ => booth_mul' a s (shift_right_1 p) m
        | true :: true :: _ => booth_mul' a s (shift_right_1 p) m
        | true :: false :: _ => booth_mul' a s
          (shift_right_1 (add p a false)) m (* ignore overflow *)
        | false :: true :: _ => booth_mul' a s
          (shift_right_1 (add p s false)) m (* ignore overflow *)
        | _ => nil
      end
  end.

(** works only with s =/= weird number *)
Definition booth_mul (a s : list bool) := idel_last
(booth_mul'
  (shl_ext (size s + 1) a)
  (shl_ext (size s + 1) (cplt2 a))
  (zext (size a) (shl_ext 1 a))
  (size s)).

Lemma size_booth_mul' : forall (k : nat) (a s p : list bool),
  size p = size s -> size p = size a -> (1 < size p) ->
  size (booth_mul' a s p k) = size p.
Proof.
elim=> //.
move=> k IHk a s p H H0 H1.
elim/last_ind : p H H0 H1 => // p' y _ H H0 H1.
rewrite size_rcons in H, H0, H1.
elim/last_ind : p' H H0 H1 => // p x _ H H0 H1.
rewrite size_rcons in H, H0, H1.
rewrite -!cats1 /=.
rewrite !rev_cat /=.
rewrite H in H1.
rewrite H in H0.
by destruct y; destruct x;
  rewrite IHk //;
    rewrite /shift_right_1 (size_shrl (size s)) // ?(size_add (size s)) // ?size_cat /= ?addn1 //.
Qed.

Definition size_booth_mul a b : size a = size b ->
  0 < size b -> size (booth_mul a b) = 2 * size a.
Proof.
move=> H H0.
rewrite /booth_mul.
rewrite size_idel_last'.
- rewrite size_booth_mul'.
  + rewrite (size_zext (size a).+1).
    * rewrite mul2n -addnn subn1; by nat_norm.
    * by rewrite (size_shl_ext (size a)).
  + rewrite (size_zext (size a).+1).
    * rewrite (size_shl_ext (size a)).
      - by rewrite H addn1 addnC.
      - by apply size_cplt2.
      - by rewrite (size_shl_ext (size a)).
  + rewrite (size_zext (size a).+1).
    * by rewrite (size_shl_ext (size a)) // H addn1 addnC.
    * by rewrite (size_shl_ext (size a)).
  + rewrite (size_zext (size a).+1).
    * by rewrite ltn_addl // ltnS H.
    * by rewrite (size_shl_ext (size a)).
- rewrite size_booth_mul'.
  + rewrite (size_zext (size a).+1).
    * by rewrite ltn_addl // ltnS H.
    * by rewrite (size_shl_ext (size a)).
  + rewrite (size_zext (size a).+1).
    * rewrite (size_shl_ext (size a)) //.
      - by rewrite H addn1 addnC.
      - by apply size_cplt2.
    * by rewrite (size_shl_ext (size a)).
  + rewrite (size_zext (size a).+1).
    * by rewrite (size_shl_ext (size a)) // H addn1 addnC.
    * by rewrite (size_shl_ext (size a)).
  + rewrite (size_zext (size a).+1).
    * by rewrite ltn_addl // ltnS H.
    * by rewrite (size_shl_ext (size a)).
Qed.

(** comparisons *)
Fixpoint listbit_eq (a b : seq bool) :=
  match (a, b) with
    | (hd :: tl, hd' :: tl') => if hd == hd' then listbit_eq tl tl' else false
    | (nil, nil) => true
    | _ => false
  end.

Lemma listbit_eq_refl : forall l, listbit_eq l l.
Proof. elim=> // hd tl IH /=; by rewrite eqxx. Qed.

Lemma listbit_eq_eq : forall a b, listbit_eq a b -> a = b.
Proof.
elim; first by case.
move=> hd tl H [|h t] //=.
by case: ifP => // /eqP -> /H ->.
Qed.

Fixpoint ult (a b : list bool) {struct a} : bool :=
  match a with
    | false :: tla =>
      match b with
        | false :: tlb => ult tla tlb
        | true :: _ => true
        | _ => false (* could not happen with lists of the same size *)
      end
    | true :: tla =>
      match b with
        | false :: _ => false
        | true :: tlb => ult tla tlb
        | _ => false (* could not happen with lists of the same size *)
      end
    | _ => false
  end.

Lemma ult_zeros : forall l, ult l (zeros (size l)) = false.
Proof. elim=> //; by case. Qed.

Definition ule a b := ult a b || listbit_eq a b.

Lemma ule_0 : forall n lst, size lst = n -> ule (zeros n) lst.
Proof.
elim; first by case.
move=> n IHn [|h t] // [Hlent].
move/IHn : Hlent => /= Hlent.
rewrite /ule /=.
by destruct h.
Qed.

Lemma ult_tail : forall n h h' t t', size h = n -> size h' = n ->
  ult (h ++ [:: t]) (h' ++ [:: t']) -> ule h h'.
Proof.
elim.
- case=> //.
  by case.
- move=> n IHn [|h t] // [|h' t'] // tl tl' [Hlent] [Hlent'] /= H.
  destruct h => //.
  destruct h' => //.
  apply IHn in H => //.
  destruct h' => //.
  rewrite /ule //=.
  by apply IHn in H.
Qed.

Lemma ult_min : forall l n, ~ ult l (zeros n).
Proof.
elim=> // hd tl IH [|n].
destruct hd => //.
destruct hd => //=.
Qed.

Lemma ult_tail' : forall n hd hd' tl, size hd = n -> size hd' = n ->
  ult (hd ++ [:: tl]) (hd' ++ [:: false]) -> ult hd hd'.
Proof.
elim.
- case=> //; case=> //; by case.
- move=> n IHn [|h t] // [|h' t'] // tl [Hlent] [Hlent'] /= H.
  destruct h.
  destruct h' => //.
  apply IHn in H => //.
  destruct h' => //.
  by apply IHn in H.
Qed.

Definition slt (a b : list bool) : bool :=
  match a with
    | false :: ta =>
      match b with
        | false :: tb => ult ta tb
        | true :: tb => false
        | nil => false (* shouldn't happen *)
      end
    | true :: ta =>
      match b with
        | false :: tb => true
        | true :: tb => negb (ult ta tb)
        | nil => false (* shouldn't happen *)
      end
    | nil => false
  end.

End bits.

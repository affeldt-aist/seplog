(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat seq.
Require Import ssrZ ZArith_ext uniq_tac ssrnat_ext.
Require Import bipl seplog integral_type syntax.

Module syntax_m := Syntax ZIT.
Import syntax_m.seplog_m.assert_m.expr_m.
Import syntax_m.seplog_m.assert_m.
Import syntax_m.seplog_m.

Local Open Scope Z_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.

Require Import seq_ext.

Module Div2.

Definition x := O.

Lemma div2_verif vx :
  {{ fun s h => [ x ]_ s = vx}} x <- var_e x ./e cst_e 2 {{ fun s h => [ x ]_ s = vx / 2}}.
Proof.
eapply hoare_prop_m.hoare_stren; last by apply while.hoare_hoare0, hoare0_assign.
rewrite /while.entails => s h H.
rewrite /wp_assign; repeat Store_upd => //.
by rewrite /= /ZIT.div H.
Qed.

End Div2.

Local Open Scope uniq_scope.

Module GCD.

(** Euclid version *)
Definition gcd0 a b x y :=
  x <- cst_e a ;
  y <- cst_e b ;
  While var_e x \!= var_e y {{
    If var_e y \> var_e x Then
      y <- var_e y \- var_e x
    Else
      x <- var_e x \- var_e y
  }}.

Local Open Scope seplog_expr_scope.

Lemma gcd0_verif a b x y : uniq(x, y) ->
  {{ fun s h => 0 < a /\ 0 < b }}
    gcd0 a b x y
  {{ fun s h => exists d, [ x ]_ s = d /\ Zis_gcd a b d }}.
Proof.
move=> Hset.
rewrite /gcd0.
(** x <- cst_e a; *)
apply hoare_assign with (fun s _ => 0 < a /\ 0 < b /\ [ x ]_ s = a).
move=> s h /= [H1 H2].
by rewrite /wp_assign; repeat Store_upd => //.
(** x <- cst_e b; *)
apply hoare_assign with (fun s _ => 0 < a /\ 0 < b /\ [ x ]_ s = a /\ [ y ]_ s = b).
move=> s h /= [H1 [H2 H3]].
rewrite /wp_assign /=; repeat Store_upd => //.
(** while (var_e x =/= var_e y) *)
apply (hoare_prop_m.hoare_stren (fun s _ =>
  exists vx vy d, 0 < vx /\ 0 < vy /\
    [ x ]_ s = vx /\ [ y ]_ s = vy /\
    Zis_gcd vx vy d /\ Zis_gcd a b d)).
move=> s h /= [H1 [H2 [H3 H4]]].
exists a; exists b.
case: (Zgcd_spec a b) => d [Hd1 Hd2].
by exists d.
apply hoare_prop_m.hoare_weak with (fun s _ =>
  (exists vx vy d, 0 < vx /\ 0 < vy /\
    [ x ]_ s = vx /\ [ y ]_ s = vy /\
    Zis_gcd vx vy d /\ Zis_gcd a b d)
  /\ ~~ [ var_e x \!= var_e y ]b_ s).
move=> s h /= [[vx [vy [d [H1 [H2 [H4 [H5 [H6 H7]]]]]]]] /negPn/eqP H8].
rewrite H4 H5 in H8; subst vy vx.
rewrite -H8{H2 H8} in H6.
have H : 0 <= store.get x s by lia.
case: (Zis_gcd_eq _ _ H H6) => X.
- by exists d.
- exists (-d); split; first by [].
  exact/Zis_gcd_opp/Zis_gcd_sym.
apply while.hoare_while.
(** var_e y >> var_e x *)
apply while.hoare_ifte.
(** y <- var_e y .-e var_e x *)
apply hoare_assign'.
move=> s h /= [[[vx [vy [d [H1 [H2 [H4 [H5 [H6 H7]]]]]]]] H8] H9].
rewrite /wp_assign.
exists vx; exists (vy - vx); exists d.
repeat Store_upd => //.
split; first by [].
split.
- move/negbTE: H8; rewrite /= /ZIT.eqb => H8.
  move/gtZP : H9; rewrite /= => H9.
  subst vx vy; lia.
- split; first by [].
  split.
  + rewrite /=.
    open_integral_type_goal.
    by rewrite H4 H5.
  + split; last by [].
    have -> : vy-vx = vx * (-1) + vy by ring.
    exact/Zis_gcd_for_euclid2/Zis_gcd_sym.
(** x <- var_e x .-e var_e y *)
apply hoare_assign'.
move=> s h /= [[[vx [vy [d [H1 [H2 [H4 [H5 [H6 H7]]]]]]]] H8] H9].
rewrite /wp_assign.
exists (vx - vy); exists vy; exists d.
repeat Store_upd => //.
split.
- move/negbTE: H8 => /= /eqP H8.
  move/negbTE: H9 => /gtZP /= H9.
  subst vx vy; lia.
- split; first by [].
  split.
  + by rewrite /= H4 H5.
  + split; first by [].
    split; last by [].
    have -> : vx - vy = vy * (-1) + vx by ring.
    by apply Zis_gcd_sym, Zis_gcd_for_euclid2.
Qed.

(** classical algorithm *)
Definition gcd1 a b r :=
  While var_e b \!= cst_e 0 {{
    r <- var_e a \% var_e b ;
    a <- var_e b ;
    b <- var_e r }}.

Lemma gcd1_verif a b r : uniq(a, b, r) ->
  forall va vb, 0 <= va -> 0 <= vb ->
  {{ fun s h => [ a ]_ s = va /\ [ b ]_ s = vb }}
  gcd1 a b r
  {{ fun s h => exists wa, exists wb, exists d,
    [ a ]_ s = wa /\ [ b ]_ s = wb /\
    Zis_gcd wa wb d /\ Zis_gcd va vb d }}.
Proof.
move=> Hset va vb Hva Hvb.
rewrite /gcd1.
(** while (var_e b =/= cst_e 0) *)
apply (hoare_prop_m.hoare_stren (fun s _ => exists wa wb d,  0 <= wa /\ 0 <= wb /\
    [ a ]_ s = wa /\ [ b ]_ s = wb /\ Zis_gcd wa wb d /\ Zis_gcd va vb d)).
move=> s h /= [H1 H2].
exists va; exists vb.
move: (Zgcd_spec va vb) => [d [Hd1 Hd2] ].
exists d => //.
apply hoare_prop_m.hoare_weak with (fun s _ => (exists wa wb d, 0 <= wa /\ 0 <= wb /\
    [ a ]_ s = wa /\ [ b ]_ s = wb /\ Zis_gcd wa wb d /\ Zis_gcd va vb d)
  /\ ~~ [ var_e b \!= cst_e 0 ]b_ s).
move=> s h /= [ [wa [wb [ d [H2 [H3 [H4 [H6 [H7 H8]]]]]]]] H1].
exists wa, wb, d => //.
apply while.hoare_while with (P := fun s _ => exists wa wb d, 0 <= wa /\ 0 <= wb /\
    [ a ]_ s = wa /\ [ b ]_ s = wb /\ Zis_gcd wa wb d /\ Zis_gcd va vb d).
(** r <- var_e a mode var_e b; *)
apply hoare_assign with (fun s _ => exists wa wb d, 0 <= wa /\ 0 < wb /\
    [ a ]_ s = wa /\ [ b ]_ s = wb /\
    Zis_gcd wa wb d /\ Zis_gcd va vb d /\ [ r ]_ s = Zmod wa wb).
move=> s h /= [ [wa [wb [ d [H2 [H3 [H4 [H6 [H7 H8]]]]]]]] H1].
exists wa, wb, d.
repeat Store_upd => //.
split; first by [].
split.
- move/negbTE : H1 => /eqP /= H1.
  subst wa wb; lia.
- split; first by [].
  split => //.
  split; first by [].
  split; first by [].
  by rewrite /= H4 H6.
(** a <- var_e b; *)
apply hoare_assign with (fun s _ => exists wa wb d, 0 <= wa /\ 0 < wb /\
    [ a ]_ s = wb /\ [ b ]_ s = wb /\ Zis_gcd wa wb d /\ Zis_gcd va vb d /\
    [ r ]_ s = wa mod wb).
move=> s h /=  [wa [wb [ d [H2 [H3 [H4 [H6 [H7 [H8 H9]]]]]]]]] .
exists wa, wb, d.
by repeat Store_upd.
(** b <- var_e r *)
apply hoare_assign'.
move=> s h /= [wa [wb [d [H2 [H3 [H4 [H6 [H7 [H8 H9]]]]]]]]].
exists wb, (wa mod wb), d.
repeat Store_upd => //.
split; first by lia.
split.
- case: (Z_mod_lt wa wb (Z.lt_gt _ _ H3)) => X1 _ //.
- split; first by [].
  split; first by [].
  split; last by [].
  move: (Z_div_mod_eq wa wb (Z.lt_gt _ _ H3)) => H.
  have ->: wa mod wb = wb * (- (wa / wb)) + wa.
    have -> : wa mod wb = wa - wb * (wa / wb) by lia.
    ring.
  by apply (Zis_gcd_for_euclid2 (wb) d (-(wa / wb)) wa).
Qed.

End GCD.

Module Factorial.

Lemma factorial n : 0 <= n -> forall x m, uniq(x, m) ->
  {{ fun s h => [ m ]_ s = n /\ [ x ]_ s = 1 }}
  While var_e m \!= cst_e 0 {{
    x <- var_e x \* var_e m;
    m <- var_e m \- cst_e 1 }}
  {{ fun s h => [ x ]_ s = Zfact n }}.
Proof.
move=> n_pos x m Hvars.
apply (hoare_prop_m.hoare_stren (fun s _ => [ x ]_ s * Zfact ([ m ]_ s) = Zfact n /\ 0 <= [ m ]_ s)).
move=> s h /= [H1 H2].
rewrite H1 H2.
split; [ring | lia].
apply hoare_prop_m.hoare_weak with (fun s _ =>
  ([ x ]_ s * Zfact ([ m ]_ s) = Zfact n /\  0 <= [ m ]_ s) /\
  ~~ [ var_e m \!= cst_e 0 ]b_ s).
move=> s h /= [[H1 H2] H3].
move/negPn : H3 => /eqP H3.
by rewrite -H1 H3 //= mulZ1.
apply while.hoare_while.
apply hoare_assign with (fun s _ =>
  [ x ]_ s * Zfact ([ m ]_ s - 1) = Zfact n /\ 0 <= [ m ]_ s - 1).
move=> s h /= [[H1 H2] H3].
rewrite /wp_assign; repeat Store_upd => //.
move/eqP : H3 => /= H3.
split; last by lia.
rewrite -H1 (Zfact_pos ([ m ]_ s)) /=; last by lia.
open_integral_type_goal.
ring.
apply hoare_assign'.
move=> s h /= [H1 H2].
by rewrite /wp_assign; repeat Store_upd.
Qed.

Local Open Scope heap_scope.

Module StringCopy.

Section clikestrings.
(* TODO: clean *)

Definition string' (lst : list nat) := ~ O \in lst.

Definition string (lst : list Z) := exists lst',
  string' lst' /\ lst = (map (fun x => Z_of_nat x) lst') ++ (0 :: nil).

Lemma string_nil : ~ string nil.
Proof.
move=> [x [H H1]].
have H0 : (1 <= size (@nil Z))%nat by rewrite H1 size_cat /=; ssromega.
inversion H0.
Qed.

Lemma string'_sub : forall lst, string' lst -> string' (List.tail lst).
Proof.
elim=> // h t IH.
rewrite /string' in_cons /= => H.
contradict H.
by rewrite H orbT.
Qed.

Lemma string_sub : forall lst, (2 <= size lst)%nat -> string lst -> string (List.tail lst).
Proof.
induction lst; intros; auto.
simpl.
red in H0.
inversion_clear H0.
inversion_clear H1.
red.
exists (List.tail x).
split.
apply string'_sub; auto.
destruct x.
simpl in H2.
rewrite H2 in H.
inversion H.
inversion H2.
simpl.
simpl in H2.
injection H2; auto.
Qed.

Lemma string_sup : forall lst, string lst ->
  forall lst', string' lst' -> string (map (fun x => Z_of_nat x) lst' ++ lst).
Proof.
induction lst'.
simpl.
auto.
simpl.
intros.
generalize (string'_sub _ H0); intro.
simpl in H1.
generalize (IHlst' H1); intro.
red in H2.
inversion_clear H2 as [lst''].
red.
exists (a::lst'').
inversion_clear H3.
split.
  red.
  red in H0.
  red in H2.
  contradict H0.
  move: H0.
  by rewrite !inE => /orP[-> //|/H2].
by rewrite /= H4.
Qed.

Lemma string_last : forall lst, string lst -> forall i, nth (-1) lst i = 0 ->
  (i = size lst - 1)%nat.
Proof.
induction lst; intros.
  generalize string_nil; tauto.
simpl.
rewrite subSS subn0.
destruct lst.
  red in H.
  inversion_clear H.
  inversion_clear H1.
  destruct x.
    simpl in H2.
    injection H2; clear H2; intro.
    subst a.
    simpl in H0.
    destruct i; auto.
    destruct i; discriminate.
  suff : (2 <= size (a::nil))%nat by [].
  rewrite H2 size_cat /= size_map; ssromega.
inversion H.
inversion H1.
destruct i.
  simpl in H0.
  subst a.
  red in H.
  inversion_clear H.
  inversion_clear H0.
  destruct x.
    simpl in H1.
    discriminate.
  simpl in H3.
  injection H3; clear H3; intros.
  have ? : n = O by lia.
  subst n.
  by rewrite /string' inE eqxx in H2.
assert (string (z :: lst)).
  rewrite (_ : z::lst = List.tail (a::z::lst)); [idtac | auto].
  apply string_sub.
    simpl.
    ssromega.
  assumption.
lapply (IHlst H4 i).
  intros.
  rewrite H5.
  simpl.
  by rewrite subSS subn0.
rewrite //= in H0 *.
Qed.

Lemma string_hd_ge0: forall a l, string (a::l) -> a >= 0.
Proof.
intros.
inversion_clear H.
inversion_clear H0.
destruct x.
injection H1.
intros.
lia.
simpl in H1.
injection H1.
intros.
lia.
Qed.

Lemma string_last' : forall i lst, string lst -> (i = size lst - 1)%nat ->
  nth (-1) lst i = 0.
Proof.
move=> i lst [lst' [H H2]] Hi.
subst lst.
rewrite size_cat /= in Hi.
by rewrite nth_cat size_map {1}Hi size_map addn1 subn1 ltnn Hi size_map addn1 subn1 /= subnn.
Qed.

Lemma string_last'' : forall i lst, string lst -> (i < size lst)%nat ->
  nth (-1) lst i >= 0.
Proof.
induction i; intros.
  red in H.
  inversion_clear H as [lst'].
inversion_clear H1.
destruct lst'.
simpl in H2.
rewrite H2.
simpl.
lia.
rewrite H2.
simpl.
red in H.
simpl in H.
lia.
inversion_clear H as [lst'].
inversion_clear H1.
destruct lst.
destruct lst'; discriminate.
simpl.
apply IHi.
destruct lst'; try discriminate.
simpl in H2.
destruct lst; try discriminate.
simpl in H0.
inversion H0.
inversion H3.
simpl in H2.
injection H2; clear H2; intros.
subst z.
rewrite H1.
red.
exists lst'.
split; auto.
generalize (string'_sub _ H); intro.
auto.
simpl in H0.
ssromega.
Qed.

End clikestrings.

(** for (c1=buf, c2=s; ( *c1++ = *c2++ )!=0) *)
Definition StringCopy c1 c2 buf str str_tmp :=
  c1 <- var_e buf;
  c2 <- var_e str;
  str_tmp <-* var_e c2;
  While var_e str_tmp \!= cst_e 0 {{
    var_e c1 *<- var_e str_tmp ;
    c1 <- var_e c1 \+ cst_e 1 ;
    c2 <- var_e c2 \+ cst_e 1 ;
    str_tmp <-* var_e c2 }} ;
  var_e c1 *<- var_e str_tmp.

Lemma StringCopy_specif c1 c2 buf str str_tmp : uniq(c1, c2, buf, str, str_tmp) ->
  forall buf_lst str_lst,
  (0 < size buf_lst)%nat ->
  (size str_lst <= size buf_lst)%nat ->
  string str_lst ->
  {{ var_e buf |---> buf_lst ** var_e str |---> str_lst }}
  StringCopy c1 c2 buf str str_tmp
  {{ (var_e buf |---> str_lst) ** TT ** (var_e str |---> str_lst) }}.
Proof.
move=> Hset buf_lst str_lst Hbuf Hbuf2 Hstr.
rewrite /StringCopy.
(**  c1 <- var_e buf; *)
apply hoare_assign with (fun s h =>
  (var_e buf |---> buf_lst ** (var_e str |---> str_lst)) s h /\
  [ c1 ]_ s = [ buf ]_ s).
move=> s h H; rewrite /wp_assign; split.
- apply inde_upd_store => //.
  apply inde_sep_con.
  + apply inde_mapstos'.
    apply disj_cons_L.
    by apply disj_nil_L.
    by Uniq_not_In.
  + apply inde_mapstos'.
    apply disj_cons_R.
    by apply disj_nil_R.
    rewrite [vars _]/=; by Uniq_not_In.
- by repeat Store_upd.
(**  c2 <- var_e str; *)
apply hoare_assign with (fun s h =>
  (var_e buf |---> buf_lst ** (var_e str |---> str_lst)) s h /\
  [ c1 ]_ s = [ buf ]_ s /\ [ c2 ]_ s = [ str ]_ s).
move=> s h [H1 H2]; rewrite /wp_assign; split.
- apply inde_upd_store => //.
  + apply inde_sep_con.
    apply inde_mapstos'.
    apply disj_cons_R.
    by apply disj_nil_R.
    by rewrite [vars _]/=; Uniq_not_In.
  + apply inde_mapstos'.
    apply disj_cons_R.
    by apply disj_nil_R.
    by rewrite [vars _]/=; Uniq_not_In.
- by repeat Store_upd.
destruct str_lst as [|str0 str_lst]; first by move: string_nil.
(**  str_tmp <-* var_e c2; *)
apply hoare_lookup_back_strictly_exact with (fun s h =>
  (var_e buf |---> buf_lst ** (var_e str |---> str0 :: str_lst)) s h /\
  [ c1 ]_ s = [ buf ]_ s /\ [ c2 ]_ s = [ str ]_ s /\ [ str_tmp ]_ s = str0).
move=> s h [H1 [H2 H3]]; exists (cst_e str0); split.
- case_sepcon H1.
  rewrite /mapstos' /= in H1_h2.
  case_sepcon H1_h2.
  exists h21; exists (h1 \U h22); split; first by map_tac_m.Disj.
  split; first by map_tac_m.Equal.
  split; [by Mapsto | by []].
- rewrite /wp_assign; repeat Store_upd => //.
  split; last by [].
  apply inde_upd_store => //.
  apply inde_sep_con.
  - apply inde_mapstos' => /=.
    apply disj_cons_R.
    exact/disj_nil_R.
    by Uniq_not_In.
  - apply inde_mapstos' => /=.
    apply disj_cons_R.
    exact/disj_nil_R.
    by Uniq_not_In.
(**  while (var_e str_tmp =/= cst_e 0) *)
apply (hoare_prop_m.hoare_stren (fun s h => exists i,
  (var_e buf |---> take i (str0 :: str_lst) ++ drop i buf_lst ** (var_e str |---> str0 :: str_lst)) s h /\
  [ c1 ]_ s = [ buf ]_ s + Z_of_nat i /\ [ c2 ]_ s = [ str ]_ s + Z_of_nat i /\
  [ str_tmp ]_ s = nth (-1)%Z (str0 :: str_lst) i /\
  (i <= size (str0 :: str_lst))%nat /\ 0 <= [ str_tmp ]_ s)).
move=> s h [H1 [H2 [H3 Hstr_tmp_is_0]]]; exists O; rewrite drop0; split => //=.
do 2 rewrite addZ0.
repeat (split => //).
apply string_hd_ge0 in Hstr.
apply Z.ge_le; by rewrite Hstr_tmp_is_0.
apply while.hoare_seq with (fun s h => (exists i,
  (var_e buf |---> (take i (str0 :: str_lst)) ++ (drop i buf_lst) ** (var_e str |---> str0 :: str_lst)) s h /\
  [ c1 ]_ s = [ buf ]_ s + Z_of_nat i /\ [ c2 ]_ s = [ str ]_ s + Z_of_nat i /\
  [ str_tmp ]_ s = nth (-1) (str0 :: str_lst) i /\
  (i <= size (str0 :: str_lst))%nat /\ 0 <= [ str_tmp ]_ s) /\
~~ [ var_e str_tmp \!= cst_e 0 ]b_ s).
apply while.hoare_while.
(**    var_e c1 *<- var_e str_tmp; *)
apply hoare_mutation_backwards'' with (fun s h => exists i,
  (var_e buf |---> take (S i) (str0 :: str_lst) ++ (drop (S i) buf_lst) ** (var_e str |---> str0 :: str_lst)) s h /\
  [ c1 ]_ s = [ buf ]_ s + Z_of_nat i /\ [ c2 ]_ s = [ str ]_ s + Z_of_nat i /\
  [ str_tmp ]_ s = nth (-1) (str0 :: str_lst) i /\ 0 < [ str_tmp ]_ s /\
  (S i < size (str0 :: str_lst))%nat).
move=> s h [[x [H2 [H3 [H4 [H5 [H6 H7]]]]]] H1].
(* is (drop buf_lst i) the empty heap ? *)
(* It depend if the size of buf_lst is larger than i  *)
have [H0 | H0] : (size buf_lst <= x \/ x < size buf_lst)%coq_nat by lia.

- (* if the size of the buffer is lesser or equal, that means that we are trying to write outside buf_lst ... *)
  rewrite drop_oversize in H2; last by ssromega.
  (* ... mutation cannot be performed !!!! but we can build a contradiction with H5, Hbuf2, H4 and H6 *)
  have H : size buf_lst = size (str0 :: str_lst) by ssromega.
  rewrite H in H0.
  have H8 : x = size (str0 :: str_lst) by ssromega.
  have H9 : store.get str_tmp s = -1 by rewrite H8 // nth_default in H5.
  by rewrite H9 in H7. (* So this case is impossible *)
- have H : 0 < [ str_tmp ]_ s.
    rewrite /hoare_m.eval_b in H1.
    eval_b2Prop_hyp H1.
    rewrite ltZ_neqAle; by auto.
  have [H9|[H9|H8]] : (S x = size (str0 :: str_lst) \/ x = size (str0 :: str_lst) \/ S x < size (str0 :: str_lst))%coq_nat by ssromega.
    + rewrite string_last' // in H5; last by rewrite -H9 subn1.
      rewrite H5 in H; by inversion H.
    + subst x.
      rewrite nth_default // in H5.
      rewrite H5 in H.
      exfalso.
      lia.
    + move/ltP in H0.
      rewrite (drop_nth (-1)) // in H2.
      case_sepcon H2.
      move/mapstos'_app_sepcon : H2_h1 => H2_h1.
      case_sepcon H2_h1.
      move/mapstos'_cons_sepcon : H2_h1_h12 => H2_h1_h12.
      case_sepcon H2_h1_h12.
      exists (cst_e (nth (-1) buf_lst x)).
      Compose_sepcon h121 (h2 \U h11 \U h122).
      rewrite [take]lock in H2_h1_h12_h122.
      rewrite [take]lock in H2_h1_h12_h121.
      move/ltP in H8.
      rewrite ltnS in H8.
      Mapsto.
      rewrite -lock H3 // size_take /=.
      by rewrite ltnW.
      rewrite /imp => h121' [X1 X2] h' Hh'.
      exists x.
      repeat (split => //).
      * Compose_sepcon (h11 \U h121' \U h122) h2 => //.
        apply mapstos'_sepcon_app.
        Compose_sepcon (h11 \U h121') h122.
        rewrite (take_nth (-1)); last by ssromega.
        rewrite -cats1.
        eapply mapstos'_sepcon_app.
        Compose_sepcon h11 h121' => //.
        rewrite /mapstos' [take]lock /=.
        apply assert_m.con_emp'.
        Mapsto.
        rewrite -lock H3 // size_take /=.
        move/ltP : H8.
        rewrite /= ltnS => H8.
        by rewrite ltnW.
        rewrite /mapstos' in H2_h1_h12_h122 *.
        move: H2_h1_h12_h122; apply mapstos_ext => //.
        rewrite [take]lock /= -lock -ZIT.addA; f_equal.
        rewrite ZIT.addC {1}(_ : 1 = ZIT.of_nat 1) // ZIT.add1.
        rewrite size_take [size _]/=.
        move/ltP : H8.
        rewrite ltnS => H8.
        by rewrite ltnW // size_take H8.
      * exact/ltP.

(**    c1 <- var_e c1 \+ cst_e 1; *)
apply hoare_assign with (fun s h => exists i,
  (var_e buf |---> take (S i) (str0 :: str_lst) ++ drop (S i) buf_lst ** (var_e str |---> str0 :: str_lst)) s h /\
  [ c1 ]_ s = [ buf ]_ s + (Z_of_nat i) + 1 /\ [ c2 ]_ s = [ str ]_ s + (Z_of_nat i) /\
  [ str_tmp ]_ s = nth (-1) (str0::str_lst) i /\ 0 < [ str_tmp ]_ s /\
  (S i < size (str0 :: str_lst))%nat).
move=> s h [x [H1 [H2 [H3 [H4 [H5 H6]]]]]]; rewrite /wp_assign.
repeat Store_upd => //.
exists x; split.
apply inde_upd_store => //.
  apply inde_sep_con.
  - apply inde_mapstos'.
    apply disj_cons_R.
    by apply disj_nil_R.
    by rewrite [vars _]/=; Uniq_not_In.
  - apply inde_mapstos' => /=.
    apply disj_cons_R.
    by apply disj_nil_R.
    by Uniq_not_In.
split; last by [].
by rewrite /= H2.
(**    c2 <- var_e c2 \+ cst_e 1; *)
apply hoare_assign with (fun s h => exists i,
  (var_e buf |---> take (S i) (str0 :: str_lst) ++ drop (S i) buf_lst  ** (var_e str |---> str0 :: str_lst)) s h /\
  [ c1 ]_ s = [ buf ]_ s + (Z_of_nat i) + 1 /\ [ c2 ]_ s = [ str ]_ s + (Z_of_nat i) + 1 /\
  [ str_tmp ]_ s = nth (-1) (str0 :: str_lst) i /\ 0 < [ str_tmp ]_ s /\
  (S i < size (str0 :: str_lst))%nat).
move=> s h [x [H1 [H2 [H3 [H4 [H5 H6]]]]]]; rewrite /wp_assign.
repeat Store_upd => //.
exists x; split.
apply inde_upd_store => //.
  apply inde_sep_con.
  - apply inde_mapstos'.
    apply disj_cons_R.
    by apply disj_nil_R.
    by rewrite [vars _]/=; Uniq_not_In.
  - apply inde_mapstos' => /=.
    apply disj_cons_R.
    by apply disj_nil_R.
    by Uniq_not_In.
split; first by [].
split=> /=; last by [].
by rewrite H3.
(**    str_tmp <-* var_e c2); *)
apply hoare_lookup_back'.
move=> s h [x [Hmem [Hc1 [Hc2 [Hstr_tmp [_ Hlenstr_lst]]]]]].
exists (cst_e (nth (-1) (str0 :: str_lst) (S x))).
apply mapsto_strictly_exact.
split.
case: Hmem => h1 [h2 [Hdisj [Hunion [Hmem1 Hmem2]]]].
rewrite -(@cat_take_drop (S x) _ (str0 :: str_lst)) in Hmem2.
apply mapstos'_app_sepcon in Hmem2. case: Hmem2 => h21 [h22 [Hdisj'' [Hunion'' [Hmem21 Hmem22]]]]. rewrite (drop_nth (-1)) // in Hmem22.
case: {Hmem22}(mapstos'_cons_sepcon _ _ _ _ _ Hmem22) => h221 [h222 [Hdisj' [Hunion' [Hmem221 Hmem222]]]].
Compose_sepcon h221 (h222 \U h21 \U h1) => //.
rewrite (_ : S x = x + 1)%nat in Hmem221; last by rewrite addnC. (*NB: bad design*)
rewrite [take]lock in Hmem221.
Mapsto.
rewrite -lock.
- rewrite Hc2 size_takel; last by rewrite addn1 ltnW.
  by rewrite {1}/ZIT.add (_ : 1 = (ZIT.of_nat 1)) // /ZIT.of_nat Nat2Z.inj_add addZA.
- by rewrite addnC.
(* *)
rewrite /wp_assign.
repeat Store_upd => //.
exists (S x).
split.
apply inde_upd_store => //.
  apply inde_sep_con.
  apply inde_mapstos'.
  apply disj_cons_R.
  by apply disj_nil_R.
  by rewrite [vars _]/=; Uniq_not_In.
  apply inde_mapstos'.
  apply disj_cons_R.
  by apply disj_nil_R.
  by rewrite [vars _]/=; Uniq_not_In.
split.
by rewrite Hc1 Z_S addZA.
split => //.
by rewrite Hc2 Z_S addZA.
split; first by [].
split.
by ssromega.
rewrite [nth]lock /= -lock.
exact/Z.ge_le/string_last''.
(**  var_e c1 *<- var_e str_tmp. *)
apply hoare_mutation_backwards'.
move=> s h [[x [Hmem [Hc1 [Hc2 [Hstr_tmp [Hx _]]]]]] Hstr_tmp_is_0].
have {}Hstr_tmp_is_0 : [ str_tmp ]_ s = 0.
  eval_b2Prop_hyps.
  tauto.
have H : (x = size (str0 :: str_lst) - 1)%nat.
  apply string_last => //.
  by rewrite -Hstr_tmp.
case: Hmem => h1 [h2 [Hdisj [Hunion [Hmem1 Hmem2]]]].
rewrite (drop_nth (-1)) // in Hmem1; last by rewrite H subn1 prednK.
case: {Hmem1}(mapstos'_app_sepcon _ _ _ _ _ Hmem1) => h11 [h12 [Hdisj' [Hunion' [Hmem11 Hmem12]]]].
case: {Hmem12}(mapstos'_cons_sepcon _ _ _ _ _ Hmem12) => h121 [h122 [Hdisj'' [Hunion'' [Hmem121 Hmem122]]]].
exists (cst_e (nth (-1) buf_lst x)).
Compose_sepcon h121 (h122 \U h11 \U h2) => //.
rewrite [take]lock in Hmem121.
rewrite [take]lock in Hmem122.
Mapsto.
by rewrite -lock size_takel.
rewrite /imp => h121' [X1 X2] h' Hh'.
rewrite -conAE.
Compose_sepcon (h122 \U h11 \U h121') h2 => //.
Compose_sepcon (h11 \U h121') h122 => //.
rewrite -(cat_take_drop x (str0 :: str_lst)).
apply mapstos'_sepcon_app.
Compose_sepcon h11 h121' => //.
rewrite /mapstos' (drop_nth (-1)); last first.
  by rewrite H /= subSS subn0.
rewrite drop_oversize; last by rewrite H /= subSS subn0.
apply assert_m.con_emp'.
rewrite [take]lock.
Mapsto.
rewrite -lock Hc1 size_take {2}H subSS subn0 leqnn.
by omegab.
Qed.

End StringCopy.

Local Open Scope vc_scope.

Lemma vc_factorial n : n >= 0 ->
  forall x m, uniq (x :: m :: nil) ->
    {{ fun s _ => [ m ]_ s = n /\ [ x ]_ s = 1 }} proj_cmd
    (while' ( var_e m \!= cst_e 0 )
      (fun s _ => [ x ]_ s * (Zfact [ m ]_ s) = Zfact n /\ [ m ]_ s >= 0)
      ( x <- var_e x \* var_e m;
        m <- var_e m \- cst_e 1))
    {{ fun s _ => [ x ]_ s = Zfact n }}.
Proof.
move=> Hpos x m Hvars.
apply wp_vc_util.
move=> s h /=.
(** vc *)
rewrite /wp_assign /=.
repeat Store_upd => //.
split.
move=> [[<- H2]].
move/negPn/eqP => -> /=; by rewrite mulZ1.
split => //.
move=> [[H1 H2] H3].
move/negbTE : H3 => /eqP H3.
split.
  rewrite -H1 (Zfact_pos (store.get m s)); last lia.
  open_integral_type_goal.
  ring.
open_integral_type_goal; lia.
move=> s h /= [-> ->].
split => //; ring.
Qed.

End Factorial.

Module Swap.

Lemma swap x y z v a b : uniq (x :: y :: z :: v :: nil) ->
  {{ var_e x |~> cst_e a ** var_e y |~> cst_e b }}
  z <-* var_e x;
  v <-* var_e y;
  var_e x *<- var_e v;
  var_e y *<- var_e z
  {{ var_e x |~> cst_e b ** var_e y |~> cst_e a }}.
Proof.
move=> Hvars.
apply hoare_lookup_back'' with (fun s h =>
  (var_e x |~> cst_e a ** var_e y |~> cst_e b) s h /\ [ var_e z ]e_s = a).
move=> s h H.
case_sepcon H.
exists (cst_e a).
Compose_sepcon h1 h2 => //.
rewrite /imp => h1' [X1 X2] h' Hh'.
rewrite /wp_assign.
split.
Compose_sepcon h1' h2; by Mapsto.
rewrite /=; repeat Store_upd => //.
apply hoare_lookup_back'' with (fun s h =>
  (var_e x |~> cst_e a ** var_e y |~> cst_e b) s h /\ [ var_e z ]e_ s = a /\ [ var_e v ]e_ s = b).
move=> s h [H1 H2].
case_sepcon H1.
exists (cst_e b).
Compose_sepcon h2 h1 => //.
rewrite /imp => h2' [X1 X2] h' Hh'.
rewrite /wp_assign.
split.
Compose_sepcon h1 h2'; by Mapsto.
rewrite /=.
by split; repeat Store_upd.
apply hoare_mutation_backwards'' with (fun s h =>
  (var_e x |~> cst_e b ** var_e y |~> cst_e b) s h /\ [ var_e z ]e_s = a /\ [ var_e v ]e_s = b).
move=> s h [H1 [H2 H3]].
case_sepcon H1.
exists (cst_e a).
Compose_sepcon h1 h2 => //.
rewrite /imp => h1' [X1 X2] h' Hh'.
split.
Compose_sepcon h1' h2; by Mapsto.
by [].
apply hoare_mutation_backwards'.
move=> s h /= [H1 [H2 H3] ].
case_sepcon H1.
exists (cst_e b).
Compose_sepcon h2 h1 => //.
rewrite /imp => h2' [X1 X2] h' Hh'.
Compose_sepcon h1 h2'; by Mapsto.
Qed.

Local Open Scope vc_scope.

Lemma vc_swap x y z v a b : uniq (x :: y :: z :: v :: nil) ->
  {{ var_e x |~> cst_e a ** var_e y |~> cst_e b }}
  proj_cmd
  (z <-*var_e x;
   v <-* var_e y;
   var_e x *<- var_e v;
   var_e y *<- var_e z)
  {{ var_e x |~> cst_e b ** var_e y |~> cst_e a }}.
Proof.
move=> Hvars.
apply wp_vc_util.
(** vc *)
move=> s h //=.
(** wp *)
rewrite /=.
exists (cst_e a).
move: H; apply assert_m.monotony => // h''; apply assert_m.currying => h0 H0.
exists (cst_e b) => /=.
have : (var_e y |~> cst_e b ** var_e x |~> cst_e a)
  (store.upd z ([ cst_e a ]e_ s) s) h0.
  apply inde_upd_store.
  apply inde_sep_con.
  apply inde_mapsto => /=.
  apply disj_singl; by Uniq_neq.
  by apply disj_nil_L.
  apply inde_mapsto => /=.
  apply disj_singl; by Uniq_neq.
  by apply disj_nil_L.
  assumption.
apply assert_m.monotony => // h''0; apply assert_m.currying => h1 H1.
exists (cst_e a).
have : (var_e x |~> cst_e a ** var_e y |~> cst_e b) (store.upd v b (store.upd z a s)) h1.
  apply inde_upd_store.
  apply inde_sep_con.
  apply inde_mapsto => /=.
  apply disj_singl; by Uniq_neq.
  by apply disj_nil_L.
  apply inde_mapsto => /=.
  apply disj_singl; by Uniq_neq.
  by apply disj_nil_L.
  assumption.
apply assert_m.monotony => // h''1; apply assert_m.currying => h2 H2.
exists (cst_e b).
move: H2; apply assert_m.monotony => // h''2; apply assert_m.currying => h3 H3.
case_sepcon H3.
Compose_sepcon h31 h32; by Mapsto.
Qed.

End Swap.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import div path tuple.
Require Import Init_ext ssrZ ZArith_ext String_ext Max_ext.
Require Import machine_int seq_ext ssrnat_ext tuple_ext path_ext.
Require order finmap.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr.

Local Open Scope C_types_scope.
Local Open Scope C_value_scope.
Local Open Scope C_expr_scope.

(** Equivalence between arithmetic expressions *)

Definition sequiv {g} {sigma : g.-env} {t} (e1 e2 : exp sigma t) :=
  forall s, [ e1 ]_ s = [ e2 ]_ s.

Notation "a '=s' b" := (sequiv a b) (at level 72, format "'[' a  '=s'  b ']'", no associativity) : C_expr_scope.

Instance sequiv_equivalence (g : wfctxt) (sigma : g.-env) (t : g.-typ) :
  Coq.Classes.RelationClasses.Equivalence (@sequiv _ sigma t).
constructor.
move=> e s; reflexivity.
move=> e1 e2 H s; by symmetry.
move=> e1 e2 e3 H12 H23 s; by transitivity ([e2]_ s).
Qed.

Transparent eval.

Instance bop_r_morphism g (sigma : g.-env) (t : integral) bop :
  Coq.Classes.Morphisms.Proper (sequiv ==> sequiv ==> sequiv) (bop_r sigma t bop).
Proof. destruct bop; move=> e1 e2 H1 a b H2 s /=; by rewrite H1 H2. Qed.

Instance bop_n_morphism g (sigma : g.-env) (t : integral) bop :
  Morphisms.Proper (sequiv ==> sequiv ==> sequiv) (bop_n sigma t bop).
Proof. destruct bop; move=> e1 e2 H1 a b H2 s /=; by rewrite H1 H2. Qed.

Instance eq_p_morphism g (sigma : g.-env) (t : g.-typ) :
  Morphisms.Proper (sequiv ==> sequiv ==> sequiv) (eq_p sigma t).
Proof. move => e1 e2 H1 a b H2 s /=; by rewrite H1 H2. Qed.

Instance add_p_morphism g (sigma : g.-env) (t : g.-typ) :
  Morphisms.Proper (eq ==> sequiv ==> sequiv) (add_p sigma t).
Proof. move=> e1 e2 -> a b H s /=; by rewrite H. Qed.

Instance safe_cast_morphism g (sigma : g.-env) (t t' : integral) :
  Morphisms.Proper (sequiv ==> eq ==> sequiv) (safe_cast sigma t t').
Proof. move=> x y Hxy H1 H2 -> s /=; by rewrite Hxy. Qed.

Opaque eval.

Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.

Lemma phy_of_si32_zext {g} {sigma : g.-env} (a : int 8) :
  [ zext 24 a ]pc =s ([ Z<=u a ]sc : exp sigma (ityp: sint)).
Proof.
Transparent eval.
move=> s /=.
apply mkPhy_irrelevance => /=.
congr (i8<=i32) => /=.
apply s2Z_inj.
rewrite (s2Z_zext 24) // Z2sK //.
split; [exact: (leZ_trans _ (min_u2Z _)) | exact: (ltZ_trans (max_u2Z _))].
Opaque eval.
Qed.

Section beq_sect.

Variable (g : wfctxt) (sigma : g.-env).

Lemma beq_exx t (e : exp sigma (ityp: t)) : e \= e =s [ 1 ]uc.
Proof.
Transparent eval.
move=> s /=.
case: t e => //= e; by destruct ([ e ]_s) => //=; rewrite eqxx.
Opaque eval.
Qed.

Lemma beq_pxx t (a : exp sigma (:* t)) : a \= a =s [ 1 ]uc.
Proof.
Transparent eval.
move=> s.
by rewrite /= eqxx.
Opaque eval.
Qed.

Lemma Ceq_sym t (a b : exp sigma (ityp: t)) : a \= b =s b \= a.
Proof.
Transparent eval.
move=> s /=.
move Ha : ( [ a ]_s ) => [ha1 ha2].
move Hb : ( [ b ]_s ) => [hb1 hb2].
destruct t; by rewrite eq_sym.
Opaque eval.
Qed.

Lemma Ceqp_sym t (a b : exp sigma (:* t)) : a \= b =s b \= a.
Proof.
Transparent eval.
move=> s; by rewrite /= eq_sym.
Opaque eval.
Qed.

Lemma sequiv_bop_re_sc x y :
  -2 ^^ 31 < x < 2 ^^ 31 -> -2 ^^ 31 < y < 2 ^^ 31 ->
  ([ x ]sc \= ([ y ]sc : exp sigma (ityp: sint))) =s [ Z<=nat (x == y) ]uc.
Proof.
Transparent eval.
move=> Hx Hy s /=.
rewrite 2!i8_of_i32K.
congr ([ _ ]p).
rewrite Z2sK; last by simpl in *; omega.
rewrite Z2sK; last by simpl in *; omega.
by case: ifP.
Opaque eval.
Qed.

End beq_sect.

Section Cadd_sect.

Variables (g : wfctxt) (sigma : g.-env).

Lemma CaddnC t (e1 e2 : exp sigma (ityp: t)) : e1 \+ e2 =s e2 \+ e1.
Proof.
Transparent eval.
move => s /=.
by case: t e1 e2 => e1 e2; destruct ([e1]_s); destruct ([e2]_s); rewrite /= addC.
Opaque eval.
Qed.

Lemma CaddnA t (e1 e2 e3 : exp sigma (ityp: t)) : e1 \+ e2 \+ e3 =s e1 \+ (e2 \+ e3).
Proof.
Transparent eval.
move => s /=.
case: t e1 e2 e3 => e1 e2 e3; destruct ([e1]_s); destruct ([e2]_s); destruct ([e3]_s).
- by rewrite /= !i8_of_i32K addA.
- by rewrite /= !i8_of_i32K addA.
- rewrite /=.
  destruct phy2seq as [|A []] => //.
  destruct phy2seq0 as [|B []] => //.
  destruct phy2seq1 as [|C []] => //.
  by rewrite /= /i8_to_i8 addA.
- rewrite /=.
  destruct phy2seq as [|A []] => //.
  destruct phy2seq0 as [|B []] => //.
  destruct phy2seq1 as [|C []] => //.
  by rewrite /= /i8_to_i8 addA.
- by rewrite /= !i8_of_i64K addA.
Opaque eval.
Qed.

Lemma sequiv_add_pe_0 t (e : exp sigma (:* t)) : e \+ [ 0 ]sc =s e.
Proof. move=> s; by rewrite add_p_0. Qed.

Lemma eq_pC_const t (a : exp sigma (:* t)) b c : a \+ b \+ c =s a \+ c \+ b.
Proof.
Transparent eval.
move=> s /=.
move Ha : ( [ a ]_ s ) => [a_s Ha_s].
have : size a_s = sizeof_ptr by rewrite Ha_s sizeof_ptyp.
case/optr_of_i8_Some => a_s' Ha_s'.
move Hb : ( [ b ]_ s ) => [b_s Hb_s].
have : size b_s = 4%nat by rewrite Hb_s.
case/oi32_of_i8_Some => b_s' Hb_s' /=.
rewrite !i8_of_ptrK.
move Hc : ( [ c ]_ s ) => [c_s Hc_s].
have : size c_s = 4%nat by rewrite Hc_s.
case/oi32_of_i8_Some => c_s' Hc_s' /=.
rewrite !i8_of_ptrK.
apply mkPhy_irrelevance.
by rewrite add_prodC.
Opaque eval.
Qed.

Lemma Ceqpn_add2r t (a a' : exp sigma (:* t)) (k : Z) :
  - 2 ^^ 31 <= Z<=nat (sizeof t) * k < 2 ^^ 31 ->
  a \+ [ k ]sc \= a' \+ [ k ]sc =s a \= a'.
Proof.
Transparent eval.
move=> Hk s /=.
move Ha : ([ a ]_s) => [la Hla].
move Ha' : ([ a' ]_s) => [la' Hla'].
have : size la = sizeof_ptr by rewrite Hla sizeof_ptyp.
case/optr_of_i8_Some => la'' Hla''.
have : size la' = sizeof_ptr by rewrite Hla' sizeof_ptyp.
case/optr_of_i8_Some => la''' Hla'''.
rewrite i8_of_i32K /add_prod Z2sK; last first.
  move: (sizeof_gt0 g t) => ty_gt0.
  case: (Z_lt_le_dec k 0) => hk.
    split; last by omega.
    apply (leZ_trans (proj1 Hk)).
    rewrite mulZC. apply Zle_scale_neg.
    exact: ltZW.
    rewrite (_ : 0%Z = Z.of_nat 0) //.
    apply inj_lt; exact/ltP.
  split; first by omega.
  apply : (leZ_ltZ_trans _ (proj2 Hk)).
  rewrite -{1}[X in (X <= _)%Z]mul1Z.
  apply leZ_wpmul2r => //.
  omegaz' ssromega.
(*  rewrite (_ : 1%Z = Z.of_nat 1) //; apply inj_le.
  by apply/leP.*)
case/boolP : (0 <=? k)%Z => k0.
- case: ifP.
    move/eqP/phy_of_ptr_inj.
    move/add_reg => la''la'''.
    move/ptr_of_i8_inj in la''la'''; subst la'.
    rewrite (_ : Hla = Hla'); last by apply eq_irrelevance.
    by rewrite eqxx.
  case: ifP => //.
  case/eqP => ?; subst la'.
  move=> abs.
  rewrite Hla'' in Hla'''.
  case: Hla''' => ?; subst la''.
  rewrite (_ : Hla = Hla') in abs; last by apply eq_irrelevance.
  by rewrite eqxx in abs.
- case: ifP.
    move/eqP/phy_of_ptr_inj.
    move/add_reg.
    move/ptr_of_i8_inj => ?; subst la'.
    rewrite (_ : Hla = Hla'); last by apply eq_irrelevance.
    by rewrite eqxx.
  case: ifP => //.
  case/eqP => ?; subst la'.
  move=> abs.
  rewrite Hla'' in Hla'''.
  case: Hla''' => ?; subst la''.
  rewrite (_ : Hla = Hla') in abs; last by apply eq_irrelevance.
  by rewrite eqxx in abs.
Opaque eval.
Qed.

Lemma CaddnpA t (a : exp sigma (:* t)) b c :
  0 <= Z<=nat (sizeof t) * b < 2 ^^ 31 -> 0 <= Z<=nat (sizeof t) * c < 2 ^^ 31 ->
  0 <= Z<=nat (sizeof t) * b + Z<=nat (sizeof t) * c < 2 ^^ 31 ->
  a \+ [ b ]sc \+ [ c ]sc =s a \+ ([ b ]sc \+ [ c ]sc).
Proof.
move=> Hb Hc Hbc s.
have Hb_weak : - 2 ^^ 31 <= b < 2 ^^ 31.
  case: Hb.
  case/Zle_0_mult_inv; last first.
    case => /Z_of_nat_neg abs.
    move: (sizeof_gt0 g t); by rewrite abs.
  case=> _ Hb1 Hb2.
  apply Zlt_Zmult_inv in Hb2; last 2 first.
    apply Z_of_nat_lt0. by apply sizeof_gt0.
    exact: expZ_ge0.
  split; [exact: (@leZ_trans Z0) | by []].
have Hc_weak : - 2 ^^ 31 <= c < 2 ^^ 31.
  case: Hc.
  case/Zle_0_mult_inv; last first.
    case => /Z_of_nat_neg abs.
    move: (sizeof_gt0 g t); by rewrite abs.
  case=> _ Hc1 Hc2.
  apply Zlt_Zmult_inv in Hc2; last 2 first.
    apply Z_of_nat_lt0. by apply sizeof_gt0.
    exact: expZ_ge0.
  split; [exact: (@leZ_trans Z0) | by []].
apply eval_add_pA => //.
rewrite /si32_of_phy [oi32_of_i8 _]/= i8_of_i32Ko [s2Z _]/= Z2sK //.
rewrite /si32_of_phy [oi32_of_i8 _]/= i8_of_i32Ko [s2Z _]/= Z2sK //.
rewrite /si32_of_phy [oi32_of_i8 _]/= 2!i8_of_i32Ko [s2Z _]/=.
by rewrite Z2sK // [s2Z _]/= Z2sK.
Qed.

Lemma sequiv_add_e_sc x y :
  - 2 ^^ 31 <= x < 2 ^^ 31 -> - 2 ^^ 31 <= y < 2 ^^ 31 ->
  - 2 ^^ 31 <= x + y < 2 ^^ 31 ->
  ([ x ]sc \+ [ y ]sc : exp sigma (ityp: sint) ) =s [ x + y ]sc .
Proof.
Transparent eval.
move=> Hx Hy xy s /=.
rewrite 2!i8_of_i32K.
suff -> : `( x )s_ 32 `+ `( y )s_ 32 = `(x + y)s_ 32 by done.
apply s2Z_inj.
rewrite Z2sK; last by done.
rewrite s2Z_add; last first.
  rewrite Z2sK; last by done.
  rewrite Z2sK; last by simpl in *; omega.
  simpl in *; omega.
rewrite Z2sK; last by simpl in *; omega.
rewrite Z2sK //; by simpl in *; omega.
Opaque eval.
Qed.

Lemma sequiv_add_e_sc_pos x y : 0 <= x -> 0 <= y -> x + y < 2 ^^ 31 ->
  ([ x ]sc \+ [ y ]sc : exp sigma (ityp: sint) ) =s [ x + y ]sc.
Proof. move=> Hx Hy xy; rewrite sequiv_add_e_sc //; omega. Qed.

Lemma sequiv_add_e_sc_pos3 x y z :
  0 <= x -> 0 <= y -> 0 <= z -> x + y + z < 2 ^^ 31 ->
  ([ x ]sc \+ [ y ]sc \+ [ z ]sc : exp sigma (ityp: sint)) =s [ x + y + z ]sc.
Proof.
move=> Hx Hy Hz xyz.
rewrite (sequiv_add_e_sc x y) //; [ | omega | omega | omega].
rewrite sequiv_add_e_sc_pos //; omega.
Qed.

Lemma sequiv_add_e_sc_pos4 x y z u :
  0 <= x -> 0 <= y -> 0 <= z -> 0 <= u -> x + y + z + u < 2 ^^ 31 ->
  ([ x ]sc \+ [ y ]sc \+ [ z ]sc \+ [ u ]sc : exp sigma (ityp: sint)) =s [ x + y + z + u ]sc.
Proof.
move=> Hx Hy Hz Hu xyzu.
rewrite sequiv_add_e_sc_pos3 //; last by omega.
rewrite sequiv_add_e_sc_pos //; omega.
Qed.

(* might need a bit more hypotheses *)
Lemma sequiv_add_p_cst x : forall (a : (:* (g.-ityp: uchar)).-phy),
  0 <= x < 2 ^^ 31 -> [ phy<=ptr _ (ptr<=phy a `+ `( x )_ ptr_len) ]c =s
  ([a ]c \+ [ x ]sc : exp sigma _).
Proof.
Transparent eval.
case=> //= l Hl Hx s.
have Hl' : size l = sizeof_ptr by rewrite Hl sizeof_ptyp.
rewrite /=.
move: (optr_of_i8_Some _ Hl') => [] x0 Hx0.
rewrite i8_of_i32K.
congr (phy<=ptr).
rewrite Z2sK; last by simpl in *; omega.
rewrite sizeof_ityp /add_prod.
have ->: (Z_of_nat 1%nat) * x = x by case x.
case: (Hx) => /leZP -> _.
rewrite /ptr_of_phy /= Hx0 /=.
erewrite i32_of_i8_bij3; eauto.
Opaque eval.
Qed.

(* see also Ceqpn_add2l' in C_expr.v: less conditions but in one direction *)
Lemma Ceqpn_add2l t (e : exp sigma (:* t)) e1 e2 : forall s H1 H2 H3 H4,
  Z.sgn (Z<=s (i32<=i8 [ e1 ]_s H1)) = Z.sgn (Z<=s (i32<=i8 [ e2 ]_ s H2)) ->
  Z<=nat (sizeof t) * Z.abs (Z<=s (i32<=i8 [ e1 ]_s H3)) < 2 ^^ ptr_len ->
  Z<=nat (sizeof t) * Z.abs (Z<=s (i32<=i8 [ e2 ]_s H4)) < 2 ^^ ptr_len ->
  [e \+ e1 \= e \+ e2 ]_ s = [ e1 \= e2 ]_s.
Proof.
move=> s H1 H2 H3 h4 Hs Hs1 Hs2.
Transparent eval.
rewrite /=.
move He : ([ e ]_s) => [he Hhe].
move He1 : ([ e1 ]_s) => [he1 Hhe1].
move He2 : ([ e2 ]_s) => [he2 Hhe2].
case: ifP => H.
- symmetry.
  move/eqP/phy_of_ptr_inj in H.
  case: ifP; first by done.
  move/eqP => H0; apply False_ind; apply: H0.
  congr (Z<=s _).
  apply add_prod_inj in H; last 4 first.
    by apply sizeof_gt0.
    set hyp := Z<=s _ in Hs1.
    set goa := Z<=s _.
    suff : goa = hyp by move=> ->.
    rewrite /goa /hyp.
    congr (Z<=s).
    apply i32_of_i8_irr.
    by rewrite He1.
    set hyp := Z<=s _ in Hs2.
    set goa := Z<=s _.
    suff : goa = hyp by move=> ->.
    rewrite /goa /hyp.
    congr (Z<=s).
    apply i32_of_i8_irr.
    by rewrite He2.
    clear -Hs He1 He2.
    set lhs_hyp := Z<=s _ in Hs.
    set lhs_goa := Z<=s _.
    set rhs_hyp := Z<=s _ in Hs.
    set rhs_goa := Z<=s _.
    have <- : lhs_hyp = lhs_goa.
      rewrite /lhs_hyp /lhs_goa.
      congr (Z<=s).
      apply i32_of_i8_irr.
      by rewrite He1.
    have <- : rhs_hyp = rhs_goa.
      rewrite /rhs_hyp /rhs_goa.
      congr (Z<=s).
      apply i32_of_i8_irr.
      by rewrite He2.
    done.
  apply s2Z_inj in H.
  move: (i32_of_i8_inj he1 Hhe1 he2 Hhe2 H) => H0.
  subst he1.
  congr (i32<=i8 _ _).
  by apply eq_irrelevance.
- case: ifP; last by [].
  move/eqP/s2Z_inj/i32_of_i8_inj => ?; subst he1.
  move: H.
  suff : Hhe1 = Hhe2 by move=> ->; rewrite eqxx.
  by apply eq_irrelevance.
Opaque eval.
Qed.

(* was eq_p_sem_eq_equiv_spec *)
Lemma Ceqpn_add2l_sc_equiv t (e : exp sigma (:* t)) e1 e2 :
  Z.sgn e1 = Z.sgn e2 ->
  - 2 ^^ 31 <= Z<=nat (sizeof t) * e1 < 2 ^^ 31 ->
  - 2 ^^ 31 <= Z<=nat (sizeof t) * e2 < 2 ^^ 31 ->
  ( e \+ [ e1 ]sc \= e \+ [ e2 ]sc) =s ( ([ e1 ]sc : exp sigma (ityp: sint)) \= [ e2 ]sc).
Proof.
move=> H1 H2 H3 s.
have Htmp : 0 < Z<=nat (sizeof t) by apply/Z_of_nat_lt0/sizeof_gt0.
have He1 : - 2 ^^ 31 <= e1 < 2 ^^ 31.
  eapply Zlt_mult_interval_inv; [by apply Htmp | done].
have He2 : - 2 ^^ 31 <= e2 < 2 ^^ 31.
  eapply Zlt_mult_interval_inv; [by apply Htmp | done].
rewrite Ceqpn_add2l //.
- by rewrite size_sc.
- by rewrite size_sc.
- by rewrite size_sc.
- by rewrite size_sc.
- move=> H6 H7. by rewrite !s2Z_sc.
- move=> H6.
  rewrite s2Z_sc // -(geZ0_norm (Z<=nat (sizeof t))); last exact/Zle_0_nat.
  rewrite -normZM.
  apply Zabs_lt.
  split; [exact: ltZ_leZ_trans (proj1 H2) | exact: (ltZ_leZ_trans (proj2 H2))].
- move=> H6.
  rewrite s2Z_sc // -(geZ0_norm (Z<=nat (sizeof t))); last exact/Zle_0_nat.
  rewrite -normZM.
  apply Zabs_lt.
  split; [exact: ltZ_leZ_trans (proj1 H3) | exact: (ltZ_leZ_trans (proj2 H3))].
Qed.

End Cadd_sect.

Lemma sequiv_ge_sym {g} {sigma : g.-env} {t} (e1 e2 : exp sigma (ityp: t)) :
   e1 \>= e2 =s e2 \<= e1.
Proof.
Transparent eval.
move=> s /=.
move H1 : ( [ e1 ]_s ) => [h1 Hh1].
move H2 : ( [ e2 ]_s ) => [h2 Hh2].
by destruct t.
Opaque beval.
Qed.

Lemma sequiv_gt_sym {g} {sigma : g.-env} {t} (e1 e2 : exp sigma (ityp: t)) :
   e1 \> e2 =s e2 \< e1.
Proof.
Transparent eval.
move=> s /=.
move H1 : ( [ e1 ]_s ) => [h1 Hh1].
move H2 : ( [ e2 ]_s ) => [h2 Hh2].
by destruct t.
Opaque eval.
Qed.

Lemma sequiv_sub_e_sc {g} {sigma : g.-env} x y :
  - 2 ^^ 31 <= x < 2 ^^ 31 -> - 2 ^^ 31 <= y < 2 ^^ 31 -> - 2 ^^ 31 <= x - y < 2 ^^ 31 ->
  ([ x ]sc \- [ y ]sc : exp sigma (ityp: sint)) =s [ x - y ]sc.
Proof.
Transparent eval.
move=> Hx Hy xy s /=.
rewrite 2!i8_of_i32K.
Local Open Scope machine_int_scope.
suff -> : `( x )s_ 32 `- `( y )s_ 32 = `(x - y)s_ 32 by done.
apply s2Z_inj.
rewrite Z2sK; last by done.
rewrite s2Z_sub; last first.
  rewrite Z2sK; last by done.
  rewrite Z2sK; last by simpl in *; omega.
  simpl in *; omega.
rewrite Z2sK; last by simpl in *; omega.
rewrite Z2sK //; by simpl in *; omega.
Opaque eval.
Qed.

(** casts *)

Lemma sequiv_intsa_uchar_sc {g} {sigma : g.-env} (a : int 8) :
  (int) ([ a ]pc : exp sigma (g.-ityp: uchar)) =s ([ u2Z a ]sc : exp sigma _).
Proof.
move=> s.
Transparent eval.
apply: mkPhy_irrelevance => /=.
congr (i8<=i32).
apply s2Z_inj.
rewrite Z2sK; last first.
  rewrite /=; split.
  apply: (leZ_trans _ (min_u2Z _)) => //.
  exact: (ltZ_leZ_trans (max_u2Z _)).
rewrite s2Z_u2Z_pos'; last first.
  rewrite (u2Z_zext 24) /=; split; first by apply min_u2Z.
  exact: (ltZ_leZ_trans (max_u2Z _)).
by rewrite (u2Z_zext 24).
Opaque eval.
Qed.

Lemma unsa_sa_i8_to_uchar_uint_to_phy {g} {sigma : g.-env} (a : int 8) :
  (UINT) ( (int) ([ a ]pc : exp sigma (g.-ityp: uchar))) =s ([ zext 24 a ]pc : exp sigma _).
Proof.
move=> s.
Transparent eval.
rewrite /= /unsafe_cast_phy /phy_of_ui32 /=.
by apply mkPhy_irrelevance.
Opaque eval.
Qed.

Lemma int_int_cast {g} {sigma : g.-env} {t H} (e : exp sigma (ityp: t)):
  safe_cast _ sint sint (safe_cast _ _ sint e H) erefl =s
  (safe_cast _ _ sint e H).
Proof. move => s. done. Qed.

(** equivalence between boolean expressions *)

Definition bequiv {g} {sigma : g.-env} (b1 b2 : bexp sigma) := forall s, [ b1 ]b_ s = [ b2 ]b_ s.

Notation "a '=b' b" := (bequiv a b) (at level 72, format "'[' a  '=b'  b ']'", no associativity) : C_expr_scope.

Instance bequiv_equivalence g (sigma : g.-env) : Equivalence (@bequiv _ sigma).
constructor.
move=> s b; reflexivity.
move=> b1 b2 H s; by rewrite H.
move=> b1 b2 b3 H1 H2 s; by rewrite H1 H2.
Qed.

Instance beval_morphism g (sigma : g.-env) :
  Morphisms.Proper (bequiv ==> eq ==> eq) (@beval _ sigma).
Proof. by move => b1 b2 H s1 s2 ->; rewrite H. Qed.

Transparent eval beval.

Instance exp2bexp_morphism g (sigma : g.-env) :
  Morphisms.Proper (sequiv ==> bequiv) (@exp2bexp _ sigma).
Proof. by move => e1 e2 H s /=; rewrite H. Qed.

Instance bneg_morphism g (sigma : g.-env) :
  Morphisms.Proper (bequiv ==> bequiv) (@bneg _ sigma).
Proof. move => b1 b2 H s. by rewrite /= (H s). Qed.

Opaque eval beval.

Section bequiv_prop.

Variables (g : wfctxt) (sigma : g.-env).

Lemma bnegK (b : bexp sigma) : (\~b \~b b) =b b.
Proof. move => s. by rewrite !beval_neg_not negbK. Qed.

Lemma bneq_neg_eq {t} (a b : exp sigma (ityp: t)): \b a \!= b =b \~b \b a \= b.
Proof. move => s; by rewrite beval_neq_not_eq beval_neg_not beval_eq_e_eq. Qed.

Lemma bneg_neq_eq {t} (a b : exp sigma (ityp: t)): (\~b \b a \!= b) =b \b a \= b.
Proof. move => s; by rewrite beval_neg_not beval_neq_not_eq  beval_eq_e_eq negbK. Qed.

Transparent eval beval.

Lemma CgeqNlt {t} (e1 e2 : exp sigma (ityp: t)) : \b e1 \>= e2 =b \~b \b e1 \< e2.
Proof.
move=> s //=.
destruct t; destruct ([ e1 ]_ s); destruct ([ e2 ]_s); rewrite negbK leZNgt';
  case: (_ <? _) => //=; by rewrite is_zero_0 (negbTE not_is_zero_1).
Qed.

Lemma CleqNgt {t} (e1 e2 : exp sigma (ityp: t)): \b e1 \<= e2 =b \~b \b e1 \> e2.
Proof.
move=> s //=.
destruct t; destruct ([ e1 ]_ s); destruct ([ e2 ]_s); rewrite negbK leZNgt';
  case: (_ <? _) => //=; by rewrite is_zero_0 (negbTE not_is_zero_1).
Qed.

Lemma CgtNle t (e1 e2 : exp sigma (ityp: t)) : \b e1 \> e2 =b \~b \b e1 \<= e2.
Proof.
move=> s /=.
destruct t.
- move H1 : ( [ e1 ]_s ) => [h1 Hh1].
  move H2 : ( [ e2 ]_s ) => [h2 Hh2].
  case: ifP.
  + case: ifP.
    * by rewrite ltZNge' => ->.
    * by rewrite not_is_zero_1 is_zero_0.
  + case: ifP.
    * by rewrite not_is_zero_1 is_zero_0.
    * move/negbT; by rewrite -ltZNge' => ->.
- move H1 : ( [ e1 ]_s ) => [h1 Hh1].
  move H2 : ( [ e2 ]_s ) => [h2 Hh2].
  case: ifP.
  + case: ifP.
    * by rewrite ltZNge' => ->.
    * by rewrite not_is_zero_1 is_zero_0.
  + case: ifP.
    * by rewrite not_is_zero_1 is_zero_0.
    * move/negbT; by rewrite -ltZNge' => ->.
- move H1 : ( [ e1 ]_s ) => [h1 Hh1].
  move H2 : ( [ e2 ]_s ) => [h2 Hh2].
  case: ifP.
  + case: ifP.
    * by rewrite ltZNge' => ->.
    * by rewrite not_is_zero_1 is_zero_0.
  + case: ifP.
    * by rewrite not_is_zero_1 is_zero_0.
    * move/negbT; by rewrite -ltZNge' => ->.
- move H1 : ( [ e1 ]_s ) => [h1 Hh1].
  move H2 : ( [ e2 ]_s ) => [h2 Hh2].
  case: ifP.
  + case: ifP.
    * by rewrite ltZNge' => ->.
    * by rewrite not_is_zero_1 is_zero_0.
  + case: ifP.
    * by rewrite not_is_zero_1 is_zero_0.
    * move/negbT; by rewrite -ltZNge' => ->.
- move H1 : ( [ e1 ]_s ) => [h1 Hh1].
  move H2 : ( [ e2 ]_s ) => [h2 Hh2].
  case: ifP.
  + case: ifP.
    * by rewrite ltZNge' => ->.
    * by rewrite not_is_zero_1 is_zero_0.
  + case: ifP.
    * by rewrite not_is_zero_1 is_zero_0.
    * move/negbT; by rewrite -ltZNge' => ->.
Qed.

Lemma Cltn_add2r (a b c : Z) :
  - 2 ^^ 31 <= a < 2 ^^ 31 -> - 2 ^^ 31 <= b < 2 ^^ 31 -> - 2 ^^ 31 <= c < 2 ^^ 31 ->
  - 2 ^^ 31 <= a + c < 2 ^^ 31 -> - 2 ^^ 31 <= b + c < 2 ^^ 31 ->
  (\b ([ a ]sc \+ [ c ]sc : exp sigma (ityp: sint)) \< [ b ]sc \+ [ c ]sc) =b \b [ a ]sc \< ([ b ]sc : exp sigma (ityp: sint)) .
Proof.
move=> Ha Hb Hc Hac Hbc s /=.
rewrite !i8_of_i32K s2Z_add; last by rewrite Z2sK // Z2sK.
rewrite s2Z_add; last by rewrite Z2sK // Z2sK.
rewrite !Z2sK //.
case: ifPn => H.
  rewrite ltZ_add2r' in H.
  by rewrite H.
rewrite -leZNgt' in H.
move/leZP/leZ_add2r/leZP in H.
rewrite leZNgt' in H.
by rewrite (negbTE H).
Qed.

Opaque beval eval.

Lemma Cltn_add2r_pos (a b c : Z) : 0 <= a -> 0 <= b -> 0 <= c ->
  a + c < 2 ^^ 31 -> b + c < 2 ^^ 31 ->
  (\b ([ a ]sc \+ [ c ]sc : exp sigma (ityp: sint)) \< [ b ]sc \+ [ c ]sc) =b
  \b [ a ]sc \< ([ b ]sc : exp sigma (ityp: sint)).
Proof. move=> ? ? ? ? ?; rewrite Cltn_add2r //; omega. Qed.

End bequiv_prop.

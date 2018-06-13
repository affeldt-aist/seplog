(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import div path tuple.
Require Import Init_ext ssrZ ZArith_ext String_ext Max_ext.
Require Import machine_int seq_ext ssrnat_ext tuple_ext path_ext.
Require order finmap.
Import MachineInt.

Require Import C_types C_types_fp C_value C_expr C_expr_equiv.

Local Close Scope Z_scope.
Local Open Scope C_types_scope.
Local Open Scope C_value_scope.
Local Open Scope C_expr_scope.
Local Open Scope machine_int_scope.

(** ground arithmetic expressions *)

Lemma cat_nil {A: Type}: forall (l1: seq A) l2, l1 ++ l2 = nil -> l1 = nil /\ l2 = nil.
elim => //=.
Defined.

Definition ground_exp  {g} {sigma : g.-env} {t : g.-typ} :
  forall (e : exp sigma t) (H: vars e = nil), t.-phy.
induction e; simpl.
- done.
- move => H; exact p.
- move => /cat_nil [] H1 H2.
  exact ([ bop_n _ t b ([ IHe1 H1 ]c) ([ IHe2 H2 ]c) ]_ (store0 sigma)).
- move => H.
  exact (eval (store0 sigma) (bopk_n _ t b [IHe H ]c n)).
- move => /cat_nil [] H1 H2.
  exact (eval (store0 sigma) (bop_r _ t b ([ IHe1 H1 ]c) ([ IHe2 H2 ]c))).
- move => /cat_nil [] H1 H2.
  exact (eval (store0 sigma) ([ IHe1 H1 ]c \+ [ IHe2 H2 ]c)).
- move => H.
  exact (eval (store0 sigma) (safe_cast _ t t' [IHe H ]c i)).
- move => H.
  exact (eval (store0 sigma) (unsafe_cast _ t t' [IHe H ]c i)).
- move => H'.
  exact (eval (store0 sigma) (fldp _ f [IHe H' ]c H e0)).
- move => /cat_nil [] H1 H2.
  exact (eval (store0 sigma) ([ IHe1 H1 ]c \= [ IHe2 H2 ]c)).
- move => /cat_nil [] H1 / cat_nil [] H2 H3.
  exact (eval (store0 sigma) (ifte_e _ t ([ IHe1 H1 ]c) ([ IHe2 H2 ]c) ([ IHe3 H3 ]c))).
Defined.
Global Opaque ground_exp.

Notation "'[' e ']ge'" := (@ground_exp _ _ _ e (Logic.eq_refl _)) (at level 9, format "'[' [  e  ]ge ']'", only parsing) : C_expr_scope.
Notation "'[' e ']ge'" := (ground_exp e _) (at level 9, format "'[' [  e  ]ge ']'"): C_expr_scope.

Lemma ground_exp_sem {g} {ts : g.-env} (s : store ts) {ty : g.-typ} :
  forall (e : exp ts ty) (H : vars e = nil), [ e ]_s = ground_exp e H.
Transparent ground_exp.
induction e => //=.
- move/cat_nil => [] H1 H2.
  by rewrite -(IHe1 H1) -(IHe2 H2).
- move => H; by rewrite -(IHe H).
- move/cat_nil => [] H1 H2.
  by rewrite -(IHe1 H1) -(IHe2 H2).
- move/cat_nil => [] H1 H2.
  by rewrite -(IHe1 H1) -(IHe2 H2).
- move => H; by rewrite -(IHe H).
- move => H; by rewrite -(IHe H).
- move => H'; by rewrite -(IHe H').
- move/cat_nil => [] H1 H2.
  by rewrite -(IHe1 H1) -(IHe2 H2).
- move/cat_nil => [] H1 /cat_nil [] H2 H3.
  by rewrite -(IHe1 H1) -(IHe2 H2) -(IHe3 H3).
Opaque ground_exp.
Qed.

Lemma ground_exp_c_inj {g} {sigma : g.-env} {t} (pv1 pv2 : t.-phy) H1 H2 :
  ground_exp ([ pv1 ]c : exp sigma t) H1 = ground_exp ([ pv2 ]c : exp sigma t) H2 ->
  pv1 = pv2.
Proof. done. Qed.

Lemma ge_cast_sint_cst_8c g (sigma : g.-env) (a : int 8) H :
  ground_exp ((int) ([ a ]pc : exp sigma (g.-ityp: uchar)) ) H = [ zext 24 a ]p.
Proof.
Transparent eval beval.
rewrite /si32_of_phy /=.
by apply mkPhy_irrelevance.
Opaque eval beval.
Qed.

Lemma ge_cast_sint_cst_sint g (sigma : g.-env) (pv : (g.-ityp: sint).-phy) H :
  ground_exp ((int) ([ pv ]c : exp sigma (g.-ityp: sint))) H = pv.
Proof. done. Qed.

(* similar to ge_cst_e but in ge_cst_e c is a phyval *)
Lemma sequiv_ge {g} {ts : g.-env} ty (e : exp ts ty) (H : vars e = nil) :
  [ ground_exp e H ]c =s e.
Proof.
Transparent eval.
move=> s /=.
by rewrite ground_exp_sem.
Opaque eval.
Qed.

Lemma ge_cst_e {g sigma} {ty : g.-typ} (pv : ty.-phy) H : @ground_exp _ sigma _ [ pv ]c H = pv.
Proof. done. Qed.

Lemma i32_ge_s_cst_e {g} {sigma : g.-env} n H :
  si32<=phy (ground_exp ([ n ]sc : exp sigma _) H) = Z2s 32 n.
Proof. by rewrite ge_cst_e (si32_of_phy_sc _ _ (store0 sigma)). Qed.

Lemma i8_ge_8_cst_e {g} sigma z H :
  i8<=phy (@ground_exp g sigma _ [ z ]pc H) = z.
Proof. by rewrite ge_cst_e phy_of_ui8K. Qed.

Local Open Scope zarith_ext_scope.

Lemma sequiv_s2Z_si32_of_phy {g} {ts : g.-env} e H :
  ([s2Z (si32<=phy (ground_exp e H) )]sc : exp ts _ ) =s e.
Proof.
move=> s.
rewrite (ground_exp_sem _ e H).
set X := ground_exp e H.
destruct X.
unfold si32_of_phy; simpl.
move: (oi32_of_i8_Some _ Hphy) => [] x Hx.
rewrite Hx /= /phy_of_si32.
apply mkPhy_irrelevance => /=.
rewrite -(oi32_of_i8_bij _ _ Hx).
Transparent eval.
by rewrite /= Z2s_s2Z.
Opaque eval.
Qed.

Lemma s2Z_ge_s_cst_e {g sigma} z H : (- 2 ^^ 31 <= z < 2 ^^ 31)%Z ->
  s2Z (si32<=phy (@ground_exp g sigma _ [ z ]sc H)) = z.
Proof. move=> Hz. by rewrite i32_ge_s_cst_e Z2sK. Qed.

Lemma u2Z_ge_s_cst_e {g sigma} z H : (0 <= z < 2 ^^ 31)%Z ->
  u2Z (si32<=phy (@ground_exp g sigma _ [ z ]sc H)) = z.
Proof.
case=> Hz0 Hz1.
rewrite i32_ge_s_cst_e-s2Z_u2Z_pos.
rewrite Z2sK //; split => //; exact: (@leZ_trans Z0).
rewrite Z2sK //; split => //; exact: (@leZ_trans Z0).
Qed.

Lemma si32_of_phy_gb_add_e {g} {sigma : g.-env} (a b : exp sigma _) H Ha Hb :
  si32<=phy (ground_exp (a \+ b) H) =
  si32<=phy (ground_exp a Ha) `+ si32<=phy (ground_exp b Hb).
Proof.
by rewrite -(ground_exp_sem (store0 sigma)) si32_of_phy_binop_ne 2!(ground_exp_sem (store0 sigma)).
Qed.

Lemma si32_of_phy_gb_or_e {g} {sigma : g.-env} (a b : exp sigma _) H Ha Hb :
  si32<=phy (ground_exp (a \| b) H) =
  si32<=phy (ground_exp a Ha) `|` si32<=phy (ground_exp b Hb).
Proof.
by rewrite -(ground_exp_sem (store0 sigma)) si32_of_phy_binop_ne 2!(ground_exp_sem (store0 sigma)).
Qed.

(* NB: generaliser? *)
Lemma sint_shl_e_to_i32_ge g (sigma : g.-env) (a : int 8) H :
  si32<=phy (ground_exp ((int) ([ a ]pc : exp sigma (g.-ityp: uchar)) \<< [ 8 ]sc : exp sigma _) H) =
  zext 16 a `|| Z2u 8 0.
Proof.
Transparent eval beval.
rewrite /si32_of_phy /= i8_of_i32Ko /= !i8_of_i32K /= Z2s_Z2u_k // Z2uK //.
apply u2Z_inj.
rewrite (@u2Z_shl _ _ _ 8) //.
- by rewrite (u2Z_concat (zext 16 a)) Z2uK // !u2Z_zext addZ0 (u2Z_zext (8 * (4 - 1)) a).
- rewrite (u2Z_zext (8 * (4 - 1)) a).
  by apply max_u2Z.
Opaque eval beval.
Qed.

Local Open Scope Z_scope.

Lemma i8_of_phy_ifte {g sigma} (a b c d : _) H :
  i8<=phy (@ground_exp g sigma _ ([ a ]c \<= [ b ]c \? [ c ]c \: [ d ]c) H) =
  if Z<=u (i8<=phy a) <=? Z<=u (i8<=phy b) then i8<=phy c else i8<=phy d.
Proof.
Transparent eval.
rewrite -(ground_exp_sem (store0 sigma)) /=.
destruct a as [a Ha] => //=.
have Ha' : size a = 1%nat by rewrite Ha sizeof_ityp.
have Ha'Ha : Ha' = Ha by apply eq_irrelevance.
subst Ha.
destruct a as [|a []] => //=.
destruct b as [b Hb] => //=.
have Hb' : size b = 1%nat by rewrite Hb sizeof_ityp.
have Hb'Hb : Hb' = Hb by apply eq_irrelevance.
subst Hb.
destruct b as [|b []] => //=.
set a1 := Z<=u _.
set b1 := Z<=u _.
case: ifP.
  rewrite /is_zero.
  case: ifP => // _ /eqP.
  case.
  move/int_break_inj => abs.
  exfalso.
  lapply abs => //.
  by apply Z2u_dis.
case: ifP => // _.
by rewrite is_zero_0.
Opaque eval.
Qed.

Local Close Scope Z_scope.

(** ground boolean expressions *)

Lemma ground_bexp_helper1 {g} {sigma : g.-env} (e : exp sigma (ityp: uint)) : bvars (exp2bexp sigma e) = nil -> vars e = nil.
Proof. done. Qed.

Lemma ground_bexp_helper2 {g} {sigma : g.-env} (b : bexp sigma) : bvars (bneg sigma b) = nil -> bvars b = nil.
Proof. done. Qed.

Fixpoint ground_bexp {g} {sigma : g.-env} (b : bexp sigma) : bvars b = nil -> bool :=
match b as b0 return bvars b0 = nil -> bool with
| exp2bexp e => fun H => ~~ is_zero (ground_exp e (ground_bexp_helper1 e H))
| bneg b' => fun H => ~~ ground_bexp b' (ground_bexp_helper2 b' H)
end.
Global Opaque ground_bexp.

Lemma gb_bneg {g} {sigma: g.-env} (b : bexp sigma) H : ground_bexp (\~b b) H = ~~ ground_bexp b H.
Proof.
congr (~~ _ _ _ _ _).
by apply eq_irrelevance.
Qed.

Lemma ground_bexp_sem  {g} {sigma : g.-env} (s : store sigma) :
  forall (b : bexp sigma) (H : bvars b = nil), [ b ]b_ s = ground_bexp b H.
Proof.
Transparent beval.
induction b => //=.
- move => H.
  rewrite ground_exp_sem /=.
  congr (~~ _ [ _ ]ge).
  by apply eq_irrelevance.
- move => H; by rewrite IHb gb_bneg.
Opaque beval.
Qed.

Notation "'[' e ']gb'" := (@ground_bexp _ _ e erefl) (at level 9, only parsing) : C_expr_scope.
Notation "'[' e ']gb'" := (ground_bexp e _) (at level 9): C_expr_scope.

Section ground_bexp_prop.

Variables (g : wfctxt) (sigma : g.-env).

Lemma bneg_0uc H : @ground_bexp _ sigma (\~b \b [ 0 ]uc) H.
Proof.
Transparent beval.
by rewrite -(ground_bexp_sem (store0 sigma)) /= is_zero_0.
Opaque beval.
Qed.

Lemma oneuc H : @ground_bexp _ sigma ( \b [ 1 ]uc ) H.
Proof.
Transparent beval.
by rewrite -(ground_bexp_sem (store0 sigma)) /= not_is_zero_1.
Opaque beval.
Qed.

Lemma gb_eq_p {t} (a b : exp sigma (:* t)) H H1 H2 :
  ground_bexp ( \b a \= b ) H = (ground_exp a H1 == ground_exp b H2).
Proof.
by rewrite -(ground_bexp_sem (store0 sigma) _ H) beval_eq_p_eq -!(ground_exp_sem (store0 _)).
Qed.

Lemma and_gb (e1 e2 : exp sigma (ityp: uint)) H H1 H2 :
  ground_bexp (\b e1 \&& e2) H = ground_bexp (\b e1) H1 && ground_bexp (\b e2) H2.
Proof.
Transparent eval beval.
rewrite -!(ground_bexp_sem (store0 sigma)) /=.
move He1 : ( [ e1 ]_(store0 _) ) => [he1 Hhe1].
move He2 : ( [ e2 ]_(store0 _) ) => [he2 Hhe2].
set tmp1 := eq_ind_r _ _ _. rewrite (_ : tmp1 = Hhe1); last by apply eq_irrelevance.
set tmp2 := eq_ind_r _ _ _. rewrite (_ : tmp2 = Hhe2); last by apply eq_irrelevance.
case: ifP => [Hcase | /negbT].
  rewrite is_zero_0; symmetry; apply/negbTE.
  rewrite negb_and 2!negbK /is_zero /=.
  apply/orP.
  case/orP : Hcase => /eqP Hcase; [left | right].
    apply/eqP.
    apply mkPhy_irrelevance => /=.
    symmetry; apply i32_of_i8_bij with Hhe1.
    apply u2Z_inj.
    by rewrite Hcase Z2uK.
  apply/eqP.
  apply mkPhy_irrelevance => /=.
  symmetry; apply i32_of_i8_bij with Hhe2.
  apply u2Z_inj; by rewrite Hcase Z2uK.
rewrite not_is_zero_1 negb_or; case/andP => Ha Hb.
symmetry; apply/andP; split.
  move: Ha; apply contra.
  rewrite /is_zero; case/eqP => ?; subst he1.
  by rewrite i8_of_i32K Z2uK.
move: Hb; apply contra.
rewrite /is_zero; case/eqP => ?; subst he2.
by rewrite i8_of_i32K Z2uK.
Opaque eval beval.
Qed.

Lemma and_8c (a b : int 8) H :
  ground_exp ([ a ]pc \& [ b ]pc : exp sigma (g.-ityp: uchar)) H =
  ground_exp ([ a `& b ]pc : exp sigma _) H.
Proof. by []. Qed.

End ground_bexp_prop.

Section ground_bexp_eq.

Variables (g : wfctxt) (sigma : g.-env) (t : integral) (a b : exp sigma (ityp: t)).
Hypotheses (Ha : vars a = nil) (Hb : vars b = nil).

Lemma gb_eq_e H : ground_bexp (\b a \= b) H = (ground_exp a Ha == ground_exp b Hb).
Proof. by rewrite -(ground_bexp_sem (store0 _) _ H) beval_eq_e_eq -!(ground_exp_sem (store0 _)). Qed.

Lemma gb_neq H H' : ground_bexp (\b a \!= b) H = ~~ ground_bexp (\b a \= b) H'.
Proof. by rewrite -!(ground_bexp_sem (store0 sigma)) beval_neq_not_eq beval_eq_e_eq. Qed.

Lemma gb_bneg_bop_r_lt H H' : ground_bexp (\~b \b a \< b) H = ground_bexp (\b a \>= b) H'.
Proof. by rewrite -!(ground_bexp_sem (store0 sigma)) CgeqNlt. Qed.

Lemma gb_bneg_bop_r_ge H H' : ground_bexp (\~b \b a \>= b) H = ground_bexp (\b a \< b) H'.
Proof. by rewrite -!(ground_bexp_sem (store0 sigma)) CgeqNlt bnegK. Qed.

Lemma gb_bneg_bop_r_gt H H' : ground_bexp (\~b \b a \> b) H = ground_bexp (\b a \<= b) H'.
Proof. by rewrite -!(ground_bexp_sem (store0 sigma)) -CleqNgt. Qed.

Lemma gb_ge_lt H H' : ground_bexp (\b a \>= b) H = ground_bexp (\b b \<= a) H'.
Proof. by rewrite -!(ground_bexp_sem (store0 sigma)) sequiv_ge_sym. Qed.

End ground_bexp_eq.

Local Open Scope zarith_ext_scope.
Local Open Scope Z_scope.

Section ground_bexp_Zlt_Zle.

Variables (g : wfctxt) (sigma : g.-env) (e1 e2 : exp sigma (ityp: sint)).
Hypotheses (H1 : vars e1 = nil) (H2 : vars e2 = nil).

(* NB: lower bounds could be generalized to - 2 ^^ 31 *)
Lemma le_n_gb H : 0 <= Z<=s (si32<=phy (ground_exp e1 H1)) < 2 ^^ 31 ->
  0 <= Z<=s (si32<=phy (ground_exp e2 H2)) < 2 ^^ 31 ->
  ground_bexp (\b e1 \<= e2) H -> si32<=phy (ground_exp e1 H1) `<= si32<=phy (ground_exp e2 H2).
Proof.
move=> K1 K2.
rewrite -!(ground_bexp_sem (store0 sigma)) -!(ground_exp_sem (store0 sigma)).
move/bop_re_le_Zle => K.
apply Zle2le_n.
case: K1; move/s2Z_u2Z_pos => K1 _.
rewrite -!(ground_exp_sem (store0 sigma)) in K1.
case: K2; move/s2Z_u2Z_pos => K2 _.
rewrite -!(ground_exp_sem (store0 sigma)) in K2.
congruence.
Qed.

Lemma lt_n_gb H : 0 <= Z<=s (si32<=phy (ground_exp e1 H1)) < 2 ^^ 31 ->
  0 <= Z<=s (si32<=phy (ground_exp e2 H2)) < 2 ^^ 31 ->
  ground_bexp (\b e1 \< e2) H -> si32<=phy (ground_exp e1 H1) `< si32<=phy (ground_exp e2 H2).
Proof.
move=> K1 K2.
rewrite -!(ground_bexp_sem (store0 sigma)) -!(ground_exp_sem (store0 sigma)).
move/bop_re_lt_Zlt =>  K.
apply Zlt2lt_n.
case: K1; move/s2Z_u2Z_pos => K1 _.
rewrite -!(ground_exp_sem (store0 sigma)) in K1.
case: K2; move/s2Z_u2Z_pos => K2 _.
rewrite -!(ground_exp_sem (store0 sigma)) in K2.
congruence.
Qed.

Lemma Zlt_gb H : ground_bexp (\b e1 \< e2) H ->
  0 <= Z<=s (si32<=phy (ground_exp e1 H1)) < 2 ^^ 31 ->
  0 <= Z<=s (si32<=phy (ground_exp e2 H2)) < 2 ^^ 31 ->
  Z<=s (si32<=phy (ground_exp e1 H1)) < Z<=s (si32<=phy (ground_exp e2 H2)).
Proof.
move=> K K1 K2.
rewrite -1!(ground_bexp_sem (store0 sigma)) in K.
rewrite -2!(ground_exp_sem (store0 sigma)).
by apply bop_re_lt_Zlt.
Qed.

Lemma Zle_gb H : ground_bexp (\b e1 \<= e2) H ->
  s2Z (si32<=phy (ground_exp e1 H1)) <= s2Z (si32<=phy (ground_exp e2 H2)).
Proof.
move=> H'.
rewrite -2!(ground_exp_sem (store0 sigma)).
apply bop_re_le_Zle.
by rewrite -(ground_bexp_sem (store0 sigma)) in H'.
Qed.

Lemma Zle_gb_inv H :
  Z<=s (si32<=phy (ground_exp e1 H1)) <= Z<=s (si32<=phy (ground_exp e2 H2)) ->
  ground_bexp (\b e1 \<= e2) H.
Proof.
Transparent eval beval.
rewrite -(ground_bexp_sem (store0 sigma)) -2!(ground_exp_sem (store0 sigma)) /=.
move He1 : ( [ e1 ]_ _) => [e1s0 He1s0].
move He2 : ( [ e2 ]_ _) => [e2s0 He2s0] K.
case: ifP; first by rewrite not_is_zero_1.
rewrite /si32_of_phy /= in K.
have He1s0' : size e1s0 = 4%nat by rewrite He1s0 sizeof_ityp.
case/oi32_of_i8_Some : He1s0' => x Hx.
rewrite Hx /= in K.
have He2s0' : size e2s0 = 4%nat by rewrite He2s0 sizeof_ityp.
case/oi32_of_i8_Some : He2s0' => y Hy.
rewrite Hy /= in K.
rewrite (i32_of_i8_bij3 _ _ _ Hx) (i32_of_i8_bij3 _ _ _ Hy).
move/leZP => abs; contradiction.
Opaque eval beval.
Qed.

(* almost the same proof as Zle_gb_inv *)
Lemma Zlt_gb_inv H :
   Z<=s (si32<=phy (ground_exp e1 H1)) < Z<=s (si32<=phy (ground_exp e2 H2)) ->
   ground_bexp (\b e1 \< e2) H.
Proof.
Transparent eval beval.
rewrite -(ground_bexp_sem (store0 sigma)) -2!(ground_exp_sem (store0 sigma)) /=.
move He1 : ( [ e1 ]_ _) => [e1s0 He1s0].
move He2 : ( [ e2 ]_ _) => [e2s0 He2s0] => K.
case: ifP; first by rewrite not_is_zero_1.
rewrite /si32_of_phy /= in K.
have He1s0' : size e1s0 = 4%nat by rewrite He1s0 sizeof_ityp.
case/oi32_of_i8_Some : He1s0' => x Hx.
rewrite Hx /= in K.
have He2s0' : size e2s0 = 4%nat by rewrite He2s0 sizeof_ityp.
case/oi32_of_i8_Some : He2s0' => y Hy.
rewrite Hy /= in K.
rewrite (i32_of_i8_bij3 _ _ _ Hx) (i32_of_i8_bij3 _ _ _ Hy).
move/ltZP => abs; contradiction.
Opaque eval beval.
Qed.

Lemma ground_bexp_lt0n H :
  0 < Z<=s (si32<=phy (ground_exp e1 H1)) -> ground_bexp (\b [ 0 ]sc \< e1) H.
Proof.
move=> H0.
Transparent beval eval.
rewrite -(ground_bexp_sem (store0 sigma) (\b [ 0 ]sc \< e1)) /=.
move He1 : ([ e1 ]_ _) => [l1 Hl1].
rewrite i8_of_i32K Z2sK //.
case: ifP; first by rewrite not_is_zero_1.
rewrite -(ground_exp_sem (store0 sigma)) He1 /= in H0.
set lhs := si32<=phy _ in H0.
set rhs := i32<=i8 _ _.
suff: lhs = rhs by move=> <- /ltZP.
rewrite /lhs /rhs {lhs rhs H0} /si32_of_phy /oi32_of_i8.
have : List.length l1 = 4%nat.
  clear He1; by rewrite sizeof_ityp /= in Hl1.
case/(int_flat_Some erefl) => x Hx.
rewrite Hx /= /i32_of_i8.
by symmetry; apply int_flat_int_flat_ok.
Opaque beval eval.
Qed.

Lemma ground_bexp_le0n H :
  0 <= Z<=s (si32<=phy (ground_exp e1 H1)) -> ground_bexp (\b [ 0 ]sc \<= e1) H.
Proof.
move=> H0.
Transparent beval eval.
rewrite -(ground_bexp_sem (store0 sigma) (\b [ 0 ]sc \<= e1)) /=.
move He1 : ([ e1 ]_ _) => [l1 Hl1].
rewrite i8_of_i32K Z2sK //.
case: ifP; first by rewrite not_is_zero_1.
rewrite -(ground_exp_sem (store0 sigma)) He1 /= in H0.
set lhs := si32<=phy _ in H0.
set rhs := i32<=i8 _ _.
suff: lhs = rhs by move=> <- /leZP.
rewrite /lhs /rhs {lhs rhs H0} /si32_of_phy /oi32_of_i8.
have : List.length l1 = 4%nat.
  clear He1; by rewrite sizeof_ityp /= in Hl1.
case/(int_flat_Some erefl) => x Hx.
rewrite Hx /= /i32_of_i8.
by symmetry; apply int_flat_int_flat_ok.
Opaque beval eval.
Qed.

End ground_bexp_Zlt_Zle.

Definition ground_bexp_relation {g} {sigma : g.-env} :
  Relations.Relation_Definitions.relation (forall (b : bexp sigma) (Hb : bvars b = nil), Prop).
red.
apply Morphisms.respectful_hetero.
exact bequiv.
move=> x y.
apply Morphisms.respectful_hetero.
exact (fun _ _ => True).
move=> Hx Hy.
exact iff.
Defined.

Instance ground_bexp_morphism {g} {sigma : g.-env} :
  Morphisms.Proper ground_bexp_relation (@ground_bexp _ sigma).
move=> b1 b2 Hb /= Hb1 Hb2 _ /=.
by rewrite -(ground_bexp_sem (store0 _)) -(ground_bexp_sem (store0 _)) Hb.
Qed.

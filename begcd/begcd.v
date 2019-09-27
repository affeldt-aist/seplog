(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Psatz.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac integral_type.
Require Import simu.
Import simu.simu_m.

Module EGCD.

Import syntax_m.seplog_m.assert_m.expr_m.
Import syntax_m.seplog_m.assert_m.
Import syntax_m.seplog_m.

Local Open Scope pseudo_cmd_scope.
Local Open Scope pseudo_expr_scope.
Local Open Scope uniq_scope.
Local Open Scope zarith_ext_scope.

(* NB: this is only for the module instantiated with Z *)
Lemma div_e_exact_full_2 : forall e s,
  [ e ]e_ s mod 2 = 0 -> 2 * [ e ./e nat_e 2 ]e_s = [ e ]e_s.
Proof. move=> e s He. by rewrite (Z_div_exact_full_2 ([ e ]e_ s) 2). Qed.

(** prelude of binary gcd algorithms *)
Definition prelude x y g :=
  While var_e x \% nat_e 2 \= nat_e O \&& var_e y \% nat_e 2 \= nat_e O {{
    x <- var_e x ./e nat_e 2 ;
    y <- var_e y ./e nat_e 2 ;
    g <- var_e g \* nat_e 2 }}.

Local Open Scope pseudo_hoare_scope.

(** binary gcd algorithm, from the Handbook of Applied Cryptography *)

Module BGCD_HAC.

Definition bgcd g x y t :=
  g <- nat_e 1 ;
  prelude x y g ;
  While var_e x \> nat_e 0 {{
    While var_e x \% nat_e 2 \= nat_e 0 {{ x <- var_e x ./e nat_e 2 }} ;
    While var_e y \% nat_e 2 \= nat_e 0 {{ y <- var_e y ./e nat_e 2 }} ;
    t <- \| (var_e x \- var_e y) \| ./e nat_e 2 ;
    If var_e x \>= var_e y Then
      x <- var_e t
    Else
      y <- var_e t
  }}.

Section bgcd_hac.

Variables x y g t : nat.
Variables vx vy : Z.

Lemma prelude_triple : uniq(x, y, g) -> 0 <= vx -> 0 <= vy ->
  {{ fun s _ => 0 <= [ x ]_s /\ 0 <= [ y ]_s /\ 0 <= [ g ]_s /\
    [ x ]_ s * [ g ]_ s = vx /\ [ y ]_ s * [ g ]_ s = vy }}
  prelude x y g
  {{ fun s _ => 0 <= [ x ]_ s /\ 0 <= [ y ]_ s /\ 0 <= [ g ]_ s /\
    [ x ]_ s * [ g ]_ s = vx /\ [ y ]_ s * [ g ]_ s = vy /\
    ~~ [ var_e x \% nat_e 2 \= nat_e 0 \&& var_e y \% nat_e 2 \= nat_e 0 ]b_ s }}.
Proof.
move=> Hset Hvx Hvy.
apply hoare_prop_m.hoare_while_invariant with (fun s _ =>
  0 <= [ x ]_ s /\ 0 <= [ y ]_ s /\ 0 <= [ g ]_ s /\
  [ x ]_ s * [g ]_ s = vx /\ [ y ]_ s * [ g ]_ s = vy ).
by move=> s h /= [H1 [H2 [H3 [H4 H5]]]].
by move=> s h /= [[H1 [H2 [H3 [H4 H5]]]] H6].
(** x <- var_e x ./e nat_e 2 *)
apply hoare_assign with (fun s h => 0 <= [ x ]_s /\ 0 <= [ y ]_s /\ 0 <= [ g ]_s /\
  2 * [ x ]_s * [ g ]_s = vx /\ [ y ]_s * [ g ]_s = vy /\ [ y ]_s mod 2 = 0).
move=> s h [[H1 [H2 [H3 [H4 H5]]]] H6].
rewrite /wp_assign.
repeat Store_upd => //.
split; first exact: Z_div_pos.
repeat (split; first by []).
split.
- rewrite div_e_exact_full_2 //; by rewrite /hoare_m.eval_b in H6; omegab.
  split; first by [].
- by rewrite /hoare_m.eval_b in H6; omegab.
(** y <- var_e y ./e nat_e 2; *)
apply hoare_assign with (fun s h => 0 <= [ x ]_s /\ 0 <= [ y ]_s /\ 0 <= [ g ]_s /\
  2 * [ x ]_s * [ g ]_s = vx /\ 2 * [ y ]_s * [ g ]_ s = vy).
move=> s h [H1 [H2 [H3 [H4 [H5 H6]]]]].
rewrite /wp_assign; repeat Store_upd => //.
split; first by [].
split; first exact: Z_div_pos.
repeat (split; first by []).
by rewrite div_e_exact_full_2.
(** g <- nat_e 2 *e var_e g *)
apply hoare_assign'.
move=> s h [H1 [H2 [H3 [H4 H5]]]].
rewrite /wp_assign; repeat Store_upd => //.
repeat (split; first by []).
split; first exact: mulZ_ge0.
split; rewrite /= -?H4 -?H5 /ZIT.mul; ring.
Qed.

Lemma bgcd_triple : uniq(x, y, g, t) -> 0 <= vx -> 0 <= vy ->
  {{ fun s h => [x]_s = vx /\ [y]_s = vy }}
  bgcd g x y t
  {{ fun s h => 0 <= [ x ]_s /\ 0 <= [ y ]_s /\ 0 <= [ g ]_s  /\
    Zis_gcd vx vy ([ g ]_s * [y]_s)}}.
Proof.
move=> Hset Hvx Hvy.
rewrite /bgcd.
(** g <- nat_e 1 ; *)
apply hoare_assign with (fun s _ =>  [x ]_ s = vx /\ [y ]_ s = vy /\ [g ]_ s = 1).
move=> s h; rewrite /wp_assign; move=> [Hx Hy].
by repeat Store_upd => //.
(** prelude x y g *)
apply while.hoare_seq with (fun s _ =>
  0 <= [x]_s /\ 0 <= [y]_s /\ 0 <= [g]_s /\
  Z.gcd vx vy = [g]_s * Z.gcd ([x]_s) ([y]_s) /\
  ~ [ var_e x \% nat_e 2 \= nat_e O \&& var_e y \% nat_e 2 \= nat_e O ]b_ s).
have Hset' : uniq(x, y, g).
  rewrite [Equality.sort _]/= in Hset *; Uniq_uniq O.
eapply while.hoare_conseq; last exact: (prelude_triple Hset' Hvx Hvy).
- move=> s h /= [H1 [H2 [H3 [H4 [H5 H6]]]]].
  repeat (split => //).
  + rewrite -H4 -H5.
    apply Zis_gcd_gcd; last first.
      rewrite (mulZC [x]_s) (mulZC [y]_s); exact/Zis_gcd_mult/Zgcd_is_gcd.
    apply mulZ_ge0 => //; exact: Zgcd_is_pos.
  + by move/negP: H6.
- move=> s h /= [-> [-> ->]]; by rewrite 2!mulZ1.
(** while (nat_e x >> nat_e 0) *)
apply hoare_prop_m.hoare_while_invariant with (fun s _ => 0 <= [x]_s /\ 0 <= [y]_s /\ 0 <= [g]_s /\
  (Zodd [x]_s \/ Zodd [y]_s) /\
  Z.gcd vx vy = [g]_s * Z.gcd ([x]_s) ([y]_s)).
- move=> s h [Hx_pos [Hy_pos [Hg_pos [H1 H2]]]].
  repeat (split => //).
  rewrite /= in H2.
  move/negP : H2.
  rewrite negb_and.
  case/orP ;
    move/eqP/not_Zmod_2_Zodd ; by auto.
- move=> s h [[Hx_pos [Hy_pos [Hg_pos [Hparity Hgcd]]]] Hx].
  repeat (split; first by []).
  have {Hx} : [x ]_ s = 0.
    move: Hx.
    rewrite /hoare_m.eval_b /= -ZIT.gebNgt.
    move/ZIT.geP.
    rewrite /ZIT.ge => ?; omega.
  rewrite /= => Hx.
  rewrite Hx /= Z.abs_eq // in Hgcd.
  rewrite -Hgcd; exact: Zgcd_is_gcd.
(** while (var_e x mode nat_e 2 =e nat_e 0) *)
apply while.hoare_seq with (fun s _ => 0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\
  Zodd [x]_s /\
  Z.gcd vx vy = [g ]_ s * Z.gcd [x ]_ s [y ]_ s).
- apply hoare_prop_m.hoare_while_invariant with (fun s _ =>
    0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\
    (Zodd [x ]_ s \/ Zodd [y ]_ s) /\
    Z.gcd vx vy = [g ]_ s * Z.gcd [x ]_ s [y ]_ s).
  + by move=> s h /= [[H2 [H3 [H4 [H5 H6]]]] H1].
  + move=> s h /= [[H2 [H3 [H4 [H5 H6]]]]] //.
    by move/eqP/not_Zmod_2_Zodd.
  + apply hoare_assign' => s h /= [[H2 [H3 [H4 [H5 H6]]]] H1].
    rewrite /wp_assign; repeat Store_upd => //.
    split; first exact: Z_div_pos.
    do 2 split => //.
    case: H5 => H5.
    * move/eqP/Zmod_2_Zeven : H1.
      by move/Zeven_not_Zodd.
    * split; first by auto.
      rewrite /= -Zgcd_even_odd //.
      by move/eqP/Zmod_2_Zeven : H1.
- apply while.hoare_seq with (fun s _ => 0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\
  Zodd [x ]_ s /\ Zodd [y]_s /\
  Z.gcd vx vy = [g ]_ s * Z.gcd [x ]_ s [y ]_ s).
  + apply hoare_prop_m.hoare_while_invariant with (fun s _ =>
    0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\
    Zodd [x ]_ s /\ Z.gcd vx vy = [g ]_ s * Z.gcd [x ]_ s [y ]_ s) => //.
    * move=> s h /= [[H2 [H3 [H4 [H5 H6]]]] H1].
      repeat (split => //).
      by move/eqP/not_Zmod_2_Zodd : H1.
    * apply hoare_assign' => s h /= [[H2 [H3 [H4 [H5 H6]]]] H1].
      rewrite /wp_assign; repeat Store_upd => //.
      split; first by [].
      split; first exact: Z_div_pos.
      repeat (split; first by []).
      rewrite /= (Zgcd_sym [x]_s) -Zgcd_even_odd //.
      by rewrite (Zgcd_sym [y]_s).
      move/eqP : H1; by move/Zmod_2_Zeven.
+ apply hoare_assign with (fun s _ => (0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\
    Zodd [x ]_ s /\ Zodd [y]_s /\
    Z.gcd vx vy = [g ]_ s * Z.gcd [x ]_ s [y ]_ s /\
    [t]_s = Z.abs ([x]_s - [y]_s) / 2)).
  move=> s h /= [Hx_pos [Hy_pos [Hg_pos [Hx [Hy Hgcd]]]]].
  by rewrite /wp_assign; repeat Store_upd.
  apply while.hoare_ifte.
  + apply hoare_assign'.
    move=> s h /= [[Hx_pos [Hy_pos [Hg_pos [Hx [Hy [Hgcd Ht]]]]]] Hcond].
    rewrite /wp_assign; repeat Store_upd => //.
    split.
    * rewrite /= Ht.
      apply Z_div_pos => //; exact/normZ_ge0.
    * repeat (split; first by []).
      split; first by right.
      rewrite /= Ht Z.abs_eq; last first.
        rewrite /ZIT.geb in Hcond.
        move/geZP : Hcond => ?; omega.
      rewrite -Zgcd_even_odd //; last first.
        apply Zodd_plus_Zodd => //; exact: Zodd_opp.
      by rewrite (Zgcd_for_euclid _ _ (-1)).
  - apply hoare_assign' => s h /= [[Hx_pos [Hy_pos [Hg_pos [Hx [Hy [Hgcd Ht]]]]]] Hcond].
    rewrite /wp_assign; repeat Store_upd => //.
    split; first by [].
    split.
    * rewrite /= Ht.
      apply Z_div_pos => //; exact/normZ_ge0.
    * split; first by [].
      split; first by left.
      rewrite /= Ht Zabs_non_eq; last by move/negbTE : Hcond => /geZP ?; omega.
      rewrite Zopp_plus_distr oppZK addZC (Zgcd_sym [x]_s) -Zgcd_even_odd //; last first.
        apply Zodd_plus_Zodd => //; exact: Zodd_opp.
      by rewrite (Zgcd_for_euclid _ _ (-1)) (Zgcd_sym [y]_s).
Qed.

End bgcd_hac.

End BGCD_HAC.

(** extended binary gcd algorithm, from the Handbook of Applied Cryptography *)

Module BEGCD_HAC.

Definition inner_loop u x y A B :=
  While var_e u \% nat_e 2 \= nat_e O {{
    u <- var_e u ./e nat_e 2 ;
    If var_e A \% nat_e 2 \= nat_e O \&& var_e B \% nat_e 2 \= nat_e O Then
      A <- var_e A ./e nat_e 2 ;
      B <- var_e B ./e nat_e 2
    Else
       A <- (var_e A \+ var_e y) ./e nat_e 2 ;
       B <- (var_e B \- var_e x) ./e nat_e 2
    }}.

Definition branch u v A B C D :=
  u <- var_e u \- var_e v ;
  A <- var_e A \- var_e C ;
  B <- var_e B \- var_e D.

Definition outer_loop u v x y A B C D :=
  While var_e u \> nat_e 0 {{
    inner_loop u x y A B ;
    inner_loop v x y C D ;
    If var_e u \>= var_e v Then
      branch u v A B C D
    Else
      branch v u C D A B
  }}.

Definition begcd g x y u v A B C D :=
  g <- nat_e 1 ;
  prelude x y g ;
  u <- var_e x ;
  v <- var_e y ;
  A <- nat_e 1 ;
  B <- nat_e O ;
  C <- nat_e O ;
  D <- nat_e 1 ;
  outer_loop u v x y A B C D.

Lemma inner_loop_triple (x y g u v : nat) vx vy (A B C D : bipl.var.v) :
  uniq(x, y, g, u, v, A, B, C, D) ->
  {{fun s _ => 0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [u ]_ s /\ 0 <= [v ]_ s /\
    [ x ]_ s * [ g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
    [ A ]_ s * [ x ]_ s + [B ]_ s * [y ]_ s = [u ]_ s /\
    [ C ]_ s * [ x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
    Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
    (Zodd [x]_s \/ Zodd [y]_s) /\
    (Zodd [u]_s \/ Zodd [v]_s) }}
  inner_loop u x y A B
  {{fun s _ => 0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [u ]_ s /\ 0 <= [v ]_ s /\
     [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
    [ A ]_ s * [ x ]_ s +  [B ]_ s * [y ]_ s = [u ]_ s /\
    [ C ]_ s * [ x ]_ s + [ D ]_ s * [y ]_ s = [v ]_ s /\
    Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
    (Zodd [ x ]_s \/ Zodd [ y ]_s) /\
    Zodd [ u ]_s }}.
Proof.
move=> Hset.
apply hoare_prop_m.hoare_while_invariant with (fun s _ =>
  0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [u ]_ s /\ 0 <= [v ]_ s /\
  [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
  [A ]_ s * [x ]_ s + [B ]_ s * [y ]_ s = [u ]_ s /\
  [C ]_ s * [x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
  Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
  (Zodd [x]_s \/ Zodd [y]_s) /\
  (Zodd [u]_s \/ Zodd [v]_s)).
move=> s h /= [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]]]].
by intuition.
move=> s h /= [[H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]]]] H1].
repeat (split => //).
move/ZIT.eqP : H1.
by move/not_Zmod_2_Zodd.
(** u <- var_e u ./e nat_e 2; *)
apply hoare_assign with (fun s _ =>
  0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [u ]_ s /\ 0 <= [v ]_ s /\
  [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
  [A ]_ s * [x ]_ s + [B ]_ s * [y ]_ s = [u ]_ s * 2 /\
  [C ]_ s * [x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
  Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
  (Zodd [x]_s \/ Zodd [y]_s) /\
  Zodd [v]_s).
move=> s h /= [[H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]]]] H1].
rewrite /wp_assign; repeat Store_upd.
move/eqP/Zmod_2_Zeven in H1.
repeat (split => //).
exact: Z_div_pos.
rewrite /= /ZIT.div.
case/Zeven_ex : H1 => u' H1.
rewrite [LHS]/= in H1.
by rewrite H1 (mulZC 2) Z_div_mult_full // -(mulZC 2) H9.
rewrite -Zgcd_even_odd //.
case: H13 => //.
by move/Zeven_not_Zodd.
case: H13 => //.
by move/Zeven_not_Zodd.
(** ifte (var_e A mode nat_e 2 =e nat_e 0 &e var_e B mode nat_e 2 =e nat_e 0) *)
apply while.hoare_ifte.
- (** A <- var_e A ./e nat_e 2; *)
  apply hoare_assign with (fun s _ =>
    0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [u ]_ s /\ 0 <= [v ]_ s /\
    [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
    [A ]_ s * [x ]_ s * 2 + [B ]_ s * [y ]_ s  = [u ]_ s * 2 /\
    [C ]_ s * [x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
    Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
    (Zodd [x]_s \/ Zodd [y]_s) /\
    Zodd [v ]_ s /\
    eval_b (var_e B \% nat_e 2 \= nat_e 0) s).
  move=> s h /= [[H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]]]] H1].
  rewrite /wp_assign.
  repeat Store_upd.
  repeat (split=> //).
  case/andP : H1.
  move/ZIT.eqP; move/Zmod_2_Zeven; case/Zeven_ex=> a H1a.
  move/ZIT.eqP; move/Zmod_2_Zeven; case/Zeven_ex=> b H1b.
  by rewrite /= /ZIT.div H1a (mulZC 2) Z_div_mult_full //
    -H9 -(mulZC 2) mulZA -H1a.
  by case/andP : H1.
  (** B <- var_e B ./e nat_e 2 *)
  apply hoare_assign'.
  move=> s h /= [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]].
  rewrite /wp_assign.
  repeat Store_upd.
  repeat (split => //).
  move/ZIT.eqP : H14; move/Zmod_2_Zeven; case/Zeven_ex=> a H14.
  rewrite H14 in H9.
  ring_simplify in H9.
  rewrite -!mulZA -mulZDr in H9.
  rewrite /= /ZIT.div H14 (mulZC 2) Z_div_mult_full //.
  by eapply eqZ_mul2l; eauto.
  by right.
- (** A <- (var_e A +e var_e y) ./e nat_e 2; *) apply hoare_assign with (fun s _ =>
    0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [u ]_ s /\ 0 <= [v ]_ s /\
    [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
    [A ]_ s * [x ]_ s * 2 - [y]_s * [x]_s +  [B ]_ s * [y ]_ s  = [u ]_ s * 2 /\
    [C ]_ s * [x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
    Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
    (Zodd [x]_s \/ Zodd [y]_s) /\
    Zodd [v ]_ s /\
    (Zodd ([A]_s *2 - [y]_s) \/ Zodd ([B]_s))).
  move=> s h /= [[H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]]]] H1].
  rewrite /wp_assign; repeat Store_upd.
  repeat (split => //).
  + rewrite /= /ZIT.div /ZIT.add.
    rewrite negb_and in H1.
    case/orP : H1.
    * move/ZIT.eqP; move/not_Zmod_2_Zodd => H1.
      rewrite -H9.
      ring_simplify.
      congr (_ + _).
      rewrite -Z_div_exact_full_2 //; first ring.
      rewrite (mulZC _ 2) in H9.
      move/Zmult_2_Zeven : H9 => /Zeven_plus_inv.
      case; case => Y1 Y2.
      - case: H12 => H12.
        + move: (Zodd_mult_Zodd _ _ H1 H12); by move/Zeven_not_Zodd.
        + exact/Zeven_Zmod_2/Zodd_plus_Zodd.
      - apply Zeven_Zmod_2.
        case: H12 => H12.
        + case/Zodd_mult_inv : Y2 => Y2 Y3; exact: Zodd_plus_Zodd.
        + exact: Zodd_plus_Zodd.
    * move/ZIT.eqP. move/not_Zmod_2_Zodd => H1.
      rewrite -H9.
      ring_simplify.
      f_equal.
      rewrite -Z_div_exact_full_2 //; first ring.
      rewrite (mulZC _ 2) in H9.
      move/Zmult_2_Zeven : H9 => /Zeven_plus_inv.
      case; case=> Y1 Y2.
      - case: H12 => H12.
        + case/Zeven_mult_inv : Y1 => Y1; last by move/Zeven_not_Zodd : Y1.
          case/Zeven_mult_inv : Y2 => Y2; first by move/Zeven_not_Zodd : Y2.
          exact/Zeven_Zmod_2/Zeven_plus_Zeven.
        + move: (Zodd_mult_Zodd _ _ H1 H12).
          by move/Zodd_not_Zeven.
      - case: H12 => H12.
        + case/Zodd_mult_inv : Y1 => Y1 _.
          case/Zodd_mult_inv : Y2 => _ Y2'.
          exact/Zeven_Zmod_2/Zodd_plus_Zodd.
        + case/Zodd_mult_inv : Y1 => Y1 _.
          exact/Zeven_Zmod_2/Zodd_plus_Zodd.
  + rewrite negb_and in H1.
    rewrite /= /ZIT.div /ZIT.add.
    case/orP : H1.
    - move/ZIT.eqP/not_Zmod_2_Zodd => H1.
      case: H12 => H12.
      * case: (Zeven_odd_dec [B]_s) => X; auto.
        rewrite (mulZC _ 2) in H9.
        move/Zmult_2_Zeven : H9.
        case/Zeven_plus_inv.
        - case=> Y1 Y2.
          by move: (Zodd_mult_Zodd _ _ H1 H12) => /Zodd_not_Zeven.
        - case=> Y1.
          by case/Zodd_mult_inv => /Zodd_not_Zeven.
      * left.
        apply Zeven_plus_Zodd.
        - rewrite mulZC; exact: Zeven_2p.
        - exact: Zodd_opp.
    - move/ZIT.eqP; by move/not_Zmod_2_Zodd; auto.
(** B <- (var_e B .-e var_e x) ./e nat_e 2 *)
apply hoare_assign'.
move=> s h /= [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]].
rewrite /wp_assign; repeat Store_upd.
repeat (split => //).
2: by right.
rewrite /= /ZIT.sub /ZIT.div.
have {}H9 : ([B ]_ s - [x ]_ s) * [y ]_ s = [u ]_ s * 2 - [A ]_ s * [x ]_ s * 2.
  rewrite -H9; ring.
rewrite -mulZBl -(mulZC 2) in H9.
case: H12 => H12.
+ case: (Zeven_odd_dec [y]_s) => X.
  * case: H14 => H14.
    - move: (Zeven_plus_Zeven _ _ (Zeven_2p [A]_s) (Zeven_opp _ X)).
      by rewrite mulZC => /Zeven_not_Zodd.
    - have Y : Zeven ([B]_s - [x]_s).
        apply Zodd_plus_Zodd => //.
        exact: Zodd_opp.
      case/Zeven_ex : Y => b' Y.
      rewrite Y -mulZA in H9.
      apply eqZ_mul2l in H9 => //.
      rewrite Y (mulZC 2) Z_div_mult_full // H9; ring.
  * case: (Zeven_odd_dec ([B]_s - [x]_s)) => Y.
    - case/Zeven_ex : Y => b' Y.
      rewrite Y -mulZA in H9.
      apply eqZ_mul2l in H9 => //.
      rewrite Y (mulZC 2) Z_div_mult_full // H9; ring.
    - have : Zodd ( ([B ]_ s - [x ]_ s) * [y ]_ s ).
      apply Zodd_mult_Zodd => //.
      rewrite H9.
      move: (Zeven_2p (([u ]_ s - [A ]_ s * [x ]_ s))).
      by move/Zeven_not_Zodd.
+ case: (Zeven_odd_dec ([B]_s - [x]_s)) => Y.
  * case/Zeven_ex : Y => b' Y.
    rewrite Y -mulZA in H9.
    apply eqZ_mul2l in H9 => //.
    rewrite Y (mulZC 2) Z_div_mult_full // H9; ring.
  * have : Zodd ( ([B ]_ s - [x ]_ s) * [y ]_ s ) by apply Zodd_mult_Zodd.
    rewrite H9.
    move: (Zeven_2p (([u ]_ s - [A ]_ s * [x ]_ s))).
    by move/Zeven_not_Zodd.
Qed.

Lemma outer_loop_triple (g x y u v A B C D : nat) vx vy :
  uniq(g, x, y, u, v, A, B, C, D) -> 0 <= vx -> 0 <= vy ->
  {{ (fun s _ => 0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\
      0 <= [u ]_ s /\ 0 <= [v ]_ s /\
      [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
      [A ]_ s * [x ]_ s + [B ]_ s * [y ]_ s = [u ]_ s /\
      [C ]_ s * [x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
      Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
      (Zodd [u ]_ s \/ Zodd [v ]_ s) /\ (Zodd [x ]_ s \/ Zodd [y ]_ s))}}
    outer_loop u v x y A B C D
    {{ (fun s h => (0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\
     0 <= [u ]_ s /\ 0 <= [v ]_ s /\
     [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
     [A ]_ s * [x ]_ s + [B ]_ s * [y ]_ s = [u ]_ s /\
     [C ]_ s * [x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
     Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
     (Zodd [u ]_ s \/ Zodd [v ]_ s) /\ (Zodd [x ]_ s \/ Zodd [y ]_ s)) /\
    ~~ [ (var_e u \> nat_e 0) ]b_ s) }}.
Proof.
move=> Hset Hvx Hvy.
rewrite /outer_loop.
apply while.hoare_while.
(** while (var_e u mode nat_e 2 =e nat_e 0) *)
apply while.hoare_seq with (fun s _ =>
  0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [u ]_ s /\ 0 <= [v ]_ s /\
  [x ]_ s * [g ]_ s = vx /\
  [y ]_ s * [g ]_ s = vy /\
  [A ]_ s * [x ]_ s + [B ]_ s * [y ]_ s = [u ]_ s /\
  [C ]_ s * [x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
  Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
  (Zodd [x]_s \/ Zodd [y]_s) /\
  Zodd [u]_s).
eapply hoare_prop_m.hoare_stren; last first.
have Hset' : uniq(x, y, g, u, v, A, B, C, D).
  rewrite [Equality.sort _]/= in Hset *. by Uniq_uniq O.
exact: (inner_loop_triple x y g u v vx vy A B C D Hset').
move=> s h /= [[H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]]]]] H1]; by intuition.
apply hoare_prop_m.hoare_stren with (fun s _ =>
  (0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [v ]_ s /\ 0 <= [u ]_ s /\
    [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
    [C ]_ s * [x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
    [A ]_ s * [x ]_ s + [B ]_ s * [y ]_ s = [u ]_ s /\
    Z.gcd vx vy = [g ]_ s * Z.gcd [v ]_ s [u ]_ s) /\
  (Zodd [x]_s \/ Zodd [y]_s) /\
  (Zodd [v]_s \/ Zodd [u]_s)).
move=> s h /=.
rewrite (Zgcd_sym [u]_s); by intuition.
have {Hset}Hset' : uniq(x, y, g, v, u, C, D, A, B).
  rewrite [Equality.sort _]/= in Hset *; by Uniq_uniq O.
move: (inner_loop_triple x y g v u vx vy C D A B Hset') => Hi.
eapply while.hoare_seq.
eapply hoare_prop_m.hoare_stren; last exact: Hi.
move=> s h /=; by intuition.
apply while.hoare_ifte.
- (** u <- var_e u .-e var_e v; *)
  apply hoare_assign with (fun s _ =>
    0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [v ]_ s /\ 0 <= [u ]_ s /\
    [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
    ([A ]_ s - [C]_s)* [x ]_ s + ([B ]_ s - [D]_s)* [y ]_ s = [u ]_ s /\
    [C ]_ s * [x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
    Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
    (Zodd [x]_s \/ Zodd [y]_s) /\
    (Zodd [v]_s \/ Zodd [u]_s)).
  move=> s h /= [[H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]] H2].
  rewrite /wp_assign; repeat Store_upd => //.
  repeat (split => //).
  move/geZP in H2.
  rewrite /=; omegab.
  rewrite /= /ZIT.sub -H10 -H11; ring.
  by rewrite /= /ZIT.sub (Zgcd_for_euclid _ _ (-1)) (Zgcd_sym [u]_s).
  rewrite /= /ZIT.sub.
  case: (Zeven_odd_dec [v]_s) => ?; by auto.
  (** A <- var_e A .-e var_e C; *)
  apply hoare_assign with (fun s _ =>
    (0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [v ]_ s /\ 0 <= [u ]_ s /\
      [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
      ([A ]_ s)* [x ]_ s + ([B ]_ s - [D]_s)* [y ]_ s = [u ]_ s /\
      [C ]_ s * [x ]_ s + [D ]_ s * [y ]_ s = [v ]_ s /\
      Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s  /\
      (Zodd [x]_s \/ Zodd [y]_s) /\
      (Zodd [v ]_ s \/ Zodd [u ]_ s))).
  move=> s h /= [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]]]]].
  by rewrite /wp_assign; repeat Store_upd.
  (** B <- var_e B .-e var_e D *)
  apply hoare_assign'.
  move=> s h /= [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]].
  rewrite /wp_assign; repeat Store_upd => //.
  tauto.
- (** v <- var_e v .-e var_e u; *)
  apply hoare_assign with (fun s _ =>
      0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [v ]_ s /\ 0 <= [u ]_ s /\
      [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
      [A ]_ s * [x ]_ s + [B ]_ s * [y ]_ s = [u ]_ s /\
      ([C ]_ s - [A]_s) * [x ]_ s + ([D ]_ s - [B]_s) * [y ]_ s = [v ]_ s /\
      Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
      (Zodd [x]_s \/ Zodd [y]_s) /\
      (Zodd [v ]_ s \/ Zodd [u ]_ s)).
  move=> s h /= [[H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]] H2].
  rewrite /wp_assign; repeat Store_upd => //.
  repeat (split => //).
  move/negbTE : H2 => /geZP H2.
  rewrite /=; omegab.
  rewrite /= /ZIT.sub -H10 -H11; ring.
  by rewrite /= /ZIT.sub (Zgcd_sym [u]_s) (Zgcd_for_euclid _ _ (-1)).
  case: (Zeven_odd_dec [u]_s) => Htmp; last by right.
  left; apply Zodd_plus_Zeven => //.
  by destruct ([u]_s).
  (** C <- var_e C .-e var_e A; *)
  apply hoare_assign with (fun s _ =>
    0 <= [x ]_ s /\ 0 <= [y ]_ s /\ 0 <= [g ]_ s /\ 0 <= [v ]_ s /\ 0 <= [u ]_ s /\
    [x ]_ s * [g ]_ s = vx /\ [y ]_ s * [g ]_ s = vy /\
    [A ]_ s * [x ]_ s + [B ]_ s * [y ]_ s = [u ]_ s /\
    [C ]_ s * [x ]_ s + ([D ]_ s - [B]_s) * [y ]_ s = [v ]_ s /\
    Z.gcd vx vy = [g ]_ s * Z.gcd [u ]_ s [v ]_ s /\
    (Zodd [x]_s \/ Zodd [y]_s) /\
    (Zodd [v ]_ s \/ Zodd [u ]_ s)).
  move=> s h /= [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]]]].
  by rewrite /wp_assign; repeat Store_upd.
  (** D <- var_e D .-e var_e B *)
  apply hoare_assign' => s h /= [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]].
  rewrite /wp_assign; repeat Store_upd => //; by intuition.
Qed.

Lemma begcd_triple (g x y u v A B C D : nat) :
  uniq(g, x, y, u, v, A, B, C, D) ->
  forall vx vy, 0 <= vx -> 0 <= vy ->
  {{ fun s h => [x]_s = vx /\ [y]_s = vy }}
  begcd g x y u v A B C D
  {{ fun s h => [C]_s * vx + [D]_s * vy = [g]_s * [v]_s /\
    Zis_gcd vx vy ([g]_s * [v]_s)}}.
Proof.
move=> Hset vx vy Hvx Hvy.
rewrite /begcd.
(** g <- nat_e 1 ; *)
apply hoare_assign with (fun s h => [x]_s = vx /\ [y]_s = vy /\ [g]_s = 1).
move=> s h [Hx Hy].
by rewrite /wp_assign; repeat Store_upd => //.
(** prelude x y g ; *)
apply while.hoare_seq with (fun s _ =>
  0 <= [x]_s /\ 0 <= [y]_s /\ 0 <= [g]_s /\
  [x]_ s * [g]_s = vx /\ [y]_s * [g]_s = vy /\
  Z.gcd vx vy = [g]_s * Z.gcd ([x]_s) ([y]_s) /\
  ~ [ var_e x \% nat_e 2 \= nat_e O \&& var_e y \% nat_e 2 \= nat_e O ]b_ s).
have Hset' : uniq(x, y, g).
  rewrite [Equality.sort _]/= in Hset *; by Uniq_uniq O.
eapply while.hoare_conseq; last exact: (BGCD_HAC.prelude_triple _ _ _ _ _ Hset' Hvx Hvy).
- move=> s h /= [H1 [H2 [H3 [x_g [y_g H6]]]]].
  repeat (split; first by []).
  split; last by move/negP: H6.
  rewrite -x_g -y_g.
  apply Zis_gcd_gcd; last first.
    rewrite (mulZC [x]_s) (mulZC [y]_s); exact/Zis_gcd_mult/Zgcd_is_gcd.
  apply mulZ_ge0 => //; exact: Zgcd_is_pos.
- move=> s h /= [-> [-> ->]]; by rewrite 2!mulZ1.
(** u <- var_e x ; *)
apply hoare_assign with (fun s _ =>
  0 <= [x]_s /\ 0 <= [y]_s /\ 0 <= [g]_s /\
  [x]_ s * [g]_s = vx /\ [y]_s * [g]_s = vy /\
  Z.gcd vx vy = [g]_s * Z.gcd ([x]_s) ([y]_s) /\
  ~ [ var_e x \% nat_e 2 \= nat_e O \&& var_e y \% nat_e 2 \= nat_e O ]b_ s /\
  [u]_s = [x]_s).
move=> s h /= [H1 [H2 [H3 [Hxg [Hyg [H4 H5]]]]]]; by rewrite /wp_assign; repeat Store_upd.
(** v <- var_e y ; *)
apply hoare_assign with (fun s _ =>
  0 <= [x]_s /\ 0 <= [y]_s /\ 0 <= [g]_s /\
  [x]_ s * [g]_s = vx /\ [y]_s * [g]_s = vy /\
  Z.gcd vx vy = [g]_s * Z.gcd ([x]_s) ([y]_s) /\
  ~ [ var_e x \% nat_e 2 \= nat_e O \&& var_e y \% nat_e 2 \= nat_e O ]b_ s /\
  [u]_s = [x]_s /\ [v]_s = [y]_s).
move=> s h /= [H1 [H2 [H3 [Hxg [Hyg [H4 [H5 Hu]]]]]]]; by rewrite /wp_assign; repeat Store_upd.
(** A <- nat_e 1 ; *)
apply hoare_assign with (fun s _ =>
  0 <= [x]_s /\ 0 <= [y]_s /\ 0 <= [g]_s /\
  [x]_ s * [g]_s = vx /\ [y]_s * [g]_s = vy /\
  Z.gcd vx vy = [g]_s * Z.gcd ([x]_s) ([y]_s) /\
  ~ [ var_e x \% nat_e 2 \= nat_e O \&& var_e y \% nat_e 2 \= nat_e O ]b_ s /\
  [u]_s = [x]_s /\ [v]_s = [y]_s /\ [A]_s = 1).
move=> s h /= [H1 [H2 [H3 [Hxg [Hyg [H4 [H5 [Hu Hv]]]]]]]]; by rewrite /wp_assign; repeat Store_upd.
(** B <- nat_e O ; *)
apply hoare_assign with (fun s _ =>
  0 <= [x]_s /\ 0 <= [y]_s /\ 0 <= [g]_s /\
  [x]_ s * [g]_s = vx /\ [y]_s * [g]_s = vy /\
  Z.gcd vx vy = [g]_s * Z.gcd ([x]_s) ([y]_s) /\
  ~ [ var_e x \% nat_e 2 \= nat_e O \&& var_e y \% nat_e 2 \= nat_e O ]b_ s /\
  [u]_s = [x]_s /\ [v]_s = [y]_s /\ [A]_s = 1 /\ [B]_s = 0).
move=> s h /= [H1 [H2 [H3 [Hxg [Hyg [H4 [H5 [Hu [Hv HA]]]]]]]]]; by rewrite /wp_assign; repeat Store_upd.
(** C <- nat_e O ; *)
apply hoare_assign with (fun s _ =>
  0 <= [x]_s /\ 0 <= [y]_s /\ 0 <= [g]_s /\
  [x]_ s * [g]_s = vx /\ [y]_s * [g]_s = vy /\
  Z.gcd vx vy = [g]_s * Z.gcd ([x]_s) ([y]_s) /\
  ~ [ var_e x \% nat_e 2 \= nat_e O \&& var_e y \% nat_e 2 \= nat_e O ]b_ s /\
  [u]_s = [x]_s /\ [v]_s = [y]_s /\ [A]_s = 1 /\ [B]_s = 0 /\ [C]_s = 0).
move=> s h /= [H1 [H2 [H3 [Hxg [Hyg [H4 [H5 [Hu [Hv [HA HB]]]]]]]]]]; by rewrite /wp_assign; repeat Store_upd.
(** D <- nat_e 1 ; *)
apply hoare_assign with (fun s _ =>
  0 <= [x]_s /\ 0 <= [y]_s /\ 0 <= [g]_s /\
  [x]_ s * [g]_s = vx /\ [y]_s * [g]_s = vy /\
  Z.gcd vx vy = [g]_s * Z.gcd ([x]_s) ([y]_s) /\
  ~ [ var_e x \% nat_e 2 \= nat_e O \&& var_e y \% nat_e 2 \= nat_e O ]b_ s /\
  [u]_s = [x]_s /\ [v]_s = [y]_s /\ [A]_s = 1 /\ [B]_s = 0 /\ [C]_s = 0 /\ [D]_s = 1).
move=> s h /= [H1 [H2 [H3 [Hxg [Hyg [H4 [H5 [Hu [Hv [HA [HB HC]]]]]]]]]]]; by rewrite /wp_assign; repeat Store_upd.
(** outer_loop *)
eapply while.hoare_conseq; last exact: (outer_loop_triple g x y u v A B C D vx vy Hset Hvx Hvy).
- move=> s h /= [[Hx [Hy [Hg [Hu_pos [Hv_pos [Hxg [Hyg [HAB [HCD [Hgcd Hparity]]]]]]]]]] Heq].
  have {}Heq : [u]_s = 0.
    move: Heq.
    rewrite -ZIT.gebNgt => /ZIT.geP.
    rewrite /ZIT.ge => ?; omega.
  rewrite Heq /= Z.abs_eq // in Hgcd.
  split; [rewrite -Hxg -Hyg -HCD; ring | rewrite -Hgcd; exact: Zgcd_is_gcd].
- move=> s h /= [Hx [Hy [Hg [Hxg [Hyg [Hgcd [Hcond [Hu [Hv [HA [HB [HC HD]]]]]]]]]]]].
  rewrite HA HB HC HD 2!mul1Z 2!mul0Z addZ0 add0Z Hu Hv.
  move/negP : Hcond.
  rewrite negb_and.
  case/orP; move/ZIT.eqP; move/not_Zmod_2_Zodd; by intuition.
Qed.

End BEGCD_HAC.

Definition uivi_init u v u1 u2 u3 v1 v2 v3 s :=
  [u1]_s = 1 /\ [u2]_s = 0 /\[u3]_s = [u]_s /\
  [v1]_s = [v]_s /\ [v2]_s = 1 - [u]_s /\ [v3]_s = [v]_s.

Definition ti_init u v t1 t2 t3 s :=
  (Zodd [u]_s -> [t1]_s = 0 /\ [t2]_s = -1 /\ [t3]_s = -[v]_s) /\
  (Zeven [u]_s -> [t1]_s = 1 /\ [t2]_s = 0 /\ [t3]_s = [u]_s).

Definition uv_init vu vv u v st := [u]_ st = vu /\ [v]_ st = vv.

Definition C1 vu vv u v g s := uv_init vu vv u v s /\ [g]_s = 1.

Definition C2 vu vv u v g s := 0 < [u]_s /\ 0 < [v]_s /\ 0 < [g]_s /\
  [u]_ s * [g]_s = vu /\ [v]_s * [g]_s = vv.

Definition C3 vu vv u v g s :=
  Z.gcd vu vv = [g]_s * Z.gcd [u]_s [v]_s /\
  ~ [ var_e u \% nat_e 2 \= nat_e O \&& var_e v \% nat_e 2 \= nat_e O ]b_ s.

Definition C4 u3 v3 t3 s := exists k, ([t3]_s * 2 ^^ k = - [v3]_s  /\ Zodd [u3]_s) \/
  ([t3]_s * 2 ^^ k = [u3]_s /\ Zodd [v3]_s) \/
  ([t3]_s * 2 ^^ k = ([u3]_s - [v3]_s) /\ (Zodd [v3]_s \/ Zodd [u3]_s)).

Definition C5 u3 v3 s := 0 < [u3]_s /\ 0 < [v3]_s.

Definition CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s :=
  [u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
  [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
  [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s.

(** binary extended gcd algorithm from The Art of Computer Programming *)

Module BEGCD_TAOCP.

Definition init u v u1 u2 u3 v1 v2 v3 t1 t2 t3 :=
  (u1 <- nat_e 1 ;
  u2 <- nat_e 0 ;
  u3 <- var_e u ;
  v1 <- var_e v ;
  v2 <- nat_e 1 \- var_e u ;
  v3 <- var_e v) ;
  If var_e u \% nat_e 2 \= nat_e 1 Then
    t1 <- nat_e 0 ;
    t2 <- cst_e (-1) ;
    t3 <- .--e var_e v
  Else
    (t1 <- nat_e 1 ;
    t2 <- nat_e 0 ;
    t3 <- var_e u).

Definition halve u v t1 t2 t3 :=
  If var_e t1 \% nat_e 2 \= nat_e 0 \&& var_e t2 \% nat_e 2 \= nat_e 0 Then
    t1 <- var_e t1 ./e nat_e 2 ;
    t2 <- var_e t2 ./e nat_e 2 ;
    t3 <- var_e t3 ./e nat_e 2
  Else
    (t1 <- (var_e t1 \+ var_e v) ./e nat_e 2 ;
     t2 <- (var_e t2 \- var_e u) ./e nat_e 2 ;
     t3 <- var_e t3 ./e nat_e 2).

Definition reset u v u1 u2 u3 v1 v2 v3 t1 t2 t3 :=
  If var_e t3 \>= nat_e 0 Then
    u1 <- var_e t1 ;
    u2 <- var_e t2 ;
    u3 <- var_e t3
  Else
    v1 <- var_e v \- var_e t1 ;
    v2 <- .--e (var_e u \+ var_e t2) ;
    v3 <- .--e var_e t3.

Definition subtract u v u1 u2 u3 v1 v2 v3 t1 t2 t3 :=
  (t1 <- var_e u1 \- var_e v1 ;
   t2 <- var_e u2 \- var_e v2 ;
   t3 <- var_e u3 \- var_e v3) ;
  If nat_e 0 \>= var_e t1 Then
    t1 <- var_e t1 \+ var_e v ;
    t2 <- var_e t2 \- var_e u
  Else
    skip.

Definition begcd g u v u1 u2 u3 v1 v2 v3 t1 t2 t3 :=
  g <- nat_e 1 ;
  prelude u v g ;
  init u v u1 u2 u3 v1 v2 v3 t1 t2 t3 ;
  While var_e t3 \!= nat_e 0 {{
    While var_e t3 \% nat_e 2 \= nat_e O {{
      halve u v t1 t2 t3 }} ;
    reset u v u1 u2 u3 v1 v2 v3 t1 t2 t3 ;
    subtract u v u1 u2 u3 v1 v2 v3 t1 t2 t3 }}.

End BEGCD_TAOCP.

(** Functional correctness only *)

Module BEGCD_TAOCP_FUN_COR.

Import BEGCD_TAOCP.

Section begcd_taocp_fun_cor.

Variables g u v u1 u2 u3 v1 v2 v3 t1 t2 t3 : nat.
Variables vv vu : Z.

Lemma triple_intermediate :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) -> 0 < vu -> 0 < vv ->
  {{ fun s _ => C2 vu vv u v g s /\
    C3 vu vv u v g s /\
    uivi_init u v u1 u2 u3 v1 v2 v3 s /\
    ti_init u v t1 t2 t3 s }}
  While var_e t3 \!= nat_e 0 {{
  (While var_e t3 \% nat_e 2 \= nat_e 0 {{ halve u v t1 t2 t3 }};
    reset u v u1 u2 u3 v1 v2 v3 t1 t2 t3;
    subtract u v u1 u2 u3 v1 v2 v3 t1 t2 t3) }}
  {{ fun s _ => vu * [u1 ]_ s + vv * [u2 ]_ s = [g ]_ s * [u3 ]_ s /\
    Z.gcd vu vv = [g ]_ s * [u3 ]_ s }}.
Proof.
move=> Hset Hvv Hvu.
(** while.while (var_e t3 <>e nat_e 0) *)
apply hoare_prop_m.hoare_while_invariant with (fun s _ =>
  C2 vu vv u v g s /\
  (Zodd [u]_s \/ Zodd [v]_s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u]_s [v]_s = Z.gcd [u3]_s [v3]_s).
rewrite /while.entails => s h.
case => [[Hu [Hv [Hg [u_g v_g]]] [[Hgcd Hcond] [[Hu1 [Hu2 [Hu3 [Hv1 [Hv2 Hv3]]]]]]]] Ht].
rewrite /CVectors Hu1 Hu2 Hu3 Hv1 Hv2 Hv3.
repeat (split; first tauto).
case: (Zeven_odd_dec [u]_s) => u_parity.
- case: Ht => _.
  move/(_ u_parity) => [Ht1 [Ht2 Ht3]].
  rewrite /C2 /C4 /C5 Ht1 Ht2 Ht3 Hu3 Hv3 mulZ1 mulZ0 addZ0.
  split; first by [].
  split.
    move/negP : Hcond => /=.
    rewrite negb_and /ZIT.eqb /ZIT.rem /=.
    case/orP; move/eqP => X.
    + left; exact: not_Zmod_2_Zodd.
    + right; exact: not_Zmod_2_Zodd.
  split.
    repeat (split; first tauto).
    ring.
  split; last by [].
  exists O; rewrite [_ ^^ _]/= !mulZ1; right; left.
  split; first by reflexivity.
  move/negP : Hcond => /=.
  rewrite negb_and /ZIT.eqb /ZIT.rem.
  case/orP; move/eqP.
  + move/not_Zmod_2_Zodd; by move/Zodd_not_Zeven.
  + by move/not_Zmod_2_Zodd.
- case: Ht.
  move/(_ u_parity) => [Ht1 [Ht2 Ht3]] _.
  rewrite /C2 /C4 /C5 Ht1 Ht2 Ht3 Hu3 Hv3 mulZ1 mulZ0 add0Z mulZ0 addZ0.
  split; first by [].
  split.
    move/negP : Hcond => /=.
    rewrite negb_and /ZIT.eqb /ZIT.rem /=.
    case/orP; move/eqP => X.
    * left; exact: not_Zmod_2_Zodd.
    * right; exact: not_Zmod_2_Zodd.
  split.
    split; first by ring.
    split; by [ | ring].
  split; last by [].
  exists O; rewrite [_ ^^ _]/= !mulZ1; tauto.
- rewrite /while.entails => s h.
  case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [[Hu3 Hv3] H14]]]]] H1].
  split; first by rewrite -u_g -v_g -Hui; ring.
  rewrite /hoare_m.eval_b /= /ZIT.eqb in H1.
  move/negPn/eqP in H1.
  case: H10 => k [H10|[H10 | H10]].
  + have abs : [v3 ]_ s = 0.
      move: (expZ_gt0 k) => X.
      case: H10 => H10 H10'.
      rewrite H1 mul0Z in H10; omega.
    rewrite abs Zgcd_0 geZ0_norm in H14; last omega.
    rewrite -H14 -Zgcd_mult; last omega.
    by rewrite mulZC u_g mulZC v_g.
  + have abs : [u ]_ s = 0 by rewrite H1 mul0Z in H10; omega.
    rewrite abs in Hu; by apply ltZZ in Hu.
  + have abs : [u3 ]_ s = [v3 ]_ s.
      rewrite H1 mul0Z in H10; omega.
    rewrite -abs Zgcd_same in H14; last omega.
    rewrite -H14 -u_g -v_g -Zgcd_mult; last omega.
    by rewrite (mulZC [u ]_ s) (mulZC [v ]_ s).

apply while.hoare_seq with (fun s h =>
  C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\
  Zodd [t3]_s ).

rewrite /halve.
apply hoare_prop_m.hoare_while_invariant with (fun s h =>
  C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  [t3]_s <> 0).

move=> s h /=.
case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [[Hu3 Hv3] H14]]]]] H1].
repeat (split => //).
by move/eqP : H1.

move=> s h /=.
case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [[Hu3 Hv3] [H14 H15]]]]]] H1].
repeat (split; first by []).
split.
  rewrite /C2 -u_g -v_g -H14 -Zgcd_mult; last omega.
  f_equal; by rewrite mulZC.
rewrite /hoare_m.eval_b /= /ZIT.eqb /ZIT.rem in H1.
by move/eqP/not_Zmod_2_Zodd : H1.

apply while.hoare_ifte.
- apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * 2 * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  [t3 ]_ s <> 0 /\
  Zeven [t3]_s /\
  Zeven [t2]_s).
  move=> s h /=.
  case => [[[[Hu [Hv [Hg [u_g v_g]]]] [H7 [[Hti [Hui Hvi]] [H11 [[Hu3 Hv3] [H14 H16]]]]]] H3] H1].
  rewrite /wp_assign /C2 /C4 /C5.
  repeat Store_upd.
  repeat (split; first tauto).
  split.
    rewrite -mulZA div_e_exact_full_2 //.
    rewrite /hoare_m.eval_b /= in H1.
    case/andP : H1 => H1 _.
    rewrite /ZIT.eqb /ZIT.rem /= in H1.
    by move/eqP : H1.
  repeat (split; first by []).
  rewrite /hoare_m.eval_b /= /ZIT.eqb /ZIT.rem /= in H1, H3.
  move/eqP in H3.
  case/andP : H1 => _ /eqP H1.
  split; exact: Zmod_2_Zeven.

apply hoare_assign with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * 2 * [t1 ]_ s + [v ]_ s * 2 * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  [t3 ]_ s <> 0 /\ Zeven [t3 ]_ s ).

move=> s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [[Hu3 Hv3] [H12 [H13 [H14 H16]]]]]]]].
rewrite /wp_assign /C2 /C4 /C5.
repeat Store_upd.
repeat (split; first tauto).
split; last by [].
rewrite -(mulZA [v]_s) div_e_exact_full_2 //; exact: Zeven_Zmod_2.

apply hoare_assign' => s h.
case => [[Hu [Hv [Hg [u_g v_g]]] [H5 [[Hti [Hui Hvi] [H9 [[Hu3 Hv3] [H15 [H16 H17]]]]]]]]].
rewrite /wp_assign /C2 /C4 /C5 /CVectors.
repeat Store_upd.
repeat (split; first tauto).
split.
  rewrite /= -Hti /ZIT.div.
  set tmp := _ + [v]_s * 2 * _ .
  have -> : tmp = ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s) * 2 by rewrite /tmp; ring.
  by rewrite Z_div_mult_full.
repeat (split; first by []).
split.
  case/Zeven_ex : H17 => m H17.
  rewrite [eval _ _]/= H17 (mulZC 2) /ZIT.div Z_div_mult_full //.
  case: H9 => k [ [H9 H9'] | ].
  + exists (S k); left.
    by rewrite ZpowerS mulZA -(mulZC 2) -H17.
  + case ; exists k.+1; right.
    * left; by rewrite ZpowerS mulZA -(mulZC 2) -H17.
    * right; by rewrite ZpowerS mulZA -(mulZC 2) -H17.
repeat (split; first by []).
case/Zeven_ex : H17 => m H17.
rewrite /= H17 (mulZC 2) /ZIT.div Z_div_mult_full //; omega.

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * (2 * [t1 ]_ s  - [v]_s) + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  [t3 ]_ s <> 0 /\ Zeven [t3]_s /\
  (Zodd (2 * [t1]_s - [v]_s) \/ Zodd [t2]_s)).

move=> s h.
case => [[[[Hu [Hv [Hg [u_g v_g]]]] [H7 [[Hti [Hui Hvi]] [H11 [[Hu3 Hv3] [H14 H16]]]]]] H3] H1].
rewrite /wp_assign /C2 /C4 /C5.
repeat Store_upd.
rewrite /hoare_m.eval_b /= /ZIT.eqb /ZIT.rem in H1 H3.
rewrite negb_and in H1.

have t1_v : [var_e t1 \+ var_e v ]e_ s mod 2 = 0.
  rewrite /= /ZIT.add.
  case/orP: H1; move/eqP => H1.
  - apply Zeven_Zmod_2, Zodd_plus_Zodd.
    exact: not_Zmod_2_Zodd.
    case: H7 => H7; last by exact H7.
    move/eqP/Zmod_2_Zeven : H3.
    rewrite -Hti.
    case/Zeven_plus_inv.
    + case=> H31 H32.
      have : Zodd ([u ]_ s * [t1 ]_ s).
        apply Zodd_mult_Zodd => //; exact: not_Zmod_2_Zodd.
      by move/Zodd_not_Zeven.
    + case => _.
      by case/Zodd_mult_inv=> ? _.
  - case: H7 => H7.
    + move/eqP/Zmod_2_Zeven : H3.
      rewrite -Hti.
      case/Zeven_plus_inv => [[u_t1 v_t2]|[]].
      * case/Zeven_mult_inv : v_t2 => v_t2.
        - case/Zeven_mult_inv : u_t1 => u_t1.
          + by move/Zodd_not_Zeven : H7.
          + exact/Zeven_Zmod_2/Zeven_plus_Zeven.
        - move/not_Zmod_2_Zodd : H1.
          by move/Zodd_not_Zeven.
      * case/Zodd_mult_inv=> _ odd_t1.
        case/Zodd_mult_inv=> odd_v _.
        exact/Zeven_Zmod_2/Zodd_plus_Zodd.
    + move/eqP/Zmod_2_Zeven : H3.
      rewrite -Hti.
      case/Zeven_plus_inv => [[u_t1 v_t2]| []].
      * have : Zodd ([v ]_ s * [t2 ]_ s).
          apply Zodd_mult_Zodd => //; exact: not_Zmod_2_Zodd.
        by move/Zodd_not_Zeven.
      * case/Zodd_mult_inv=> _ odd_t1 _.
        exact/Zeven_Zmod_2/Zodd_plus_Zodd.

split; first by [].
repeat (split; first by []).
split.
  split; by [rewrite div_e_exact_full_2 //= /ZIT.add -Hti; ring | ].
repeat (split; first by []).
split; first exact/Zmod_2_Zeven/eqP.
case/orP : H1 => H1.
- left.
  rewrite div_e_exact_full_2 //.
  move/eqP/not_Zmod_2_Zodd : H1.
  suff : [var_e t1 \+ var_e v ]e_ s - [v ]_ s = [t1]_s by move=> ->.
  rewrite /= /ZIT.add; ring.
- right.
  by move/eqP/not_Zmod_2_Zodd : H1.

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * (2 * [t1 ]_ s  - [v]_s) + [v ]_ s * (2 * [t2 ]_ s + [u]_s) = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  [t3 ]_ s <> 0 /\ Zeven [t3]_s).

move=> s h H.
rewrite (mulZC 2) /= -(mulZC 2) in H.
case: H => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [[Hu3 Hv3] [H12 [H13 [H14 H16]]]]]]]].
rewrite /C2 /wp_assign /C4 /C5.
repeat Store_upd.
have t2_u : [var_e t2 \- var_e u ]e_ s mod 2 = 0.
  apply Zeven_Zmod_2.
  case: H5 => [odd_u | odd_v].
  - case: H16 => H16.
    + move: H14.
      rewrite -Hti.
      case/Zeven_plus_inv.
      * case.
        case/Zeven_mult_inv; by move/Zeven_not_Zodd.
      * case.
        case/Zodd_mult_inv=> K1 _.
        case/Zodd_mult_inv=> _ K4.
        apply Zodd_plus_Zodd => //; exact: Zodd_opp.
    + apply Zodd_plus_Zodd => //; exact: Zodd_opp.
  - case: H16 => H16.
    + move: H14.
      rewrite -Hti.
      case/Zeven_plus_inv.
      * case.
        case/Zeven_mult_inv => [u_even | ].
        - case/Zeven_mult_inv => [ | even_t2].
          by move/Zeven_not_Zodd.
          apply Zeven_plus_Zeven => //; exact: Zeven_opp.
        - by move/Zeven_not_Zodd.
      * case.
        case/Zodd_mult_inv=> odd_u _.
        case/Zodd_mult_inv=> _ odd_t2.
        apply Zodd_plus_Zodd => //; exact: Zodd_opp.
    + move: H14.
      rewrite -Hti.
      case/Zeven_plus_inv.
      * case.
        case/Zeven_mult_inv => [u_even | _]; case/Zeven_mult_inv; by move/Zeven_not_Zodd.
      * case.
        case/Zodd_mult_inv=> odd_u _ _.
        apply Zodd_plus_Zodd => //; exact: Zodd_opp.

repeat (split; first by []).
split; last by [].
split; by [rewrite div_e_exact_full_2 // /ZIT.add -Hti (mulZC 2) /= /ZIT.sub; ring | ].

apply hoare_assign' => s h H.
rewrite !(mulZC 2) in H.
case: H => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [[Hu3 Hv3] [H12 [H13 H15]]]]]]].
rewrite /C2 /wp_assign /C4 /C5 /CVectors.
repeat Store_upd.
repeat (split; first tauto).
split.
  rewrite /= -Hti /ZIT.div.
  have : ([u ]_ s * ([t1 ]_ s * 2 - [v ]_ s) + [v ]_ s * ([t2 ]_ s * 2 + [u ]_ s)) =
    ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s) * 2 by ring.
  move=> ->; by rewrite Z_div_mult_full.
repeat (split; first by []).
split.
  case/Zeven_ex : H15 => m H15.
  rewrite [eval _ _]/= H15 (mulZC 2) /ZIT.div Z_div_mult_full //.
  case: H9 => k [[H9 H9']|].
  - exists (S k); left.
    by rewrite ZpowerS mulZA -(mulZC 2) -H15.
  - case=> H9; exists (S k); right.
    + left; by rewrite ZpowerS mulZA -(mulZC 2) -H15.
    + right; by rewrite ZpowerS mulZA -(mulZC 2) -H15.
repeat (split; first by []).
case/Zeven_ex : H15 => m H15 /=.
rewrite H15 mulZC /ZIT.div Z_div_mult_full //; omega.

apply while.hoare_seq with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  (0 <= [t3]_s -> Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\ Zodd [u3]_s /\
    [u3]_s = [t3]_s ) /\
  ([t3]_s < 0 -> Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [t3 ]_ s /\ Zodd [v3]_s /\
    [v3]_s = - [t3]_s ) /\
  C5 u3 v3 s).

rewrite /reset.
apply while.hoare_ifte.

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\ Zodd [t3 ]_ s /\
  C5 u3 v3 s /\
  0 < [t3]_s).

move=> s h /=.
case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [[Hu3 Hv3] [H13 H15]]]]]] H1].
rewrite /wp_assign /C2 /C4 /C5.
repeat Store_upd.
rewrite /hoare_m.eval_b /= /ZIT.geb in H1.
move/geZP in H1.
repeat (split; first tauto).
move/Z.ge_le : H1.
case/leZ_eqVlt => H1 //.
by rewrite -H1 in H15.

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\
  Zodd [t3 ]_ s /\ C5 u3 v3 s /\ 0 < [t3 ]_ s).

move=> s h /= H.
rewrite /wp_assign /C2 /C4 /C5.
repeat Store_upd.
tauto.

apply hoare_assign' => s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [H11 [[Hu3 Hv3] H15]]]]]]].
rewrite /wp_assign /C2 /C4 /C5 /CVectors.
repeat Store_upd.
repeat (split; first tauto).
split.
  move=> Ht3.
  case: H9 => k [ [H9 H9'] | [ [H9 H9'] | [H9 H9']]].
  - exfalso.
    have abs : -[v3]_s < 0 by omega.
    rewrite -H9 in abs.
    move/Zlt_not_le : abs.
    apply.
    apply mulZ_ge0 => //; exact: expZ_ge0.
  - rewrite -H9 in H10.
    by rewrite Zgcd_Zpower_odd // in H10.
  - have Htmp : [u3 ]_ s = [t3 ]_ s * 2 ^^ k + [v3 ]_ s by omega.
    rewrite Htmp in H10.
    move: (Zgcd_for_euclid ([t3 ]_ s * 2 ^^ k) [v3 ]_ s 1) => X.
    rewrite mul1Z in X.
    rewrite {}X in H10.
    destruct k as [|k].
    - by rewrite /= mulZ1 in H10.
    - case: H9' => // H9'.
      by rewrite Zgcd_Zpower_odd // in H10.
      rewrite Zgcd_Zpower_odd // in H10.
      have -> : [v3 ]_ s = [u3 ]_ s - [t3 ]_ s * 2 ^^ S k by omega.
      apply Zodd_plus_Zeven => //.
      exact/Zeven_opp/Zeven_mult_Zeven_r/Zeven_power.
split; last by [].
move=> Ht3.
exfalso.
omega.

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1]_s + [v]_s * (- [u]_s - [t2]_s ) = - [t3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\ Zodd [t3 ]_ s /\
  [t3]_s < 0).

move=> s h /= H.
case : H => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [[Hu3 Hv3] [H13 H15]]]]]] H1].
rewrite /wp_assign /C2 /C4 /C5.
repeat Store_upd.
repeat (split; first by []).
split.
  split; first by rewrite -Hti /= /ZIT.sub; ring.
  split; by [ | rewrite -Hti /= /ZIT.sub; ring].
repeat (split; first by []).
rewrite /hoare_m.eval_b /= /ZIT.geb in H1.
move/geZP : H1 => ?; omega.

apply hoare_assign with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1]_s + [v]_s * [v2]_s = - [t3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\
  Zodd [t3 ]_ s /\ [t3 ]_ s < 0).
move=> s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [H11 [H12 [H13 H15]]]]]]].
rewrite /wp_assign /C2 /C4 /C5.
repeat Store_upd.
repeat (split => //).
rewrite /= /ZIT.add -Hvi; ring.

apply hoare_assign' => s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [[Hu3 Hv3] [H13 [H15 H16]]]]]]].
rewrite /wp_assign /C2 /C4 /C5 /CVectors.
repeat Store_upd.
split; first by [].
repeat (split; first by []).
rewrite /=.
split; first by move/Zle_not_lt.
split; last omega.
move=> _.
  rewrite /=.
  case: H10 => k [ [H10 H10'] | [ [H10 H10'] | [H10 H10'] ] ].
  - have X : [v3 ]_ s = - ([t3 ]_ s * 2 ^^ k) by omega.
    rewrite {}X Zgcd_opp in H13.
    symmetry in H13.
    rewrite Zgcd_sym Zgcd_Zpower_odd // in H13.
    split; first by symmetry; rewrite Zgcd_sym.
    split; by [ apply Zodd_opp | ].
  - rewrite -H10 in Hu3.
    move: (Zmult_lt_0_reg_r _ _ (expZ_gt0 k) Hu3) => abs.
    exfalso. omega.
  - have Htmp : [v3]_s = [u3 ]_ s - [t3 ]_ s * 2 ^^ k by omega.
    rewrite Htmp in H13.
    move: (Zgcd_for_euclid (-[t3]_s * 2 ^^ k) ([u3]_s) 1).
    rewrite mul1Z addZC mulNZ addZNE Zgcd_sym.
    move=> X.
    rewrite X (Zgcd_sym _ [u3]_s) Zgcd_opp (Zgcd_sym [u3]_s) in H13.
    destruct k.
    + rewrite /= mulZ1 in H13.
      split; first by rewrite (Zgcd_sym [u3]_s).
      split; by [apply Zodd_opp | ].
    + rewrite Zgcd_Zpower_odd // in H13; last first.
        have -> : [u3 ]_ s = [v3 ]_ s + [t3 ]_ s * 2 ^^ S k by omega.
        apply Zodd_plus_Zeven; last exact/Zeven_mult_Zeven_r/Zeven_power.
        case: H10' => H10'; first by [].
        rewrite Htmp.
        apply Zodd_plus_Zeven => //.
        exact/Zeven_opp/Zeven_mult_Zeven_r/Zeven_power.
      split; first by rewrite (Zgcd_sym [u3]_s).
      split; by [ apply Zodd_opp |].

rewrite /subtract.

apply while.hoare_seq with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  [t3]_s = [u3]_s - [v3]_s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\
  (Zodd [v3 ]_ s \/ Zodd [u3 ]_ s) /\
  C5 u3 v3 s).

apply hoare_assign with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * ([u2]_s - [v2 ]_ s) = [u3 ]_ s - [v3]_s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  (0 <= [t3]_s -> Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\ Zodd [u3]_s /\
    [u3]_s = [t3]_s ) /\
  ([t3]_s < 0 -> Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [t3 ]_ s /\ Zodd [v3]_s /\
    [v3]_s = - [t3]_s) /\
  C5 u3 v3 s).

move=> s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [Hu3 Hv3]]]]]].
rewrite /wp_assign /C2 /C5 /CVectors.
repeat Store_upd.
repeat (split; first by []).
split; last by [].
split; by [rewrite /= /ZIT.sub -Hui -Hvi; ring | ].

apply hoare_assign with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2]_s = [u3 ]_ s - [v3]_s/\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  (0 <= [t3]_s -> Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\ Zodd [u3]_s /\
    [u3]_s = [t3]_s) /\
  ([t3]_s < 0 -> Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [t3 ]_ s /\ Zodd [v3]_s /\
    [v3]_s = - [t3]_s) /\
  C5 u3 v3 s).

move=> s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [Hu3 Hv3]]]]]].
rewrite /wp_assign /C2 /C5.
by repeat Store_upd.

apply hoare_assign'.
move=> s h [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [Hu3 Hv3]]]]]].
rewrite /wp_assign /C2 /C5 /CVectors.
repeat Store_upd.
repeat (split; first tauto).
split.
  case: (Z_lt_le_dec [t3]_s 0).
  - move/H10 => H10'.
    move: (Zgcd_for_euclid [u3]_s [v3]_s (-1)).
    rewrite mulN1Z addZNE => ->.
    case: H10' => H10' [H10'' H10'''].
    rewrite H10''' Zgcd_opp; tauto.
  - move/H9.
    case => H9' [H9'' H9'''].
    rewrite /= H9'''.
    move: (Zgcd_for_euclid [t3]_s [v3]_s (-1)).
    by rewrite mulN1Z addZNE => ->.
split; last by [].
case: (Z_lt_le_dec [t3]_s 0).
- move/H10; tauto.
- move/H9; tauto.

apply while.hoare_ifte.

(** t1 <- svar t1 +e svar v *)

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * ([t2]_s - [u]_s) = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  [t3 ]_ s = [u3 ]_ s - [v3 ]_ s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\
  (Zodd [v3 ]_ s \/ Zodd [u3 ]_ s) /\
  C5 u3 v3 s).

move=> s h.
case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [H11 [H12 [Hu3 Hv3]]]]]]] H1].
rewrite /wp_assign /C2 /C5.
repeat Store_upd.
repeat (split; first by []).
split; last by [].
split; by [rewrite /= /ZIT.add -Hti; ring | ].

apply hoare_assign' => s h.
case=> [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [H11 [Hu3 Hv3]]]]]]].
rewrite /wp_assign /C2 /C4 /C5 /CVectors.
repeat Store_upd.
repeat (split; first by []).
split; first by exists O; right; right; rewrite /= mulZ1.
repeat (split; first by []).
rewrite -(Zgcd_for_euclid [u3]_s [v3]_s (-1)) mulN1Z addZNE.
rewrite H9 -u_g -v_g -2!(mulZC [g]_s) Zgcd_mult in H10; last omega.
apply eqZ_mul2l in H10 => //; omega.

apply hoare_skip' => s h.
case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [H11 [H12 [Hu3 Hv3]]]]]]] H1].
rewrite /wp_assign /C2 /C4.
repeat Store_upd.
repeat (split; first by []).
split; first by exists O; right; right; rewrite /= mulZ1.
repeat (split; first by []).
rewrite -(Zgcd_for_euclid [u3]_s [v3]_s (-1)) mulN1Z addZNE.
rewrite H10 -v_g -u_g -2!(mulZC [g]_s) Zgcd_mult in H11; last omega.
apply eqZ_mul2l in H11 => //; omega.
Qed.

(* NB: compared with prelude_triple, we have strict inequalities *)
Lemma prelude_triple_strict : uniq(u, v, g) ->
  0 < vu -> 0 < vv ->
  {{ fun s _ => C2 vu vv u v g s }}
  prelude u v g
  {{ fun s _ => C2 vu vv u v g s /\
    ~~ [ var_e u \% nat_e 2 \= nat_e 0 \&& var_e v \% nat_e 2 \= nat_e 0 ]b_ s }}.
Proof.
move=> Hset Hvu Hvv.
apply hoare_prop_m.hoare_while_invariant with (fun s _ => C2 vu vv u v g s).
by move=> s h /= [H1 [H2 [H3 [H4 H5]]]].
by move=> s h /= [[H1 [H2 [H3 [H4 H5]]]] H6].
(** u <- var_e u ./e nat_e 2 *)
apply hoare_assign with (fun s h => 0 < [ u ]_s /\ 0 < [ v ]_s /\ 0 < [ g ]_s /\
  2 * [ u ]_s * [ g ]_s = vu /\ [ v ]_s * [ g ]_s = vv /\ [ v ]_s mod 2 = 0).
move=> s h [[H1 [H2 [H3 [H4 H5]]]] H6].
rewrite /hoare_m.eval_b /= in H6; case/andP : H6. rewrite /ZIT.rem.
move/eqP => even_u. move/eqP => even_v.
rewrite /wp_assign; repeat Store_upd => //.
split.
  rewrite /=.
  apply Zlt_0_Zdiv => //.
  rewrite -> Zmod_divides in even_u; last by auto.
  case: even_u => k Hk; omega.
repeat (split; first by []).
split; last by [].
rewrite div_e_exact_full_2 //; by rewrite /hoare_m.eval_b in H6; omegab.
(** v <- var_e v ./e nat_e 2; *)
apply hoare_assign with (fun s h => 0 < [ u ]_s /\ 0 < [ v ]_s /\ 0 < [ g ]_s /\
  2 * [ u ]_s * [ g ]_s = vu /\ 2 * [ v ]_s * [ g ]_ s = vv).
move=> s h [H1 [H2 [H3 [H4 [H5 H6]]]]].
rewrite /wp_assign; repeat Store_upd => //.
split; first by [].
split.
  rewrite /=; apply Zlt_0_Zdiv => //.
  rewrite -> Zmod_divides in H6; last by auto.
  case: H6 => k Hk; omega.
repeat (split; first by []).
by rewrite div_e_exact_full_2.
(** g <- nat_e 2 *e var_e g *)
apply hoare_assign' => s h [H1 [H2 [H3 [H4 H5]]]].
rewrite /wp_assign /C2; repeat Store_upd => //.
repeat (split; first by []).
split; first exact: mulZ_gt0.
rewrite /= -H4 -H5 /ZIT.mul; split; ring.
Qed.

Lemma triple_init0 : uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) ->
  0 < vu -> 0 < vv ->
  {{fun s _ => C2 vu vv u v g s /\ C3 vu vv u v g s }}
  u1 <- nat_e 1;
  u2 <- nat_e 0;
  u3 <- var_e u;
  v1 <- var_e v;
  v2 <- nat_e 1 \- var_e u;
  v3 <- var_e v
  {{fun s _ => C2 vu vv u v g s /\ C3 vu vv u v g s /\ uivi_init u v u1 u2 u3 v1 v2 v3 s}}.
Proof.
move=> Hset Hvu Hvv.
set pre := fun s (h : heap.t) => _.
apply hoare_assign with (fun s h => [u1]_s = 1 /\ pre s h).
  rewrite /wp_assign => s h H.
  rewrite /pre /C2 /C3 /= in H *.
  by repeat Store_upd.
rewrite /pre {pre}.
set pre := fun s (h : heap.t) => _.
apply hoare_assign with (fun s h => [u2]_s = 0 /\ pre s h).
  rewrite /wp_assign => s h H.
  rewrite /pre /C2 /C3 /= in H *.
  by repeat Store_upd.
rewrite /pre {pre}.
set pre := fun s (h : heap.t) => _.
apply hoare_assign with (fun s h => [u3]_s = [u]_s /\ pre s h).
  rewrite /wp_assign.
  move=> s h H.
  rewrite /pre /C2 /C3 /= in H *.
  by repeat Store_upd.
rewrite /pre {pre}.
set pre := fun s (h : heap.t) => _.
apply hoare_assign with (fun s h => [v1]_s = [v]_s /\ pre s h).
  rewrite /wp_assign => s h H.
  rewrite /pre /C2 /C3 /= in H *.
  by repeat Store_upd.
rewrite /pre {pre}.
set pre := fun s (h : heap.t) => _.
apply hoare_assign with (fun s h => [v2]_s = 1 - [u]_s /\ pre s h).
  rewrite /wp_assign => s h H.
  rewrite /pre /C2 /C3 in H *.
  repeat Store_upd.
  rewrite eval_b_upd; last by rewrite [vars_b _]/=; apply/negP/inP; Uniq_not_In.
  tauto.
rewrite /pre {pre}.
set pre := fun s (h : heap.t) => _.
apply hoare_assign'.
rewrite /wp_assign => s h H.
rewrite /pre /C2 /C3 in H *.
rewrite /uivi_init.
repeat Store_upd.
rewrite eval_b_upd; last by rewrite [vars_b _]/=; apply/negP/inP; Uniq_not_In.
tauto.
Qed.

Lemma triple_init1 : uniq(g,u,v,u1,u2,u3,v1,v2,v3,t1,t2,t3) ->
  0 < vu -> 0 < vv ->
  {{fun s _ => C2 vu vv u v g s /\ C3 vu vv u v g s /\ uivi_init u v u1 u2 u3 v1 v2 v3 s}}
  while.ifte (var_e u \% nat_e 2 \= nat_e 1)
    (t1 <- nat_e 0;
    t2 <- cst_e (-1);
    t3 <- .--e var_e v)
  (
    t1 <- nat_e 1;
    t2 <- nat_e 0;
    t3 <- var_e u)
  {{fun s _ => C2 vu vv u v g s /\ C3 vu vv u v g s /\
    uivi_init u v u1 u2 u3 v1 v2 v3 s /\ ti_init u v t1 t2 t3 s}}.
Proof.
move=> Hset Hvu Hvv.
apply while.hoare_ifte.
- set pre := fun s (h : heap.t) => _.
  apply hoare_assign with (fun s h => [t1]_s = 0 /\ pre s h).
    rewrite /wp_assign => s h H.
    rewrite /pre /uivi_init /C2 /C3 in H *.
    repeat Store_upd.
    rewrite eval_b_upd; last by rewrite [vars_b _]/=; apply/negP/inP; Uniq_not_In.
    rewrite /hoare_m.eval_b.
    rewrite eval_b_upd; last by rewrite [vars_b _]/=; apply/negP/inP; Uniq_not_In.
    tauto.
  rewrite /pre {pre}.
  set pre := fun s (h : heap.t) => _.
  apply hoare_assign with (fun s h => [t2]_s = -1 /\ pre s h).
    rewrite /wp_assign => s h H /=.
    rewrite /pre /uivi_init /C2 /C3 in H *.
    repeat Store_upd.
    rewrite eval_b_upd; last by rewrite [vars_b _]/=; apply/negP/inP; Uniq_not_In.
    rewrite /hoare_m.eval_b.
    rewrite eval_b_upd; last by rewrite [vars_b _]/=; apply/negP/inP; Uniq_not_In.
    tauto.
  rewrite /pre {pre}.
  set pre := fun s (h : heap.t) => _.
  apply hoare_assign'.
  rewrite /wp_assign => s h H.
  repeat Store_upd.
  rewrite /pre {pre} in H.
  rewrite /uivi_init /C2 /C3 in H *.
  rewrite [eval _ _]/=.
  repeat Store_upd.
  case: H => [Ht2 [Ht1] [[[Hu [Hv [Hg [Hhg Hvg]]]] [[Hgcd Htest'] [Hu1 [Hu2 [Hu3 [Hv1 [Hv2 Hv3]]]]]]] Htest]].
  repeat (split; first by []).
  repeat (split; first by []).
  split.
    rewrite /=.
    by do 2 Store_upd.
  repeat (split; first tauto).
  rewrite /ti_init.
  repeat Store_upd.
  rewrite /= /ZIT.eqb /ZIT.rem in Htest.
  move/eqP in Htest.
  have {}Htest : Zodd [u]_s.
    rewrite /= /ZIT.rem in Htest.
    apply not_Zmod_2_Zodd; by rewrite Htest.
  split; first by [].
  by move/Zeven_not_Zodd.
- set pre := fun s (h : heap.t) => _.
  apply hoare_assign with (fun s h => [t1]_s = 1 /\ pre s h).
    rewrite /wp_assign => s h H.
    rewrite /pre /uivi_init /C2 /C3 in H *.
    rewrite /hoare_m.eval_b ![fst _]/= in H *.
    repeat Store_upd.
    by do 2 (rewrite eval_b_upd; last by simpl vars_b; apply/negP/inP; Uniq_not_In).
  rewrite /pre {pre}.
  set pre := fun s (h : heap.t) => _.
  apply hoare_assign with (fun s h => [t2]_s = 0 /\ pre s h).
    rewrite /wp_assign => s h H.
    rewrite /pre /uivi_init /C2 /C3 /hoare_m.eval_b in H *.
    repeat Store_upd.
    by do 2 (rewrite eval_b_upd; last by simpl vars_b; apply/negP/inP; Uniq_not_In).
  rewrite /pre {pre}.
  set pre := fun s (h : heap.t) => _.
  apply hoare_assign'.
  rewrite /wp_assign => s h H.
  rewrite /pre /uivi_init /C2 /C3 /= in H *.
  split.
    repeat Store_upd.
    tauto.
  repeat Store_upd.
  case: H => [Ht2 [Ht1] [[[Hu [Hv [Hg [Hhg Hvg]]]] [[Hgcd Htest'] [Hu1 [Hu2 [Hu3 [Hv1 [Hv2 Hv3]]]]]]] Htest]].
  repeat (split; first by []).
  rewrite /ti_init.
  repeat Store_upd.
  split => u_parity.
  - rewrite /= in Htest', Htest.
    move/negP : Htest'.
    rewrite negb_and.
    case/orP => X.
    + exfalso.
      move/negP : X.
      apply.
      rewrite /hoare_m.eval_b /ZIT.eqb /= /ZIT.rem in Htest *.
      move/eqP in Htest.
      apply/eqP.
      lapply (Z_mod_lt [u]_s 2) => //.
      move=> ?; omega.
    + exfalso.
      move/negP : Htest; apply.
      rewrite /ZIT.eqb /ZIT.rem.
      apply/eqP.
      by apply Zodd_Zmod_2 in u_parity.
  - rewrite /= in Htest, Htest'.
    move/negP : Htest'.
    rewrite negb_and.
    case/orP=> X; last by [].
    exfalso.
    move/negP : X.
    apply.
    exact/eqP/Zeven_Zmod_2.
Qed.

Lemma triple_init : uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) ->
  0 < vu -> 0 < vv ->
  {{fun s _ => C2 vu vv u v g s /\ C3 vu vv u v g s }}
  init u v u1 u2 u3 v1 v2 v3 t1 t2 t3
  {{fun s _ => C2 vu vv u v g s /\ C3 vu vv u v g s /\
    uivi_init u v u1 u2 u3 v1 v2 v3 s /\ ti_init u v t1 t2 t3 s}}.
Proof.
move=> Hset Hvu Hvv.
rewrite /init.
apply while.hoare_seq with (fun s h => C2 vu vv u v g s /\ C3 vu vv u v g s /\
  uivi_init u v u1 u2 u3 v1 v2 v3 s).
exact: triple_init0.
exact: triple_init1.
Qed.

Lemma triple_prelude_init : uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) ->
  0 < vu -> 0 < vv ->
  {{ fun s h => [u]_s = vu /\ [v]_s = vv }}
  g <- nat_e 1;
  prelude u v g;
  init u v u1 u2 u3 v1 v2 v3 t1 t2 t3
  {{ fun s _ => C2 vu vv u v g s /\ C3 vu vv u v g s /\
    uivi_init u v u1 u2 u3 v1 v2 v3 s /\
    ti_init u v t1 t2 t3 s }}.
Proof.
move=> Hset Hvu Hvv.
(** g <- nat_e 1 ; *)
apply hoare_assign with (fun s h => C1 vu vv u v g s).
move=> s h [Hu Hv].
by rewrite /wp_assign /C1 /uv_init; repeat Store_upd.
(** prelude u v g ; *)
apply while.hoare_seq with (fun s _ => C2 vu vv u v g s /\ C3 vu vv u v g s).
have Hset' : uniq(u, v, g) by rewrite [Equality.sort _]/= in Hset *; Uniq_uniq O.

eapply while.hoare_conseq; last exact: (prelude_triple_strict Hset' Hvu Hvv).
- move=> s h /= [[H1 [H2 [H3 [H4 H5]]]] H6].
  rewrite /C2 /C3.
  repeat (split; first omega).
  split; last by move/negP: H6.
  rewrite -H4 -H5.
  apply Zis_gcd_gcd; last first.
    rewrite (mulZC [u]_s) (mulZC [v]_s).
    exact/Zis_gcd_mult/Zgcd_is_gcd.
  apply mulZ_ge0 => //; [omega | exact: Zgcd_is_pos].
- rewrite /C1 /uv_init /C2 => s h /= [[-> ->] ->]; by rewrite 2!mulZ1.
exact: triple_init.
Qed.

Lemma triple :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) -> 0 < vu -> 0 < vv ->
  {{ fun s h => [u]_s = vu /\ [v]_s = vv }}
  begcd g u v u1 u2 u3 v1 v2 v3 t1 t2 t3
  {{ fun s h => vu * [u1]_s + vv * [u2]_s = [g]_s * [u3]_s /\
    Z.gcd vu vv = ([g]_s * [u3]_s)}}.
Proof.
move=> Hset Hvu Hvv.
rewrite /begcd.
do 2 apply hoare_prop_m.hoare_seq_assoc'.
eapply while.hoare_seq.
apply hoare_prop_m.hoare_seq_assoc.
exact: triple_prelude_init.
exact: triple_intermediate.
Qed.

End begcd_taocp_fun_cor.

End BEGCD_TAOCP_FUN_COR.

Definition uivi_bounds u v u1 v1 u2 v2 u3 v3 st :=
  0 <= [u1 ]_ st <= [v ]_ st /\ 0 <= [v1 ]_ st <= [v ]_ st /\
  - [u ]_ st <= [u2 ]_ st <= 0 /\ - [u ]_ st <= [v2 ]_ st <= 0 /\
  0 < [u3 ]_ st <= [u ]_ st /\  0 < [v3 ]_ st <= [v ]_ st.

Definition ti_bounds u v t1 t2 t3 st :=
  0 <= [t1 ]_ st <= [v ]_ st /\
  - [u ]_ st <= [t2 ]_ st <= 0 /\
  - [v ]_ st <= [t3 ]_ st <= [u ]_ st.

Lemma init_bounds u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s :
  0 < [u]_s -> 0 < [v]_s ->
  uivi_init u v u1 u2 u3 v1 v2 v3 s ->
  ti_init u v t1 t2 t3 s ->
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\ ti_bounds u v t1 t2 t3 s.
Proof.
move=> Hu Hv Huivi_init Hti_init.
rewrite /uivi_init in Hti_init.
rewrite /uivi_init in Huivi_init.
case : Huivi_init => [Hu1 [Hu2 [Hu3 [Hv1 [Hv2 Hv3]]]]].
split.
  rewrite /uivi_bounds Hu1 Hu2 Hu3 Hv1 Hv2 Hv3.
  omega.
rewrite /ti_bounds.
case: (Zeven_odd_dec [u]_s).
case/(proj2 Hti_init) => -> [-> ->]; omega.
case/(proj1 Hti_init)=> -> [-> ->]; omega.
Qed.

Module BEGCD_TAOCP_COR.

Section begcd_taocp_cor.

Variables g u v u1 u2 u3 v1 v2 v3 t1 t2 t3 : nat.
Variables vu vv : Z.

Lemma triple_init :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) -> 0 < vu -> 0 < vv ->
  {{ fun s h => uv_init vu vv u v s }}
  g <- nat_e 1;
  prelude u v g;
  BEGCD_TAOCP.init u v u1 u2 u3 v1 v2 v3 t1 t2 t3
  {{fun s _ => C2 vu vv u v g s /\ C3 vu vv u v g s /\
    uivi_init u v u1 u2 u3 v1 v2 v3 s /\
    ti_init u v t1 t2 t3 s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
    ti_bounds u v t1 t2 t3 s}}.
Proof.
move=> Hset Hvu Hvv.
eapply hoare_prop_m.hoare_weak; last exact: BEGCD_TAOCP_FUN_COR.triple_prelude_init.
rewrite /while.entails => s h.
case => HC2 [HC3 [Huivi_init Hti_init]].
repeat (split; first by []).
rewrite /C2 in HC2.
apply init_bounds => //; tauto.
Qed.

Lemma while_halve_invariant : uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) ->
  0 < vu -> 0 < vv ->
  {{ fun s h => (C2 vu vv u v g s /\
    (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
    CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
    C4 u3 v3 t3 s /\
    C5 u3 v3 s /\
    Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
    ti_bounds u v t1 t2 t3 s /\ [t3 ]_ s <> 0) /\
  hoare_m.eval_b (var_e t3 \% nat_e 2 \= nat_e 0) (s, h)}}
  while.ifte (var_e t1 \% nat_e 2 \= nat_e 0 \&& var_e t2 \% nat_e 2 \= nat_e 0)
    (t1 <- var_e t1 ./e nat_e 2;
    t2 <- var_e t2 ./e nat_e 2;
    t3 <- var_e t3 ./e nat_e 2)
    (t1 <- (var_e t1 \+ var_e v) ./e nat_e 2;
     t2 <- (var_e t2 \- var_e u) ./e nat_e 2;
     t3 <- var_e t3 ./e nat_e 2)
  {{ fun s _ => C2 vu vv u v g s /\
    (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
    CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
    C4 u3 v3 t3 s /\
    C5 u3 v3 s /\
    Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
    ti_bounds u v t1 t2 t3 s /\ [t3 ]_ s <> 0 }}.
Proof.
move=> Hset Hvu Hvv.
apply while.hoare_ifte.
- apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * 2 * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  [t3 ]_ s <> 0 /\
  Zeven [t3]_s /\
  Zeven [t2]_s).

  move=> s h /=.
  case => [[[[Hu [Hv [Hg [u_g v_g]]]] [H7 [[Hti [Hui Hvi]] [H11 [[Hu3 Hv3] [H14 [Hinvar1 [Hinvar2 H16]]]]]]]] H3] H1].
  rewrite /wp_assign /C2 /C4 /C5.
  repeat Store_upd.
  repeat (split; first by []).
  split.
    rewrite -mulZA div_e_exact_full_2 //.
    rewrite /hoare_m.eval_b /= in H1.
    case/andP : H1 => H1 _.
    rewrite /ZIT.eqb /ZIT.rem /= in H1.
    by move/eqP : H1.
  repeat (split; first tauto).
  rewrite /hoare_m.eval_b /= /ZIT.eqb /ZIT.rem /= in H1, H3.
  move/eqP in H3.
  case/andP : H1 => _ /eqP H1.
  split.
    rewrite /uivi_bounds in Hinvar1 *.
    by repeat Store_upd.
  split.
    rewrite /ti_bounds in Hinvar2 *.
    repeat Store_upd.
    split; last tauto.
    rewrite /= /ZIT.div.
    split.
      apply Z_div_pos => //; tauto.
    apply (@leZ_trans ([t1]_s)); last tauto.
    apply Zdiv_le_pos => //; tauto.
  split; [assumption | split; exact: Zmod_2_Zeven].

apply hoare_assign with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * 2 * [t1 ]_ s + [v ]_ s * 2 * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  [t3 ]_ s <> 0 /\ Zeven [t3 ]_ s ).

move=> s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [[Hu3 Hv3] [H12 [Hinvar1 [Hinvar2 [H13 [H14 H16]]]]]]]]]].
rewrite /wp_assign /C2 /C4 /C5.
repeat Store_upd.
repeat (split; first tauto).
split; first by rewrite -(mulZA [v]_s) div_e_exact_full_2 //;  exact: Zeven_Zmod_2.
repeat (split; first by []).
split.
  rewrite /uivi_bounds in Hinvar1 *.
  by repeat Store_upd.
split; last by [].
rewrite /ti_bounds in Hinvar2 *.
repeat Store_upd.
split; first tauto.
split; last tauto.
rewrite /= /ZIT.div.
split.
  apply (@leZ_trans ([t2]_s)); [tauto | apply Zdiv_le_neg => //; tauto].
apply Z_div_neg => //; tauto.

apply hoare_assign' => s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [[Hu3 Hv3] [H12 [Hinvar1 [Hinvar2 [H13 H15]]]]]]]]].
rewrite /wp_assign /C2 /C4 /C5 /CVectors.
repeat Store_upd.
repeat (split; first tauto).
split.
  rewrite /= -Hti /ZIT.div.
  set tmp := _ + [v]_s * 2 * _ .
  have -> : tmp = ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s) * 2 by rewrite /tmp; ring.
  by rewrite Z_div_mult_full.
repeat (split; first by []).
split.
 case/Zeven_ex : H15 => m H15.
 rewrite [eval _ _]/= H15 (mulZC 2) /ZIT.div Z_div_mult_full //.
 case: H9 => k [ [H9 H9'] | ].
 + exists (S k); left.
   by rewrite ZpowerS mulZA -(mulZC 2) -H15.
 + case => H9; exists (S k); right.
   * left; by rewrite ZpowerS mulZA -(mulZC 2) -H15.
   * right; by rewrite ZpowerS mulZA -(mulZC 2) -H15.
repeat (split; first by []).
split.
  rewrite /uivi_bounds.
  by repeat Store_upd.
split.
  rewrite /ti_bounds in Hinvar2 *.
  repeat Store_upd.
  repeat (split; first tauto).
  rewrite /= /ZIT.div.
  split.
    case: (Z_lt_le_dec [t3]_s 0) => Ht3.
      apply (@leZ_trans [t3]_s); first tauto.
      apply Zdiv_le_neg => //; exact: ltZW.
    apply (@leZ_trans 0); first omega.
    exact: Z_div_pos.
  case: (Z_lt_le_dec [t3]_s 0) => Ht3.
   apply (@leZ_trans 0); last omega.
    apply Z_div_neg => //; exact: ltZW.
  apply (@leZ_trans [t3]_s); [exact: Zdiv_le_pos | tauto].
case/Zeven_ex : H15 => m H15.
rewrite /= H15 (mulZC 2) /ZIT.div Z_div_mult_full //; omega.

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * (2 * [t1 ]_ s  - [v]_s) + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  [t3 ]_ s <> 0 /\ Zeven [t3]_s /\
  (Zodd (2 * [t1]_s - [v]_s) \/ Zodd [t2]_s)).

move=> s h.
case => [[[[Hu [Hv [Hg [u_g v_g]]] [H7 [[Hti [Hui Hvi]] [H11 [[Hu3 Hv3] [H14 [Hinvar1 [Hinvar2 H16]]]]]]]]] H3] H1].
rewrite /wp_assign /C2 /C4 /C5.
repeat Store_upd.
rewrite /hoare_m.eval_b /= /ZIT.eqb /ZIT.rem in H1 H3.
rewrite negb_and in H1.

have t1_v : [var_e t1 \+ var_e v ]e_ s mod 2 = 0.
  rewrite /= /ZIT.add.
  case/orP: H1 => [/eqP odd_t1 | /eqP odd_t2].
  - apply Zeven_Zmod_2, Zodd_plus_Zodd.
    exact: not_Zmod_2_Zodd.
    case: H7 => [odd_u |]; last exact.
    move/eqP/Zmod_2_Zeven : H3.
    rewrite -Hti.
    case/Zeven_plus_inv => [[u_t1 v_t2] | [] _].
    + move/not_Zmod_2_Zodd : odd_t1.
      move/(Zodd_mult_Zodd _ _ odd_u).
      by move/Zodd_not_Zeven.
    + by case/Zodd_mult_inv.
  - case: H7 => [odd_u | odd_v].
    + move/eqP/Zmod_2_Zeven : H3.
      rewrite -Hti.
      case/Zeven_plus_inv => [[u_t1 v_t2] | []].
      * case/Zeven_mult_inv : v_t2 => v_t2.
        - case/Zeven_mult_inv : u_t1 => u_t1.
          + by move/Zodd_not_Zeven : odd_u.
          + exact/Zeven_Zmod_2/Zeven_plus_Zeven.
        - move/not_Zmod_2_Zodd : odd_t2.
          by move/Zodd_not_Zeven.
      * case/Zodd_mult_inv=> _ odd_t1.
        case/Zodd_mult_inv=> odd_v _.
        exact/Zeven_Zmod_2/Zodd_plus_Zodd.
    + move/eqP/Zmod_2_Zeven : H3.
      rewrite -Hti.
      case/Zeven_plus_inv => [[u_t1 v_t2] | []].
      * have : Zodd ([v ]_ s * [t2 ]_ s).
          apply Zodd_mult_Zodd => //; exact: not_Zmod_2_Zodd.
        by move/Zodd_not_Zeven.
      * case/Zodd_mult_inv=> _ odd_t1 _.
        exact/Zeven_Zmod_2/Zodd_plus_Zodd.

repeat (split; first by []).
split.
  split; by [rewrite div_e_exact_full_2 //= /ZIT.add -Hti; ring | ].
repeat (split; first by []).
split.
  rewrite /uivi_bounds; by repeat Store_upd.
split.
  rewrite /ti_bounds in Hinvar2 *.
  repeat Store_upd.
  rewrite /= /ZIT.div /ZIT.add.
  split; last tauto.
  split.
  + apply Z_div_pos => //; omega.
  + apply (@leZ_trans (([v]_s + [v]_s) / 2)).
    apply Z_div_le => //; omega.
    rewrite addZZ Z_div_mult_full //; exact: leZZ.
split; first by [].
split.
  apply Zmod_2_Zeven; exact/eqP.
case/orP : H1 => H1.
- left.
  rewrite div_e_exact_full_2 //.
  move/eqP : H1 => /not_Zmod_2_Zodd.
  suff : [var_e t1 \+ var_e v ]e_ s - [v ]_ s = [t1]_s by move=> ->.
  rewrite /= /ZIT.add; ring.
- right.
  by move/eqP/not_Zmod_2_Zodd : H1.

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * (2 * [t1 ]_ s  - [v]_s) + [v ]_ s * (2 * [t2 ]_ s + [u]_s) = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  [t3 ]_ s <> 0 /\ Zeven [t3]_s).

move=> s h H.
rewrite (mulZC 2) /= -(mulZC 2) in H.
case: H => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [[Hu3 Hv3] [H12 [Hinvar1 [Hinvar2 [H13 [H14 H16]]]]]]]]]].
rewrite /wp_assign /C2 /C4 /C5.
repeat Store_upd.
have Htmp : [var_e t2 \- var_e u ]e_ s mod 2 = 0.
  rewrite /= /ZIT.sub.
  apply Zeven_Zmod_2.
  case: H5 => H5.
  - case: H16 => H16.
    + move: H14.
      rewrite -Hti.
      case/Zeven_plus_inv => [[] | [] ].
      * case/Zeven_mult_inv; by move/Zeven_not_Zodd.
      * case/Zodd_mult_inv=> K1 _.
        case/Zodd_mult_inv=> _ K4.
        apply Zodd_plus_Zodd => //; exact: Zodd_opp.
    + apply Zodd_plus_Zodd => //; exact: Zodd_opp.
  - case: H16 => H16.
    + move: H14.
      rewrite -Hti.
      case/Zeven_plus_inv => [[] | []].
      * case/Zeven_mult_inv => [u_even | ].
        - case/Zeven_mult_inv => [ | even_t2].
          by move/Zeven_not_Zodd.
          apply Zeven_plus_Zeven => //; exact: Zeven_opp.
        - by move/Zeven_not_Zodd.
      * case/Zodd_mult_inv=> odd_u _.
        case/Zodd_mult_inv=> _ odd_t2.
        apply Zodd_plus_Zodd => //; exact: Zodd_opp.
    + move: H14.
      rewrite -Hti.
      case/Zeven_plus_inv => [[] | []].
      * case/Zeven_mult_inv => [u_even | _]; case/Zeven_mult_inv; by move/Zeven_not_Zodd.
      * case/Zodd_mult_inv=> K1 _ _.
        apply Zodd_plus_Zodd => //; exact: Zodd_opp.

repeat (split; first by []).
split.
  split; by [rewrite div_e_exact_full_2 // /ZIT.add -Hti (mulZC 2) /= /ZIT.sub; ring | ].
repeat (split; first by []).
split.
  rewrite /uivi_bounds; by repeat Store_upd.
split; last by [].
rewrite /ti_bounds in Hinvar2 *.
repeat Store_upd.
split; first tauto.
split; last tauto.
rewrite /= /ZIT.div /ZIT.sub.
split.
- apply (@leZ_trans ((- [u]_s - [u]_s) /2)).
  apply Zdiv_le_lower_bound => //; omega.
  apply Z_div_le => //; omega.
- apply Z_div_neg => //; omega.

apply hoare_assign' => s h H.
rewrite !(mulZC 2) in H.
case: H => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [[Hu3 Hv3] [H12 [Hinvar1 [Hinvar2 [H13 H15]]]]]]]]].
rewrite /wp_assign /C2 /C4 /C5 /CVectors.
repeat Store_upd.
repeat (split; first tauto).
split.
  split; last by [].
  rewrite /= -Hti /ZIT.div.
  have : ([u ]_ s * ([t1 ]_ s * 2 - [v ]_ s) + [v ]_ s * ([t2 ]_ s * 2 + [u ]_ s)) =
    ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s) * 2 by ring.
  move=> ->; by rewrite Z_div_mult_full.
split.
  case/Zeven_ex : H15 => m H15.
  rewrite [eval _ _]/= H15 (mulZC 2) /ZIT.div Z_div_mult_full //.
  case: H9 => k H9.
  case: H9 => H9.
  - case: H9 => H9 H9'.
    exists (S k); left.
    by rewrite ZpowerS mulZA -(mulZC 2) -H15.
  - case: H9 => H9; exists (S k); right.
    + left; by rewrite ZpowerS mulZA -(mulZC 2) -H15.
    + right; by rewrite ZpowerS mulZA -(mulZC 2) -H15.
repeat (split; first by []).
split.
  rewrite /uivi_bounds; by repeat Store_upd.
split.
  rewrite /ti_bounds in Hinvar2 *.
  repeat Store_upd.
  repeat (split; first tauto).
  rewrite /= /ZIT.div.
  case: (Z_lt_le_dec [t3]_s 0) => Ht3.
    split.
      apply (@leZ_trans [t3]_s); first tauto.
      apply Zdiv_le_neg => //; omega.
    apply (@leZ_trans 0); last exact: ltZW.
    apply Z_div_neg => //. exact: ltZW.
  split.
    apply (@leZ_trans 0); [omega | exact: Z_div_pos].
  apply (@leZ_trans [t3]_s); [exact: Zdiv_le_pos | tauto].
case/Zeven_ex : H15 => m H15.
rewrite /= H15 mulZC /ZIT.div Z_div_mult_full //; omega.
Qed.

Lemma while_halve_invariant_stren :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) -> 0 < vu -> 0 < vv ->
  while.entails hoare_m.store hoare_m.heap
  (fun s h => (C2 vu vv u v g s /\
      (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
      CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
      C4 u3 v3 t3 s /\
      C5 u3 v3 s /\
      Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
      uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\ ti_bounds u v t1 t2 t3 s) /\
    [ var_e t3 \!= nat_e 0 ]b_ s)
  (fun s _ => C2 vu vv u v g s /\
    (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
      CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
      C4 u3 v3 t3 s /\
      C5 u3 v3 s /\
      Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
      uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
      ti_bounds u v t1 t2 t3 s /\ [t3 ]_ s <> 0).
Proof.
move=> Hset Hvu Hvv => s h /=.
case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [H7 [H8 [H9 [H10 [[Hu3 Hv3] [H12 [H14 [Hinvar1 Hinvar2]]]]]]]]]] H1].
repeat (split => //).
rewrite /hoare_m.eval_b /= /ZIT.eqb in H1.
by move/eqP : H1.
Qed.

Lemma while_halve_invariant_weak :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) -> 0 < vu -> 0 < vv ->
while.entails hoare_m.store hoare_m.heap
(fun s h => (C2 vu vv u v g s /\
    (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
    CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
    C4 u3 v3 t3 s /\
    C5 u3 v3 s /\
    Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
    ti_bounds u v t1 t2 t3 s /\ [t3 ]_ s <> 0) /\
  ~~ [ var_e t3 \% nat_e 2 \= nat_e 0 ]b_ s)
(fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\ Zodd [t3 ]_ s).
Proof.
move=> Hset Hvu Hvv => s h /=.
case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [[Hu3 Hv3] [H13 [Hinvar1 [Hinvar2 H15]]]]]]]] H1].
repeat (split; first by []).
split.
  rewrite -u_g -v_g -H13 -Zgcd_mult; last omega.
  f_equal; by rewrite mulZC.
rewrite /hoare_m.eval_b /= /ZIT.eqb /ZIT.rem in H1.
move/eqP : H1; by move/not_Zmod_2_Zodd.
Qed.

Lemma while_halve :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) -> 0 < vu -> 0 < vv ->
{{ fun s h => (C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\ ti_bounds u v t1 t2 t3 s) /\
  hoare_m.eval_b (var_e t3 \!= nat_e 0) (s, h) }}
while.while (var_e t3 \% nat_e 2 \= nat_e 0) (BEGCD_TAOCP.halve u v t1 t2 t3)
{{ fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\ Zodd [t3 ]_ s}}.
Proof.
move=> Hset Hvu Hvv.
rewrite /BEGCD_TAOCP.halve.
apply hoare_prop_m.hoare_while_invariant with (fun s h =>
  C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  [t3]_s <> 0).
exact: while_halve_invariant_stren.
exact: while_halve_invariant_weak.
exact: while_halve_invariant.
Qed.

Lemma reset_triple :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) ->  0 < vu -> 0 < vv ->
  {{fun s _ => C2 vu vv u v g s /\
    (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
    CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
    C4 u3 v3 t3 s /\
    C5 u3 v3 s /\
    Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
    ti_bounds u v t1 t2 t3 s /\ Zodd [t3 ]_ s}}
  BEGCD_TAOCP.reset u v u1 u2 u3 v1 v2 v3 t1 t2 t3
  {{fun s _ => C2 vu vv u v g s /\
    (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
     CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
     (0 <= [t3 ]_ s ->
       Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\
       Zodd [u3 ]_ s /\ [u3 ]_ s = [t3 ]_ s) /\
     ([t3 ]_ s < 0 ->
       Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [t3 ]_ s /\
       Zodd [v3 ]_ s /\ [v3 ]_ s = - [t3 ]_ s) /\
     uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
     ti_bounds u v t1 t2 t3 s /\ C5 u3 v3 s}}.
Proof.
move=> Hset Hvu Hvv.
rewrite /BEGCD_TAOCP.reset.
apply while.hoare_ifte.
apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\ Zodd [t3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  C5 u3 v3 s /\
  0 < [t3]_s).
move=> s h /=.
case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [[Hu3 Hv3] [H13 [Hinvar1 [Hinvar2 H15]]]]]]]] H1].
rewrite /wp_assign /C2 /C4 /C5 /CVectors.
repeat Store_upd.
rewrite /hoare_m.eval_b /= /ZIT.geb in H1.
move/geZP in H1.
repeat (split; first by []).
split.
  rewrite /uivi_bounds /= in Hinvar1 *.
  rewrite /ti_bounds in Hinvar2.
  repeat Store_upd.
  tauto.
split.
  rewrite /ti_bounds; by repeat Store_upd.
move/Z.ge_le : H1; case/leZ_eqVlt => H1 //.
by rewrite -H1 in H15.

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  C4 u3 v3 t3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\
  Zodd [t3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  C5 u3 v3 s /\
  0 < [t3 ]_ s).

move=> s h /=.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [H11 [Hinvar1 [Hinvar2 [[H3 Hv3] H17]]]]]]]]].
rewrite /wp_assign /C2 /C4 /C5 /CVectors.
repeat Store_upd.
repeat (split; first tauto).
split.
  rewrite /= /uivi_bounds in Hinvar1 *.
  repeat Store_upd.
  repeat (split; first tauto).
  split; last tauto.
  rewrite /ti_bounds in Hinvar2; tauto.
split; last by [].
rewrite /ti_bounds.
by repeat Store_upd.

apply hoare_assign' => s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [H11 [Hinvar1 [Hinvar2 [[Hu3 Hv3] H15]]]]]]]]].
rewrite /wp_assign /C2 /CVectors.
repeat Store_upd.
repeat (split; first tauto).
split.
  move=> Ht3.
  case: H9 => k [ [H9 H9'] | [ [H9 H9'] | [H9 H9'] ]].
  - exfalso.
    have : -[v3]_s < 0 by omega.
    rewrite -H9.
    move/Zlt_not_le.
    apply.
    apply mulZ_ge0 => //; exact: expZ_ge0.
  - by rewrite -H9 Zgcd_Zpower_odd // in H10.
  - have Htmp : [u3 ]_ s = [t3 ]_ s * 2 ^^ k + [v3 ]_ s by omega.
    rewrite{} Htmp in H10.
    move: (Zgcd_for_euclid ([t3 ]_ s * 2 ^^ k) [v3 ]_ s 1) => X.
    rewrite mul1Z in X.
    rewrite {}X in H10.
    destruct k as [|k].
    - by rewrite /= mulZ1 in H10.
    - case: H9' => // H9'.
      by rewrite Zgcd_Zpower_odd // in H10.
      rewrite Zgcd_Zpower_odd // in H10.
      have -> : [v3 ]_ s = [u3 ]_ s - [t3 ]_ s * 2 ^^ S k by omega.
      apply Zodd_plus_Zeven => //.
      exact/Zeven_opp/Zeven_mult_Zeven_r/Zeven_power.
split.
  move=> Ht3.
  exfalso.
  omega.
split.
  rewrite /uivi_bounds in Hinvar1 *.
  repeat Store_upd.
  repeat (split; first tauto).
  split; last tauto.
  rewrite /ti_bounds in Hinvar2.
  rewrite /=; omega.
split.
  rewrite /ti_bounds.
  by repeat Store_upd.
rewrite /C5; by repeat Store_upd.

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1]_s + [v]_s * (- [u]_s - [t2]_s ) = - [t3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  Zodd [t3 ]_ s /\
  [t3]_s < 0).

move=> s h /= H.
case : H => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hi Hvi]] [H10 [[Hu3 Hv3] [H13 [Hinvar1 [Hinvar2 H15]]]]]]]] H1].
rewrite /wp_assign /C2 /C4 /C5.
repeat Store_upd.
repeat (split; first by []).
split.
  repeat (split; first by []).
  rewrite -Hti /= /ZIT.sub; ring.
repeat (split; first by []).
split.
  rewrite /uivi_bounds in Hinvar1 *.
  repeat Store_upd.
  split; first tauto.
  split; last tauto.
  rewrite /= /ZIT.sub.
  rewrite /ti_bounds in Hinvar2.
  omega.
split.
  rewrite /ti_bounds in Hinvar2 *.
  repeat Store_upd.
  tauto.
split; first by [].
rewrite /hoare_m.eval_b /= /ZIT.geb in H1.
move/geZP : H1 => ?; omega.

apply hoare_assign with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2 ]_ s = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1]_s + [v]_s * [v2]_s = - [t3 ]_ s) /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  Zodd [t3 ]_ s /\ [t3 ]_ s < 0).
move=> s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [[Hu3 Hv3] [H12 [Hinvar1 [Hinvar2 [H13 H15]]]]]]]]].
rewrite /wp_assign /C2 /C4 /C5 /CVectors.
repeat Store_upd.
repeat (split; first by []).
split.
  repeat (split; first by []).
  rewrite /= /ZIT.add -Hvi; ring.
repeat (split; first by []).
split.
  rewrite /uivi_bounds in Hinvar1 *.
  repeat Store_upd.
  repeat (split; first tauto).
  split; last tauto.
  rewrite /= /ZIT.add.
  rewrite /ti_bounds in Hinvar2; omega.
split; last by [].
rewrite /ti_bounds.
by repeat Store_upd.

apply hoare_assign' => s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [[Hu3 Hv3] [H12 [Hinvar1 [Hinvar2 [H13 H15]]]]]]]]].
rewrite /wp_assign /C2 /C5 /CVectors.
repeat Store_upd.
repeat (split; first by []).
rewrite /=.
split; first by move/Zle_not_lt.
split.
move=> _.
  rewrite /=.
  case: H9 => k [ [H9 H9'] | [ [H9 H9'] | [H9 H9'] ] ].
  - have X : [v3 ]_ s = - ([t3 ]_ s * 2 ^^ k) by omega.
    rewrite {}X Zgcd_opp in H12.
    symmetry in H12.
    rewrite Zgcd_sym Zgcd_Zpower_odd // in H12.
    split; first by symmetry; rewrite Zgcd_sym.
    split; by [ apply Zodd_opp | ].
  - rewrite -H9 in Hu3.
    move: (Zmult_lt_0_reg_r _ _ (expZ_gt0 k) Hu3) => abs.
    exfalso. omega.
  - have Htmp : [v3]_s = [u3 ]_ s - [t3 ]_ s * 2 ^^ k by omega.
    rewrite Htmp in H12.
    move: (Zgcd_for_euclid (-[t3]_s * 2 ^^ k) ([u3]_s) 1).
    rewrite mul1Z addZC mulNZ addZNE Zgcd_sym.
    move=> X.
    rewrite X (Zgcd_sym _ [u3]_s) Zgcd_opp (Zgcd_sym [u3]_s) in H12.
    destruct k.
    + rewrite /= mulZ1 in H12.
      split; first by rewrite (Zgcd_sym [u3]_s).
      split; by [ apply Zodd_opp | ].
    + rewrite Zgcd_Zpower_odd // in H12; last first.
        have -> : [u3 ]_ s = [v3 ]_ s + [t3 ]_ s * 2 ^^ S k by omega.
        apply Zodd_plus_Zeven; last exact/Zeven_mult_Zeven_r/Zeven_power.
        case: H9' => H9' //.
        rewrite Htmp.
        apply Zodd_plus_Zeven => //.
        exact/Zeven_opp/Zeven_mult_Zeven_r/Zeven_power.
      split; first by rewrite (Zgcd_sym [u3]_s).
      split; by [ apply Zodd_opp | ].
split.
  rewrite /uivi_bounds in Hinvar1 *.
  repeat Store_upd.
  repeat (split; first tauto).
  rewrite /ti_bounds in Hinvar2.
  omega.
split.
  rewrite /ti_bounds.
  by repeat Store_upd.
omega.
Qed.

Lemma subtract_part1 : uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) ->  0 < vu -> 0 < vv ->
   {{fun s _ => C2 vu vv u v g s /\
     (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
     CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
     (0 <= [t3 ]_ s ->
      Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\
      Zodd [u3 ]_ s /\ [u3 ]_ s = [t3 ]_ s) /\
     ([t3 ]_ s < 0 ->
      Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [t3 ]_ s /\
      Zodd [v3 ]_ s /\ [v3 ]_ s = - [t3 ]_ s) /\
     uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
     ti_bounds u v t1 t2 t3 s /\ C5 u3 v3 s}}
   t1 <- var_e u1 \- var_e v1;
   t2 <- var_e u2 \- var_e v2; t3 <- var_e u3 \- var_e v3
   {{fun s _ => C2 vu vv u v g s /\
     (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
     CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
     [t3 ]_ s = [u3 ]_ s - [v3 ]_ s /\
     Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\
     [t1 ]_ s = [u1 ]_ s - [v1 ]_ s /\
     uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
     ((0 < [t1]_s (*[v1 ]_ s < [u1 ]_ s*) -> ti_bounds u v t1 t2 t3 s) /\
      ([t1]_s <= 0 (* [u1 ]_ s <= [v1 ]_ s *) ->
       0 <= [t1 ]_ s + [v ]_ s <= [v ]_ s /\
       - [u ]_ s <= [t2 ]_ s - [u ]_ s <= 0 /\
       - [v ]_ s <= [t3 ]_ s <= [u ]_ s)) /\
     (Zodd [v3 ]_ s \/ Zodd [u3 ]_ s) /\ C5 u3 v3 s}}.
Proof.
move=> Hset Hvu Hvv.

(** t1 <- var_e u1 .-e var_e v1; *)

apply hoare_assign with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * ([u2]_s - [v2 ]_ s) = [u3 ]_ s - [v3]_s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  (0 <= [t3 ]_ s -> Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s/\ Zodd [u3 ]_ s
    /\ [u3 ]_ s = [t3 ]_ s) /\
  ([t3 ]_ s < 0 ->  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [t3 ]_ s /\ Zodd [v3 ]_ s /\
    [v3 ]_ s = - [t3 ]_ s) /\
  [t1]_s = [u1]_s - [v1]_s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  (([v1]_s < [u1]_s -> ti_bounds u v t1 t2 t3 s) /\
   ([u1]_s <= [v1]_s ->  0 <= [t1 ]_ s + [v]_s <= [v ]_ s /\
                        - [u ]_ s <= [t2 ]_ s <= 0 /\
                        - [v ]_ s <= [t3 ]_ s <= [u ]_ s)) /\
  C5 u3 v3 s).

move=> s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [Hinvar1 [Hinvar2 [Hu3 Hv3]]]]]]]].
rewrite /wp_assign /C2.
repeat Store_upd.
repeat (split; first by []).
split.
  split; by [rewrite /= /ZIT.sub -Hui -Hvi; ring | ].
repeat (split; first by []).
split.
  rewrite /uivi_bounds; by repeat Store_upd.
split.
  split=> u1_v1.
    rewrite /ti_bounds in Hinvar2 *.
    repeat Store_upd.
    split; last tauto.
    rewrite /= /ZIT.sub.
    rewrite /uivi_bounds in Hinvar1.
    omega.
  rewrite /ti_bounds in Hinvar2 *.
  repeat Store_upd.
  split; last tauto.
  rewrite /= /ZIT.sub.
  rewrite /uivi_bounds in Hinvar1.
  omega.
rewrite /C5; by repeat Store_upd.

(** t2 <- svar u2 .-e svar v2; *)

apply hoare_assign with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * [t2]_s = [u3 ]_ s - [v3]_s/\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  (0 <= [t3 ]_ s ->
    Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s/\ Zodd [u3 ]_ s /\
    [u3 ]_ s = [t3 ]_ s) /\
  ([t3 ]_ s < 0 ->
    Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [t3 ]_ s/\ Zodd [v3 ]_ s /\
    [v3 ]_ s = - [t3 ]_ s) /\
  [t1]_s = [u1]_s - [v1]_s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  (([v1]_s < [u1]_s -> ti_bounds u v t1 t2 t3 s) /\
   ([u1]_s <= [v1]_s -> 0 <= [t1 ]_ s + [v]_s <= [v ]_ s /\
                        - [u ]_ s <= [t2 ]_ s - [u]_s <= 0 /\
                        - [v ]_ s <= [t3 ]_ s <= [u ]_ s)) /\
  C5 u3 v3 s).

move=> s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [tuv1 [Hinvar1 [Hinvar2 [Hu3 Hv3]]]]]]]]].
rewrite /wp_assign /C2.
repeat Store_upd.
repeat (split; first by []).
split.
  rewrite /uivi_bounds; by repeat Store_upd.
split.
  split=> u1_v1.
    rewrite /ti_bounds in Hinvar2 *.
    repeat Store_upd.
    split; first tauto.
    split; last tauto.
    rewrite /= /ZIT.sub.
    move: {Hinvar2}(proj1 Hinvar2 u1_v1) => Hinvar2.
    rewrite /uivi_bounds in Hinvar1.
    split.
    omega.
    have Htmp : [v3]_s + [v]_s * ([u2]_s - [v2]_s) <= 0.
      have -> : [v3]_s + [v]_s * ([u2]_s - [v2]_s) = [u3 ]_ s - [u ]_ s * ([u1 ]_ s - [v1 ]_ s).
        rewrite !mulZBr in Hti *.
        omega.
      have Htmp : 0 < [u1 ]_ s - [v1 ]_ s.
        omega.
      apply (@leZ_trans ([u ]_ s - [u ]_ s * ([u1 ]_ s - [v1 ]_ s))).
        apply leZ_sub => //; omega.
        have Htmp2 : [u ]_ s <= [u ]_ s * ([u1 ]_ s - [v1 ]_ s).
        apply Zle_scale => //; omega.
      omega.
      apply Zle_plus_0_inv in Htmp; last omega.
      apply Zle_mult_0_inv in Htmp; last omega.
      by [].
  rewrite /ti_bounds in Hinvar2 *.
  repeat Store_upd.
  split; first tauto.
  split; last tauto.
  rewrite /= /ZIT.sub.
  rewrite /uivi_bounds in Hinvar1.
  split; last omega.
  move: {Hinvar2}(proj2 Hinvar2 u1_v1) => Hinvar2.
  suff : 0 <= [u2 ]_ s - [v2 ]_ s by move=> ?; omega.
  have Htmp : - [v]_s * ([u2]_s - [v2]_s) - [v3]_s < 0.
    have -> : - [v ]_ s * ([u2 ]_ s - [v2 ]_ s) - [v3 ]_ s =
      [u]_s * ([u1]_s - [v1]_s) - [u3]_s.
      have Htmp : [u3 ]_ s = [u ]_ s * [t1 ]_ s + [v ]_ s * ([u2 ]_ s - [v2 ]_ s) + [v3 ]_ s.
        omega.
      rewrite Htmp tuv1; ring.
    have Htmp : [u1 ]_ s - [v1 ]_ s <= 0 by omega.
    have {}Htmp : [u ]_ s * ([u1 ]_ s - [v1 ]_ s) <= 0.
      apply mulZ_ge0_le0 => //; omega.
    omega.
  have {}Htmp : - [v ]_ s * ([u2 ]_ s - [v2 ]_ s) < [v3 ]_ s by omega.
  apply/leZP/negPn/negP; rewrite -ltZNge' => /ltZP abs.
  have {}Htmp : - [v ]_ s * ([u2 ]_ s - [v2 ]_ s) < [v]_s by omega.
  rewrite mulNZ -mulZN in Htmp.
  apply Zlt_Zmult_inv' in Htmp; last 2 first.
    omega.
    omega.
    by apply ltZZ in Htmp.
    omega.
rewrite /C5; by repeat Store_upd.

(** t3 <- var_e u3 .-e var_e v3 *)

apply hoare_assign'.
move=> s h [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [tuv1 [Hinvar1 [Hinvar2 [Hu3 Hv3]]]]]]]]].
rewrite /wp_assign /C2 /CVectors.
repeat Store_upd.
repeat (split; first tauto).
split.
  case: (Z_lt_le_dec [t3]_s 0).
  - move/H10 => H10'.
    move: (Zgcd_for_euclid [u3]_s [v3]_s (-1)).
    rewrite mulN1Z addZNE => ->.
    case: H10' => H10' [H10'' ->].
    rewrite Zgcd_opp; tauto.
  - case/H9 => H9' [H9'' /= ->].
    move: (Zgcd_for_euclid [t3]_s [v3]_s (-1)).
    by rewrite mulN1Z addZNE => ->.
split; first by [].
split.
  rewrite /uivi_bounds; by repeat Store_upd.
split.
  split=> v1_u1.
    rewrite /ti_bounds in Hinvar2 *.
    repeat Store_upd.
    repeat (split; first tauto).
    rewrite /= /ZIT.sub.
    rewrite /uivi_bounds in Hinvar1.
    omega.
  rewrite /ti_bounds in Hinvar2 *.
  repeat Store_upd.
  repeat (split; first tauto).
  rewrite /= /ZIT.sub.
  rewrite /uivi_bounds in Hinvar1; omega.
split; last by rewrite /C5; repeat Store_upd.
case: (Z_lt_le_dec [t3]_s 0) => [/H10 | /H9]; tauto.
Qed.

Lemma subtract_triple :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) ->  0 < vu -> 0 < vv ->
  {{ fun s _ => C2 vu vv u v g s /\
     (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
     CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
     (0 <= [t3 ]_ s ->
      Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\
      Zodd [u3 ]_ s /\ [u3 ]_ s = [t3 ]_ s) /\
     ([t3 ]_ s < 0 ->
      Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [t3 ]_ s /\
      Zodd [v3 ]_ s /\ [v3 ]_ s = - [t3 ]_ s) /\
     uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
     ti_bounds u v t1 t2 t3 s /\ C5 u3 v3 s}}
   BEGCD_TAOCP.subtract u v u1 u2 u3 v1 v2 v3 t1 t2 t3
   {{ fun s _ => C2 vu vv u v g s /\
     (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
     CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
     C4 u3 v3 t3 s /\
     C5 u3 v3 s /\
     Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
     uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\ ti_bounds u v t1 t2 t3 s}}.
Proof.
move=> Hset Hvu Hvv.
rewrite /BEGCD_TAOCP.subtract.

apply while.hoare_seq with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  [t3]_s = [u3]_s - [v3]_s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\
  [t1]_s = [u1]_s - [v1]_s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ((0 < [t1]_s -> ti_bounds u v t1 t2 t3 s) /\
   ([t1]_s <= 0 -> 0 <= [t1 ]_ s + [v]_s <= [v ]_ s /\
                        - [u ]_ s <= [t2 ]_ s - [u]_s <= 0 /\
                        - [v ]_ s <= [t3 ]_ s <= [u ]_ s)) /\
  (Zodd [v3 ]_ s \/ Zodd [u3 ]_ s) /\
  C5 u3 v3 s).

exact: subtract_part1.

apply while.hoare_ifte.

apply hoare_assign with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  ([u ]_ s * [t1 ]_ s + [v ]_ s * ([t2]_s - [u]_s) = [t3 ]_ s /\
   [u ]_ s * [u1 ]_ s + [v ]_ s * [u2 ]_ s = [u3 ]_ s /\
   [u ]_ s * [v1 ]_ s + [v ]_ s * [v2 ]_ s = [v3 ]_ s) /\
  [t3 ]_ s = [u3 ]_ s - [v3 ]_ s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\
  [u1]_s <= [v1]_s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  (0 <= [t1 ]_ s <= [v ]_ s /\
   - [u ]_ s <= [t2 ]_ s - [u]_s <= 0 /\
   - [v ]_ s <= [t3 ]_ s <= [u ]_ s) /\
  (Zodd [v3 ]_ s \/ Zodd [u3 ]_ s) /\
  C5 u3 v3 s).

move=> s h.
case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [H11 [tuv1 [Hinvar1 [Hinvar2 [H12 [Hu3 Hv3]]]]]]]]]] H1].
rewrite /wp_assign /C2.
repeat Store_upd.
repeat (split; first by []).
split.
  split; by [rewrite /= /ZIT.add -Hti; ring | ].
repeat (split; first by []).
split.
  rewrite /= /hoare_m.eval_b /ZIT.geb /= in H1.
  move/geZP : H1 => ?; omega.
split.
  rewrite /uivi_bounds; by repeat Store_upd.
split.
  rewrite /ti_bounds in Hinvar2 *.
  repeat Store_upd.
  have u1_v1 : [u1 ]_ s <= [v1 ]_ s.
    rewrite /= /hoare_m.eval_b /ZIT.geb /= in H1.
    move/geZP : H1 => ?; omega.
  move/geZP in H1.
  split; last omega.
  rewrite /= /ZIT.add.
  rewrite /ti_bounds in Hinvar1.
  omega.
rewrite /C5; by repeat Store_upd.

apply hoare_assign' => s h.
case=> [[Hu [Hv [Hg [u_g v_g]]]] [H5 [[Hti [Hui Hvi]] [H9 [H10 [uv1 [Hinvar1 [Hinvar2 [H11 [Hu3 Hv3]]]]]]]]]].
rewrite /wp_assign /C2 /C4 /C5 /CVectors.
repeat Store_upd.
repeat (split; first by []).
split; first by exists O; right; right; rewrite /= mulZ1.
repeat (split; first by []).
split.
  rewrite -(Zgcd_for_euclid [u3]_s [v3]_s (-1)) mulN1Z addZNE.
  rewrite H9 -u_g -v_g -2!(mulZC [g]_s) Zgcd_mult in H10; last omega.
  apply eqZ_mul2l in H10 => //; omega.
split.
  rewrite /uivi_bounds.
  by repeat Store_upd.
rewrite /ti_bounds in Hinvar2 *.
repeat Store_upd.
split; first tauto.
split; last tauto.
rewrite /= /ZIT.sub.
rewrite /uivi_bounds in Hinvar1.
omega.

apply hoare_skip' => s h.
case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [H11 [tuv1 [Hinvar1 [Hinvar2 [H12 [Hu3 Hv3]]]]]]]]]] H1].
rewrite /wp_assign /C2.
repeat Store_upd.
repeat (split; first by []).
split.
  exists O; right; right; by rewrite /= mulZ1.
repeat (split; first by []).
split.
  rewrite -(Zgcd_for_euclid [u3]_s [v3]_s (-1)) mulN1Z addZNE.
  rewrite H10 -v_g -u_g -2!(mulZC [g]_s) Zgcd_mult in H11; last omega.
  apply eqZ_mul2l in H11 => //; omega.
split; first by [].
rewrite /= /hoare_m.eval_b /ZIT.geb /= in H1.
move/geZP in H1.
apply (proj1 Hinvar2); omega.
Qed.

Lemma triple_intermediate_invariant :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) ->  0 < vu -> 0 < vv ->
  {{ fun s h => (C2 vu vv u v g s /\
    (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
    CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
    C4 u3 v3 t3 s /\
    C5 u3 v3 s /\
    Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\ ti_bounds u v t1 t2 t3 s) /\
  [ var_e t3 \!= nat_e 0 ]b_ s}}
  while.while (var_e t3 \% nat_e 2 \= nat_e 0) (BEGCD_TAOCP.halve u v t1 t2 t3);
  BEGCD_TAOCP.reset u v u1 u2 u3 v1 v2 v3 t1 t2 t3;
  BEGCD_TAOCP.subtract u v u1 u2 u3 v1 v2 v3 t1 t2 t3
  {{ fun s h => C2 vu vv u v g s /\
    (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
    CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
    C4 u3 v3 t3 s /\
    C5 u3 v3 s /\
    Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\ ti_bounds u v t1 t2 t3 s }}.
Proof.
move=> Hset Hvu Hvv.
apply while.hoare_seq with (fun s h => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [v3 ]_ s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  Zodd [t3]_s).
exact: while_halve.
apply while.hoare_seq with (fun s _ => C2 vu vv u v g s /\
  (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  (0 <= [t3]_s -> Z.gcd vu vv = [g ]_ s * Z.gcd [t3 ]_ s [v3 ]_ s /\ Zodd [u3]_s /\
    [u3]_s = [t3]_s) /\
  ([t3]_s < 0 -> Z.gcd vu vv = [g ]_ s * Z.gcd [u3 ]_ s [t3 ]_ s /\ Zodd [v3]_s /\
    [v3]_s = - [t3]_s) /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s /\
  C5 u3 v3 s).
exact: reset_triple.
exact: subtract_triple.
Qed.

Lemma triple_intermediate_invariant_stren :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) -> 0 < vu -> 0 < vv ->
  while.entails hoare_m.store hoare_m.heap
  (fun s _ =>
    C2 vu vv u v g s /\
    C3 vu vv u v g s /\
    uivi_init u v u1 u2 u3 v1 v2 v3 s /\
    ti_init u v t1 t2 t3 s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\ ti_bounds u v t1 t2 t3 s)
  (fun s _ =>
    C2 vu vv u v g s /\
    (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
    CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
    C4 u3 v3 t3 s /\
    C5 u3 v3 s /\
    Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\ ti_bounds u v t1 t2 t3 s).
Proof.
move=> Hset Hvv Hvu.
rewrite /while.entails => s h.
case => [[Hu [Hv [Hg [u_g v_g]]]] [[Hgcd Hcond] [[Hu1 [Hu2 [Hu3 [Hv1 [Hv2 Hv3]]]]] [Ht [Hinvar1 Hinvar2]]]]].
rewrite /CVectors Hu1 Hu2 Hu3 Hv1 Hv2 Hv3.
repeat (split; first tauto).
case: (Zeven_odd_dec [u]_s) => u_parity.
- case: Ht => _.
  move/(_ u_parity) => [Ht1 [Ht2 Ht3]].
  rewrite /C2 /C4 /C5 Ht1 Ht2 Ht3 Hu3 Hv3 mulZ1 mulZ0 addZ0.
  repeat (split; first by []).
  split.
    move/negP : Hcond => /=.
    rewrite negb_and /ZIT.eqb /ZIT.rem /=.
    case/orP => /eqP X.
    + left; exact: not_Zmod_2_Zodd.
    + right; exact: not_Zmod_2_Zodd.
  split.
    repeat (split; first by []).
    ring.
  split; last by [].
  exists O; rewrite [_ ^^ _]/= !mulZ1; right; left.
  split; first by reflexivity.
  move/negP : Hcond => /=.
  rewrite negb_and /ZIT.eqb /ZIT.rem.
  case/orP => /eqP.
  + move/not_Zmod_2_Zodd; by move/Zodd_not_Zeven.
  + by move/not_Zmod_2_Zodd.
- case: Ht.
  move/(_ u_parity) => [Ht1 [Ht2 Ht3]] _.
  rewrite Ht1 Ht2 Ht3 /C4 /C5 Hu3 Hv3 mulZ1 mulZ0 add0Z mulZ0 addZ0.
  repeat (split; first by []).
  split.
    move/negP : Hcond => /=.
    rewrite negb_and /ZIT.eqb /ZIT.rem /=.
    case/orP => /eqP X.
    * left; exact: not_Zmod_2_Zodd.
    * right; exact: not_Zmod_2_Zodd.
  split.
    split; first by ring.
    split; by [| ring].
  split; last by [].
  exists O; rewrite [_ ^^ _]/= !mulZ1; tauto.
Qed.

Lemma triple_intermediate_invariant_weak :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) -> 0 < vu -> 0 < vv ->
  while.entails hoare_m.store hoare_m.heap
  (fun s h => (C2 vu vv u v g s /\
    (Zodd [u ]_ s \/ Zodd [v ]_ s) /\
    CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
    C4 u3 v3 t3 s /\
    C5 u3 v3 s /\
    Z.gcd [u ]_ s [v ]_ s = Z.gcd [u3 ]_ s [v3 ]_ s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\ ti_bounds u v t1 t2 t3 s) /\
  ~~ [ var_e t3 \!= nat_e 0 ]b_ s)
  (fun s _ =>
    vu * [u1 ]_ s + vv * [u2 ]_ s = [g ]_ s * [u3 ]_ s /\
    Z.gcd vu vv = [g ]_ s * [u3 ]_ s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\ ti_bounds u v t1 t2 t3 s).
Proof.
move=> Hset Hvv Hvu.
- rewrite /while.entails => s h.
  case => [[[Hu [Hv [Hg [u_g v_g]]]] [H6 [[Hti [Hui Hvi]] [H10 [[Hu3 Hv3] [H12 [H14 [Hinvar1 Hinvar2]]]]]]]] H1].
  split; first by rewrite -u_g -v_g -Hui; ring.
  rewrite /hoare_m.eval_b /= /ZIT.eqb in H1.
  move/negPn : H1 => /eqP H1.
  case: H10 => k.
  case => [H10|].
  + have abs : [v3 ]_ s = 0.
      move: (expZ_gt0 k) => ?.
      case: H10 => H10 H10'.
      rewrite H1 mul0Z in H10; omega.
    rewrite abs Zgcd_0 Z.abs_eq in H12; last omega.
    rewrite -H12 -Zgcd_mult; last omega.
    by rewrite mulZC u_g mulZC v_g.
  + case => H10.
    * have abs : [u ]_ s = 0.
        rewrite H1 mul0Z in H10; omega.
      rewrite abs in Hu; by apply ltZZ in Hu.
    * have abs : [u3 ]_ s = [v3 ]_ s.
        rewrite H1 mul0Z in H10; omega.
      rewrite -abs Zgcd_same in H12; last omega.
      rewrite -H12 -u_g -v_g -Zgcd_mult; last omega.
      by rewrite (mulZC [u ]_ s) (mulZC [v ]_ s).
Qed.

Lemma triple_intermediate :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) -> 0 < vu -> 0 < vv ->
  ({{fun s _ => C2 vu vv u v g s /\ C3 vu vv u v g s /\
    uivi_init u v u1 u2 u3 v1 v2 v3 s /\
    ti_init u v t1 t2 t3 s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
    ti_bounds u v t1 t2 t3 s }}
  while.while (var_e t3 \!= nat_e 0)
  (while.while (var_e t3 \% nat_e 2 \= nat_e 0) (BEGCD_TAOCP.halve u v t1 t2 t3);
    BEGCD_TAOCP.reset u v u1 u2 u3 v1 v2 v3 t1 t2 t3;
    BEGCD_TAOCP.subtract u v u1 u2 u3 v1 v2 v3 t1 t2 t3)
  {{fun s _ =>
    vu * [u1 ]_ s + vv * [u2 ]_ s = [g ]_ s * [u3 ]_ s /\
    Z.gcd vu vv = [g ]_ s * [u3 ]_ s /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
    ti_bounds u v t1 t2 t3 s }})%seplog_hoare.
Proof.
move=> Hset Hvv Hvu.
apply hoare_prop_m.hoare_while_invariant with (fun s _ =>
  C2 vu vv u v g s /\
  (Zodd [u]_s \/ Zodd [v]_s) /\
  CVectors u v u1 u2 u3 v1 v2 v3 t1 t2 t3 s /\
  C4 u3 v3 t3 s /\
  C5 u3 v3 s /\
  Z.gcd [u]_s [v]_s = Z.gcd [u3]_s [v3]_s /\
  uivi_bounds u v u1 v1 u2 v2 u3 v3 s /\
  ti_bounds u v t1 t2 t3 s).
exact: triple_intermediate_invariant_stren.
exact: triple_intermediate_invariant_weak.
exact: triple_intermediate_invariant.
Qed.

Lemma triple :
  uniq(g, u, v, u1, u2, u3, v1, v2, v3, t1, t2, t3) -> 0 < vu -> 0 < vv ->
  ({{ fun st _ => uv_init vu vv u v st }}
  BEGCD_TAOCP.begcd g u v u1 u2 u3 v1 v2 v3 t1 t2 t3
  {{ fun st _ =>
    vu * [u1]_st + vv * [u2]_st = [g]_st * [u3]_st /\
    Z.gcd vu vv = ([g]_st * [u3]_st) /\
    uivi_bounds u v u1 v1 u2 v2 u3 v3 st /\
    ti_bounds u v t1 t2 t3 st
  }})%seplog_hoare.
Proof.
move=> Hset Hvu Hvv.
rewrite /BEGCD_TAOCP.begcd.
do 2 apply hoare_prop_m.hoare_seq_assoc'.
eapply while.hoare_seq.
  apply hoare_prop_m.hoare_seq_assoc.
  exact: triple_init.
exact: triple_intermediate.
Qed.

End begcd_taocp_cor.

End BEGCD_TAOCP_COR.

End EGCD.

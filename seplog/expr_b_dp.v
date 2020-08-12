(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Max Lia.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext.
Require Import seplog integral_type.

(**
  The goal of this decision procedure:

  prove that for every environment a system of arithmetic constraints is true
  ==>
  We try to eliminate all the variables, such that to evaluate the system
  we do not need an environment (and thus this evaluation is the same for
  every environment)

  Note: in fact we negate the formula of the system and find if
  for every environment its evaluation is false
  ( comes from the fact that ~ forall x, P x <-> exists x, ~ P x )
*)

(*
  some references:
  http://users.rsise.anu.edu.au/~michaeln/pubs/arith-dp-slides.pdf
  http://users.rsise.anu.edu.au/~michaeln/pubs/omega-slides.pdf
  http://cs156.stanford.edu/notes/dp-4.pdf
*)

Local Close Scope Z_scope.
Local Close Scope positive_scope.

Module Import seplog_Z_m := Seplog ZIT.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.

Definition andb_option (a b : option bool) :=
  match a with
    | None => None
    | Some a' => match b with
                   | None => None
                   | Some b' => Some (andb a' b')
                 end
  end.

Definition orb_option (a b : option bool) :=
  match a with
    | None => None
    | Some a' => match b with
                   | None => None
                   | Some b' => Some (orb a' b')
                 end
  end.

(** We put a formula of expr_b into the disjunctive normal form
   (... /\ ...) \/ (... /\ ...)
   This is perform in three steps:
   1) we propagate negation to final constructor
   2) we translate the expr_b formula into a orlist (data-structure
      representing a disjunctive normal form), and we replace final
      (possibly negative) constructor by counter part of form >= *)

(** step 1: propagation of negation *)
Fixpoint neg_propagate (b : expr_b) (n : bool) : expr_b :=
  match b with
    | neg_b b1 => neg_propagate b1 (negb n)
    | b1 \&& b2 =>
      if n then
        (neg_propagate b1 true) \|| (neg_propagate b2 true)
      else
        (neg_propagate b1 false) \&& (neg_propagate b2 false)
    | b1 \|| b2 =>
      if n then
        (neg_propagate b1 true) \&& (neg_propagate b2 true)
      else
        (neg_propagate b1 false) \|| (neg_propagate b2 false)
    | _ => if n then neg_b b else b
  end.

(** Propagation of negation preserves the semantics of a formula *)
Lemma neg_propagate_preserve : forall b n s,
  [ neg_propagate b n ]b_ s = [ if n then (neg_b b) else b ]b_ s.
Proof.
induction b; simpl; intros; auto.
- rewrite IHb.
  destruct n; simpl; auto.
  by rewrite negbK.
- destruct b1.
  + destruct n; simpl; rewrite IHb1; rewrite IHb2; simpl; auto.
    by rewrite negb_and.
  + destruct n; simpl; rewrite IHb1; rewrite IHb2; simpl; auto.
    by rewrite negb_or.
Qed.

(** we now prove the correctness of the function bneg_propagate. We
   first build the predicate is_bneg_propagate, which asserts that no
   connectives is under a negation *)

Inductive is_neg_propagate : expr_b -> Prop :=
(* atomic boolean expression are valid formulas *)
| true_b_is_neg_propagate: is_neg_propagate true_b
| eq_b_is_neg_propagate: forall e1 e2, is_neg_propagate (e1 \= e2)
| neq_b_is_neg_propagate: forall e1 e2, is_neg_propagate (e1 \!= e2)
| ge_b_is_neg_propagate: forall e1 e2, is_neg_propagate (e1 \>= e2)
| gt_b_is_neg_propagate: forall e1 e2, is_neg_propagate (e1 \> e2)
(* if a boolean expression is negative, its size must be 1, which means that it is an atomic formula*)
| neg_b_is_neg_propagate: forall e, Expr_B_size e = 1 -> is_neg_propagate (neg_b e)
(* formulas on both size of connective must be valid formulas *)
| and_b_is_neg_propagate: forall e1 e2,
  is_neg_propagate e1 -> is_neg_propagate e2 ->
  is_neg_propagate (e1 \&& e2)
| or_is_neg_propagate: forall e1 e2,
  is_neg_propagate e1 -> is_neg_propagate e2 ->
  is_neg_propagate (e1 \|| e2).

Lemma neg_propagate_correct : forall b n, is_neg_propagate (neg_propagate b n).
Proof.
induction b; simpl; intros.
- destruct n; constructor; auto.
- destruct b; destruct n; constructor; auto.
- apply IHb.
- destruct b1.
  + destruct n; constructor; intuition.
  + destruct n; constructor; intuition.
Qed.

(** step 2: put in normal disjunctive form *)

(** definitions of arithmetic constraints and normal forms *)

Definition constraint := expr.

Definition constraint_sem (c : constraint) : expr_b := (nat_e 0) \>= c.

(** andlists representent conjunctions of constraints *)
Definition andlist := list constraint.

Fixpoint andlist_sem (l : andlist) : expr_b :=
 match l with
   | nil => true_b
   | hd :: tl => (constraint_sem hd) \&& (andlist_sem tl)
 end.

Definition andlist_plus (c1 c2 : andlist) : andlist := c1 ++ c2.

Lemma andlist_plus_sem : forall l1 l2 s,
  [ andlist_sem (andlist_plus l1 l2) ]b_ s =
  [ (andlist_sem l1) \&& (andlist_sem l2) ]b_ s.
Proof.
induction l1; simpl; intros; auto.
by rewrite IHl1 andbA.
Qed.

(** an orlist is a disjunction of andlists *)
Definition orlist := list andlist.

Fixpoint orlist_sem (l : orlist) : expr_b :=
  match l with
    | nil => \~ true_b
    | hd :: tl => (andlist_sem hd) \|| (orlist_sem tl)
  end.

Definition orlist_plus (d1 d2 : orlist) : orlist := d1 ++ d2.

Lemma orlist_plus_sem : forall b1 b2 s,
  [ orlist_sem (orlist_plus b1 b2) ]b_s =
  [ orlist_sem b1 ]b_s || [ orlist_sem b2 ]b_s.
Proof. elim=> //= hd tl IH b2 s; by rewrite IH orbA. Qed.

Fixpoint andlist_mult_orlist (c : andlist) (d : orlist) {struct d} : orlist :=
  match d with
    | nil => nil
    | hd :: tl => orlist_plus ((andlist_plus c hd) :: nil) (andlist_mult_orlist c tl)
  end.

Lemma andlist_mult_orlist_sem: forall b2 b1 s,
  [ orlist_sem (andlist_mult_orlist b1 b2) ]b_s =
  [ andlist_sem b1 ]b_s && [ orlist_sem b2 ]b_s.
Proof.
induction b2; simpl; intros; auto.
- by rewrite andbC.
- by rewrite IHb2 andb_orr andlist_plus_sem.
Qed.

Fixpoint orlist_mult_orlist (d1 d2 : orlist) {struct d1} : orlist :=
  match d1 with
    | nil => nil
    | hd :: tl => orlist_plus (andlist_mult_orlist hd d2) (orlist_mult_orlist tl d2)
  end.

Lemma orlist_mult_orlist_sem: forall b1 b2 s,
  [ orlist_sem (orlist_mult_orlist b1 b2) ]b_ s =
  [ orlist_sem b1 ]b_s && [ orlist_sem b2 ]b_s.
Proof.
induction b1; simpl; intros; auto.
by rewrite orlist_plus_sem IHb1 andb_orl andlist_mult_orlist_sem.
Qed.

(** the main function of step 2 *)
Fixpoint disj_nf (b : expr_b) : orlist :=
  match b with
    | e1 \&& e2 =>
      orlist_mult_orlist (disj_nf e1) (disj_nf e2)
    | e1 \|| e2 =>
      orlist_plus (disj_nf e1) (disj_nf e2)
    | neg_b b1 =>
      match b1 with
        | true_b => (nat_e 1 :: nil) :: nil
        | e1 \= e2 => ((e1 \+ nat_e 1 \- e2) :: nil) :: ((e2 \+ nat_e 1 \- e1) :: nil) :: nil
        | e1 \!= e2 => ((e1 \- e2) :: (e2 \- e1) :: nil) :: nil
        | e1 \>= e2 => ((e1 \+ nat_e 1 \- e2) :: nil) :: nil
        | e1 \> e2 => ((e1 \- e2) :: nil) :: nil
        | _ => nil
      end
    | true_b => (nat_e 0 :: nil) :: nil
    | e1 \= e2 => ((e1 \- e2) :: (e2 \- e1)::nil) :: nil
    | e1 \!= e2 => ((e1 \+ nat_e 1 \- e2) :: nil) :: ((e2 \+ nat_e 1 \- e1)::nil) :: nil
    | e1 \>= e2 => ((e2 \- e1) :: nil) :: nil
    | e1 \>e2 => ((e2 \+ nat_e 1 \- e1)::nil) :: nil
  end.

(** disj_nf preserves the semantics of neg_propagated formula *)

Lemma disj_nf_preserve : forall b, is_neg_propagate b ->
  forall s, [ orlist_sem (disj_nf b) ]b_ s = [ b ]b_ s.
Proof.
induction b; simpl; intros; auto.
- destruct b => //=.
  + open_integral_type_goal => /=.
    rewrite andbT orbF.
    case/boolP : (0 >=? _ - _)%Z => [/geZP H0|] /=.
      case/boolP : (0 >=? _ - _)%Z => [/geZP H1|] /=.
        apply/esym/eqP; lia.
      rewrite Z.geb_leb -ltZNge' => /ltZP H1.
      apply/esym/eqP; lia.
    rewrite Z.geb_leb -ltZNge' => /ltZP H0.
    apply/esym/eqP; lia.
  + open_integral_type_goal => /=.
    rewrite 2!andbT orbF.
    case/boolP : (0 >=? _ - _)%Z => [/geZP H0|] /=.
      apply/esym/eqP; lia.
    rewrite Z.geb_leb -ltZNge' => /ltZP H0.
    case/boolP : (0 >=? _ - _)%Z => [/geZP H1|] /=.
      apply/esym/eqP; lia.
    rewrite Z.geb_leb -ltZNge' => /ltZP H1.
    apply/esym/eqP; lia.
  + open_integral_type_goal.
    rewrite andbT orbF.
    case/boolP : (0 >=? _ - _)%Z => [/geZP H0|] /=.
      case/boolP : (_ >=? _)%Z => [/geZP H1|] //=.
      rewrite Z.geb_leb -ltZNge' => /ltZP H1; lia.
    rewrite Z.geb_leb -ltZNge' => /ltZP H0.
    apply/esym/negbTE.
    rewrite Z.geb_leb -ltZNge'; apply/ltZP; lia.
  + repeat open_integral_type_goal.
    rewrite andbT orbF.
    case/boolP : (0 >=? _ - _)%Z => [/geZP H0|] /=.
      apply/esym/gtZP; lia.
    rewrite Z.geb_leb -ltZNge' => /ltZP H0.
    apply/esym/negbTE.
    rewrite Z.gtb_ltb ltZNge' negbK; apply/leZP; lia.
- destruct b; simpl; auto.
  + destruct b => //=.
    * open_integral_type_goal.
      rewrite 2!andbT orbF.
      case/boolP : (0 >=? _)%Z => [/geZP H0|] /=.
        apply/esym/eqP; lia.
      rewrite Z.geb_leb -ltZNge' => /ltZP H0.
      case/boolP : (0 >=? _)%Z => [/geZP H1|] /=.
        apply/esym/eqP; lia.
      rewrite Z.geb_leb -ltZNge' => /ltZP H1.
      apply/esym/eqP; lia.
    * open_integral_type_goal.
      rewrite andbT orbF.
      case/boolP : (0 >=? _)%Z => [/geZP H0|] /=.
        case/boolP : (0 >=? _)%Z => [/geZP H1|] /=.
          rewrite negbK; apply/esym/eqP; lia.
        rewrite Z.geb_leb -ltZNge' => /ltZP H1.
        rewrite negbK; apply/esym/eqP; lia.
      rewrite Z.geb_leb -ltZNge' => /ltZP H0.
      rewrite negbK; apply/esym/eqP; lia.
    * open_integral_type_goal.
      rewrite andbT orbF.
      case/boolP : (0 >=? _)%Z => [/geZP H0|] /=.
        rewrite Z.geb_leb -ltZNge'; apply/esym/ltZP; lia.
      rewrite Z.geb_leb -ltZNge' => /ltZP H0.
      rewrite Z.geb_leb -ltZNge'; apply/esym/ltZP; lia.
    * open_integral_type_goal.
      rewrite andbT orbF.
      case/boolP : (0 >=? _)%Z => [/geZP H0|] /=.
        rewrite Z.gtb_ltb ltZNge' negbK; apply/esym/leZP; lia.
      rewrite Z.geb_leb -ltZNge' => /ltZP H0.
      rewrite Z.gtb_ltb ltZNge' negbK; apply/esym/leZP; lia.
  + inversion_clear H; simpl in H0; generalize (expr_b_min_size b); intros; assert (False); [ssromega | contradiction].
    inversion_clear H; simpl in H0;
      generalize (expr_b_min_size b2); generalize (expr_b_min_size b3); intros; assert (False); [ssromega | contradiction].
- inversion_clear H.
  + by rewrite -(IHb1 H0) -(IHb2 H1) orlist_mult_orlist_sem.
  + by rewrite -(IHb1 H0) -(IHb2 H1) orlist_plus_sem.
Qed.

(** We compose both step in one *)
Definition expr_b2constraints (b : expr_b) : orlist := disj_nf (neg_propagate b false).

Lemma expr_b2constraints_correct: forall b s,
  [ orlist_sem (expr_b2constraints b) ]b_ s = [ b ]b_ s.
Proof.
intros.
rewrite /expr_b2constraints disj_nf_preserve.
by rewrite neg_propagate_preserve.
by apply neg_propagate_correct.
Qed.

Local Open Scope Z_scope.

(** return Some z where z is the value of the expression if this expression is variable-free, None o.w. *)
(* TODO: fonction d'interpretation pour les binops? *)
Fixpoint expr_compute (e : expr) : option Z :=
   match e with
     | var_e x => None
     | cst_e x => Some x
     | e1 \+ e2 => match expr_compute e1 with
                     | None => None
                     | Some e1' =>
                       match expr_compute e2 with
                         | None => None
                         | Some e2' => Some (ZIT.add e1' e2')
                       end
                   end
     | e1 \- e2 => match expr_compute e1 with
                     | None => None
                     | Some e1' =>
                       match expr_compute e2 with
                         | None => None
                         | Some e2' => Some (ZIT.sub e1' e2')
                       end
                   end
     | e1 \* e2 => match expr_compute e1 with
                     | None =>
                       match expr_compute e2 with
                         | None => None
                         | Some e2' => if e2' == 0 then Some 0 else None
                       end
                     | Some e1' =>
                       if e1' == 0 then Some 0 else
                         match expr_compute e2 with
                           | None => None
                           | Some e2' => Some (e1' * e2') (*TODO: * -> ZIT.t_mult? *)
                         end
                   end
     | _ => None
   end.

(** if an arithmetic expression can be evaluated without environment, this value is correct *)
Lemma expr_compute_correct : forall e z, expr_compute e = Some z ->
  forall s, [ e ]e_s = z.
Proof.
induction e => //; intros; simpl in H; simpl.
- by case: H.
- destruct b => //.
  + destruct (expr_compute e1) => //.
    destruct (expr_compute e2) => //.
    case: H => H.
    subst z.
    by rewrite (IHe1 z0) // (IHe2 z1).
  + destruct (expr_compute e1) => //.
    destruct (expr_compute e2) => //.
    case: H => H.
    subst z.
    by rewrite (IHe1 z0) // (IHe2 z1).
  + destruct (expr_compute e1) => //.
    * destruct (expr_compute e2) => //.
      - case/boolP : (z0 == 0) => [/eqP H0 | H0].
          rewrite H0 eqxx in H; case: H => <-.
          by rewrite (IHe1 z0) // (IHe2 z1) // H0.
        rewrite (negbTE H0) in H; case: H => <-.
        by rewrite (IHe1 z0) // (IHe2 z1).
      - case/boolP : (z0 == 0) => [/eqP H0 | H0].
          rewrite H0 eqxx in H; case: H => <-.
          by rewrite (IHe1 z0) // H0.
        by rewrite (negbTE H0) in H.
    * destruct (expr_compute e2) => //.
      case/boolP : (z0 == 0) => [/eqP H0 | H0].
        rewrite H0 eqxx in H; case: H => <-.
        rewrite (IHe2 z0) // H0 /=.
        open_integral_type_goal.
        by rewrite mulZ0.
      by rewrite (negbTE H0) in H.
  Qed.

Fixpoint simpl_expr' (e : expr) : expr :=
  match e with
    | var_e v => var_e v
    | cst_e z => cst_e z
    | e1 \+ e2 =>
      match expr_compute (simpl_expr' e1) with
        | None =>
          match expr_compute (simpl_expr' e2) with
            | None => e
            | Some e2' => if e2' == 0 then e1 else e1 \+ cst_e e2'
          end
        | Some e1' =>
          if e1' == 0 then
            match expr_compute (simpl_expr' e2) with
              | None => e2
              | Some e2' => if e2' == 0 then cst_e 0 else cst_e e2'
            end
          else
            match expr_compute (simpl_expr' e2) with
              | None => cst_e e1' \+ e2
              | Some e2' => if e2' == 0 then cst_e e1' else cst_e (e1' + e2')
            end
      end
    | e1 \- e2 =>
      match expr_compute (simpl_expr' e1) with
        | None =>
          match expr_compute (simpl_expr' e2) with
            | None => e
            | Some e2' =>
              if e2' == 0 then e1 else e1 \- cst_e e2'
          end
        | Some e1' =>
          if e1' == 0 then
            match expr_compute (simpl_expr' e2) with
                | None => (cst_e 0 \- e2)
                | Some e2' => if e2' == 0 then cst_e 0 else cst_e ( - e2')
              end
          else
            match expr_compute (simpl_expr' e2) with
              | None => cst_e e1' \- e2
              | Some e2' => if e2' == 0 then cst_e e1' else cst_e (e1' - e2')
            end
      end
    | e1 \* e2 =>
      match expr_compute (simpl_expr' e1) with
        | None =>
          match expr_compute (simpl_expr' e2) with
            | None => e
            | Some e2' =>
              if e2' == 0 then cst_e 0 else
              if e2' == 1 then e1 else e1 \* (cst_e e2')
          end
        | Some e1' =>
          if e1' == 0 then
            cst_e 0
          else
            if e1' == 1 then
              match expr_compute (simpl_expr' e2) with
              | None => e2
              | Some e2' => if e2' == 0 then cst_e 0 else cst_e e2'
              end
            else
              match expr_compute (simpl_expr' e2) with
              | None => (cst_e e1') \* e2
              | Some e2' =>
                if e2' == 0 then cst_e 0 else
                if e2' == 1 then cst_e e1' else cst_e (e1' * e2')
              end
      end
    | _ => e
  end.

Lemma simpl_expr'_correct: forall e s, [ e ]e_s = [ simpl_expr' e ]e_s.
Proof.
induction e; simpl; auto.
destruct b => //.
- move: (expr_compute_correct (simpl_expr' e1)) => H s.
  destruct (expr_compute (simpl_expr' e1)).
  + move: {H}(H z (refl_equal _) s) => H.
    rewrite -IHe1 in H.
    case/boolP : (z == 0) => [/eqP |] H0.
    * move: (expr_compute_correct (simpl_expr' e2)) => H1.
      destruct (expr_compute (simpl_expr' e2)).
      - move: {H1}(H1 z0 (refl_equal _) s) => H1.
        rewrite -IHe2 in H1.
        case/boolP : (z0 == 0) => [/eqP |] H2.
        + by rewrite /= H H1 H0 H2.
        + by rewrite H H1 H0.
      - by rewrite {H1} H H0.
    * move: (expr_compute_correct (simpl_expr' e2)) => H1.
      destruct (expr_compute (simpl_expr' e2)).
      move: {H1}(H1 z0 (refl_equal _) s) => H1.
      rewrite -IHe2 in H1.
      case/boolP : (z0 == 0) => [/eqP |] H2.
        by rewrite H H1 /= H2 /ZIT.add addZC.
      by rewrite H H1.
      by simpl; rewrite /ZIT.add H.
  + move: (expr_compute_correct (simpl_expr' e2)) => H0.
    destruct (expr_compute (simpl_expr' e2)) => //.
    move: {H0}(H0 z (refl_equal _) s) => H0.
    rewrite -IHe2 in H0.
    case/boolP : (z == 0) => [/eqP |] H1.
    - by rewrite H0 /= H1 /ZIT.add addZC.
    - by rewrite H0.
- move: (expr_compute_correct (simpl_expr' e1)) => H s.
  destruct (expr_compute (simpl_expr' e1)).
  move: {H}(H z (refl_equal _) s) => H.
  rewrite -IHe1 in H.
  case/boolP : (z == 0) => [/eqP |] H0.
  move: (expr_compute_correct (simpl_expr' e2)) => H1.
  destruct (expr_compute (simpl_expr' e2)).
  move: {H1}(H1 z0 (refl_equal _) s) => H1.
  rewrite -IHe2 in H1.
  case/boolP : (z0 == 0) => [/eqP |] H2.
  by rewrite H H1 H0 H2.
  by rewrite H H1 H0.
  by rewrite {H1} H H0.
  move: (expr_compute_correct (simpl_expr' e2)) => H1.
  destruct (expr_compute (simpl_expr' e2)).
  move: {H1}(H1 z0 (refl_equal _) s) => H1.
  rewrite -IHe2 in H1.
  case/boolP : (z0 == 0) => [/eqP |] H2.
  rewrite H H1 H2 /=.
  open_integral_type_goal; by rewrite subZ0.
  by rewrite H H1.
  by rewrite -H.
  move: (expr_compute_correct (simpl_expr' e2)) => H0.
  destruct (expr_compute (simpl_expr' e2)) => //.
  move: {H0}(H0 z (refl_equal _) s) => H0.
  rewrite -IHe2 in H0.
  case/boolP : (z == 0) => [/eqP|] H1.
  rewrite H0 H1 /=.
  open_integral_type_goal; by rewrite subZ0.
  by rewrite H0.
- move: (expr_compute_correct (simpl_expr' e1)) => H s.
  destruct (expr_compute (simpl_expr' e1)).
  + move: {H}(H z (refl_equal _) s) => H.
    rewrite -IHe1 in H.
    case/boolP : (z == 0) => [/eqP |] H0.
    * subst z; by rewrite H0.
    * case/boolP : (z == 1) => [/eqP |] H1.
      - subst z.
        rewrite H1.
        move: (expr_compute_correct (simpl_expr' e2)) => H2.
        destruct (expr_compute (simpl_expr' e2)).
        + move: {H2}(H2 z (refl_equal _) s) => H2.
          rewrite -IHe2 in H2.
          case/boolP : (z == 0) => [/eqP |] H3.
          * subst z; by rewrite H3.
          * rewrite H2 [binop_e_interp _]/=.
            open_integral_type_goal.
            by rewrite mul1Z.
        + rewrite [binop_e_interp _]/=.
          open_integral_type_goal.
          by rewrite mul1Z.
      - move: (expr_compute_correct (simpl_expr' e2)) => H2.
        destruct (expr_compute (simpl_expr' e2)).
        + move: {H2}(H2 z0 (refl_equal _) s) => H2.
          rewrite -IHe2 in H2.
          case/boolP : (z0 == 0) => [/eqP | ] H3.
          * subst z0.
            rewrite H3 H [binop_e_interp _]/=.
            open_integral_type_goal.
            by rewrite mulZ0.
          * case/boolP : (z0 == 1) => [/eqP |] H4.
            - subst z0.
              rewrite H4 H [binop_e_interp _]/=.
              open_integral_type_goal.
              by rewrite mulZ1.
            - by rewrite /= H H2.
        + by rewrite {H2} H.
  + move: {H}(expr_compute_correct (simpl_expr' e2)) => H.
    destruct (expr_compute (simpl_expr' e2)) => //.
    move: {H}(H z (refl_equal _) s) => H.
    rewrite -IHe2 in H.
    case/boolP : (z == 0) => [/eqP |] H0.
    subst z.
    * rewrite H0 [binop_e_interp _]/=.
      open_integral_type_goal; by rewrite mulZ0.
    * case/boolP : (z == 1) => [/eqP |] H1.
      - subst z.
        rewrite H1 [binop_e_interp _]/=.
        open_integral_type_goal.
        by rewrite mulZ1.
      - by rewrite H.
Qed.

Fixpoint simpl_expr_fp (e : expr) (n : nat) {struct n} : expr :=
  match n with
    | O => e
    | S n' =>
      match e with
        | var_e v => var_e v
        | cst_e z => cst_e z
        | e1 \+ e2 => simpl_expr' ((simpl_expr_fp e1 n') \+ (simpl_expr_fp e2 n'))
        | e1 \- e2 => simpl_expr' ((simpl_expr_fp e1 n') \- (simpl_expr_fp e2 n'))
        | e1 \* e2 => simpl_expr' ((simpl_expr_fp e1 n') \* (simpl_expr_fp e2 n'))
        | _ => e
      end
  end.

Lemma simpl_expr_fp_correct: forall n e s, [ e ]e_ s = [ simpl_expr_fp e n ]e_s.
Proof.
elim=> // n IH [] //.
case=> // e1 e2 s; by rewrite -simpl_expr'_correct /= -!IH.
Qed.

Local Open Scope nat_scope.

Fixpoint expr_depth (e : expr) : nat :=
  match e with
    | e1 \+ e2 => 1 + max (expr_depth e1) (expr_depth e2)
    | e1 \- e2 => 1 + max (expr_depth e1) (expr_depth e2)
    | e1 \* e2 => 1 + max (expr_depth e1) (expr_depth e2)
    | _ => 1
  end.

Local Close Scope nat_scope.

Definition simpl_expr (e : expr) : expr := simpl_expr_fp e (expr_depth e).

Lemma simpl_expr_correct : forall e s, [ e ]e_ s = [ simpl_expr e ]e_ s.
Proof. move=> e s; by apply simpl_expr_fp_correct. Qed.

Fixpoint expr_fact' (e : expr) (v : nat) { struct e } : (expr * expr) :=
  match e with
    | var_e x => if x == v then (nat_e 1, nat_e 0) else (nat_e 0, var_e x)
    | cst_e x => (nat_e 0, cst_e x)
    | e1 \+ e2 => match expr_fact' e1 v with
                    | (e11, e12) => match expr_fact' e2 v with
                                      | (e21, e22) => (e11 \+ e21, e12 \+ e22)
                          	    end
                  end
    | e1 \- e2 => match expr_fact' e1 v with
                    | (e11, e12) => match expr_fact' e2 v with
                                      | (e21, e22) => (e11 \- e21, e12 \- e22)
                                    end
                   end
    | e1 \* e2 => match expr_fact' e1 v with
                    | (e11, e12) => match expr_fact' e2 v with
                                     | (e21, e22) =>
                                       (((e12 \* e21) \+ (e11 \* e22))
                                         \+
                                         (var_e v \* (e11 \* e21)),
                                       e12 \* e22)
                                   end
                  end
    | e1 ./e e2 => (nat_e 0, e1 ./e e2)
    | e1 \% e2 => (nat_e 0, e1 \% e2)
    | uop_e valabs_e e' => (nat_e 0, uop_e valabs_e e')
    | uop_e negate_e e' => match expr_fact' e' v with
                             | (e'1, e'2) => (nat_e O \- e'1, cst_e 0 \- e'2)
                           end
  end.

Lemma expr_fact'_correct : forall e v e1 e2, expr_fact' e v = (e1, e2) ->
  forall s, [ e ]e_ s = [ (var_e v \* e1) \+ e2 ]e_ s.
Proof.
elim => /=.
- move=> v v0 e1 e2 H s; case H0 : (v == v0).
  + rewrite H0 in H.
    case: H => X Y; subst e1 e2.
    rewrite /= (eqP H0).
    open_integral_type_goal.
    by rewrite mulZ1 addZ0.
  + intros; rewrite H0 in H.
    case: H => X Y; subst e1 e2.
    open_integral_type_goal.
    by rewrite mulZ0.
- intros; injection H; intros; subst e1 e2.
  open_integral_type_goal => /=; ring.
- destruct b => //.
  + move=> e1 IHe1 e2 IHe2; intros; move: {IHe1}(IHe1 v) => H0.
    move: {IHe2}(IHe2 v) => H1.
    destruct (expr_fact' e1 v); destruct (expr_fact' e2 v); case: H => X Y; subst e0 e3.
    rewrite (H0 e e4) // (H1 e5 e6) //.
    repeat open_integral_type_goal => /=.
    by ring_simplify.
  + move=> e1 IHe1 e2 IHe2; intros; move: {IHe1}(IHe1 v) => H0.
    move: {IHe2}(IHe2 v) => H1.
    destruct (expr_fact' e1 v); destruct (expr_fact' e2 v); case: H => X Y; subst e0 e3.
    rewrite (H0 e e4) // (H1 e5 e6) //.
    repeat open_integral_type_goal => /=.
    by ring_simplify.
  + move=> e1 IHe1 e2 IHe2; intros; move: {IHe1}(IHe1 v) => H0.
    move: {IHe2}(IHe2 v) => H1.
    destruct (expr_fact' e1 v); destruct (expr_fact' e2 v); case: H => X Y; subst e0 e3.
    rewrite (H0 e e4) // (H1 e5 e6) //.
    repeat open_integral_type_goal => /=.
    by ring_simplify.
  + move=> e1 IHe1 e2 IHe2 v e3 e4 [] X Y s; subst e3 e4.
    repeat open_integral_type_goal => /=; by rewrite mulZ0.
  + move=> e1 IHe1 e2 IHe2 v e3 e4 [] X Y s; subst e3 e4.
    repeat open_integral_type_goal => /=; by rewrite mulZ0.
 case.
  + move=> e IHe v e1 e2 [] X Y s; subst e1 e2.
    rewrite /= /ZIT.abs.
    open_integral_type_goal.
    by rewrite mulZ0.
  + (* negate *) move=> e IHe v e1 e2.
    move: {IHe}(IHe v) => H.
    destruct (expr_fact' e v). case=> X Y; subst e1 e2.
    move=> s.
    rewrite (H _ _ refl_equal) /=.
    open_integral_type_goal => /=; ring.
Qed.

(** Simplify a constraint for a given list a variables

  Simplify means that it tries to replace coefficient of
  variables by a value (evaluation without environment)
*)
Fixpoint simpl_varlist_constraint (c : constraint) (v : list nat) {struct v} : constraint :=
  match v with
    | nil => simpl_expr c
    | hd :: tl =>
      match expr_fact' c hd with
        | (e1, e2) =>
          simpl_expr ((simpl_expr (var_e hd \* (simpl_varlist_constraint e1 tl)))
            \+
            (simpl_expr (simpl_varlist_constraint e2 tl)))
      end
  end.

(** an arithmetic expression and its simplification evaluate
   similarly for every environment *)
Lemma simpl_varlist_constraint_correct: forall v c c',
 simpl_varlist_constraint c v = c' -> (forall s, [ c ]e_ s = [ c' ]e_ s).
Proof.
induction v.
- simpl.
  intros.
  by rewrite simpl_expr_correct H.
- simpl; intros.
  move: (expr_fact'_correct c a) => H0.
  destruct (expr_fact' c a).
  rewrite (H0 _ _ (refl_equal _) s) /=.
  rewrite -H -!simpl_expr_correct.
  simpl eval.
  rewrite -!simpl_expr_correct /=.
  move: (IHv e0 (simpl_varlist_constraint e0 v));
    move: (IHv e (simpl_varlist_constraint e v)) => H1 H2.
  by rewrite -H2 // -H1.
Qed.

Definition simpl_constraint (c : constraint) : constraint :=
  simpl_varlist_constraint c (vars_set c).

Lemma simpl_constraint_correct: forall c s, [ c ]e_ s = [ simpl_constraint c ]e_s.
Proof.
intros.
unfold simpl_constraint.
eapply simpl_varlist_constraint_correct; reflexivity.
Qed.

Fixpoint simpl_expr_b (b : expr_b) : expr_b :=
  match b with
    | bop_b b e1 e2 => bop_b b (simpl_constraint e1) (simpl_constraint e2)
    | bop_b2 b e1 e2 => bop_b2 b (simpl_expr_b e1) (simpl_expr_b e2)
    | neg_b e => neg_b (simpl_expr_b e)
    | _ => b
  end.

Lemma simpl_expr_b_correct: forall b s, eval_b b s = eval_b (simpl_expr_b b) s.
Proof.
induction b; simpl; auto; intros.
destruct b => //=.
- by rewrite -!simpl_constraint_correct.
- by rewrite -!simpl_constraint_correct.
- by rewrite -!simpl_constraint_correct.
- by rewrite -!simpl_constraint_correct.
- by rewrite -IHb.
- by rewrite -IHb1 -IHb2.
Qed.

(** simplification of every constraints of an andlist  *)
Fixpoint simpl_andlist (l : andlist) : andlist :=
  match l with
    | nil => nil
    | hd :: tl => simpl_constraint hd :: simpl_andlist tl
  end.

(** simplification preserves evaluation *)
Lemma simpl_andlist_correct: forall l s,
  eval_b (andlist_sem l) s = eval_b (andlist_sem (simpl_andlist l)) s.
Proof.
induction l; auto.
simpl andlist_sem.
intros.
apply expr_b_reflect; split; intros.
- have {H}[H H1] : [ constraint_sem a ]b_s /\ [ andlist_sem l ]b_s.
    split; omegab.
  have [H2 H3] : [ constraint_sem (simpl_constraint a) ]b_s /\
    [ andlist_sem (simpl_andlist l) ]b_s.
    split.
    rewrite /= -simpl_constraint_correct //.
    by rewrite -IHl.
  omegab.
- have {H}[H H1] : [ constraint_sem (simpl_constraint a) ]b_s /\
    [ andlist_sem (simpl_andlist l) ]b_s.
    split; omegab.
  rewrite -IHl in H1.
  have H0 : [ constraint_sem a ]b_s.
    by rewrite /= -simpl_constraint_correct in H.
  omegab.
Qed.

Fixpoint simpl_orlist (l : orlist) : orlist :=
  match l with
    | nil => nil
    | hd :: tl => simpl_andlist hd :: simpl_orlist tl
  end.

Lemma simpl_orlist_correct: forall l s,
  eval_b (orlist_sem l) s = eval_b (orlist_sem (simpl_orlist l)) s.
Proof.
induction l; auto.
simpl orlist_sem.
intros.
apply expr_b_reflect; split; intros.
have [H1 | H1] : ([ andlist_sem a ]b_s \/ [ orlist_sem l ]b_s).
  eval_b2Prop_hyps.
  inversion_clear H.
  left; omegab.
  right; omegab.
rewrite simpl_andlist_correct in H1; omegab.
rewrite IHl in H1; omegab.
have [H1 | H1] : ([ andlist_sem (simpl_andlist a) ]b_s \/
  [ orlist_sem (simpl_orlist l) ]b_s).
  eval_b2Prop_hyps.
  inversion_clear H.
  left; omegab.
  right; omegab.
rewrite -simpl_andlist_correct in H1; omegab.
rewrite -IHl in H1; omegab.
Qed.

Definition expr_fact (e : expr) (v : nat) : expr * expr :=
  match expr_fact' e v with
    | (e1, e2) => (simpl_constraint e1, simpl_constraint e2)
  end.

Lemma expr_fact_correct : forall c v e1 e2, expr_fact c v = (e1, e2) ->
  forall s, [ c ]e_ s = [ (var_e v \* e1) \+ e2 ]e_ s.
Proof.
move=> c v e1 e2.
rewrite /expr_fact => H s.
move: (expr_fact'_correct c v) => H0.
destruct (expr_fact' c v).
case : H => ? ?; subst e1 e2.
by rewrite /= -!simpl_constraint_correct (H0 e e0).
Qed.

(** Variable elimination:
  c1 and c2 are two constraints containing the variable v.
  By computing the coefficients of v we can compute if the variables can be eliminated
  (for details on the elimination mechanism see the following lemma)
*)
Definition elim_var_constraint (c1 c2 : constraint) (v : nat) : constraint :=
  match expr_fact c1 v with
    | (e11, e12) =>
      match expr_fact c2 v with
        | (e21, e22) =>
          match expr_compute (simpl_constraint e11) with
            | None => simpl_constraint c2
            | Some e11' =>
              match expr_compute (simpl_constraint e21) with
                | None => simpl_constraint c2
                | Some e21' =>
                  if Zlt_bool e11' 0 && Zlt_bool 0 e21' then
                    simpl_constraint ((e21 \* e12) \- (e11 \* e22))
                    else
                      (if Zlt_bool 0 e11' && Zlt_bool e21' 0 then
                        simpl_constraint ((e11 \* e22) \- (e21 \* e12))
                        else
                          simpl_constraint c2)
              end
          end
      end
   end.

Lemma fourier_motzkin_for_integers: forall a1 b1 a2 b2 x,
  a1 < 0 -> 0 < a2 ->
  0 >= x * a1 + b1 -> 0 >= x * a2 + b2 ->
  a1 * b2 >= a2 * b1.
Proof.
intros.
have H3 : b1 <= - (x * a1) by intuition.
have H4 : (x * a2) <= - b2 by intuition.
have H5 : b1 * a2 <= - (x * a1) * a2 by intuition.
have H6 : (x * a2) * -a1 <= - b2 * - a1 by intuition.
have H7 : x * a2 * - a1 = -(x * a1) * a2 by ring.
rewrite H7{H7} in H6.
have H7 : b1 * a2 <= - b2 * - a1 by intuition.
have H8 : -b2 * - a1 = a1 * b2 by ring.
rewrite H8{H8} in H7.
by rewrite (_ :  a2 * b1 = b1 * a2); intuition.
Qed.

Eval compute in (expr_fact (((var_e 1%nat \* cst_e 2) \+ cst_e 1) \- (var_e 0%nat \* cst_e 2)) O).
Eval compute in (expr_fact ((var_e 0%nat \* cst_e 2)\- ((var_e 1%nat \* cst_e 2) \+ cst_e 1)) O).

Eval compute in (elim_var_constraint
  (((var_e 1%nat \* cst_e 2) \+ cst_e 1) \- (var_e 0%nat \* cst_e 2))
  ((var_e 0%nat \* cst_e 2)\- ((var_e 1%nat \* cst_e 2) \+ cst_e 1))
  0).

(*Lemma expr_b_semantic_good' : forall e s, eval_b e s -> expr_b_sem e s.
Proof.
intros.
generalize (expr_b_semantic_good e s); tauto.
Qed.*)

(** The two constraints allowing the variables elimination implies the constraint resulting from elimination *)
Lemma elim_var_constraint_correct : forall c1 c2 v s,
  [ (constraint_sem c1) \&& (constraint_sem c2) ]b_s ->
  [ constraint_sem (elim_var_constraint c1 c2 v) ]b_s.
Proof.
move=> c1 c2 v s H.
generalize ((proj1 (expr_bP _ _)) H); intro X; simpl in X.
unfold elim_var_constraint.
generalize (expr_fact_correct c1 v) => H0.
generalize (expr_fact_correct c2 v) => H1.
destruct (expr_fact c1 v); destruct (expr_fact c2 v).
move: {H0}(H0 _ _ (refl_equal (e, e0)) s) => H0.
move: {H1}(H1 _ _ (refl_equal (e1, e2)) s) => H1.
simpl in H0; simpl in H1.
generalize (expr_compute_correct (simpl_constraint e)) => H2.
generalize (expr_compute_correct (simpl_constraint e1)) => H3.
destruct (expr_compute (simpl_constraint e)); destruct (expr_compute (simpl_constraint e1)).
- move: {H2}(H2 _ (refl_equal (Some z)) s) => H2.
  move: {H3}(H3 _ (refl_equal (Some z0)) s) => H3.
  rewrite -simpl_constraint_correct in H2.
  rewrite -simpl_constraint_correct in H3.
  generalize (Zlt_cases z 0) => H4.
  generalize (Zlt_cases 0 z0) => H5.
  destruct (Zlt_bool z 0); destruct (Zlt_bool 0 z0).
  - simpl.
    apply ZIT.geP.
    rewrite -simpl_constraint_correct /=.
    open_integral_type_goal.
    have H6 : [ e ]e_ s * [ e2 ]e_ s >= [ e1 ]e_ s * [ e0 ]e_ s.
      repeat open_integral_type_hyp.
      apply fourier_motzkin_for_integers with (store.get v s).
      by rewrite H2.
      by rewrite H3.
      rewrite -H0; by case: X.
      rewrite -H1; by case: X.
    lia.
  - rewrite /=.
    apply ZIT.geP.
    have -> : 0 <? z = false by apply/ltZP; lia.
    rewrite /= -simpl_constraint_correct; tauto.
  - rewrite /=.
    apply ZIT.geP.
    have -> : z0 <? 0 = false by apply/ltZP; lia.
    rewrite andbC /= -simpl_constraint_correct; tauto.
  - rewrite /=.
    generalize (Zlt_cases 0 z) => H6.
    generalize (Zlt_cases z0 0) => H7.
    destruct (Zlt_bool 0 z); destruct (Zlt_bool z0 0).
    + simpl.
      apply/geZP.
      rewrite -simpl_constraint_correct.
      have H8 : eval e1 s * eval e0 s >= eval e s * eval e2 s.
        apply fourier_motzkin_for_integers with (store.get v s).
        by rewrite H3.
        by rewrite H2.
        repeat open_integral_type_hyp.
        rewrite -H1; tauto.
        repeat open_integral_type_hyp.
        rewrite -H0;tauto.
      rewrite /=.
      open_integral_type_goal.
      lia.
    + rewrite /= -simpl_constraint_correct.
      apply/geZP; tauto.
    + rewrite /= -simpl_constraint_correct.
      apply/geZP; tauto.
    + rewrite /= -simpl_constraint_correct.
      apply/geZP; tauto.
- rewrite /= -simpl_constraint_correct.
  apply/geZP; tauto.
- rewrite /= -simpl_constraint_correct.
  apply/geZP; tauto.
- rewrite /= -simpl_constraint_correct.
  apply/geZP; tauto.
Qed.

(** Given a constraint c, a list a constraint l and a variable v,
  we build the list l' of constraints such that it contains
  i) all the constraints of l where v does not appear
  ii)  all the constraints of l where v appears but cannot be eliminated using c
  iii) all constraints of l where v appears and have been eliminated using c
*)

Fixpoint elim_var_andlist' (c: constraint) (l l':andlist) (v: nat) {struct l} : andlist :=
  match l with
    | nil => l'
    | hd :: tl =>
      if v \in vars_set (simpl_constraint hd) then
        elim_var_andlist' c tl (elim_var_constraint c hd v :: l') v
      else
        elim_var_andlist' c tl l' v
  end.

Lemma elim_var_andlist'_correct : forall l l' c v s,
  [ andlist_sem (c :: l ++ l') ]b_s ->
  [ andlist_sem (elim_var_andlist' c l l' v) ]b_s.
Proof.
induction l.
- simpl andlist_sem.
  by intros; omegab.
- simpl andlist_sem; simpl andlist_sem in IHl.
  move=> l' c v s H.
  case: ifPn => // H_.
  + have [H1 [H0 H3]] : [ constraint_sem c ]b_s /\
      [ constraint_sem a ]b_s /\ [ andlist_sem (l ++ l') ]b_s .
      split; first by omegab.
      by split; omegab.
    rewrite andlist_plus_sem in H3.
    apply IHl.
    have [H4 H5] : [ constraint_sem c ]b_s /\
      [ andlist_sem (l ++ elim_var_constraint c a v :: l') ]b_s.
      rewrite andlist_plus_sem.
      have [H2 H4] : [ andlist_sem l ]b_s /\
        [ andlist_sem (elim_var_constraint c a v :: l') ]b_s.
        simpl andlist_sem.
        have [H2 H4] : [ constraint_sem (elim_var_constraint c a v) ]b_s /\
          [ andlist_sem l' ]b_s.
          split; last by omegab.
          apply elim_var_constraint_correct; by omegab.
        split; by omegab.
     split; by omegab.
    by omegab.
  + apply IHl.
    by omegab.
Qed.

(** For a given variable v, find the next constraint containing v, and
   use it to eliminate v on the rest of the list *)
Fixpoint elim_var_andlist (l l' : andlist) (v : nat) {struct l} : andlist :=
  match l with
    | nil => l'
    | hd :: tl => if v \in vars_set (simpl_constraint hd) then
      elim_var_andlist tl (l' ++ (elim_var_andlist' hd tl nil v)) v
      else
        elim_var_andlist tl (hd :: l') v
  end.

Lemma elim_var_andlist_correct: forall l l' v s, [ andlist_sem (andlist_plus l l') ]b_s ->
  [ andlist_sem (elim_var_andlist l l' v) ]b_s.
Proof.
induction l.
- simpl andlist_sem.
  by intuition.
- simpl andlist_sem.
  move=> l' v s H.
  case: ifPn => H_.
  + apply IHl.
    rewrite andlist_plus_sem.
    have [H1 H2] : [ andlist_sem l ]b_s /\ [ andlist_sem (l' ++ elim_var_andlist' a l nil v) ]b_s.
      have [H1 H2] : [ constraint_sem a ]b_s /\ [ andlist_sem (l ++ l') ]b_s by split; omegab.
      split.
      rewrite andlist_plus_sem in H2.
      by omegab.
      rewrite andlist_plus_sem.
      rewrite andlist_plus_sem in H2.
      have [H0 H4] : [ andlist_sem l' ]b_s /\ [ andlist_sem (elim_var_andlist' a l nil v) ]b_s.
        split.
        by omegab.
        apply elim_var_andlist'_correct.
        rewrite [andlist_sem _]/= cats0.
        by omegab.
      by omegab.
    by omegab.
  + apply IHl.
    rewrite andlist_plus_sem.
    simpl andlist_sem.
    have [H1 H2] : ([ constraint_sem a ]b_s /\ [ andlist_sem (l ++ l') ]b_s ) by split; omegab.
    rewrite andlist_plus_sem in H2.
    by omegab.
Qed.

(** elimination of the variable v in the orlist  *)
Fixpoint elim_var_orlist (l : orlist) (v : nat) {struct l} : orlist :=
   match l with
      | nil => nil
      | hd::tl => elim_var_andlist hd nil v :: elim_var_orlist tl v
   end.

Lemma elim_var_orlist_correct: forall l v s,
  eval_b (orlist_sem l) s -> eval_b (orlist_sem (elim_var_orlist l v)) s.
Proof.
induction l.
- simpl; by intuition.
- simpl orlist_sem.
  intros.
  have H0 : [ andlist_sem a ]b_s \/ [ orlist_sem l ]b_s.
    eval_b2Prop_hyps.
    inversion_clear H.
    left; omegab.
    right; omegab.
  rewrite simpl_orlist_correct in H0.
  have H1 : [ andlist_sem (elim_var_andlist a nil v) ]b_s \/ [ orlist_sem (elim_var_orlist l v) ]b_s.
    inversion_clear H0.
    + left.
      apply elim_var_andlist_correct.
      by rewrite /andlist_plus cats0.
    + right.
      apply IHl.
      by rewrite -simpl_orlist_correct in H1.
  inversion_clear H1; omegab.
Qed.

(** Elimination of a list of variables *)
Fixpoint elim_varlist_orlist (l : orlist) (v : list nat) {struct v} : orlist :=
  match v with
    | nil => simpl_orlist l
    | hd :: tl => elim_varlist_orlist (elim_var_orlist l hd) tl
  end.

Lemma elim_varlist_orlist_correct: forall v l s, eval_b (orlist_sem l) s ->
  eval_b (orlist_sem (elim_varlist_orlist l v)) s.
Proof.
induction v.
- simpl.
  intros.
  by rewrite -simpl_orlist_correct.
- simpl elim_varlist_orlist.
  intros.
  apply IHv.
  by apply elim_var_orlist_correct.
Qed.

(** boolean evaluation of a constraint without environment  *)
Definition eval_constraint (c : constraint) : option bool :=
   match expr_compute c with
     | Some z => Some (Zge_bool 0 z)
     | _ => None
   end.

(** if possible, evaluation is valid for every environment  *)
Lemma eval_constraint2constraint_sem: forall c b,
  eval_constraint c = Some b ->
  forall s, eval_b (constraint_sem c) s = b.
Proof.
intros.
generalize (expr_compute_correct c) => H0.
unfold eval_constraint in H.
destruct (expr_compute c) => //.
simpl.
case: H => X; subst b.
by rewrite (H0 z).
Qed.

(** evaluation of a not empty andlist without environment *)
Fixpoint eval_andlist' (a : andlist) : option bool :=
  match a with
    | nil => Some true
    | hd :: tl => match eval_constraint hd with
                    | Some false => Some false
                    | o => match eval_andlist' tl with
                             | None => None
                             | Some false => Some false
                             | Some true => andb_option o (Some true)
                           end
                end
  end.

(** if evaluation was possible, it holds for every environment *)
Lemma eval_andlist'2andlist_sem: forall a b,
  eval_andlist' a = Some b ->
  forall s, eval_b (andlist_sem a) s = b.
Proof.
induction a.
- simpl.
  intros.
  by case: H.
- simpl eval_andlist'.
  move=> b H s.
  generalize (eval_constraint2constraint_sem a) => H0.
  destruct (eval_constraint a).
  + simpl in H0.
    rewrite /= (H0 b0) //.
    destruct b0.
    * simpl.
      destruct (eval_andlist' a0) => //.
      rewrite (IHa b0) //.
      destruct b0; simpl in H; by case: H.
    * simpl; injection H; auto.
  + simpl.
    destruct (eval_andlist' a0) => //.
    rewrite (IHa b0) //.
    destruct b0 => //.
    rewrite andbF.
    by case: H.
Qed.

(** Evaluation of an andlist without environment. If empty => error !Z*)
Definition eval_andlist (a : andlist) : option bool :=
  if size a == O then
    None
  else
    eval_andlist' a.

(** if the evaluation is possible, it holds for every environment *)
Lemma eval_andlist2andlist_sem: forall a b, eval_andlist a = Some b ->
  forall s, eval_b (andlist_sem a) s = b.
Proof.
intros.
unfold eval_andlist in H.
case H0 : (size a == O).
- by rewrite H0 in H.
- rewrite H0 in H.
  by apply eval_andlist'2andlist_sem.
Qed.

(** Evaluation of a non empty orlist without environment *)
Fixpoint eval_orlist' (o : orlist) : option bool :=
   match o with
     | nil => Some false
     | hd :: tl => orb_option (eval_andlist hd) (eval_orlist' tl)
   end.

(** if possible, evaluation holds for every environment *)
Lemma eval_orlist'2orlist_sem: forall a b,
  eval_orlist' a = Some b ->
  forall s, eval_b (orlist_sem a) s = b.
Proof.
induction a; simpl; intros.
injection H; auto.
generalize ( eval_andlist2andlist_sem a); intros.
destruct (eval_andlist a); simpl in H; try discriminate.
rewrite (H0 b0); auto.
destruct (eval_orlist' a0); simpl in H; try discriminate.
simpl in H.
rewrite (IHa b1 (refl_equal _)).
by case: H.
Qed.

(** evaluation of an orlist without environement *)
Definition eval_orlist (a : orlist) : option bool :=
  if size a == O then None else eval_orlist' a.

(** if possible, evaluation holds for every environment *)
Lemma eval_orlist2orlist_sem: forall a b,
  eval_orlist a = Some b -> (forall s, eval_b (orlist_sem a) s = b).
Proof.
intros.
unfold eval_orlist in H.
case X : (size a == O).
rewrite X in H; discriminate.
rewrite X in H.
by apply eval_orlist'2orlist_sem.
Qed.

(** The algorithm:
  i) put the boolean expression in normal form
  ii) eliminate all its variables
  iii) evaluate without environment
  iv) return the negation
*)
Definition expr_b_dp (b : expr_b) : bool :=
  match eval_orlist (elim_varlist_orlist
    (simpl_orlist (expr_b2constraints (simpl_expr_b (\~ b))))
    (vars_b_set (simpl_expr_b b))) with
    | None => false
    | Some res => negb res
  end.

(** if the function result is true then the original expression is true for every environment *)
Lemma expr_b_dp_correct: forall b, expr_b_dp b -> forall s, [ b ]b_s.
Proof.
intros.
case/boolP : ([ b ]b_s) => // H1.
have {H1}H0 : [ \~ b ]b_s by omegab.
rewrite simpl_expr_b_correct -expr_b2constraints_correct simpl_orlist_correct in H0.
move: (elim_varlist_orlist_correct (vars_b_set (simpl_expr_b b)) _ _ H0) => H1.
move: (eval_orlist2orlist_sem (elim_varlist_orlist
  (simpl_orlist (expr_b2constraints (simpl_expr_b (\~ b))))
  (vars_b_set (simpl_expr_b b)))) => H2.
rewrite /expr_b_dp in H.
destruct (eval_orlist
  (elim_varlist_orlist
    (simpl_orlist (expr_b2constraints (simpl_expr_b (\~ b))))
    (vars_b_set (simpl_expr_b b)))); last by [].
destruct b0; first by [].
by rewrite (H2 _ (refl_equal _) s) in H1.
Qed.

(** FrontEnd Tactics for the expr_b_dp function *)

(** Determine if t is a Coq positive variable *)
Ltac Is_pos_var p :=
  match p with
    | xH => false
    | xI ?n => false
    | xO ?n => false
    | _ => true
  end.

(** Determine if t is a Coq Z variable *)
Ltac Is_Z_var t :=
  match t with
    | Z0 => false
    | Zpos ?e  => Is_pos_var e
    | Zneg ?e => Is_pos_var e
    | _ => true
  end.

(** add an element to a list only if not already present *)
Ltac Add_list e l :=
  match l with
    | e :: ?tl => l
    | ?hd :: ?tl => let x := Add_list e tl in constr:(hd :: x)
    | (@nil Z) => constr:(e :: nil)
  end.

(** concatenate two lists without adding duplicates *)
Ltac Concat_list l1 l2 :=
  match l1 with
    | ?hd :: ?tl => let x:= Add_list hd l2 in Concat_list tl x
    | nil => l2
  end.

(** Build the list of the Coq variable inside the term t
 Such a list is used as an environment  *)
Ltac Build_env t :=
  match t with
    | (?t1 + ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 - ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 * ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 = ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 -> ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 > ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 < ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 >= ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 <= ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 /\ ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 \/ ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (?t1 <> ?t2)%Z =>
      let x := Build_env t1 in let y := Build_env t2 in
      Concat_list x y
    | (~ ?t1)%Z => let x := Build_env t1 in x
    | _ => let x := Is_Z_var t in
        match eval compute in x with
          | true => constr: (t :: nil)
          | false => constr: (@nil Z)
        end
  end.

(** return the index of variable v in list l *)
Ltac Get_var_index v l := find_indice v l(*Find_var Z v l O*).

(** translate a Coq term to an arithmetic expression using a list of variables l *)
Ltac To_expr t l :=
  match t with
    | (?t1 + ?t2)%Z =>
      let x := To_expr t1 l in let y := To_expr t2 l in
      constr: (x \+ y)
    | (?t1 - ?t2)%Z =>
      let x := To_expr t1 l in let y := To_expr t2 l in
      constr: (x \- y)
    | (?t1 * ?t2)%Z =>
      let x := To_expr t1 l in let y := To_expr t2 l in
      constr: (x \* y)
    | _ =>
      let x:= Is_Z_var t in
        match eval compute in x with
          | true => let y := find_indice t l (*Find_var Z t l O*) in
                    constr: (var_e y)
          | false => constr: (cst_e t)
        end
  end.

(** Translate a Coq term to a boolean expression using a list of variables l *)
Ltac To_expr_b t l :=
  match t with
    | (?t1 = ?t2) =>
      let x := To_expr t1 l in let y := To_expr t2 l in
      constr: (x \= y)
    | (?t1 > ?t2)%Z =>
      let x := To_expr t1 l in let y := To_expr t2 l in
      constr: (x \> y)
    | (?t1 >= ?t2)%Z =>
      let x := To_expr t1 l in let y := To_expr t2 l in
      constr: (x \>= y)
    | (?t1 < ?t2)%Z =>
      let x := To_expr t1 l in let y := To_expr t2 l in
      constr: (\~ (x \>= y))
    | (?t1 <= ?t2)%Z =>
      let x := To_expr t1 l in let y := To_expr t2 l in
      constr: (\~ (x \> y)) (* TODO: change to << when expr_b is extended with lt constructor? *)
    | (?t1 -> ?t2) =>
      let x := To_expr_b t1 l in let y := To_expr_b t2 l in
      constr:(x =b> y)
    | (?t1 /\ ?t2) =>
      let x := To_expr_b t1 l in let y := To_expr_b t2 l in
      constr: (x \&& y)
    | (?t1 \/ ?t2) =>
      let x := To_expr_b t1 l in let y := To_expr_b t2 l in
      constr: (x \|| y)
    | (?t1 <> ?t2) =>
      let x := To_expr_b t1 l in let y := To_expr_b t2 l in
      constr: (x \!= y)
    | (~ ?t1) =>
      let x := To_expr_b t1 l in constr: (\~ x)
  end.

Fixpoint list2store (l : list Z) { struct l } : store.t :=
   match l with
     | nil => store.emp
     | hd::tl => store.upd (length l - 1)%nat hd (list2store tl)
   end.

Require Import bipl.

Lemma lookup_list2store : forall l x, store.get x (list2store l) = nth 0%Z (rev l) x.
Proof.
rewrite /var.v.
elim.
- move=> x.
  rewrite store.get_emp; by destruct x.
- move=> /= a l H x.
  rewrite subSS subn0.
  have [H0 | H0] : (x = size l \/ x <> size l)%nat by lia.
  + subst x.
    by rewrite store.get_upd' nth_rev // subSS subnn.
  + rewrite store.get_upd //; last by apply/eqP.
    rewrite H.
    have [H1 | H1] : (x < size l \/ x > size l)%nat.
      apply not_eq in H0.
      case: H0 => H0; ssromega.
    * by rewrite rev_cons -cats1 nth_cat size_rev H1.
    * rewrite nth_default; last by rewrite size_rev ltnW.
      by rewrite nth_default // size_rev.
Qed.

Ltac Expr_b_dp_reflect :=
  match goal with
    | |- ?G =>
      (* l is the environment including all coq variable of the goal *)
      let l := (Build_env G) in
      (* x is the boolean expression corresponding to the goal with respect to the environement l *)
      let x := (To_expr_b G l) in
      let s := constr:(list2store (rev l)) in
      (* a proof of the goal can be achieve by proving that evaluation of x for l is true  *)
      cut (eval_b x s = true)
  end.

Ltac expr_b_dp_decision :=
  (** Introduction of all relevant hypothesis *)
  match goal with
    | |- ?G =>
      let l := (Build_env G) in
      let x := (To_expr_b G l) in
      let s := constr:(list2store (rev l)) in
      cut (eval_b x s = true) ;
(* To prove the evaluation we use the expr_b_dp function  *)
     [
(*       move/expr_bP ;
         rewrite [list2store]lock /= -lock !lookup_list2store /= ;
           intro; firstorder*)
       let h:= fresh in
       intro h;
       let y := fresh in
       generalize (proj1 (expr_bP x s) h); clear h; intro y; simpl in y;
       repeat (rewrite lookup_list2store in y); simpl in y; firstorder
       |
       (apply expr_b_dp_correct; vm_compute; apply refl_equal)
     ]
  end.

Ltac Reflection_is_correct :=
  match goal with
    | [ |- [ ?e ]b_ ?s = true -> ?P ] =>
       let h:= fresh in
       intro h;
       let y := fresh in
       generalize (proj1 (expr_bP e s) h); clear h; intro y; simpl in y;
       repeat (rewrite lookup_list2store in y); simpl in y; firstorder; try lia
(*move/expr_bP.
rewrite [list2store]lock /= -lock !lookup_list2store /=.
by auto.*)
  end.

Ltac Apply_dp := apply expr_b_dp_correct; vm_compute; reflexivity.

Lemma btest1 : forall x y : Z, x = y -> x = y.
Proof.
move=> x y.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

Lemma btest2 : forall x y z res,
  (res = x /\ x >= y /\ x >= z) -> (res >= x /\ res >= y /\ res >= z).
Proof.
do 4 intro.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

Lemma btest3 : forall x y z res, (res = x /\ x >= y /\ x >= z) -> res >= x.
Proof.
do 4 intro.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

Lemma btest4 : forall x y z res, (res = x /\ x >= y /\ x >= z) -> res >= x.
Proof.
do 4 intro.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

Lemma btest5 : forall x y, x = 1 -> y = 1 -> x = y.
Proof.
do 2 intro.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

(* generalize and clear the first hypothesis that comport a variable in l and then call expr_b_dp or expr_b_dp_decision *)
(*Ltac Intro_hyp_var_list l :=
  match goal with
    | id: ?a%Z |- _ =>
      let l' := Build_env a in
      let x := In_list_list l' l in
      match eval compute in x with
        | true => generalize id; clear id; (Expr_b_dp || expr_b_dp_decision)
        | false => fail
      end
    | _ => expr_b_dp_decision
  end*)
(* call Intro_hyp_var_list with the list of Coq variables present in the goal  *)
(*with Expr_b_dp :=
  match goal with
    | |- ?G =>
      let l := Build_env G in
        Intro_hyp_var_list l
  end.    *)

(* try to find a hypothesis that can be prove wrong *)
(*Ltac Contradiction_b :=
  match goal with
    | id: ?A |- _ =>
      assert (~A); [Expr_b_dp | tauto]
    | _ => fail
  end.*)

Lemma btest6 : forall z, z > 0 -> 2 * z + 1 > z.
Proof.
intro z.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
(* open_integral_type_goal. ? *)
Qed.

Lemma btest7 : forall a b, (a < b \/ b < a) -> a <> b.
Proof.
intros a b.
Expr_b_dp_reflect.
by Reflection_is_correct.
(* open_integral_type_goal *)
by Apply_dp.
Qed.

Lemma btest8 : forall a b c, (a > b /\ a < b) -> a=c.
Proof.
intros a b c.
Expr_b_dp_reflect.
by Reflection_is_correct.
(* open_integral_type_goal *)
by Apply_dp.
Qed.

Lemma btest9 :  1 <= 1.
Proof.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

Definition pp (n: nat) : Z := Z_of_nat n * 66.

Lemma btest10 : forall a b c, pp a > b -> b > c -> pp a > c.
Proof.
do 3 intro.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

Lemma btest11 : forall a b c, a >= b -> b > c -> a > c.
Proof.
do 3 intro.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

Lemma btest12 : forall a b c, a < b -> b < c -> a < c.
Proof.
do 3 intro.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

Lemma btest13 : forall a b c, a < b -> b < c -> a < c.
Proof.
do 3 intro.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

(* 2011/3/29: several Ltacs moved to integral_type.v *)
(*Module Import ZIT_prop_m := IntegralType_Prop ZIT.*)

Lemma btest14 : forall a b, (a + b) * (a + b) = a * a + b * b + 2 * a * b.
Proof.
do 2 intro.
Expr_b_dp_reflect.

(* TODO *)
move/expr_bP.
rewrite [list2store]lock /= -lock !lookup_list2store /=.
open_integral_type_goal.
by auto.

by Apply_dp.
Qed.

Lemma btest15 : forall a b, (a + b) * (a + b) = a * a + b * b + 2 * a * b.
Proof.
intros a b.
Expr_b_dp_reflect.

move/expr_bP ;
  rewrite [list2store]lock /= -lock !lookup_list2store /=.
open_integral_type_goal.
firstorder.

(* TODO *)

by Apply_dp.
Qed.

Lemma btest16 : forall m n, 1 + 2 * m <> 2 * n.
Proof.
do 2 intro.
Expr_b_dp_reflect.

by Reflection_is_correct.

apply expr_b_dp_correct.

(*rewrite {1}/expr_b_dp.
simpl vars_b_set.
simpl simpl_expr_b.

rewrite {1}/simpl_constraint.
rewrite {1}[simpl_varlist_constraint _ _]/=.
rewrite {4}/simpl_expr.
simpl simpl_expr_fp.
rewrite {3}/simpl_expr.
simpl simpl_expr_fp.
rewrite {2}/simpl_expr.
simpl simpl_expr_fp.
rewrite {1}/simpl_expr.
simpl simpl_expr_fp.

rewrite {1}/simpl_constraint.
rewrite {1}[simpl_varlist_constraint _ _]/=.
rewrite /simpl_expr.
simpl simpl_expr_fp.

rewrite /expr_b2constraints.
simpl neg_propagate.
simpl disj_nf.

Eval compute in
       (simpl_orlist
             (((((var_e 1%nat \* cst_e 2) \+ cst_e 1)
                \- (var_e 0%nat \* cst_e 2))
               :: ((var_e 0%nat \* cst_e 2)
                   \- ((var_e 1%nat \* cst_e 2) \+ cst_e 1)) :: nil) :: nil)).

Eval compute in eval_orlist (elim_varlist_orlist
          (simpl_orlist
             (((((var_e 1%nat \* cst_e 2) \+ cst_e 1)
                \- (var_e 0%nat \* cst_e 2))
               :: ((var_e 0%nat \* cst_e 2)
                   \- ((var_e 1%nat \* cst_e 2) \+ cst_e 1)) :: nil) :: nil))
          (0%nat :: 1%nat :: nil)).
*)

vm_compute.


Abort.

Lemma btest17 : forall x y, 0 < x /\ y < x -> y + 1 < 2 * x.
Proof.
intros x y.
Expr_b_dp_reflect.
by Reflection_is_correct.
by Apply_dp.
Qed.

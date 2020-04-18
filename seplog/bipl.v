(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import Max_ext ssrnat_ext ZArith_ext seq_ext uniq_tac.
Require Import order finmap integral_type.
Require while.

(** This file provides:
  - a module "var" for the variables of a programming language
  - a module "Store" for the set of variables of a programming language;
    it is parameterized by some "integral type";
    by default, variables are to zero
  - a module "Expr" for the arithmetic expressions of a programming language
  - a module "Sep" for the BI formulas underlying Separation Logic

  These modules are parameterized by the type of data held into variables.
*)

Declare Scope seplog_expr_scope.
Declare Scope heap_scope.
Declare Scope seplog_assert_scope.

Module Type VAR.
Parameter v : eqType.
End VAR.

Module var <: VAR with Definition v := nat_eqType.
Definition v := nat_eqType.
End var.

Module Type STORE.
Parameter u : eqType. (* type of stored data *)
Parameter u0 : u. (* default value for stored data *)
Parameter t : Type. (* type of stores *)
Parameter dom : t -> seq var.v.
Parameter emp : t.
Parameter get : var.v -> t -> u.
Parameter upd : var.v -> u -> t -> t.
Parameter proj : t -> seq var.v -> t.
Parameter upds : seq var.v -> seq u -> t -> t.
Parameter get_emp : forall x, get x emp = u0.
Parameter get_upd : forall x y z s, x != y -> get x (upd y z s) = get x s.
Parameter get_upds : forall x ys zs s, ~ x \in ys -> get x (upds ys zs s) = get x s.
Parameter get_upd' : forall x z s, get x (upd x z s) = z.
Parameter extensionality : forall d st1 st2, inc d (dom st1) -> inc d (dom st2) ->
  (forall x, x \in d -> get x st1 = get x st2) -> proj st1 d = proj st2 d.
Parameter upd_upd : forall s x x' v v', x != x' -> upd x v (upd x' v' s) = upd x' v' (upd x v s).
Parameter upd_upd_eq : forall s x v v', upd x v (upd x v' s) = upd x v s.

End STORE.

(** local store with a default element *)
Module Store (A : IntegralType) <: STORE.
Definition u : eqType := A.t.
Definition u0 := A.of_nat O.

Module Codom <: EQTYPE.
  Definition A : eqType := A.t.
End Codom.
Module store := finmap.map NatOrder Codom.

Local Notation "k '#' m" := (store.disj k m).
Local Notation "k '\U' m" := (store.union k m).
Local Notation "k '\D\' m" := (store.difs k m).
Local Notation "k '|P|' m" := (store.proj k m).
Local Notation "k '\I' m" := (store.inclu k m).
Local Notation "k '\d\' l" := (store.dif k l).

Definition t := store.t.

Definition dom (st : t) : seq var.v := store.dom st.

Definition emp : t := store.emp.

Definition get (w : var.v) (st : t) : A.t :=
  match store.get w st with Some i => i | None => u0 end.

Definition upd (i : var.v) (w : A.t) (st : t) : t :=
  match Bool.bool_dec (w == A.of_nat 0) true with
  | left _ => st \d\ i
  | right X => store.sing i w \U st
  end.

Definition proj := store.proj.

Fixpoint upds (xs : seq var.v) (vs : seq u) (st : t) {struct xs} : t :=
  match xs with
    | nil => st
    | hx :: tx =>
      match vs with
        | nil => st
        | hv :: tv =>
          let st' := upds tx tv st in
          upd hx hv st'
      end
  end.

Lemma get_emp x : get x emp = u0.
Proof. by rewrite /get store.get_emp. Qed.

Lemma get_upd x y z st : x != y -> get x (upd y z st) = get x st.
Proof.
move/eqP => Hneq.
rewrite {1}/get /upd.
case: Bool.bool_dec => X; by
  [rewrite store.get_dif' | rewrite store.get_union_sing_neq].
Qed.

Lemma get_upds x ys : forall zs st, ~ x \in ys -> get x (upds ys zs st) = get x st.
Proof.
elim: ys x => // hy ty IH x [|hzs tzs] //= st H.
have {H}/andP[H1 H2] : (hy != x) && (x \notin ty).
  move/negP in H.
  by rewrite in_cons negb_or eq_sym in H.
rewrite get_upd; last by rewrite eq_sym.
apply IH => //; exact/negP.
Qed.

Lemma get_upd' w z st : get w (upd w z st) = z.
Proof.
rewrite /get /upd.
case: Bool.bool_dec => [/eqP X|X];
  [ by rewrite store.get_dif | by rewrite store.get_union_sing_eq].
Qed.

Lemma extensionality d s1 s2 : inc d (dom s1) -> inc d (dom s2) ->
  (forall x, x \in d -> get x s1 = get x s2) -> s1 |P| d = s2 |P| d.
Proof.
move=> d1 d2 H; apply store.extensionality => x.
case/boolP : (x \in d) => xd; last first.
  by rewrite !store.get_proj_None.
move: (H x xd).
rewrite /get.
move H1 : (store.get x _) => [v1|] => //.
  move H2 : (store.get x _) => [v2|] => //.
    move=> ?; subst v2.
    by rewrite store.get_proj // store.get_proj // H1 H2.
  move/store.get_None_notin in H2.
  exfalso.
  move : xd; apply/negP.
  apply: contra H2.
  move/incP' in d2.
  by move/d2.
move/store.get_None_notin in H1.
exfalso.
move : xd; apply/negP.
apply: contra H1.
move/incP' in d1.
by move/d1.
Qed.

Lemma upd_upd s x y v v' : x != y -> upd x v (upd y v' s) = upd y v' (upd x v s).
Proof.
move=> H.
rewrite /upd.
case: Bool.bool_dec => v0.
  case: Bool.bool_dec => v'0.
    by rewrite !store.difE store.difs_difs.
  rewrite !store.difE.
  case/boolP : (dis (store.dom s) [:: x]) => sx.
    rewrite store.difs_union_L // store.dis_difs; last first.
      by rewrite store.dom_sing -dis_singl eq_sym.
    by rewrite store.dis_difs.
  by rewrite store.difs_union_R // store.dom_sing -dis_singl eq_sym.
case: Bool.bool_dec => v'0.
  rewrite !store.difE.
  case/boolP : (dis (store.dom s) [:: y]) => sy.
    rewrite store.difs_union_L // store.dis_difs //.
    by rewrite store.dis_difs // store.dom_sing -dis_singl.
  by rewrite store.difs_union_R // store.dom_sing -dis_singl.
rewrite !store.unionA (store.unionC (store.sing _ _)) //; exact/store.disj_sing.
Qed.

Lemma upd_upd_eq s x v v' : upd x v (upd x v' s) = upd x v s.
Proof.
rewrite /upd.
case: Bool.bool_dec => v0.
  case: Bool.bool_dec => v'0.
    by rewrite !store.difE store.difsK.
  rewrite store.difE store.difs_union.
  by rewrite -{1}(store.dom_sing x v') store.difs_self store.unioneh store.difE.
case: Bool.bool_dec => v'0.
  by rewrite !store.difE store.union_sing_difs.
rewrite store.unionA.
by rewrite store.sing_union_sing.
Qed.

(* TODO: to put in the interface? *)
Lemma get_proj' (d : seq store.l) k n : n \notin d -> get n (k |P| d) = u0.
Proof.
move=> H.
rewrite /get.
move Heq : (store.get _ _) => e.
destruct e => //.
by rewrite store.get_proj_None in Heq.
Qed.

Lemma get_proj (d : seq store.l) k n : n \in d -> get n (k |P| d) = get n k.
Proof.
move=> H.
rewrite /get.
move Heq : (store.get _ _) => e.
destruct e; rewrite store.get_proj // in Heq; by rewrite Heq.
Qed.

Lemma get_difs k x (d : seq store.l) : x \notin d -> get x (k \D\ d) = get x k.
Proof.
move=> H.
rewrite /get.
move Heq : (store.get _ _) => e.
destruct e; rewrite store.get_difs // in Heq; by rewrite Heq.
Qed.

Lemma get_difs' k x (d : seq store.l) : x \in d -> get x (k \D\ d) = u0.
Proof.
move=> H.
rewrite /get.
move Heq : (store.get _ _) => e.
destruct e => //.
by rewrite store.get_difs_None in Heq.
Qed.

End Store.

Module Expr (A : IntegralType).

Inductive binop_e : Set := add_e | sub_e | mul_e | div_e | mod_e.

Definition binop_e_interp (bo : binop_e) : A.t -> A.t -> A.t :=
  match bo with
    | add_e => A.add
    | sub_e => A.sub
    | mul_e => A.mul
    | div_e => A.div
    | mod_e => A.rem
  end.

Definition binop_e_eq b1 b2 :=
  match b1 with
    | add_e => match b2 with add_e => true | _ => false end
    | sub_e => match b2 with sub_e => true | _ => false end
    | mul_e => match b2 with mul_e => true | _ => false end
    | div_e => match b2 with div_e => true | _ => false end
    | mod_e => match b2 with mod_e => true | _ => false end
  end.

Inductive unaop_e : Set := valabs_e | negate_e.

Definition unaop_e_eq b1 b2 :=
  match b1 with
    | valabs_e => match b2 with valabs_e => true | _ => false end
    | negate_e => match b2 with negate_e => true | _ => false end
  end.

Definition unaop_e_interp uo :=
  match uo with
    | valabs_e => A.abs
    | negate_e => fun x => A.sub (A.of_nat 0) x
  end.

(** Definition of expressions *)
Inductive expr : Type :=
| var_e : var.v -> expr
| cst_e : A.t -> expr
| bop_e : binop_e -> expr -> expr -> expr
| uop_e : unaop_e -> expr -> expr.

Definition nat_e x := cst_e (A.of_nat x).
Definition null := nat_e O.
Notation "a '\+' b" := (bop_e add_e a b) (at level 61, left associativity) : seplog_expr_scope.
Notation "a '\-' b" := (bop_e sub_e a b) (at level 61, left associativity) : seplog_expr_scope.
Notation "a '\*' b" := (bop_e mul_e a b) (at level 58, left associativity) : seplog_expr_scope.
(* NB: the "." before "/e" is to prevent confusion of the rewrite tactic *)
Notation "e1 './e' e2" := (bop_e div_e e1 e2) (at level 75) : seplog_expr_scope.
Notation "e \% n" := (bop_e mod_e e n) (at level 57, left associativity) : seplog_expr_scope.
(* TODO: change notation to .- ? *)
Notation ".--e e" := (uop_e negate_e e) (at level 75) : seplog_expr_scope.
Local Open Scope seplog_expr_scope.
Delimit Scope seplog_expr_scope with seplog_expr.
(* Notation for structures *)
Definition field x f := var_e x \+ cst_e f.
Notation "x '-.>' f " := (field x f) (at level 75) : seplog_expr_scope.

Fixpoint vars (e : expr) : seq var.v :=
  match e with
    | var_e x => x :: nil
    | cst_e z => nil
    | bop_e _ e1 e2 => cat (vars e1) (vars e2)
    | uop_e _ e' => vars e'
  end.

Definition fresh_e x e := (max_lst (vars e) < x)%nat.

Lemma fresh_e_var_e_neq : forall x y, fresh_e x (var_e y) -> x <> y.
Proof.
move=> x y H.
rewrite /fresh_e /= /max_lst in H.
apply/Nat.neq_sym/Nat.lt_neq/ltP/(lt_max_list_inv2 _ _ _ H y).
by left.
Qed.

Fixpoint var_max_lst (l : seq (var.v * expr)) : var.v :=
  match l with
    | nil => O
    | (v, e) :: tl => max (max v (max_lst (vars e))) (var_max_lst tl)
  end.

Definition fresh_lst x l := (var_max_lst l < x)%nat.

Lemma fresh_lst_inv : forall x h0 h1 t, fresh_lst x ((h0, h1) :: t) ->
  fresh_e x h1 /\ x <> h0 /\ fresh_lst x t.
Proof.
move=> x h0 h1 t; rewrite /fresh_lst /=.
case/lt_max_inv; case/lt_max_inv => H1 H2 H3.
rewrite /fresh_e; ssromega.
Qed.

(** the list (without redundancies) of free vars of an expr *)
Fixpoint vars_set (e : expr) : seq var.v :=
  match e with
    | var_e x => x :: nil
    | cst_e z => nil
    | bop_e _ e1 e2 => app_set (vars_set e1) (vars_set e2)
    | uop_e _ e' => vars_set e'
  end.

Lemma incl_vars_vars_set : forall e, inc (vars e) (vars_set e).
Proof.
elim=> [x /= | r /= | bo e1 H1 e2 H2 /= | //].
- by rewrite inE eqxx.
- by [].
- apply/incP/List.incl_app.
  + move/incP in H1; apply/(List.incl_tran H1)/incl_app_set_L => *; exact/eqP.
  + move/incP in H2; apply/(List.incl_tran H2)/incl_app_set_R => *; exact/eqP.
Qed.

Fixpoint expr_eq (e1 e2 : expr) {struct e1} : bool :=
  match e1 with
    | var_e w1 =>
      match e2 with var_e w2 => w1 == w2 | _ => false end
    | cst_e i1 =>
      match e2 with cst_e i2 => A.eqb i1 i2 | _ => false end
    | bop_e bo e11 e12 =>
      match e2 with
        | bop_e bo' e21 e22 =>
          binop_e_eq bo bo' && expr_eq e11 e21 && expr_eq e12 e22
        | _ => false
      end
    | uop_e uo e11 =>
      match e2 with
        | uop_e uo' e22 => unaop_e_eq uo uo' && expr_eq e11 e22 | _ => false
      end
  end.

(** substitute "pattern" for "replacement" in "e" *)
Fixpoint subst_e (e patt repl : expr) {struct e} : expr :=
  match e with
    | var_e w => match expr_eq e patt with
                 | true => repl
                 | _ => e
               end
    | cst_e i => match expr_eq e patt with
                   | true => repl
                   | _ => e
                 end
    | bop_e bo e1 e2 =>
      match expr_eq e patt with
        | true => repl
        | _ => bop_e bo (subst_e e1 patt repl) (subst_e e2 patt repl)
      end
    | uop_e uo e' => match expr_eq e patt with
                       | true => repl
                       | _ => uop_e uo (subst_e e' patt repl)
                     end
  end.

(** Boolean expressions

   neq_b and ge_b are redundant
   (<> =def= ~ _ = _  and  >= =def=  > \/ =)
   but defining then as such slows down evaluation
   (e.g., by a factor 2.5 for ge_b)

   *)
Inductive binop_b : Set := eq_b | neq_b | ge_b | gt_b.

(* TODO: remonter *)

Definition binop_b_interp (bo : binop_b) : A.t -> A.t -> bool :=
match bo with
| eq_b => A.eqb
| neq_b => fun a b => negb (A.eqb a b)
| ge_b => A.geb
| gt_b => A.gtb
end.

Definition binop_b_eq b1 b2 :=
  match b1 with
    | eq_b => match b2 with eq_b => true | _ => false end
    | neq_b => match b2 with neq_b => true | _ => false end
    | ge_b => match b2 with ge_b => true | _ => false end
    | gt_b => match b2 with gt_b => true | _ => false end
  end.

Inductive binop_b2 : Set := and_b | or_b.

Definition binop_b2_interp (bo : binop_b2) : bool -> bool -> bool :=
  match bo with
    | and_b => andb
    | or_b => orb
  end.

Definition binop_b2_eq b1 b2 :=
  match b1 with
    | and_b => match b2 with and_b => true | _ => false end
    | or_b => match b2 with or_b => true | _ => false end
  end.

Inductive expr_b : Type :=
| true_b: expr_b
| bop_b : binop_b -> expr -> expr -> expr_b
| neg_b : expr_b -> expr_b
| bop_b2 : binop_b2 -> expr_b -> expr_b -> expr_b.

(** Number of constructors in an expr_b formula *)
Fixpoint Expr_B_size (e : expr_b) : nat :=
  match e with
    | true_b => 1%nat
    | bop_b _ e1 e2 => 1%nat
    | bop_b2 _ e1 e2 => (1 + (Expr_B_size e1) + (Expr_B_size e2))%nat
    | neg_b e => (1 + Expr_B_size e)%nat
  end.

Lemma expr_b_min_size: forall b, (Expr_B_size b >= 1)%nat.
Proof. elim=> //= *; omega. Qed.

Notation "a '\=' b" := (bop_b eq_b a b) (at level 64, left associativity) : seplog_expr_scope.
Notation "a '\!=' b" := (bop_b neq_b a b) (at level 64, left associativity) : seplog_expr_scope.
Notation "a '\>=' b" := (bop_b ge_b a b) (at level 63, left associativity) : seplog_expr_scope.
Notation "a '\>' b" := (bop_b gt_b a b) (at level 63, left associativity) : seplog_expr_scope.
Notation "a '\&&' b" := (bop_b2 and_b a b) (at level 67, left associativity) : seplog_expr_scope.
Notation "a '\||' b" := (bop_b2 or_b a b) (at level 68, left associativity) : seplog_expr_scope.
Notation "\~ e" := (neg_b e) (at level 60) : seplog_expr_scope.

Fixpoint vars_b (e : expr_b) : seq var.v :=
  match e with
    | true_b => nil
    | bop_b _ e1 e2 => vars e1 ++ vars e2
    | bop_b2 _ e1 e2 => vars_b e1 ++ vars_b e2
    | \~ e => vars_b e
  end.

Definition fresh_b x b := (max_lst (vars_b b) < x)%nat.

(** the list (without redundancies) of free vars of an expr_b *)
Fixpoint vars_b_set (e : expr_b) : seq var.v :=
  match e with
    | true_b => nil
    | bop_b _ e1 e2 => app_set (vars_set e1) (vars_set e2)
    | bop_b2 _ e1 e2 => app_set (vars_b_set e1) (vars_b_set e2)
    | \~ e => vars_b_set e
  end.

Lemma incl_vars_b_vars_b_set : forall e, inc (vars_b e) (vars_b_set e).
Proof.
elim=> // [b e1 e2 |b e1 H1 e2 H2] /=.
- apply/incP.
  apply List.incl_app.
    apply/incP.
    apply (inc_trans (incl_vars_vars_set e1)).
    apply/incP.
    apply incl_app_set_L => *; by apply/eqP.
  apply/incP.
  apply (inc_trans (incl_vars_vars_set e2)).
  apply/incP.
  apply incl_app_set_R => *; by apply/eqP.
- apply/incP/List.incl_app.
    move/incP in H1.
    apply (List.incl_tran H1), incl_app_set_L => *; by apply/eqP.
  move/incP in H2.
  apply (List.incl_tran H2), incl_app_set_R => *; by apply/eqP.
Qed.

Fixpoint expr_b_eq (e1 e2 : expr_b) : bool :=
match e1 with
  | true_b => match e2 with true_b => true | _ => false end
  | bop_b bo f g =>
    match e2 with
      | bop_b bo' f' g' =>
        binop_b_eq bo bo' && expr_eq f f' && expr_eq g g'
      | _ => false
    end
  | bop_b2 bo f g =>
    match e2 with
      | bop_b2 bo' f' g' =>
        binop_b2_eq bo bo' && expr_b_eq f f' && expr_b_eq g g'
      | _ => false
    end
  | \~ e => match e2 with \~ e' => expr_b_eq e e' | _ => false end
end.

(** substitute "pattern" for "replacement" in "e" *)
Fixpoint subst_b (e : expr_b) (patt repl : expr) {struct e} : expr_b :=
  match e with
    | true_b => true_b
    | bop_b bo f g =>
      bop_b bo (subst_e f patt repl) (subst_e g patt repl)
    | bop_b2 bo f g =>
      bop_b2 bo (subst_b f patt repl) (subst_b g patt repl)
    | \~ e => \~ (subst_b e patt repl)
  end.

Module store := Store A.

(** this tactic resolves some simple goals over store_upd *)
Ltac Store_upd :=
  match goal with
    | |- context [store.get ?x (store.upd ?x ?z ?s)] =>
      rewrite -> (store.get_upd' x z s)
    | |- context [store.get ?x (store.upd ?x' ?z ?s)] =>
      rewrite -> (store.get_upd x x' z s); [ idtac | apply/eqP; Uniq_neq]
    | |- _ => fail
  end.

(** Compute the value of an expression in a store *)
Fixpoint eval (e : expr) (s : store.t) : A.t :=
match e with
  | var_e w => store.get w s
  | cst_e i => i
  | bop_e bo e1 e2 => binop_e_interp bo (eval e1 s) (eval e2 s)
  | uop_e uo e' => unaop_e_interp uo (eval e' s)
end.
Notation "'[' x ']_' s" := (store.get x s) (at level 9, format "'[' [  x  ]_ s ']'") : seplog_expr_scope.
Notation "'[' e ']e_' s" := (eval e s) (at level 9, format "'[' [  e  ]e_ s ']'") : seplog_expr_scope.

Lemma store_get_proj s x d : x \in d ->
  [ x ]_ (store.store.proj s d) = [ x ]_ s.
Proof. move=> ?; by rewrite /store.get store.store.get_proj. Qed.

Lemma eval_upd : forall e s v x, ~ x \in vars e ->
  [ e ]e_ (store.upd x v s) = [ e ]e_ s.
Proof.
elim=> // [v s v' x HIn /= | bo e1 IH1 e2 IH2 l /= v x HIn | uo e IH s v x HIn /=].
- rewrite store.get_upd //.
  move: HIn; by rewrite /= mem_seq1 eq_sym => /negP.
- f_equal.
  apply IH1; contradict HIn; by rewrite mem_cat HIn.
  apply IH2; contradict HIn; by rewrite mem_cat HIn orbT.
- by rewrite IH.
Qed.

Lemma eval_upds : forall e xs, disj (vars e) xs ->
  forall s zs, [ e ]e_ (store.upds xs zs s) = [ e ]e_ s.
Proof.
elim => // [v xs H s zs /= | b e1 IH1 e2 IH2 xs H s zs | uo e IH xs H s sz /=].
- rewrite store.get_upds //.
  move/disj_sym in H.
  move/inP.
  apply (disj_not_In H) => /=; by left.
- rewrite /= in H; case/disj_app_inv : H => H1 H2 /=.
  by rewrite IH1 // IH2.
- by rewrite IH.
Qed.

Ltac open_fresh :=
  open_fresh_hypo; open_fresh_goal
with open_fresh_hypo := match goal with
    | H: is_true (fresh_e _ _) |- _ => unfold fresh_e in H; simpl in H; open_fresh_hypo
    | H: is_true (fresh_b _ _) |- _ => unfold fresh_b in H; simpl in H; open_fresh_hypo
    | H: is_true (fresh_lst _ _) |- _ => unfold fresh_lst in H; simpl in H; open_fresh_hypo
    | |- _ =>  idtac
  end
with open_fresh_goal := match goal with
    | |- is_true (fresh_e _ _) => unfold fresh_e; simpl; open_fresh_goal
    | |- is_true (fresh_b _ _) => unfold fresh_b; simpl; open_fresh_goal
    | |- is_true (fresh_lst _ _) => unfold fresh_lst; simpl; open_fresh_goal
    | |- _ => idtac
  end.

Ltac maxinf_resolve := open_fresh; Resolve_lt_max.

Lemma fresh_e_eval : forall e x v s, fresh_e x e ->
  [ e ]e_(store.upd x v s) = [ e ]e_s.
Proof.
induction e; simpl; intros; auto.
- rewrite store.get_upd //.
  rewrite /fresh_e /max_lst /= in H.
  ssromega.
- rewrite IHe1 //; last by maxinf_resolve.
  rewrite IHe2 //; by maxinf_resolve.
- rewrite IHe //; by maxinf_resolve.
Qed.

Lemma eval_upd_subst : forall e s x v,
  [ e ]e_ (store.upd x ([ v ]e_s) s) = [ subst_e e (var_e x) v ]e_ s.
Proof.
elim=> //.
- move=> v s x v0 /=.
  case/boolP : (v == x) => [/eqP -> | /eqP X].
  + by rewrite store.get_upd'.
  + rewrite store.get_upd //; by apply/eqP.
- move=> bo e1 IHe1 e2 IHe2 ? ? ? /=; by rewrite IHe1 IHe2.
- move=> uo e IHe ? ? ? /=; by rewrite IHe.
Qed.

Lemma eval_proj : forall e s d, inc (vars e) d ->
  [ e ]e_ (store.proj s d) = [ e ]e_ s.
Proof.
elim=> //.
- move=> x s d /= H.
  rewrite store_get_proj //; by case: ifPn H.
- move=> bo e1 IH1 he2 IH2 s d /= Hincl.
  rewrite IH1; last first.
    move/incP : Hincl.
    case/incl_app_inv.
    by move/incP.
  rewrite IH2 //.
  move/incP : Hincl.
  case/incl_app_inv.
  by move=> _ /incP.
- move=> uo e IH s d /= Hincl; by rewrite IH.
Qed.

Lemma store_proj_upd (x : var.v) v (s : store.t) (d : seq var.v) :
  x \in d ->
  store.proj (store.upd x v s) d = store.upd x v (store.proj s d).
Proof.
move=> Hx; rewrite /store.upd; destruct Bool.bool_dec;
  [exact: store.store.proj_dif | exact: store.store.proj_union_sing].
Qed.

Lemma abstract_subst_e e x v s : exists e', [ e ]e_ s = [ subst_e e' (var_e x) v ]e_ s.
Proof. by exists (cst_e ([ e ]e_ s)). Qed.

Lemma fresh_e_subst_e : forall e x v0 e0,
  fresh_e x e -> x <> v0 -> fresh_e x e0 ->
  fresh_e x (subst_e e (var_e v0) e0).
Proof.
induction e.
- simpl; intros.
  by destruct (s == v0).
- by move=> x v0 e0 H /= H0 H1.
- move=> x v0 e0 H H0 H1.
  have H2 : fresh_e x e1 by maxinf_resolve.
  have H3 : fresh_e x e2 by maxinf_resolve.
  move: {IHe1}(IHe1 _ _ _ H2 H0 H1) => IHe1.
  move: {IHe2}(IHe2 _ _ _ H3 H0 H1) => IHe2.
  by maxinf_resolve.
- move=> x v e' H Hneq H' /=; by apply IHe.
Qed.

(** simultaneous substitutions *)
Fixpoint subst_e_lst (l : seq (var.v * expr)) (e: expr) {struct l} : expr :=
  match l with
    | nil => e
    | (x, e') :: tl => subst_e_lst tl (subst_e e (var_e x) e')
  end.

Lemma subst_e_lst_cst_e : forall l v s, [ subst_e_lst l (cst_e v) ]e_ s =  v.
Proof.
induction l.
by intuition.
induction a; simpl; intros.
by apply IHl.
Qed.

Lemma subst_e_lst_eval : forall l e x v s, fresh_e x e -> fresh_lst x l ->
  [ subst_e_lst l e ]e_(store.upd x v s) = [ subst_e_lst l e ]e_s.
Proof.
induction l; simpl; intros; auto.
- rewrite fresh_e_eval //.
- destruct a.
  rewrite IHl //.
  case/fresh_lst_inv : H0 => H2 [H4 H5].
  by apply fresh_e_subst_e.
  by maxinf_resolve.
Qed.

(** Compute the value of a boolean expression *)
Fixpoint eval_b (e : expr_b) (s : store.t) : bool :=
match e with
  | true_b  => true
  | bop_b bo e1 e2 => binop_b_interp bo ([ e1 ]e_ s) ([ e2 ]e_ s)
  | bop_b2 bo e1 e2 => binop_b2_interp bo (eval_b e1 s) (eval_b e2 s)
  | \~ e => ~~ eval_b e s
end.

Notation "'[' e ']b_' s" := (eval_b e s) (at level 9, format "'[' [  e  ]b_ s ']'") : seplog_expr_scope.
Notation " b1 =b> b2 " := ((\~ b1) \|| b2) (right associativity, at level 80) : seplog_expr_scope.

Lemma eval_b_neg : forall t s, [ \~ t ]b_s = ~~ [ t ]b_ s.
Proof. done. Qed.

Lemma expr_b_neg_involutive a s :  [ \~ \~ a ]b_ s = [ a ]b_s.
Proof. move=> /=. by rewrite Bool.negb_elim. Qed.

Lemma expr_b_impl_intro b1 b2 s : [ b1 ]b_s -> [ b1 =b> b2 ]b_s -> [ b2 ]b_s.
Proof. by move=> /= ->. Qed.

Fixpoint subst_b_lst (l : seq (var.v * expr)) (e : expr_b) {struct l}: expr_b :=
  match l with
    | nil => e
    | (x, e') :: tl => subst_b_lst tl (subst_b e (var_e x) e')
  end.

Lemma eval_b_upd : forall b s v x, ~ x \in vars_b b ->
  [ b ]b_ (store.upd x v s) = [ b ]b_ s.
Proof.
elim=> //=.
move=> b e e0 s v0 x /negP/inP H.
  rewrite !eval_upd //.
  contradict H; apply/inP; by rewrite mem_cat H orbT.
  contradict H; apply/inP; by rewrite mem_cat H.
move=> b IHb s v0 x H; rewrite IHb //.
move=> b b1 IHb1 b2 IHb2 s v0 x H.
rewrite IHb1 // ?IHb2 //.
contradict H; by rewrite mem_cat H orbT.
contradict H; by rewrite mem_cat H.
Qed.

Lemma eval_b_proj : forall e s d, inc (vars_b e) d ->
  [ e ]b_ (store.proj s d) = [ e ]b_ s.
Proof.
elim=> //.
- move=> b e1 e2 s d /= Hincl.
  rewrite eval_proj; last first.
    move/incP : Hincl.
    by case/incl_app_inv => /incP.
  rewrite eval_proj //.
  move/incP : Hincl.
  by case/incl_app_inv => _ /incP.
- move=> e IH s d /= Hincl.
  f_equal.
  by apply IH.
- move=> b e1 H1 e2 H2 s d /= Hincl.
  rewrite H1; last first.
    move/incP : Hincl.
    by case/incl_app_inv => /incP.
  rewrite H2 //.
  move/incP : Hincl.
  by case/incl_app_inv => _ /incP.
Qed.

Lemma eval_b_upds : forall e xs, disj (vars_b e) xs ->
  forall s zs, [ e ]b_ (store.upds xs zs s) = [ e ]b_ s.
Proof.
elim => // [b e1 e2 xs H | e IH xs /= H s zs | b e1 IH1 e2 IH2 xs H].
- rewrite /= in H; case/disj_app_inv : H => H1 H2 s zs.
  by rewrite /= !eval_upds.
- by rewrite IH.
- rewrite /= in H; case/disj_app_inv : H => H1 H2 s zs /=.
  by rewrite IH1 // IH2.
Qed.

Lemma eval_b_upd_subst : forall b s x v,
  [ b ]b_ (store.upd x ([ v ]e_ s) s) = [ subst_b b (var_e x) v ]b_s.
Proof.
induction b; simpl; auto; try (intros; repeat rewrite eval_upd_subst; auto ).
by rewrite IHb.
by rewrite IHb1 IHb2.
Qed.

Fixpoint eval_b_Prop (e : expr_b) (s : store.t) : Prop :=
  match e with
    | true_b => True
    | f \= g => [ f ]e_ s = [ g ]e_ s
    | f \!= g => [ f ]e_ s <> [ g ]e_ s
    | f \>= g => A.ge ([ f ]e_ s) ([ g ]e_ s)
    | f \> g => A.gt ([ f ]e_ s) ([ g ]e_ s)
    | f \&& g => eval_b_Prop f s /\ eval_b_Prop g s
    | f \|| g => eval_b_Prop f s \/ eval_b_Prop g s
    | \~ e => ~ eval_b_Prop e s
  end.

Lemma expr_bP : forall e s, [ e ]b_ s <-> eval_b_Prop e s.
Proof.
elim=> //= [|e IHe s|b e1 IHe1 e2 IHe2 s].
- case=> [e e0 s|e e0 s|e e0 s|e e0 s].
  + split=> [H|->]; exact/A.eqP.
  + split; by move/A.eqP.
  + split=> H; exact/A.geP.
  + split=> H; exact/A.gtP.
- split=> H.
  + rewrite <- (IHe s); exact/negP.
  + by apply/negP; rewrite (IHe s).
- split=> H.
  + case: (IHe1 s) => H0 H1.
    case: (IHe2 s) => H2 H3.
    destruct b.
    * case/andP : H => H4 H5; by auto.
    * case/orP: H => H4; by intuition.
  + destruct b.
    * apply/andP.
      case: (IHe1 s) => H0 H1.
      case: (IHe2 s) => H2 H3.
      by intuition.
    * apply/orP.
      case: (IHe1 s) => H0 H1.
      case: (IHe2 s) => H2 H3.
      by intuition.
Qed.

Lemma expr_b_reflect b1 b2 s :
  ([ b1 ]b_s <-> [ b2 ]b_s) -> [ b1 ]b_ s = [ b2 ]b_ s.
Proof.
move=> [H0 H1].
case/boolP: ([ b1 ]b_s) => X.
  case/boolP: ([ b2 ]b_s) => //.
  by rewrite H0.
case/boolP : ([ b2 ]b_s) => Y //.
move: (H1 Y) => Z //.
by rewrite Z in X.
Qed.

Lemma expr_b_reflect' b1 b2 s :
  [ b1 ]b_ s = [ b2 ]b_ s -> ([ b1 ]b_s <-> [ b2 ]b_s).
Proof. move=> H; split=> H0; [by rewrite -H | by rewrite H]. Qed.

Ltac eval_b2Prop_hyp h :=
  match goal with
    | H : is_true (eval_b ?e ?s) |- _ =>
      move: {H}(proj1 (expr_bP e _) H) => H; simpl in H
  end.

Ltac eval_b2Prop_hyps :=
  match goal with
    | id : is_true (eval_b ?e ?s) |- _ => eval_b2Prop_hyp id; eval_b2Prop_hyps
    | id : is_true (~~ eval_b ?e ?s) |- _ =>
      rewrite <- eval_b_neg in id; eval_b2Prop_hyps
    | |- _ => idtac
  end.

Ltac eval_b2Prop_goal :=
  match goal with
    | |- is_true (eval_b ?e ?s) => apply (proj2 (expr_bP e s)); simpl
    | |- is_true (~~ eval_b ?e ?s) =>
      rewrite <- eval_b_neg;
        eval_b2Prop_goal
    | |- _ => idtac
  end.

Ltac eval2Prop_hyp :=
  match goal with
    | h : context [ (eval (var_e ?e) ?s) ] |- _ =>
      simpl in h
  end.

Ltac omegab :=
  eval_b2Prop_hyps ; eval_b2Prop_goal ;
  repeat eval2Prop_hyp ;
  (try tauto || ssromega ||
    ( (repeat open_integral_type_hyp);
       open_integral_type_goal );
    (omegaz' ssromega)).

End Expr.

Module Assert (A : IntegralType).

Module Import expr_m := Expr A.

Local Open Scope seplog_expr_scope.

Canonical Structure t_eqMixin := EqMixin A.eqP.
Canonical Structure t_eqType := Eval hnf in EqType _ t_eqMixin.

Module int_type <: EQTYPE.
  Definition A : eqType := t_eqType.
End int_type.

Module AOrder <: ORDER.

Definition A := A.t.

Definition ltA : A -> A -> bool := fun a b => negb (A.geb a b).

Lemma ltA_trans n m p : ltA m n -> ltA n p -> ltA m p.
Proof.
rewrite /ltA => /negP m_n n_p.
apply/negP.
contradict m_n.
apply/A.geP/(A.ge_trans p); first exact/A.geP.
move: n_p.
rewrite A.gebNgt => /negPn ?; exact/A.gtW/A.gtP.
Qed.

Lemma ltA_irr a : ltA a a = false.
Proof. exact/negPn/A.geP/A.ge_refl. Qed.

Lemma ltA_total m n : (m != n) = (ltA m n) || (ltA n m).
Proof.
case/boolP : (m == n) => m_n; first by rewrite (eqP m_n) ltA_irr.
by rewrite /ltA A.gebNgt negbK A.gtbE eq_sym !m_n andbC /= orbN.
Qed.

End AOrder.

Module heap := finmap.map AOrder int_type.

Notation "k '\d\' m" := (heap.dif k m) : heap_scope.
Notation "k '\U' m" := (heap.union k m) : heap_scope.
Notation "k '#' m" := (heap.disj k m) : heap_scope.
Local Open Scope heap_scope.

Definition assert := store.t -> heap.t -> Prop.

Definition TT : assert := while.TT store.t heap.t.
Definition FF : assert := while.FF store.t heap.t.
Definition Not (P : assert) : assert := while.Not P.
Notation "P '//\\' Q" := (while.And store.t heap.t P Q) (at level 80, right associativity) : seplog_assert_scope.
Notation "P '\\//' Q" := (while.Or store.t heap.t P Q) (at level 80, right associativity) : seplog_assert_scope.
Notation "P ===> Q" := (while.entails store.t heap.t P Q) (at level 90, no associativity) : seplog_assert_scope.
Notation "P <==> Q" := (while.equiv store.t heap.t P Q) (at level 90, no associativity) : seplog_assert_scope.
Local Open Scope seplog_assert_scope.
Delimit Scope seplog_assert_scope with seplog_assert.

Definition x_EQ_y (x y : var.v) : assert := fun s _ => [ x ]_ s = [ y ]_ s.

(** The separation conjunction *)
Definition con (P Q : assert) : assert := fun s h =>
  exists h1 h2, h1 # h2 /\ h = h1 \U h2 /\ P s h1 /\ Q s h2.
Notation "P ** Q" := (con P Q) (at level 80, right associativity) : seplog_assert_scope.

Lemma con_cons : forall (P Q : assert) s h1 h2, h1 # h2 ->
  P s h1 -> Q s h2 -> (P ** Q) s (h1 \U h2).
Proof. move=> P Q s h1 h2 ? ? ?; exists h1, h2; repeat (split => //). Qed.

Lemma semi_distributivity (P1 P2 Q : assert) : (P1 //\\ P2) ** Q ===> (P1 ** Q) //\\ (P2 ** Q).
Proof. move=> ? ? [h1 [h2 [? [? [[? ?] ?]]]]]; split; exists h1, h2 => //. Qed.

(** an assertion is said to be pure if, for any store, it is independent of the heap *)
Definition pure (Q : assert) := forall s h h', Q s h <-> Q s h'.

Lemma con_and_pure (P Q R : assert) : pure R -> (P ** Q) //\\ R ===> P ** (Q //\\ R).
Proof.
move=> HpureR s h [H1 H2].
rewrite /pure in HpureR.
case: H1 => h1 [h2 [Hdisj [Hunion [Hh1 Hh2]]]].
exists h1; exists h2.
repeat (split => //).
by apply (proj1 (HpureR _ _ _) H2).
Qed.

(** Extensionality of predicates can be safely added to Coq (see Coq FAQ) *)
Axiom assert_ext: forall P Q, P <==> Q -> P = Q.

(* TODO: put in while.v? *)
Lemma AndCE P Q : (P //\\ Q) = (Q //\\ P).
Proof. apply assert_ext=> s h; split; case=> HP HQ //. Qed.

Lemma AndAE1 P Q R : (Q //\\ P //\\ R) ===> ((Q //\\ P) //\\ R).
Proof. move=> s h [] H1 [] H2 H3. rewrite /while.And. by intuition. Qed.

Lemma AndAE2 P Q R : ((Q //\\ P) //\\ R)  ===> (Q //\\ P //\\ R).
Proof. move=> s h [] [] H1 H2 H3; rewrite /while.And; by intuition. Qed.

Lemma AndAE P Q R : (Q //\\ P //\\ R) = ((Q //\\ P) //\\ R).
Proof. apply assert_ext; split; by [apply AndAE1 | apply AndAE2]. Qed.

Lemma conC P Q : P ** Q ===> Q ** P.
Proof.
move=> s h [h1 [h2 [Ha [Hb [Hc Hd]]]]].
exists h2, h1.
split; first by apply heap.disj_sym.
split => //.
apply trans_eq with (h1 \U h2) => //.
by apply heap.unionC.
Qed.

Lemma conCE P Q : (P ** Q) = (Q ** P).
Proof. apply assert_ext => s h; split => H; by apply conC. Qed.

Lemma conA P Q R : (P ** Q) ** R ===> P ** (Q ** R).
Proof.
move=> s h [h12 [h3 [H1 [H2 [H3 H4]]]]].
case: H3 => [h1 [h2 [H5 [H6 [H7 H8]]]]].
exists h1, (h2 \U h3); split.
- apply heap.disjhU => //.
  move/heap.disj_sym : H1.
  rewrite H6.
  case/heap.disj_union_inv => X _.
  by apply heap.disj_sym.
- split.
  + by rewrite heap.unionA H2 H6.
  + split => //.
    exists h2, h3; split => //.
    move/heap.disj_sym : H1.
    rewrite H6.
    case/heap.disj_union_inv => _ X.
    by apply heap.disj_sym.
Qed.

Lemma conAE P Q R : ((Q ** P) ** R) = (Q ** (P ** R)).
Proof.
apply assert_ext => s h; split=> H.
- by apply conA.
- rewrite conCE.
  apply conA.
  rewrite conCE.
  apply conA.
  by rewrite conCE.
Qed.

Lemma con_TT P : P ===> P ** TT.
Proof.
move=> s h H.
exists h, heap.emp.
split.
by apply heap.disjhe.
by rewrite heap.unionhe.
Qed.

Lemma monotony s s' h (P Q P' Q' : assert) :
  (forall h, P s h -> P' s' h) -> (forall h, Q s h -> Q' s' h) ->
  (P ** Q) s h -> (P' ** Q') s' h.
Proof.
move=> HP HQ [h1 [h2 [Hdisj [Hunion [Hh1 Hh2]]]]].
rewrite Hunion.
exists h1, h2; repeat (split => //).
by apply HP.
by apply HQ.
Qed.

Lemma monotony' P1 P2 P3 P4 :
  P1 ===> P2 -> P3 ===> P4 -> P1 ** P3 ===> P2 ** P4.
Proof. move=> *; rewrite /while.entails => s h; eapply monotony; eauto. Qed.

Definition emp : assert := fun s h => h = heap.emp.

Lemma con_emp P : P ** emp ===> P .
Proof.
move=> s h [h1 [h2 [Hdisj [Hunion [HPh1 Hemph2]]]]].
rewrite /emp in Hemph2; subst h2.
by rewrite Hunion heap.unionhe.
Qed.

Lemma con_emp' P : P ===> P ** emp.
Proof.
move=> s h H.
exists h, heap.emp; repeat (split => //).
by apply heap.disjhe.
by rewrite heap.unionhe.
Qed.

Lemma con_emp_equiv P : (P ** emp) = P .
Proof. apply assert_ext; split; [apply con_emp|apply con_emp']. Qed.

(** The separation implication *)
Definition imp (P Q : assert) : assert := fun s h =>
  forall h', h # h' /\ P s h' -> forall h'', h'' = h \U h' -> Q s h''.
Notation "P -* Q" := (imp P Q) (at level 80) : seplog_assert_scope.

(* Alternative definition *)
(*Definition imp2 (P Q:assert) : assert := fun s h => forall h', h # h' /\ P s h' -> Q s (h +++ h').*)

Lemma emp_imp s h (P : assert) : P s h -> (emp -* P) s h.
Proof.
move=> HP.
rewrite /imp => h' [X1 X2] h'' Hh''.
rewrite /emp in X2; subst h'.
by rewrite heap.unionhe in Hh''; subst h''.
Qed.

Lemma emp_imp_inv s h (P : assert) : (emp -* P) s h -> P s h .
Proof.
rewrite /imp => H.
apply H with heap.emp.
split; last by done.
by apply heap.disjhe.
by rewrite heap.unionhe.
Qed.

Lemma mp P Q : Q ** (Q -* P) ===> P.
Proof.
move=> s h [h1 [h2 [Hh1h2disj [Hh1h2union [HQh1 HQimpP]]]]].
apply HQimpP with h1.
split => //.
by apply heap.disj_sym.
rewrite heap.unionC //; by apply heap.disj_sym.
Qed.

Lemma pm P Q : Q ===> P -* (P ** Q).
Proof.
move=> s h HQ h' [Hhh'disj HPh'] h'' Hhh'union.
exists h'; exists h; repeat (split => //).
apply heap.disj_sym => //.
rewrite heap.unionC => //; apply heap.disj_sym => //.
Qed.

Lemma monotony_imp s s' h (P Q P' Q' : assert) :
  (forall h, P' s' h -> P s h) -> (forall h, Q s h -> Q' s' h) ->
  (P -* Q) s h -> (P' -* Q') s' h.
Proof.
move=> HP HQ H.
rewrite /imp => h' [X1 X2] h'' Hh''.
apply HQ.
apply H with h'; last by done.
split => //; by apply HP.
Qed.

Lemma monotony_imp' P1 P2 P3 P4 :
  P2 ===> P1 -> P3 ===> P4 -> P1 -* P3 ===> P2 -* P4.
Proof.
move=> P2_P1 P3_P4 => s h H.
rewrite /imp => h' [X1 X2] h'' H1.
apply P3_P4.
apply (H h'); last by done.
split; [done | by apply P2_P1].
Qed.

Lemma currying (P1 P2 P3 : assert) s :
  (forall h, (P1 ** P2) s h -> P3 s h) ->
    forall h, P1 s h -> (P2 -* P3) s h.
Proof.
move=> H h H' h' [H1 H2] h'' H3.
apply H => //; by exists h, h'.
Qed.

Lemma uncurrying (P1 P2 P3 : assert) s :
  (forall h, P1 s h -> (P2 -* P3) s h) ->
    forall h, (P1 ** P2) s h -> P3 s h.
Proof.
move=> H h [h1 [h2 [H1 [H2 [HP1h1 H4]]]]].
apply H in HP1h1; eapply HP1h1; eauto.
Qed.

(** Tactics to decompose / compose heaps related by separating conjunction *)

Ltac Heap_emp_clean :=
  match goal with
    | id: ?h = heap.emp |- _ => subst h; Heap_emp_clean
    | id: emp ?s ?h |- _ => red in id; Heap_emp_clean
    | id: heap.emp = ?h |- _ => subst h; Heap_emp_clean
    | _ => idtac
  end.

Ltac case_sepcon H :=
  move: H ;
  match goal with
    | |- (con _ _) ?s ?h -> _ =>
      let h1 := fresh h "1" in
      let h2 := fresh h "2" in
      let Hdisj := fresh h1 "_d_" h2 in
      let Hunion := fresh h1 "_U_" h2 in
      let Hh1 := fresh H "_" h1 in
      let Hh2 := fresh H "_" h2 in
      case => h1 [h2 [Hdisj [Hunion [Hh1 Hh2]]]]
  end.

Module map_tac_m := Map_Tac heap.

Ltac Compose_sepcon id1 id2:=
  exists id1; exists id2; split;
    [Heap_emp_clean ; map_tac_m.Disj |
      (split; [Heap_emp_clean; map_tac_m.Equal | split; idtac])].

Definition mapsto e e' s h := exists p, [ e ]e_ s = p /\ h = heap.sing p ([ e' ]e_s).
Notation "e1 '|~>' e2" := (mapsto e1 e2) (at level 77, no associativity) : seplog_assert_scope.

Lemma singl_equal s h1 h2 e1 e2 e3 e4 :
  (e1 |~> e2) s h1 -> (e3 |~> e4) s h2 ->
  [ e1 ]e_ s = [ e3 ]e_ s -> [ e2 ]e_ s = [ e4 ]e_ s -> h1 = h2.
Proof. by move=> [p_e1 [<- ->]] [p_e3 [<- ->]] -> ->. Qed.

Lemma singl_disj_neq e1 e2 e3 e4 h1 h2 s :
  (e1 |~> e2) s h1 -> (e3 |~> e4) s h2 -> h1 # h2 ->
  [ e1 ]e_ s <> [ e3 ]e_ s.
Proof.
move=> [? [? ?]] [? [? ?]]; subst; by move/heap.disj_sing'/eqP.
Qed.

Lemma mapsto_strictly_exact e v Q s h :
  (e |~> v ** TT) s h /\ Q s h -> (e |~> v ** (e |~> v -* Q)) s h.
Proof.
move=> [H1 H2].
case_sepcon H1.
Compose_sepcon h1 h2; first by assumption.
move=> h1' [X1 X2] h' Hh'.
have ? : h1' = h1 by apply (singl_equal _ _ _ _ _ _ _ X2 H1_h1).
subst h1'.
suff : h' = h by move=> ->.
by map_tac_m.Equal.
Qed.

Lemma mapsto_strictly_exact' e v (Q : assert) s h1 h2 :
  Q s (h1 \U h2) -> h1 # h2  -> (e |~> v) s h1 -> (e |~> v -* Q) s h2.
Proof.
move=> HQ h1_d_h2 H_h1.
rewrite /imp => h' [X1 X2] h'' Hh''.
move: (singl_equal _ _ _ _ _ _ _ H_h1 X2 (refl_equal _) (refl_equal _)) => ?.
subst h'.
by rewrite Hh'' heap.unionC.
Qed.

Lemma mapsto_store_upd_subst e1 e2 x p s h :
  (subst_e e1 (var_e x) (cst_e p) |~> subst_e e2 (var_e x) (cst_e p)) s h ->
  (e1 |~> e2) (store.upd x p s) h.
Proof.
intros.
red in H; red.
inversion_clear H.
inversion_clear H0.
exists x0.
by split; rewrite (eval_upd_subst _ _ _ (cst_e p)).
Qed.

(* TODO: change the order of parameters *)
Lemma mapsto_ext s s' h e1' e2' e1 e2 :
  [ e1' ]e_ s' = [ e1 ]e_ s -> [ e2' ]e_ s' = [ e2 ]e_ s ->
  (e1' |~> e2') s' h -> (e1 |~> e2) s h.
Proof. move=> H H0 [] x [H1 H2]; exists x; by rewrite -H -H0. Qed.

Definition cell_exists (e1 : expr) : assert := fun s h => exists y, (e1 |~> y) s h.
Notation " e '|~>_' " := (cell_exists e) (right associativity, at level 77) : seplog_assert_scope.

Lemma cell_exists_ext s s' h e1 e2 :
  (e1 |~>_) s' h -> [ e1 ]e_s' = [ e2 ]e_s -> (e2 |~>_) s h.
Proof.
move=> [p H] H'.
exists (cst_e [ p ]e_s'); by eapply mapsto_ext; eauto.
Qed.

(** Tactic to solve goals of the form: (e |~> e') s h *)

Ltac Mapsto :=
  match goal with
    | id: (?e1 |~> ?e2) ?s1 ?h |- (?e3 |~> ?e4) ?s2 ?h =>
      apply (mapsto_ext s2 s1 h e1 e2 e3 e4) ;
        [simpl; (omegab || (repeat Store_upd => //) || auto)|
          simpl; (omegab || (repeat Store_upd => //) || auto) |
          exact id]
    | id: (?e1 |~>_) ?s1 ?h |- (?e3 |~>_) ?s2 ?h =>
      apply (cell_exists_ext s2 s1 h e1 e3 id);
        (simpl; (omegab || (repeat Store_upd => //) || auto))
  end.

(** tactics to apply monotony and adjunction *)

Ltac assocs_sepcon :=
  match goal with
    | |- ?P -> _  => repeat rewrite conAE
  end.

Ltac rotate_sepcon :=
  match goal with
    | |- ?P -> _ => rewrite conCE; assocs_sepcon
  end.

Ltac try_monotony :=
match goal with
  | |- (?P ** ?PP) ?S ?SS ?M ?H -> (?P ** ?QQ) ?S ?H =>
    apply monotony; [intros; auto | intros; idtac]
  | |- ((?L |~> ?V) ** ?PP) ?S ?H -> ((?K |~> ?W) ** ?QQ) ?S ?H =>
    apply monotony; [intros; Mapsto | intros; idtac]
  | |- (?P -* ?PP) ?S ?H -> (?Q -* ?QQ) ?S ?H =>
(* TODO: replace with monotony_imp, try to expand use of this tactic *)
    apply monotony_imp';
      [rewrite /while.entails; intros; Mapsto |
       rewrite /while.entails; intros; idtac]
  | |- (?P ** ?PP) ?S ?H -> (?Q ** ?QQ) ?S ?H =>
    rotate_sepcon; try_monotony
end.

Ltac Monotony Hyp := generalize Hyp; clear Hyp; try_monotony.

Fixpoint mapstos (e : expr) (l : seq expr) {struct l} : assert :=
  match l with
    | nil => emp
    | e1 :: tl => e |~> e1 ** mapstos (e \+ cst_e (A.of_nat 1)) tl
  end.
Notation "x '|-->' l" := (mapstos x l) (at level 77) : seplog_assert_scope.

(* TODO: changer l'order des parametres *)
Lemma mapstos_ext : forall l s h e' e, [ e' ]e_s = [ e ]e_s ->
  (e' |--> l) s h -> (e |--> l) s h.
Proof.
elim=> // a l IH /= s h e' e H0 H.
case: H => h1 [h2 [H [H2 [H1 H4]]]].
exists h1; exists h2; repeat (split => //).
by eapply mapsto_ext; eauto.
move: H4 ; apply IH => /=; by rewrite H0.
Qed.

(** A specialization version of mapstos for lists of integers *)
Definition mapstos' (e : expr) (lst : seq A.t) :=
  mapstos e (map (fun x => cst_e x) lst).
Notation "x '|--->' l" := (mapstos' x l) (at level 77).

Lemma mapstos'_app_sepcon : forall l1 l2 st s h, (st |---> l1 ++ l2) s h ->
  (st |---> l1 ** (st \+ nat_e (size l1)) |---> l2) s h.
Proof.
induction l1; simpl; intros.
- rewrite {1}/mapstos' /=.
  rewrite conCE.
  apply con_emp'.
  rewrite /mapstos' in H *.
  move: H; apply mapstos_ext => /=; by rewrite A.add0.
- rewrite /mapstos' /= in H.
  case_sepcon H.
  move: {H_h2}(IHl1 _ _ _ _ H_h2) => H_h2.
  case_sepcon H_h2.
  Compose_sepcon (h1 \U h21) h22.
  rewrite /mapstos' /=.
  Compose_sepcon h1 h21; assumption.
  rewrite /mapstos' in H_h2_h22 *.
  move: H_h2_h22; apply mapstos_ext => /=.
  by rewrite /= -A.addA A.add1.
Qed.

Lemma mapstos'_cons_sepcon a l st s h : (st |---> a :: l) s h ->
  (st |~> cst_e a ** (st \+ nat_e 1) |---> l) s h.
Proof.
intros.
rewrite (_ : a :: l = (a :: nil) ++ l) in H; [idtac | auto].
apply mapstos'_app_sepcon in H.
simpl in H.
unfold mapstos' at 1 in H.
simpl in H.
case_sepcon H.
Compose_sepcon h1 h2.
- by apply con_emp.
- assumption.
Qed.

Lemma mapstos'_sepcon_app : forall l1 l2 st s h,
  (st |---> l1 ** (st \+ nat_e (size l1)) |---> l2) s h ->
  (st |---> l1 ++ l2) s h.
Proof.
elim.
- move=> l2 st s h H.
  case_sepcon H.
  rewrite /mapstos' /= /mapstos /= /emp in H_h1; subst h1.
  rewrite heap.unioneh in h1_U_h2; subst h2.
  rewrite /mapstos' /= in H_h2.
  move: H_h2; apply mapstos_ext => /=; by rewrite /= A.add0.
- move=> hd tl IH l2 st s h H.
  case_sepcon H.
  rewrite /mapstos' /= in H_h1.
  case_sepcon H_h1.
  rewrite /mapstos' /=.
  Compose_sepcon h11 (h12 \U h2) => //.
  apply IH.
  Compose_sepcon h12 h2.
  + move: H_h1_h12; by apply mapstos_ext.
  + move: H_h2; apply mapstos_ext => /=.
    rewrite /= (_: S (size tl) = size tl + 1)%nat; last by ssromega.
    by rewrite /= -A.addA A.add1 addnC.
Qed.

(** independence of an assertion w.r.t. a list of variables *)
Definition inde (l : seq var.v) (P : assert) := forall s h,
  (forall x v, x \in l -> (P s h <-> P (store.upd x v s) h)).

Lemma inde_nil P : inde nil P.
Proof. by rewrite /inde => ? ? ? ?; rewrite in_nil. Qed.

Lemma inde_upd_store (P : assert) x z s h :
  inde (x :: nil) P -> P s h -> P (store.upd x z s) h.
Proof. move=> H H0; by rewrite -(H s h x z) //= in_cons eqxx. Qed.

Local Open Scope nat_scope.

(* TODO: clean *)
Lemma fresh_b_inde: forall b x v, fresh_b x b ->
  inde (x :: nil) (fun s h => [ b ]b_ s = v).
Proof.
induction b; simpl; intros; auto.
- red.
  by intuition.
- rewrite /inde; intros.
  rewrite mem_seq1 in H0.
  move/eqP in H0.
  split; intros.
  rewrite fresh_e_eval; last by maxinf_resolve.
  rewrite fresh_e_eval //. by maxinf_resolve.
  rewrite fresh_e_eval in H1; last by maxinf_resolve.
  rewrite fresh_e_eval // in H1. by maxinf_resolve.
- rewrite /inde; intros.
  split; intros.
  + case: (IHb x (negb v) H s h x0 v0 H0) => H2 _.
    by rewrite H2 // ?negbK // -H1 negbK.
  + case: (IHb x (negb v) H s h x0 v0 H0) => H2 H3.
    by rewrite H3 // ?negbK // -H1 negbK.
- rewrite /inde; split; intros.
  rename b1 into b. rename b2 into b1. rename b3 into b2.
  destruct b.
  + induction v.
    * apply/andP.
      have [H3 H4] : [ b1 ]b_ s /\ [ b2 ]b_ s by case/andP : H1.
      split.
      - have H2 : fresh_b x b1 by maxinf_resolve.
        case: (IHb1 x true H2 s h x0 v0 H0) => H5 _; by apply H5.
      - have H2 : fresh_b x b2 by maxinf_resolve.
        case: (IHb2 _ true H2 s h x0 v0 H0) => H5 _; by apply H5.
    * case/nandP : H1 => H2.
      - apply/nandP; left.
        have H1 : fresh_b x b1 by maxinf_resolve.
        case (IHb1 x false H1 s h x0 v0 H0) => H3 _; rewrite H3 //; by apply/negbTE.
      - apply/nandP; right.
        have H1 : fresh_b x b2 by maxinf_resolve.
        case: (IHb2 x false H1 s h x0 v0 H0) => H3 _; rewrite H3 //; by apply/negbTE.
  + induction v.
    * apply/orP.
      case/orP : H1 => H2.
      * left.
        have H1 : fresh_b x b1 by maxinf_resolve.
        case: (IHb1 x true H1 s h x0 v0 H0) => H3 _; by apply H3.
      * right.
        have H1 : fresh_b x b2 by maxinf_resolve.
        case: (IHb2 x true H1 s h x0 v0 H0) => H3 _; by apply H3.
    * case/norP : H1 => H1 H2.
      rewrite /=.
      apply/norP; split.
      - have H3 : fresh_b x b1 by maxinf_resolve.
        case: (IHb1 x false H3 s h x0 v0 H0) => H4 _; rewrite H4 //; by apply/negbTE.
      - have H3 : fresh_b x b2 by maxinf_resolve.
        case: (IHb2 x false H3 s h x0 v0 H0) => H4  _; rewrite H4 //; by apply/negbTE.
- rename b1 into b. rename b2 into b1. rename b3 into b2.
  destruct b.
  + induction v.
    apply andb_true_intro.
    have [H3 H4] : true = [ b1 ]b_ (store.upd x0 v0 s) /\ true = [ b2 ]b_ (store.upd x0 v0 s) by apply Bool.andb_true_eq.
    split.
    assert (fresh_b x b1) by maxinf_resolve.
    generalize (IHb1 x true H2 s h x0 v0 H0); intro X; inversion_clear X.
    by intuition.
    assert (fresh_b x b2) by maxinf_resolve.
    generalize (IHb2 x true H2 s h x0 v0 H0); intro X; inversion_clear X.
    by intuition.
    generalize (Bool.andb_false_elim _ _ H1); intro X; inversion_clear X.
    apply Bool.andb_false_intro1.
    assert (fresh_b x b1) by maxinf_resolve.
    generalize (IHb1 x false H3 s h x0 v0 H0); intro X; inversion_clear X.
    by intuition.
    apply Bool.andb_false_intro2.
    assert (fresh_b x b2) by maxinf_resolve.
    generalize (IHb2 x false H3 s h x0 v0 H0); intro X; inversion_clear X.
    by intuition.
  + induction v.
    * apply Bool.orb_true_intro.
      case: (Bool.orb_prop _ _ H1) => H2; [left | right].
      - assert (fresh_b x b1) by maxinf_resolve.
        case: (IHb1 x true H3 s h x0 v0 H0) => H4 H5.
        by intuition.
      - assert (fresh_b x b2) by maxinf_resolve.
        case: (IHb2 x true H3 s h x0 v0 H0) => H4 H5.
        by intuition.
    * move: (Bool.orb_false_elim _ _ H1) => H2.
      apply Bool.orb_false_intro.
      - assert (fresh_b x b1) by maxinf_resolve.
        case: (IHb1 x false H3 s h x0 v0 H0) => H4 H5.
        by intuition.
      - assert (fresh_b x b2) by maxinf_resolve.
        case: (IHb2 x false H3 s h x0 v0 H0) => H4 H5.
        by intuition.
Qed.

Local Close Scope nat_scope.

Lemma inde_TT : forall l, inde l TT. Proof. by []. Qed.

Lemma inde_sep_con l P Q : inde l P -> inde l Q -> inde l (P ** Q).
Proof.
move=> H H0 s h x v H1; split=> H2;
  case: H2 => x0 [x1 [Ha [Hb [Hc Hd]]]]; exists x0; exists x1; repeat (split => //).
by rewrite -H.
by rewrite -H0.
by rewrite (H s x0 x v H1).
by rewrite (H0 s x1 x v H1).
Qed.

Lemma inde_sep_imp l P Q : inde l P -> inde l Q -> inde l (P -* Q).
Proof.
move=> H H0 s h x v H1; split => H2 h' [H3 H3'] h'' H4.
- apply (proj1 (H0 s h'' _ v H1)).
  have H5 : P s h' by move: (H s h' _ v H1); tauto.
  eapply H2; eauto.
- apply (proj2 (H0 s h'' _ v H1)) => //.
  have H5 : P (store.upd x v s) h' by move: (H s h' _ v H1); tauto.
  eapply H2; eauto.
Qed.

Lemma inde_mapsto lst e e' :
  disj (vars e) lst -> disj (vars e') lst -> inde lst (e |~> e').
Proof.
move=> H H0; red => s h x v0 H1; split => H2; case: H2 => [p [Hp Hh]]; exists p.
- rewrite eval_upd; last first.
    apply/negP/inP; eapply disj_not_In; eauto. by apply/inP.
  rewrite eval_upd //; apply/negP/inP; eapply disj_not_In; eauto. by apply/inP.
- rewrite eval_upd in Hp; last first.
    apply/negP/inP; eapply disj_not_In; eauto. by apply/inP.
  rewrite eval_upd // in Hh; apply/negP/inP; eapply disj_not_In; eauto. by apply/inP.
Qed.

Lemma inde_mapstos : forall (l : seq expr) (xs : seq var.v) e,
  disj (foldr (@app var.v) nil (map vars l)) xs ->
  disj (vars e) xs -> inde xs (e |--> l).
Proof.
elim => // a l IHl xs e /=; case/disj_app_inv => H H' H1; red => s h x v H0; split => H2.
- case: H2 => h1 [h2 [H3 [H5 [H4 H7]]]]; exists h1, h2.
  repeat (split => //).
  + apply inde_upd_store => //.
    apply inde_mapsto; apply disj_cons_R.
    by apply disj_nil_R.
    by apply (@disj_not_In _ xs) => //; apply/inP.
    exact/disj_nil_R.
    by apply (@disj_not_In _ xs) => //; apply/inP.
  + apply inde_upd_store => //.
    apply IHl; apply disj_cons_R.
    by apply disj_nil_R.
    by apply (@disj_not_In _ xs) => //; apply/inP.
    exact/disj_nil_R.
    rewrite /= cats0.
    by apply (@disj_not_In _ xs) => //; apply/inP.
- case: H2 => h1 [h2 [H3 [H5 [H4 H7]]]]; exists h1, h2.
  repeat (split => //).
  + move: H4; apply mapsto_ext => //.
    * rewrite eval_upd //; by apply/negP/inP/(disj_not_In H1)/inP.
    * rewrite eval_upd //; by apply/negP/inP/(disj_not_In H)/inP.
  + move/(IHl _ (e \+ cst_e (A.of_nat 1))) : H' => {IHl} /=.
    rewrite cats0.
    by move/(_ H1 _ _ x v) => ->.
Qed.

Lemma map_vars_list_expr : forall (l : seq expr),
  (forall e, List.In e l -> vars e = nil) -> map vars l = map (fun _ => nil) l.
Proof.
elim => // hd tl IH H /=.
rewrite IH /=; last first.
  move=> e H'; rewrite H //=; by right.
rewrite H //=; by left.
Qed.

Lemma inde_mapstos' l xs p : disj (vars p) xs -> inde xs (p |---> l).
Proof.
move=> H.
rewrite /mapstos'.
apply inde_mapstos => //.
rewrite map_vars_list_expr; last first.
  move=> e H0.
  rewrite -> List.in_map_iff in H0.
  by case: H0 => x [<- ?].
rewrite (_ : foldr _ _ _ = nil); last by elim: l.
exact: disj_nil_L.
Qed.

End Assert.

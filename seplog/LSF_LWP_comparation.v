(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ZArith List EqNat Classical Omega Max.
From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import bipl seplog integral_type.

Require Import expr_b_dp.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.

Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.
Local Close Scope Z_scope.

Require Import frag_list_triple.
Require Import frag_list_entail.

Import Fresh.

(** Smallfoot like proof-system (pure forward) with arithmetic *)

Inductive LSF : assrt -> @while.cmd cmd0 expr_b -> assrt -> Prop :=
| LSF_precond_stre : forall L1 L1' L2 c,
  assrt_interp L1 ===> assrt_interp L1' ->
  LSF L1' c L2 ->
  LSF L1 c L2

| LSF_seq_assoc : forall P Q c1 c2 c3,
  LSF P (c1; (c2; c3)) Q ->
  LSF P ((c1; c2); c3) Q

| LSF_add_empty : forall P Q c,
  LSF P (c; skip) Q ->
  LSF P c Q

| LSF_empty: forall P Q,
  assrt_interp P ===> assrt_interp Q ->
  LSF P skip Q

| LSF_assign: forall pi sig Q c x e x',
  fresh_assrt x' (pi, sig) ->
  fresh_assrt x' Q ->
  fresh_cmd x' c ->
  fresh_e x' e ->
  fresh_e x' (var_e x) ->
  LSF (((subst_b pi (var_e x) (var_e x')) \&& (var_e x \= subst_e e (var_e x) (var_e x'))), subst_Sigma sig x (var_e x')) c Q ->
  LSF (pi, sig) (x <- e ; c) Q

| LSF_lookup: forall pi sig e1 e2 e x Q c x',
  (forall s, eval_b pi s  -> eval_b (e1 \= e) s ) ->
  fresh_assrt x' (pi, star sig (singl e1 e2)) ->
  fresh_assrt x' Q ->
  fresh_cmd x' c ->
  fresh_e x' e ->
  fresh_e x' (var_e x) ->
  LSF (((subst_b pi (var_e x) (var_e x')) \&& ((var_e x) \= (subst_e e2 (var_e x) (var_e x')))), subst_Sigma (star sig (singl e1 e2)) x (var_e x')) c Q ->
  LSF (pi,star sig (singl e1 e2)) (x <-* e; c) Q

| LSF_mutation: forall pi1 sig1 e1 e2 e3 e4 Q c,
  (forall s, eval_b pi1 s  -> eval_b (e1 \= e3) s ) ->
  LSF (pi1,star sig1 (singl e1 e4)) c Q ->
  LSF (pi1,star sig1 (singl e1 e2)) (e3 *<- e4 ; c) Q

| LSF_mutation': forall pi1 sig1 e1 e3 e4 Q c,
  (forall s, eval_b pi1 s  -> eval_b (e1 \= e3) s ) ->
  LSF (pi1,star sig1 (singl e1 e4)) c Q ->
  LSF (pi1,star sig1 (cell e1)) (e3 *<- e4 ; c) Q

| LSF_cond: forall b c1 c2 c Q pi sig,
  LSF (pi \&& b, sig) (c1; c) Q ->
  LSF (pi \&& (\~ b), sig) (c2 ; c) Q ->
  LSF (pi, sig) ((If b Then c1 Else c2) ; c) Q

| LSF_unroll_lst_lookup: forall pi sig e1 e2 e x Q c x',
  (forall s, eval_b pi s  -> eval_b (e1 \= e) s ) ->
  fresh_assrt x' (pi, star sig (lst e1 e2)) ->
  fresh_assrt x' Q ->
  fresh_cmd x' c ->
  fresh_e x' e ->
  fresh_e x' (var_e x) ->
  (forall s, [ pi =b> (e1 \!= e2) ]b_s) ->
  LSF ((pi \&& ((var_e x') \= e2) ,star sig (star (star (singl e1 (var_e x')) (cell (e1 \+ nat_e 1))) (lst (var_e x') e2)))) (x <-* e; c) Q ->
  LSF ((pi \&& ((var_e x') \!= e2) ,star sig (star (star (singl e1 (var_e x')) (cell (e1 \+ nat_e 1))) (lst (var_e x') e2)))) (x <-* e; c) Q ->
  LSF (pi,star sig (lst e1 e2)) (x <-* e; c) Q.

Axiom LSF_sound: forall P c Q,
  LSF P c Q ->
  {{assrt_interp P}} c {{assrt_interp Q}}.

Axiom LSF_lookup': forall pi sig e1 e2 e x Q c x',
  (forall s, eval_b pi s  -> eval_b (e1 \= e) s ) ->
  x' = (max (var_max_cmd c) (max (var_max_assrt (pi,star sig (singl e1 e2))) (max (var_max_assrt Q) (max x (Max_ext.max_lst (vars e)))))) + 1 ->
  LSF (((subst_b pi (var_e x) (var_e x')) \&& ((var_e x) \= (subst_e e2 (var_e x) (var_e x')))), subst_Sigma (star sig (singl e1 e2)) x (var_e x')) c Q ->
  LSF (pi,star sig (singl e1 e2)) (x <-* e; c) Q.

Axiom LSF_assign': forall pi sig Q c x e x',
  x' = (max (var_max_cmd c) (max (var_max_assrt (pi,sig)) (max (var_max_assrt Q) (max x (Max_ext.max_lst (vars e)))))) + 1 ->
  LSF (((subst_b pi (var_e x) (var_e x')) \&& ((var_e x) \= (subst_e e (var_e x) (var_e x')))), subst_Sigma sig x (var_e x')) c Q ->
  LSF (pi, sig) (x <- e ; c) Q.

Axiom LSF_unroll_lst_lookup': forall pi sig e1 e2 e x Q c x',
  (forall s, eval_b pi s  -> eval_b (e1 \= e) s ) ->
  x' = (max (var_max_cmd c) (max (var_max_assrt (pi,star sig (lst e1 e2))) (max (var_max_assrt Q) (max x (Max_ext.max_lst (vars e)))))) + 1 ->
  (forall s, [ pi =b> (e1 \!= e2) ]b_s) ->
  LSF ((pi \&& (var_e x' \= e2), star sig (star (star (singl e1 (var_e x')) (cell (e1 \+ nat_e 1))) (lst (var_e x') e2)))) (x <-* e; c) Q ->
  LSF ((pi \&& (var_e x' \!= e2), star sig (star (star (singl e1 (var_e x')) (cell (e1 \+ nat_e 1))) (lst (var_e x') e2)))) (x <-* e; c) Q ->
  LSF (pi, star sig (lst e1 e2)) (x <-* e; c) Q.

(* oui mais la c'est une expression qui est introduite, comment introduire une variable ??? *)

(* bete test, pas si bete que ca finalement *)

Local Open Scope frag_list_scope.

Goal
  {{{ ((var_e 1 \!= var_e 2) \&& (var_e 1 \!= cst_e 0%Z), lst (var_e 1) (var_e 2)) }}}
  0 <-* (var_e 1)
  {{{ (true_b, lst (var_e 1) (var_e 2)) }}}.
Proof.
  eapply tritra_use.
    by compute.
  eapply tritra_precond_stre with (((var_e 1 \!= var_e 2) \&& (var_e 1 \!= cst_e 0%Z)), star emp (lst (var_e 1) (var_e 2))).
    eapply entail_soundness.
    by Entail_turnr; Entail.

  eapply tritra_lookup_lst.
  intro x; split; omegab.
  simpl; intuition.

  eapply tritra_precond_stre.
  eapply entail_soundness.
  Entail_turnl.
  Entail_turnl.
  Entail_turnl.
  Entail_turnl.
  eapply entail_id.

  eapply tritra_lookup.

  intros; omegab.

  eapply tritra_subst_elt.
  simpl.

  eapply tritra_entail.

  eapply Decompose_Assrt_interp.
  left.
  eapply entail_soundness.
  Entail_turnr.
  eapply entail_lstelim'''.


  intros; omegab.
  intros; omegab.
  intros; omegab.
  Entail_turnl.
  Entail_turnr.
  Entail_turnr.
  Entail_turnr.
  Entail.

  eapply tritra_lookup.

  intros; omegab.

  eapply tritra_subst_elt.
  simpl.

  eapply tritra_entail.

  eapply Decompose_Assrt_interp.
  left.
  eapply entail_soundness.
  Entail_turnr.
  eapply entail_lstelim'''.
  intros; omegab.
  intros; omegab.
  intros; omegab.
  Entail_turnl.
  Entail_turnr.
  Entail_turnr.
  Entail_turnr.
  Entail.
(*  Show Proof.*)
  (* TODO: old comment size = 1505 *)
Qed.

Goal
  {{ assrt_interp ((var_e 1 \!= var_e 2) \&& (var_e 1 \!= cst_e 0%Z), lst (var_e 1) (var_e 2))}}
  0 <-* (var_e 1)
  {{ assrt_interp (true_b, lst (var_e 1) (var_e 2))}}.

  eapply LSF_sound.
  eapply LSF_add_empty.

  eapply LSF_precond_stre with (((var_e 1 \!= var_e 2) \&& (var_e 1 \!= cst_e 0%Z)), star emp (lst (var_e 1) (var_e 2))).

  eapply entail_soundness.
  Entail_turnr; Entail.

  eapply LSF_unroll_lst_lookup'.
  intros; omegab.
  compute; intuition.
  intros; omegab.

  eapply LSF_precond_stre with
    ((var_e 1 \!= var_e 2) \&& (var_e 1 \!= cst_e 0%Z),
     star
     (star (lst (var_e 3) (var_e 2)) (cell (var_e 1 \+ nat_e 1)))
     (singl (var_e 1) (var_e 3))).

  eapply entail_soundness.
  Entail_turnl.
  Entail_turnl.
  Entail_turnr.
  Entail_turnr.
  Entail.

  eapply LSF_lookup'.
  intros; omegab.
  compute; intuition.

  eapply LSF_empty.

  simpl subst_Sigma.

  eapply entail_soundness.

  Entail_turnr.
  eapply entail_lstelim'''.
  intros; omegab.
  intros; omegab.
  intros; omegab.
  Entail_turnl.
  Entail_turnr.
  Entail_turnr.
  eapply entail_lstsamelst.
  intros; omegab.
  intros; omegab.
  simpl.
  Entail_turnl.
  eapply entail_star_elim''.
  intros; omegab.
  Entail.
  eapply LSF_precond_stre with
    ((var_e 1 \!= var_e 2) \&& var_e 1 \!= cst_e 0%Z,
     star
     (star (lst (var_e 3) (var_e 2)) (cell (var_e 1 \+ nat_e 1)))
     (singl (var_e 1) (var_e 3))).

  eapply entail_soundness.
  Entail_turnl.
  Entail_turnl.
  Entail_turnr.
  Entail_turnr.
  Entail.

  eapply LSF_lookup'.
  intros; omegab.
  compute; intuition.

  eapply LSF_empty.

  simpl subst_Sigma.

  eapply entail_soundness.

  Entail_turnr.
  eapply entail_lstelim'''.
  intros; omegab.
  intros; omegab.
  intros; omegab.
  Entail_turnl.
  Entail_turnr.
  Entail_turnr.
  eapply entail_lstsamelst.
  intros; omegab.
  intros; omegab.
  simpl.
  Entail_turnl.
  eapply entail_star_elim''.
  intros; omegab.
  Entail.
(*  Show Proof.*)
  (* size = 1440 *)
Qed.

(* max3: return the max of three variable*)

(* with small foot *)
Goal
  {{ assrt_interp (true_b, emp)}}
  If ((var_e 1) \>= (var_e 2)) Then
    If (var_e 1 \>= var_e 3) Then
      (0 <- var_e 1)
    Else
      (0 <- (var_e 3))
  Else
    If (var_e 2 \>= var_e 3) Then
      (0 <- (var_e 2))
    Else
      (0 <- (var_e 3))
  {{ assrt_interp (((var_e 0) \= (var_e 1)) \|| ((var_e 0) \= (var_e 2)) \|| ((var_e 0) \= (var_e 3)), emp)}}.
  eapply LSF_sound.
  eapply LSF_add_empty.
  eapply LSF_cond.
  eapply LSF_cond.
  eapply LSF_assign'.
  simpl; intuition.
  simpl.
  eapply LSF_empty.

(*  Show Proof.*)

  eapply entail_soundness; Entail.

(*  Show Proof.*)

  eapply LSF_assign'.
  simpl; intuition.
  simpl.
  eapply LSF_empty.
  eapply entail_soundness; Entail.
  eapply LSF_cond.
  eapply LSF_assign'.
  simpl; intuition.
  simpl.
  eapply LSF_empty.
  eapply entail_soundness; Entail.
  eapply LSF_assign'.
  simpl; intuition.
  simpl.
  eapply LSF_empty.
  eapply entail_soundness; Entail.
(*  Show Proof.*)
  (* proof size = 601 *)
Qed.

(* with bigtoe *)

Goal
  {{{ (true_b, emp) }}}
  If (var_e 1 \>= var_e 2) Then
    If (var_e 1 \>= var_e 3) Then
      (0 <- var_e 1)
    Else
      (0 <- var_e 3)
  Else
    If (var_e 2 \>= var_e 3) Then
      (0 <- var_e 2)
    Else
      (0 <- var_e 3)
  {{{ ((var_e 0 \= var_e 1) \|| (var_e 0 \= var_e 2) \|| var_e 0 \= var_e 3,emp) }}}.
Proof.
  eapply tritra_use.
  simpl.
  intuition.
  eapply tritra_if.
  eapply tritra_if.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  eapply tritra_if.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
  eapply tritra_subst_elt.
  simpl.
  eapply tritra_entail.
  eapply Decompose_Assrt_interp; left.
  eapply entail_soundness; Entail.
(*  Show Proof.*)
  (* proof size = 612 *)
Qed.

Ltac Rotate_LSF_sig_lhs :=
  match goal with
    | |- LSF (?pi,?sig) ?c ?Q =>
      eapply LSF_precond_stre with (
        (pi, remove_empty_heap pi (star_assoc_left (star_com sig) emp))
      ); [apply entail_soundness; simpl; Entail| simpl]
  end.

Section swap.

(* swap: swap the value of two cells *)

Definition i : var.v := 1.
Definition j : var.v := 2.
Definition x : var.v := 4.
Definition y : var.v := 3.
Definition vx : var.v := 5.
Definition vy : var.v := 6.

Definition swap (x y:var.v) : @while.cmd cmd0 expr_b :=
    i <-* var_e x;
    j <-* var_e y;
    var_e x *<- var_e j;
    var_e y *<- var_e i.

Definition swap_precond (x y:var.v) (vx vy : nat) : assrt :=
  (true_b, star (singl (var_e x) (var_e vx)) (singl (var_e y) (var_e vy))).

Definition swap_postcond (x y:var.v) (vx vy : nat) : assrt :=
  (true_b, star (singl (var_e x) (var_e vy)) (singl (var_e y) (var_e vx))).

(* with smallfoot *)

Lemma swap_verif:
  {{assrt_interp (swap_precond x y vx vy)}}
  swap x y
  {{assrt_interp ((swap_postcond x y vx vy))}}.
Proof.
intros.
unfold swap_precond.
unfold swap_postcond.
eapply LSF_sound.
simpl; intuition.
unfold x; unfold y; unfold i; unfold j; unfold vx; unfold vy.
unfold swap.

eapply LSF_add_empty.
repeat (eapply LSF_seq_assoc).
Rotate_LSF_sig_lhs.
eapply LSF_lookup'.
intros; omegab.
simpl; intuition.
simpl.
repeat (eapply LSF_seq_assoc).
Rotate_LSF_sig_lhs.
eapply LSF_lookup'.
intros; omegab.
simpl; intuition.
repeat (eapply LSF_seq_assoc).
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation.
intros; omegab.
Rotate_LSF_sig_lhs.
eapply LSF_mutation.
intros; omegab.
eapply LSF_empty.
eapply entail_soundness.
Entail.
(*Show Proof.*)
(* size= 1765 *)
Qed.

(* with bigtoe *)

Lemma swap_verif':
    {{assrt_interp (swap_precond x y vx vy)}}
    swap x y
    {{Assrt_interp ((swap_postcond x y vx vy)::nil)}}.
Proof.
intros.
unfold swap_precond.
unfold swap_postcond.
eapply tritra_use.
simpl; intuition.
unfold x, y, i, j, vx, vy.

Rotate_tritra_sig_lhs.
eapply tritra_lookup.
intros; omegab.
Rotate_tritra_sig_lhs.
eapply tritra_subst_lookup2.
intros; omegab.
simpl; intuition.
Rotate_tritra_sig_lhs.
eapply tritra_subst_mutation.
simpl.
eapply tritra_mutation.
intros; omegab.
eapply tritra_subst_mutation.
simpl.
Rotate_tritra_sig_lhs.
eapply tritra_mutation.
intros; omegab.
eapply tritra_subst_elt.
simpl.
eapply tritra_entail.
eapply Decompose_Assrt_interp; left.
eapply entail_soundness; Entail.
(*Show Proof.*)
(* size = 1424 *)
Qed.

End swap.

(* initialization: initialize some field of an array of data-structure*)

Definition ptr : var.v := 1.
Definition startl : var.v := 2.
Definition size: var.v := 3.
Definition idx: var.v := 4.
Definition init_val: var.v := 5.

Fixpoint init_body (n: nat) {struct n}: @while.cmd cmd0 expr_b :=
  match n with
    0 => skip
    | S n' =>
      (var_e ptr \+ var_e idx) *<- var_e init_val;
       ptr <- var_e ptr \+ var_e size;
       init_body n'
   end.

Definition init (n: nat) : @while.cmd cmd0 expr_b :=
    ptr <- var_e startl;
    init_body n.

Fixpoint init_precond_sigma (n: nat) {struct n} : Sigma :=
  match n with
    0 => emp
    | S n' => star
        (cell (var_e startl \+ var_e idx \+ var_e size \* cst_e (Z_of_nat n') ))
	(init_precond_sigma n')
end.

Definition init_precond (n: nat) : assrt :=
  (var_e startl \> cst_e 0%Z, init_precond_sigma n).

Fixpoint init_postcond_sigma (n: nat) {struct n}: Sigma :=
  match n with
    0 => emp
    | S n' => star
	(singl (var_e startl \+ var_e idx \+ var_e size \* cst_e (Z_of_nat n')) (var_e init_val))
	(init_postcond_sigma n')
end.

Definition init_postcond (n: nat) : assrt :=
  (var_e startl \> cst_e 0%Z, init_postcond_sigma n).

(* with bigtoe *)


Lemma init_verif_bigtoe_5: forall n, n = 5 ->
  {{{ init_precond n }}} init n {{{ init_postcond n }}}.
Proof.
intros; subst n.
unfold init; simpl init_body.
unfold init_precond; simpl init_precond_sigma.
unfold init_postcond; simpl init_postcond_sigma.
unfold ptr; unfold startl; unfold size; unfold idx; unfold init_val.

eapply tritra_use.
simpl; intuition.

Tritra.
(*Show Proof.*)
(* size = 3699 *)
Qed.

Lemma init_verif_bigtoe_10: forall n, n = 10 ->
  {{{ init_precond n }}} init n {{{ init_postcond n }}}.
Proof.
intros; subst n.
unfold init; simpl init_body.
unfold init_precond; simpl init_precond_sigma.
unfold init_postcond; simpl init_postcond_sigma.
unfold ptr, startl, size, idx, init_val.

eapply tritra_use.
simpl; intuition.

Tritra.
(*Show Proof.*)
(* size = 5558 *)
Qed.

Lemma init_verif_bigtoe_12: forall n, n = 12 ->
  {{{ init_precond n }}} init n {{{ init_postcond n }}}.
Proof.
intros; subst n.
unfold init; simpl init_body.
unfold init_precond; simpl init_precond_sigma.
unfold init_postcond; simpl init_postcond_sigma.
unfold ptr, startl, size, idx, init_val.

eapply tritra_use.
simpl; intuition.

Tritra.
(*Show Proof.*)
(* size = 5950 *)
Qed.

(* with smallfoot *)

Import ZIT.

(** tactics for cleaning hypothesis *)

Ltac Decompose_hyp := eval_b2Prop_hyps;
  match goal with
    | id: ex ?P |- _ => inversion_clear id; Decompose_hyp
    | id: ?P1 /\ ?P2 |- _ => decompose [and] id; clear id; Decompose_hyp
    | id: eval ?e ?s = ?v |- _ => simpl in id
    | |- _ => idtac
  end.

Lemma init_verif_smallfoot_5: forall n, n = 5 ->
  {{ assrt_interp (init_precond n)}} (init n) {{ assrt_interp (init_postcond n)}}.
Proof.
intros; subst n.
unfold init; simpl init_body.
unfold init_precond; simpl init_precond_sigma.
unfold init_postcond; simpl init_postcond_sigma.
unfold ptr, startl, size, idx, init_val.

eapply LSF_sound.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
intros; omegab.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s H.

(*Ltac unfold_t_plus := match goal with
| id:context[t_plus _ _] |- _ => rewrite /t_plus in id
end.*)

Ltac local_omega :=
  Decompose_hyp; (*repeat unfold_t_plus;*) omegab.

local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s H; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.

eapply LSF_empty.
eapply entail_soundness.
Entail.
(*Show Proof.*)
(* size= 4715 *)
Qed.

Lemma init_verif_smallfoot_10: forall n, n = 10 ->
  {{ assrt_interp (init_precond n)}} init n {{ assrt_interp (init_postcond n)}}.
Proof.
intros; subst n.
unfold init; simpl init_body.
unfold init_precond; simpl init_precond_sigma.
unfold init_postcond; simpl init_postcond_sigma.
unfold ptr, startl, size, idx, init_val.

eapply LSF_sound.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
intros; omegab.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.

eapply LSF_empty.
eapply entail_soundness.
Entail.
(*Show Proof.*)
(* size= 7268 *)
Qed.

Lemma init_verif_smallfoot_12: forall n, n = 12 ->
  {{ assrt_interp (init_precond n)}} (init n) {{ assrt_interp (init_postcond n)}}.
Proof.
intros; subst n.
unfold init; simpl init_body.
unfold init_precond; simpl init_precond_sigma.
unfold init_postcond; simpl init_postcond_sigma.
unfold ptr, startl, size, idx, init_val.

eapply LSF_sound.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
intros; omegab.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.
Rotate_LSF_sig_lhs.
eapply LSF_mutation'.
move=> s h; local_omega.

eapply LSF_assign'.
simpl; intuition.
simpl.

eapply LSF_empty.
eapply entail_soundness.
Entail.
(*Show Proof.*)
(* size= 7825 *)
Qed.
